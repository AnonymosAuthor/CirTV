from z3 import *

# 模数p
p = BitVecVal(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001, 256)

R = BitVecVal(0x0e0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb, 256)

R2 = BitVecVal(0x0216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7, 256)

# 创建256位的位向量
a_shortVal = BitVec('shortVal', 32)
a_longVal = BitVec('longVal', 256)
r_1 = BitVec('r_1', 64)

r_2 = BitVec('r_2', 64)

a_type = BitVec('type', 32)
r_1can64 = Bool('r1can64')
r_2can64 = Bool('r2can64')

Fr_SHORT = 0
Fr_LONG = 1
Fr_LONGMONTGOMERY = 2
Fr_SHORTMONTGOMERY = 3

# 创建求解器
s = Solver()
s.add(ULT(a_longVal, p))
# 定义 r 和 a
a = {'shortVal': a_shortVal, 'longVal': a_longVal, 'type': a_type}
# 添加对 a['type'] 的限制
s.add(Or(a['type'] == Fr_SHORT, a['type'] == Fr_LONG, a['type'] == Fr_LONGMONTGOMERY, a['type'] == Fr_SHORTMONTGOMERY))

f_a = If(Or(a['type'] == Fr_SHORT, a['type'] == Fr_SHORTMONTGOMERY), SignExt(224, a['shortVal']), a['longVal'])
f_a_type = a['type']


# if @[src2, 8]{63} = 1 then
long_condition = Or(a_type == Fr_LONG, a_type == Fr_LONGMONTGOMERY)
# 将 a_longVal 拆分为 64 位的部分
src2_8 = Extract(63, 0, a_longVal)  # 低64位
src2_16 = Extract(127, 64, a_longVal)  # 65~128位
src2_24 = Extract(191, 128, a_longVal)  # 129~192位
src2_32 = Extract(255, 192, a_longVal)  # 193~256位

# 修改后的条件
condition2 = And(Extract(63, 31, src2_8) == 0, src2_16 == 0, src2_24 == 0, src2_32 == 0)
condition3 = And(Or(Extract(63, 31, src2_8) != 0, src2_16 != 0, src2_24 != 0, src2_32 != 0), UGE(a_longVal, p))
condition4 = And(Or(Extract(63, 31, src2_8) != 0, src2_16 != 0, src2_24 != 0, src2_32 != 0), ULT(a_longVal, p))

# Fr_Constraint
# if @[src2, 8]{63} = 0 then
s.add(If(Or(a['type'] == Fr_SHORT, a['type'] == Fr_SHORTMONTGOMERY),
         And(r_1 == SignExt(32, a['shortVal']), r_1can64 == True), True))
s.add(If(long_condition,
         If(condition2,
            And(r_1 == src2_8, r_1can64 == True),
            If(condition3,
               r_1can64 == False,
               And(r_1 == src2_8 - Extract(63, 0, p), If(Extract(31, 31, r_1) == 0, r_1can64 == False, r_1can64 == True))
               )),
         True))

# FF_Constraint

s.add(If(Or(f_a_type == Fr_SHORT, f_a_type == Fr_SHORTMONTGOMERY),
         And(r_2 == Extract(63, 0, f_a), r_2can64 == True), True))
# IF a['type'] == Fr_LONGMONTGOMERY
# constraint1 = r_2_type == Fr_LONG
# constraint2 = r_2 * R % p == f_a
result2 = f_a - p
s.add(If(long_condition,
         If(ULE(f_a, 2 ** 31 - 1),
            And(r_2 == Extract(63, 0, f_a), r_2can64 == True),
            If(UGE(f_a, p),
               r_2can64 == False,
               If(result2 < -2 ** 31, r_2can64 == False, And(r_2 == Extract(63, 0, f_a - p), r_2can64 == True))
               )),
         True))

s.add(condition3 == False)
# target
target = And(r_1can64 == r_2can64, If(r_1can64 == True, r_1 == r_2, True))

# term
term = And(Not(target))

s.add(term)

# 检查模型
if s.check() == sat:
    model = s.model()
    print("Satisfiable")
    print(f"a_shortVal: {model[a_shortVal]} (hex: {hex(model[a_shortVal].as_long())})")
    print(f"a_longVal: {model[a_longVal]} (hex: {hex(model[a_longVal].as_long())})")
    print(f"a_type: {model[a['type']]}")
    print(f"r_1: {model[r_1]} (hex: {hex(model[r_1].as_long())})")
    print(f"f_a: {model.eval(f_a)} (hex: {hex(model.eval(f_a).as_long())})")
    print(f"r_2: {model[r_2]} (hex: {hex(model[r_2].as_long())})")
    print(model.eval(condition2))
    print(model.eval(condition3))
    print(model.eval(condition4))
    print(f"r_1can64: {model[r_1can64]}")
    print(f"r_2can64: {model[r_2can64]}")

else:
    print("Unsatisfiable")
