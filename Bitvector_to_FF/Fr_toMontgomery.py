# void Fr_toMontgomery(PFrElement r, PFrElement a)
# {
#     if (a->type & Fr_MONTGOMERY)
#     {
#         Fr_copy(r, a);
#     }
#     else if (a->type & Fr_LONG)
#     {
#         r->shortVal = a->shortVal;
#
#         Fr_rawMMul(r->longVal, a->longVal, Fr_R2.longVal);
#
#         r->type = Fr_LONGMONTGOMERY;
#     }
#     else if (a->shortVal < 0)
#     {
#        int64_t a_shortVal = a->shortVal;
#        Fr_rawMMul1(r->longVal, Fr_R2.longVal, -a_shortVal);
#        Fr_rawNeg(r->longVal, r->longVal);
#
#        r->type = Fr_SHORTMONTGOMERY;
#     }
#     else
#     {
#         Fr_rawMMul1(r->longVal, Fr_R2.longVal, a->shortVal);
#
#         r->type = Fr_SHORTMONTGOMERY;
#     }
# }
from z3 import *

# 模数p
p = BitVecVal(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001, 256)

R = BitVecVal(0x0e0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb, 256)
R2 = BitVecVal(0x0216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7, 256)

# 创建256位的位向量
a_shortVal = BitVec('shortVal', 32)
a_longVal = BitVec('longVal', 256)
r_shortVal = BitVec('r_shortVal', 32)
r_longVal = BitVec('r_longVal', 256)

r_2 = BitVec('r_2', 256)

a_type = BitVec('type', 32)

Fr_SHORT = 0
Fr_LONG = 1
Fr_LONGMONTGOMERY = 2
Fr_SHORTMONTGOMERY = 3

# 创建求解器
s = Solver()

# 定义 r 和 a
r = {'shortVal': r_shortVal, 'longVal': r_longVal, 'type': BitVec('r_type', 32)}
a = {'shortVal': a_shortVal, 'longVal': a_longVal, 'type': a_type}
# 添加对 a['type'] 的限制
s.add(Or(a['type'] == Fr_SHORT, a['type'] == Fr_LONG, a['type'] == Fr_LONGMONTGOMERY, a['type'] == Fr_SHORTMONTGOMERY))

f_a = If(a['type'] == Fr_SHORT, SignExt(224, a['shortVal']) % p, a['longVal'])
r_2_type = BitVec('r_2type', 32)
f_a_type = a['type']

# 条件1: 如果 a 的类型已经是蒙哥马利类型
condition1 = Or(a['type'] & Fr_LONGMONTGOMERY != 0, a['type'] & Fr_SHORTMONTGOMERY != 0)
action1 = And(r['shortVal'] == a['shortVal'], r['longVal'] == a['longVal'], r['type'] == a['type'])
action1_2 = And(r_2 == f_a, r_2_type == f_a_type)

# 条件2: 如果 a 的类型是长整数
condition2 = a['type'] & Fr_LONG != 0
action2 = And(
    r['shortVal'] == a['shortVal'],
    r['longVal'] == (a['longVal'] * R) % p,
    r['type'] == Fr_LONGMONTGOMERY
)
action2_2 = And(r_2 == f_a * R % p, r_2_type == Fr_LONGMONTGOMERY)

# 条件3: 如果 a 的短整数值是负数
condition3 = a['shortVal'] < 0
neg_a = -SignExt(480, a['shortVal'])
result = Extract(255, 0, (neg_a * ZeroExt(256, R)) % ZeroExt(256, p))
neg_longVal = If(result == 0, 0, p - result)
action3 = And(
    r['longVal'] == neg_longVal,
    r['type'] == Fr_SHORTMONTGOMERY
)
action3_2 = And(r_2 == Extract(255, 0, ZeroExt(256, f_a) * ZeroExt(256, R) % ZeroExt(256, p)), r_2_type == Fr_SHORTMONTGOMERY)

# 条件4: 其他情况 如果 a 的短整数值是正数
condition4 = True
action4 = And(
    r['longVal'] == Extract(255, 0, (ZeroExt(480, a['shortVal']) * ZeroExt(256, R)) % ZeroExt(256, p)),
    r['type'] == Fr_SHORTMONTGOMERY
)
action4_2 = And(r_2 == Extract(255, 0, ZeroExt(256, f_a) * ZeroExt(256, R) % ZeroExt(256, p)), r_2_type == Fr_SHORTMONTGOMERY)

#s.add(And(condition1 == False, condition1 == False, condition3 == True))
#s.add(r['shortVal'] == -1)

# Fr_Constraint
s.add(If(condition1, action1, If(condition2, action2, If(condition3, action3, action4))))

## FF_Constraint
s.add(If(condition1, action1_2, If(condition2, action2_2, If(condition3, action3_2, action4_2))))

# target
target = And(r['longVal'] == r_2, r['type'] == r_2_type)

# term
term = Not(target)

s.add(term)
# 检查是否UNSAT
if s.check() == unsat:
    print("The term is UNSAT, indicating the code has no errors.")
else:
    print("The term is SAT, indicating there might be errors in the code.")
# # 检查模型
# if s.check() == sat:
#     model = s.model()
#     print("Satisfiable")
#     print(f"a_shortVal: {model[a_shortVal]} (hex: {hex(model[a_shortVal].as_long())})")
#     print(f"a_longVal: {model[a_longVal]} (hex: {hex(model[a_longVal].as_long())})")
#     print(f"r_type: {model[a['type']]}")
#     print(f"r_shortVal: {model[r_shortVal]} (hex: {hex(model[r_shortVal].as_long())})")
#     print(f"r_longVal: {model[r_longVal]} (hex: {hex(model[r_longVal].as_long())})")
#     print(f"r_type: {model[r['type']]}")
#     print(f"condition1: {model.eval(condition1)}")
#     print(f"condition2: {model.eval(condition2)}")
#     print(f"condition3: {model.eval(condition3)}")
#
#     print(f"fa_longVal: {model.eval(f_a)} (hex: {hex(model.eval(f_a).as_long())})")
#     print(f"f_a_type: {model.eval(f_a_type)}")
#     print(f"r_2: {model.eval(r_2)} (hex: {hex(model.eval(r_2).as_long())})")
#     print(f"r_2type: {model.eval(r_2_type)}")
#     print(f"result2: {model.eval(result2)} (hex: {hex(model.eval(result2).as_long())})")
#
# else:
#     print("Unsatisfiable")
