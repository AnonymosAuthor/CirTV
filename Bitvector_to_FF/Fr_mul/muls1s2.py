from z3 import *

# 创建32位和256位的位向量
a = BitVec('a', 32)
b = BitVec('b', 32)
f_a = BitVec('f_a', 256)
f_b = BitVec('f_b', 256)

# 模数p
p = BitVecVal(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001, 256)

# 结果
r_1 = BitVec('r_1', 256)
r_1_type = BitVec('r_1_type', 32)  # 使用32位表示类型，0表示SHORT，1表示LONG

# 创建求解器
s = Solver()

# 设置范围约束
s.add(-2 ** 31 <= a, a <= 2 ** 31 - 1)
s.add(-2 ** 31 <= b, b <= 2 ** 31 - 1)

# 设置 f_a 和 f_b 的约束
s.add(f_a == SignExt(224, a) % p)
s.add(f_b == SignExt(224, b) % p)

# FF_constraints
FF_constraints = And(ZeroExt(256, r_1) == ZeroExt(256, f_a) * ZeroExt(256, f_b) % ZeroExt(256, p), r_1_type == 1)
s.add(a == 0x80000000)
s.add(b == 0x40000001)
s.add(FF_constraints)

# Fr_constraint
# 创建64位的位向量用于存储结果
result_64 = SignExt(32, a) * SignExt(32, b)

# 创建一个256位的位向量用于保存溢出的结果
r_2 = BitVec('r_2', 256)

# 定义上溢出和下溢出的条件
overflow_lower = result_64 < 0

Fr_constraints = If(overflow_lower,
                    r_2 == SignExt(192, result_64) + p,  # 如果下溢出，先将result_64扩展到256位，再加上p
                    r_2 == SignExt(192, result_64))  # 如果没有溢出，直接用64位保存

s.add(Fr_constraints)

# target
target = And(r_1 == r_2 % p)

# term
term = And(Not(target))

s.add(term)
if s.check() == sat:
    model = s.model()
    print("Satisfiable")
    print(f"a: {model[a]} (hex: {hex(model[a].as_long())})")
    print(f"b: {model[b]} (hex: {hex(model[b].as_long())})")
    print(f"f_a: {model[f_a]} (hex: {hex(model[f_a].as_long())})")
    print(f"f_b: {model[f_b]} (hex: {hex(model[f_b].as_long())})")
    print(f"r_1: {model[r_1]} (hex: {hex(model[r_1].as_long())})")
    print(f"r_2: {model[r_2]} (hex: {hex(model[r_2].as_long())})")
    print(model.eval(overflow_lower))
    print(f"result64: {model.eval(result_64)} (hex: {hex(model.eval(result_64).as_long())})")

else:
    print("Unsatisfiable")
# 检查是否UNSAT
if s.check() == unsat:
    print("The term is UNSAT, indicating the code has no errors.")
else:
    print("The term is SAT, indicating there might be errors in the code.")
