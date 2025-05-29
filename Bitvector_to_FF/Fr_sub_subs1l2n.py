from z3 import *

# 创建256位的位向量
a = BitVec('a', 32)
b = BitVec('b', 256)
r_2 = BitVec('r_2', 256)
r_2_type = BitVec('r_1_type', 32)
f_a = BitVec('f_a', 256)
f_b = BitVec('f_b', 256)
r_1 = BitVec('r_1', 256)
r_1_type = BitVec('r_1_type', 32)  # 使用32位表示类型，0表示SHORT，1表示LONG, 2表示L&M， 3表示S&M

Fr_SHORT = 0
Fr_LONG = 1
Fr_LONGMONTGOMERY = 2
Fr_SHORTMONTGOMERY = 3

# 模数p
p = BitVecVal(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001, 256)
s = Solver()
s.add(ULE(b, p))
# 设置 f_a 和 f_b 的约束
s.add(f_a == SignExt(224, a) % p)
s.add(f_b == b % p)

# 条件1: 如果 a 的短整数值是正数
condition1 = a >= 0
# 检查是否是负数
less = (SignExt(224, a) < b)
# 计算expected_result
expected_result = SignExt(224, a) - b
# 条件: 如果a < b
condition1_1 = less
sub_ab = f_a - f_b
# FR_constraint
action_1 = If(condition1_1, r_2 == expected_result + p, r_2 == expected_result)
# FF_constraint
action_1_2 = And(r_1_type == 1, r_1 == sub_ab % p)

# 条件2: 其他情况 如果 a 的短整数值是负数
condition2 = a < 0
neg_a = -SignExt(224, a)      # 计算 -a_shortVal
result1 = p - neg_a
expected_result2 = result1 - b
less2 = ULT(result1, b)
# 条件: 如果a < b
condition2_1 = less2
sub_ab2 = f_a - f_b
# FR_constraint
action_2 = If(condition2_1, r_2 == expected_result2 + p, r_2 == expected_result2)
# FF_constraint
action_2_2 = And(r_1_type == 1, r_1 == sub_ab2 % p)

# Fr_Constraint
s.add(If(condition1, action_1, action_2))

# FF_Constraint
s.add(If(condition1, action_1_2, action_2_2))
# target
target = And(r_1 == r_2 % p)

# term
term = Not(target)
s.add(term)
# s.add(a == 0x40000000)
# s.add(b == 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000)
# 检查模型
if s.check() == sat:
    model = s.model()
    print("Satisfiable")
    print(f"a: {model[a]} (hex: {hex(model[a].as_long())})")
    print(f"b: {model[b]} (hex: {hex(model[b].as_long())})")
    print(f"f_a: {model[f_a]} (hex: {hex(model[f_a].as_long())})")
    print(f"f_b: {model[f_b]} (hex: {hex(model[f_b].as_long())})")
    print(f"r_1: {model[r_1]} (hex: {hex(model[r_1].as_long())})")
    print(f"r_2: {model[r_2]} (hex: {hex(model[r_2].as_long())})")
    print(f"condition1: {model.eval(condition1)} ")
else:
    print("Unsatisfiable")
# 检查是否UNSAT
if s.check() == unsat:
    print("The term is UNSAT, indicating the code has no errors.")
else:
    print("The term is SAT, indicating there might be errors in the code.")