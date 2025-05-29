from z3 import *

# 创建256位的位向量
a = BitVec('a', 256)
b = BitVec('b', 256)
r_2 = BitVec('r_2', 256)
f_a = BitVec('f_a', 256)
f_b = BitVec('f_b', 256)
r_1 = BitVec('r_1', 256)
r_1_type = BitVec('r_1_type', 32)  # 使用32位表示类型，0表示SHORT，1表示LONG

# 模数p
p = BitVecVal(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001, 256)

# 扩展a和b到512位，并进行相加
result2 = ZeroExt(256, a) + ZeroExt(256, b)

# 检查是否有溢出
over = Bool('over')
over_constraint = over == (Extract(511, 256, result2) != 0)

# 计算expected_result
expected_result = a + b

# 创建求解器
s = Solver()

# 条件1: 如果相加结果大于等于模数p或者有溢出
condition1 = UGE(expected_result, p) | over

# FR_constraint
FR_constraint = If(condition1, result2 == ZeroExt(256, p + r_2), r_2 == expected_result)

# 设置 f_a 和 f_b 的约束
s.add(f_a == a % p)
s.add(f_b == b % p)
# 计算 f_a 和 f_b 之和
sum_ab = f_a + f_b

# FF_constraint
FF_constraint = And(r_1_type == 1, r_1 == sum_ab % p)



s.add(over_constraint)
s.add(FR_constraint)
# 添加约束条件，确保a和b小于p
s.add(0 <= a)
s.add(a < p)
s.add(0 <= b)
s.add(b < p)
# s.add(a == 21888242871839275222246405745257275088548364400416034343698204186575808495616)
# s.add(b == 2)
# 检查模型

# target
target = And(a % p == f_a, b % p == f_b, r_1 == r_2 % p)

# term
term = And(FF_constraint, FR_constraint, Not(target))

s.add(term)


# 检查是否UNSAT
if s.check() == unsat:
    print("The term is UNSAT, indicating the code has no errors.")
else:
    print("The term is SAT, indicating there might be errors in the code.")
