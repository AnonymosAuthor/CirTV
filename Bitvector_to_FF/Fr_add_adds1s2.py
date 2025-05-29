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

# 计算 f_a 和 f_b 之和
sum_ab = f_a + f_b

# 计算扩展为64位的 a + b
sum_64 = SignExt(32, a) + SignExt(32, b)

# 0 <= a + b <= 2**31-1 ->  fa + fb = a + b -> 0 <= a + b <= 2**31-1
# -2**31 <= a + b < 0 -> fa + fb = a + b +p -> -2**31 + p <= a + b < p


# FF_constraints
FF_constraints = If(And(sum_ab < p-2 ** 31, sum_ab > 2 ** 31 - 1),
                    And(r_1_type == 1, r_1 == sum_ab % p),  # 上溢出或下溢出情况
                    And(r_1_type == 0, r_1 == sum_ab % p))  # 没有溢出情况

s.add(FF_constraints)

# Fr_constraint
# 创建64位的位向量用于存储结果
result_64 = SignExt(32, a) + SignExt(32, b)

# 创建一个256位的位向量用于保存溢出的结果
r_2 = BitVec('r_2', 256)

# 定义上溢出和下溢出的条件
overflow_upper = result_64 > BitVecVal(2 ** 31 - 1, 64)
overflow_lower = result_64 < BitVecVal(-2 ** 31, 64)

Fr_constraints = If(overflow_upper,
                    r_2 == ZeroExt(192, result_64),  # 如果上溢出，直接使用256位保存结果
                    If(overflow_lower,
                       r_2 == SignExt(192, result_64) + p,  # 如果下溢出，先将result_64扩展到256位，再加上p
                       r_2 == SignExt(192, result_64)))  # 如果没有溢出，直接用64位保存

s.add(Fr_constraints)

# target
target = And((SignExt(224, a) % p == f_a), (SignExt(224, b) % p == f_b), r_1 == r_2 % p)

# term
term = And(FF_constraints, Fr_constraints, Not(target))

s.add(term)

# 检查是否UNSAT
if s.check() == unsat:
    print("The term is UNSAT, indicating the code has no errors.")
else:
    print("The term is SAT, indicating there might be errors in the code.")