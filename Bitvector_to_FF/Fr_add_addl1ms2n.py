from z3 import *

# 创建256位的位向量
a = BitVec('a', 256)
b = BitVec('b', 32)
r_2 = BitVec('r_2', 256)
f_a = BitVec('f_a', 256)
f_b = BitVec('f_b', 256)
r_1 = BitVec('r_1', 256)
r_1_type = BitVec('r_1_type', 32)  # 使用32位表示类型，0表示SHORT，1表示LONG, 2表示L&M， 3表示S&M

# 模数p
p = BitVecVal(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001, 256)
s = Solver()
# 设置 f_a 和 f_b 的约束
s.add(f_a == a % p)
s.add(f_b == b % p)
# ;
# f_b_m = Fr_toMontgomery(f_b)
# FF_constraint = And(r->type = Fr_LONGMONTGOMERY, r_1 == (f_a + f_b_m) % p)