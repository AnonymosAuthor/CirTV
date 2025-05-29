# void Fr_toNormal(PFrElement r, PFrElement a)
# {
#     if (a->type == Fr_LONGMONTGOMERY)
#     {
#         r->type = Fr_LONG;
#         Fr_rawFromMontgomery(r->longVal, a->longVal);
#     }
#     else
#     {
#         Fr_copy(r, a);
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

f_a = a['longVal']
r_2_type = BitVec('r_2type', 32)
f_a_type = a['type']


# a['type'] == Fr_LONGMONTGOMERY
# constraint1 = r_2_type == Fr_LONG
# constraint2 = r_2 * R % p == f_a

# a['type'] != Fr_LONGMONTGOMERY
# action1_2 = And(r_2 == f_a, r_2_type == f_a_type)