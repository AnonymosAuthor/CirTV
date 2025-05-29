# 常量定义
Fr_N64 = 4  # 4个64位块，代表256位整数
lboMask = 0x3FFFFFFFFFFFFFFF  # 最后的64位屏蔽
Fr_rawq = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

# 辅助函数：将整数转换为64位块的列表（模拟 256 位整数）
def to_uint64_list(num, n=Fr_N64):
    """ 将整数转换为长度为n的64位块列表 """
    return [(num >> (64 * i)) & 0xFFFFFFFFFFFFFFFF for i in range(n)]

# 辅助函数：将64位块列表转换为整数
def from_uint64_list(lst):
    """ 将64位块列表转换为整数 """
    result = 0
    for i in range(len(lst)):
        result |= (lst[i] << (64 * i))
    return result

# Fr_rawAnd：按位与操作
def Fr_rawAnd(pRawResult, pRawA, pRawB):
    # 将A和B转换为64位块列表
    A_blocks = to_uint64_list(pRawA)
    B_blocks = to_uint64_list(pRawB)

    # 按位与操作
    result_blocks = [A_blocks[i] & B_blocks[i] for i in range(Fr_N64)]

    # 最后的64位屏蔽
    result_blocks[3] &= lboMask

    # 检查是否大于或等于Fr_rawq，如果是，进行模减法
    result_value = from_uint64_list(result_blocks)
    if result_value >= Fr_rawq:
        result_value -= Fr_rawq

    return result_value

# Fr_rawOr：按位或操作
def Fr_rawOr(pRawResult, pRawA, pRawB):
    # 将A和B转换为64位块列表
    A_blocks = to_uint64_list(pRawA)
    B_blocks = to_uint64_list(pRawB)

    # 按位或操作
    result_blocks = [A_blocks[i] | B_blocks[i] for i in range(Fr_N64)]

    # 最后的64位屏蔽
    result_blocks[3] &= lboMask

    # 检查是否大于或等于Fr_rawq，如果是，进行模减法
    result_value = from_uint64_list(result_blocks)
    if result_value >= Fr_rawq:
        result_value -= Fr_rawq

    return result_value

# Fr_rawXor：按位异或操作
def Fr_rawXor(pRawResult, pRawA, pRawB):
    # 将A和B转换为64位块列表
    A_blocks = to_uint64_list(pRawA)
    B_blocks = to_uint64_list(pRawB)

    # 按位异或操作
    result_blocks = [A_blocks[i] ^ B_blocks[i] for i in range(Fr_N64)]

    # 最后的64位屏蔽
    result_blocks[3] &= lboMask

    # 检查是否大于或等于Fr_rawq，如果是，进行模减法
    result_value = from_uint64_list(result_blocks)
    if result_value >= Fr_rawq:
        result_value -= Fr_rawq

    return result_value

# Fr_rawNot：按位取反操作
def Fr_rawNot(pRawResult, pRawA):
    # 将A转换为64位块列表
    A_blocks = to_uint64_list(pRawA)

    # 按位取反操作
    result_blocks = [~A_blocks[i] & 0xFFFFFFFFFFFFFFFF for i in range(Fr_N64)]

    # 最后的64位屏蔽
    result_blocks[3] &= lboMask

    # 检查是否大于或等于Fr_rawq，如果是，进行模减法
    result_value = from_uint64_list(result_blocks)
    if result_value >= Fr_rawq:
        result_value -= Fr_rawq

    return result_value

# 测试函数
pRawA = 0x123456789ABCDEF123456789ABCDEF123456789ABCDEF123456789ABCDEF1234  # 示例256位数
pRawB = 0xFEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210  # 示例256位数

# 测试按位与操作
result_and = Fr_rawAnd(0, pRawA, pRawB)
print(f"按位与操作结果: {hex(result_and)}")

# 测试按位或操作
result_or = Fr_rawOr(0, pRawA, pRawB)
print(f"按位或操作结果: {hex(result_or)}")

# 测试按位异或操作
result_xor = Fr_rawXor(0, pRawA, pRawB)
print(f"按位异或操作结果: {hex(result_xor)}")

# 测试按位取反操作
result_not = Fr_rawNot(0, pRawA)
print(f"按位取反操作结果: {hex(result_not)}")
