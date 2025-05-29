import numpy as np

# 定义常量
Fr_N64 = 4  # 4个64位字
lboMask = 0x3fffffffffffffff  # 用于屏蔽最后的64位

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

# 左移操作
def Fr_rawShl(r, a, b):
    bit_shift = b % 64
    word_shift = b // 64
    word_count = Fr_N64 - word_shift

    # 将a转换为64位块列表
    a_blocks = to_uint64_list(a)
    r_blocks = [0] * Fr_N64

    # 复制a的高位到r中
    r_blocks[word_shift:] = a_blocks[:word_count]

    # 如果需要位移
    if bit_shift:
        num = from_uint64_list(r_blocks)
        num <<= bit_shift
        r_blocks = to_uint64_list(num)

    # 屏蔽最后一块
    r_blocks[3] &= lboMask

    # 检查是否需要模减法
    r_value = from_uint64_list(r_blocks)
    Fr_rawq = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
    if r_value >= Fr_rawq:
        r_value -= Fr_rawq

    # 将结果转换为64位块列表
    r_blocks = to_uint64_list(r_value)

    # 返回结果
    return from_uint64_list(r_blocks)

# 右移操作
def Fr_rawShr(r, a, b):
    bit_shift = b % 64
    word_shift = b // 64
    word_count = Fr_N64 - word_shift

    # 将a转换为64位块列表
    a_blocks = to_uint64_list(a)
    r_blocks = [0] * Fr_N64

    # 复制a的低位到r中
    r_blocks[:word_count] = a_blocks[word_shift:]

    # 如果需要位移
    if bit_shift:
        num = from_uint64_list(r_blocks)
        num >>= bit_shift
        r_blocks = to_uint64_list(num)

    # 返回结果
    return from_uint64_list(r_blocks)

# 测试
a = 0x123456789ABCDEF123456789ABCDEF123456789ABCDEF123456789ABCDEF1234  # 示例256位整数
b = 72  # 需要左移或右移的位数
r = 0  # 结果初始化

# 左移
r_shl = Fr_rawShl(r, a, b)
print(f"左移结果: {hex(r_shl)}")

# 右移
r_shr = Fr_rawShr(r, a, b)
print(f"右移结果: {hex(r_shr)}")
