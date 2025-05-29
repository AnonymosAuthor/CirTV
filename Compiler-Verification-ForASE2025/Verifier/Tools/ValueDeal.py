from Tools.Check import TypeCheck
from Tools.Errors import MyNumError


# 大小端调整
def reverse_pairs(s):
    TypeCheck(str, s)
    s = s.replace(' ', '')
    if len(s) % 2 != 0:
        MyNumError("输入的字符串长度必须为偶数")

    reversed_str = ''
    for i in range(len(s), 0, -2):
        reversed_str += s[i-2] + s[i-1]

    return int(reversed_str, 16)
