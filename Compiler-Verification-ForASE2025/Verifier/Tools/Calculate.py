from Elements.Circuit.BuildinWords import EIO, EPO
from Tools.ColorPrint import colorPrint, COLOR
from Tools.Errors import UnSupportedOperators


def calculate_deterministic_infixOp(left, op, right, prime):
    if op == EIO.Add.value:
        return (left + right) % prime
    elif op == EIO.Sub.value:
        return (left - right) % prime
    elif op == EIO.Mul.value:
        return (left * right) % prime
    elif op == EIO.Div.value:
        rev = pow(right, -1, prime)
        return (left * rev) % prime
        # return (left // right) % prime
    elif op == EIO.IntDiv.value:
        return left // right
    elif op == EIO.Mod.value:
        return (left % right) % prime
    elif op == EIO.Pow.value:
        # return (left ** right) % prime
        return pow(left, right, prime)
    elif op == EIO.Lesser.value:
        return val(left, prime) < val(right, prime)
    elif op == EIO.LesserEq.value:
        return val(left, prime) <= val(right, prime)
    elif op == EIO.Greater.value:
        return val(left, prime) > val(right, prime)
    elif op == EIO.GreaterEq.value:
        return val(left, prime) >= val(right, prime)
    elif op == EIO.Eq.value:
        return val(left, prime) == val(right, prime)
    elif op == EIO.NotEq.value:
        return val(left, prime) != val(right, prime)
    elif op == EIO.ShiftR.value:
        return shift_right(left, right, prime)
    elif op == EIO.ShiftL.value:
        return shift_left(left, right, prime)
    elif op == EIO.BitAnd.value:
        return (left & right) % prime
    elif op == EIO.BitOr.value:
        return (left | right) % prime
    elif op == EIO.BitXor.value:
        return (left ^ right) % prime
    elif op == EIO.BoolAnd.value:
        return left and right
    elif op == EIO.BoolOr.value:
        return left or right
    else:
        colorPrint(f'WARNING: meet currently unsupported infix operator: {op}', COLOR.PURPLE)
        UnSupportedOperators()


def calculate_deterministic_prefixOp(op, right, prime):
    if op == EPO.Sub.value:
        return (-right) % prime
    elif op == EPO.BoolNot.value:
        return not right
    elif op == EPO.Complement.value:
        m = prime.bit_length()
        all_ones = (1 << m) - 1
        complement = all_ones - right
        return complement % prime
    else:
        colorPrint(f'WARNING: meet currently unsupported prefix operator: {op}', COLOR.PURPLE)
        UnSupportedOperators()


def shift_right(x, k, p):
    b = (p - 1).bit_length()  # 计算p的有效位数
    mask = (1 << b) - 1  # 计算掩码

    if 0 <= k <= p // 2:
        return x // (1 << k)  # x >> k
    elif p // 2 + 1 <= k < p:
        return (x * (1 << (p - k)) & mask) % p  # x << (p - k)


def shift_left(x, k, p):
    b = (p - 1).bit_length()
    mask = (1 << b) - 1

    if 0 <= k <= p // 2:
        return (x * (1 << k) & mask) % p  # x << k
    elif p // 2 + 1 <= k < p:
        return x // (1 << (p - k))  # x >> (p - k)


def val(raw, prime):
    if prime + 2 <= raw * 2 <= prime * 2:
        return raw - prime
    else:
        return raw


def arrangeNumber(array, prime):
    outcome = 0
    i = 0
    for item in reversed(array):
        outcome = outcome + item
        i = i + 1
        if i < len(array):
            outcome = outcome << 32
    return outcome % prime
