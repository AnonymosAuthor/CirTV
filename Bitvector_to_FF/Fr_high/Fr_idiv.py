def Fr_idiv(r, a, b):
    # Perform floor division
    quotient = a // b

    # Check if quotient fits within signed int range (-2^31 to 2^31 - 1)
    signed_int_min = -2 ** 31
    signed_int_max = 2 ** 31 - 1

    if signed_int_min <= quotient <= signed_int_max:
        is_l = 0
    else:
        is_l = 1

    # Store the quotient in r
    r = quotient

    return r, is_l


# Example usage
r = 0  # To store the result
a = 10 ** 18
b = 3
r, is_l = Fr_idiv(r, a, b)

print(f"Quotient: {r}, is_l: {is_l}")
