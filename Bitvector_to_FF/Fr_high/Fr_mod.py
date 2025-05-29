def Fr_mod(r, a, b):
    # Perform floor division remainder (non-negative)
    remainder = a % b

    # If the remainder is negative, adjust it to be non-negative
    if remainder < 0:
        remainder += abs(b)

    # Store the remainder in r
    r = remainder

    # Check if quotient fits within signed int range (-2^31 to 2^31 - 1)
    signed_int_min = -2 ** 31
    signed_int_max = 2 ** 31 - 1

    if signed_int_min <= remainder <= signed_int_max:
        is_l = 0
    else:
        is_l = 1

    return r, is_l

# Example usage
r = 0  # To store the result
a = -7
b = 3
r, is_l = Fr_mod(r, a, b)

print(f"Remainder: {r}, is_l: {is_l}")
