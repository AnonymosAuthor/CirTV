def Fr_pow(r, a, b, q):
    # Calculate a raised to the power of b, and then take modulo q
    result = pow(a, b, q)

    # Check if result fits within signed int range (-2^31 to 2^31 - 1)
    signed_int_min = -2 ** 31
    signed_int_max = 2 ** 31 - 1

    if signed_int_min <= result <= signed_int_max:
        is_l = 0
    else:
        is_l = 1

    # Store the result in r
    r[0] = result

    return is_l


# Example usage
r = [0]  # To store the result
a = 2
b = 10
q = 21888242871839275222246405745257275088548364400416034343698204186575808495617

is_l = Fr_pow(r, a, b, q)

print(f"Result: {r[0]}, is_l: {is_l}")
