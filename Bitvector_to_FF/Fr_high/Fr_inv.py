def Fr_inv(r, a, q):
    try:
        # Calculate modular inverse of a mod q
        inverse = pow(a, -1, q)

        # Check if inverse fits within signed int range (-2^31 to 2^31 - 1)
        signed_int_min = -2 ** 31
        signed_int_max = 2 ** 31 - 1

        if signed_int_min <= inverse <= signed_int_max:
            is_l = 0
        else:
            is_l = 1

        # Store the inverse in r
        r[0] = inverse

        return is_l

    except ValueError:
        # Modular inverse does not exist
        return 0


# Example usage
r = [0]  # To store the result
a = 3
q = 21888242871839275222246405745257275088548364400416034343698204186575808495617

is_l = Fr_inv(r, a, q)

print(f"Modular Inverse: {r[0]}, is_l: {is_l}")
