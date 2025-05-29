def deal_dat(dat_path):
    file = open(dat_path, 'rb')
    content = file.read()
    file.close()
    num = content[-40:]
    short = num[0:4]
    type = num[4:8]
    long = num[8:]

    short_value = int.from_bytes(short, byteorder='little', signed=False)
    print(hex(short_value))

    type_value = int.from_bytes(type, byteorder='little', signed=False)
    print(hex(type_value))
    if_long = bool(type_value & (1 << 31))
    if_mong = bool(type_value & (1 << 30))

    print(f'if_long = {if_long}')
    print(f'if_mong = {if_mong}')

    long_value_0 = int.from_bytes(long[0:8], byteorder='little', signed=False)
    long_value_1 = int.from_bytes(long[8:16], byteorder='little', signed=False)
    long_value_2 = int.from_bytes(long[16:24], byteorder='little', signed=False)
    long_value_3 = int.from_bytes(long[24:32], byteorder='little', signed=False)

    long_value = long_value_3
    long_value = (long_value << 64) + long_value_2
    long_value = (long_value << 64) + long_value_1
    long_value = (long_value << 64) + long_value_0
    print(hex(long_value))
