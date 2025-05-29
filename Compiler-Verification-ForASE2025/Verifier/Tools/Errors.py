def MyTypeError(wanted_type, got_type):
    if type(wanted_type) is not type:
        raise TypeError(MyTypeError(type, type(wanted_type)))
    if type(got_type) is not type:
        raise TypeError(MyTypeError(type, type(got_type)))
    raise TypeError(f"TypeError! want:{wanted_type} get:{got_type}")


def MyEnumError(enum, element):
    raise TypeError(f"TypeError! {element} is not an element of {enum}")


def MyItemError(item_name):
    raise ValueError(f"unsolved item :! {item_name}")


def MyNoneError(stmt):
    raise ValueError(f"{stmt} should not be None!")


def MyNumError(stmt):
    raise ValueError(f"{stmt}")


def MyUnCompiledError(name):
    raise FileExistsError(f"{name} have not been compiled!")

def UnSupportedOperators():
    raise f'meet currently unsupported signal operator'
