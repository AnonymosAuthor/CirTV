from Tools.Errors import *


def TypeCheck(wanted_type, got_sample):
    if type(wanted_type) is not type:
        MyTypeError(type, type(wanted_type))
    if type(got_sample) is not wanted_type:
        MyTypeError(wanted_type, type(got_sample))


def EnumCheck(enum, element):
    if not isinstance(element, enum):
        MyEnumError(enum, element)

