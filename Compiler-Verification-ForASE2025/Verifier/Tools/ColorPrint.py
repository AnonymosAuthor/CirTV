from abc import ABC


class COLOR(ABC):
    DEFAULT = 0
    BLACK = 30
    RED = 31
    GREEN = 32
    YELLOW = 33
    BLUE = 34
    PURPLE = 35
    CYAN = 36
    WHITE = 37


def colorPrint(txt='', color=COLOR.DEFAULT, end='\n'):
    print(f'\033[{color}m{txt}\033[{COLOR.DEFAULT}m', end=end)
    return colorPrint
