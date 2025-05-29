from Elements.Circuit.BuildinWords import CBW
from Tools.Check import TypeCheck


class Function:
    __function_dic = None

    @staticmethod
    def init_definitions(js_definitions):
        Function.__function_dic = dict()
        for item in js_definitions:
            if CBW.Function.value in item:
                js_function = item[CBW.Function.value]
                function = Function(js_function)
                Function.__function_dic[function.get_name()] = function

    @staticmethod
    def get_Function(name):
        TypeCheck(str, name)
        return Function.__function_dic[name]

    def __init__(self, js_function):
        self.__name = js_function[CBW.name.value]
        self.__body = js_function[CBW.body.value]
        self.__args = js_function[CBW.args.value]
        self.__called_times = 0

    def prepare_call_function(self):
        suffix = f'[{self.__called_times}]'
        self.__called_times += 1
        return suffix

    def get_called_times(self):
        return self.__called_times

    def get_name(self):
        return self.__name

    def get_body(self):
        return self.__body

    def get_block(self):
        return self.__body[CBW.Block.value]

    # return args
    def get_args(self):
        return self.__args
