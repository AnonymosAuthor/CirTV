from Elements.Circuit.BuildinWords import CBW
from Tools.Check import TypeCheck


class Template:
    # template name (str) --> template
    __template_dic = None

    @staticmethod
    def init_definitions(js_definitions):
        Template.__template_dic = dict()
        for item in js_definitions:
            if CBW.Template.value in item:
                js_template = item[CBW.Template.value]
                template = Template(js_template)
                Template.__template_dic[template.get_name()] = template


    @staticmethod
    def get_Template(name):
        TypeCheck(str, name)
        return Template.__template_dic[name]

    def __init__(self, js_template):
        self.__name = js_template[CBW.name.value]
        self.__body = js_template[CBW.body.value]
        self.__args = js_template[CBW.args.value]
        self.__component_num = 0

    def get_name(self):
        return self.__name

    def get_body(self):
        return self.__body

    def prepare_build_component(self):
        suffix = f'[{self.__component_num}]'
        self.__component_num += 1
        return suffix

    def get_component_num(self):
        return self.__component_num

    def get_block(self):
        return self.__body[CBW.Block.value]

    # return args
    def get_args(self):
        return self.__args
