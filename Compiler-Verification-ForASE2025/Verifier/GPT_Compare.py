import json

from cvc5 import Kind

from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Circuit.BuildinWords import CBW
from Elements.Circuit.Component import Component
from Elements.Circuit.Template import Template
from Tools.ColorPrint import colorPrint, COLOR



def GPT_compare(raw, generate, prime):
    # 初始化求解器
    exp_slv = ExpandedCVC5(prime)

    colorPrint('===== START DEALING RAW CIRCOM =====', COLOR.GREEN)

    # 打开JSON文件
    with open(f'./demos/{raw}.json', 'r') as f:
        # 加载JSON数据
        raw_data = json.load(f)

    # 初始化Template
    raw_js_definitions = raw_data[CBW.definitions.value]
    Template.init_definitions(raw_js_definitions)

    # 获取main component
    raw_js_main_component = raw_data[CBW.main_component.value]
    raw_main_component = Component.main_component(raw_js_main_component, exp_slv)

    # 获取main component所对应约束
    raw_terms = raw_main_component.get_all_terms()

    # 输出
    colorPrint('The SMT statements of RAW circom:', COLOR.BLUE)
    colorPrint(raw_terms)

    colorPrint('===== START DEALING GENERATED CIRCOM =====', COLOR.GREEN)

    # 打开JSON文件
    with open(f'./demos/{generate}.json', 'r') as f:
        # 加载JSON数据
        gen_data = json.load(f)

    # 初始化Template
    gen_js_definitions = gen_data[CBW.definitions.value]
    Template.init_definitions(gen_js_definitions)

    # 获取main component
    gen_js_main_component = gen_data[CBW.main_component.value]
    gen_main_component = Component.main_component(gen_js_main_component, exp_slv)

    # 获取main component所对应约束
    gen_terms = gen_main_component.get_all_terms()

    # 输出
    colorPrint('The SMT statements of GENERATED circom:', COLOR.BLUE)
    colorPrint(gen_terms)

    # 所有约束
    raw_calculate = exp_slv.mkTerm(Kind.AND, *raw_terms)
    gen_calculate = exp_slv.mkTerm(Kind.AND, *gen_terms)

    # 生成约束
    input_equation, output_equation = generate_equation(exp_slv, raw_main_component, gen_main_component)
    cond = exp_slv.mkTerm(Kind.AND, input_equation, raw_calculate, gen_calculate)
    target = exp_slv.mkTerm(Kind.IMPLIES, cond, output_equation)
    neg_target = exp_slv.mkTerm(Kind.NOT, target)

    colorPrint('The target property is:', COLOR.GREEN)
    colorPrint(target)

    exp_slv.assertFormula(neg_target)

    all_signals = list()
    all_signals.extend(raw_main_component.get_all_signals())
    all_signals.extend(gen_main_component.get_all_signals())
    exp_slv.get_model(all_signals, True)

def generate_equation(exp_slv, raw_main_component, gen_main_component):
    raw_input_signals = raw_main_component.get_all_input_signals()
    raw_output_signals = raw_main_component.get_all_output_signals()
    gen_input_signals = gen_main_component.get_all_input_signals()
    gen_output_signals = gen_main_component.get_all_output_signals()

    input_list = list()
    for i in range(len(raw_input_signals)):
        raw_smt = raw_input_signals[i].toSmt()
        gen_smt = gen_input_signals[i].toSmt()
        input_list.append(exp_slv.mkTerm(Kind.EQUAL, raw_smt, gen_smt))
    input_equation = exp_slv.mkTerm(Kind.AND, *input_list)

    output_list = list()
    for i in range(len(raw_output_signals)):
        raw_smt = raw_output_signals[i].toSmt()
        gen_smt = gen_output_signals[i].toSmt()
        output_list.append(exp_slv.mkTerm(Kind.EQUAL, raw_smt, gen_smt))
    output_equation = exp_slv.mkTerm(Kind.AND, *output_list)

    return input_equation, output_equation


if __name__ == '__main__':
    prime = 29
    demo_group_dic = {'raw': ['generate']}
    for raw, generates in demo_group_dic.items():
        passed_num = 0
        for generate in generates:
            GPT_compare(raw, generate, prime)