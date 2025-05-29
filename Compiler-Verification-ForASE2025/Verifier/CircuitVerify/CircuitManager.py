import json
import os
import shutil
import subprocess
import re
import time

from cvc5 import Kind

from Convert.FrFunction import FrFunction
from Elements.Circuit.BuildinWords import CBW
from Elements.Circuit.Component import Component
from Elements.Circuit.Function import Function
from Elements.Circuit.Signal import SignalTypes, Signal
from Elements.Circuit.Template import Template
from Elements.Directory.FrElementModel import FrElementModel
from OutcomeDeal.ConstranitsDeal import ConstraintsDealer
from Tools.ColorPrint import colorPrint, COLOR
from Tools.DealSym import SymDataDic
from Tools.Errors import MyUnCompiledError, MyEnumError


class CircuitTerms:
    def __init__(self, main_component, compiled_calculate_terms, compiled_constraint_terms,
                 compiled_constraint_terms_independent, variable_dic):
        self.main_component = main_component
        self.input_signals_dic = main_component.get_input_signals_dic()
        self.output_signals_dic = main_component.get_output_signals_dic()
        self.all_signals_dic = main_component.get_all_signals_dic()
        self.calculate_terms = main_component.get_all_calculate_terms()
        self.constraint_terms = main_component.get_all_constraint_terms()
        self.compiled_calculate_terms = compiled_calculate_terms
        self.compiled_constraint_terms = compiled_constraint_terms
        self.compiled_constraint_terms_independent = compiled_constraint_terms_independent
        self.variable_dic = variable_dic



'''
用于管理Circom代码的类，每一个类对象维护一个circom电路实例
包含：
raw_path 原始路径
circuit_name 名称
case_temp_path 临时文件路径
exp_slv 求解器对象
information 约束信息
'''


class CircuitManager:
    temp_file_dir = './temp_file'
    ast_builder_path = './dependence/AstBuilder'
    compiler_path = './dependence/circom'
    polish_list = ['O0', 'O1', '02', 'O3']

    @staticmethod
    def set_temp_file_dir(path):
        CircuitManager.temp_file_dir = path

    @staticmethod
    def set_ast_builder_path(path):
        CircuitManager.ast_builder_path = path

    @staticmethod
    def set_compiler_path(path):
        CircuitManager.compiler_path = path

    def __init__(self, raw_path, exp_slv):
        self.__raw_path = raw_path
        self.__circuit_name = os.path.splitext(os.path.basename(raw_path))[0]
        self.__case_temp_path = f'{CircuitManager.temp_file_dir}/{self.__circuit_name}'
        self.__exp_slv = exp_slv
        # 检查临时文件夹是否存在，不存在就创建
        if not os.path.exists(CircuitManager.temp_file_dir) or not os.path.isdir(CircuitManager.temp_file_dir):
            os.makedirs(CircuitManager.temp_file_dir)
        self.__compiled = False
        self.__information = None
        self.__input_signals = None
        self.__output_signals = None
        self.__inter_signals = None
        self.__fr_element_dic = None
        self.__all_smt = set()
        self.component_num = None
        self.constraints_num = None
        self.polish_level = self.polish_list[0]
        colorPrint(f'=============== {self.__circuit_name} ===============', COLOR.GREEN)

    @property
    def name(self):
        return self.__circuit_name

    def comp_constraint_num(self, cpp_path):
        with open(cpp_path, 'r') as file:
            for line in file:
                # 匹配 get_number_of_components 并提取数字
                match_components = re.match(r'uint get_number_of_components\(\) \{return (\d+);\}', line)
                if match_components:
                    self.component_num = int(match_components.group(1))

                # 匹配 get_size_of_constants 并提取数字
                match_constants = re.match(r'uint get_size_of_constants\(\) \{return (\d+);\}', line)
                if match_constants:
                    self.constraints_num = int(match_constants.group(1))
                    # 终止文件解析
                    break

    def __pick_information(self):
        # 生成 ast
        colorPrint('-- GENERATING AST FILE --', COLOR.YELLOW)
        start_time = time.time()  # 记录开始时间
        ast_path = f'{self.__case_temp_path}/ast.json'
        build_ast_cmd = [CircuitManager.ast_builder_path, self.__raw_path, ast_path]
        subprocess.run(build_ast_cmd)
        end_time = time.time()  # 记录结束时间
        elapsed_time = end_time - start_time
        print(f'AST Generating Time: {elapsed_time:.4f} s')

        # 处理 ast
        start_time = time.time()  # 记录开始时间
        main_component = CircuitManager.deal_ast(ast_path, self.__exp_slv)
        end_time = time.time()  # 记录结束时间
        elapsed_time = end_time - start_time
        print(f'AST Processing Time: {elapsed_time:.4f} s')

        self.__input_signals = set(main_component.get_input_signals_dic().values())
        self.__output_signals = set(main_component.get_output_signals_dic().values())
        self.__inter_signals = set(main_component.get_all_signals_dic().values()) - self.__input_signals - self.__output_signals

        # 读取sym文件
        colorPrint(f'-- DEALING SYM FILE --', COLOR.YELLOW)
        sym_path = f'{self.__case_temp_path}/{self.__circuit_name}.sym'
        all_signals = list(main_component.get_all_signals_dic().values())
        sym_data_dic = SymDataDic(sym_path, all_signals, self.__exp_slv.FF_number(1))

        # 读取constraint文件，即json格式的R1CS
        start_time = time.time()  # 记录开始时间
        cons_path = f'{self.__case_temp_path}/{self.__circuit_name}_constraints.json'
        cons_dealer = ConstraintsDealer(cons_path, self.__exp_slv, sym_data_dic)
        # 获取编译后的constraint约束
        colorPrint(f'-- DEALING R1CS FILE --', COLOR.YELLOW)
        compiled_constraint_terms = cons_dealer.get_all_terms()
        compiled_constraint_terms_independent, variable_dic = cons_dealer.get_independent_terms()
        end_time = time.time()  # 记录结束时间
        elapsed_time = end_time - start_time
        print(f'R1CS Processing Time: {elapsed_time:.4f} s')


        # 读取cpp文件
        start_time = time.time()  # 记录开始时间
        cpp_path = f'{self.__case_temp_path}/{self.__circuit_name}_cpp/{self.__circuit_name}.cpp'
        # 读取dat文件
        dat_path = f'{self.__case_temp_path}/{self.__circuit_name}_cpp/{self.__circuit_name}.dat'
        # 获取编译后的计算约束
        colorPrint(f'-- DEALING CPP FILES --', COLOR.YELLOW)
        ccp_dealer = FrFunction(self.__exp_slv)
        self.comp_constraint_num(cpp_path)
        ccp_dealer.deal_dat(dat_path=dat_path, num=self.constraints_num)
        ccp_dealer.directory_2_smt(sym_path, cpp_path, self.component_num)
        # print(1111111111111111)
        # print(ccp_dealer.directory_terms)
        # print(1111111111111111)
        # print(ccp_dealer.element_dict)
        compiled_calculate_terms = ccp_dealer.directory_terms
        end_time = time.time()  # 记录结束时间
        elapsed_time = end_time - start_time
        print(f'C++ Processing Time: {elapsed_time:.4f} s')

        self.__fr_element_dic = ccp_dealer.element_dict

        self.__all_smt.update(set(variable_dic.values()))
        self.__all_smt.update(set(variable_dic.keys()))

        self.__information = CircuitTerms(main_component,
                                          compiled_calculate_terms,
                                          compiled_constraint_terms,
                                          compiled_constraint_terms_independent,
                                          variable_dic)
        return self.__information

    @property
    def circuitTerms(self):
        if self.__compiled:
            return self.__information
        else:
            raise MyUnCompiledError(self.__circuit_name)

    def compile_case(self, polish, prime_name):
        self.polish_level = polish
        if os.path.exists(self.__case_temp_path) and os.path.isdir(self.__case_temp_path):
            shutil.rmtree(self.__case_temp_path)
        os.makedirs(self.__case_temp_path)

        colorPrint('-- COMPILING CIRCUIT --', COLOR.YELLOW)
        compile_cmd = [CircuitManager.compiler_path, f'--{polish}', self.__raw_path, '--prime', prime_name, '--r1cs',
                       '--sym',
                       '--c', '--json', '-o', self.__case_temp_path]
        result = subprocess.run(compile_cmd, capture_output=True, text=True)
        if result.returncode == 0:
            print(result.stdout, end='')
            self.__compiled = True
            # 这里进行了操作
            self.__pick_information()
            return True
        else:
            print(result.stderr, end='')
            return False

    def generate_mapping_property(self, with_m):
        input_terms = list()
        other_terms = list()
        for signal in self.__information.all_signals_dic.values():
            if signal.sym_name in self.__fr_element_dic:
                element = self.__fr_element_dic[signal.sym_name]
                # 这里注意，看看是否需要把蒙哥马利的情况考虑在内
                if with_m:
                    term = self.generate_element_property_with_m(signal, element)
                else:
                    term = self.generate_element_property_without_m(signal, element)
                if signal.signal_type == SignalTypes.Input:
                    input_terms.append(term)
                else:
                    other_terms.append(term)
        return input_terms, other_terms

    # 考虑了蒙哥马利的情况
    def generate_element_property_with_m(self, signal: Signal, element: FrElementModel):
        s_eq = self.__exp_slv.mkTerm(Kind.EQUAL, signal.toSmt(), element.s_v)
        l_eq = self.__exp_slv.mkTerm(Kind.EQUAL, signal.toSmt(), element.l_v)
        m_value = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, signal.toSmt(), self.__exp_slv.R())
        m_eq = self.__exp_slv.mkTerm(Kind.EQUAL, m_value, element.l_v)

        n = self.__exp_slv.mkTerm(Kind.NOT, element.is_m)
        m = element.is_m
        s = self.__exp_slv.mkTerm(Kind.NOT, element.is_l)
        l = element.is_l

        sn = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, s, n), s_eq)
        sm = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, s, m), self.__exp_slv.mkTerm(Kind.AND, s_eq, m_eq))
        ln = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, l, n), l_eq)
        lm = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, l, m), m_eq)

        # s_case = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, not_m, not_l), s_eq)
        # l_case = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, not_m, element.is_l), l_eq)
        # m_case = self.__exp_slv.mkTerm(Kind.IMPLIES, element.is_m, m_eq)
        return self.__exp_slv.mkTerm(Kind.AND, sn, sm, ln, lm)

    # 不考虑蒙哥马利的情况
    def generate_element_property_without_m(self, signal: Signal, element: FrElementModel):
        s_eq = self.__exp_slv.mkTerm(Kind.EQUAL, signal.toSmt(), element.s_v)
        l_eq = self.__exp_slv.mkTerm(Kind.EQUAL, signal.toSmt(), element.l_v)

        not_l = self.__exp_slv.mkTerm(Kind.NOT, element.is_l)

        s_case = self.__exp_slv.mkTerm(Kind.IMPLIES, not_l, s_eq)
        l_case = self.__exp_slv.mkTerm(Kind.IMPLIES, element.is_l, l_eq)

        if signal.signal_type is SignalTypes.Input:
            not_m = self.__exp_slv.mkTerm(Kind.EQUAL, element.is_m, self.__exp_slv.Boolean_False())
            return self.__exp_slv.mkTerm(Kind.AND, s_case, l_case, not_m)
        else:
            m_value = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, signal.toSmt(), self.__exp_slv.R())
            m_case = self.__exp_slv.mkTerm(Kind.EQUAL, m_value, element.l_v)
            lm = self.__exp_slv.mkTerm(Kind.IMPLIES, element.is_m, m_case)
            is_n = self.__exp_slv.mkTerm(Kind.NOT, element.is_m)
            n = self.__exp_slv.mkTerm(Kind.AND, l_case, s_case)
            n_case = self.__exp_slv.mkTerm(Kind.IMPLIES, is_n, n)
            return self.__exp_slv.mkTerm(Kind.AND, lm, n_case)
            # return self.__exp_slv.mkTerm(Kind.AND, s_case, l_case)

    def check_correctness(self):
        # pre = self.__exp_slv.associativeForm(self.__information.calculate_terms)
        # suf = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms)
        # return self.__exp_slv.check_implies(pre, suf)
        input_eq = self.__exp_slv.associativeForm(self.__build_variable_equal_terms(SignalTypes.Input))
        witness = self.__exp_slv.associativeForm(self.__information.calculate_terms)
        r1cs = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms)
        r1cs_ = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms_independent)
        imply_1 = self.__exp_slv.mkTerm(Kind.IMPLIES, self.__exp_slv.mkTerm(Kind.AND, input_eq, r1cs_), witness)
        imply_2 = self.__exp_slv.mkTerm(Kind.IMPLIES, witness, r1cs)
        exp = self.__exp_slv.mkTerm(Kind.IMPLIES, imply_1, imply_2)
        not_exp = self.__exp_slv.mkTerm(Kind.NOT, exp)
        return not self.__exp_slv.check_satisfy(not_exp)

    def __build_variable_equal_terms(self, sigal_type):
        if sigal_type == SignalTypes.Input:
            signal_set = self.__input_signals
        elif sigal_type == SignalTypes.Output:
            signal_set = self.__output_signals
        elif sigal_type == SignalTypes.Intermediate:
            signal_set = self.__inter_signals
        else:
            raise MyEnumError(sigal_type, SignalTypes)
        terms = list()
        for signal in signal_set:
            signal_smt = signal.toSmt()
            # 有可能在R1CS中，某些变量被编译器优化掉了
            if signal_smt not in self.__information.variable_dic:
                continue
            variable = self.__information.variable_dic[signal_smt]
            term = self.__exp_slv.mkTerm(Kind.EQUAL, signal_smt, variable)
            terms.append(term)
        return terms

    def check_safety(self):
        input_eq = self.__exp_slv.associativeForm(self.__build_variable_equal_terms(SignalTypes.Input))
        output_eq = self.__exp_slv.associativeForm(self.__build_variable_equal_terms(SignalTypes.Output))
        witness = self.__exp_slv.associativeForm(self.__information.calculate_terms)
        r1cs = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms)
        r1cs_ = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms_independent)
        not_output_eq = self.__exp_slv.mkTerm(Kind.NOT, output_eq)
        exp = self.__exp_slv.mkTerm(Kind.AND, witness, r1cs, input_eq, not_output_eq, r1cs_)
        return not self.__exp_slv.check_satisfy(exp)

    def check_strongly_safety(self):
        input_eq = self.__exp_slv.associativeForm(self.__build_variable_equal_terms(SignalTypes.Input))
        output_eq = self.__exp_slv.associativeForm(self.__build_variable_equal_terms(SignalTypes.Output))
        inter_eq = self.__exp_slv.associativeForm(self.__build_variable_equal_terms(SignalTypes.Intermediate))
        witness = self.__exp_slv.associativeForm(self.__information.calculate_terms)
        r1cs = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms)
        r1cs_ = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms_independent)
        not_output_inter_eq = self.__exp_slv.mkTerm(Kind.NOT, self.__exp_slv.mkTerm(Kind.AND, inter_eq, output_eq))
        exp = self.__exp_slv.mkTerm(Kind.AND, witness, r1cs, input_eq, not_output_inter_eq, r1cs_)
        # print(exp)
        return not self.__exp_slv.check_satisfy(exp)

    def check_constraint_equality(self):
        num1 = len(self.__information.constraint_terms)
        num2 = len(self.__information.compiled_constraint_terms)
        # print(f'====================================')
        print(f'circom code constraint num : {num1}')
        print(f'R1CS constraint num : {num2}')
        # print(f'====================================')

        circom_constraint = self.__exp_slv.associativeForm(self.__information.constraint_terms)
        compiled_constraint = self.__exp_slv.associativeForm(self.__information.compiled_constraint_terms)

        # colorPrint('--- detailed constraints ---', COLOR.GREEN)
        # print(circom_constraint)
        # print()
        # print(compiled_constraint)
        # colorPrint('--- detailed constraints ---', COLOR.GREEN)

        # for item in self.__information.constraint_terms:
        #     print(item)
        #
        # print()
        # for item in self.__information.compiled_constraint_terms:
        #     print(item)

        if self.polish_level == self.polish_list[0]:
            return self.__exp_slv.check_equality(circom_constraint,
                                                 compiled_constraint,
                                                 list(self.__information.all_signals_dic.values())
                                                 )
        else:
            return self.__exp_slv.check_implies(circom_constraint,
                                                compiled_constraint,
                                                list(self.__information.all_signals_dic.values())
                                                )


    # 即验证输入相等，然后witness计算值相等
    def check_calculate_equality(self, with_m):
        input_terms, other_terms = self.generate_mapping_property(with_m)
        input_equal = self.__exp_slv.associativeForm(input_terms)
        witness_equal = self.__exp_slv.associativeForm(other_terms)
        circom_calculate = self.__exp_slv.associativeForm(self.__information.calculate_terms)
        compiled_calculate = self.__exp_slv.associativeForm(self.__information.compiled_calculate_terms)

        num1 = len(self.__information.calculate_terms)
        num2 = len(self.__information.compiled_calculate_terms)

        # print(f'====================================')
        print(f'circom code calculate num : {num1}')
        print(f'C++ calculate num : {num2}')
        # print(f'====================================')

        # colorPrint('--- detailed constraints ---', COLOR.GREEN)
        # print(input_equal)
        # print()
        # print(witness_equal)
        # print()
        # print(circom_calculate)
        # print()
        # print(compiled_calculate)

        # colorPrint('--- detailed constraints ---', COLOR.GREEN)

        all_SMTs = list()
        for signal in self.__information.all_signals_dic.values():
            all_SMTs.append(signal.toSmt())
        for element in self.__fr_element_dic.values():
            all_SMTs.append(element.is_m)
            all_SMTs.append(element.is_l)
            all_SMTs.append(element.s_v)
            all_SMTs.append(element.l_v)

        not_witness_eq = self.__exp_slv.mkTerm(Kind.NOT, witness_equal)

        # print(temp_eq)
        temp_exp = self.__exp_slv.mkTerm(Kind.AND, compiled_calculate, self.__exp_slv.mkTerm(Kind.NOT, not_witness_eq))
        # print(temp_exp)
        # return self.__exp_slv.check_satisfy(temp_exp, smt_list)

        exp = self.__exp_slv.mkTerm(Kind.AND, input_equal, circom_calculate, compiled_calculate, not_witness_eq)

        # print('exp is :')
        # print(exp)

        # self.__exp_slv.printAssertions()
        return not self.__exp_slv.check_satisfy(exp, all_SMTs)


        # return self.__exp_slv.check_implies_with_settings(input_equal, witness_equal, [circom_calculate, compiled_calculate], all_SMTs)

    # 即验证输入相等，然后witness可计算性一致
    def check_calculate_ability_equality(self, with_m):
        input_terms, other_terms = self.generate_mapping_property(with_m)
        input_equal = self.__exp_slv.associativeForm(input_terms)
        witness_equal = self.__exp_slv.associativeForm(other_terms)
        circom_calculate = self.__exp_slv.associativeForm(self.__information.calculate_terms)
        compiled_calculate = self.__exp_slv.associativeForm(self.__information.compiled_calculate_terms)

        


    @staticmethod
    def deal_ast(ast_path, exp_slv):
        # 打开JSON文件
        with open(ast_path, 'r') as f:
            # 加载JSON数据
            data = json.load(f)

        # 初始化Template
        js_definitions = data[CBW.definitions.value]
        Template.init_definitions(js_definitions)
        Function.init_definitions(js_definitions)

        # 获取main component
        colorPrint('-- DEALING AST FILE --', COLOR.YELLOW)
        # colorPrint(f'Signals and Vars:')

        js_main_component = data[CBW.main_component.value]
        main_component = Component.main_component(js_main_component, exp_slv)

        return main_component

    @staticmethod
    def try_deal_ast(ast_path, exp_slv):
        outcome = True
        colorPrint('=========== DEALING AST FILE ===========', COLOR.GREEN)
        colorPrint(f'AST PATH : {ast_path}', COLOR.YELLOW)

        try:
            CircuitManager.deal_ast(ast_path, exp_slv)
        except Exception as e:
            colorPrint('!!!!!!!! Exception Happened !!!!!!!!', COLOR.RED)
            colorPrint(e.with_traceback(None))
            outcome = False

        # colorPrint('=========== DEALING ENDS ===========', COLOR.GREEN)
        colorPrint()
        return outcome
