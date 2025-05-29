import sys


from CircuitVerify.CircuitManager import CircuitManager
from Elements.Directory.FrElementModel import *
from SupportForTest.TestSupporter import TestSupporter
from Tools.ColorPrint import *


# demo_name: name of the ast file in the form of json
# prime: the large prime that defines the finite field

# def run_demos():
#     # prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617
#     prime = 29
#
#     demo_name_list = ['array',
#                       'compare',
#                       'data2',
#                       'data3',
#                       'iszero',
#                       'parameters',
#                       'parameters2',
#                       'Powers',
#                       'simple',
#                       'simple2',
#                       'square',
#                       'raw',
#                       'generate',
#                       'signal2var',
#                       'ast']
#     passed_num = 0
#     for demo_name in demo_name_list:
#         ast_path = f'./demos/{demo_name}.json'
#         # 初始化求解器
#         exp_slv = ExpandedCVC5(prime)
#         outcome = CircuitManager.try_deal_ast(ast_path, exp_slv)
#         if outcome:
#             passed_num += 1
#
#     colorPrint('*********** DEMO REPORT ***********', COLOR.YELLOW)
#     colorPrint(f'Demos num  = {len(demo_name_list)}')
#     colorPrint(f'Passed num = {passed_num}')
#     colorPrint(f'Failed num = {len(demo_name_list) - passed_num}')
#     colorPrint('*********** REPORT ENDS ***********', COLOR.YELLOW)


# Test verify
# if __name__ == '__main__':
#     can_deal = False
#     raw_path = None
#
#     # now = datetime.now()
#     # formatted_now = now.strftime("_%Y_%m_%d_%H_%M_%S_%f")[:-3]
#
#     sys.argv = list()
#     sys.argv.append(0)
#     # sys.argv.append('../../Verify_CASES/bug/bug.circom')
#
#     sys.argv.append('../../Verify_CASES/Add/Add.circom')
#     sys.argv.append('bn128')
#     sys.argv.append('O1')
#
#     if len(sys.argv) == 2:
#         raw_path = sys.argv[1]
#         prime_name = 'bn128'
#         polish = 'O1'
#         can_deal = True
#     elif len(sys.argv) == 4:
#         raw_path = sys.argv[1]
#         prime_name = sys.argv[2]
#         polish = sys.argv[3]
#         can_deal = True
#     else:
#         colorPrint("Wrong Number of Parameters", color=COLOR.RED)
#         colorPrint("USAGE: Verify [raw circom file path] [the prime number]")
#
#     if can_deal:
#         # 初始化求解器
#         exp_slv = ExpandedCVC5(prime_name)
#         circuitManager_1 = CircuitManager(raw_path, exp_slv)
#
#         compile_passed = circuitManager_1.compile_case(polish, prime_name)
#
#         if compile_passed:
#             CircuitTerms = circuitManager_1.circuitTerms
#             colorPrint('The SMT statements of calculate terms:', COLOR.YELLOW)
#             colorPrint(CircuitTerms.calculate_terms)
#             colorPrint('The SMT statements of constraint terms:', COLOR.YELLOW)
#             colorPrint(CircuitTerms.constraint_terms)
#             colorPrint('The SMT statements of calculate terms after compilation:', COLOR.YELLOW)
#             colorPrint(CircuitTerms.compiled_calculate_terms)
#             colorPrint('The SMT statements of constraint terms after compilation:', COLOR.YELLOW)
#             colorPrint(CircuitTerms.compiled_constraint_terms)
#
#             # 比较编译后constraint的等价性
#             colorPrint(f'============ CHECKING CONSTRAINT ============', COLOR.GREEN)
#             constraint_compare_result = exp_slv.check_equality(exp_slv.associativeForm(CircuitTerms.constraint_terms),
#                                                                exp_slv.associativeForm(CircuitTerms.compiled_constraint_terms),
#                                                                list(CircuitTerms.signals_dic.values())
#                                                                )
#
#             colorPrint(f'constraint check passed: {constraint_compare_result}', COLOR.GREEN)
#
#             colorPrint()
#
#             # 求取一个可以满足的输入集合
#             colorPrint(f'============ SEEKING A VALUATION ============', COLOR.GREEN)
#             for term in CircuitTerms.calculate_terms:
#                 exp_slv.assertFormula(term)
#
#             for term in CircuitTerms.constraint_terms:
#                 exp_slv.assertFormula(term)
#
#             input_signal_list = list(CircuitTerms.main_component.get_input_signals_dic().values())
#             colorPrint('valuation found: ', end='', color=COLOR.GREEN)
#             exp_slv.get_model(input_signal_list, True)


# Test equivalence check
if __name__ == '__main__':
    raw_path_1 = '../../Test_CASES/Simple/raw.circom'
    raw_path_2 = '../../Test_CASES/Simple/generate.circom'

    prime_name = 'bn128'
    polish = 'O0'
    exp_slv = ExpandedCVC5(prime_name)
    circuitManager_1 = CircuitManager(raw_path_1, exp_slv)
    circuitManager_2 = CircuitManager(raw_path_2, exp_slv)

    compile1_pass = circuitManager_1.compile_case(polish, prime_name)
    compile2_pass = circuitManager_2.compile_case(polish, prime_name)

    if compile1_pass != compile2_pass:
        colorPrint(f'=== Inconsistent Compilation Pass Status ===', COLOR.RED)
    else:
        if not compile1_pass:
            colorPrint(f'=== Compilation failed For Both Circuits ===', COLOR.RED)
        else:
            colorPrint(f'============ CHECKING CIRCUIT PROPERTIES ============', COLOR.GREEN)
            colorPrint(f'****** {circuitManager_1.name} ******', COLOR.YELLOW)
            # correctness
            correctness_1 = circuitManager_1.check_correctness()
            colorPrint(f'correctness : {correctness_1}')
            # safety
            safety_1 = circuitManager_1.check_safety()
            colorPrint(f'safety : {safety_1}')
            # strongly_safety
            strong_safety_1 = circuitManager_1.check_strongly_safety()
            colorPrint(f'strongly safety : {strong_safety_1}')

            colorPrint(f'****** {circuitManager_2.name} ******', COLOR.YELLOW)
            # correctness
            correctness_2 = circuitManager_2.check_correctness()
            colorPrint(f'correctness : {correctness_2}')
            # safety
            safety_2 = circuitManager_2.check_safety()
            colorPrint(f'safety : {safety_2}')
            # strongly_safety
            strong_safety_2 = circuitManager_2.check_strongly_safety()
            colorPrint(f'strongly safety : {strong_safety_2}')


            outcome = TestSupporter.equivalence_check(circuitManager_1, circuitManager_2, exp_slv)
            colorPrint(f'============ CHECKING DOMAIN EQUIVALENCE ============', COLOR.GREEN)
            print(outcome[0])
            colorPrint(f'============ CHECKING CONSTRAINT EQUIVALENCE ============', COLOR.GREEN)
            print(outcome[1])
            colorPrint(f'============ CHECKING CALCULATE EQUIVALENCE ============', COLOR.GREEN)
            print(outcome[2])




