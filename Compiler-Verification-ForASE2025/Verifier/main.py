import argparse
import time

from CircuitVerify.CircuitManager import CircuitManager
from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Circuit.Signal import Signal
from Tools.ColorPrint import colorPrint, COLOR

def run_case(raw_path, prime_name='bn128', polish='O0'):
    prime_name = 'bn128'
    polish = 'O0'
    exp_slv = ExpandedCVC5(prime_name)

    circuitManager = CircuitManager(raw_path, exp_slv)
    compile_pass = circuitManager.compile_case(polish, prime_name)

    if compile_pass:
        # colorPrint(f'-- CHECKING CIRCUIT PROPERTIES --', COLOR.YELLOW)

        # 用于检查circom源代码的安全性和正确性的代码
        # # correctness
        # correctness = circuitManager.check_correctness()
        # colorPrint(f'correctness : {correctness}')
        # # safety
        # safety = circuitManager.check_safety()
        # colorPrint(f'safety : {safety}')
        # # strongly_safety
        # strong_safety = circuitManager.check_strongly_safety()
        # colorPrint(f'strongly safety : {strong_safety}')

        start_time = time.time()  # 记录开始时间

        colorPrint(f'-- CHECKING COMPILER CORRECTNESS --', COLOR.YELLOW)
        print(f'total signal num : {Signal.total_num}')
        constraint_equality = circuitManager.check_constraint_equality()
        colorPrint(f'constraint_equality : {constraint_equality}')

        end_time = time.time()  # 记录结束时间
        elapsed_time = end_time - start_time

        print(f'Constraint Equivalence Checking Time: {elapsed_time:.4f} s')

        start_time = time.time()  # 记录开始时间
        calculate_equality = circuitManager.check_calculate_equality(with_m=True)
        colorPrint(f'calculate_equality : {calculate_equality}')
        end_time = time.time()  # 记录结束时间
        elapsed_time = end_time - start_time

        print(f'Calculation Equivalence Checking Time: {elapsed_time:.4f} s')


if __name__ == '__main__':
    # raw_path = '../../Verify_CASES/while/while.circom'
    # raw_path = '../../Verify_CASES/func/func.circom'
    # raw_path = '../../Verify_CASES/SignalArray/SignalArray.circom'
    # raw_path = '../../Verify_CASES/SingalInFunction/singalFunc.circom'
    # raw_path = '../../Verify_CASES/CircomLib/circuits/eddsa.circom'
    # raw_path = '../../Verify_CASES/while/while.circom'
    # raw_path = '../../Verify_CASES/sha256/sha.circom'
    # raw_path = '../../Verify_CASES/RandomGenerated/bugs/bug1.circom'
    # raw_path = '../../Verify_CASES/funcArray/funcArray.circom'
    # raw_path = '/home/zeno/Desktop/RandomGenerate/tbcctfiw/temp/success22.circom'
    # raw_path = '../../Verify_CASES/CircomLib/test.circom'
    # raw_path = '../../Verify_CASES/Optimization/second.circom'

    # raw_path = '/home/zeno/Desktop/BlockChain/OurTools/Compiler-Verification/knownBugs/A.circom'

    # raw_path = '/home/zeno/Desktop/BlockChain/OurTools/CompilerVerification/Verify_CASES/circomlib-master/circomlib-master/circuits/aatest.circom'

    # raw_path = '/home/zeno/Desktop/BlockChain/OurTools/Compiler-Verification/TempCases/aboutBenchmarks/temp.circom'

    # run_case(raw_path=raw_path)
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Process cases with configurable parameters.')

    # Required positional argument for file path
    parser.add_argument('file_path', type=str, help='Path to the input file')

    # Optional arguments with default values
    parser.add_argument('--polish', '-p',
                        choices=['O0', 'O1', 'O2'],
                        default='O0',
                        help='Optimization level (O0, O1, O2)')

    parser.add_argument('--prime', '-n',
                        default='bn128',
                        help='Elliptic curve name (default: bn128)')

    # Parse arguments
    args = parser.parse_args()

    # Run the case with provided or default arguments
    run_case(
        raw_path=args.file_path,
        prime_name=args.prime,
        polish=args.polish
    )

