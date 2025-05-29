from CircuitVerify.CircuitManager import CircuitManager
from Convert.AdditionalOperations import ExpandedCVC5

if __name__ == '__main__':
    ast_path = 'temp_file/batchverify/ast.json'

    prime_name = 'bn128'
    polish = 'O0'
    exp_slv = ExpandedCVC5(prime_name)

    CircuitManager.deal_ast(ast_path, exp_slv)
