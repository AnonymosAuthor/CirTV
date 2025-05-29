from cvc5 import Kind

from CircuitVerify.CircuitManager import CircuitManager, CircuitTerms
from Convert.AdditionalOperations import ExpandedCVC5
from Tools.ColorPrint import colorPrint, COLOR


class TestSupporter:
    @staticmethod
    def equivalence_check(circuitManager_1, circuitManager_2, exp_slv):
        circuitTerms1 = circuitManager_1.circuitTerms
        circuitTerms2 = circuitManager_2.circuitTerms

        calculate1 = exp_slv.associativeForm(circuitTerms1.calculate_terms)
        calculate2 = exp_slv.associativeForm(circuitTerms2.calculate_terms)

        R1CS_1 = exp_slv.associativeForm(circuitTerms1.compiled_constraint_terms)
        R1CS_2 = exp_slv.associativeForm(circuitTerms2.compiled_constraint_terms)

        input_1 = circuitTerms1.input_signals_dic
        input_2 = circuitTerms2.input_signals_dic
        input_equivalence = TestSupporter.build_io_equivalence(input_1, input_2, exp_slv)

        domain_equivalence = exp_slv.check_equality_with_settings(calculate1, calculate2, [input_equivalence])

        constraint_equivalence = exp_slv.check_equality_with_settings(R1CS_1, R1CS_2, [input_equivalence, calculate1, calculate2])

        output_1 = circuitTerms1.output_signals_dic
        output_2 = circuitTerms2.output_signals_dic
        output_equivalence = TestSupporter.build_io_equivalence(output_1, output_2, exp_slv)

        calculate_equivalence = exp_slv.check_implies_with_settings(input_equivalence,
                                                                    output_equivalence,
                                                                    [calculate1, calculate2])
        return [domain_equivalence, constraint_equivalence, calculate_equivalence]

    @staticmethod
    def build_io_equivalence(dic_1, dic_2, exp_slv):
        temp_name_dic = dict()
        for signal in dic_1.values():
            name = signal.call_name
            temp_name_dic[name] = signal.smt

        terms = list()
        for signal in dic_2.values():
            smt_1 = temp_name_dic.get(signal.call_name)
            smt_2 = signal.smt
            term = exp_slv.mkTerm(Kind.EQUAL, smt_1, smt_2)
            terms.append(term)

        return exp_slv.associativeForm(terms)
