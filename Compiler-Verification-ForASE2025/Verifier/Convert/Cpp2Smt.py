import cvc5
from cvc5 import Kind

from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Directory.FrElementModel import FrElementModel
from Tools.Check import TypeCheck
from Tools.ValueDeal import reverse_pairs


class CppSmtConstructor:
    def __init__(self, exp_slv):
        TypeCheck(ExpandedCVC5, exp_slv)
        self.__exp_slv = exp_slv
        self.__total_signal_no = 4
        self.__input_signal_start = 2
        self.signals = None
        self.directory_terms = list()

    # for add function
    def directory_2_smt(self):
        mySignalStart = 1
        self.signals = FrElementModel.construct_value_bash('v0', 'v1', 'v2', 'v3')
        constant0 = FrElementModel.construct_constant('constant_0',
                                                      0x00000000,
                                                      0x00000000000000000000000000000000,
                                                      0x40000000)
        constant1 = FrElementModel.construct_constant('constant_1',
                                                      0x00000001,
                                                      reverse_pairs(
                                                     'FBFFFF4F1C3496AC29CD609F9576FC362E4679786FA36E662FDF079AC1770A0E'),
                                                      0x40000000)
        constants = [constant0, constant1]
        expaux = FrElementModel.construct_value_bash('e0', 'e1', 'e2', 'e3')
        # 初始化设计
        # input signal 永远是非蒙哥马利的 长短则是视情况而自动判断
        self.directory_terms.append(self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[2].is_m, FrElementModel.smt_false))
        self.directory_terms.append(self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[3].is_m, FrElementModel.smt_false))
        # Fr_add
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[2].is_l, FrElementModel.smt_false)
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[2].is_l, FrElementModel.smt_true)
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[3].is_l, FrElementModel.smt_false)
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[3].is_l, FrElementModel.smt_true)

        cond_ss = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)
        cond_ls = self.__exp_slv.mkTerm(Kind.AND, a_l, b_s)
        cond_sl = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l)
        cond_ll = self.__exp_slv.mkTerm(Kind.AND, a_l, b_l)

        sum_ss = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, self.signals[2].s_v, self.signals[3].s_v)
        sum_sl = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, self.signals[2].s_v, self.signals[3].l_v)
        sum_ls = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, self.signals[2].l_v, self.signals[3].s_v)
        sum_ll = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, self.signals[2].l_v, self.signals[3].l_v)

        added_ss = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_l, FrElementModel.smt_false),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_m, FrElementModel.smt_false),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].s_v, sum_ss))

        added_ls = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_l, FrElementModel.smt_true),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_m, FrElementModel.smt_false),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].l_v, sum_ls))

        added_sl = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_l, FrElementModel.smt_true),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_m, FrElementModel.smt_false),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].l_v, sum_sl))

        added_ll = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_l, FrElementModel.smt_true),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_m, FrElementModel.smt_false),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].l_v, sum_ll))

        case_ss = self.__exp_slv.mkTerm(Kind.IMPLIES, cond_ss, added_ss)
        case_sl = self.__exp_slv.mkTerm(Kind.IMPLIES, cond_sl, added_sl)
        case_ls = self.__exp_slv.mkTerm(Kind.IMPLIES, cond_ls, added_ls)
        case_ll = self.__exp_slv.mkTerm(Kind.IMPLIES, cond_ll, added_ll)

        fr_add = self.__exp_slv.mkTerm(Kind.AND, case_ss, case_sl, case_ls, case_ll)
        self.directory_terms.append(fr_add)

        # Fr_copy
        copy_s = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].s_v, expaux[0].s_v)
        copy_l = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].l_v, expaux[0].l_v)
        copy_if_l = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].is_l, expaux[0].is_l)
        copy_if_m = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].is_m, expaux[0].is_m)
        fr_copy = self.__exp_slv.mkTerm(Kind.AND, copy_s, copy_l, copy_if_l, copy_if_m)
        self.directory_terms.append(fr_copy)

    def directory_2_smt_compare(self):
        self.signals = FrElementModel.construct_value_bash('v0', 'ret', 'in')
        expaux = FrElementModel.construct_value_bash('e0', 'e1', 'e2')
        constant0 = FrElementModel.construct_constant('constant_0',
                                                      0x00000000,
                                                      0x00000000000000000000000000000000,
                                                      0x40000000)
        constant1 = FrElementModel.construct_constant('constant_1',
                                                      0x00000001,
                                                      reverse_pairs(
                                                     'FBFFFF4F1C3496AC29CD609F9576FC362E4679786FA36E662FDF079AC1770A0E'),
                                                      0x40000000)
        constants = [constant0, constant1]
        # input signal 永远是非蒙哥马利的 长短则是视情况而自动判断
        self.directory_terms.append(self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[2].is_m, self.__exp_slv.Boolean_False()))
        # Fr_gt
        in_s = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[2].is_l, self.__exp_slv.Boolean_False())
        in_l = self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[2].is_l, self.__exp_slv.Boolean_True())

        s_gt = self.__exp_slv.mkFFTerm_Gt(self.signals[2].s_v, constant0.s_v)
        l_gt = self.__exp_slv.mkFFTerm_Gt(self.signals[2].l_v, constant0.s_v)

        s_gt_true = self.__exp_slv.mkTerm(Kind.EQUAL, s_gt, self.__exp_slv.Boolean_True())
        s_gt_false = self.__exp_slv.mkTerm(Kind.EQUAL, s_gt, self.__exp_slv.Boolean_False())
        l_gt_true = self.__exp_slv.mkTerm(Kind.EQUAL, l_gt, self.__exp_slv.Boolean_True())
        l_gt_false = self.__exp_slv.mkTerm(Kind.EQUAL, l_gt, self.__exp_slv.Boolean_False())

        case_true = self.__exp_slv.mkTerm(Kind.AND,
                                          self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].s_v, self.__exp_slv.FF_one()),
                                          self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_l,
                                                                self.__exp_slv.Boolean_False()),
                                          self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_m,
                                                                self.__exp_slv.Boolean_False()))

        case_false = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].s_v, self.__exp_slv.FF_zero()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_l,
                                                                 self.__exp_slv.Boolean_False()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].is_m,
                                                                 self.__exp_slv.Boolean_False()))

        case_s = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, s_gt_true, case_true),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, s_gt_false, case_false))

        case_l = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, l_gt_true, case_true),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, l_gt_false, case_false))

        Fr_gt = self.__exp_slv.mkTerm(Kind.AND,
                                      self.__exp_slv.mkTerm(Kind.IMPLIES, in_s, case_s),
                                      self.__exp_slv.mkTerm(Kind.IMPLIES, in_l, case_l))

        self.directory_terms.append(Fr_gt)

        check_false = self.__exp_slv.mkTerm(Kind.EQUAL, expaux[0].s_v, self.__exp_slv.FF_zero())
        check_true = self.__exp_slv.mkTerm(Kind.NOT, check_false)

        ret0 = self.__exp_slv.mkTerm(Kind.AND,
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].s_v, constant0.s_v),
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].l_v, constant0.l_v),
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].is_l, constant0.is_l),
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].is_m, constant0.is_m))

        ret1 = self.__exp_slv.mkTerm(Kind.AND,
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].s_v, constant1.s_v),
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].l_v, constant1.l_v),
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].is_l, constant1.is_l),
                                     self.__exp_slv.mkTerm(Kind.EQUAL, self.signals[1].is_m, constant1.is_m))

        constraint = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, check_true, ret1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, check_false, ret0))

        self.directory_terms.append(constraint)

    def assert_all(self):
        for term in self.directory_terms:
            self.__exp_slv.assertFormula(term)
