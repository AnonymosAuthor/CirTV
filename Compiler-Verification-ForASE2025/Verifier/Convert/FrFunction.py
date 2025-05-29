from cvc5 import Kind
import re
from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Directory.FrElementModel import FrElementModel
from Tools.Check import TypeCheck
from Tools.ColorPrint import colorPrint, COLOR
from Tools.ValueDeal import reverse_pairs
import copy


class FrFunction:

    def __init__(self, exp_slv):
        self.__exp_slv = exp_slv
        FrElementModel.init(self.__exp_slv)
        self.R = self.__exp_slv.FF_number(
            6350874878119819312338956282401532410528162663560392320966563075034087161851)  # is that right?
        self.R2 = self.__exp_slv.FF_number(944936681149208446651664254269745548490766851729442924617792859073125903783)
        self.p = self.__exp_slv.FF_number(21888242871839275222246405745257275088548364400416034343698204186575808495617)
        self.Rr_int = 9915499612839321149637521777990102151350674507940716049588462388200839649614
        self.p_int = 21888242871839275222246405745257275088548364400416034343698204186575808495617
        self.directory_terms = list()
        self.signal_map = {}
        self.element_dict = {}
        self.int_dict = {}
        self.constants_dict = {}
        self.my_signal_start = 1

        self.template_name_dict = {}
        self.template_line_dict = {}
        self.template_start_position_dict = {}

        # self.function_name_dict = {}
        self.function_line_dict = {}
        self.function_destination = {}
        self.function_destination_size = {}
        self.function_replace_name = {}
        self.is_running_subfunction = False
        self.go_subfunction_line = []
        self.which_subfunction = None

        self.mySubcomponents = {}
        self.template_name_componentMemory = {}
        self.template_name_signalStart = {}
        self.template_name_direct = {}

        self.dest_var = None
        self.current_aux_create = None
        self.current_cmp_index_ref = None
        self.is_running_subtemplate = False
        self.go_subtemplate_line = []
        self.value_to_subtemplate = None
        self.new_expaux = False
        self.else_start_line = -1
        self.else_end_line = -1
        self.ctx_index_stack = []

        self.if_terms = list()
        self.else_terms = list()
        self.use_if_terms = False
        self.use_else_terms = False
        self.use_normal_terms = True
        self.if_start_line = -1
        self.if_key = None

        self.expaux_type = {}
        self.if_else_type = 1
        self.origin_lines = []
        self.update_lines_end = []
        self.origin_lines_locate = []  #从循环出来后，原lines开始位置
        self.have_append_ctx_index = {}

        self.lvar_iterate = {}
        self.if_iterate = {}
        self.num_lvar93 = 0
        self.lines_len = 0
        self.operate_lvar = False

    def Fr_Copy(self, r: FrElementModel, a: FrElementModel):
        copy_s = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, a.s_v)
        copy_l = self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, a.l_v)
        copy_if_l = self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, a.is_l)
        copy_if_m = self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, a.is_m)
        fr_copy = self.__exp_slv.mkTerm(Kind.AND, copy_s, copy_l, copy_if_l, copy_if_m)
        return fr_copy

    def add_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_addl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ml2m

    def add_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_addl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b_m.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ml2n

    def add_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_addl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1nl2m

    def add_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_addl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_addl1nl2n

    def add_l1ms2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_addl1ms2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ms2m

    def add_l1ms2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_addl1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b_m.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ms2n

    def add_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_addl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                        b.s_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_addl1ns2

    def add_s1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_adds1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_adds1ml2m

    def add_s1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_addl1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ms2n

    def add_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_adds1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.s_v,
                                                                                        b.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_adds1l2n

    def add_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        up = self.__exp_slv.FF_number(2 ** 31 - 1)
        down = self.__exp_slv.FF_number(-2 ** 31)
        sum_ab = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.s_v, b.s_v)

        condition1_1 = self.__exp_slv.mkFFTerm_Lt(sum_ab, down)
        condition1_2 = self.__exp_slv.mkFFTerm_Gt(sum_ab, up)
        condition2_1 = self.__exp_slv.mkFFTerm_Ge(sum_ab, down)
        condition2_2 = self.__exp_slv.mkFFTerm_Le(sum_ab, up)
        # condition1_1 = self.__exp_slv.mkFFTerm_Gt(down, sum_ab)
        # condition1_2 = self.__exp_slv.mkFFTerm_Gt(sum_ab, up)
        # condition2_1 = self.__exp_slv.mkFFTerm_Ge(sum_ab, down)
        # condition2_2 = self.__exp_slv.mkFFTerm_Ge(up, sum_ab)

        condition1 = self.__exp_slv.mkTerm(Kind.OR, condition1_1, condition1_2)
        condition2 = self.__exp_slv.mkTerm(Kind.AND, condition2_1, condition2_2)

        result_1 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, sum_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                         )
        result_2 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, sum_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                         )
        fr_adds1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2)
                                           )

        # fr_adds1s2 = self.__exp_slv.mkTerm(Kind.AND,
        #                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
        #                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, sum_ab))

        return fr_adds1s2

    def Fr_add(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        add_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        add_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        add_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        add_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        add_l1ms2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s, b_m)
        add_l1ms2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s, b_n)
        add_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        add_s1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_s, a_m, b_l, b_m)
        add_s1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_s, a_n, b_l, b_m)
        add_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        add_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        fr_add = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1ml2m, self.add_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1ml2n, self.add_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1nl2m, self.add_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1nl2n, self.add_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1ms2m, self.add_l1ms2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1ms2n, self.add_l1ms2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_l1ns2, self.add_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_s1ml2m, self.add_s1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_s1nl2m, self.add_s1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_s1l2n, self.add_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, add_s1s2, self.add_s1s2(r, a, b))
                                       )
        return fr_add
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 return self.add_l1ml2m(r, a, b)
        #             else:
        #                 return self.add_l1ml2n(r, a, b)
        #         else:
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 return self.add_l1nl2m(r, a, b)
        #             else:
        #                 return self.add_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         if b.is_m == self.__exp_slv.Boolean_True():
        #             return self.add_l1ms2m(r, a, b)
        #         else:
        #             return self.add_l1ms2n(r, a, b)
        #     else:
        #         return self.add_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             return self.add_s1ml2m(r, a, b)
        #         else:
        #             return self.add_s1nl2m(r, a, b)
        #     else:
        #         return self.add_s1l2n(r, a, b)
        # else:
        #     return self.add_s1s2(r, a, b)

    def sub_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_subl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ml2m

    def sub_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_subl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b_m.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ml2n

    def sub_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_subl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1nl2m

    def sub_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_subl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_subl1nl2n

    def sub_l1ms2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_subl1ms2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ms2m

    def sub_l1ms2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_subl1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b_m.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ms2n

    def sub_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_subl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                        self.__exp_slv.mkTerm(
                                                                                            Kind.FINITE_FIELD_NEG,
                                                                                            b.s_v))),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_subl1ns2

    def sub_s1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_subs1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subs1ml2m

    def sub_s1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_subs1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subs1nl2m

    def sub_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_subs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.s_v,
                                                                                        self.__exp_slv.mkTerm(
                                                                                            Kind.FINITE_FIELD_NEG,
                                                                                            b.l_v))),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_subs1l2n

    def sub_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        up = self.__exp_slv.FF_number(2 ** 31 - 1)
        down = self.__exp_slv.FF_number(-2 ** 31)
        sub_ab = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.s_v,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, b.s_v))

        condition1_1 = self.__exp_slv.mkFFTerm_Lt(sub_ab, down)
        condition1_2 = self.__exp_slv.mkFFTerm_Gt(sub_ab, up)
        condition2_1 = self.__exp_slv.mkFFTerm_Ge(sub_ab, down)
        condition2_2 = self.__exp_slv.mkFFTerm_Le(sub_ab, up)

        condition1 = self.__exp_slv.mkTerm(Kind.OR, condition1_1, condition1_2)
        condition2 = self.__exp_slv.mkTerm(Kind.AND, condition2_1, condition2_2)

        result_1 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, sub_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                         )
        result_2 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, sub_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                         )
        fr_subs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2)
                                           )

        return fr_subs1s2

    def Fr_sub(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        sub_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        sub_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        sub_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        sub_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        sub_l1ms2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s, b_m)
        sub_l1ms2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s, b_n)
        sub_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        sub_s1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_s, a_m, b_l, b_m)
        sub_s1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_s, a_n, b_l, b_m)
        sub_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        sub_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        fr_sub = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1ml2m, self.sub_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1ml2n, self.sub_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1nl2m, self.sub_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1nl2n, self.sub_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1ms2m, self.sub_l1ms2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1ms2n, self.sub_l1ms2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_l1ns2, self.sub_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_s1ml2m, self.sub_s1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_s1nl2m, self.sub_s1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_s1l2n, self.sub_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, sub_s1s2, self.sub_s1s2(r, a, b))
                                       )
        return fr_sub
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 return self.sub_l1ml2m(r, a, b)
        #             else:
        #                 return self.sub_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             return self.sub_l1nl2m(r, a, b)
        #         else:
        #             return self.sub_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         if b.is_m == self.__exp_slv.Boolean_True():
        #             return self.sub_l1ms2m(r, a, b)
        #         else:
        #             return self.sub_l1ms2n(r, a, b)
        #     else:
        #         return self.sub_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             return self.sub_s1ml2m(r, a, b)
        #         else:
        #             return self.sub_s1nl2m(r, a, b)
        #     else:
        #         return self.sub_s1l2n(r, a, b)
        # else:
        #     return self.sub_s1s2(r, a, b)

    def mul_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1ml2m

    def mul_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1ml2n

    def mul_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1nl2m

    def mul_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        r_temp = FrElementModel.construct_value('r_temp')  # temp right?
        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                         r.l_v)
        fr_mull1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1,
                                             result_2,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1nl2n

    def mul_l1ms2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ms2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1ms2m

    def mul_l1ms2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.s_v))
        fr_mull1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1ms2n

    def mul_l1ns2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ns2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1ns2m

    def mul_l1ns2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        r_temp = FrElementModel.construct_value('r_temp')  # temp right?
        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.s_v))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                         r.l_v)
        fr_mull1ns2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1,
                                             result_2,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1ns2n

    def mul_s1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_muls1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_muls1ml2m

    def mul_s1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_muls1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_muls1ml2n

    def mul_s1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.s_v, b.l_v))
        fr_muls1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_muls1nl2m

    def mul_s1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        r_temp = FrElementModel.construct_value('r_temp')  # temp right?
        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.s_v, b.l_v))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                         r.l_v)
        fr_muls1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1,
                                             result_2,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_muls1nl2n

    def mul_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_muls1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.s_v,
                                                                                       b.s_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
                                           )
        return fr_muls1s2

    def Fr_mul(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        mul_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        mul_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        mul_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        mul_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        mul_l1ms2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s, b_m)
        mul_l1ms2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s, b_n)
        mul_l1ns2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s, b_m)
        mul_l1ns2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s, b_n)
        mul_s1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_s, a_m, b_l, b_m)
        mul_s1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_s, a_m, b_l, b_n)
        mul_s1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_s, a_n, b_l, b_m)
        mul_s1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_s, a_n, b_l, b_n)
        mul_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        fr_mul = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1ml2m, self.mul_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1ml2n, self.mul_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1nl2m, self.mul_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1nl2n, self.mul_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1ms2m, self.mul_l1ms2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1ms2n, self.mul_l1ms2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1ns2m, self.mul_l1ns2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_l1ns2n, self.mul_l1ns2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_s1ml2m, self.mul_s1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_s1ml2n, self.mul_s1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_s1nl2m, self.mul_s1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_s1nl2n, self.mul_s1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, mul_s1s2, self.mul_s1s2(r, a, b))
                                       )
        return fr_mul
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 return self.mul_l1ml2m(r, a, b)
        #             else:
        #                 return self.mul_l1ml2n(r, a, b)
        #         else:
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 return self.mul_l1nl2m(r, a, b)
        #             else:
        #                 return self.mul_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         if b.is_m == self.__exp_slv.Boolean_True():
        #             return self.mul_l1ms2m(r, a, b)
        #         else:
        #             return self.mul_l1ms2n(r, a, b)
        #     else:
        #         if b.is_m == self.__exp_slv.Boolean_True():
        #             return self.mul_l1ns2m(r, a, b)
        #         else:
        #             return self.mul_l1ns2n(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if a.is_m == self.__exp_slv.Boolean_True():
        #         if b.is_m == self.__exp_slv.Boolean_True():
        #             return self.mul_s1ml2m(r, a, b)
        #         else:
        #             return self.mul_s1ml2n(r, a, b)
        #     elif b.is_m == self.__exp_slv.Boolean_True():
        #         return self.mul_s1nl2m(r, a, b)
        #     else:
        #         return self.mul_s1nl2n(r, a, b)
        # else:
        #     return self.mul_s1s2(r, a, b)

    def Fr_inv(self, r: FrElementModel, a: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        a_inv = FrElementModel.construct_value('a_inv')  # temp right?

        before = self.Fr_toNormal(a_n, a)

        an_l = self.__exp_slv.mkTerm(Kind.EQUAL, a_n.is_l, self.__exp_slv.Boolean_True())
        an_s = self.__exp_slv.mkTerm(Kind.EQUAL, a_n.is_l, self.__exp_slv.Boolean_False())

        up = self.__exp_slv.FF_number(2 ** 31 - 1)
        down = self.__exp_slv.FF_number(-2 ** 31)

        fr_invtemp = self.__exp_slv.mkTerm(Kind.AND,
                                           before,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, an_l,
                                                                 self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                                       self.__exp_slv.mkTerm(
                                                                                           Kind.FINITE_FIELD_MULT,
                                                                                           a_inv.l_v, a_n.l_v),
                                                                                       self.__exp_slv.FF_one())),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, an_s,
                                                                 self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                                       self.__exp_slv.mkTerm(
                                                                                           Kind.FINITE_FIELD_MULT,
                                                                                           a_inv.l_v, a_n.s_v),
                                                                                       self.__exp_slv.FF_one()))
                                           )

        # condition1_1 = self.__exp_slv.mkTerm(Kind.AND, fr_invtemp, self.__exp_slv.mkFFTerm_Lt(a_inv.l_v, down))
        # condition1_2 = self.__exp_slv.mkTerm(Kind.AND, fr_invtemp, self.__exp_slv.mkFFTerm_Gt(a_inv.l_v, up))
        # condition2_1 = self.__exp_slv.mkTerm(Kind.AND, fr_invtemp, self.__exp_slv.mkFFTerm_Ge(a_inv.l_v, down))
        # condition2_2 = self.__exp_slv.mkTerm(Kind.AND, fr_invtemp, self.__exp_slv.mkFFTerm_Le(a_inv.l_v, up))

        condition1_1 = self.__exp_slv.mkFFTerm_Lt(a_inv.l_v, down)
        condition1_2 = self.__exp_slv.mkFFTerm_Gt(a_inv.l_v, up)
        condition2_1 = self.__exp_slv.mkFFTerm_Ge(a_inv.l_v, down)
        condition2_2 = self.__exp_slv.mkFFTerm_Le(a_inv.l_v, up)

        condition1 = self.__exp_slv.mkTerm(Kind.OR, condition1_1, condition1_2)
        condition2 = self.__exp_slv.mkTerm(Kind.AND, condition2_1, condition2_2)

        result_1 = self.__exp_slv.mkTerm(Kind.AND,
                                         fr_invtemp,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, a_inv.l_v),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                         )
        result_2 = self.__exp_slv.mkTerm(Kind.AND,
                                         fr_invtemp,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, a_inv.l_v),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                         )
        fr_inv = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2)
                                       )
        return fr_inv

    def Fr_div(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_inv = FrElementModel.construct_value('b_inv')  # temp right?
        first = self.Fr_inv(b_inv, b)
        second = self.Fr_mul(r, a, b_inv)
        fr_div = self.__exp_slv.mkTerm(Kind.AND, first, second)

        return fr_div

    def Fr_toMontgomery(self, r: FrElementModel, a: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())

        l1n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n)
        s1n = self.__exp_slv.mkTerm(Kind.AND, a_s, a_n)

        fr_toMont_l1n = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                    r.l_v,
                                                                    self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
                                                                                          self.R, a.l_v)),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                              )
        fr_toMont_s1n = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                    r.l_v,
                                                                    self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
                                                                                          self.R, a.s_v)),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                              )

        fr_toMont = self.__exp_slv.mkTerm(Kind.AND,
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, a_m, self.Fr_Copy(r, a)),
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, l1n, fr_toMont_l1n),
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, s1n, fr_toMont_s1n)
                                          )
        return fr_toMont
        # if a.is_m == self.__exp_slv.Boolean_True():  # yes/not?
        #     return self.Fr_Copy(r, a)
        # elif a.is_l == self.__exp_slv.Boolean_True():  # mult?
        #     fr_toMont = self.__exp_slv.mkTerm(Kind.AND,
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                                             r.l_v,
        #                                                             self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
        #                                                                                   self.R, a.l_v)),
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
        #                                       )
        #     return fr_toMont
        # else:
        #     fr_toMont = self.__exp_slv.mkTerm(Kind.AND,
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                                             r.l_v,
        #                                                             self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
        #                                                                                   self.R, a.s_v)),
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
        #                                       )
        #     return fr_toMont

    def Fr_toNormal(self, r: FrElementModel, a: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())

        l1m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m)
        elseKind = self.__exp_slv.mkTerm(Kind.NOT, l1m)

        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       a.l_v)
        fr_tonormal_l1m = self.__exp_slv.mkTerm(Kind.AND,
                                                result,
                                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                      self.__exp_slv.Boolean_True()),
                                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                      self.__exp_slv.Boolean_False()))
        fr_toNormal = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, l1m, fr_tonormal_l1m),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, elseKind, self.Fr_Copy(r, a))
                                            )
        return fr_toNormal

    def Fr_toLongNormal(self, r: FrElementModel, a: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())

        l1m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m)
        l1n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n)

        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       a.l_v)
        fr_tolongnormal_l1m = self.__exp_slv.mkTerm(Kind.AND,
                                                    result,
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                          self.__exp_slv.Boolean_True()),
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                          self.__exp_slv.Boolean_False()))
        fr_toLongNormal_s1 = self.__exp_slv.mkTerm(Kind.AND,
                                                   self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, a.s_v),
                                                   self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v,
                                                                         self.__exp_slv.FF_number(0)),
                                                   self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                         self.__exp_slv.Boolean_True()),
                                                   self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                         self.__exp_slv.Boolean_False()))

        fr_toLongNormal = self.__exp_slv.mkTerm(Kind.AND,
                                                self.__exp_slv.mkTerm(Kind.IMPLIES, l1m, fr_tolongnormal_l1m),
                                                self.__exp_slv.mkTerm(Kind.IMPLIES, l1n, self.Fr_Copy(r, a)),
                                                self.__exp_slv.mkTerm(Kind.IMPLIES, a_s, fr_toLongNormal_s1)
                                                )
        return fr_toLongNormal
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                        self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
        #                                        a.l_v)
        #         fr_tolongnormal = self.__exp_slv.mkTerm(Kind.AND,
        #                                                 result,
        #                                                 self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
        #                                                                       self.__exp_slv.Boolean_True()),
        #                                                 self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
        #                                                                       self.__exp_slv.Boolean_False()))
        #         return fr_tolongnormal
        #     else:
        #         return self.Fr_Copy(r, a)
        # else:
        #     fr_tolongnormal = self.__exp_slv.mkTerm(Kind.AND,
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, a.s_v),
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v,
        #                                                                   self.__exp_slv.FF_number(0)),
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
        #                                                                   self.__exp_slv.Boolean_True()),
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
        #                                                                   self.__exp_slv.Boolean_False()))
        #     return fr_tolongnormal
    def Fr_neg(self, r: FrElementModel, a: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)

        fr_neg = self.__exp_slv.mkTerm(Kind.AND,
                                       before_a_n,
                                       self.__exp_slv.mkTerm(Kind.EQUAL,
                                                             r.l_v,
                                                             self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, a_n.l_v)),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                       )
        return fr_neg



    def Fr_Square(self, r: FrElementModel, a: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())

        l1m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m)
        l1n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n)

        result_l1m = self.__exp_slv.mkTerm(Kind.EQUAL,
                                           self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                           self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, a.l_v))
        fr_squarel1m = self.__exp_slv.mkTerm(Kind.AND,
                                             result_l1m,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                   self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                   self.__exp_slv.Boolean_True()))

        r_temp = FrElementModel.construct_value('r_temp')  # temp right?
        result_1_l1n = self.__exp_slv.mkTerm(Kind.EQUAL,
                                             self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                             self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, a.l_v))
        result_2_l1n = self.__exp_slv.mkTerm(Kind.EQUAL,
                                             self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                             r.l_v)
        fr_squarel1n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1_l1n,
                                             result_2_l1n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                   self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                   self.__exp_slv.Boolean_True()))

        fr_squares = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
                                                                                       a.s_v, a.s_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                 self.__exp_slv.Boolean_False()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
                                           )

        fr_square = self.__exp_slv.mkTerm(Kind.AND,
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, l1m, fr_squarel1m),
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, l1n, fr_squarel1n),
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, a_s, fr_squares)
                                          )
        return fr_square
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if a.is_m == self.__exp_slv.Boolean_True():  # yes/not?
        #         result = self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                        self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
        #                                        self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, a.l_v))
        #         fr_squarelm = self.__exp_slv.mkTerm(Kind.AND,
        #                                             result,
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
        #                                                                   self.__exp_slv.Boolean_True()),
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
        #                                                                   self.__exp_slv.Boolean_True()))
        #         return fr_squarelm
        #     else:
        #         r_temp = FrElement.construct_value('r_temp')  # temp right?
        #         result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                          self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
        #                                          self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, a.l_v))
        #         result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                          self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
        #                                          r.l_v)
        #         fr_squareln = self.__exp_slv.mkTerm(Kind.AND,
        #                                             result_1,
        #                                             result_2,
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
        #                                                                   self.__exp_slv.Boolean_True()),
        #                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
        #                                                                   self.__exp_slv.Boolean_True()))
        #         return fr_squareln
        #
        # else:
        #     fr_squares = self.__exp_slv.mkTerm(Kind.AND,
        #                                        self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                                              r.l_v,
        #                                                              self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
        #                                                                                    a.s_v, a.s_v)),
        #                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
        #                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
        #                                                              self.__exp_slv.Boolean_False()),
        #                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        #                                        )
        #
        #     return fr_squares

    def req_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ml2m

    def rneq_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ml2m

    def req_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ml2n

    def rneq_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                              before,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ml2n

    def req_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1nl2m

    def rneq_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                              before,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1nl2m

    def req_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1nl2n

    def rneq_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1nl2n

    def req_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ms2

    def rneq_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ms2

    def req_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ns2

    def rneq_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ns2

    def req_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reqs1l2m

    def rneq_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneqs1l2m

    def req_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reqs1l2n

    def rneq_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneqs1l2n

    def req_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_reqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reqs1s2

    def rneq_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rneqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneqs1s2

    def Fr_eq(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        req_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        req_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        req_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        req_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        req_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        req_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        req_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        req_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        req_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        result = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_l1ml2m, self.req_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_l1ml2n, self.req_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_l1nl2m, self.req_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_l1nl2n, self.req_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_l1ms2, self.req_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_l1ns2, self.req_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_s1l2m, self.req_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_s1l2n, self.req_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, req_s1s2, self.req_s1s2(r, a, b))
                                       )
        fr_eq = self.__exp_slv.mkTerm(Kind.AND,
                                      result,
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                      )
        return fr_eq

        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 result = self.req_l1ml2m(r, a, b)
        #             else:
        #                 result = self.req_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             result = self.req_l1nl2m(r, a, b)
        #         else:
        #             result = self.req_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.req_l1ms2(r, a, b)
        #     else:
        #         result = self.req_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         result = self.req_s1l2m(r, a, b)
        #     else:
        #         result = self.req_s1l2n(r, a, b)
        # else:
        #     result = self.req_s1s2(r, a, b)
        #
        # fr_eq = self.__exp_slv.mkTerm(Kind.AND,
        #                               result,
        #                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
        #                               )
        # return fr_eq

    def Fr_neq(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        neq_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        neq_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        neq_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        neq_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        neq_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        neq_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        neq_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        neq_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        neq_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        result = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_l1ml2m, self.rneq_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_l1ml2n, self.rneq_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_l1nl2m, self.rneq_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_l1nl2n, self.rneq_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_l1ms2, self.rneq_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_l1ns2, self.rneq_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_s1l2m, self.rneq_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_s1l2n, self.rneq_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, neq_s1s2, self.rneq_s1s2(r, a, b))
                                       )
        fr_neq = self.__exp_slv.mkTerm(Kind.AND,
                                       result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                       )
        return fr_neq
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 result = self.rneq_l1ml2m(r, a, b)
        #             else:
        #                 result = self.rneq_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             result = self.rneq_l1nl2m(r, a, b)
        #         else:
        #             result = self.rneq_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.rneq_l1ms2(r, a, b)
        #     else:
        #         result = self.rneq_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         result = self.rneq_s1l2m(r, a, b)
        #     else:
        #         result = self.rneq_s1l2n(r, a, b)
        # else:
        #     result = self.rneq_s1s2(r, a, b)
        #
        # fr_neq = self.__exp_slv.mkTerm(Kind.AND,
        #                                result,
        #                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
        #                                )
        # return fr_neq

    def geq_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ml2m

    def rlt_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rltl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ml2m

    def geq_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ml2n

    def rlt_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rltl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ml2n

    def geq_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1nl2m

    def rlt_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rltl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1nl2m

    def geq_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1nl2n

    def rlt_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rltl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1nl2n

    def geq_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ms2

    def rlt_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rltl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ms2

    def geq_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ns2

    def rlt_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rltl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ns2

    def geq_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geqs1l2m

    def rlt_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rlts1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rlts1l2m

    def geq_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geqs1l2n

    def rlt_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rlts1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rlts1l2n

    def geq_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_geqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geqs1s2

    def rlt_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rlts1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rlts1s2

    def Fr_lt(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        rlt_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        rlt_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        rlt_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        rlt_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        rlt_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        rlt_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        rlt_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        rlt_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        rlt_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        result = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_l1ml2m, self.rlt_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_l1ml2n, self.rlt_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_l1nl2m, self.rlt_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_l1nl2n, self.rlt_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_l1ms2, self.rlt_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_l1ns2, self.rlt_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_s1l2m, self.rlt_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_s1l2n, self.rlt_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rlt_s1s2, self.rlt_s1s2(r, a, b))
                                       )
        fr_lt = self.__exp_slv.mkTerm(Kind.AND,
                                      result,
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                      )
        return fr_lt

        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 result = self.rlt_l1ml2m(r, a, b)
        #             else:
        #                 result = self.rlt_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             result = self.rlt_l1nl2m(r, a, b)
        #         else:
        #             result = self.rlt_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.rlt_l1ms2(r, a, b)
        #     else:
        #         result = self.rlt_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         result = self.rlt_s1l2m(r, a, b)
        #     else:
        #         result = self.rlt_s1l2n(r, a, b)
        # else:
        #     result = self.rlt_s1s2(r, a, b)
        #
        # fr_lt = self.__exp_slv.mkTerm(Kind.AND,
        #                               result,
        #                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
        #                               )
        # return fr_lt

    def Fr_geq(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        geq_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        geq_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        geq_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        geq_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        geq_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        geq_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        geq_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        geq_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        geq_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        result = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_l1ml2m, self.geq_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_l1ml2n, self.geq_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_l1nl2m, self.geq_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_l1nl2n, self.geq_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_l1ms2, self.geq_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_l1ns2, self.geq_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_s1l2m, self.geq_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_s1l2n, self.geq_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, geq_s1s2, self.geq_s1s2(r, a, b))
                                       )
        fr_geq = self.__exp_slv.mkTerm(Kind.AND,
                                       result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                       )
        return fr_geq

        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 result = self.geq_l1ml2m(r, a, b)
        #             else:
        #                 result = self.geq_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             result = self.geq_l1nl2m(r, a, b)
        #         else:
        #             result = self.geq_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.geq_l1ms2(r, a, b)
        #     else:
        #         result = self.geq_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         result = self.geq_s1l2m(r, a, b)
        #     else:
        #         result = self.geq_s1l2n(r, a, b)
        # else:
        #     result = self.geq_s1s2(r, a, b)
        #
        # fr_geq = self.__exp_slv.mkTerm(Kind.AND,  # have some questions
        #                                result,
        #                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
        #                                )
        # return fr_geq

    def leq_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ml2m

    def rgt_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgtl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ml2m

    def leq_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ml2n

    def rgt_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgtl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ml2n

    def leq_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1nl2m

    def rgt_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgtl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1nl2m

    def leq_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1nl2n

    def rgt_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgtl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1nl2n

    def leq_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ms2

    def rgt_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_m = FrElementModel.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgtl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ms2

    def leq_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ns2

    def rgt_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgtl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ns2

    def leq_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leqs1l2m

    def rgt_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_m = FrElementModel.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgts1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgts1l2m

    def leq_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leqs1l2n

    def rgt_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgts1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgts1l2n

    def leq_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))

        fr_leqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leqs1s2

    def rgt_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(0))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, self.__exp_slv.FF_number(1))

        fr_rgts1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgts1s2

    def Fr_gt(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        rgt_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        rgt_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        rgt_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        rgt_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        rgt_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        rgt_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        rgt_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        rgt_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        rgt_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        result = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_l1ml2m, self.rgt_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_l1ml2n, self.rgt_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_l1nl2m, self.rgt_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_l1nl2n, self.rgt_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_l1ms2, self.rgt_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_l1ns2, self.rgt_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_s1l2m, self.rgt_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_s1l2n, self.rgt_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, rgt_s1s2, self.rgt_s1s2(r, a, b))
                                       )
        fr_gt = self.__exp_slv.mkTerm(Kind.AND,
                                      result,
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                      )
        return fr_gt

        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 result = self.rgt_l1ml2m(r, a, b)
        #             else:
        #                 result = self.rgt_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             result = self.rgt_l1nl2m(r, a, b)
        #         else:
        #             result = self.rgt_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.rgt_l1ms2(r, a, b)
        #     else:
        #         result = self.rgt_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         result = self.rgt_s1l2m(r, a, b)
        #     else:
        #         result = self.rgt_s1l2n(r, a, b)
        # else:
        #     result = self.rgt_s1s2(r, a, b)
        #
        # fr_gt = self.__exp_slv.mkTerm(Kind.AND,
        #                               result,
        #                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
        #                               )
        # return fr_gt

    def Fr_leq(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        leq_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        leq_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        leq_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        leq_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        leq_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        leq_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        leq_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        leq_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        leq_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        result = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_l1ml2m, self.leq_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_l1ml2n, self.leq_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_l1nl2m, self.leq_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_l1nl2n, self.leq_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_l1ms2, self.leq_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_l1ns2, self.leq_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_s1l2m, self.leq_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_s1l2n, self.leq_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, leq_s1s2, self.leq_s1s2(r, a, b))
                                       )
        fr_leq = self.__exp_slv.mkTerm(Kind.AND,
                                       result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                       )
        return fr_leq
        # if a.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_l == self.__exp_slv.Boolean_True():
        #         if a.is_m == self.__exp_slv.Boolean_True():
        #             if b.is_m == self.__exp_slv.Boolean_True():
        #                 result = self.leq_l1ml2m(r, a, b)
        #             else:
        #                 result = self.leq_l1ml2n(r, a, b)
        #         elif b.is_m == self.__exp_slv.Boolean_True():
        #             result = self.leq_l1nl2m(r, a, b)
        #         else:
        #             result = self.leq_l1nl2n(r, a, b)
        #     elif a.is_m == self.__exp_slv.Boolean_True():
        #         result = self.leq_l1ms2(r, a, b)
        #     else:
        #         result = self.leq_l1ns2(r, a, b)
        # elif b.is_l == self.__exp_slv.Boolean_True():
        #     if b.is_m == self.__exp_slv.Boolean_True():
        #         result = self.leq_s1l2m(r, a, b)
        #     else:
        #         result = self.leq_s1l2n(r, a, b)
        # else:
        #     result = self.leq_s1s2(r, a, b)
        #
        # fr_leq = self.__exp_slv.mkTerm(Kind.AND,  # have some questions
        #                                result,
        #                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
        #                                self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
        #                                )
        # return fr_leq

    def Fr_isTrue(self, pE: FrElementModel):
        result = 1

        pE_l = self.__exp_slv.mkTerm(Kind.EQUAL, pE.is_l, self.__exp_slv.Boolean_True())
        pE_s = self.__exp_slv.mkTerm(Kind.EQUAL, pE.is_l, self.__exp_slv.Boolean_False())
        fr_isTrue = self.__exp_slv.mkTerm(Kind.AND,
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, pE_l,
                                                                self.__exp_slv.mkTerm(Kind.EQUAL, pE.l_v,
                                                                                      self.__exp_slv.FF_number(1))),
                                          self.__exp_slv.mkTerm(Kind.IMPLIES, pE_s,
                                                                self.__exp_slv.mkTerm(Kind.EQUAL, pE.s_v,
                                                                                      self.__exp_slv.FF_number(1)))
                                          )
        return fr_isTrue
        # if pE.is_l == self.__exp_slv.Boolean_True():
        #     if pE.l_v != self.__exp_slv.FF_number(0):
        #         return self.__exp_slv.Boolean_True()
        #     else:
        #         return self.__exp_slv.Boolean_False()
        #     # condition1 = self.__exp_slv.mkFFTerm_Eq(pE.l_v, 0)
        #     # condition2 = self.__exp_slv.mkFFTerm_Neq(pE.l_v, 0)
        #     # result1 = self.__exp_slv.mkTerm(Kind.EQUAL, result, 0)
        #     # result2 = self.__exp_slv.mkTerm(Kind.EQUAL, result, self.__exp_slv.FF_number(1))
        #     # return self.__exp_slv.mkTerm(Kind.AND,
        #     #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result1),
        #     #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result2)
        #     #                              )
        # else:
        #     if pE.s_v != self.__exp_slv.FF_number(0):
        #         return self.__exp_slv.Boolean_True()
        #     else:
        #         return self.__exp_slv.Boolean_False()
        #     # condition1 = self.__exp_slv.mkFFTerm_Eq(pE.s_v, 0)
        #     # condition2 = self.__exp_slv.mkFFTerm_Neq(pE.s_v, 0)
        #     # result1 = self.__exp_slv.mkTerm(Kind.EQUAL, result, 0)
        #     # result2 = self.__exp_slv.mkTerm(Kind.EQUAL, result, self.__exp_slv.FF_number(1))
        #     # return self.__exp_slv.mkTerm(Kind.AND,
        #     #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result1),
        #     #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result2)
        #     #                              )

    def and_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        b_n = FrElementModel.construct_value('b_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_andl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before_a_n,
                                             before_b_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_And(a_n.l_v, b_n.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_andl1ml2m

    def and_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        fr_andl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before_a_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_And(a_n.l_v, b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_andl1ml2n

    def and_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_andl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before_b_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_And(a.l_v, b_n.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_andl1nl2m

    def and_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_andl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_And(a.l_v, b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_andl1nl2n

    def and_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')

        Ge_0 = self.__exp_slv.mkFFTerm_Ge(b.s_v, self.__exp_slv.FF_number(0))
        Lt_0 = self.__exp_slv.mkFFTerm_Lt(b.s_v, self.__exp_slv.FF_number(0))
        # is right?
        before_b_n = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, Ge_0,
                                                                 self.__exp_slv.mkTerm(Kind.EQUAL, b_n.l_v, b.s_v)),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, Lt_0,
                                                                 self.Fr_toLongNormal(b_n, b))
                                           )

        fr_andl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_And(a_n.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_andl1ms2

    def and_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)
        fr_andl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_And(a.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_andl1ns2

    def and_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_ands1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_And(a_n.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_ands1l2m

    def and_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        fr_ands1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_And(a_n.l_v, b.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_ands1l2n

    def and_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        # ab_Ge0 = self.__exp_slv.mkTerm(Kind.AND,
        #                                self.__exp_slv.mkFFTerm_Ge(a.s_v, self.__exp_slv.FF_number(0)),
        #                                self.__exp_slv.mkFFTerm_Ge(b.s_v, self.__exp_slv.FF_number(0))
        #                                )
        # ab_Ge0_result = self.__exp_slv.mkTerm(Kind.AND,
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL,
        #                                                             r.s_v,
        #                                                             self.__exp_slv.mkFFTerm_Bit_And(a.s_v, b.s_v)),
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
        #                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
        #                                       )
        # fr_ands1s2_s = self.__exp_slv.mkTerm(Kind.IMPLIES,
        #                                      ab_Ge0,
        #                                      ab_Ge0_result
        #                                      )

        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_ands1s2_o = self.__exp_slv.mkTerm(Kind.AND,
                                             before_a_n,
                                             before_b_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_And(a_n.l_v, b_n.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_ands1s2_o

    def Fr_band(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        and_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        and_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        and_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        and_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        and_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        and_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        and_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        and_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        and_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        fr_band = self.__exp_slv.mkTerm(Kind.AND,
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_l1ml2m, self.and_l1ml2m(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_l1ml2n, self.and_l1ml2n(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_l1nl2m, self.and_l1nl2m(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_l1nl2n, self.and_l1nl2n(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_l1ms2, self.and_l1ms2(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_l1ns2, self.and_l1ns2(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_s1l2m, self.and_s1l2m(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_s1l2n, self.and_s1l2n(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, and_s1s2, self.and_s1s2(r, a, b))
                                        )

        return fr_band

    def xor_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        b_n = FrElementModel.construct_value('b_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_xorl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before_a_n,
                                             before_b_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_Xor(a_n.l_v, b_n.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_xorl1ml2m

    def xor_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        fr_xorl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before_a_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_Xor(a_n.l_v, b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_xorl1ml2n

    def xor_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_xorl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before_b_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_Xor(a.l_v, b_n.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_xorl1nl2m

    def xor_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_xorl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_Xor(a.l_v, b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_xorl1nl2n

    def xor_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')

        Ge_0 = self.__exp_slv.mkFFTerm_Ge(b.s_v, self.__exp_slv.FF_number(0))
        Lt_0 = self.__exp_slv.mkFFTerm_Lt(b.s_v, self.__exp_slv.FF_number(0))
        # is right?
        before_b_n = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, Ge_0,
                                                                 self.__exp_slv.mkTerm(Kind.EQUAL, b_n.l_v, b.s_v)),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, Lt_0,
                                                                 self.Fr_toLongNormal(b_n, b))
                                           )

        fr_xorl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Xor(a_n.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_xorl1ms2

    def xor_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)
        fr_xorl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Xor(a.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_xorl1ns2

    def xor_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_xors1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Xor(a_n.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_xors1l2m

    def xor_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        fr_xors1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Xor(a_n.l_v, b.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_xors1l2n

    def xor_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_xors1s2_o = self.__exp_slv.mkTerm(Kind.AND,
                                             before_a_n,
                                             before_b_n,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkFFTerm_Bit_Xor(a_n.l_v, b_n.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_xors1s2_o

    def Fr_bxor(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        xor_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        xor_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        xor_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        xor_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        xor_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        xor_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        xor_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        xor_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        xor_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        fr_bxor = self.__exp_slv.mkTerm(Kind.AND,
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_l1ml2m, self.xor_l1ml2m(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_l1ml2n, self.xor_l1ml2n(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_l1nl2m, self.xor_l1nl2m(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_l1nl2n, self.xor_l1nl2n(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_l1ms2, self.xor_l1ms2(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_l1ns2, self.xor_l1ns2(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_s1l2m, self.xor_s1l2m(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_s1l2n, self.xor_s1l2n(r, a, b)),
                                        self.__exp_slv.mkTerm(Kind.IMPLIES, xor_s1s2, self.xor_s1s2(r, a, b))
                                        )

        return fr_bxor

    def or_l1ml2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        b_n = FrElementModel.construct_value('b_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_orl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Or(a_n.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_orl1ml2m

    def or_l1ml2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        fr_orl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Or(a_n.l_v, b.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_orl1ml2n

    def or_l1nl2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_orl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Or(a.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_orl1nl2m

    def or_l1nl2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        fr_orl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Or(a.l_v, b.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_orl1nl2n

    def or_l1ms2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')

        Ge_0 = self.__exp_slv.mkFFTerm_Ge(b.s_v, self.__exp_slv.FF_number(0))
        Lt_0 = self.__exp_slv.mkFFTerm_Lt(b.s_v, self.__exp_slv.FF_number(0))
        # is right?
        before_b_n = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, Ge_0,
                                                                 self.__exp_slv.mkTerm(Kind.EQUAL, b_n.l_v, b.s_v)),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, Lt_0,
                                                                 self.Fr_toLongNormal(b_n, b))
                                           )

        fr_orl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                           before_a_n,
                                           before_b_n,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkFFTerm_Bit_Or(a_n.l_v, b_n.l_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                           )

        return fr_orl1ms2

    def or_l1ns2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)
        fr_orl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                           before_b_n,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkFFTerm_Bit_Or(a.l_v, b_n.l_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                           )

        return fr_orl1ns2

    def or_s1l2m(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toNormal(b_n, b)
        fr_ors1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                           before_a_n,
                                           before_b_n,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkFFTerm_Bit_Or(a_n.l_v, b_n.l_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                           )

        return fr_ors1l2m

    def or_s1l2n(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        fr_ors1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                           before_a_n,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkFFTerm_Bit_Or(a_n.l_v, b.l_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                           )

        return fr_ors1l2n

    def or_s1s2(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_ors1s2_o = self.__exp_slv.mkTerm(Kind.AND,
                                            before_a_n,
                                            before_b_n,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkFFTerm_Bit_Or(a_n.l_v, b_n.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_ors1s2_o

    def Fr_bor(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_l = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_True())
        a_s = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_l, self.__exp_slv.Boolean_False())
        a_n = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_False())
        a_m = self.__exp_slv.mkTerm(Kind.EQUAL, a.is_m, self.__exp_slv.Boolean_True())
        b_l = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_True())
        b_s = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_l, self.__exp_slv.Boolean_False())
        b_n = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_False())
        b_m = self.__exp_slv.mkTerm(Kind.EQUAL, b.is_m, self.__exp_slv.Boolean_True())

        or_l1ml2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_m)
        or_l1ml2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_l, b_n)
        or_l1nl2m = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_m)
        or_l1nl2n = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_l, b_n)
        or_l1ms2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_m, b_s)
        or_l1ns2 = self.__exp_slv.mkTerm(Kind.AND, a_l, a_n, b_s)
        or_s1l2m = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_m)
        or_s1l2n = self.__exp_slv.mkTerm(Kind.AND, a_s, b_l, b_n)
        or_s1s2 = self.__exp_slv.mkTerm(Kind.AND, a_s, b_s)

        fr_bor = self.__exp_slv.mkTerm(Kind.AND,
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_l1ml2m, self.or_l1ml2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_l1ml2n, self.or_l1ml2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_l1nl2m, self.or_l1nl2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_l1nl2n, self.or_l1nl2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_l1ms2, self.or_l1ms2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_l1ns2, self.or_l1ns2(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_s1l2m, self.or_s1l2m(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_s1l2n, self.or_s1l2n(r, a, b)),
                                       self.__exp_slv.mkTerm(Kind.IMPLIES, or_s1s2, self.or_s1s2(r, a, b))
                                       )

        return fr_bor

    def Fr_bnot(self, r: FrElementModel, a: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)

        fr_bnot = self.__exp_slv.mkTerm(Kind.AND,
                                        before_a_n,
                                        self.__exp_slv.mkTerm(Kind.EQUAL,
                                                              r.l_v,
                                                              self.__exp_slv.mkFFTerm_bit_Complement(a_n.l_v)),
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                        )
        return fr_bnot

    def Fr_lnot(self, r: FrElementModel, a: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)

        a_n_0 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, self.__exp_slv.FF_number(0))
        a_n_1 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, self.__exp_slv.FF_number(0))

        a_n_0_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                             a_n_0,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(1)))
        a_n_1_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                             a_n_1,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(0)))

        fr_lnot = self.__exp_slv.mkTerm(Kind.AND,
                                        before_a_n,
                                        a_n_0_result,
                                        a_n_1_result,
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                        )
        return fr_lnot

    def Fr_land(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        a_n_0 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, self.__exp_slv.FF_number(0))
        a_n_1 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, self.__exp_slv.FF_number(0))
        b_n_0 = self.__exp_slv.mkFFTerm_Eq(b_n.l_v, self.__exp_slv.FF_number(0))
        b_n_1 = self.__exp_slv.mkFFTerm_Neq(b_n.l_v, self.__exp_slv.FF_number(0))

        an0_bn0_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_0,
                                               b_n_0,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(0)))
        an0_bn1_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_0,
                                               b_n_1,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(0)))
        an1_bn1_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_1,
                                               b_n_1,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(1)))
        an1_bn0_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_1,
                                               b_n_0,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(0)))
        fr_land = self.__exp_slv.mkTerm(Kind.AND,
                                        before_a_n,
                                        before_b_n,
                                        an0_bn0_result,
                                        an0_bn1_result,
                                        an1_bn0_result,
                                        an1_bn1_result,
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                        )
        return fr_land

    def Fr_lor(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        a_n_0 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, self.__exp_slv.FF_number(0))
        a_n_1 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, self.__exp_slv.FF_number(0))
        b_n_0 = self.__exp_slv.mkFFTerm_Eq(b_n.l_v, self.__exp_slv.FF_number(0))
        b_n_1 = self.__exp_slv.mkFFTerm_Neq(b_n.l_v, self.__exp_slv.FF_number(0))

        an0_bn0_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_0,
                                               b_n_0,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(0)))
        an0_bn1_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_0,
                                               b_n_1,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(1)))
        an1_bn1_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_1,
                                               b_n_1,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(1)))
        an1_bn0_result = self.__exp_slv.mkTerm(Kind.IMPLIES,
                                               a_n_1,
                                               b_n_0,
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, self.__exp_slv.FF_number(1)))

        fr_lor = self.__exp_slv.mkTerm(Kind.AND,
                                       before_a_n,
                                       before_b_n,
                                       an0_bn0_result,
                                       an0_bn1_result,
                                       an1_bn0_result,
                                       an1_bn1_result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                       )
        return fr_lor

    def Fr_shr(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_shr = self.__exp_slv.mkTerm(Kind.AND,
                                       before_a_n,
                                       before_b_n,
                                       self.__exp_slv.mkTerm(Kind.EQUAL,
                                                             r.l_v,
                                                             self.__exp_slv.mkFFTerm_Right_Shift(a_n.l_v, b_n.l_v)),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                       )
        return fr_shr

    def Fr_shl(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_shl = self.__exp_slv.mkTerm(Kind.AND,
                                       before_a_n,
                                       before_b_n,
                                       self.__exp_slv.mkTerm(Kind.EQUAL,
                                                             r.l_v,
                                                             self.__exp_slv.mkFFTerm_Left_Shift(a_n.l_v, b_n.l_v)),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                       )
        return fr_shl

    def Fr_idiv(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_idiv = self.__exp_slv.mkTerm(Kind.AND,
                                        before_a_n,
                                        before_b_n,
                                        self.__exp_slv.mkTerm(Kind.EQUAL,
                                                              r.l_v,
                                                              self.__exp_slv.mkFFTerm_IntDiv(a_n.l_v, b_n.l_v)),
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                        )
        return fr_idiv

    def Fr_mod(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_mod = self.__exp_slv.mkTerm(Kind.AND,
                                       before_a_n,
                                       before_b_n,
                                       self.__exp_slv.mkTerm(Kind.EQUAL,
                                                             r.l_v,
                                                             self.__exp_slv.mkFFTerm_Mod(a_n.l_v, b_n.l_v)),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                       )
        return fr_mod

    def Fr_pow(self, r: FrElementModel, a: FrElementModel, b: FrElementModel):
        a_n = FrElementModel.construct_value('a_n')
        before_a_n = self.Fr_toLongNormal(a_n, a)
        b_n = FrElementModel.construct_value('b_n')
        before_b_n = self.Fr_toLongNormal(b_n, b)

        fr_pow = self.__exp_slv.mkTerm(Kind.AND,
                                       before_a_n,
                                       before_b_n,
                                       self.__exp_slv.mkTerm(Kind.EQUAL,
                                                             r.l_v,
                                                             self.__exp_slv.mkFFTerm_Pow(a_n.l_v, b_n.l_v)),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                       )
        return fr_pow

    def Fr_if(self, expaux: FrElementModel, if_terms: list, else_terms: list):
        condition_False = self.__exp_slv.mkTerm(Kind.AND,
                                                self.__exp_slv.mkTerm(Kind.AND,
                                                                      self.__exp_slv.mkTerm(Kind.EQUAL, expaux.l_v,
                                                                                            self.__exp_slv.FF_number(
                                                                                                0)),
                                                                      self.__exp_slv.mkTerm(Kind.EQUAL, expaux.is_l,
                                                                                            self.__exp_slv.Boolean_True())),
                                                self.__exp_slv.mkTerm(Kind.AND,
                                                                      self.__exp_slv.mkTerm(Kind.EQUAL, expaux.s_v,
                                                                                            self.__exp_slv.FF_number(
                                                                                                0)),
                                                                      self.__exp_slv.mkTerm(Kind.EQUAL, expaux.is_l,
                                                                                            self.__exp_slv.Boolean_False()))
                                                )
        condition_True = self.__exp_slv.mkTerm(Kind.NOT, condition_False)

        combined_if_terms = None
        combined_else_terms = None

        if else_terms:
            combined_else_terms = else_terms[0]
            for term in else_terms[1:]:
                combined_else_terms = self.__exp_slv.mkTerm(Kind.AND, combined_else_terms, term)
        else:
            #print(self.lvar_iterate)
            #print(self.element_dict)
            combined_else_terms = self.__exp_slv.mkTerm(Kind.EQUAL, self.__exp_slv.Boolean_True(), self.__exp_slv.Boolean_True())
            for key in self.lvar_iterate.keys():
                origin = self.element_dict[key]
                new = self.element_dict[f"{key}_{self.lvar_iterate[key]}"]
                temp_term = self.__exp_slv.mkTerm(Kind.AND,
                                                  self.__exp_slv.mkTerm(Kind.EQUAL, origin.l_v, new.l_v, ),
                                                  self.__exp_slv.mkTerm(Kind.EQUAL, origin.is_l, new.is_l))
                combined_else_terms = self.__exp_slv.mkTerm(Kind.AND, combined_else_terms, temp_term)
        if if_terms:
            combined_if_terms = if_terms[0]
            for term in if_terms[1:]:
                combined_if_terms = self.__exp_slv.mkTerm(Kind.AND, combined_if_terms, term)

        fr_if = self.__exp_slv.mkTerm(Kind.AND,
                                      self.__exp_slv.mkTerm(Kind.IMPLIES, condition_False, combined_else_terms),
                                      self.__exp_slv.mkTerm(Kind.IMPLIES, condition_True, combined_if_terms)
                                      )
        return fr_if

    def append_term(self, term):
        """
        根据条件将 term 添加到相应的数组。
        """
        if self.use_if_terms:
            self.if_terms.append(term)
        elif self.use_else_terms:
            self.else_terms.append(term)
        elif self.use_normal_terms:
            self.directory_terms.append(term)

    def parse_sym_file(self, filepath):
        with open(filepath, 'r') as file:
            for line in file:
                parts = line.strip().split(',')
                if len(parts) == 4:
                    signal_index = int(parts[0])
                    signal_name = parts[3].strip()
                    self.signal_map[signal_index] = signal_name

    def get_signal_name(self, index):
        if index in self.signal_map:
            #print(self.signal_map)
            return self.signal_map[index]
        else:
            raise ValueError(f"Signal index {index} not found in the signal map.")

    def process_expression(self, expression):
        # 使用正则表达式替换 Fr_toInt(&lvar[n])，提取并从 int_dict 中替换值
        def replace_lvar_to_int(match):
            lvar_index = match.group(1)  # 提取 lvar 中的索引
            if f"lvar[{lvar_index}]" in self.int_dict:
                return str(self.int_dict[f"lvar[{lvar_index}]"])  # 替换为 int_dict 中的值
            elif f"lvarcall[{lvar_index}]" in self.int_dict:
                return str(self.int_dict[f"lvarcall[{lvar_index}]"])  # 替换为 int_dict 中的值
            else:
                raise ValueError(f"Key lvar[{lvar_index}] not found in int_dict")

        def replace_expaux_to_int(match):
            expaux_index = match.group(1)  # 提取 lvar 中的索引
            if f"expaux[{expaux_index}]" in self.int_dict:
                return str(self.int_dict[f"expaux[{expaux_index}]"])  # 替换为 int_dict 中的值
            else:
                raise ValueError(f"Key lvar[{expaux_index}] not found in int_dict")

        # 匹配并替换所有 Fr_toInt(&lvar[n])，n 是任意整数
        if 'lvar' in expression:
            processed_expression = re.sub(r'Fr_toInt\(&lvar\[(\d+)\]\)', replace_lvar_to_int, expression)
        elif 'lvarcall' in expression:
            processed_expression = re.sub(r'Fr_toInt\(&lvarcall\[(\d+)\]\)', replace_lvar_to_int, expression)
        elif 'expaux' in expression:
            processed_expression = re.sub(r'Fr_toInt\(&expaux\[(\d+)\]\)', replace_expaux_to_int, expression)
        return processed_expression

    def extract_index(self, part, mySignalStart):
        global mySub_idx
        part = part.strip().rstrip(';')
        if part.startswith('&'):
            part = part[1:]
        if 'ctx->signalValues' in part:
            # Extract cmp_index_ref value
            start_index = part.find('[') + 1
            end_index = part.find(']')
            subcomponent_ref = part[start_index:end_index].strip()

            # Use the value_to_subfunction to calculate the index
            if self.value_to_subtemplate is not None:
                component_index = self.value_to_subtemplate
                start_pos = self.template_start_position_dict.get(component_index, 0)
                #print(self.template_start_position_dict)
                # 检查是否有 Fr_toInt(&lvar[n])，并替换为 int_dict 中的值
                if 'Fr_toInt' in part:
                    # 提取和替换 Fr_toInt(&lvar[0]) 的值
                    part = self.process_expression(part)

                    # 继续解析 offset 部分
                    offset_expression = part.split('+', 1)[1].split(']')[0].strip()
                    number = start_pos + eval(offset_expression)  # 使用 eval 计算复杂表达式
                    if (number == 9):
                        print(number)
                    signal_name = self.get_signal_name(number)
                else:
                    number = start_pos + int(part.split('+')[1].split(']')[0].strip())  # Extract offset
                    signal_name = self.get_signal_name(number)
                if signal_name not in self.element_dict:
                    self.element_dict[signal_name] = FrElementModel.construct_value(signal_name)
                return signal_name
            elif 'ctx->componentMemory' in part:
                match = re.search(r'mySubcomponents\[(\d+)\]', part)
                if match:
                    mySub_idx = match.group(1)  # 获取 0

                # 查找 self.mySubcomponents[0] 的值
                if mySub_idx in self.mySubcomponents:
                    temp1 = self.mySubcomponents[mySub_idx]  # 获取 temp1

                    temp2 = None
                    for key, value in self.template_name_componentMemory.items():
                        #print(key)
                        if value == temp1:
                            temp2 = key
                            break

                    # 查找 self.function_name_signalStart[temp2] 的值
                    if temp2 in self.template_name_signalStart:
                        temp3 = self.template_name_signalStart[temp2]  # 获取 temp3

                        # 提取 signalStart + 后面的数字
                        number_match = re.search(r'signalStart \+ (\d+)', part)
                        if number_match:
                            number = int(number_match.group(1))  # 获取 number

                            # 计算 temp3 + number
                            result = temp3 + number
                            signal_name = self.get_signal_name(result)
                            if signal_name not in self.element_dict:
                                self.element_dict[signal_name] = FrElementModel.construct_value(signal_name)
                            return signal_name

        elif part.startswith('expaux') or part.startswith('circuitConstants') or part.startswith('lvar'):
            # if part not in self.element_dict: # reuse the lvar
            if part.startswith('circuitConstants'):
                self.element_dict[part] = self.constants_dict[part]
            else:
                if self.element_dict.get(part) is None:
                    self.element_dict[part] = FrElementModel.construct_value(part)
                    self.new_expaux = False
                else:
                    if self.new_expaux:
                        self.element_dict[part] = FrElementModel.construct_value(part)
                        self.new_expaux = False
                    else:
                        pass
            return part
        else:
            # print(mySignalStart)

            parts = part.split('[', 1)
            index_part = parts[1].rsplit(']', 1)
            index_str = index_part[0].strip().rstrip(';')
            if 'Fr_toInt' in index_str:
                # 提取和替换 Fr_toInt(&lvar[0]) 的值
                index_str = self.process_expression(index_str)

                # 继续解析 offset 部分
                offset_expression = index_str.split('+', 1)[1].split(']')[0].strip()
                number = (mySignalStart + eval(offset_expression)) % self.p_int  # 使用 eval 计算复杂表达式
                if number == 893:
                    print(2)
                signal_name = self.get_signal_name(number)
            else:
                index = int(index_str.replace('mySignalStart +', '').strip()) + mySignalStart
                signal_name = self.get_signal_name(index)
            if signal_name not in self.element_dict:
                self.element_dict[signal_name] = FrElementModel.construct_value(signal_name)
            return signal_name

    def deal_dat(self, dat_path, num):
        file = open(dat_path, 'rb')
        content = file.read()
        file.close()

        # 每组40个字节，从文件末尾取 num * 40 个字节
        total_bytes_to_read = num * 40
        groups = content[-total_bytes_to_read:]

        for i in range(num):
            group = groups[-(i + 1) * 40: -(i * 40) if i > 0 else None]
            short = group[0:4]
            type = group[4:8]
            long = group[8:]

            short_value = int.from_bytes(short, byteorder='little', signed=True)
            #print(f'Group {i + 1} Short Value: {hex(short_value)}')

            type_value = int.from_bytes(type, byteorder='little', signed=False)
            #print(f'Group {i + 1} Type Value: {hex(type_value)}')
            if_long = bool(type_value & (1 << 31))
            if_mong = bool(type_value & (1 << 30))

            #print(f'Group {i + 1} if_long = {if_long}')
            #print(f'Group {i + 1} if_mong = {if_mong}')

            long_value_0 = int.from_bytes(long[0:8], byteorder='little', signed=False)
            long_value_1 = int.from_bytes(long[8:16], byteorder='little', signed=False)
            long_value_2 = int.from_bytes(long[16:24], byteorder='little', signed=False)
            long_value_3 = int.from_bytes(long[24:32], byteorder='little', signed=False)

            long_value = long_value_3
            long_value = (long_value << 64) + long_value_2
            long_value = (long_value << 64) + long_value_1
            long_value = (long_value << 64) + long_value_0
            #print(f'Group {i + 1} Long Value: {hex(long_value)}')

            true_int = None
            if if_long:
                if if_mong:
                    element_type = 0xC0000000
                    true_int = self.Rr_int * long_value % self.p_int
                else:
                    element_type = 0x80000000
                    true_int = long_value % self.p_int
            else:
                if if_mong:
                    element_type = 0x40000000
                    true_int = short_value
                else:
                    element_type = 0x00000000
                    true_int = short_value % self.p_int

            self.constants_dict[f'circuitConstants[{num - 1 - i}]'] = FrElementModel.construct_constant(
                f'circuitConstants[{num - 1 - i}]',
                short_value, long_value, element_type)
            self.int_dict[f'circuitConstants[{num - 1 - i}]'] = true_int

    # 定义位移操作的辅助函数
    def shift_right(self, x, k, p):
        b = (p - 1).bit_length()  # 计算p的有效位数
        mask = (1 << b) - 1  # 计算掩码

        if 0 <= k <= p // 2:
            return x // (2 ** k)  # x >> k
        elif p // 2 + 1 <= k < p:
            return (x * (2 ** (p - k)) & ~mask) % p  # x << (p - k)

    def shift_left(self, x, k, p):
        b = (p - 1).bit_length()
        mask = (1 << b) - 1

        if 0 <= k <= p // 2:
            return (x * (2 ** k) & ~mask) % p  # x << k
        elif p // 2 + 1 <= k < p:
            return x // (2 ** (p - k))  # x >> (p - k)

    def evaluate_expression_extend(self, line):
        def evaluate_index(index_str):
            """
            计算包含 'mySignalStart +' 的索引值。
            """
            # 检查是否包含 "mySignalStart +"
            if "mySignalStart +" in index_str:
                # 提取偏移量并计算
                offset = int(re.search(r"mySignalStart \+ (\d+)", index_str).group(1))
                return self.my_signal_start + offset
            else:
                # 如果没有 "mySignalStart +"，直接转换为整数
                return int(index_str)

        # 正则表达式匹配其他位操作（包含复杂索引）
        match_three_operate = re.match(
            r'Fr_(shr|shl|band|bor|bxor|land|lor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)', line
        )
        # 正则表达式匹配 一个操作数 操作
        match_two_operate = re.match(r'Fr_(bnot|square|lnot|neg)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)', line)

        # 处理 一个操作数 操作
        if match_two_operate:
            operation = match_two_operate.group(1)  # 操作类型，bnot 或 square 或neg
            result_var = match_two_operate.group(2)  # 结果存储的变量名
            result_index = evaluate_index(match_two_operate.group(3))  # 结果存储的索引
            operand_var = match_two_operate.group(4)  # 操作数的变量名
            operand_index = evaluate_index(match_two_operate.group(5))  # 操作数的索引
            # 从 int_dict 中获取操作数的值
            operand = self.int_dict.get(f"{operand_var}[{operand_index}]", 0)
            result = None
            if operation == "bnot":
                # 执行按位取反操作并取模
                result = (~operand) % self.p_int
                #print(f"Processed bnot: ~{operand} = {result} (mod {self.p_int})")

            elif operation == "square":
                # 执行平方操作并取模
                result = (operand ** 2) % self.p_int

            elif operation == "neg":
                # 执行负数操作并取模
                result = (-operand) % self.p_int

            elif operation == "lnot":
                # 执行平方操作并取模
                result = (not operand) % self.p_int
                #print(f"Processed lnot: ")

            # 将结果存储回 int_dict
            self.int_dict[f"{result_var}[{result_index}]"] = result

        elif match_three_operate:
            operation = match_three_operate.group(1)  # 操作类型，如 shr, shl 等
            result_var = match_three_operate.group(2)  # 结果存储的变量名（expaux）
            result_index = evaluate_index(match_three_operate.group(3))  # 结果存储的索引
            left_var = match_three_operate.group(4)  # 左操作数的变量名（lvar）
            left_index = evaluate_index(match_three_operate.group(5))  # 左操作数的索引
            right_var = match_three_operate.group(6)  # 右操作数的变量名（circuitConstants）
            right_index = evaluate_index(match_three_operate.group(7))  # 右操作数的索引
            # print(result_var)
            # print(left_var)
            # print(right_var)
            # print(operation)
            # 从 int_dict 中获取 expaux[], lvar[], circuitConstants[] 的值
            left = self.int_dict.get(f"{left_var}[{left_index}]", 0)
            right = self.int_dict.get(f"{right_var}[{right_index}]", 0)
            result = self.int_dict.get(f"{result_var}[{result_index}]", 0)

            # 执行相应的操作
            if operation == 'shr':
                result = self.shift_right(left, right, self.p_int)
            elif operation == 'shl':
                result = self.shift_left(left, right, self.p_int)
            elif operation == 'band':
                result = (left & right) % self.p_int
            elif operation == 'bor':
                result = (left | right) % self.p_int
            elif operation == 'bxor':
                result = (left ^ right) % self.p_int
            elif operation == 'land':
                result = (left and right) % self.p_int
            elif operation == 'lor':
                result = (left or right) % self.p_int
            # 将结果存储回 int_dict
            self.int_dict[f"{result_var}[{result_index}]"] = result
            # 打印输出调试
            #print(f"Processed {operation}: {left} {operation} {right} = {result} (mod {self.p_int})")

    def get_value(self, source):
        # 检查 source 是否包含 "mySignalStart +"
        if "mySignalStart +" in source:
            # 提取 mySignalStart 后面的偏移值，并进行计算
            offset = int(re.search(r"mySignalStart \+ (\d+)", source).group(1))
            calculated_index = self.my_signal_start + offset
            # 获取计算后的变量名称
            calculated_source = re.sub(r"\[mySignalStart \+ \d+\]", f"[{calculated_index}]", source)
            return self.int_dict.get(calculated_source, 0)
        else:
            # 如果没有包含 "mySignalStart +"，直接返回字典中的值
            return self.int_dict.get(source, 0)

    # 解析并计算表达式
    def evaluate_expression_three(self, operation):
        result = None
        match = re.match(r'Fr_(add|mul|div|sub|lt|gt|leq|geq|eq|neq|mod|idiv|pow)\(&expaux\[(\d+)\],', operation)
        if match:
            op = match.group(1)
            dest = match.group(2)

            # 手动解析 src1 和 src2
            parts = operation.split(',', 2)  # 分成三部分
            src1 = parts[1].strip().lstrip('&')
            src2 = parts[2].rsplit(')', 1)[0].lstrip('&')  # 去掉结尾的 `)` 和开头的 `&`

            # 获取 src1 和 src2 的值
            src1_val = self.get_value(src1)
            src2_val = self.get_value(src2)

            if op == 'add':
                result = (src1_val + src2_val) % self.p_int
            elif op == 'mul':
                result = (src1_val * src2_val) % self.p_int
            elif op == 'div':
                inverse = pow(src2_val, -1, self.p_int)
                result = (src1_val * inverse) % self.p_int
            elif op == 'sub':
                result = (src1_val - src2_val) % self.p_int
            elif op == 'lt':
                result = 1 if src1_val < src2_val else 0
            elif op == 'gt':
                result = 1 if src1_val > src2_val else 0
            elif op == 'leq':
                result = 1 if src1_val <= src2_val else 0
            elif op == 'geq':
                result = 1 if src1_val >= src2_val else 0
            elif op == 'eq':
                result = 1 if src1_val == src2_val else 0
            elif op == 'neq':
                result = 1 if src1_val != src2_val else 0
            elif op == 'mod':
                result = (src1_val % src2_val) % self.p_int
            elif op == 'idiv':
                result = (src1_val // src2_val) % self.p_int
            elif op == 'pow':
                result = (src1_val ** src2_val) % self.p_int
            self.int_dict[f'expaux[{dest}]'] = result

    # 解析循环体中的操作
    def parse_while_loop(self, while_loop_code):
        dest_var = None
        dest_key = None
        for line in while_loop_code:
            if re.search(r'PFrElement aux_dest = &lvar\[\d+\]', line):
                dest_var = re.findall(r'&lvar\[\d+\]', line)[0]
                dest_key = dest_var[1:]
            elif re.search(r'PFrElement aux_dest = &lvarcall\[\d+\]', line):
                dest_var = re.findall(r'&lvarcall\[\d+\]', line)[0]
                dest_key = dest_var[1:]
            if re.match(r'Fr_(add|mul|div|sub|lt|gt|leq|geq|eq|neq|mod|idiv|pow)\(&expaux\[(\d+)\],&\w+\[[^]]+\],'
                        r'&\w+\[[^]]+\]\)', line) and 'mySignalStart' not in line:
                self.evaluate_expression_three(line)
            elif re.match(
                    r'Fr_(shr|shl|band|bor|bxor|land|lor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                    line) and 'mySignalStart' not in line:
                self.evaluate_expression_extend(line)
            elif re.match(r'Fr_(bnot|square|lnot|neg)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                          line) and 'mySignalStart' not in line:
                self.evaluate_expression_extend(line)
            elif re.match(r'Fr_copy\(aux_dest,\&(expaux\[\d+\]|circuitConstants\[\d+\])\)',
                          line) and 'mySignalStart' not in line:
                src_var = re.findall(r'(&expaux\[\d+\]|&circuitConstants\[\d+\])', line)[0]
                self.int_dict[dest_key] = self.int_dict.get(src_var[1:], 0)

    # 计算循环次数
    def calculate_loop_iterations(self, loop_condition_lines, while_loop_code):
        iterations = 0
        temp_dict = self.int_dict
        while True:
            for line in loop_condition_lines:
                self.evaluate_expression_three(line)

            if self.int_dict.get('expaux[0]', 0) == 0:
                break
            iterations += 1
            self.parse_while_loop(while_loop_code)
        self.int_dict = temp_dict
        return iterations

    def dealWhile(self, i, lines):

        loop_start = i
        in_while_loop = True
        loop_condition_lines = []
        while_loop_code = []
        update_code = []
        circom_line_number = None
        loop_end = None
        # 向前搜索一行，获取circom行号
        previous_line = lines[i - 1].strip().rstrip(';') if i > 0 else None
        if previous_line and re.search(r'// line circom \d+', previous_line):
            circom_line_number = re.findall(r'// line circom (\d+)', previous_line)[0]
        if in_while_loop and circom_line_number:
            for j in range(i - 1, -1, -1):
                line = lines[j].strip().rstrip(';')
                if re.search(rf'// line circom {circom_line_number}', line):
                    loop_condition_lines.insert(0, line)
                else:
                    loop_end = j + 1
                    break

        # 搜索循环体内的操作和完整的循环体代码
        for i in range(loop_start + 1, len(lines)):
            line = lines[i].strip().rstrip(';')
            if loop_end is not None and lines[loop_end].strip().rstrip(';') in line:
                break
            else:
                while_loop_code.append(line)

        # 搜索the代码 need to update later
        for i in range(loop_start + 1, len(lines)):
            line = lines[i].strip().rstrip(';')
            if previous_line in line:
                update_code.append(line)
                loop_end = i
                break
            else:
                update_code.append(line)

        return loop_condition_lines, while_loop_code, update_code, loop_start, loop_end

    # 更新代码中的循环部分
    def update_lines(self, lines, loop_start, loop_end, update_code, iterations):
        updated_lines = lines[:loop_start - 1]
        for _ in range(iterations):
            updated_lines.extend(update_code)
        self.update_lines_end.append(len(updated_lines) - 1)
        self.origin_lines_locate.append(loop_end + 1)
        updated_lines.extend(lines[loop_end + 1:])
        return updated_lines

    def directory_2_smt(self, symFile_path, code_block_file_path, componentNum):

        self.parse_sym_file(symFile_path)
        # 打开并读取 code_block_file_path 对应的文件内容
        with open(code_block_file_path, 'r') as file:
            lines = file.readlines()

        # 提取倒数第三行
        third_last_line = lines[-4].strip()

        match = re.match(r'(\w+)_create\((\d+),(\d+),', third_last_line)

        if match:
            # 提取 temp_1，create(1 中的 1 和 0
            name = match.group(1)
            create_value_1 = match.group(2)
            create_value_2 = match.group(3)
            # 将它们作为键值对存储在字典中
            self.template_name_componentMemory = {name: int(create_value_2)}
            self.template_name_signalStart = {name: int(create_value_1)}
            self.ctx_index_stack = [0]

        aux_dest = None
        i = 0
        componentNo = 0
        while i < len(lines):
            line = lines[i].strip().rstrip(';')
            if componentNo < componentNum:
                if '(Circom_CalcWit* ctx,FrElement* lvar,uint componentFather,FrElement* destination,int destination_size){' in line:
                    match = re.match(
                        r'\w+\s+(\w+)\s*\(Circom_CalcWit\* ctx,FrElement\* lvar,uint componentFather,FrElement\* destination,int destination_size\)\{',
                        line
                    )
                    if match:
                        function_name = match.group(1)  # 获取函数名
                        self.function_line_dict[function_name] = i

                if '_create(uint soffset,uint coffset,Circom_CalcWit* ctx,std::string componentName,uint componentFather){' in line:
                    # 向下搜索 8 行
                    # 提取函数名
                    function_line_match = re.search(r'(\w+)_create', line)
                    if function_line_match:
                        function_name = function_line_match.group(1)
                        for j in range(1, 9):
                            if i + j < len(lines):  # 检查索引是否越界
                                next_line = lines[i + j].strip()

                                # 如果发现 '_run(coffset,ctx)' 进入 if 分支
                                if '_run(coffset,ctx)' in next_line:
                                    self.template_name_direct[function_name] = True

                if '_run(uint ctx_index,Circom_CalcWit* ctx){' in line:
                    # 提取函数名
                    function_line_match = re.search(r'(\w+)_run', line)
                    if function_line_match:
                        function_name = function_line_match.group(1)
                        self.template_line_dict[function_name] = i
                        #print(function_name)
                        #print(i)
                        componentNo += 1
                i += 1
            else:
                break
        while i < len(lines):
            if self.update_lines_end and i == self.update_lines_end[-1]:
                lines = self.origin_lines[-1]
                if self.origin_lines:
                    self.origin_lines.pop()
                self.update_lines_end.pop()
                i = self.origin_lines_locate[-1]
                if self.origin_lines_locate:
                    self.origin_lines_locate.pop()
            line = lines[i].strip().rstrip(';')
            # print(line)
            if self.my_signal_start == 20 and i == 389:
                print(111)
            if 'Fr_add(&expaux[0],&lvar[37],&circuitConstants[1]); // line circom 45' in line:
                print(111111)
            # if 'PFrElement aux_dest = &lvar[93]' in line and 'Fr_add(&expaux[0],&lvar[93],&circuitConstants[2]); // line circom 126' in lines[i+2]:
            #     self.num_lvar93 += 1
            #     print(self.num_lvar93)
            # if self.lines_len != len(lines):
            #                     # 打开一个文本文件进行写入，如果文件不存在会自动创建
            #     with open('/home/zeno/Desktop/BlockChain/OurTools/CompilerVerification/RAW/Verifier/temp_file/output.txt', 'w') as file:
            #         # 使用 writelines 方法将每行写入文件，确保每行末尾添加换行符
            #         file.writelines([line + '\n' for line in lines])
            #     self.lines_len = len(lines)
            #     temp2 = 0
            #     while temp2 < len(lines):
            #         if 'CompConstant_1_create(csoffset,aux_cmp_num,ctx,new_cmp_name,myId)' in lines[temp2]:
            #             self.num_lvar93 += 1
            #             print(self.num_lvar93)
            #             if self.num_lvar93 == 2:
            #                 print(line)
            #         temp2 += 1
            #         self.num_lvar93 = 0
            # if 'lvar[93]' in self.int_dict:
            #     if self.int_dict[
            #         'lvar[93]'] == 10:
            #         print(self.int_dict[
            #         'lvar[93]'])
            self.use_if_terms = False
            self.use_else_terms = False
            self.use_normal_terms = True
            if self.is_running_subtemplate and line.startswith('void '):
                # 判断当前行是否为新函数定义
                # self.is_running_subtemplate = False
                i = self.go_subtemplate_line[-1] + 1  # 返回到 temp 的下一个位置继续解析
                if self.go_subtemplate_line:
                    self.go_subtemplate_line.pop()
                if not self.go_subtemplate_line:
                    self.is_running_subtemplate = False
                # self.go_subtemplate_line = None
                # self.my_signal_start = 1
                if self.ctx_index_stack:
                    self.ctx_index_stack.pop()
                    key = None
                    for k, v in self.template_name_componentMemory.items():
                        if v == self.ctx_index_stack[-1]:
                            key = k
                            break
                    self.my_signal_start = self.template_name_signalStart[key]
                else:
                    self.my_signal_start = 1
                continue

            if self.is_running_subfunction and line.startswith('void '):
                # self.is_running_subfunction = False
                i = self.go_subfunction_line[-1] + 1
                if self.go_subfunction_line:
                    self.go_subfunction_line.pop()
                if not self.go_subfunction_line:
                    self.is_running_subfunction = False
                #self.go_subfunction_line = None
                self.which_subfunction = None
                continue

            if self.is_running_subfunction:
                # 替换 `lvar` 为 `self.function_replace_name`
                if 'lvar[' in line:
                    line = line.replace('lvar[', self.function_replace_name[self.which_subfunction] + '[')
                # 检查 `destination` 并替换
                if 'destination' in line:
                    line = line.replace('destination', self.function_destination[self.which_subfunction])

            if self.else_start_line <= i < self.else_end_line and self.if_else_type == 2:
                self.use_if_terms = False
                self.use_else_terms = True
                self.use_normal_terms = False
                # i += 1
                # continue
            elif self.if_start_line <= i < self.else_start_line and self.if_else_type == 2:
                self.use_if_terms = True
                self.use_else_terms = False
                self.use_normal_terms = False
            elif i == self.else_end_line and self.if_else_type == 2:
                self.directory_terms.append(self.Fr_if(self.element_dict[self.if_key], self.if_terms, self.else_terms))
                self.if_start_line = -1
                self.else_start_line = -1
                self.else_end_line = -1
            if self.else_start_line <= i < self.else_end_line and self.if_else_type == 1:
                i += 1
                continue

            if 'uint cmp_index_ref' in line:
                # Extract the value assigned to cmp_index_ref
                self.value_to_subtemplate = line.split('=')[1].strip(';').strip()

            # 记录 uint aux_create 的标记
            if 'uint aux_create =' in line:
                aux_create_match = re.search(r'uint aux_create = (\d+)', line)
                if aux_create_match:
                    self.current_aux_create = aux_create_match.group(1)
            elif 'int aux_cmp_num =' in line:
                # 提取等号后面的表达式部分
                expression = line.split('=')[1].strip()
                # 如果栈非空，使用栈顶的值替换 ctx_index
                if self.ctx_index_stack:
                    ctx_index_value = self.ctx_index_stack[-1]  # 获取栈顶元素
                    expression = expression.replace('ctx_index', str(ctx_index_value))
                # 计算表达式的结果
                result = eval(expression)  # 使用 eval 来计算表达式的值
                # 将结果压入栈
                self.ctx_index_stack.append(result)
                self.have_append_ctx_index[result] = True
                self.mySubcomponents[self.current_aux_create] = result
                #print(self.ctx_index_stack)

            # 记录起始位置
            elif 'uint csoffset = mySignalStart+' in line:
                # 提取 number
                csoffset_match = re.search(r'uint csoffset = mySignalStart\+(\d+)', line)
                if csoffset_match and self.current_aux_create is not None:
                    number = int(csoffset_match.group(1))
                    self.template_start_position_dict[self.current_aux_create] = number + self.my_signal_start  # 记录起始位置
                    # 记录函数名
                    #print(self.template_start_position_dict)
            elif '_create(csoffset,aux_cmp_num,ctx,new_cmp_name,myId)' in line:
                function_match = re.search(r'(\w+)_create', line)
                if function_match and self.current_aux_create is not None:
                    function_name = function_match.group(1)
                    self.template_name_dict[function_name] = self.current_aux_create
                    self.template_name_signalStart[function_name] = self.template_start_position_dict[
                        self.template_name_dict[function_name]]
                    self.template_name_componentMemory[function_name] = self.ctx_index_stack[-1]
                    if self.ctx_index_stack:
                        self.ctx_index_stack.pop()
                    self.current_aux_create = None
                    #print(self.template_name_dict)
                    #print("self.mySubcomponents", self.mySubcomponents)
                    #print("self.function_name_signalStart:", self.template_name_signalStart)
                    #print("self.function_name_componentMemory", self.template_name_componentMemory)

                    if function_name in self.template_name_direct and self.template_name_direct[function_name]:
                        self.go_subtemplate_line.append(i)
                        self.is_running_subtemplate = True
                        i = self.template_line_dict[function_name] + 1  # 跳转到记录的行号解析子函数
                        self.my_signal_start = self.template_start_position_dict[
                            self.template_name_dict[function_name]]  # is it ok/
                        continue

            # 运行子函数
            elif '_run(mySubcomponents[cmp_index_ref],ctx)' in line:
                # 提取函数名并记录当前位置
                function_match = re.search(r'(\w+)_run', line)
                if function_match:
                    function_name = function_match.group(1)
                    for k, v in self.template_name_componentMemory.items():
                        if k == function_name:
                            if self.have_append_ctx_index[self.template_name_componentMemory[k]]:
                                self.have_append_ctx_index[self.template_name_componentMemory[k]] = False
                                self.ctx_index_stack.append(v)
                                break
                            else:
                                self.ctx_index_stack.append(v)
                                break
                    if function_name in self.template_line_dict:
                        self.go_subtemplate_line.append(i)
                        self.is_running_subtemplate = True
                        i = self.template_line_dict[function_name] + 1  # 跳转到记录的行号解析子函数
                        self.my_signal_start = self.template_name_signalStart[function_name]  # is it ok/
                        continue
                    # 解析子函数
            elif line.count(',') == 4:
                # 如果包含四个逗号，则开始遍历 function_line_dict
                for function_name, jump_line_number in self.function_line_dict.items():
                    if function_name in line:
                        # 提取 lvarcall、lvar[1] 和 1
                        match = re.match(rf'{function_name}\(ctx,(\w+),myId,&(\w+\[\d+\]),(\d+)\)', line)
                        if match:
                            # 存储提取的值
                            self.function_replace_name[function_name] = match.group(1)
                            self.function_destination[function_name] = match.group(2)
                            self.function_destination_size[function_name] = int(match.group(3))
                            self.is_running_subfunction = True
                            self.go_subfunction_line.append(i)

                            # 跳转到记录的行号
                            i = self.function_line_dict[function_name] + 1
                            self.which_subfunction = function_name
                            continue

            # elif line.startswith('assert('):
            #     if self.value_to_subfunction is not None:
            #         self.value_to_subfunction = None
            elif 'if(Fr_isTrue(&expaux[0])){' in line:
                self.if_start_line = i
                expaux_index = line.split('expaux[')[1].split(']')[0].strip()
                expaux_key = f'expaux[{expaux_index}]'
                self.if_key = expaux_key

                if self.expaux_type[expaux_key]:
                    self.if_else_type = 2
                    temp = i
                    temp2 = i
                    has_else = False
                    if_number = 1
                    kuohao_number = 1  # 进入 else 块，初始化括号计数器
                    while temp2 < len(lines) and not kuohao_number == 0:
                        temp2 += 1  # 跳到 else 块的下一个部分
                        if 'if(Fr_isTrue(&expaux[0])){' in lines[temp2]:
                            if_number += 1
                        if '{' in lines[temp2]:
                            kuohao_number += 1
                        if '}' in lines[temp2]:
                            kuohao_number -= 1
                        if "else" in lines[temp2] and if_number == 1:
                            kuohao_number -= 1
                        if "else" in lines[temp2] and if_number > 1:
                            if_number -= 1
                        if "else" in lines[temp2] and kuohao_number == 0:
                            has_else = True
                    if not has_else:
                        self.else_start_line = temp2
                        self.else_end_line = temp2
                    else:
                        # while temp < len(lines) and not lines[temp].strip().startswith('}else{'):
                        #     temp += 1
                        temp = temp2
                        self.else_start_line = temp2  # 记录 else 的开始行号
                        kuohao_number = 1  # 进入 else 块，初始化括号计数器
                        while temp < len(lines) and not kuohao_number == 0:
                            temp += 1  # 跳到 else 块的下一个部分
                            if '{' in lines[temp]:
                                kuohao_number += 1
                            if '}' in lines[temp]:
                                kuohao_number -= 1
                            # 当括号计数器为 0 时，说明 else 块结束
                        self.else_end_line = temp
                else:
                    self.if_else_type = 1
                    if expaux_key in self.int_dict:
                        expaux_value = self.int_dict[expaux_key]
                        if expaux_value == 1:
                            temp = i
                            temp2 = i
                            has_else = False
                            kuohao_number = 1  # 进入 else 块，初始化括号计数器
                            if_number = 1
                            while temp2 < len(lines) and not kuohao_number == 0:
                                temp2 += 1  # 跳到 else 块的下一个部分
                                if 'if(Fr_isTrue(&expaux[0])){' in lines[temp2]:
                                    if_number += 1
                                if '{' in lines[temp2]:
                                    kuohao_number += 1
                                if '}' in lines[temp2]:
                                    kuohao_number -= 1
                                if "else" in lines[temp2] and if_number == 1:
                                    kuohao_number -= 1
                                if "else" in lines[temp2] and if_number > 1:
                                    if_number -= 1
                                if "else" in lines[temp2] and kuohao_number == 0:
                                    has_else = True
                            if not has_else:
                                self.else_start_line = temp2
                                self.else_end_line = temp2
                            else:
                                # while temp < len(lines) and not lines[temp].strip().startswith('}else{'):
                                #     temp += 1
                                # self.else_start_line = temp  # 记录 else 的开始行号
                                temp = temp2
                                self.else_start_line = temp2
                                kuohao_number = 1  # 进入 else 块，初始化括号计数器
                                while temp < len(lines) and not kuohao_number == 0:
                                    temp += 1  # 跳到 else 块的下一个部分
                                    if '{' in lines[temp]:
                                        kuohao_number += 1
                                    if '}' in lines[temp]:
                                        kuohao_number -= 1
                                    # 当括号计数器为 0 时，说明 else 块结束
                                self.else_end_line = temp
                        else:
                            temp2 = i
                            has_else = False
                            kuohao_number = 1  # 进入 else 块，初始化括号计数器
                            if_number = 1
                            while temp2 < len(lines) and not kuohao_number == 0:
                                temp2 += 1  # 跳到 else 块的下一个部分
                                if 'if(Fr_isTrue(&expaux[0])){' in lines[temp2]:
                                    if_number += 1
                                if '{' in lines[temp2]:
                                    kuohao_number += 1
                                if '}' in lines[temp2]:
                                    kuohao_number -= 1
                                if "else" in lines[temp2] and if_number == 1:
                                    kuohao_number -= 1
                                if "else" in lines[temp2] and if_number > 1:
                                    if_number -= 1
                                if "else" in lines[temp2] and kuohao_number == 0:
                                    has_else = True
                            i = temp2
                            i += 1
                            # if not has_else:
                            #     i = temp2
                            #     i += 1
                            # else:
                            #     # 搜索到 else 部分，找到 }else{ 行
                            #     # while i < len(lines) and not lines[i].strip().startswith('}else{'):
                            #     #     i += 1
                            #     i = temp2
                            #     i += 1
                            #################maybe false######################
                            # 找到 }else{，标记跳过结束并开始执行 else 块
                            continue
                    else:
                        raise ValueError(f"Key {expaux_key} not found in int_dict")

            elif 'while(Fr_isTrue(&expaux[0]))' in line:
                temp = copy.deepcopy(self.int_dict)
                loop_condition_lines, while_loop_code, update_code, loop_start, loop_end = self.dealWhile(i, lines)

                loop_num = self.calculate_loop_iterations(loop_condition_lines, while_loop_code)

                self.origin_lines.append(lines)
                lines = self.update_lines(lines, loop_start, loop_end, update_code, loop_num)
                self.int_dict = temp
                #print(len(lines))
                # number_test = 0
                # for j in range(1, len(lines) - 2):
                #     if 'PFrElement aux_dest = &lvar[93]' in lines[
                #         j] and 'Fr_add(&expaux[0],&lvar[93],&circuitConstants[2]); // line circom 126' in \
                #             lines[j + 2]:
                #         number_test += 1
                # print(number_test)
                i = loop_start - 2  # 重新设置 i 到更新后的部分的起始位置

            elif line.startswith('PFrElement aux_dest'):
                dest_var = self.extract_index(line.split('&', 1)[1], self.my_signal_start)
                # aux_dest = FrElement.construct_value(dest_var)
                aux_dest = self.element_dict[dest_var]
                self.dest_var = dest_var
                #print(self.dest_var)
                if (re.search(r'PFrElement aux_dest = &lvar\[\d+\]', line) or re.search(
                        r'PFrElement aux_dest = &lvarcall\[\d+\]', line)) and (
                        self.use_if_terms or self.use_else_terms):
                    self.operate_lvar = True
                    if "lvarcall" in line:
                        lvar_match = re.search(r'(lvarcall\[\d+\])', line)
                    else:
                        lvar_match = re.search(r'(lvar\[\d+\])', line)
                    if lvar_match:
                        lvar_key = lvar_match.group(1)  # 获取到 lvar[数字] 的键
                        # 如果 lvar_iterate 中没有该键，初始化为 0；如果有，增加其值
                        if lvar_key not in self.lvar_iterate and self.use_if_terms:
                            self.lvar_iterate[lvar_key] = 0
                        elif self.use_if_terms:
                            self.lvar_iterate[lvar_key] += 1
                        dest_var = self.extract_index(f"{lvar_key}_{self.lvar_iterate[lvar_key]}", self.my_signal_start)
                        # aux_dest = FrElement.construct_value(dest_var)
                        aux_dest = self.element_dict[dest_var]
                        self.dest_var = dest_var
                        #print(self.dest_var)
                    # if re.search(r'PFrElement aux_dest = &lvar\[\d+\]', line):
                    #     dest_var = re.findall(r'&lvar\[\d+\]', line)[0]
                    # elif re.search(r'PFrElement aux_dest = &lvarcall\[\d+\]', line):
                    #     dest_var = re.findall(r'&lvarcall\[\d+\]', line)[0]
                    # dest_key = dest_var[1:]
                    # temp = i + 1
                    # while temp < len(lines):
                    #     line = lines[temp].strip().rstrip(';')
                    #     if re.match(r'Fr_(add|mul|sub|div)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                    #                 line) and 'mySignalStart' not in line:
                    #         self.evaluate_expression(line)
                    #         temp = temp + 1
                    #     elif re.match(
                    #             r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                    #             line) and 'mySignalStart' not in line:
                    #         self.bit_fr_operation(line)
                    #         temp = temp + 1
                    #     elif re.match(r'Fr_bnot\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                    #                   line) and 'mySignalStart' not in line:
                    #         self.bit_fr_operation(line)
                    #         temp = temp + 1
                    #     elif re.match(r'Fr_copy\(aux_dest,\&(expaux\[\d+\]|circuitConstants\[\d+\])\)', line):
                    #         src_var = re.findall(r'(&expaux\[\d+\]|&circuitConstants\[\d+\])', line)[0]
                    #         self.int_dict[dest_key] = self.int_dict.get(src_var[1:], 0)
                    #         # if 'lvar[93]' in self.int_dict:
                    #         #     if self.int_dict[
                    #         #         'lvar[93]'] == 92:
                    #         #         print(line)
                    #         #         print(i)
                    #         #i = temp + 1 # 修改 var smt
                    #         break
                    #     else:
                    #         temp = temp + 1
                # else:
                #     self.operate_lvar = False
            elif '}' in line:
                self.operate_lvar = False
            elif 'Fr_add' in line or 'Fr_mul' in line or 'Fr_div' in line or 'Fr_sub' in line or 'Fr_eq' in line or 'Fr_neq' in line \
                    or 'Fr_gt' in line or 'Fr_lt' in line or 'Fr_geq' in line or 'Fr_leq' in line or 'Fr_mod' in line or 'Fr_idiv' in line or 'Fr_pow' in line:
                parts = line.split(',')
                dest_var = None
                dest_part = parts[0].split('(')[1]
                src1_part = parts[1]
                src2_part = parts[2].rsplit(')', 1)[0]

                if 'aux_dest' in dest_part:
                    dest_element = aux_dest
                else:
                    if 'expaux' in dest_part:
                        self.new_expaux = True
                    dest_var = self.extract_index(dest_part, self.my_signal_start)
                    dest_element = self.element_dict[dest_var]
                if 'expaux' in dest_part:
                    if 'mySignalStart' in line:
                        self.expaux_type[dest_var] = True
                    elif 'expaux' in src1_part or 'expaux' in src2_part:
                        if ('expaux' in src1_part and self.expaux_type[src1_part.split('&')[1]]) or ('expaux' in src2_part and self.expaux_type[src2_part.split('&')[1]]):
                            self.expaux_type[dest_var] = True
                        else:
                            self.expaux_type[dest_var] = False
                    else:
                        self.expaux_type[dest_var] = False

                src1_var = self.extract_index(src1_part, self.my_signal_start)
                src2_var = self.extract_index(src2_part, self.my_signal_start)
                if src1_var in self.lvar_iterate:
                    src1_element = self.element_dict[f"{src1_var}_{self.lvar_iterate[src1_var]}"]
                else:
                    src1_element = self.element_dict[src1_var]
                if src2_var in self.lvar_iterate:
                    src2_element = self.element_dict[f"{src2_var}_{self.lvar_iterate[src2_var]}"]
                else:
                    src2_element = self.element_dict[src2_var]

                if 'Fr_add' in line:
                    self.append_term(self.Fr_add(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(add|mul|sub|div)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                    #print(self.Fr_add(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_mul' in line:
                    self.append_term(self.Fr_mul(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(add|mul|sub|div)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                    #print(self.Fr_mul(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_div' in line:
                    self.append_term(self.Fr_div(dest_element, src1_element, src2_element))
                    # if re.match(r'Fr_(add|mul|sub|div)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)', line) and 'mySignalStart' not in line:
                    #     self.evaluate_expression(line)
                    #print(self.Fr_div(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_mod' in line:
                    self.append_term(self.Fr_mod(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(mod|idiv|pow)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                    #print(self.Fr_mod(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_idiv' in line:
                    self.append_term(self.Fr_idiv(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(mod|idiv|pow)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                    #print(self.Fr_idiv(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_pow' in line:
                    self.append_term(self.Fr_pow(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(mod|idiv|pow)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                    #print(self.Fr_pow(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_sub' in line:
                    self.append_term(self.Fr_sub(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(add|mul|sub|div)\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                elif 'Fr_eq' in line:  # isTrue Function
                    self.append_term(self.Fr_eq(dest_element, src1_element, src2_element))
                    self.append_term(self.Fr_isTrue(dest_element))
                    if re.match(r'Fr_eq\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                elif 'Fr_neq' in line:
                    self.append_term(self.Fr_neq(dest_element, src1_element, src2_element))
                    self.append_term(self.Fr_isTrue(dest_element))
                    if re.match(r'Fr_neq\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                elif 'Fr_gt' in line:
                    self.append_term(self.Fr_gt(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_gt\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                elif 'Fr_lt' in line:
                    self.append_term(self.Fr_lt(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_lt\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                elif 'Fr_geq' in line:
                    self.append_term(self.Fr_geq(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_geq\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)
                elif 'Fr_leq' in line:
                    self.append_term(self.Fr_leq(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_leq\(&expaux\[(\d+)\],&\w+\[[^]]+\],&\w+\[[^]]+\]\)',
                                line) and 'mySignalStart' not in line:
                        self.evaluate_expression_three(line)

            elif 'Fr_copyn' in line:
                parts = line.split(',')
                dest_part = parts[0].split('(')[1].strip()
                src_part = parts[1].strip()
                num_elements = int(parts[2].split(')')[0].strip())  # 获取复制元素的数量

                if 'aux_dest' in dest_part:
                    print(line)
                else:
                    if 'expaux' in dest_part:
                        self.new_expaux = True
                    self.dest_var = self.extract_index(dest_part, self.my_signal_start)

                # 获取初始 dest_element 和 src_element
                src_var = self.extract_index(src_part, self.my_signal_start)

                # 分离 dest_var 和 src_var 的名称与索引
                if '.' in self.dest_var:
                    dest_name, dest_index = re.match(r'([\w\.]+)\[(\d+)\]', self.dest_var).groups()
                else:
                    dest_name, dest_index = re.match(r'(\w+)\[(\d+)\]', self.dest_var).groups()
                if '.' in src_var:
                    src_name, src_index = re.match('([\w\.]+)\[(\d+)\]', src_var).groups()
                else:
                    src_name, src_index = re.match(r'(\w+)\[(\d+)\]', src_var).groups()
                # src_name, src_index = re.match(r'(\w+)\[(\d+)\]', src_var).groups()

                # 转换索引为整数
                dest_index = int(dest_index)
                src_index = int(src_index)

                # 复制指定数量的元素
                for index in range(num_elements):
                    # 动态构造当前的目标和源
                    if f"{dest_name}[{dest_index + index}]" not in self.element_dict:
                        self.element_dict[f"{dest_name}[{dest_index + index}]"] = FrElementModel.construct_value(
                            f"{dest_name}[{dest_index + index}]")
                    current_dest_element = self.element_dict[f"{dest_name}[{dest_index + index}]"]
                    if f"{src_name}[{src_index + index}]" not in self.element_dict:
                        self.element_dict[f"{src_name}[{src_index + index}]"] = FrElementModel.construct_value(
                            f"{src_name}[{src_index + index}]")
                    current_src_element = self.element_dict[f"{src_name}[{src_index + index}]"]

                    # 执行复制操作
                    self.append_term(self.Fr_Copy(current_dest_element, current_src_element))
                    #print(f"Copied {current_dest_element} from {current_src_element}")

            elif 'Fr_copy' in line or 'Fr_square' in line or 'Fr_inv' in line or 'Fr_bnot' in line or 'Fr_lnot' in line or 'Fr_neg' in line:
                # print(line)
                dest_var = None
                parts = line.split(',')
                dest_part = parts[0].split('(')[1]
                src_part = parts[1].rsplit(')', 1)[0]

                if 'aux_dest' in dest_part:
                    dest_element = aux_dest
                else:
                    if 'expaux' in dest_part:
                        self.new_expaux = True
                    dest_var = self.extract_index(dest_part, self.my_signal_start)
                    dest_element = self.element_dict[dest_var]

                if 'expaux' in dest_part:
                    if 'mySignalStart' in line:
                        self.expaux_type[dest_var] = True
                    elif 'expaux' in src1_part or 'expaux' in src2_part:
                        if ('expaux' in src1_part and self.expaux_type[src1_part.split('&')[1]]) or ('expaux' in src2_part and self.expaux_type[src2_part.split('&')[1]]):
                            self.expaux_type[dest_var] = True
                        else:
                            self.expaux_type[dest_var] = False
                    else:
                        self.expaux_type[dest_var] = False

                src_var = self.extract_index(src_part, self.my_signal_start)
                if src_var in self.lvar_iterate:
                    src_element = self.element_dict[f"{src_var}_{self.lvar_iterate[src_var]}"]
                else:
                    src_element = self.element_dict[src_var]

                if 'Fr_copy' in line:
                    self.append_term(self.Fr_Copy(dest_element, src_element))
                    #print(self.Fr_Copy(dest_element, src_element))
                    #print('\n')
                    self.int_dict[self.dest_var] = self.int_dict.get(src_var[1:], 0)
                elif 'Fr_square' in line:
                    self.append_term(self.Fr_Square(dest_element, src_element))
                    if re.match(r'Fr_square\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print('\n')
                elif 'Fr_neg' in line:
                    self.append_term(self.Fr_neg(dest_element, src_element))
                    if re.match(r'Fr_neg\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print('\n')
                elif 'Fr_inv' in line:
                    self.append_term(self.Fr_inv(dest_element, src_element))
                elif 'Fr_bnot' in line:
                    self.append_term(self.Fr_bnot(dest_element, src_element))
                    if re.match(r'Fr_bnot\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_bnot(dest_element, src_element))
                    #print('\n')
                elif 'Fr_lnot' in line:
                    self.append_term(self.Fr_lnot(dest_element, src_element))
                    if re.match(r'Fr_lnot\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_lnot(dest_element, src_element))
                    #print('\n')

            elif 'Fr_shr' in line or 'Fr_band' in line or 'Fr_shl' in line or 'Fr_bor' in line or 'Fr_bxor' in line or 'Fr_lor' in line or 'Fr_land' in line:
                parts = line.split(',')
                dest_var = None
                dest_part = parts[0].split('(')[1]
                src1_part = parts[1]
                src2_part = parts[2].rsplit(')', 1)[0]

                if 'aux_dest' in dest_part:
                    dest_element = aux_dest
                else:
                    if 'expaux' in dest_part:
                        self.new_expaux = True
                    dest_var = self.extract_index(dest_part, self.my_signal_start)
                    dest_element = self.element_dict[dest_var]

                if 'expaux' in dest_part:
                    if 'mySignalStart' in line:
                        self.expaux_type[dest_var] = True
                    elif 'expaux' in src1_part or 'expaux' in src2_part:
                        if ('expaux' in src1_part and self.expaux_type[src1_part.split('&')[1]]) or ('expaux' in src2_part and self.expaux_type[src2_part.split('&')[1]]):
                            self.expaux_type[dest_var] = True
                        else:
                            self.expaux_type[dest_var] = False
                    else:
                        self.expaux_type[dest_var] = False

                src1_var = self.extract_index(src1_part, self.my_signal_start)
                src2_var = self.extract_index(src2_part, self.my_signal_start)
                if src1_var in self.lvar_iterate:
                    src1_element = self.element_dict[f"{src1_var}_{self.lvar_iterate[src1_var]}"]
                else:
                    src1_element = self.element_dict[src1_var]
                if src2_var in self.lvar_iterate:
                    src2_element = self.element_dict[f"{src2_var}_{self.lvar_iterate[src2_var]}"]
                else:
                    src2_element = self.element_dict[src2_var]

                if 'Fr_shr' in line:
                    self.append_term(self.Fr_shr(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_shr(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_shl' in line:
                    self.append_term(self.Fr_shl(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_shl(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_band' in line:
                    self.append_term(self.Fr_band(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_band(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_bor' in line:
                    self.append_term(self.Fr_bor(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_bor(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_bxor' in line:
                    self.append_term(self.Fr_bxor(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_bxor(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_lor' in line:
                    self.append_term(self.Fr_lor(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(lor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_lor(dest_element, src1_element, src2_element))
                    #print('\n')
                elif 'Fr_land' in line:
                    self.append_term(self.Fr_land(dest_element, src1_element, src2_element))
                    if re.match(r'Fr_(land)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
                                line) and 'mySignalStart' not in line:
                        # #print(line)
                        self.evaluate_expression_extend(line)
                    #print(self.Fr_land(dest_element, src1_element, src2_element))
                    #print('\n')

            # elif re.match(r'Fr_(shr|shl|band|bor|bxor)\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)',
            #               line) and 'mySignalStart' not in line:
            #     print(line)
            #     self.bit_fr_operation(line)
            # elif re.match(r'Fr_bnot\(&(\w+)\[([^]]+)\],&(\w+)\[([^]]+)\]\)', line) and 'mySignalStart' not in line:
            #     print(line)
            #     self.bit_fr_operation(line)

            i += 1


if __name__ == '__main__':
    exp_slv = ExpandedCVC5('bn128')
    test = FrFunction(exp_slv=exp_slv)
    symFile_path = 'Add.sym'
    codeblock = 'Add.txt'
    # datFile_path = 'Add.dat'
    # test.deal_dat(dat_path=datFile_path, num=0)
    print(test.constants_dict)
    print(test.int_dict)
    test.directory_2_smt(symFile_path=symFile_path, code_block_file_path=codeblock, componentNum=1)
    print(test.directory_terms)
    print(test.signal_map)
    print(test.element_dict)

# if __name__ == '__main__':
#     exp_slv = ExpandedCVC5('bn128')
#     test = FrFunction(exp_slv=exp_slv)
#     symFile_path = '../temp_file/simple1/simple1.sym'
#     codeblock = '../temp_file/simple1/simple1_cpp/simple1.cpp'
#     dat_path = '../temp_file/simple1/simple1_cpp/simple1.dat'
#     test.deal_dat(dat_path, 0)
#     test.directory_2_smt(symFile_path=symFile_path, code_block_file_path=codeblock, componentNum=1)
#
#     # 自动构造的约束条件
#     auto_made = exp_slv.associativeForm(test.directory_terms)
#
#     # 手动构造的约束条件
#     element_a = test.element_dict['main.a']
#     element_b = test.element_dict['main.b']
#     smt_list = list()
#     smt_list.append(element_a.is_l)
#     smt_list.append(element_a.is_m)
#     smt_list.append(element_a.s_v)
#     smt_list.append(element_a.l_v)
#     smt_list.append(element_b.is_l)
#     smt_list.append(element_b.is_m)
#     smt_list.append(element_b.s_v)
#     smt_list.append(element_b.l_v)
#     hand_made = exp_slv.mkTerm(Kind.AND,
#                                exp_slv.mkTerm(Kind.EQUAL, element_b.s_v, element_a.s_v),
#                                exp_slv.mkTerm(Kind.EQUAL, element_b.l_v, element_a.l_v),
#                                exp_slv.mkTerm(Kind.EQUAL, element_b.is_l, element_a.is_l),
#                                exp_slv.mkTerm(Kind.EQUAL, element_b.is_m, element_a.is_m)
#                                )
#
#     # 目标性质
#     s_eq = exp_slv.mkTerm(Kind.EQUAL, element_a.s_v, element_b.s_v)
#     print(s_eq)
#
#     # 手工构造的情况
#     colorPrint(f'============ 手工构造的情况 ============', COLOR.GREEN)
#     hand_exp = exp_slv.mkTerm(Kind.AND, hand_made, exp_slv.mkTerm(Kind.NOT, s_eq))
#     print(hand_exp)
#     outcome = exp_slv.check_satisfy(hand_exp, smt_list)
#     print(f'是否可解: {outcome}')
#
#     # 自动构造的情况
#     colorPrint(f'============ 自动生成的情况 ============', COLOR.GREEN)
#     auto_exp = exp_slv.mkTerm(Kind.AND, auto_made, exp_slv.mkTerm(Kind.NOT, s_eq))
#     print(auto_exp)
#     outcome = exp_slv.check_satisfy(auto_exp, smt_list)
#     print(f'是否可解: {outcome}')
