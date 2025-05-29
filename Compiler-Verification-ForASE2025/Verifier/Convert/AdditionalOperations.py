import cvc5
from cvc5 import Kind

from Tools.Check import TypeCheck
from Tools.ColorPrint import colorPrint, COLOR


class ExpandedCVC5:
    prime_dic = {'bn128': 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001,
                 'bls12381': 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001,
                 'goldilocks': 0xffffffff00000001,
                 'grumpkin': 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47,
                 'secq256r1': 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
                 'pallas': 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001,
                 'vesta': 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001}

    R_dic = {'bn128': 0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb}

    def __init__(self, prime_name):
        TypeCheck(str, prime_name)
        prime = ExpandedCVC5.prime_dic[prime_name]
        self.__prime_name = prime_name
        self.__prime = prime
        self.__slv = cvc5.Solver()
        self.__slv.setLogic('ALL')
        self.__slv.setOption('produce-models', 'true')
        self.__slv.setOption('mbqi', 'true')
        self.__F = self.__slv.mkFiniteFieldSort(prime)
        self.__R = self.FF_number(ExpandedCVC5.R_dic[prime_name])
        self.__B = self.__slv.getBooleanSort()
        self.__FF_zero = self.FF_number(0)
        self.__FF_one = self.FF_number(1)

        self.__FF2F_binary_operations = self.__slv.mkFunctionSort([self.__F, self.__F], self.__F)
        self.__F2F_unary_bit_operations = self.__slv.mkFunctionSort([self.__F], self.__F)
        self.__FF2B_Compare = self.__slv.mkFunctionSort([self.__F, self.__F], self.__B)  # 比较元素

        self.__assert_property = False

        self.init_comparator()
        self.init_bit_operations()
        self.init_other_operations()

    def print(self):
        print(self.__slv)
    def init_comparator(self):
        # 比较运算符的实现
        self.__FFF_Gt = self.__slv.mkConst(self.__FF2B_Compare, 'FFF_Gt')


        # 添加比较的性质
        a = self.__slv.mkVar(self.__F, "a")
        b = self.__slv.mkVar(self.__F, "b")
        c = self.__slv.mkVar(self.__F, "c")

        # 不等性
        eq = self.__slv.mkTerm(Kind.EQUAL, a, b)
        not_eq = self.__slv.mkTerm(Kind.NOT, eq)
        gt = self.__slv.mkTerm(Kind.APPLY_UF, self.__FFF_Gt, a, b)
        not_gt = self.__slv.mkTerm(Kind.NOT, gt)
        property = self.__slv.mkTerm(Kind.AND,
                                     self.__slv.mkTerm(Kind.IMPLIES, eq, not_gt),
                                     self.__slv.mkTerm(Kind.IMPLIES, gt, not_eq))
        property_exp = self.mkTerm(Kind.FORALL, self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b), property)
        self.__slv.assertFormula(property_exp)

        # 传递性
        imply = self.__slv.mkTerm(Kind.IMPLIES,
                                  self.__slv.mkTerm(Kind.AND,
                                                    self.__slv.mkTerm(Kind.APPLY_UF, self.__FFF_Gt, a, b),
                                                    self.__slv.mkTerm(Kind.APPLY_UF, self.__FFF_Gt, b, c)),
                                  self.__slv.mkTerm(Kind.APPLY_UF, self.__FFF_Gt, a, c))

        transitivity = self.__slv.mkTerm(Kind.FORALL, self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b, c), imply)

        if self.__assert_property:
            self.__slv.assertFormula(transitivity)

    def init_bit_operations(self):
        self.__right_shift = self.__slv.mkConst(self.__FF2F_binary_operations, 'FFF_RST')    # 右移
        self.__left_shift = self.__slv.mkConst(self.__FF2F_binary_operations, 'FFF_LST')     # 左移
        self.__bit_and = self.__slv.mkConst(self.__FF2F_binary_operations, 'FFF_BIT_AND')    # 按位与
        self.__bit_or = self.__slv.mkConst(self.__FF2F_binary_operations, 'FFF_BIT_OR')      # 按位或
        self.__bit_xor = self.__slv.mkConst(self.__FF2F_binary_operations, 'FFF_BIT_XOR')    # 按位异或

        self.__bit_not = self.__slv.mkConst(self.__F2F_unary_bit_operations, 'FFF_BIT_NOT')     # 按位取反
        self.__bit_complement = self.__slv.mkConst(self.__F2F_unary_bit_operations, 'FFF_BIT_COMPLEMENT')  # 取补码

        # ************************************************
        # *******************与操作的性质*******************
        # ************************************************
        if self.__assert_property:
            self.init_right_shift()
            self.init_left_shift()
            self.init_bit_and()
            self.init_bit_or()
            self.init_bit_xor()
            self.init_bit_not()
            self.init_bit_complement()

    def init_right_shift(self):
        a = self.__slv.mkVar(self.__F, "a")
        b = self.__slv.mkVar(self.__F, "b")
        c = self.__slv.mkVar(self.__F, "c")
        # 结合性 a >> b >> c == a >> b + c
        right_shift_P1 = self.__slv.mkTerm(Kind.FORALL,
                                           self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b, c),
                                           self.__slv.mkTerm(Kind.EQUAL,
                                                             self.__slv.mkTerm(Kind.APPLY_UF,
                                                                               self.__right_shift,
                                                                               self.__slv.mkTerm(Kind.APPLY_UF,
                                                                                                 self.__right_shift, a,
                                                                                                 b),
                                                                               c),
                                                             self.__slv.mkTerm(Kind.APPLY_UF,
                                                                               self.__right_shift,
                                                                               a,
                                                                               self.__slv.mkTerm(Kind.FINITE_FIELD_ADD,
                                                                                                 b, c)
                                                                               )
                                                             )
                                           )

        # 移动零位还是自己
        right_shift_P2 = self.__slv.mkTerm(Kind.FORALL,
                                           self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                           self.__slv.mkTerm(Kind.EQUAL,
                                                             self.__slv.mkTerm(Kind.APPLY_UF, self.__right_shift, a,
                                                                               self.__FF_zero),
                                                             a)
                                           )

        self.__slv.assertFormula(right_shift_P1)
        self.__slv.assertFormula(right_shift_P2)

    def init_left_shift(self):
        a = self.__slv.mkVar(self.__F, "a")
        b = self.__slv.mkVar(self.__F, "b")
        c = self.__slv.mkVar(self.__F, "c")
        # 结合性 a << b << c == a << b + c
        left_shift_P1 = self.__slv.mkTerm(Kind.FORALL,
                                          self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b, c),
                                          self.__slv.mkTerm(Kind.EQUAL,
                                                            self.__slv.mkTerm(Kind.APPLY_UF,
                                                                              self.__left_shift,
                                                                              self.__slv.mkTerm(Kind.APPLY_UF,
                                                                                                self.__left_shift, a,
                                                                                                b),
                                                                              c),
                                                            self.__slv.mkTerm(Kind.APPLY_UF,
                                                                              self.__left_shift,
                                                                              a,
                                                                              self.__slv.mkTerm(Kind.FINITE_FIELD_ADD,
                                                                                                b, c)
                                                                              )
                                                            )
                                          )

        # 移动零位还是自己
        left_shift_P2 = self.__slv.mkTerm(Kind.FORALL,
                                          self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                          self.__slv.mkTerm(Kind.EQUAL,
                                                            self.__slv.mkTerm(Kind.APPLY_UF, self.__left_shift, a,
                                                                              self.__FF_zero),
                                                            a)
                                          )

        self.__slv.assertFormula(left_shift_P1)
        self.__slv.assertFormula(left_shift_P2)

    def init_bit_and(self):
        a = self.__slv.mkVar(self.__F, "a")
        b = self.__slv.mkVar(self.__F, "b")
        # 交换律
        bit_and_P1 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b),
                                       self.__slv.mkTerm(Kind.EQUAL,
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_and, a, b),
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_and, b, a)
                                                         )
                                       )

        # 结合律 暂时用不到先留着吧

        # 和自己与 a and a = a
        bit_and_P3 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                       self.__slv.mkTerm(Kind.EQUAL,
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_and, a, a),
                                                         a)
                                       )

        # 和0与 a and 0 = 0
        bit_and_P4 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                       self.__slv.mkTerm(Kind.EQUAL,
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_and, a,
                                                                           self.__FF_zero),
                                                         self.__FF_zero)
                                       )

        # 和1与 a and 1 = 0 or 1
        bit_and_P5 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                       self.__slv.mkTerm(Kind.OR,
                                                         self.__slv.mkTerm(Kind.EQUAL,
                                                                           self.__slv.mkTerm(Kind.APPLY_UF,
                                                                                             self.__bit_and, a,
                                                                                             self.__FF_one),
                                                                           self.__FF_one),
                                                         self.__slv.mkTerm(Kind.EQUAL,
                                                                           self.__slv.mkTerm(Kind.APPLY_UF,
                                                                                             self.__bit_and, a,
                                                                                             self.__FF_one),
                                                                           self.__FF_zero)
                                                         )
                                       )

        self.__slv.assertFormula(bit_and_P1)
        self.__slv.assertFormula(bit_and_P3)
        self.__slv.assertFormula(bit_and_P4)
        self.__slv.assertFormula(bit_and_P5)

    def init_bit_or(self):
        a = self.__slv.mkVar(self.__F, "a")
        b = self.__slv.mkVar(self.__F, "b")
        # 交换律
        bit_or_P1 = self.__slv.mkTerm(Kind.FORALL,
                                      self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b),
                                      self.__slv.mkTerm(Kind.EQUAL,
                                                        self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_or, a, b),
                                                        self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_or, b, a)
                                                        )
                                      )

        # 结合律 暂时用不到先留着吧

        # 和自己与 a or a = a
        bit_or_P3 = self.__slv.mkTerm(Kind.FORALL,
                                      self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                      self.__slv.mkTerm(Kind.EQUAL,
                                                        self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_or, a, a),
                                                        a)
                                      )

        # 和0与 a or 0 = a
        bit_or_P4 = self.__slv.mkTerm(Kind.FORALL,
                                      self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                      self.__slv.mkTerm(Kind.EQUAL,
                                                        self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_or, a,
                                                                          self.__FF_zero),
                                                        a)
                                      )

        self.__slv.assertFormula(bit_or_P1)
        self.__slv.assertFormula(bit_or_P3)
        self.__slv.assertFormula(bit_or_P4)

    def init_bit_xor(self):
        a = self.__slv.mkVar(self.__F, "a")
        b = self.__slv.mkVar(self.__F, "b")
        # 交换律
        bit_xor_P1 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a, b),
                                       self.__slv.mkTerm(Kind.EQUAL,
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_xor, a, b),
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_xor, b, a)
                                                         )
                                       )

        # 结合律 暂时用不到先留着吧

        # 和自己与 a xor a = 0
        bit_xor_P3 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                       self.__slv.mkTerm(Kind.EQUAL,
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_xor, a, a),
                                                         self.__FF_zero)
                                       )

        # 和0与 a xor 0 = a
        bit_xor_P4 = self.__slv.mkTerm(Kind.FORALL,
                                       self.__slv.mkTerm(Kind.VARIABLE_LIST, a),
                                       self.__slv.mkTerm(Kind.EQUAL,
                                                         self.__slv.mkTerm(Kind.APPLY_UF, self.__bit_xor, a,
                                                                           self.__FF_zero),
                                                         a)
                                       )

        self.__slv.assertFormula(bit_xor_P1)
        self.__slv.assertFormula(bit_xor_P3)
        self.__slv.assertFormula(bit_xor_P4)

    def init_bit_not(self):
        # 按位取反暂时没有想到什么性质
        pass

    def init_bit_complement(self):
        pass

    def init_other_operations(self):
        self.__FF_pow = self.__slv.mkConst(self.__FF2F_binary_operations, 'FF_pow')
        self.__FF_mod = self.__slv.mkConst(self.__FF2F_binary_operations, 'FF_mod')
        self.__FF_int_div = self.__slv.mkConst(self.__FF2F_binary_operations, 'FF_int_div')

    def prime(self):
        return self.__prime

    def slv(self):
        return self.__slv

    def F(self):
        return self.__F

    def B(self):
        return self.__B

    def R(self):
        return self.__R

    def FF_number(self, num):  # num : int or String
        return self.__slv.mkFiniteFieldElem(num, self.__F)

    def FF_zero(self):
        return self.__FF_zero

    def FF_one(self):
        return self.__FF_one

    def Boolean_True(self):
        return self.__slv.mkTrue()

    def Boolean_False(self):
        return self.__slv.mkFalse()

    def FF_const(self, name):
        TypeCheck(str, name)
        return self.__slv.mkConst(self.__F, name)

    def Bool_const(self, name):
        TypeCheck(str, name)
        return self.__slv.mkConst(self.__B, name)

    def mkTerm(self, kind_or_op, *args):
        try:
            return self.__slv.mkTerm(kind_or_op, *args)
        except Exception as e:
            pass

    # 全都且在一起
    def associativeForm(self, terms):
        if len(terms) == 0:
            return self.Boolean_True()
        elif len(terms) == 1:
            return terms[0]
        else:
            return self.mkTerm(Kind.AND, *terms)

    def mkConst(self, Sort_sort, symbol=None):
        return self.__slv.mkConst(Sort_sort, symbol)

    def mkVar(self, Sort_sort, symbol=None):
        return self.__slv.mkVar(Sort_sort, symbol)

    def mkFiniteFieldElem(self, value, Sort_sort, int_base=10):
        return self.__slv.mkFiniteFieldElem(value, Sort_sort, int_base)

    def assertFormula(self, Term_term):
        self.__slv.assertFormula(Term_term)

    def push(self):
        self.__slv.push()

    def pop(self):
        self.__slv.pop()

    def checkSat(self):
        return self.__slv.checkSat()

    def getValue(self, term_or_list):
        return self.__slv.getValue(term_or_list)

    # raw: 被移位的数  shift_num: 右移位数
    def mkFFTerm_Right_Shift(self, raw, shift_num):
        return self.mkTerm(Kind.APPLY_UF, self.__right_shift, raw, shift_num)

    # raw: 被移位的数  shift_num: 右移位数
    def mkFFTerm_Left_Shift(self, raw, left_num):
        return self.mkTerm(Kind.APPLY_UF, self.__left_shift, raw, left_num)

    def mkFFTerm_Bit_And(self, a, b):
        return self.mkTerm(Kind.APPLY_UF, self.__bit_and, a, b)

    def mkFFTerm_Bit_Or(self, a, b):
        return self.mkTerm(Kind.APPLY_UF, self.__bit_or, a, b)

    def mkFFTerm_Bit_Xor(self, a, b):
        return self.mkTerm(Kind.APPLY_UF, self.__bit_xor, a, b)

    def mkFFTerm_Bit_Not(self, a):
        return self.mkTerm(Kind.APPLY_UF, self.__bit_not, a)

    def mkFFTerm_bit_Complement(self, a):
        return self.mkTerm(Kind.APPLY_UF, self.__bit_complement, a)

    def mkFFTerm_Pow(self, a, b):
        return self.mkTerm(Kind.APPLY_UF, self.__FF_pow, a, b)

    def mkFFTerm_Mod(self, a, b):
        return self.mkTerm(Kind.APPLY_UF, self.__FF_mod, a, b)

    def mkFFTerm_IntDiv(self, a, b):
        return self.mkTerm(Kind.APPLY_UF, self.__FF_int_div, a, b)

    def mkFFTerm_Eq(self, a, b):
        return self.mkTerm(Kind.EQUAL, a, b)

    def mkFFTerm_Neq(self, a, b):
        Eq = self.mkFFTerm_Eq(a, b)
        return self.mkTerm(Kind.NOT, Eq)

    def mkFFTerm_Gt(self, a, b):
        raw_gt = self.mkTerm(Kind.APPLY_UF, self.__FFF_Gt, a, b)
        return raw_gt

    def mkFFTerm_Ge(self, a, b):
        Gt = self.mkFFTerm_Gt(a, b)
        Eq = self.mkFFTerm_Eq(a, b)
        return self.mkTerm(Kind.OR, Gt, Eq)

    def mkFFTerm_Lt(self, a, b):
        Ge = self.mkFFTerm_Ge(a, b)
        return self.mkTerm(Kind.NOT, Ge)

    def mkFFTerm_Le(self, a, b):
        Gt = self.mkFFTerm_Gt(a, b)
        return self.mkTerm(Kind.NOT, Gt)

    def get_model(self, signals, show=False):
        outcome = list()
        if show:
            colorPrint('SAT', COLOR.GREEN)
            colorPrint(f'P is {self.__prime_name} values {self.__prime}')
        for signal in signals:
            value = self.getValue(signal.toSmt())
            item = f'{signal.id_name} == {value}'
            outcome.append(item)
            if show:
                item = item.replace(f'{self.__prime}', 'P')
                colorPrint(f'{item}')
        return outcome

    def get_model_smt(self, SMTs, show=False):
        outcome = list()
        if show:
            colorPrint('SAT', COLOR.GREEN)
            colorPrint(f'P is {self.__prime_name} values {self.__prime}')
        for smt in SMTs:
            value = self.getValue(smt)
            item = f'{smt} == {value}'
            outcome.append(item)
            if show:
                item = item.replace(f'{self.__prime}', 'P')
                colorPrint(f'{item}')
        return outcome

    # 考察两个式子的等价性
    def check_equality(self, exp_A, exp_B, signals=None):
        self.push()
        aim_property = self.mkTerm(Kind.AND,
                                   self.mkTerm(Kind.IMPLIES, exp_A, exp_B),
                                   self.mkTerm(Kind.IMPLIES, exp_B, exp_A))
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and signals != None:
            self.get_model(signals, True)
        self.pop()
        return outcome

    # A -> B
    def check_implies(self, exp_A, exp_B, signals=None):
        self.push()
        aim_property = self.mkTerm(Kind.IMPLIES, exp_A, exp_B)
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and signals != None:
            self.get_model(signals, True)
        self.pop()
        return outcome

    # 考察两个式子的等价性
    def check_equality_with_settings(self, exp_A, exp_B, settings, signals=None):
        self.push()
        aim_property = self.mkTerm(Kind.AND,
                                   self.mkTerm(Kind.IMPLIES, exp_A, exp_B),
                                   self.mkTerm(Kind.IMPLIES, exp_B, exp_A))
        for setting in settings:
            self.assertFormula(setting)
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and signals != None:
            self.get_model(signals, True)
        self.pop()
        return outcome

    def check_implies(self, pre, suf, SMTs=None):
        self.push()
        aim_property = self.mkTerm(Kind.IMPLIES, pre, suf)
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and SMTs is not None:
            self.get_model_smt(SMTs, True)
        self.pop()
        return outcome

    def check_implies_with_settings(self, pre, suf, settings, SMTs=None):
        self.push()
        aim_property = self.mkTerm(Kind.IMPLIES, pre, suf)
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        for setting in settings:
            self.assertFormula(setting)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and SMTs is not None:
            self.get_model_smt(SMTs, True)
        self.pop()
        return outcome

    def check_satisfy(self, exp, SMTs=None):
        self.push()
        self.assertFormula(exp)
        raw_outcome = self.checkSat()
        outcome = raw_outcome.isSat()
        if outcome and SMTs is not None:
            self.get_model_smt(SMTs, True)
        self.pop()
        return outcome

    def check_satisfy_with_settings(self, exp, settings, SMTs=None):
        self.push()
        for setting in settings:
            self.assertFormula(setting)
        self.assertFormula(exp)
        outcome = self.checkSat().isSat()
        if outcome and SMTs is not None:
            self.get_model_smt(SMTs, True)
        self.pop()
        return outcome

    def getAssertions(self):
        return self.__slv.getAssertions()

    def printAssertions(self):
        print(self.__slv.getAssertions())