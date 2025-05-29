from cvc5 import Kind

from Elements.Circuit.BuildinWords import CBW, OP, EPO, EIO
from Elements.Circuit.Function import Function
from Tools.Calculate import calculate_deterministic_infixOp, calculate_deterministic_prefixOp, arrangeNumber
from Tools.ColorPrint import colorPrint, COLOR
from Tools.Errors import MyItemError

class F_var:
    def __init__(self, name):
        self.name = name
        self.value = 0

    def type(self):
        return CBW.Var

    def __str__(self):
        return f'{self.name} = {self.value}'


class F_var_array:
    @staticmethod
    def generate_from_list(name, value_list, owner):
        var_list = list()
        var_array = F_var_array(name, None)
        owner.add_var(var_array, name)
        for i in range(len(value_list)):
            item = value_list[i]
            var_name = f'{name}[{i}]'
            if isinstance(item, list):
                var_list.append(F_var_array.generate_from_list(var_name, item, owner))
                var_array.child_type = CBW.VarArray
            else:
                var = F_var(var_name)
                var.value = item
                var_list.append(var)
                var_array.child_type = CBW.Var
                owner.add_var(var, var_name)
        var_array.var_list = var_list

    def __init__(self, name, structure):
        self.name = name
        if structure is None:
            self.child_type = None
            self.var_list = None
        elif len(structure) == 1:
            self.child_type = CBW.Var
            self.var_list = list()
            for i in range(structure[0]):
                var = F_var(f'{name}[{i}]')
                self.var_list.append(var)
        else:
            self.child_type = CBW.VarArray
            self.var_list = list()
            for i in range(structure[0]):
                child_Array = F_var_array(f'{name}[{i}]', structure[1:])
                self.var_list.append(child_Array)

    def get_all_var_dict(self):
        outcome = dict()
        outcome[self.name] = self
        if self.child_type == CBW.VarArray:
            for sub_array in self.var_list:
                outcome.update(sub_array.get_all_var_dict())
        elif self.child_type == CBW.Var:
            for var in self.var_list:
                outcome[var.name] = var
        return outcome

    def get_value_list(self):
        outcome = list()
        if self.child_type == CBW.Var:
            for var in self.var_list:
                outcome.append(var.value)
        elif self.child_type == CBW.VarArray:
            for subArray in self.var_list:
                outcome.append(subArray.get_value_list())
        return outcome

    def type(self):
        return CBW.VarArray

    def set_values(self, value_list):
        if self.child_type == CBW.Var:
            for i in range(len(value_list)):
                self.var_list[i].value = value_list[i]
        elif self.child_type == CBW.VarArray:
            for i in range(len(value_list)):
                self.var_list[i].set_values(value_list[i])

    def __str__(self):
        return self.name


class FunctionCall:
    def __init__(self, func_name, args_values, exp_slv, circuit_terms):
        # 在Function中的var都是临时的var，在本地维护即可，
        # 而不是与component中的var一起维护
        self.__func_name = func_name
        self.__variable_dic = dict()
        self.__exp_slv = exp_slv
        self.__prime = exp_slv.prime()
        self.__ret_value = 0
        self.circuit_terms = circuit_terms
        func = Function.get_Function(func_name)
        func_args = func.get_args()
        func_block = func.get_block()
        self.deal_args(func_args, args_values)
        self.deal_block(func_block)

    def deal_args(self, args, args_values):
        for i in range(len(args)):
            name = args[i]
            var = F_var(name)
            value = args_values[i]
            if isinstance(value, list):
                F_var_array.generate_from_list(name, value, self)
            else:
                var.value = args_values[i]
                self.__variable_dic[name] = var

    def add_var(self, var, name):
        self.__variable_dic[name] = var

    def deal_block(self, stmt):
        func_stmts = stmt[CBW.stmts.value]
        for sub_stmt in func_stmts:
            ended = self.deal_sub_field(sub_stmt)
            if ended:
                return True
        return False
    def deal_sub_field(self, sub_stmt):
        for subfield, value in sub_stmt.items():
            if subfield == CBW.InitializationBlock.value:
                return self.deal_initialization(value)
            elif subfield == CBW.Substitution.value:
                return self.deal_substitution(value)
            elif subfield == CBW.Block.value:
                return self.deal_block(value)
            elif subfield == CBW.While.value:
                return self.deal_while(value)
            elif subfield == CBW.IfThenElse.value:
                return self.deal_ifThenElse(value)
            elif subfield == CBW.Return.value:
                return self.deal_return(value)
            else:
                print('unsolved subfield :' + subfield)
                return False

    def deal_initialization(self, stmt):
        initializations = stmt[CBW.initializations.value]
        for item in initializations:
            for subfield, value in item.items():
                if subfield == CBW.Declaration.value:
                    self.deal_declaration(value)
                elif subfield == CBW.Substitution.value:
                    self.deal_substitution(value)
                else:
                    print('unsolved subfield :' + subfield)
        return False

    def deal_declaration(self, stmt):
        xtype = stmt[CBW.xtype.value]
        name = stmt[CBW.name.value]
        dimensions = stmt[CBW.dimensions.value]
        if xtype == CBW.Var.value:
            self.build_var(name, dimensions)
        elif xtype == CBW.Component.value:
            MyItemError('component in func')
        elif CBW.Signal.value in xtype:
            MyItemError('signal in func')

    def getVarStmtValue(self, stmt):
        if CBW.Number.value in stmt:
            cond = stmt[CBW.Number.value][1][0]
            if cond == 0:
                return 0
            else:
                array = stmt[CBW.Number.value][1][1]
                return arrangeNumber(array, self.__exp_slv.prime())
        elif CBW.Variable.value in stmt:
            variable = stmt[CBW.Variable.value]
            var_name = variable[CBW.name.value]
            access = variable[CBW.access.value]
            is_component, name_suffix, point_suffix = self.get_access(access)

            var = self.__variable_dic[var_name + name_suffix]
            if var.type() == CBW.Var:
                return var.value
            elif var.type() == CBW.Signal:
                return var.toSmt()
            elif var.type() == CBW.VarArray:
                return var.get_value_list()
        elif CBW.InfixOp.value in stmt:
            stmt = stmt[CBW.InfixOp.value]
            left = stmt[CBW.lhe.value]
            op = stmt[CBW.infix_op.value]
            right = stmt[CBW.rhe.value]
            left_value = self.getVarStmtValue(left)
            right_value = self.getVarStmtValue(right)
            return self.dealVarInfixOp(left_value, op, right_value)
        elif CBW.PrefixOp.value in stmt:
            stmt = stmt[CBW.PrefixOp.value]
            op = stmt[CBW.prefix_op.value]
            right = stmt[CBW.rhe.value]
            right_value = self.getVarStmtValue(right)
            return self.dealVarPrefixOp(op, right_value)
        elif CBW.InlineSwitchOp.value in stmt:
            stmt = stmt[CBW.InlineSwitchOp.value]
            cond = stmt[CBW.cond.value]
            true_case = stmt[CBW.if_true.value]
            false_case = stmt[CBW.if_false.value]
            if self.getVarStmtValue(cond) != 0:
                return self.getVarStmtValue(true_case)
            else:
                return self.getVarStmtValue(false_case)
        elif CBW.Call.value in stmt:
            return self.call_function(stmt)
        elif CBW.ArrayInLine.value in stmt:
            stmt = stmt[CBW.ArrayInLine.value]
            return self.deal_arrayInline(stmt)
        else:
            colorPrint(f'unsupported VarStmtType!', COLOR.PURPLE)

    def call_function(self, stmt):
        call_stmt = stmt[CBW.Call.value]
        func_name = call_stmt[CBW.id.value]
        args_raw_values = call_stmt[CBW.args.value]
        args_values = list()
        for arg_raw_value in args_raw_values:
            arg_value = self.getVarStmtValue(arg_raw_value)
            args_values.append(arg_value)
        func_call = FunctionCall(func_name,
                                 args_values,
                                 self.__exp_slv,
                                 self.circuit_terms)
        return func_call.get_return()

    def get_access(self, access):
        is_component = False
        # 用于直接接在后面的
        name_suffix = ''
        # 用于接在.后面的
        point_suffix = ''

        pointed = False
        for acc in access:
            if CBW.ArrayAccess.value in acc:
                stmt = acc[CBW.ArrayAccess.value]
                index = self.getVarStmtValue(stmt)
                if pointed:
                    point_suffix = f'{point_suffix}[{index}]'
                else:
                    name_suffix = f'{name_suffix}[{index}]'
            elif CBW.ComponentAccess.value in acc:
                pointed = True
                call_name = acc[CBW.ComponentAccess.value]
                point_suffix = f'{call_name}'
                is_component = True
            else:
                pass
        return (is_component, name_suffix, point_suffix)

    def get_dimension_structure(self, dimensions):
        data = list()
        for stmt in dimensions:
            n = self.getVarStmtValue(stmt)
            data.append(n)
        return data

    def build_dimension_names(self, suffix, dimensions, i):
        if i < len(dimensions):
            stmt = dimensions[i]
            n = self.getVarStmtValue(stmt)

            next = list()
            for suf in suffix:
                for index in range(0, n):
                    next.append(f'{suf}[{index}]')
            return self.build_dimension_names(next, dimensions, i+1)
        else:
            return suffix

    def build_var(self, name, dimensions):
        structure = self.get_dimension_structure(dimensions)
        if len(structure) == 0:
            var = F_var(name)
            self.__variable_dic[name] = var
        else:
            var_array = F_var_array(name, structure)
            self.__variable_dic.update(var_array.get_all_var_dict())

    def deal_substitution(self, stmt):
        op = stmt[CBW.op.value]
        name = stmt[CBW.subbed_var.value]
        # name_prefix = self.component_name_mapping(name_prefix)
        access = stmt[CBW.access.value]

        is_component, name_suffix, point_suffix = self.get_access(access)
        name = name + name_suffix

        left = self.__variable_dic[name]
        right = stmt[CBW.rhe.value]

        if op == OP.AssignVar.value:
            if left.type() == CBW.Var:
                left.value = self.getVarStmtValue(right)
            elif left.type() == CBW.VarArray:
                if CBW.UniformArray.value in right:
                    uniform_array = right[CBW.UniformArray.value]
                    array_data = self.deal_uniformArray(uniform_array)
                    left.set_values(array_data)
                elif CBW.ArrayInLine.value in right:
                    array_inline = right[CBW.ArrayInLine.value]
                    array_data = self.deal_arrayInline(array_inline)
                    left.set_values(array_data)
                else:
                    array_data = self.getVarStmtValue(right)
                    left.set_values(array_data)
        else:
            MyItemError('op')

        return False

    def deal_uniformArray(self, uniform_array):
        outcome = list()
        value_stmt = uniform_array[CBW.value.value]
        if CBW.Number.value in value_stmt or CBW.Variable.value in value_stmt:
            value = self.getVarStmtValue(value_stmt)
        elif CBW.UniformArray.value in value_stmt:
            value = self.deal_uniformArray(value_stmt[CBW.UniformArray.value])
        dimension = uniform_array[CBW.dimension.value]
        size = self.getVarStmtValue(dimension)
        for i in range(size):
            outcome.append(value)
        return outcome

    def deal_arrayInline(self, array_inline):
        outcome = list()
        values_stmt = array_inline[CBW.values.value]
        for stmt in values_stmt:
            if CBW.ArrayInLine.value in stmt:
                value = self.deal_arrayInline(stmt[CBW.ArrayInLine.value])
            elif CBW.Number.value in stmt or CBW.Variable.value in stmt:
                value = self.getVarStmtValue(stmt)
            outcome.append(value)
        return outcome

    def deal_while(self, stmt):
        cond = stmt[CBW.cond.value]
        body = stmt[CBW.stmt.value]
        while self.check_cond(cond):
            if CBW.Block.value in body:
                ended = self.deal_block(body[CBW.Block.value])
            else:
                ended = self.deal_sub_field(body)
            if ended:
                return True
        return False

    def dealVarInfixOp(self, left, op, right):
        if isinstance(left, int) and isinstance(right, int):
            return calculate_deterministic_infixOp(left, op, right, self.__exp_slv.prime())
        if isinstance(left, int):
            if isinstance(left, bool):
                left = self.__exp_slv.FF_one() if left else self.__exp_slv.FF_zero()
            else:
                left = self.__exp_slv.FF_number(left)
        if isinstance(right, int):
            if isinstance(right, bool):
                right = self.__exp_slv.FF_one() if right else self.__exp_slv.FF_zero()
            else:
                right = self.__exp_slv.FF_number(right)
        return self.mkInfixTerm(left, op, right)

    def dealVarPrefixOp(self, op, right):
        if isinstance(right, int):
            return calculate_deterministic_prefixOp(op, right, self.__exp_slv.prime())
        else:
            return self.mkPrefixTerm(op, right)

    def mkInfixTerm(self, left, op, right):
        # print(f'{left} {op} {right}')
        if op == EIO.Add.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, left, right)

        elif op == EIO.Sub.value:
            # 取负
            neg_right = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, right)
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, left, neg_right)

        elif op == EIO.Mul.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, left, right)

        elif op == EIO.Div.value:
            # 取乘法逆元
            inv_right = self.__exp_slv.slv().mkConst(self.__exp_slv.F(), f'1 / {right}')
            mult = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, right, inv_right)
            eq = self.__exp_slv.mkTerm(Kind.EQUAL, mult, self.__exp_slv.FF_one())
            self.circuit_terms.append(eq)
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, left, inv_right)

        elif op == EIO.Eq.value:
            return self.__exp_slv.mkTerm(Kind.EQUAL, left, right)

        elif op == EIO.NotEq.value:
            Eq = self.__exp_slv.mkTerm(Kind.EQUAL, left, right)
            return self.__exp_slv.mkTerm(Kind.NOT, Eq)

        elif op == EIO.BoolAnd.value:
            return self.__exp_slv.mkTerm(Kind.AND, left, right)

        elif op == EIO.BoolOr.value:
            return self.__exp_slv.mkTerm(Kind.OR, left, right)

        elif op == EIO.Greater.value:
            return self.__exp_slv.mkFFTerm_Gt(left, right)

        elif op == EIO.Lesser.value:
            return self.__exp_slv.mkFFTerm_Lt(left, right)

        elif op == EIO.GreaterEq.value:
            return self.__exp_slv.mkFFTerm_Ge(left, right)

        elif op == EIO.LesserEq.value:
            return self.__exp_slv.mkFFTerm_Le(left, right)

        elif op == EIO.ShiftR.value:
            return self.__exp_slv.mkFFTerm_Right_Shift(left, right)

        elif op == EIO.ShiftL.value:
            return self.__exp_slv.mkFFTerm_Left_Shift(left, right)

        elif op == EIO.BitAnd.value:
            return self.__exp_slv.mkFFTerm_Bit_And(left, right)

        elif op == EIO.BitOr.value:
            return self.__exp_slv.mkFFTerm_Bit_Or(left, right)

        elif op == EIO.BitXor.value:
            return self.__exp_slv.mkFFTerm_Bit_Xor(left, right)

        elif op == EIO.Pow.value:
            return self.__exp_slv.mkFFTerm_Pow(left, right)

        elif op == EIO.Mod.value:
            return self.__exp_slv.mkFFTerm_Mod(left, right)

        elif op == EIO.IntDiv.value:
            return self.__exp_slv.mkFFTerm_IntDiv(left, right)

        else:
            colorPrint(f'WARNING: meet currently unsupported signal operator in function: {op}', COLOR.PURPLE)

    def mkPrefixTerm(self, op, right):
        if op == EPO.Sub.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, right)
        elif op == EPO.BitNot.value:
            return self.__exp_slv.mkFFTerm_Bit_Not(right)
        elif op == EPO.Complement.value:
            return self.__exp_slv.mkFFTerm_bit_Complement(right)
        else:
            colorPrint(f'WARNING: meet currently unsupported prefix signal operator: {op}', COLOR.PURPLE)

    def check_cond(self, stmt):
        return self.getVarStmtValue(stmt)

    def deal_ifThenElse(self, stmt):
        cond = stmt[CBW.cond.value]
        if self.check_cond(cond):
            if_case = stmt[CBW.if_case.value]
            if CBW.Block.value in if_case:
                return self.deal_block(if_case[CBW.Block.value])
            else:
                return self.deal_sub_field(if_case)
        else:
            else_case = stmt[CBW.else_case.value]
            if else_case is not None:
                if CBW.Block.value in else_case:
                    return self.deal_block(else_case[CBW.Block.value])
                else:
                    return self.deal_sub_field(else_case)
            return False

    def deal_return(self, stmt):
        self.__ret_value = self.getVarStmtValue(stmt[CBW.value.value])
        return True

    def get_return(self):
        return self.__ret_value