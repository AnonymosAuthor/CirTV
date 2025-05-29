from cvc5 import Kind

from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Circuit.BuildinWords import CBW, EIO, EPO, OP
from Elements.Circuit.FunctionCall import FunctionCall
from Elements.Circuit.Interfaces import Type
from Elements.Circuit.LogicTree import LogicNode
from Elements.Circuit.Signal import SignalTypes, Signal, SignalArray
from Elements.Circuit.Template import Template
from Elements.Circuit.Var import Var, VarArray
from Tools.Calculate import calculate_deterministic_infixOp, calculate_deterministic_prefixOp, arrangeNumber
from Tools.Check import TypeCheck
from Tools.ColorPrint import colorPrint, COLOR
from Tools.Errors import MyItemError, MyNumError, UnSupportedOperators


class Component(Type):

    @staticmethod
    def main_component(js_mc, exp_slv:ExpandedCVC5):
        component = Component('main', exp_slv)
        prime = exp_slv.prime()
        call = js_mc[1][CBW.Call.value]
        template_name = call[CBW.id.value]
        raw_args = call[CBW.args.value]
        args = Component.deal_main_args(raw_args, prime)
        component.call_template(template_name, args)
        return component

    @staticmethod
    def deal_main_args(args, prime):
        outcome = list()
        for stmt in args:
            arg_value = Component.deal_main_arg_core(stmt, prime)
            outcome.append(arg_value)
        return outcome

    # 处理参数的
    @staticmethod
    def deal_main_arg_core(stmt, prime):
        for key, item in stmt.items():
            if key == CBW.Number.value:
                value_type = item[1][0]
                if value_type == 0:
                    return 0
                else:
                    array = item[1][1]
                    return arrangeNumber(array, prime)
            elif key == CBW.InfixOp.value:
                op = item[CBW.infix_op.value]
                lhe = item[CBW.lhe.value]
                rhe = item[CBW.rhe.value]
                delt_lhe = Component.deal_main_arg_core(lhe, prime)
                delt_rhe = Component.deal_main_arg_core(rhe, prime)
                value = calculate_deterministic_infixOp(delt_lhe, op, delt_rhe, prime)
                return value
            elif key == CBW.PrefixOp.value:
                op = item[CBW.prefix_op.value]
                rhe = item[CBW.rhe.value]
                delt_rhe = Component.deal_main_arg_core(rhe, prime)
                value = calculate_deterministic_prefixOp(op, delt_rhe, prime)
                return value
            elif key == CBW.InlineSwitchOp.value:
                cond = item[CBW.cond.value]
                true_case = item[CBW.if_true.value]
                false_case = item[CBW.if_false.value]
                if Component.deal_main_arg_core(cond, prime) != 0:
                    return Component.deal_main_arg_core(true_case, prime)
                else:
                    return Component.deal_main_arg_core(false_case, prime)

            elif key == CBW.ArrayInLine.value:
                outcome = list()
                values_stmt = item[CBW.values.value]
                for stmt in values_stmt:
                    value = Component.deal_main_arg_core(stmt, prime)
                    outcome.append(value)
                return outcome

            else:
                raise MyNumError('unsupported main args types')

    def __init__(self, call_name, exp_slv: ExpandedCVC5):
        TypeCheck(str, call_name)
        TypeCheck(ExpandedCVC5, exp_slv)
        self.__exp_slv = exp_slv
        # call_name 是在代码段中的名字
        self.__call_name = call_name
        # id_name 是唯一的名字，在调用template生成后才会给定
        self.__id_name = ''
        # subcomponent name --> component
        self.__sub_components = dict()
        # variable name --> variable
        self.__variable_dic = dict()
        self.__signal_dic = dict()
        self.__parameter_list = list()
        self.__input_signal_dic = dict()
        self.__output_signal_dic = dict()
        self.__all_signals_dic = None
        self.calculate_terms = list()
        self.constraint_terms = list()
        self.__all_signals_dic = None

    def call_template(self, template_name, args_values):

        # print(f'============= {template_name} is called =============')

        template = Template.get_Template(template_name)
        suffix = template.prepare_build_component()
        self.__id_name = template.get_name() + suffix
        args_names = template.get_args()
        self.init_parameter_list(args_names, args_values)
        block = template.get_block()
        self.block_2_smt(block)

    def init_parameter_list(self, args_names, args_values):
        for i in range(len(args_names)):
            call_name = args_names[i]
            id_name = self.build_id_name(call_name)
            value = args_values[i]
            if isinstance(value, int):
                var = Var(call_name, id_name, self.__exp_slv)
                var.value = args_values[i]
                self.__variable_dic[call_name] = var
                self.__parameter_list.append(var)
                # print(f'Para var {id_name} = {var.value}')
            elif isinstance(value, VarArray):
                var_array = VarArray.deep_clone_and_rename(call_name, id_name, value, self.__exp_slv)
                self.record_var_array(var_array)
            elif isinstance(value, list):
                var_array = VarArray.generate_from_list(call_name, id_name, value, self.__exp_slv)
                self.record_var_array(var_array)
            else:
                print('unsupported argv type')

    def type(self):
        return CBW.Component

    def get_all_calculate_terms(self):
        outcome = list()
        outcome.extend(self.calculate_terms)
        for call_name, comp in self.__sub_components.items():
            outcome.extend(comp.get_all_calculate_terms())
        return outcome

    def get_all_constraint_terms(self):
        outcome = list()
        outcome.extend(self.constraint_terms)
        for call_name, comp in self.__sub_components.items():
            outcome.extend(comp.get_all_constraint_terms())
        return outcome

    def get_all_signals_dic(self):
        if self.__all_signals_dic is None:
            self.__all_signals_dic = dict()
            self.__all_signals_dic.update(self.__signal_dic)
            for call_name, comp in self.__sub_components.items():
                sub_comp_signals = comp.get_all_signals_dic()
                for signal in sub_comp_signals.values():
                    signal.loc_sym_name(self.__call_name)
                    self.__all_signals_dic[signal.id_name] = signal
        return self.__all_signals_dic

    def get_io_signal(self, call_name):
        TypeCheck(str, call_name)
        return self.__variable_dic[call_name]

    def get_output_signals_dic(self):
        return self.__output_signal_dic

    def get_input_signals_dic(self):
        return self.__input_signal_dic

    def block_2_smt(self, block, node=None):
        stmts = block[CBW.stmts.value]
        for stmt in stmts:
            self.stmt_2_smt(stmt, node)

    # Node: logicNode 如果非空，即表明处于分支环境下
    def stmt_2_smt(self, stmt, node=None):
        for subfield, value in stmt.items():
            if subfield == CBW.InitializationBlock.value:
                self.initialization_block_2_smt(value)
            elif subfield == CBW.Substitution.value:
                self.substitution_2_smt(value, node)
            elif subfield == CBW.Block.value:
                self.block_2_smt(value, node)
            elif subfield == CBW.ConstraintEquality.value:
                self.equality_2_smt(value)
            elif subfield == CBW.While.value:
                self.deal_while(value)
            elif subfield == CBW.IfThenElse.value:
                self.deal_ifThenElse(value, node)
            elif subfield == CBW.Assert.value:
                self.deal_assert(value, node)
            else:
                print('unsolved subfield :' + subfield)

    def deal_assert(self, value, node=None):
        # print('assert')
        assert_value = self.getVarStmtValue(value[CBW.arg.value], node)
        if not assert_value:
            raise "assert is violated!!!"

    def initialization_block_2_smt(self, initialization_block):
        initializations = initialization_block[CBW.initializations.value]
        self.initialization_2_smt(initializations)

    def initialization_2_smt(self, initialization):
        for item in initialization:
            for subfield, value in item.items():
                if subfield == CBW.Declaration.value:
                    self.declaration_2_smt(value)
                elif subfield == CBW.Substitution.value:
                    self.substitution_2_smt(value)
                else:
                    print('unsolved subfield :' + subfield)

    def declaration_2_smt(self, declaration):
        xtype = declaration[CBW.xtype.value]
        name = declaration[CBW.name.value]
        dimensions = declaration[CBW.dimensions.value]
        if xtype == CBW.Var.value:
            self.build_var(name, dimensions)
        elif xtype == CBW.Component.value:
            self.build_component(name, dimensions)
        elif CBW.Signal.value in xtype:
            self.build_signal(xtype, name, dimensions)

    def build_var(self, call_name, dimensions):
        id_name = self.build_id_name(call_name)
        suffix = self.build_dimension_names([''], dimensions, 0)
        # 以数组形式构造的
        if suffix[0] != '':
            var_list = list()
            structure = self.get_dimension_structure(dimensions)
            # print(structure)
            for suf in suffix:
                delt_id_name = id_name + suf
                delt_call_name = call_name + suf
                var = Var(delt_call_name, delt_id_name, self.__exp_slv)
                # self.__variable_dic[delt_call_name] = var
                var_list.append(var)
                # print(var)
            var_array = VarArray(call_name, id_name, var_list, structure)
            self.record_var_array(var_array)
            #self.__variable_dic[call_name] = var_array
        else:
            var = Var(call_name, id_name, self.__exp_slv)
            self.__variable_dic[call_name] = var

    def record_var_array(self, var_array):
        self.__variable_dic[var_array.call_name] = var_array
        if var_array.child_type == CBW.Var:
            for var in var_array.var_list:
                self.__variable_dic[var.call_name] = var
        elif var_array.child_type == CBW.VarArray:
            for child_array in var_array.var_list:
                self.record_var_array(child_array)

    def build_component(self, call_name, dimensions):
        suffix = self.build_dimension_names([''], dimensions, 0)
        for suf in suffix:
            delt_call_name = call_name + suf
            component = Component(delt_call_name, self.__exp_slv)
            self.__variable_dic[delt_call_name] = component
            self.__sub_components[delt_call_name] = component

    def build_signal(self, xtype, call_name, dimensions):
        id_name = self.build_id_name(call_name)
        raw_type = xtype[CBW.Signal.value][0]
        if raw_type == CBW.Input.value:
            signal_type = SignalTypes.Input
        elif raw_type == CBW.Output.value:
            signal_type = SignalTypes.Output
        elif raw_type == CBW.Intermediate.value:
            signal_type = SignalTypes.Intermediate
        else:
            raise MyItemError(raw_type)

        suffix = self.build_dimension_names([''], dimensions, 0)
        signal_list = list()
        for suf in suffix:
            delt_id_name = id_name + suf
            delt_call_name = call_name + suf
            delt_sym_name = f'{self.__call_name}.{delt_call_name}'
            smt = self.__exp_slv.mkConst(self.__exp_slv.F(), delt_id_name)
            signal = Signal(delt_call_name, delt_id_name, delt_sym_name, signal_type, smt)
            self.__variable_dic[delt_call_name] = signal
            self.__signal_dic[signal.id_name] = signal
            signal_list.append(signal)
            if signal_type == SignalTypes.Output:
                self.__output_signal_dic[signal.id_name] = signal
            elif signal_type == SignalTypes.Input:
                self.__input_signal_dic[signal.id_name] = signal
            # print(signal)
        if len(dimensions) > 0:
            signalArray = SignalArray(call_name, id_name, signal_list, self.get_dimension_structure(dimensions))
            self.record_signal_array(signalArray)

    def record_signal_array(self, signal_array):
        self.__variable_dic[signal_array.call_name] = signal_array
        if signal_array.child_type == CBW.SignalArray:
            for child_array in signal_array.signal_list:
                self.record_signal_array(child_array)

    def get_dimension_structure(self, dimensions, node=None):
        data = list()
        for stmt in dimensions:
            n = self.getVarStmtValue(stmt, node)
            data.append(n)
        return data

    def build_dimension_names(self, suffix, dimensions, i, node=None):
        if i < len(dimensions):
            stmt = dimensions[i]
            n = self.getVarStmtValue(stmt, node)

            next = list()
            for suf in suffix:
                for index in range(0, n):
                    next.append(f'{suf}[{index}]')
            return self.build_dimension_names(next, dimensions, i+1)
        else:
            return suffix

    def component_name_mapping(self, name_prefix):
        if name_prefix in self.__sub_components.keys():
            current_name = self.__sub_components.get(name_prefix).__id_name
            if len(current_name) != 0:
                return current_name
        return name_prefix

    def substitution_2_smt(self, substitution, node=None):
        op = substitution[CBW.op.value]
        name = substitution[CBW.subbed_var.value]

        # name_prefix = self.component_name_mapping(name_prefix)
        access = substitution[CBW.access.value]

        is_component, name_suffix, point_suffix = self.get_access(access)
        name = name + name_suffix

        left = self.__variable_dic[name]
        right = substitution[CBW.rhe.value]
        # for signals <== <--
        if op == OP.AssignConstraintSignal.value or op == OP.AssignSignal.value:
            if left.type() is CBW.Signal:
                delt_left = left.toSmt()

            elif left.type() is CBW.SignalArray:
                delt_left = left

            elif left.type() is CBW.Component:
                call_name = point_suffix
                signal = left.get_io_signal(call_name)
                delt_left = signal.toSmt()

            else:
                colorPrint(f'unsupport left type: {left.type()}', COLOR.PURPLE)
                delt_left = None

            # 需要考察右测是否有条件运算
            if CBW.InlineSwitchOp.value in right:
                switch = right[CBW.InlineSwitchOp.value]
                cond = switch[CBW.cond.value]
                t_case = switch[CBW.if_true.value]
                f_case = switch[CBW.if_false.value]
                d_cond = self.item_2_smt(cond)

                if isinstance(d_cond, int):
                    d_cond = d_cond != 0
                if isinstance(d_cond, bool):
                    if d_cond:
                        dt_case = self.item_2_smt(t_case)
                        if isinstance(dt_case, int):
                            dt_case = self.__exp_slv.FF_number(dt_case)
                        term = self.construct_eq(delt_left, dt_case)
                    else:
                        df_case = self.item_2_smt(f_case)
                        if isinstance(df_case, int):
                            df_case = self.__exp_slv.FF_number(df_case)
                        term = self.construct_eq(delt_left, df_case)
                else:
                    dt_case = self.item_2_smt(t_case)
                    df_case = self.item_2_smt(f_case)
                    if isinstance(dt_case, int):
                        dt_case = self.__exp_slv.FF_number(dt_case)
                    if isinstance(df_case, int):
                        df_case = self.__exp_slv.FF_number(df_case)
                    term = self.mkSwitchTerm(delt_left, op, d_cond, dt_case, df_case)
            else:
                if CBW.Call.value in right:
                    call_stmt = right[CBW.Call.value]
                    delt_right = self.call_function(call_stmt, node)
                else:
                    delt_right = self.item_2_smt(right)
                if isinstance(delt_right, int):
                    if delt_right == 0:
                        delt_right = self.__exp_slv.FF_zero()
                    else:
                        delt_right = self.__exp_slv.FF_number(delt_right)
                term = self.construct_eq(delt_left, delt_right)
            self.calculate_terms.append(term)
            if op == OP.AssignConstraintSignal.value:
                self.constraint_terms.append(term)

        elif op == OP.AssignVar.value:
            if left.type() == CBW.Component:
                call = right[CBW.Call.value]
                template_name = call[CBW.id.value]

                args_raw_values = call[CBW.args.value]
                args_values = list()
                for arg_raw_value in args_raw_values:
                    arg_value = self.getVarStmtValue(arg_raw_value, node)
                    args_values.append(arg_value)

                left.call_template(template_name, args_values)
            elif left.type() == CBW.Var:
                new_value = self.getVarStmtValue(right, node)
                if node is None:            # 不在分支中，直接更新
                    left.value = new_value
                else:                       # 在分支中，更新局部表
                    node.updateVar(left.call_name, new_value)
            elif left.type() == CBW.VarArray:
                if CBW.UniformArray.value in right:
                    uniform_array = right[CBW.UniformArray.value]
                    array_data = self.deal_uniformArray(uniform_array)
                    left.set_values(array_data)
                elif CBW.ArrayInLine.value in right:
                    array_inline = right[CBW.ArrayInLine.value]
                    array_data = self.deal_arrayInline(array_inline)
                    left.set_values(array_data)
                elif CBW.Call.value in right:
                    call_stmt = right[CBW.Call.value]
                    array_data = self.call_function(call_stmt, node)
                    left.set_values(array_data)

    def construct_eq(self, left, right):
        if isinstance(left, VarArray) or isinstance(left, SignalArray):
            left_plant_array = left.get_all_children()
            terms = list()
            # 用于处理arrayInline的情况
            if isinstance(right, list):
                for i in range(len(left_plant_array)):
                    left_element = left_plant_array[i]
                    if isinstance(right[i], int):
                        element_eq = self.__exp_slv.mkTerm(Kind.EQUAL, left_element.toSmt(), self.__exp_slv.FF_number(right[i]))
                    else:
                        element_eq = self.__exp_slv.mkTerm(Kind.EQUAL, left_element.toSmt(), right[i])
                    terms.append(element_eq)
            else:
                right_plant_array = right.get_all_children()
                for i in range(len(left_plant_array)):
                    left_element = left_plant_array[i]
                    right_element = right_plant_array[i]
                    element_eq = self.__exp_slv.mkTerm(Kind.EQUAL, left_element.toSmt(), right_element.toSmt())
                    terms.append(element_eq)
            if len(terms) == 1:
                return terms[0]
            else:
                return self.__exp_slv.mkTerm(Kind.AND, *terms)
        else:
            return self.__exp_slv.mkTerm(Kind.EQUAL, left, right)

    def deal_uniformArray(self, uniform_array, node=None):
        outcome = list()
        value_stmt = uniform_array[CBW.value.value]
        if CBW.Number.value in value_stmt or CBW.Variable.value in value_stmt:
            value = self.getVarStmtValue(value_stmt, node)
        elif CBW.UniformArray.value in value_stmt:
            value = self.deal_uniformArray(value_stmt[CBW.UniformArray.value])
        dimension = uniform_array[CBW.dimension.value]
        size = self.getVarStmtValue(dimension, node)
        for i in range(size):
            outcome.append(value)
        return outcome

    def deal_arrayInline(self, array_inline, node=None):
        outcome = list()
        values_stmt = array_inline[CBW.values.value]
        for stmt in values_stmt:
            if CBW.ArrayInLine.value in stmt:
                value = self.deal_arrayInline(stmt[CBW.ArrayInLine.value])
            elif CBW.Number.value in stmt or CBW.Variable.value in stmt:
                value = self.getVarStmtValue(stmt, node)
            else:
                value = self.getVarStmtValue(stmt, node)
            outcome.append(value)
        return outcome

    def get_access(self, access, node=None):
        is_component = False
        # 用于直接接在后面的
        name_suffix = ''
        # 用于接在.后面的
        point_suffix = ''

        pointed = False
        for acc in access:
            if CBW.ArrayAccess.value in acc:
                stmt = acc[CBW.ArrayAccess.value]
                index = self.getVarStmtValue(stmt, node)
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

    def mkSwitchTerm(self, left, op, cond, t_case, f_case):
        if op == OP.AssignSignal.value:
            neg_cond = self.__exp_slv.mkTerm(Kind.NOT, cond)
            t_eq = self.construct_eq(left, t_case)
            f_eq = self.construct_eq(left, f_case)
            t_imply = self.__exp_slv.mkTerm(Kind.IMPLIES, cond, t_eq)
            f_imply = self.__exp_slv.mkTerm(Kind.IMPLIES, neg_cond, f_eq)
            return self.__exp_slv.mkTerm(Kind.AND, t_imply, f_imply)

    def item_2_smt(self, item, node=None):
        if CBW.InfixOp.value in item:
            stmt = item[CBW.InfixOp.value]
            left = stmt[CBW.lhe.value]
            infix_op = stmt[CBW.infix_op.value]
            right = stmt[CBW.rhe.value]
            delt_left = self.item_2_smt(left)
            delt_right = self.item_2_smt(right)
            return self.dealVarInfixOp(delt_left, infix_op, delt_right)
            # return self.mkInfixTerm(delt_left, infix_op, delt_right)

        elif CBW.PrefixOp.value in item:
            stmt = item[CBW.PrefixOp.value]
            prefix_op = stmt[CBW.prefix_op.value]
            right = stmt[CBW.rhe.value]
            delt_right = self.item_2_smt(right)
            return self.dealVarPrefixOp(prefix_op, delt_right)
            # return self.mkPrefixTerm(prefix_op, delt_right)

        elif CBW.Variable.value in item:
            js_variable = item[CBW.Variable.value]
            name = js_variable[CBW.name.value]
            # name_prefix = self.component_name_mapping(name_prefix)
            access = js_variable[CBW.access.value]
            is_component, name_suffix, point_suffix = self.get_access(access)
            name = name + name_suffix

            variable = self.__variable_dic[name]
            if variable.type() is CBW.Signal:
                return variable.toSmt()
            elif variable.type() is CBW.Var:
                # 对于var变量，如果被signal赋值过了，那就会返回term
                # 否则就是返回自己的值
                value = variable.value
                return value
            elif variable.type() is CBW.Component:
                call_name = point_suffix
                signal = variable.get_io_signal(call_name)
                return signal.toSmt()
            elif variable.type() is CBW.SignalArray:
                return variable
            elif variable.type() is CBW.VarArray:
                return variable

        elif CBW.Number.value in item:
            value_type = item[CBW.Number.value][1][0]
            if value_type == 0:
                return 0
            else:
                array = item[CBW.Number.value][1][1]
                return arrangeNumber(array, self.__exp_slv.prime())

                # 这个是不对的
                # value = item[CBW.Number.value][1][1][0]
                # return value

        elif CBW.Call.value in item:
            call_stmt = item[CBW.Call.value]
            func_name = call_stmt[CBW.id.value]

            # print(f'============= function: {func_name} is called =============')

            args_raw_values = call_stmt[CBW.args.value]
            args_values = list()
            for arg_raw_value in args_raw_values:
                arg_value = self.getVarStmtValue(arg_raw_value, node)
                args_values.append(arg_value)
            func_call = FunctionCall(func_name,
                                     args_values,
                                     self.__exp_slv,
                                     self.calculate_terms)
            return func_call.get_return()

        elif CBW.ArrayInLine.value in item:
            array_inline = item[CBW.ArrayInLine.value]
            return self.deal_arrayInline(array_inline)

        else:
            MyItemError(item)

    def tryGetVarValue(self, var : Var):
        terms = self.get_all_calculate_terms()
        self.__exp_slv.push()
        name = f'{var.call_name}_temp_value'
        temp_v = self.__exp_slv.mkConst(self.__exp_slv.F(), name)
        temp_term = self.__exp_slv.mkTerm(Kind.EQUAL, temp_v, var.value)
        self.__exp_slv.assertFormula(temp_term)
        for term in terms:
            self.__exp_slv.assertFormula(term)
        outcome = self.__exp_slv.checkSat()
        # print(outcome)
        self.__exp_slv.pop()

    def getVarStmtValue(self, stmt, node):
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
            if is_component:
                subcomponent = self.__sub_components[var_name + name_suffix]
                var = subcomponent.get_io_signal(point_suffix)
            else:
                var = self.__variable_dic[var_name + name_suffix]
            if var.type() == CBW.Var:
                if node is None:
                    return var.value
                else:
                    value = node.getValue(var.call_name)
                    if value is not None:
                        return value
                    else:
                        return var.value
            elif var.type() == CBW.VarArray:
                return var.get_value_list()
            elif var.type() == CBW.Signal:
                return var.toSmt()
            elif var.type() == CBW.SignalArray:
                return var.toSmt()
        elif CBW.InfixOp.value in stmt:
            stmt = stmt[CBW.InfixOp.value]
            left = stmt[CBW.lhe.value]
            op = stmt[CBW.infix_op.value]
            right = stmt[CBW.rhe.value]
            left_value = self.getVarStmtValue(left, node)
            right_value = self.getVarStmtValue(right, node)
            return self.dealVarInfixOp(left_value, op, right_value)
        elif CBW.PrefixOp.value in stmt:
            stmt = stmt[CBW.PrefixOp.value]
            op = stmt[CBW.prefix_op.value]
            right = stmt[CBW.rhe.value]
            right_value = self.getVarStmtValue(right, node)
            return self.dealVarPrefixOp(op, right_value)
        elif CBW.Call.value in stmt:
            call_stmt = stmt[CBW.Call.value]
            return self.call_function(call_stmt, node)
        elif CBW.InlineSwitchOp.value in stmt:
            stmt = stmt[CBW.InlineSwitchOp.value]
            cond = stmt[CBW.cond.value]
            true_case = stmt[CBW.if_true.value]
            false_case = stmt[CBW.if_false.value]
            if self.getVarStmtValue(cond, node) != 0:
                return self.getVarStmtValue(true_case, node)
            else:
                return self.getVarStmtValue(false_case, node)
        elif CBW.ArrayInLine.value in stmt:
            array_inline = stmt[CBW.ArrayInLine.value]
            return self.deal_arrayInline(array_inline)
        else:
            print('unsupported var calculating method')

    def call_function(self, call_stmt, node):
        func_name = call_stmt[CBW.id.value]

        # print(f'============= {func_name} is called =============')

        args_raw_values = call_stmt[CBW.args.value]
        args_values = list()
        for arg_raw_value in args_raw_values:
            arg_value = self.getVarStmtValue(arg_raw_value, node)
            args_values.append(arg_value)
        func_call = FunctionCall(func_name, args_values, self.__exp_slv, self.calculate_terms)
        return func_call.get_return()

    # 这里计算的是var对象和var对象，当然也有可能是signal
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

    # 处理中缀表达式
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
            self.calculate_terms.append(eq)
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, left, inv_right)

        elif op == EIO.Eq.value:
            return self.__exp_slv.mkTerm(Kind.EQUAL, left, right)

        elif op == EIO.NotEq.value:
            Eq = self.__exp_slv.mkTerm(Kind.EQUAL, left, right)
            return self.__exp_slv.mkTerm(Kind.NOT, Eq)

        elif op == EIO.Greater.value:
            return self.__exp_slv.mkFFTerm_Gt(left, right)

        elif op == EIO.Lesser.value:
            return self.__exp_slv.mkFFTerm_Lt(left, right)

        elif op == EIO.GreaterEq.value:
            return self.__exp_slv.mkFFTerm_Ge(left, right)

        elif op == EIO.LesserEq.value:
            return self.__exp_slv.mkFFTerm_Le(left, right)

        elif op == EIO.BoolAnd.value:
            return self.__exp_slv.mkTerm(Kind.AND, left, right)

        elif op == EIO.BoolOr.value:
            return self.__exp_slv.mkTerm(Kind.OR, left, right)

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
            colorPrint(f'WARNING: meet currently unsupported suffix signal operator: {op}', COLOR.PURPLE)
            UnSupportedOperators()

    def mkPrefixTerm(self, op, right):
        if op == EPO.Sub.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, right)
        elif op == EPO.BitNot.value:
            return self.__exp_slv.mkFFTerm_Bit_Not(right)
        elif op == EPO.Complement.value:
            return self.__exp_slv.mkFFTerm_bit_Complement(right)
        else:
            colorPrint(f'WARNING: meet currently unsupported prefix signal operator: {op}', COLOR.PURPLE)
            UnSupportedOperators()

    def equality_2_smt(self, equality):
        left = equality[CBW.lhe.value]
        right = equality[CBW.rhe.value]
        delt_left = self.item_2_smt(left)
        delt_right = self.item_2_smt(right)
        if isinstance(delt_left, int):
            delt_left = self.__exp_slv.FF_number(delt_left)
        if isinstance(delt_right, int):
            delt_right = self.__exp_slv.FF_number(delt_right)
        constraint = self.__exp_slv.mkTerm(Kind.EQUAL, delt_left, delt_right)
        self.calculate_terms.append(constraint)     # 也需要添加，因为c++会对应增加assert语句
        self.constraint_terms.append(constraint)

    # 生成变量，如signal等在具体component中的名字
    def build_id_name(self, call_name):
        return f'{self.__id_name}.{call_name}'

    def deal_while(self, item):
        cond = item[CBW.cond.value]
        block = item[CBW.stmt.value][CBW.Block.value]
        while self.check_cond(cond):
            self.block_2_smt(block)

    def deal_ifThenElse(self, item, node=None):
        cond = item[CBW.cond.value]
        if_case = item[CBW.if_case.value]
        else_case = item[CBW.else_case.value]

        # temp = self.check_cond(cond)
        # if temp:
        #     pass
        #
        # if self.check_cond(cond):
        #     self.stmt_2_smt(if_case)
        # elif else_case is not None:
        #     self.stmt_2_smt(else_case)

        # temp temp temp
        delt_cond = self.check_cond(cond)
        # self.tryGetCondValue(delt_cond)
        if isinstance(delt_cond, bool):
            if delt_cond:
                self.stmt_2_smt(if_case)
            elif else_case is not None:
                self.stmt_2_smt(else_case)
        else:
            # 处理分支逻辑
            if node is None:
                root = LogicNode(node, None, self.__exp_slv)  # 根节点
                node = root

            trueChild = LogicNode(node, delt_cond, self.__exp_slv)
            node.setTrueChild(trueChild)
            self.stmt_2_smt(if_case, trueChild)

            delt_cond_not = self.__exp_slv.mkTerm(Kind.NOT, delt_cond)
            falseChild = LogicNode(node, delt_cond_not, self.__exp_slv)
            node.setFalseChild(falseChild)
            if else_case is not None:
                self.stmt_2_smt(else_case, falseChild)

            updatedVars = node.getChildUpdatedVars()

            # 没更新就直接结束
            if len(updatedVars) == 0:
                return

            trueExps = list()
            falseExps = list()
            for callName in updatedVars:
                var = self.__variable_dic[callName]
                newSmt = var.indexing()

                trueValue = trueChild.getValue(callName)
                if trueValue is None:
                    trueValue = var.value
                if isinstance(trueValue, int):
                    trueValue = self.__exp_slv.FF_number(trueValue)
                trueExps.append(self.__exp_slv.mkTerm(Kind.EQUAL, newSmt, trueValue))

                falseValue = falseChild.getValue(callName)
                if falseValue is None:
                    falseValue = var.value
                if isinstance(falseValue, int):
                    falseValue = self.__exp_slv.FF_number(falseValue)
                falseExps.append(self.__exp_slv.mkTerm(Kind.EQUAL, newSmt, falseValue))

                if node.isRoot():
                    var.value = newSmt
                else:
                    node.updateVar(callName, newSmt)

            if len(updatedVars) == 1:
                trueExp = trueExps[0]
                falseExp = falseExps[0]
            else:
                trueExp = self.__exp_slv.mkTerm(Kind.AND, *trueExps)
                falseExp = self.__exp_slv.mkTerm(Kind.AND, *falseExps)

            trueCond = trueChild.getTotalCond()
            falseCond = falseChild.getTotalCond()
            self.calculate_terms.append(self.__exp_slv.mkTerm(Kind.IMPLIES, trueCond, trueExp))
            self.calculate_terms.append(self.__exp_slv.mkTerm(Kind.IMPLIES, falseCond, falseExp))


    def check_cond(self, stmt, node=None):
        exp = self.getVarStmtValue(stmt, node)
        # temp = self.tryGetCondValue(exp)
        return exp

    # true
    # false
    # null 未知
    def tryGetCondValue(self, cond):
        terms = self.get_all_calculate_terms()
        self.__exp_slv.push()
        name = f'temp_boolean_value'
        exp = self.__exp_slv.mkTerm(Kind.EQUAL, cond, self.__exp_slv.Boolean_True())
        self.__exp_slv.assertFormula(exp)
        for term in terms:
            self.__exp_slv.assertFormula(term)
        outcome = self.__exp_slv.checkSat()
        print(outcome)

        self.__exp_slv.pop()
        pass

