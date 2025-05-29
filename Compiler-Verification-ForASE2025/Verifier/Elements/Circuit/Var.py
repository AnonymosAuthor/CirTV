from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Circuit.BuildinWords import CBW
from Elements.Circuit.Interfaces import Type, SmtBuild
from Tools.Check import *
from Tools.ColorPrint import colorPrint


class Var(SmtBuild, Type):
    def __init__(self, call_name, id_name, exp_slv:ExpandedCVC5):
        TypeCheck(str, call_name)
        TypeCheck(str, id_name)
        self.call_name = call_name
        self.id_name = id_name
        self.exp_slv = exp_slv
        self.value = 0
        self.count = 0          # 用于变量化的序数
        # deterministic == True ===> value is int
        # deterministic == False ===> expression

    def __str__(self):
        return f"Var {self.id_name}"

    def indexing(self):
        outcome = self.exp_slv.mkConst(self.exp_slv.F(), self.id_name + '_' + str(self.count))
        self.count += 1
        return outcome

    def type(self):
        return CBW.Var

    def toSmt(self):
        if isinstance(self.value, int):
            return self.exp_slv.FF_number(self.value)
        else:
            return self.value

    def __repr__(self):
        return self.id_name


class VarArray(Type):

    @staticmethod
    def generate_from_list(call_name, id_name, raw, exp_slv):
        if isinstance(raw, int):
            var = Var(call_name, id_name, exp_slv)
            var.value = raw
            return var
        elif isinstance(raw, list):
            var_list = list()
            for i in range(len(raw)):
                element = raw[i]
                var = VarArray.generate_from_list(f'{call_name}[{i}]', f'{id_name}[{i}]', element, exp_slv)
                var_list.append(var)
            var = var_list[0]
            structure = [len(raw)]
            child_type = CBW.Var
            if isinstance(var, VarArray):
                structure = structure + var.structure
                child_type = CBW.VarArray
            var_array = VarArray(call_name, id_name, None, structure)
            var_array.var_list = var_list
            var_array.child_type = child_type
            return var_array
        else:
            colorPrint(f'unsupported args type:{type(raw)}')

    @staticmethod
    def deep_clone_and_rename(call_name, id_name, raw, exp_slv):
        if raw.type() == CBW.Var:
            var = Var(call_name, id_name, exp_slv)
            var.value = raw.value
            return var
        elif raw.type() == CBW.VarArray:
            var_list = list()
            i = 0
            for raw_var in raw.var_list:
                var = VarArray.deep_clone_and_rename(f'{call_name}{[i]}',
                                                     f'{id_name}{[i]}',
                                                     raw_var,
                                                     exp_slv)
                var_list.append(var)
                i += 1
            var_array = VarArray(call_name, id_name, var_list, None)
            var_array.structure = raw.structure
            if isinstance(var_list[0], Var):
                var_array.child_type = CBW.Var
            elif isinstance(var_list[0], VarArray):
                var_array.child_type = CBW.VarArray
            return var_array

    def __init__(self, call_name, id_name, var_list, structure):
        self.call_name = call_name
        self.id_name = id_name
        self.structure = structure
        if var_list is None:
            self.var_list = None
            self.child_type = None
        elif structure is None:
            self.var_list = var_list
            self.child_type = None
        elif len(structure) == 1:
            self.var_list = var_list
            self.child_type = CBW.Var
        else:
            self.var_list = list()
            self.child_type = CBW.VarArray
            next_structure = structure[1:]
            num = structure[0]
            step = int(len(var_list) / num)
            for i in range(num):
                next_var_list = var_list[step*i:step*i+step]
                next_call_name = f'{call_name}[{i}]'
                next_id_name = f'{id_name}[{i}]'
                child_Array = VarArray(next_call_name, next_id_name, next_var_list, next_structure)
                self.var_list.append(child_Array)


    def set_values(self, value_list):
        if self.child_type == CBW.Var:
            for i in range(len(value_list)):
                self.var_list[i].value = value_list[i]
        elif self.child_type == CBW.VarArray:
            for i in range(len(value_list)):
                self.var_list[i].set_values(value_list[i])

    def type(self):
        return CBW.VarArray

    def get_all_children(self):
        outcome = list()
        if self.child_type == CBW.Var:
            outcome = outcome + self.var_list
        elif self.child_type == CBW.VarArray:
            for subArray in self.var_list:
                outcome = outcome + subArray.get_all_children()
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

    def __repr__(self):
        result = ','.join(f'{child.id_name}' for child in self.var_list)
        return f'[{result}]'


    