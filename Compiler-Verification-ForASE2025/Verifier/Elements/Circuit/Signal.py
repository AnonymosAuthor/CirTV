from enum import Enum

from Elements.Circuit.BuildinWords import CBW
from Tools.Check import *
from Elements.Circuit.Interfaces import *


class SignalTypes(Enum):
    Input = 'Input '
    Output = 'Output'
    Intermediate = 'Inter '


class Signal(SmtBuild, Type):
    total_num = 0

    def __init__(self, call_name, id_name, sym_name, signal_type, smt):
        TypeCheck(str, call_name)
        TypeCheck(str, id_name)
        EnumCheck(SignalTypes, signal_type)
        self.call_name = call_name
        self.id_name = id_name
        self.sym_name = sym_name
        self.signal_type = signal_type
        self.smt = smt
        Signal.total_num += 1

    def __str__(self):
        return f"{self.signal_type.value} signal {self.id_name}"

    def toSmt(self):
        return self.smt

    def type(self):
        return CBW.Signal

    def loc_sym_name(self, loc):
        self.sym_name = f'{loc}.{self.sym_name}'

    def __hash__(self):
        return hash(self.id_name)


'''
其实更好地应该使用一个同一的数组结构，但是现在积重难返了
'''


class SignalArray(Type):
    def __init__(self, call_name, id_name, signal_list, structure):
        self.call_name = call_name
        self.id_name = id_name
        self.structure = structure
        if structure is None:
            self.signal_list = signal_list
            self.child_type = None
        elif len(structure) == 1:
            self.signal_list = signal_list
            self.child_type = CBW.Signal
        else:
            self.signal_list = list()
            self.child_type = CBW.SignalArray
            next_structure = structure[1:]
            num = structure[0]
            step = int(len(signal_list) / num)
            for i in range(num):
                next_signal_list = signal_list[step*i:step*i+step]
                next_call_name = f'{call_name}[{i}]'
                next_id_name = f'{id_name}[{i}]'
                child_Array = SignalArray(next_call_name, next_id_name, next_signal_list, next_structure)
                self.signal_list.append(child_Array)

    def type(self):
        return CBW.SignalArray

    def get_all_children(self):
        outcome = list()
        if self.child_type == CBW.Signal:
            outcome = outcome + self.signal_list
        elif self.child_type == CBW.SignalArray:
            for subArray in self.signal_list:
                outcome = outcome + subArray.get_all_children()
        return outcome

    def __repr__(self):
        result = ','.join(f'{child.id_name}' for child in self.signal_list)
        return f'[{result}]'

    def toSmt(self):
        outcome = list()
        for item in self.signal_list:
            outcome.append(item.toSmt())
        return outcome
