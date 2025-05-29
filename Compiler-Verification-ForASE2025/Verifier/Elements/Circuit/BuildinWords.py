from enum import Enum

# Circom Build in Words
class CBW(Enum):
    Input = 'Input'
    Output = 'Output'
    Intermediate = 'Intermediate'

    args = 'args'
    body = 'body'
    Signal = 'Signal'
    SignalArray = 'SignalArray'                     # 虽然SignalArray并不是内置关键字，但是为了方便，我们这里添加了一个
    InitializationBlock = 'InitializationBlock'
    Substitution = 'Substitution'                   # <-- <== =
    ConstraintEquality = 'ConstraintEquality'       # ===
    Block = 'Block'
    meta = 'meta'
    xtype = 'xtype'
    initializations = 'initializations'
    name = 'name'
    id = 'id'
    stmts = 'stmts'
    stmt = 'stmt'
    Declaration = 'Declaration'
    dimensions = 'dimensions'
    dimension = 'dimension'
    VarArray = 'VarArray'
    Var = 'Var'
    value = 'value'
    values = 'values'
    Component = 'Component'
    definitions = 'definitions'
    Template = 'Template'
    Function = 'Function'
    Return = 'Return'
    main_component = 'main_component'
    UniformArray = 'UniformArray'
    ArrayInLine = 'ArrayInLine'

    op = 'op'
    rhe = 'rhe'
    lhe = 'lhe'
    infix_op = 'infix_op'
    prefix_op = 'prefix_op'
    subbed_var = 'var'
    Call = 'Call'
    access = 'access'
    ComponentAccess = 'ComponentAccess'
    ArrayAccess = 'ArrayAccess'
    While = 'While'
    IfThenElse = 'IfThenElse'
    if_case = 'if_case'
    else_case = 'else_case'
    Assert = 'Assert'
    arg = 'arg'

    # item的类别
    Variable = 'Variable'
    Number = 'Number'
    InfixOp = 'InfixOp'
    PrefixOp = 'PrefixOp'
    InlineSwitchOp = 'InlineSwitchOp'       # 三目运算符

    cond = 'cond'
    if_true = 'if_true'
    if_false = 'if_false'


class OP(Enum):
    AssignVar = 'AssignVar'
    AssignConstraintSignal = 'AssignConstraintSignal'
    AssignSignal = 'AssignSignal'


# TypeReduction
class TR(Enum):
    Variable = 'Variable'
    Component = 'Component'
    Signal = 'Signal'
    Tag = 'Tag'


# ExpressionInfixOpcode
class EIO(Enum):
    Mul = 'Mul'
    Div = 'Div'
    Add = 'Add'
    Sub = 'Sub'
    Pow = 'Pow'
    IntDiv = 'IntDiv'
    Mod = 'Mod'
    ShiftL = 'ShiftL'
    ShiftR = 'ShiftR'
    LesserEq = 'LesserEq'
    GreaterEq = 'GreaterEq'
    Lesser = 'Lesser'
    Greater = 'Greater'
    Eq = 'Eq'
    NotEq = 'NotEq'
    BoolOr = 'BoolOr'
    BoolAnd = 'BoolAnd'
    BitOr = 'BitOr'
    BitAnd = 'BitAnd'
    BitXor = 'BitXor'


# ExpressionPrefixOpcode
class EPO(Enum):
    Sub = 'Sub'
    BoolNot = 'BoolNot'
    Complement = 'Complement'
    BitNot = 'BitNot'
