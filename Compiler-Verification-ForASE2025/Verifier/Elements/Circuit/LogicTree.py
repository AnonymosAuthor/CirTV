from cvc5 import Kind

from Convert.AdditionalOperations import ExpandedCVC5


class LogicNode:
    def __init__(self, parent, cond, exp_slv: ExpandedCVC5):
        self.parent = parent
        self.__exp_slv = exp_slv
        self.trueChild = None
        self.falseChild = None
        self.__exp = cond                   # 在上一个节点基础上添加的分支逻辑
        self.varCacheDict = dict()          # 变量缓存列表，如果一个变量被更新了，它会被存入这个缓存中，在调用这个值的时候，优先查缓存
        self.__detailCond = None            # 从根节点出发开始的所有逻辑条件

    def isRoot(self):
        return self.parent is None

    def setTrueChild(self, node):
        self.trueChild = node

    def setFalseChild(self, node):
        self.falseChild = node

    def getTrueChildDict(self):
        return self.trueChild.varCacheDict
    
    def getFalseChildDict(self):
        return self.falseChild.varCacheDict

    def getChildUpdatedVars(self):
        outcome = set()
        if self.trueChild is not None:
            outcome = outcome.union(self.trueChild.varCacheDict.keys())
        if self.falseChild is not None:
            outcome = outcome.union(self.falseChild.varCacheDict.keys())
        return outcome

    def isLeaf(self):
        return self.trueChild is None and self.falseChild is None            # list为空即为false

    def updateVar(self, varCallName, exp):    # 更新只更新自己当前的值
        self.varCacheDict[varCallName] = exp

    def getValue(self, varCallName):          # 递归一直找到根节点
        value = self.varCacheDict.get(varCallName, None)
        if value is not None:
            return value
        elif self.parent is None:
            return None
        else:
            return self.parent.getValue(varCallName)

    def getTotalCond(self):
        if self.__detailCond is not None:
            return self.__detailCond
        else:
            conds = list()
            current = self
            while current.parent is not None:
                conds.append(current.__exp)
                current = current.parent
            if len(conds) == 1:
                return conds[0]
            else:
                return self.__exp_slv.mkTerm(Kind.AND, *conds)

    def getAllUpdatedVar(self):             # 收集全部被更新过的Variable
        outcome = set()
        outcome = outcome.union(self.varCacheDict.keys())
        if self.trueChild is not None:
            outcome = outcome.union(self.trueChild.getAllUpdatedVar())
        if self.falseChild is not None:
            outcome = outcome.union(self.falseChild.getAllUpdatedVar())
        return outcome
