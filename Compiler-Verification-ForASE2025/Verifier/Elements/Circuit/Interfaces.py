from abc import ABC, abstractmethod


class SmtBuild(ABC):
    @abstractmethod
    def toSmt(self):
        pass


class Type(ABC):
    @abstractmethod
    def type(self):
        pass