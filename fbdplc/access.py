'''
TODO(Jmeyer): All of these probably need namespaces, type info
and all kinds of other stuff to be useful.

We need to be able to find the data these access after processing
the entire program and verify that the accesses are correct.

Correct could mean a few things, but certainly the variable
needs to exist and it needs to have the right type.
'''


class Access:
    ''' Represents a memory access of some sort '''
    pass


class SymbolAccess(Access):
    def __init__(self, scope, symbol: str):
        self.scope = scope
        self.symbol = symbol
    
    def __str__(self):
        return f'SymbolAccess("{self.symbol}", scope={self.scope})'


class SymbolConstantAccess(Access):
    def __init__(self, scope, symbol: str):
        self.scope = scope
        self.symbol = symbol
    def __str__(self):
        return f'SymbolConstantAccess("{self.symbol}")'

class LiteralConstantAccess(Access):
    def __init__(self, value):
        self.value = value
        self.ltype = type(value)
    def __str__(self):
        return f'LiteralAccess({self.ltype}({self.value}))'