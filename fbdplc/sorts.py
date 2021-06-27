import z3


class Integer:
    @staticmethod
    def make(name: str, ctx: z3.Context):
        return z3.BitVec(name, 16, ctx=ctx)


class Boolean:
    @staticmethod
    def make(name: str, ctx: z3.Context):
        return z3.Bool(name, ctx=ctx)


class Time:
    @staticmethod
    def make(name: str, ctx: z3.Context):
        return z3.Int(name, ctx=ctx)

class AnyType:
    pass

# Primitives
SORT_MAP = {
    'Bool': Boolean,
    'Int': Integer,
    'Time': Time  # ???
}


class UserDefinedType:
    '''
    A struct that is composed of primitives or other data types that themselves
    are composed of primitives.

    No recursive data types are allowed.
    '''

    def __init__(self, name):
        self.name = name
        self.fields = []

    def flatten(self, name):
        variables = []
        for varname, vartype in self.fields:
            sort = SORT_MAP[vartype]
            qualified_name = name + '.' + varname
            variables.append((qualified_name, sort))
        return variables


    def __str__(self):
        return f'UserDataType({self.name})'
