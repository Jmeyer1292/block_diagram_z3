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

SORT_MAP = {
    'Bool': Boolean,
    'Int': Integer,
    'Time': Time # ???
}
