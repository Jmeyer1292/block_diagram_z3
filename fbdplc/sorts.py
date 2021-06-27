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


class UDTSchema:
    def __init__(self, name: str):
        self.name = name
        self.fields = {}

    def __str__(self):
        return f'UDTSchema({self.name})'
    
    def make(self, name: str, ctx: z3.Context):
        instance = UDTInstance(self)
        for key, value in self.fields.items():
            n = name + '.' + key
            instance.fields[key] = value.make(n, ctx=ctx)
        return instance
    
    def iterfields(self, prefix = ''):
        for n, v in self.fields.items():
            if isinstance(v, UDTSchema):
                for _x in v.iterfields(n + '.'):
                    yield _x
            else:
                yield (prefix + n, v)


class UDTInstance:
    def __init__(self, schema: UDTSchema):
        self.schema = schema
        self.fields = {}

    def __str__(self):
        return f'UDTInstance({self.schema.name})'

    def __eq__(self, other):
        if self.schema.name != other.schema.name:
            raise RuntimeError(
                f'Can not equate UDTs of different schema {self.schema} vs {other.schema}')
        
        exprs = []
        for name, value in self.fields.items():
            other_value = other.fields[name]
            exprs.append(value == other_value)
        return z3.And(exprs)
    
    def field(self, name: str):
        return self.fields[name]


g_udt_archive = {}


def in_archive(sort):
    if not isinstance(sort, UDTSchema):
        return False
    else:
        return sort.name in g_udt_archive

def make_schema(name, parsed_schema):
    schema = UDTSchema(name)
    for key, value in parsed_schema.items():
        schema.fields[key] = value
    g_udt_archive[name] = schema
    return schema