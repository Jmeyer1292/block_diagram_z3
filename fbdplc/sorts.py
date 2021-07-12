import typing
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

    def iterfields(self, prefix=''):
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
    if name in g_udt_archive:
        # TODO(Jmeyer): Cross check that the types are, in fact, the same
        print(f'Schema {name} is already in archive')
        return g_udt_archive[name]

    schema = UDTSchema(name)
    for key, value in parsed_schema.items():
        schema.fields[key] = value
    register_udt(name, schema)
    return schema


def register_udt(name, schema):
    g_udt_archive[name] = schema


SORT_LIKE = typing.Union[UDTSchema, Integer, Boolean, Time]


def is_primitive(sort: SORT_LIKE):
    return sort in SORT_MAP.values()


def children(sort: SORT_LIKE):
    if isinstance(sort, UDTSchema):
        return [(x, sort.fields[x]) for x in sort.fields]
    else:
        return []


def get_sort_factory(name):
    if name in SORT_MAP:
        return SORT_MAP[name]
    if name in g_udt_archive:
        return g_udt_archive[name]
    raise RuntimeError(f'Sort "{name}" not known')
