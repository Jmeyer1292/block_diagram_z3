from fbdplc.sorts import Boolean, Integer, UDTSchema, make_schema
from fbdplc.graph import MemoryProxy
import z3


def test_mem():
    ctx = z3.Context()
    mem = MemoryProxy('', ctx)
    mem.create('foo', Boolean)

    x = mem.read('foo')
    print(x, x.sort())

def test_mem_udt():
    schema = make_schema('Point', {'x': Integer, 'y': Integer})
    
    ctx = z3.Context()
    mem = MemoryProxy('SUPER_NESTED_CALL', ctx)
    mem.create('p0', schema)

    print(mem.data)
    print(mem._variables)

    proxy = mem.read('p0', 0, schema)
    print(proxy)
    print(proxy.fields)