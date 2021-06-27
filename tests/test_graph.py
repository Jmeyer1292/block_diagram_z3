from fbdplc.sorts import Boolean, Integer, UDTSchema, make_schema
from fbdplc.graph import MemoryProxy
import z3


def test_mem():
    ctx = z3.Context()
    mem = MemoryProxy('', ctx)
    mem.create('foo', Boolean)

    x = mem.read('foo')
    print(x, x.sort())

    x1 = mem.write('foo')
    print(x1, x1.sort())

    x2 = mem.write('foo')
    print(x2, x2.sort())

def test_mem_udt():
    schema = make_schema('Point', {'x': Integer, 'y': Integer})
    
    ctx = z3.Context()
    mem = MemoryProxy('SUPER_NESTED_CALL', ctx)
    mem.create('p0', schema)

    print(mem.data)
    print(mem._variables)

    proxy = mem.read('p0', 0, schema)
    print(proxy, proxy.fields)
    
    proxy1 = mem.write('p0', schema)
    print(proxy1, proxy1.fields)
    