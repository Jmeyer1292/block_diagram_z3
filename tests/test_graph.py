from z3.z3 import BitVec, BitVecSort
from fbdplc.sorts import Boolean, Integer, UDTSchema, make_schema
from fbdplc.graph import MemoryProxy
import z3


def test_mem():
    ctx = z3.Context()
    mem = MemoryProxy('', ctx)
    mem.create('foo', Boolean)

    assert 'foo' in mem.list_variables()
    assert len(mem.list_variables()) == 1

    ACCESS_COUNT_IDX = 0

    x1 = mem.write('foo')
    assert len(mem.list_variables()) == 1
    assert mem._sorts['foo'] == Boolean
    assert mem.data['foo'][ACCESS_COUNT_IDX] == 1

    x2 = mem.write('foo')
    assert mem.data['foo'][ACCESS_COUNT_IDX] == 2


def test_mem_udt():
    # Interface goals:
    # You should be able to create a UDT in memory and access it in a tree like fashion.
    point_schema = make_schema('Point', {'x': Integer, 'y': Integer})

    box_schema = make_schema('Box', {'min': point_schema, 'max': point_schema})

    ctx = z3.Context()
    mem = MemoryProxy('', ctx)

    # Create a point in memory
    mem.create2('foo.p0', point_schema)
    mem.create2('mybox', box_schema)

    x = mem.read('mybox')