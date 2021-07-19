from fbdplc.sorts import Boolean, Integer, UDTInstance, make_schema
from fbdplc.graph import MemoryProxy
import z3

ACCESS_COUNT_IDX = 0


def test_mem():
    ctx = z3.Context()
    mem = MemoryProxy('', ctx)
    mem.create('foo', Boolean)

    assert 'foo' in mem.list_variables()
    assert len(mem.list_variables()) == 1

    x1 = mem.write('foo')
    assert len(mem.list_variables()) == 1
    assert mem.sort('foo') == Boolean
    assert mem.data['foo'][ACCESS_COUNT_IDX] == 1

    x2 = mem.write('foo')
    assert mem.data['foo'][ACCESS_COUNT_IDX] == 2


def test_udt_creation():
    # Interface goals:
    # You should be able to create a UDT in memory and access it in a tree like fashion.
    point_schema = make_schema('Point', {'x': Integer, 'y': Integer})
    box_schema = make_schema('Box', {'min': point_schema, 'max': point_schema})

    ctx = z3.Context()
    mem = MemoryProxy('', ctx)

    mem.create('p0', point_schema)
    assert len(mem.data) == 2
    assert 'p0.x' in mem.data

    mem.create('p1', point_schema)
    assert len(mem.data) == 4

    mem.create('box', box_schema)
    assert len(mem.data) == 8
    assert 'box.min.x' in mem.data
    assert 'box.max.y' in mem.data


def test_udt_access():
    point_schema = make_schema('Point', {'x': Integer, 'y': Integer})

    ctx = z3.Context()
    mem = MemoryProxy('', ctx)

    mem.create('p0', point_schema)
    p0 = mem.read('p0')
    assert type(p0) == UDTInstance
    assert p0.schema == point_schema
    assert 'x' in p0.fields
    assert 'y' in p0.fields

    p0_x = mem.read('p0.x')
    assert p0_x is p0.fields['x']
    p0_y = mem.read('p0.y')
    assert p0_y is p0.fields['y']

    assert mem.data['p0.x'][ACCESS_COUNT_IDX] == 0
    assert mem.data['p0.y'][ACCESS_COUNT_IDX] == 0

    p0_1 = mem.write('p0')
    assert mem.data['p0.x'][ACCESS_COUNT_IDX] == 1
    assert mem.data['p0.y'][ACCESS_COUNT_IDX] == 1
