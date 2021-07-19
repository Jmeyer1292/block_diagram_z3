import fbdplc.s7db
import pprint


def test_example0():
    parsed = fbdplc.s7db.parse_db_file('testdata/db/example0.db')

    assert 'name' in parsed
    assert 'symbols' in parsed

    assert parsed['name'] == '"DebugData"'
    symbols = parsed['symbols']

    assert len(symbols) == 3

    for s in symbols:
        assert 'name' in symbols[s]
        assert 'type' in symbols[s]

    assert 'source' in parsed['initializers']
    assert parsed['initializers']['source'] == '1'


def test_udt():
    parsed = fbdplc.s7db.parse_udt_file(
        'testdata/udt_project/PLC_1/PLC data types/Box.udt')

    assert 'name' in parsed
    assert 'symbols' in parsed

    assert parsed['name'] == '"Box"'
    symbols = parsed['symbols']

    assert len(symbols) == 2
    assert 'min' in symbols
    assert 'max' in symbols


def test_udt_array_with_defaults():
    '''
    Parses a data structure with an array with declared defaults like so:
    v : Array[0..15] of Bool := [false, true];
    '''
    parsed = fbdplc.s7db.parse_udt_file('testdata/udt/ArrayWithDefault.udt')


def test_udt_polygon():
    '''
    A composite of an integer and an array of UDT
    '''
    parsed = fbdplc.s7db.parse_udt_file('testdata/udt/Polygon.udt')


def test_udt_points():
    '''
    Two simple data structures of template<typename T> { x: T, y: T} where T in {Real, Int}
    '''
    parsed_f = fbdplc.s7db.parse_udt_file('testdata/udt/Pointf.udt')
    parsed_i = fbdplc.s7db.parse_udt_file('testdata/udt/Pointi.udt')


def test_udt_nested_anon():
    '''
    A data structure with two nested anonymous data structures
    '''
    parsed = fbdplc.s7db.parse_udt_file('testdata/udt/AnonStruct.udt')


def test_db_anon():
    parsed = fbdplc.s7db.parse_db_file('testdata/db/AnonTestDB.db')


def test_db_polygon():
    '''
    The structure of a DB can be adhoc but it can also be derived from a user defined type.
    This example contains a DB mapped to the "Polygon" type (defined in "testdata/udt/Polygon.udt")
    and also has a couple of special initializers. TODO(Jmeyer): Support for the init statements.
    '''
    parsed = fbdplc.s7db.parse_db_file('testdata/db/PolygonDB.db')
