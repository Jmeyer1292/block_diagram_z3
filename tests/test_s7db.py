import fbdplc.s7db


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
