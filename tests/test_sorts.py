import fbdplc.sorts as sorts
import z3


def test():
    ctx = z3.Context()
    schema = sorts.make_schema('Point', {'x': sorts.Integer, 'y': sorts.Integer})
    p0 = schema.make('p0', ctx)
    p1 = schema.make('p1', ctx)
    expr = p0 == p1
    print(expr)

def test_iterfields():
    schema = sorts.make_schema('Point2', {'x': sorts.Integer, 'y': sorts.Integer})

    l = [(key, sort) for key, sort in schema.iterfields('foo.')]
    assert len(l) == 2
    print(l)