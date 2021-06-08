from fbdplc.parts import OrPart
import z3

def test():
    or0 = OrPart('or0', 2)
    
    z3_ctx = z3.Context()
    model = or0.instantiate('', z3_ctx)
    print(model.assertions)
    
    solver = z3.Solver(ctx=z3_ctx)
    for a in model.assertions:
        solver.add(a)
    
    print(solver)
    result = solver.check(model.evar('in1') == True, model.evar('in2') == False)
    assert(result == z3.sat)
    assert(solver.model().eval(model.evar('out')) == True)