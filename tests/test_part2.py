from fbdplc.parts import OrPart2
import z3

def test():
    or0 = OrPart2('or0')
    or0.negations.add('in1')
    
    z3_ctx = z3.Context()
    model = or0.instantiate('', z3_ctx)
    print(model.assertions)
    
    solver = z3.Solver(ctx=z3_ctx)
    for a in model.assertions:
        solver.add(a)
    
    print(solver)
    print(solver.check())