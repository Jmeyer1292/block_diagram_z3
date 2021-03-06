from fbdplc.functions import Block, Program, Scope
from fbdplc.parts import MovePart, PartModel, PartPort, PortDirection
from fbdplc.wires import IdentConnection, NamedConnection, Wire, WireConnection
from fbdplc.graph import MemoryProxy, ScopeContext, merge_nets
from fbdplc.access import LiteralConstantAccess, SymbolAccess, SymbolConstantAccess

from typing import List
import logging
import z3
from z3.z3types import Z3Exception

logger = logging.getLogger(__name__)


class ProgramModel:
    def __init__(self, ctx=None):
        self.assertions = []
        self.ctx = ctx if ctx else z3.Context()
        # We need some kind of static call graph for users to write assertions against
        # or we need to accumulate annotations from the code itself.
        self.root: Scope = None
        self.global_mem = MemoryProxy('', self.ctx)


class MemoryAccessProxy:
    def __init__(self, name, scope):
        self.name, self.scope = name, scope

    def __str__(self):
        return f'MemoryAccessProxy({self.name} from {self.scope})'


def hunt_for_type(uid, code: ScopeContext, scope: Scope):
    result = None
    for wire_id, wire in code.wires.items():
        wire: Wire = wire
        # Test to see if wire endpoint 'a' is connecting to the part whose
        # type we wish to infer.
        a_matches = type(
            wire.a) == NamedConnection and wire.a.target_uid == uid
        b_matches = type(
            wire.b) == NamedConnection and wire.b.target_uid == uid

        if a_matches:
            if type(wire.b) == IdentConnection:
                access = code.accesses[wire.b.target_uid]
                logger.debug(f'\tOther end is a {access}')
                if isinstance(access, SymbolAccess) and access.scope == 'LocalVariable':
                    sort = scope.mem.sort(access.symbol)
                    logger.debug(f'\tSort determined to be {sort}')
                    return sort
        elif b_matches:
            if type(wire.a) == IdentConnection:
                access = code.accesses[wire.a.target_uid]
                logger.debug(f'\tOther end is a {access}')
                if isinstance(access, SymbolAccess) and access.scope == 'LocalVariable':
                    sort = scope.mem.sort(access.symbol)
                    logger.debug(f'\tSort determined to be {sort}')
                    return sort

    return result


def _model_block(program: Program, program_model: ProgramModel, block: Block, call_stack: List):
    ns = call_stack[-1].ns
    logger.info(f'Considering block {block.name} w/ call_stack {call_stack}')
    logger.info(f'This block has the following scope/namespace: {ns}')

    # A block consists of an ordered sequence of networks.
    # Each network could potentially call into other blocks, in which case the translator
    # recursively descends into them and generates a model.
    #
    # Each entity within a scope has a 'uid' associated with it. This uid is unique only to
    # the scope it is contained within.
    code = merge_nets(block.networks)

    logger.debug('--ACCESSES--')
    # NOTE(Jmeyer): No action should be necessary on these actions at this point in the analysis.
    # The variables they reference should have already been created.
    for uid, access in code.accesses.items():
        pass

    # Build a dictionary of instantiated parts
    callables = {}
    logger.debug('--PARTS--')
    for uid, part_template in code.parts.items():
        # TODO(Jmeyer): I need a more general way to signal that type inference is required. Right
        # now I've got one part that needs it, so we just check for that.
        if isinstance(part_template, MovePart):
            logger.debug(
                f'A part requiring type inference was detected: {part_template}')
            part_template.port_type = hunt_for_type(uid, code, call_stack[-1])
            assert part_template.port_type is not None, f'Type inference failed for {part_template}'

        model: PartModel = part_template.instantiate(ns, program_model.ctx)
        callables[uid] = model
        program_model.assertions.extend(model.assertions)

    # We can generate the logic for all of the primitives first
    # We can generate function call instances now too.
    logger.debug('--CALLS--')
    for uid, call in code.calls.items():
        if call.static_memory_access:
            logger.info(
                f'Consering call {call} w/ statics = "{call.static_memory_access}"')

        next_block = program.blocks[call.target]

        # The interface to a function call in THIS scope.
        # Acts as a sort of user defined "part" that can be connected to via ports like any of
        # the primitives.
        model = call.instantiate(
            f'{ns}:({uid})', program_model.ctx, next_block)
        callables[uid] = model

        # The act of calling a function creates a new scope in which the block variables
        # associated with that scope are available in the eval of the block and are also
        # connected to the input/output variables.
        new_scope = Scope(ns, uid, program_model.ctx,
                          next_block, call_stack[-1])
        new_scope.global_mem = call_stack[-1].global_mem
        if call.static_memory_access:
            new_scope.static_access_info = call.static_memory_access
        _model_block(program, program_model, next_block,
                     call_stack + [new_scope])
        link_assertions = new_scope.link_call(model)
        program_model.assertions.extend(link_assertions)

    # Then wire it all up.
    # The wires define the program execution order, so translation to something akin to SSA
    # should be a matter of following this though.
    logger.debug('--WIRES--')
    for uid, wire in code.wires.items():
        a_is_access = type(wire.a) == IdentConnection
        b_is_access = type(wire.b) == IdentConnection
        assert(not(a_is_access and b_is_access))

        # The general idea is that every endpoint is resolved to a model variable
        # When we're connecting ports, all we have to do is assert equality: The signal on the wire is the same at each end
        # When we connect to symbolic memory, however, things get more complicated:
        #   1. A symbol may be read from or written to multiple times.
        #   2. This program translates the input into a new program where each write creates a new variable
        def _resolve3(conn):
            assert(isinstance(conn, WireConnection))
            if isinstance(conn, IdentConnection):
                access = code.accesses[conn.target_uid]
                # 3 types of memory access right now:
                if isinstance(access, SymbolConstantAccess):
                    if access.scope == 'LocalConstant':
                        return MemoryAccessProxy(access.symbol, call_stack[-1])
                    else:
                        raise NotImplementedError(
                            f'Unhandled scope {access.scope} in Symbolic Constant Access')
                elif isinstance(access, LiteralConstantAccess):
                    return access.value
                elif isinstance(access, SymbolAccess):
                    if access.scope == 'LocalVariable':
                        local: Scope = call_stack[-1]
                        return MemoryAccessProxy(access.symbol, local)
                    elif access.scope == 'GlobalVariable':
                        return MemoryAccessProxy(access.symbol, program_model.global_mem)
                    else:
                        raise RuntimeError(
                            f'Unhandled access scope: {access.scope}')
                else:
                    raise RuntimeError(
                        f'Unhandled access type: {type(access)}')
            else:
                assert isinstance(conn, NamedConnection)
                part_iface: PartModel = callables[conn.target_uid]
                port = part_iface.ports[conn.target_port]
                return port

        a = _resolve3(wire.a)
        b = _resolve3(wire.b)

        write_to_a = a_is_access and b.direction == PortDirection.OUT
        write_to_b = b_is_access and a.direction == PortDirection.OUT
        has_write_to_mem = write_to_a or write_to_b

        def get_var(resolvable):
            if isinstance(resolvable, MemoryAccessProxy):
                scope = resolvable.scope
                return scope.read(resolvable.name)
            elif isinstance(resolvable, PartPort):
                return resolvable.external_var()
            else:
                return resolvable

        def get_writeable(resolvable):
            if isinstance(resolvable, MemoryAccessProxy):
                scope: Scope = resolvable.scope
                return scope.write(resolvable.name)
            else:
                return get_var(resolvable)

        if not has_write_to_mem:
            a_var = get_var(a)
            b_var = get_var(b)
            try:
                program_model.assertions.append(a_var == b_var)
            except Z3Exception:
                logger.error(
                    f'An exception occurred while assigning wires {a_var} of {type(a_var)} and {b_var} of {type(b_var)}')
                raise
        else:
            the_access = None
            the_port = None
            the_part = None
            if a_is_access:
                the_access = a
                the_port = b
                the_part: PartModel = callables[wire.b.target_uid]
                the_port_name = wire.b.target_port
            else:
                the_access = b
                the_port = a
                the_part: PartModel = callables[wire.a.target_uid]
                the_port_name = wire.a.target_port

            _prev = get_var(the_access)
            _next = get_writeable(the_access)
            other = get_var(the_port)
            program_model.assertions.append(_next == other)

            # NOTE(Jmeyer): This is an important step and an "oddity" in the code base: Functions
            # in this codebase must be pure, so pass-by-reference is translated into an output var
            # of the normal name and a *special* input parameter that takes the old value.
            old = f'_old_{the_port_name}'
            if old in the_part.ports:
                old_port = the_part.evar(old)
                a = _prev == old_port
                program_model.assertions.append(a)
            else:
                logger.debug(
                    f'Mem write does not have associated old part {old}, part: {the_part}')

    logger.info(f'Done w/ Block: {ns}')


def program_model(program: Program, context=None, global_memory=None):
    # Need to load the "main" entry point and start symbolically translating the program.
    main: Block = program.blocks[program.entry]

    program_model = ProgramModel(ctx=context)
    if global_memory:
        program_model.global_mem = global_memory

    call_stack = [Scope('', '', program_model.ctx, main)]
    program_model.root = call_stack[0]

    if main.block_type == Block.BLOCK_TYPE_FB:
        if program.entry_point_db:
            access = SymbolAccess('GlobalVariable', program.entry_point_db)
        else:
            # This clause supports building models without having to specify the (optional) static
            # memory locations. Most users should call this function via the project module which
            # will set all of this up in advance.
            for name, sort in main.variables.statics:
                program_model.global_mem.create('__main.' + name, sort)
            access = SymbolAccess('GlobalVariable', '__main')

        call_stack[-1].static_access_info = access

    call_stack[-1].global_mem = program_model.global_mem
    _model_block(program, program_model, main, call_stack)

    return program_model
