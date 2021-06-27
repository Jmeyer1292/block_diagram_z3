from fbdplc.sorts import Boolean, Integer, Time
import z3
from typing import Dict
from fbdplc.utils import namespace
from enum import Enum


class PortDirection(Enum):
    IN = 1
    OUT = 2


class PartPort:
    # Siemens appears to associate the "negation" of a boolean
    # signal not with a separate, NOT gate but instead with a
    # given part port.

    # I'm going to try to stay consistent for the moment, so some
    # ports may have 2 variables internally.

    def __init__(self, name: str, port_type: type, direction: PortDirection):
        self.name = name
        self.port_type = port_type
        self.direction = direction
        self.is_negated = False
        # internal & external variables
        self._var = None
        self._negated = None

    def instantiate(self, ctx: z3.Context):
        if self.port_type == Boolean:
            self._var = Boolean.make(self.name, ctx=ctx)
        elif self.port_type == Integer:
            self._var = Integer.make(self.name, ctx=ctx)
        elif self.port_type == Time:
            self._var = Time.make(self.name, ctx=ctx)
        else:
            raise NotImplementedError(
                f'Cannot instantiate port {self.name} of type {self.port_type} as this type is not yet implemented')

        if self.is_negated:
            assert self.port_type == Boolean, "Can only negate a boolean port"
            self._negated = Boolean.make(self.name + '__neg', ctx=ctx)

    def set_negated(self):
        if self.port_type != Boolean:
            raise RuntimeError(f"Can't negate a port of type {self.port_type}")
        if self._negated is not None:
            raise RuntimeError(f'Port {self.name} already negated')

        self.is_negated = True

    def internal_var(self):
        if self._negated is None:
            return self._var
        else:
            return self._negated if self.direction == PortDirection.IN else self._var

    def external_var(self):
        if self._negated is None:
            return self._var
        else:
            return self._var if self.direction == PortDirection.IN else self._negated

    def model(self):
        if self._negated is None:
            return []
        else:
            return [self._negated == z3.Not(self._var)]


class PartModel:
    def __init__(self, name):
        self.name = name
        self.assertions = []
        self.ports: Dict[str, PartPort] = {}

    def add_port(self, name: str, port_type: type, dir: PortDirection):
        self.ports[name] = PartPort(namespace(self.name, name), port_type, dir)

    def instantiate_ports(self, context: z3.Context):
        model = []
        for p in self.ports.values():
            p.instantiate(context)
            port_model = p.model()
            model.extend(port_model)
        self.assertions.extend(model)

    def ivar(self, port_name: str):
        return self.ports[port_name].internal_var()

    def evar(self, port_name: str):
        return self.ports[port_name].external_var()


class PartTemplate:
    def __init__(self, name: str):
        self.name = name
        self.negations = set()

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        ''' Returns a unique program model '''
        raise NotImplementedError()

    def add_negation(self, port_name: str):
        self.negations.add(port_name)


class OrPart(PartTemplate):
    def __init__(self, name, n: int):
        super().__init__(name)
        self.dimension = n

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        for i in range(1, self.dimension + 1):
            model.add_port(f'in{i}', Boolean, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        or_expr = z3.Or([model.ivar(f'in{i}')
                        for i in range(1, self.dimension + 1)])

        model.assertions.append(or_expr == model.ivar('out'))
        return model


class AndPart(PartTemplate):
    def __init__(self, name, n: int):
        super().__init__(name)
        self.dimension = n

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        for i in range(1, self.dimension + 1):
            model.add_port(f'in{i}', Boolean, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        and_expr = z3.And([model.ivar(f'in{i}')
                          for i in range(1, self.dimension + 1)])
        model.assertions.append(and_expr == model.ivar('out'))
        return model


class CoilPart(PartTemplate):
    def __init__(self, name, port_type=Boolean, coil_type: str = 'Coil'):
        super().__init__(name)
        self.coil_type = coil_type
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in', self.port_type, PortDirection.IN)
        model.add_port('operand', self.port_type, PortDirection.OUT)
        model.add_port('out', self.port_type, PortDirection.OUT)
        model.add_port('_old_operand', self.port_type, PortDirection.IN)
        for p in self.negations:
            model.ports[p].set_negated()
        model.instantiate_ports(context)

        logic = z3.And(self._internal_model(model),
                       model.ivar('in') == model.ivar('out'))
        model.assertions.append(logic)

        return model

    def _internal_model(self, model: PartModel):
        # So a normal coil is just
        #   in == operand
        if self.coil_type == 'Coil':
            return model.ivar('in') == model.ivar('operand')

        if self.coil_type == 'SCoil':
            return z3.If(model.ivar('in'), model.ivar('operand') == True, model.ivar('operand') == model.ivar('_old_operand'))

        if self.coil_type == 'RCoil':
            return z3.If(model.ivar('in'), model.ivar('operand') == False, model.ivar('operand') == model.ivar('_old_operand'))

        raise RuntimeError('Unknown coil type {}'.format(self.coil_type))


class AddPart(PartTemplate):
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in1', self.port_type, PortDirection.IN)
        model.add_port('in2', self.port_type, PortDirection.IN)
        model.add_port('out', self.port_type, PortDirection.OUT)
        model.instantiate_ports(context)

        logic = model.ivar('out') == (model.ivar('in1') + model.ivar('in2'))
        model.assertions.append(logic)

        return model


class GreaterThanOrEqualPart(PartTemplate):
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in1', self.port_type, PortDirection.IN)
        model.add_port('in2', self.port_type, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        logic = model.ivar('out') == (model.ivar('in1') >= model.ivar('in2'))
        model.assertions.append(logic)

        return model


class GreaterThanPart(PartTemplate):
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in1', self.port_type, PortDirection.IN)
        model.add_port('in2', self.port_type, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        logic = model.ivar('out') == (model.ivar('in1') > model.ivar('in2'))
        model.assertions.append(logic)

        return model


class LessThanOrEqualPart(PartTemplate):
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in1', self.port_type, PortDirection.IN)
        model.add_port('in2', self.port_type, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        logic = model.ivar('out') == (model.ivar('in1') <= model.ivar('in2'))
        model.assertions.append(logic)

        return model


class LessThanPart(PartTemplate):
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in1', self.port_type, PortDirection.IN)
        model.add_port('in2', self.port_type, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        logic = model.ivar('out') == (model.ivar('in1') < model.ivar('in2'))
        model.assertions.append(logic)

        return model


class PTriggerPart(PartTemplate):
    def __init__(self, name):
        super().__init__(name)

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in', Boolean, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        model.add_port('_old_bit', Boolean, PortDirection.IN)
        model.add_port('bit', Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        save_input_logic = model.ivar('in') == model.ivar('bit')
        compute_edge_logic = z3.And(model.ivar('in'), z3.Not(
            model.ivar('_old_bit'))) == model.ivar('out')

        model.assertions.append(save_input_logic)
        model.assertions.append(compute_edge_logic)

        return model


class NTriggerPart(PartTemplate):
    def __init__(self, name):
        super().__init__(name)

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)
        model.add_port('in', Boolean, PortDirection.IN)
        model.add_port('out', Boolean, PortDirection.OUT)
        model.add_port('_old_bit', Boolean, PortDirection.IN)
        model.add_port('bit', Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        save_input_logic = model.ivar('in') == model.ivar('bit')
        compute_edge_logic = z3.And(z3.Not(model.ivar('in')),
                                    model.ivar('_old_bit')) == model.ivar('out')

        model.assertions.append(save_input_logic)
        model.assertions.append(compute_edge_logic)

        return model


class WordToBitsPart(PartTemplate):
    # TODO(Jmeyer): Support alternate word sizes?
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)

        model.add_port('IN', self.port_type, PortDirection.IN)
        for i in range(16):
            n = f'OUT{i}'
            model.add_port(n, Boolean, PortDirection.OUT)
        model.instantiate_ports(context)

        logic = []
        for i in range(16):
            n = f'OUT{i}'
            l = model.ivar(n) == (z3.Extract(i, i, model.ivar('IN')) == 1)
            logic.append(l)

        model.assertions.append(z3.And(logic))
        return model


class BitsToWordPart(PartTemplate):
    # TODO(Jmeyer): Support alternate word sizes?
    def __init__(self, name, port_type):
        super().__init__(name)
        self.port_type = port_type

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)

        model.add_port('OUT', self.port_type, PortDirection.OUT)
        for i in range(16):
            n = f'IN{i}'
            model.add_port(n, Boolean, PortDirection.IN)
        model.instantiate_ports(context)

        logic = []
        for i in range(16):
            n = f'IN{i}'
            l = model.ivar(n) == (z3.Extract(i, i, model.ivar('OUT')) == 1)
            logic.append(l)

        model.assertions.append(z3.And(logic))
        return model


class TOnPart(PartTemplate):
    def __init__(self, name):
        # TODO(Jmeyer): Support custom or different time types?
        super().__init__(name)

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)

        model.add_port('IN', Boolean, PortDirection.IN)
        model.add_port('Q', Boolean, PortDirection.OUT)
        model.add_port('PT', Time, PortDirection.IN)
        model.add_port('ET', Time, PortDirection.OUT)
        # How do we interact with this part for the purposes of analysis?
        model.add_port('__elapsed', Boolean, PortDirection.IN)

        model.instantiate_ports(context)

        logic = z3.And(model.ivar('IN'), model.ivar(
            '__elapsed')) == model.ivar('Q')
        model.assertions.append(logic)
        return model


class TOfPart(PartTemplate):
    def __init__(self, name):
        # TODO(Jmeyer): Support custom or different time types?
        super().__init__(name)

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)

        model.add_port('IN', Boolean, PortDirection.IN)
        model.add_port('Q', Boolean, PortDirection.OUT)
        model.add_port('PT', Time, PortDirection.IN)
        model.add_port('ET', Time, PortDirection.OUT)
        # How do we interact with this part for the purposes of analysis?
        model.add_port('__elapsed', Boolean, PortDirection.IN)

        model.instantiate_ports(context)

        logic = z3.Or(model.ivar('IN'), model.ivar(
            '__elapsed')) == model.ivar('Q')
        model.assertions.append(logic)
        return model


class AckGlobalPart(PartTemplate):
    # TODO How do we represent the global ack state?
    def __init__(self, name):
        super().__init__(name)

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)

        model.add_port('ACK_GLOB', Boolean, PortDirection.IN)
        model.add_port('en', Boolean, PortDirection.IN)

        model.instantiate_ports(context)
        # TODO(Jmeyer): Logic?
        return model


class MovePart(PartTemplate):
    # TODO The XML doesn't directly tell you what the types are here. We need to go
    # and figure them out.
    def __init__(self, name):
        # TODO(Jmeyer): Support custom or different time types?
        super().__init__(name)

    def instantiate(self, ns, context: z3.Context) -> PartModel:
        instance_name = namespace(ns, self.name)
        model = PartModel(instance_name)

        model.add_port('in', Boolean, PortDirection.IN)
        model.add_port('out1', Boolean, PortDirection.OUT)

        model.instantiate_ports(context)
        # TODO(Jmeyer): Logic?
        return model
