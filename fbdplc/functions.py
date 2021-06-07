from fbdplc.utils import namespace
from fbdplc.parts import Part, PartPort, PortDirection
from typing import Dict
from fbdplc.graph import ScopeContext
import enum


class Program:
    def __init__(self, title: str):
        self.title = title
        self.blocks = {}
        self.entry = 'main'


class Section(enum.Enum):
    INPUT = 0
    OUTPUT = 1
    INOUT = 2
    TEMP = 3
    CONSTANT = 4
    RETURN = 5


class BlockVariables:
    def __init__(self):
        self.input = []
        self.output = []
        self.inout = []
        self.temp = []
        self.constant = []
        self.ret = []

    def __str__(self):
        input = ','.join([f'({s[0]}, {s[1]})' for s in self.input])
        output = ','.join([f'({s[0]}, {s[1]})' for s in self.output])
        inout = ','.join([f'({s[0]}, {s[1]})' for s in self.inout])
        temp = ','.join([f'({s[0]}, {s[1]})' for s in self.temp])
        constant = ','.join([f'({s[0]}, {s[1]})' for s in self.constant])
        ret = ','.join([f'({s[0]}, {s[1]})' for s in self.ret])

        return f'VarBlock(\n\tinputs={input}\n\toutput={output}\n\tinout={inout}\n\ttemp={temp}\n\tconstant={constant}\n\tret={ret}\n)'

    def add(self, section: Section, name: str, datatype: type):
        data_section = None
        if section == Section.INPUT:
            data_section = self.input
        elif section == Section.OUTPUT:
            data_section = self.output
        elif section == Section.INOUT:
            data_section = self.inout
        elif section == Section.TEMP:
            data_section = self.temp
        elif section == Section.CONSTANT:
            data_section == self.constant
        elif section == Section.RETURN:
            data_section = self.ret
            assert(len(self.ret) == 0)
        else:
            raise RuntimeError(f'Unrecognized section enum {section}')
        data_section.append((name, datatype))


class Block:
    '''
    In Siemens land, a block is sort of akin to a class.
    FB blocks have state associated with them.
    FC blocks are stateless; a sort of general function call.
    '''

    def __init__(self, name: str):
        pass
        # A function block has a name
        # It has an interface which tracks what variables we have.
        #  Section = Input | Output | InOut | Temp | Constant | Return
        #
        # where each section is composed of 0+ "Members"
        #  Member = (Name, Datatype)
        self.name = name
        self.variables = BlockVariables()  # includes constants
        self.networks = []


class Call(Part):
    def __init__(self, target: str):
        super().__init__(target)
        self.target = target
        # The data structure also has info about the block type
        # and each of the parameters. Is this redundant with the
        # info in the associated call?
        self.ports: Dict[str, PartPort] = {}
        # A unique identifer for this particularly call. Needs to be statically determinable. No recursion.
        # self._block = block
        
        # # Need to allocate ports
        # for v in self._block.variables.input:
        #     self._add_port(v[0], v[1], PortDirection.IN)
        # for v in self._block.variables.output:
        #     self._add_port(v[0], v[1], PortDirection.OUT)
        # for v in self._block.variables.inout:
        #     self._add_port(v[0], v[1], PortDirection.OUT)
        
