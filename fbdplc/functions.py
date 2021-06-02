from fbdplc.graph import ScopeContext
import enum

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
        inputs = ','.join([f'({s[0]}, {s[1]})' for s in self.input])
        return f'VarBlock({inputs})'
    
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

class Networks:
    pass

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
        self.variables = BlockVariables() # includes constants
        self.networks = []


