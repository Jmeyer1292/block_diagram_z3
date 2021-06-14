'''
Edges in a block diagram computational graph. The edges themselves don't have direction,
but the ports that they attach to may.
'''


class WireConnection:
    pass


class NamedConnection(WireConnection):
    def __init__(self, target_uid: int, target_port: str):
        self.target_uid = target_uid
        self.target_port = target_port

    def __str__(self):
        return f'NamedConnection(id={self.target_uid}, port={self.target_port})'


class IdentConnection(WireConnection):
    def __init__(self, target_uid: int):
        self.target_uid = target_uid

    def __str__(self):
        return f'IdentConnection(id={self.target_uid})'


class Wire:
    '''
    Wires in TIA's S7 XML format can have more than two terminals, but we always decompose them
    into a series of two terminal blocks.
    '''

    def __init__(self, a: WireConnection, b: WireConnection):
        self.a = a
        self.b = b
