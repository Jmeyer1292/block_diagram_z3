'''
Edges
'''


class WireConnection:
    pass

class NamedConnection(WireConnection):
    def __init__(self, target_uid:int , target_port : str):
        self.target_uid = target_uid
        self.target_port = target_port
    
    def resolve(self, context:ScopeContext):
        return context.parts[self.target_uid].resolve(self.target_port)

class IdentConnection(WireConnection):
    def __init__(self, target_uid:int):
        self.target_uid = target_uid
    
    def resolve(self, context : ScopeContext):
        return context.accesses[self.target_uid]

def resolve(conn: WireConnection, context :ScopeContext):
    if type(conn) == NamedConnection:
        return context.parts[conn.target_uid].port(conn.target_port)
    else:
        return context.accesses[conn.target_uid]

class Wire:
    def __init__(self, a, b):
        self.a = a
        self.b = b
