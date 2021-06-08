
def namespace(ns : str , name : str):
    if len(ns) != 0:
        return ':'.join([ns, name])
    else:
        return name


