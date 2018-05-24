
def get_parity(par):
    if str(par) == "odd": return 1
    else: return 0

def invert_parity(par):
    return int(par) ^ 1

def symbols_to_xor(init):
    constraints = {}
    xor_literals = [] 

    for atom in init.symbolic_atoms.by_signature("__parity",2):
        cid = atom.symbol.arguments[0].number
        par = atom.symbol.arguments[1].name
        constraints[cid] = {"parity": get_parity(par), "literals": set()}

    for atom in init.symbolic_atoms.by_signature("__parity",3):
        cid = atom.symbol.arguments[0].number
        lit = init.solver_literal(atom.literal)
        ass = init.assignment

        if ass.is_true(lit):
            constraints[cid]["parity"] = invert_parity(constraints[cid]["parity"])
        elif not ass.is_false(lit):
            literals = constraints[cid]["literals"]
            if lit in literals:
                literals.remove(lit)
            elif -lit in literals:
                literals.remove(-lit)
                constraints[cid]["parity"] = invert_parity(constraints[cid]["parity"])
            else:
                constraints[cid]["literals"].add(lit)
                if abs(lit) not in xor_literals:
                    xor_literals.append(abs(lit))
    return constraints, sorted(xor_literals)
