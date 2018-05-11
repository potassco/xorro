#script (python)
## This xor propagator actually does not interfere with clasp's propagation...
## In fact we just check (count) the number of truth's assignments given by clasp respecting the parity given for each xor constraint
## In case of conflict, add the nogood and let clasp to propagate again

def get_parity(par):
    if str(par) == "odd": return 1
    else: return 0

def invert_parity(par):
    return int(par)^1    
	
##########################################################################################################
class XOR:
    def __init__(self, literals, parity):
        self.__literals = literals
        self.__parity = parity

    def __getitem__(self, idx):
        return self.__literals[idx]
    
class CountCheckPropagator:
    def __init__(self):
        self.__states = []

    def init(self, init):
        size = 0
        parities = []

        for atom in init.symbolic_atoms.by_signature("__parity",2):
	    p = int(str(get_parity(atom.symbol.arguments[1])))
            parities.append(p)
            size+=1
        
        lits = [[] for _ in range(size)]    
        for atom in init.symbolic_atoms.by_signature("__parity",3):            
            xor_id = int(str(atom.symbol.arguments[0]))
            lit = init.solver_literal(atom.literal)
            
            if lit == 1:				
		parities[xor_id]  = invert_parity(parities[xor_id])
	    elif lit > 1 and lit not in lits[xor_id]:
		lits[xor_id].append(lit)
            elif lit < -1 and abs(lit) not in lits[xor_id]:
                lits[xor_id].append(abs(lit))

        for i in range(len(parities)):
            for thread_id in range(len(self.__states), init.number_of_threads):
                self.__states.append({})
            #print lits[i], parities[i]
            xor = XOR(lits[i], parities[i])
            self.__states[thread_id].setdefault(i, []).append((xor))            
        #print self.__states

    def check(self, control):
        state = self.__states[control.thread_id]
        for id, xor in state.items():
            nogood     = []
            constraint = xor[0]._XOR__literals
            parity     = xor[0]._XOR__parity
            count      = 0

            for literal in constraint:
                if control.assignment.is_true(literal):
                    nogood.append(literal)
                    count+=1
                else:
                    nogood.append(-literal)
            if count % 2 != parity:
                if not control.add_nogood(nogood):
                    return
#end.
