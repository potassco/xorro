#script (python)
## This xor propagator by preprocesing, identifies xor constraints of size 1 which are positive or negated facts. Add the corresponding rule. Not done!!!
## After that, all xor constraints of size 2 or greater are added to the state and watch two (both phases) literals.
## Proceed as normal, when propagating one watched literal, find if exist another unnassigned (not watched) literal to watch.
## If this fails, means that exist only one watched literal remaining to assign a truth value.
## **If a constraint is size 2, do not search for another unassigned literal and proceed to xor constraint propagation
## Proceed with unit propagation on xor constraint to get the corresponding nogood.

def invert_parity(par):
    return int(par)^1

def get_parity(par):
    if str(par) == "odd": return 1
    else: return 0

##########################################################################################################
class XOR:
    def __init__(self, literals, parity):
        #assert(len(literals) > 0)
        self.__literals = literals
        self.__parity = parity

    def __getitem__(self, idx):
        return self.__literals[idx]

    def propagate(self, assignment, unassigned):
        changeLit = False
        for i in range(2, len(self.__literals)):
            lit = self.__literals[i]
            value = assignment.value(lit)
            if value is None:
                changeLit = True
                temp = self.__literals[unassigned]
                self.__literals[unassigned] = lit
                self.__literals[i] = temp
                break

        return changeLit, unassigned

    def reason_unitpropagate(self, assignment):
        nogood = []
        parity = self.__parity
        unassigned = 0
        conflict = False
        count = 0
        for literal in self.__literals:
            if assignment.is_true(literal):
                nogood.append(literal)
                parity = invert_parity(parity)
                count +=1
            elif assignment.is_false(literal):
                nogood.append(-literal)
            else:
                unassigned = literal

        if unassigned != 0:
            if parity == 1: #UP
                nogood.append(-unassigned)
            else:
                nogood.append( unassigned)
                count+=1
        if count%2 != self.__parity:
            conflict = True
        return nogood, conflict

##########################################################################################################
class WatchesUnitPropagator:
    def __init__(self):
        self.__states  = []

    def __add_watch(self, ctl, xor, unassigned, thread_ids):
        if len(xor._XOR__literals) > 1:
            variable = abs(xor[unassigned])
        else:
            variable = 1
        for thread_id in thread_ids:
            ctl.add_watch( variable)
            ctl.add_watch(-variable)
            self.__states[thread_id].setdefault(variable, []).append((xor, unassigned))

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
            self.__add_watch(init, xor, 0, range(init.number_of_threads))
            if len(lits) > 1:
                self.__add_watch(init, xor, 1, range(init.number_of_threads))
        #print "state", self.__states

    def propagate(self, control, changes):
        state  = self.__states[control.thread_id]
        for literal in changes:
            variable = abs(literal)
            watch = state[variable]
            #assert(len(watch) > 0)
            state[variable] = []
            for xor, unassigned in watch:
                update_watch, unassigned = xor.propagate(control.assignment, unassigned)
                if update_watch:
                    self.__add_watch(control, xor, unassigned, (control.thread_id,))
                else:
                    state[variable].append((xor, unassigned))
                    ng, conflict = xor.reason_unitpropagate(control.assignment)
                    if conflict:
                        if not control.add_nogood(ng):
                            return

            if len(state[variable]) == 0:
                control.remove_watch( variable)
                control.remove_watch(-variable)
                state.pop(variable)
