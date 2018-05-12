#script (python)
## This xor propagator by preprocesing, identifies xor constraints of size 1 which are positive or negated facts. Add the corresponding rule. Not done!!!
## After that, all xor constraints of size 2 or greater are added to the state and watch two (both phases) literals.
## Proceed as normal, when propagating one watched literal, find if exist another unnassigned (not watched) literal to watch.
## If this fails, means that exist only one watched literal remaining to assign a truth value.
## **If a constraint is size 2, do not search for another unassigned literal and proceed to xor constraint propagation
## Proceed with unit propagation on xor constraint to get the corresponding nogood.

from . import util

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
                parity = util.invert_parity(parity)
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
        constraints = util.symbols_to_xor(init)

        for constraint in constraints.values():
            for thread_id in range(len(self.__states), init.number_of_threads):
                self.__states.append({})
            xor = XOR(list(sorted(constraint["literals"])), constraint["parity"])
            self.__add_watch(init, xor, 0, range(init.number_of_threads))

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
