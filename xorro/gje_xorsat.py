from . import util
from itertools import chain
import clingo

class XOR:
    """
    A XOR constraint maintains the following invariants:
    1. there are at least two literals, and
    2. the first two literals are unassigned, or all literals are assigned and
       the first two literals have been assigned last on the same decision
       level.
    Furthermore, an index pointing to the literal after the literal assigned
    last is maintained. We start the search for the next unassigned literal
    from this point. This is important to get the amortized linear propagation
    time.
    """
    def __init__(self, id, literals):
        assert(len(literals) >= 2)
        self.__literals = literals
        self.__index = 2
        self.__id = id

    def __len__(self):
        return len(self.__literals)

    def __getitem__(self, idx):
        return self.__literals[idx]

    def __setitem__(self, idx, val):
        self.__literals[idx] = val
        return val

    def check(self, ass):
        if not sum(1 for lit in self if ass.is_true(lit)) % 2:
            return [lit if ass.is_true(lit) else -lit for lit in self]

    def __iter__(self):
        return iter(self.__literals)

    def reason(self, assignment):
        """
        If the constraint is unit resulting or conflicting returns a reason in
        form of a clause.
        """
        count, i = 0, None
        nogood = []
        for j in range(len(self)):
            if assignment.is_true(self[j]):
                nogood.append(self[j])
                count += 1
            elif assignment.is_false(self[j]):
                nogood.append(-self[j])
            elif assignment.value(self[j]) is None:
                i = j
        if i is not None:
            nogood.append(self[i] if count % 2 else -self[i])
        elif i is None and count %2 != 1:
            return nogood
        
        return None if assignment.is_true(nogood[-1]) else nogood

class XorSat_GJE:
    def __init__(self):
        self.__states  = []
        self.__binary  = []
        self.__basics  = []
        self.__tableau = []
        self.__sat = True
        self.__consequences = []
        self.__assignment = []
        self.__lits_to_propagate = []
        self.__display = False
        self.__literals = []

    def __add_watch(self, ctl, xor, i, thread_ids):
        """
        Adds a watch for the for the given index.
        """
        variable = abs(xor[i])
        ctl.add_watch( variable)
        ctl.add_watch(-variable)
        for thread_id in thread_ids:
            self.__states[thread_id].setdefault(variable, []).append((xor))

    def __add_basic(self, ctl, xor, thread_ids):
        """
        Adds the corresponding basic variable
        """
        for thread_id in thread_ids:
            j = 0
            for i in range(len(xor)):
                lit = xor[i]
                variable = abs(lit)
                #print(variable, ctl.assignment.value(variable))
                if ctl.assignment.value(variable) is None:
                    self.__basics[thread_id].setdefault(variable, []).append((xor))
                    #print("  Unassinged lit: %s"%variable)
                    j = i
                    break
            xor[j], xor[0] = xor[0], xor[j]
            if xor[j] < 0 and i != 0:
                xor[j], xor[0] = -xor[j], -xor[0]
            #elif j == 0:
            #    print("all assigned")
            #    self.__basics[thread_id].setdefault(abs(xor[0]), []).append((xor))

    def __reduce(self, constr1, constr2, display):
        ## Reduce
        reduced = False
        sat = True
        basic_1 = constr1[0]
        non_basic_1 = constr1[1:]
        parity_1 = 1
        if basic_1 < 0:
            parity_1 = 0
            basic_1 = -basic_1
        if display:
            print("  basic 1: %s, non basic: %s, parity: %s"%(basic_1,non_basic_1,parity_1))

        if basic_1 in constr2 or -basic_1 in constr2:
            if display:
                print("  reducing...")
            reduced = True
            parity_2 = 1
            if constr2[0] < 0:
                parity_2 = 0
                constr2[0] = -constr2[0]
            if display:
                print("  with %s, parity: %s"%(constr2,parity_2))
            constr2.remove(basic_1) ## Remove basic
            for lit in non_basic_1:
                if lit not in constr2:
                    constr2.append(lit)
                else:
                    constr2.remove(lit)
            parity_2 ^= parity_1 ## Update parity
            if parity_2 == 0:
                constr2[0] = -constr2[0]
            if display:
                print("  After reduce: %s, parity: %s"%(sorted(constr2), parity_2))
        else:
            if display:
                print("  Not reducing, basic literal %s is not in the XOR: %s"%(basic_1, constr2))
        if not constr2 and parity_2 == 1:
            sat = False
        return reduced, sat 

    def init(self, init):
        """
        Initializes xor constraints and watches based on the symbol table.
        Constraints of length zero and one are handled specially, to keep the
        implementation of the general constraints simple.
        """
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append({})
            self.__binary.append([])
            self.__basics.append({})
            #self.__tableau.append([]) ## This needs to work

        ret = util.symbols_to_xor_r(init.symbolic_atoms, util.default_get_lit(init))
        if ret is None:
            self.__sat = False
        else:
            constraints, facts = ret
            self.__consequences.extend(facts)

            ## First, check if exist constraints of size 2 and move them to the binary state
            ## Remove it (them) from the constraints list
            ## If still more than one XOR remains
            ## Reduce
            ## Check again the resultant XOR(s)

            #TODO.
            #All preprocessing
            #The new xor counter should be made from each literal and check the assignments.
            #The assignments list may have no purpose
            ##If there are no common variables, there is no need to make GJE. Send them to the other state
            
            ## If exist an XORs conjunction
            if len(constraints) > 1:
                ## Reduce
                for constr1 in constraints:
                    for constr2 in constraints:
                        if constr1 != constr2 and constr1 and constr2:
                            _, sat = self.__reduce(constr1, constr2, False)
                            if not sat:
                                self.__sat = False

                if self.__sat:
                    ## After reduce
                    k = 0
                    for i in range(len(constraints)):
                        ## Binary XORs
                        if len(constraints[i]) == 2:
                            if self.__display:
                                print("XOR ID: %s, %s"%(i, sorted(constraints[i])))
                            xor = XOR(0,list(sorted(constraints[i])))
                            self.__binary[thread_id].append(xor)            
                        ## Ternary or greater XORs
                        elif len(constraints[i]) > 2:         
                            self.__lits_to_propagate.append(len(constraints[i]))
                            if self.__display:
                                print("XOR ID: %s, %s"%(i, sorted(constraints[i])))
                            xor = XOR(k,sorted(constraints[i]))
                            k +=1
                            self.__tableau.append(xor)
                            self.__add_basic(init, xor, range(init.number_of_threads))
                            for j in range(len(constraints[i])):
                                self.__add_watch(init, xor, j, range(init.number_of_threads))
            ## Only one XOR exists
            elif len(constraints) == 1:
                if self.__display:
                    print("XOR ID: %s, %s"%(0, sorted(constraints[0])))
                xor = XOR(0,list(sorted(constraints[0])))
                self.__binary[thread_id].append(xor)   

        init.check_mode = clingo.PropagatorCheckMode.Fixpoint


        ## Add all literals... this must be removed afterwards. Just to double check that the assingments and undos are tracked correctly
        for xor in self.__tableau:
            if self.__display:
                print(xor._XOR__literals)
            for lit in xor._XOR__literals:
                if abs(lit) not in self.__literals:
                    self.__literals.append(abs(lit))
        
        if self.__display:
            print("")
            print("State: %s"%self.__states)
            print("")
            print("Lits per XOR: %s"%self.__lits_to_propagate)
            print("Binary XORs: %s"%self.__binary)
            print("Basics: %s"%self.__basics)
            print("Tableau: %s"%self.__tableau)
            print("Literals: %s"%sorted(self.__literals))
        

    def check(self, control):
        """
        Since the XOR constraint above handles only constraints with at least
        three literals, here the other two cases are handled.

        Empty conflicting constraints result in top-level conflicts and unit
        constraints will be propagated on the top-level.
        Additionally, XORs with two literals are handled via a lazy count approach
        """
        if control.assignment.decision_level == 0:
            if not self.__sat:
                control.add_clause([]) and control.propagate()
                return
            for lit in self.__consequences:
                if not control.add_clause([lit]) or not control.propagate():
                    return

        if control.assignment.is_total:
            state = self.__binary[control.thread_id]
            for xor in state:
                nogood = xor.check(control.assignment)
                if nogood is not None:
                    control.add_nogood(nogood) and control.propagate()
                    return
        
    def propagate(self, control, changes):
        """
        Propagates XOR constraints maintaining two watches per constraint.

        Generated conflicts are guaranteed to be asserting (have at least two
        literals from the current decision level).
        """
        state        = self.__states[control.thread_id]
        to_propagate = self.__lits_to_propagate
        assignment   = self.__assignment
        basics       = self.__basics[control.thread_id]
        tableau      = self.__tableau
        literals     = self.__literals
        if self.__display:
            print("\nState at beginning of propagate-----------------------------------------------------------------------------------------------------------------------------------------")
            #for key, value in state.items():
            #    __state = "%s: %s  "%(key, len(value))
            #    print(__state,end = '')
            #print("")
        for literal in changes: ## To keep the relationship between propagations and undos
            #print(changes)
            assignment.append(literal)
            variable = abs(literal)
            watches = state[variable]
            assert(len(watches) > 0)
            for i in range(len(watches)):
                if watches[i]:
                    xor = watches[i]
                    ## Reduce the counter from the XOR for each assigned literal
                    to_propagate[xor._XOR__id] -= 1
            
        for literal in changes:
            #print(changes)
            #assignment.append(literal)
            #print("add", assignment, literal)
            if self.__display:
                print("add %s"%literal)
                signed = 0
                #for lit in literals:
                #    if control.assignment.value(lit) is not None:
                #        signed +=1
                #print(" assignment: %s, %s of %s"%(sorted(assignment), len(self.__assignment), signed))
                #print(" basics: %s"%basics)
            variable = abs(literal)
            watches = state[variable]
            assert(len(watches) > 0)
            for i in range(len(watches)):
                if watches[i]:
                    xor = watches[i]
                    ## Reduce the counter from the XOR for each assigned literal
                    #to_propagate[xor._XOR__id] -= 1
                    #print(xor._XOR__id, to_propagate[xor._XOR__id])
                    assert to_propagate[xor._XOR__id] > -1,"Negative literals left to propagate"

                    #unass = 0
                    #for lit in xor._XOR__literals:
                    #    if control.assignment.value(lit) is None:
                    #        unass+=1
                    #if self.__display:
                    #    print("remaining in XOR %s: %s of %s"%(xor._XOR__id, to_propagate[xor._XOR__id], unass))
                    #to_propagate[xor._XOR__id] = unass
                    #if  to_propagate[xor._XOR__id] < 10:
                    #    print("XOR ID: %s, To propagate: %s _______________________________________________________"%(xor._XOR__id, to_propagate[xor._XOR__id]))
                    #    ## Double check the literals to propagate
                    #    print("left to propagate: %s"%unass)
                    
                    #if self.__display:
                    #    print(" XOR id: %s, literals: %s, to propagate: %s"%(xor._XOR__id, xor._XOR__literals, to_propagate[xor._XOR__id]))

                    ## The constraint is not unit, there are more literals to propagate and changes needs to be made
                    ## Check basic and non basic literals and perform substitutions if needed
                    if variable in basics and to_propagate[xor._XOR__id] > 1:
                        if self.__display:
                            print("  %s is a basic literal, perform swap"%variable)
                            print("  XOR before swap: %s"%xor._XOR__literals)
                            print("  basics before swap: %s"%basics)
                        basics[variable] = []
                        basics.pop(variable)
                        self.__add_basic(control, xor, (control.thread_id,))
                        if self.__display:
                            print("  swapped: %s"%xor._XOR__literals)
                            print("  basics after swap: %s"%basics)
                        ## Reduce
                        for constraint in tableau:
                            if xor != constraint:
                                prev_lits = [abs(lit) for lit in constraint._XOR__literals]
                                status, _ = self.__reduce(xor._XOR__literals, constraint._XOR__literals, self.__display)
                                if status:                                
                                    id = constraint._XOR__id
                                    if self.__display:
                                        #print("  Status: %s update counters and remove watches"%status)
                                        print("  Prev lits: %s"%prev_lits)
                                    for lit in prev_lits:
                                        state[lit].remove(constraint)
                                        if len(state[lit]) == 0:
                                            state.pop(lit)
                                    if self.__display:
                                        print("  New XOR: %s"%constraint._XOR__literals)
                                    ## Add new literals/watches to state
                                    unassigned = 0
                                    for i in range(len(constraint)):
                                        self.__add_watch(control, constraint, i, (control.thread_id,))
                                        if control.assignment.value(constraint[i]) is None:
                                            unassigned+=1
                                    to_propagate[id] = unassigned#len(constraint._XOR__literals)
                                    #if self.__display:
                                    #    print("   Updating number of unassigned literals")
                                    #assigned = 0
                                    #for lit in assignment:
                                    #    if lit in constraint._XOR__literals or -lit in constraint._XOR__literals:
                                    #        assigned +=1
                                    #to_propagate[id] = len(constraint._XOR__literals) - assigned
                                    #if self.__display:
                                    #    print("   Remaining: %s"%to_propagate[id])


                    # Here the constraint is either unit, satisfied, or conflicting. 
                    if to_propagate[xor._XOR__id] == 1 or to_propagate[xor._XOR__id] == 0:
                        #self.__display = True
                        if self.__display:
                            print("  XOR: %s, remaining: %s"%(xor._XOR__literals,to_propagate[xor._XOR__id]))
                            print("  propagate or conflict")
                        nogood = xor.reason(control.assignment)
                        if self.__display:
                            print("  nogood: %s"%nogood)
                        if nogood is not None:
                            if not control.add_nogood(nogood) or not control.propagate():
                                return
                    #else:
                    #    print("  XOR ID: %s, remaining: %s"%(xor._XOR__id,to_propagate[xor._XOR__id]))
                        #self.__display = False
            

    def undo(self, thread_id, assignment, changes):
        """
        Remove from assignment
        """
        state  = self.__states[thread_id]
        assign = self.__assignment
        to_propagate = self.__lits_to_propagate
        #removed = []
        for literal in changes:
            #if self.__display:
            #print("undo", assign, literal)
            #    removed.append(literal)
            #if literal in assign: ## This must be removed after fixing the state
            assign.remove(literal)
            variable = abs(literal)
            watches = state[variable]
            for i in range(len(watches)):
                xor = watches[i]
                to_propagate[xor._XOR__id] += 1

                #unass = 0
                #for lit in xor._XOR__literals:
                #    if assignment.value(lit) is None:
                #        unass+=1
                #to_propagate[xor._XOR__id] = unass
        #if self.__display:
        #    print("Removed literals: %s"%removed)
