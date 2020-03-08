from . import util
from itertools import chain
import clingo
import copy ## Remove
import timeit ## Remove

def propagate_implications(constraints, facts):
    #print "constraints", constraints, "-----------"
    for lit in facts:
        #print "UP on literal", lit
        for constraint in constraints:
            if constraint:
                #print "  constraint ", constraint
                #print "    Check lit ", lit, "in constraint", constraint
                if lit in constraint:
                    constraint.remove(lit)
                    #print "      Remove lit %s, new constraint %s"%(lit, constraint)
                    if constraint:# and lit < 0:
                        constraint[0] = -constraint[0]## Keep the even parity
                elif -lit in constraint:
                    constraint.remove(-lit)
                    #print "      Remove lit %s, new constraint %s"%(-lit, constraint)

                ## Check for new implications after each propagated literal
                if len(constraint) == 1: ## New implication
                    #print "  New implication ", constraint
                    if constraint[0] not in facts:
                        facts.append(constraint[0])
                    constraint.remove(constraint[0])
                    #print "updated facts", facts

    return [x for x in constraints if x], facts

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
    def __init__(self, literals):
        assert(len(literals) >= 2)
        self.__literals = literals
        self.__index = 2

    def __len__(self):
        return len(self.__literals)

    def __getitem__(self, idx):
        return self.__literals[idx]

    def __setitem__(self, idx, val):
        self.__literals[idx] = val
        return val

    def propagate(self, assignment, i):
        """
        Propagates the given assigned index.

        If an unwatched unassigned literal is found, the literals are
        rearranged so that the given index points to it. The function returns
        true if an such a literal is found.
        """
        assert(i < 2)
        for j in chain(range(self.__index, len(self)), range(2, self.__index)):
            if assignment.value(self[j]) is None:
                self.__index = j + 1 if j + 1 < len(self) else 2
                self[i], self[j] = self[j], self[i]
                return True
        return False

    def reason(self, assignment, i, display):
        """
        If the constraint is unit resulting or conflicting returns a reason in
        form of a clause.
        """
        # Switch to the index of the other watched literal that is either
        # unassigned and has to be propagated or has to be checked for a
        # conflict. In the second case it was assigned on the same level as the
        # propagated literal.
        if display:
            print("   reason")
        i = 1 - i
        count = 0
        nogood = []
        conflict = False
        for j in range(len(self)):
            if display:
                print("   lit %s: %s"%(abs(self[j]), assignment.value(abs(self[j]))))
            if i == j:
                continue
            if assignment.is_true(self[j]):
                nogood.append(self[j])
                count += 1
            else:
                nogood.append(-self[j])

        #if display:
        #    print "   ", count, nogood, self[i] if count % 2 else -self[i]
        ## If clause (constraint) already satisfied by the count % 2, append the unnasigned literal as negative
        ## Else, if clause is not satisfied, append the unnasigned literal as positive
        nogood.append(self[i] if count % 2 else -self[i])

        ## Return None if the appended unnasigned literal in clause is true. This means that the clause is satisfied and no need to return a reason
        ## Else, the unnasigned literal in clause is false, meaning that a clause must be given as a reason
        return nogood if assignment.is_true(nogood[-1]) else None

class UPExtendedPropagator:
    def __init__(self):
        self.__states  = []
        self.__sat = True
        self.__consequences = []
        self.__xors = []
        self.__lits = []
        self.__extended = False ## If more than one constraint remains, if not, it is just more overhead
        self.__preprocess = False ## new feature
        self.__feature = False ## new feature
        self.__display = False ## Display for debugging
        self.__display_ = False ## Display number of propagatons and undos
        self.__propagations = 0
        self.__undos = 0

    def __extended_propagation(self, assignment, xor):
        starttime = timeit.default_timer()
        constraints = copy.deepcopy(self.__xors[:])
        constraints.remove(xor)
        if self.__display:
            print("    deep copy time     : %.10f"%(timeit.default_timer() - starttime))

        starttime = timeit.default_timer()
        constraints = []
        for constr in self.__xors:
            if constr != xor:
                constraints.append(constr[:])
        if self.__display:
            print("    sublist slice time : %.10f"%(timeit.default_timer() - starttime))
        
        literals = self.__lits[:]
        clause = []
        facts_  = []
        facts  = []
        implications = []
        ## Get facts
        for lit in literals:
            if assignment.is_true(lit):
                facts.append( lit)
                facts_.append( lit)
            elif assignment.is_false(lit):
                facts.append(-lit)
                facts_.append(-lit)

        if self.__display:
            print("    constraints: %s"%constraints)
            print("    facts: %s"%facts)

        if facts and constraints:            
            for lit in facts_:
                for constraint in constraints:
                    if constraint:                        
                        if lit in constraint:
                            constraint.remove(lit)
                            if constraint:# and lit < 0:
                                constraint[0] = -constraint[0]## Keep the even parity
                        elif -lit in constraint:
                            constraint.remove(-lit)
                        ## Check for new implications after each propagated literal
                        if len(constraint) == 1: ## New implication
                            #if self.__display:
                            #    print "      New implication ", constraint
                            if constraint[0] not in facts:
                                facts_.append(constraint[0])
                                implications.append(constraint[0])
                            constraint.remove(constraint[0])
        if self.__display:
            print("")
            print("    constraints: %s"%constraints)
            print("    facts: %s"%facts)
            print("    facts_: %s"%facts_)
            print("    implications: %s"%implications)

        return facts, implications

    def __add_watch(self, ctl, xor, unassigned, thread_ids):
        """
        Adds a watch for the for the given index.

        The literal at the given index has to be either unassigned or become
        unassigned through backtracking before the associated constraint can
        become unit resulting again.
        """
        variable = abs(xor[unassigned])
        #ctl.add_watch( variable)
        #ctl.add_watch(-variable)
        for thread_id in thread_ids:
            self.__states[thread_id].setdefault(variable, []).append((xor, unassigned))

    def init(self, init):
        """
        Initializes xor constraints and watches based on the symbol table.

        Constraints of length zero and one are handled specially, to keep the
        implementation of the general constraints simple.
        """
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append({})

        ret = util.symbols_to_xor_r(init.symbolic_atoms, util.default_get_lit(init))
        if ret is None:
            self.__sat = False
        else:
            constraints, facts = ret
            self.__consequences.extend(facts)

            ## Reduce constraints with facts (Pre-GJE)
            ## Perform propagation from facts
            if self.__preprocess:
                if facts and constraints:
                    constraints, facts = propagate_implications(constraints, facts)
                    ## TODO: Detect conflicts and satisfiability from here
                    self.__consequences.extend(facts)
                
            for constraint in constraints:
                if len(constraint) > 1:
                    self.__xors.append(constraint)
                    for literal in constraint:
                        if abs(literal) not in self.__lits:
                            self.__lits.append(abs(literal))
                    xor = XOR(constraint)
                    self.__add_watch(init, xor, 0, range(init.number_of_threads))
                    self.__add_watch(init, xor, 1, range(init.number_of_threads))

        if len(self.__xors) > 1:
            self.__extended = True

        init.check_mode = clingo.PropagatorCheckMode.Fixpoint

        if self.__display:
            print("facts %s"%facts)
            for constraint in constraints:
                print(constraint)
            print("literals: %s"%self.__lits)
            print("xors: %s"%self.__xors)

    def check(self, control):
        """
        Since the XOR constraint above handles only constraints with at least
        two literals, here the other two cases are handled.

        Empty conflicting constraints result in top-level conflicts and unit
        constraints will be propagated on the top-level.
        """
        if control.assignment.decision_level == 0:
            if not self.__sat:
                control.add_clause([]) and control.propagate()
                return
            for lit in self.__consequences:
                if not control.add_clause([lit]) or not control.propagate():
                    return

        #elif control.assignment.decision_level > 0:
        #    assigned = []
        #    for lit in self.__lits:
        #        if control.assignment.is_true(lit):
        #            assigned.append( lit)
        #        elif control.assignment.is_false(lit):
        #            assigned.append(-lit)
            
        #    print "dl", control.assignment.decision_level, "assigned:", len(assigned), "of", len(self.__lits)
        #    #print self.__xors

        elif control.assignment.is_total:
            xors = self.__xors
            for xor in xors:
                conflict = True
                nogood = []
                if xor[0] < 0:
                    conflict = False
                
                for lit in xor:
                    lit = abs(lit)
                    if control.assignment.is_true(lit):
                        nogood.append( lit)
                    elif control.assignment.is_false(lit):
                        nogood.append(-lit)
                        
                    value = control.assignment.value(lit)
                    if value:
                        conflict ^= True
                        
                if conflict:
                    if not control.add_nogood(nogood) or not control.propagate():
                        return    

                    


#    def propagate(self, control, changes):
#        """
#        Propagates XOR constraints maintaining two watches per constraint.

#        Generated conflicts are guaranteed to be asserting (have at least two
#        literals from the current decision level).
#        """
#        extended = self.__extended
#        state  = self.__states[control.thread_id]
        
#        for literal in changes:
#            self.__propagations += 1
#            variable = abs(literal)

#            state[variable], watches = [], state[variable]
#            assert(len(watches) > 0)
#            for i in range(len(watches)):
#                xor, unassigned = watches[i]
#                if self.__display:
#                    print("propagating literal %s in xor %s"%(literal,xor._XOR__literals))
#                if xor.propagate(control.assignment, unassigned):
#                    # We found an unassigned literal, which is watched next.
#                    self.__add_watch(control, xor, unassigned, (control.thread_id,))
#                else:
                    # Here the constraint is either unit, satisfied, or
                    # conflicting. In any case, we can keep the watch because
                    # (*) the current decision level has to be backtracked
                    # before the constraint can become unit again.
                    # Extend the reason method to propagate more over other XORs
#                    state[variable].append((xor, unassigned))

#                    if self.__display:
#                        print(" not propagated xor: %s"%xor._XOR__literals)

#                    nogood = xor.reason(control.assignment, unassigned, self.__display)
#                    if self.__display:
#                        print("   nogood: %s"%nogood)
#                    if not nogood:
#                        if self.__display:
#                            print("   satisfied nogood... nothing to propagate")
#                    if nogood is not None:
#                        if self.__display:
#                            print("   add nogood %s"%nogood)
#                        if not control.add_nogood(nogood) or not control.propagate():
#                            assert(state[variable])
#                            # reestablish the remaining watches with the same
#                            # reason as in (*)
#                            state[variable].extend(watches[i + 1:])
#                            return

#                        if self.__feature:
#                            if extended:
#                                #if self.__display:
#                                print("   Extended propagation...")
#                                clause, implications = self.__extended_propagation(control.assignment, xor._XOR__literals)
#                                if implications:
#                                    if self.__display:
#                                        print("   Add Extended clause %s with implications %s"%(clause,implications))
#                                    #for lit in implications:
#                                    if not control.add_clause(implications+clause) or not control.propagate():
#                                        #if not control.add_nogood([-lit for lit in clause+implications]) or not control.propagate():
#                                        return
#                                if self.__display:
#                                    print("")
                        
#            if len(state[variable]) == 0:
#                control.remove_watch( variable)
#                control.remove_watch(-variable)
#                state.pop(variable)
