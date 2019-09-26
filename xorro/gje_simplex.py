from . import util
from . import gje
from itertools import chain
import clingo

def get_nogood(assignment, literals):
    ng = []
    for lit in literals:
        print lit, assignment.value(lit)
        if assignment.value(lit) is False:
            ng.append(-lit)
        elif assignment.value(lit) is True:
            ng.append( lit)

    return ng

class Matrix:
    """
    The Matrix maintains the following invariants:
    1. Every row must contain at least three 1 entries
    2. Two watched literals, one basic and one non basic
    
    """
    def __init__(self, matrix):
        self.__rows = len(matrix)
        self.__cols = len(matrix[0])
        self.__matrix = matrix

    def __getitem__(self, idx):
        return self.__matrix[idx]

    def __setitem__(self, idx, item):
        self.__matrix[idx] = item

    def __get_rows__(self):
        return self.__rows

    def __get_cols__(self):
        return self.__cols

    def __print__(self):
        for row in self.__matrix:
            print(row)
        print("")

    def __reduce__(self, col, pos):
        pivot_row = self.__matrix[pos]
        pivot_val = self.__matrix[pos][col]
        changes = []
        unaffected = []
        
        for i in range(self.__rows):
            if self.__matrix[i] != pivot_row:
                if self.__matrix[i][col] == 1:
                    changes.append(i)
                    for k in range(self.__cols):
                        self.__matrix[i][k] ^= pivot_row[k]
                else:
                    unaffected.append(i)

        return changes, unaffected

    def __check_conflict__(self, literals, assignment):
        conflict = True
        for row in self.__matrix:
            if row[-1] == 1: ## Find the potential conflicting parity
                print literals
                print row
                for i in range(len(row)-1):
                    if row[i] == 1:
                        assmt = assignment.value(literals[i])
                        print row[i], literals[i], assmt
                        if assmt == True or assmt == None: ## If at least one literal is not False, then there is no conflict
                            conflict = False
                            break

                        print conflict
        return conflict

    def __remove_row__(self, row):
        self.__matrix.remove(row)
        return self.__matrix

    def __remove_col__(self, col):
        for row in self.__matrix:
            del row[col]
        return self.__matrix

    def __update_xors__(self, xor_index, variable, literals, affected):
        row = self.__matrix[xor_index]
        xor = []
        for i in range(len(literals)):
            if row[i] == 1 and literals[i] != variable:
                xor.append(literals[i])
        if row[-1] == 0:
            xor[0] = -xor[0]

        if affected:
            xor.append(variable)
        return xor


    def get_implication(self, assignment, literals):
        xors = []
        unit = []
        partial_assignment = []
        ## Get reduced XORs via UP
        for row in self.__matrix:
            parity = row[-1]
            xor = []
            for i in range(len(literals)):
                if row[i] == 1:
                    if assignment.value(literals[i]) == None:
                        xor.append(literals[i])
                    elif assignment.value(literals[i]) == True:
                        parity = parity ^ 1
                        if literals[i] not in partial_assignment:
                            partial_assignment.append(literals[i])
                    elif assignment.value(literals[i]) == False:
                        if -literals[i] not in partial_assignment:
                            partial_assignment.append(-literals[i])
            if len(xor) == 1:
                if parity == 0: 
                    unit.append(-xor[0])
                elif parity == 1:
                    unit.append( xor[0])
            else:
                if parity == 0 and xor:
                    xor[0] = -xor[0]
                xors.append(xor)

        #print xors
        #print unit

        ## UP
        state = []
        while True:
            state = unit[:]
            for lit in unit:
                for xor in xors:
                    if not xor:
                        continue
                    else:
                        if lit in xor:
                            xor.remove(lit)
                            if xor and lit < 0:
                                xor[0] = -xor[0]## Keep the even parity
                        elif -lit in xor:
                            xor.remove(-lit)
                        if len(xor) == 1: ## New implication
                            unit.append(xor[0])
                            xor.remove(xor[0])

            if unit == state:
                break

        #print unit
        return unit, partial_assignment

        

        


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

    def reason(self, assignment, i):
        """
        If the constraint is unit resulting or conflicting returns a reason in
        form of a clause.
        """
        # Switch to the index of the other watched literal that is either
        # unassigned and has to be propagated or has to be checked for a
        # conflict. In the second case it was assigned on the same level as the
        # propagated literal.
        i = 1 - i
        count = 0
        clause = []
        for j in range(len(self)):
            if i == j:
                continue
            if assignment.is_true(self[j]):
                clause.append(-self[j])
                count += 1
            else:
                clause.append(self[j])

        clause.append(-self[i] if count % 2 else self[i])

        return None if assignment.is_true(clause[-1]) else clause
        
                

class Simplex_GJE:
    def __init__(self, cutoff):
        self.__states  = []
        self.__states_gje = []
        self.__sat = True
        self.__consequences = []
        self.__cutoff = cutoff
        self.__literals = []
        self.__matrix = []
        self.__basic_lits = []
        self.__lits_xor = []

        
    def __add_watch(self, ctl, xor, unassigned, thread_ids, states):
        """
        Adds a watch for the for the given index.

        The literal at the given index has to be either unassigned or become
        unassigned through backtracking before the associated constraint can
        become unit resulting again.
        """
        variable = abs(xor[unassigned])
        ctl.add_watch( variable)
        ctl.add_watch(-variable)
        for thread_id in thread_ids:
            states[thread_id].setdefault(variable, []).append((xor, unassigned))

    def init(self, init):
        """
        Initializes xor constraints based on the symbol table to build a binary matrix.
        This propagator is called on fixpoints to perform Gauss-Jordan Elimination after Unit Propagation
        """
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append({})
            self.__states_gje.append({})
            self.__lits_xor.append({})

        init.check_mode = clingo.PropagatorCheckMode.Fixpoint
        ## Get the constraints
        ret = util.symbols_to_xor_r(init.symbolic_atoms, util.default_get_lit(init))
        
        if ret is None:
            self.__sat = False
        elif ret is not None:
            # NOTE: whether facts should be handled here is up to question
            #       this should only be necessary if the propagator is to be used standalone
            #       without any of the other approaches
            constraints, facts = ret
            self.__consequences.extend(facts)
            ## Add facts to the matrix. Unit xors serves to deduce more information after GJE.
            for fact in facts:
                constraints.append([fact])

            
            """
            How the preprocessing works:
            Get all the literals involved in parity constraints
            Build the matrix and perform a GJE procedure
            Rebuild the XORs after reducing the matrix
            Count the number of XORs of length greater than 2. If more than one exist, it is worth it to keep the matrix
            Else, if exist only one longer XOR or XORs of lenght 2, do not keep the matrix and no GJE is done. Add these XORs to the UP state
            Else, if exist XORs of size 1, extend the consquences list
            If the matrix is not kept, the propagator runs as the UP approach
            Else, if the matrix exist, we need to identify the basic and non basic literals
            TODO: Analyze if the XORs belonging to the matrix are going to be handled in the same state as the other XORs or separately.
            """
            
            print("constraints :%s"%constraints)
            for constraint in constraints:
                for lit in constraint:
                    if abs(lit) not in self.__literals:
                        self.__literals.append(abs(lit))
            
            # Build Matrix
            for constraint in constraints:
                row = []
                for lit in self.__literals:
                    if lit in constraint or -lit in constraint:
                        row.append(1)
                    else:
                        row.append(0)
                # If even constraint
                if constraint[0] < 0:
                    row.append(0)
                else:
                    row.append(1)
                self.__matrix.append(row)

            # Preprocess by reducing the matrix to Reduced Row Echelon Form
            print("Initial Matrix")
            gje.print_matrix(self.__matrix)
            self.__matrix = gje.perform_gauss_jordan_elimination(self.__matrix,False)
            print("Reduced Matrix")
            gje.print_matrix(self.__matrix)

            constraints = []
            ## Rebuild XORs after initial GJE
            ## Check cases if XORs of size 1, 2 or greater or equal than 3.
            print("Rebuild xors")
            for row in self.__matrix:
                constraint = []
                for i in range(len(row)-1):
                    if row[i] == 1:
                        constraint.append(self.__literals[i])
                if constraint:
                    if row[-1] == 0:
                        constraint[0] = -constraint[0]
                    constraints.append(constraint)

            print(constraints)
            longer_xor = 0
            for constraint in constraints:
                if len(constraint) > 2:
                    longer_xor+=1

            matrix = self.__matrix
            self.__matrix = []

            ## Check for constraints after reduced matrix
            for constraint in constraints:
                if len(constraint) == 0:
                    self.__sat = False
                    break
                if len(constraint) == 1:
                    ## Consequences
                    self.__consequences.extend(constraint)
                    pos = self.__literals.index(abs(constraint[0]))
                    for row in matrix:
                        del row[pos]
                    self.__literals.pop(pos)
                elif longer_xor < 2:
                    ## UP
                    xor = XOR(constraint)
                    self.__add_watch(init, xor, 0, range(init.number_of_threads), self.__states)
                    self.__add_watch(init, xor, 1, range(init.number_of_threads), self.__states)
                elif longer_xor >= 2:
                    ## For GJE
                    pos = constraints.index(constraint)
                    self.__matrix.append(matrix[pos])
                    xor = XOR(constraint)
                    self.__add_watch(init, xor, 0, range(init.number_of_threads), self.__states_gje)
                    self.__add_watch(init, xor, 1, range(init.number_of_threads), self.__states_gje)
                    for lit in constraint:
                        for thread in range(init.number_of_threads):
                            self.__lits_xor[thread_id].setdefault(lit, []).append(xor)
            print "lits_xor"
            print self.__lits_xor

            ## Get basic and non basic literals
            number_basics = len(self.__matrix)
            if number_basics > 0:
                print("")
                print("literals: %s"%self.__literals)
                gje.print_matrix(self.__matrix)
                print(constraints)

                self.__basic_lits = self.__literals[0:number_basics]
                print("basic lits: %s"%self.__basic_lits)
                                            
        else:
            # NOTE: if the propagator is to be used standalone, this case has to be handled
            pass

        self.m = Matrix(self.__matrix)

        print self.m._Matrix__matrix

        #mm.__print__(self.__literals)
        #mm.__reduce_matrix__(0, 0)
        #mm.__print__(self.__literals)

        #print self.__states
        print self.__states_gje
                     

    def check(self, control):
        """
        Check if current assignment is conflict-free, detect a conflict or deduce literals
        by doing Gauss-Jordan Elimination
        """
        """
        Since the XOR constraint above handles only constraints with at least
        two literals, here the other two cases are handled.

        Empty conflicting constraints result in top-level conflicts and unit
        constraints will be propagated on the top-level.
        """
        if not self.__sat:
            control.add_clause([]) and control.propagate()
            return
        for lit in self.__consequences:
            if not control.add_clause([lit]) or not control.propagate():
                return

    def propagate(self, control, changes):
        """
        Propagates XOR constraints maintaining two watches per constraint.

        Generated conflicts are guaranteed to be asserting (have at least two
        literals from the current decision level).
        """
        state = self.__states_gje[control.thread_id]
        basic = self.__basic_lits
        matrix = self.m
        #constraints = self.__constraints
        
        for literal in changes:
            variable = abs(literal)
            print "propagate literal", literal, "variable", variable

            if variable in state and state[variable]:
                state[variable], watches = [], state[variable]
                print state
                assert(len(watches) > 0)
                
                for i in range(len(watches)):
                    # Basic vabriables
                    # GJE process
                    if variable in basic:
                        xor, unassigned = watches[i]
                        if xor.propagate(control.assignment, unassigned):
                            print "xor", xor._XOR__literals, "xor index", xor._XOR__index
                            print "index", unassigned, "literal", xor._XOR__literals[unassigned]
                        
                            print "Basic variable"
                            print "Update basic literals"
                            col = self.__literals.index(xor._XOR__literals[unassigned])
                            pos = basic.index(variable)
                            print "Update basic", variable, "with", xor._XOR__literals[unassigned], "in position", col
                            basic[pos] = xor._XOR__literals[unassigned]
                            print basic

                            print "Check state"
                            print state
                            for key in state.keys():
                                state[key] = []

                            print state

                            
                            print "Before reduce"
                            matrix.__print__()
                            print "Reduce matrix"
                            update_xor_index, unaffected = matrix.__reduce__(col, pos)
                            print "update xor index", update_xor_index, "unaffected", unaffected
                            print self.__literals
                            matrix.__print__()
                            
                            
                            print ""
                            print "Current xor"
                            print xor._XOR__literals
                            print "watches", xor._XOR__literals[0], xor._XOR__literals[1]
                            self.__add_watch(control, xor, 0, (control.thread_id,), self.__states_gje)
                            self.__add_watch(control, xor, 1, (control.thread_id,), self.__states_gje)
                            
                            print "Update xors"
                            updated_xors = []
                            unaffected_xors = []
                            for index in update_xor_index:
                                updated_xors.append(matrix.__update_xors__(index, variable, self.__literals, True))

                            for xor_ in updated_xors:
                                print xor_
                                print "watches", xor_[0], xor_[1]
                                xor = XOR(xor_)
                                self.__add_watch(control, xor, 0, (control.thread_id,), self.__states_gje)
                                self.__add_watch(control, xor, 1, (control.thread_id,), self.__states_gje)

                            print "Unaffected xors"
                            for index in unaffected:
                                unaffected_xors.append(matrix.__update_xors__(index, variable, self.__literals, False))

                            for xor_ in unaffected_xors:
                                print xor_
                                print "watches", xor_[0], xor_[1]
                                xor = XOR(xor_)
                                self.__add_watch(control, xor, 0, (control.thread_id,), self.__states_gje)
                                self.__add_watch(control, xor, 1, (control.thread_id,), self.__states_gje)

                            print "state:"
                            print state
                            #print self.__states_gje[control.thread_id][variable]
                            #if not state[variable]:
                            #    print "remove watches"
                            #    control.remove_watch( variable)
                            #    control.remove_watch(-variable)
                            #    state.pop(variable)
                            #print "state:"
                            #print state
                            #print self.__states_gje
                            #print "lits xor:"
                            #print self.__lits_xor
                            print ""
                            
                            print "Check for conflict"
                            """
                            Check for conflicts after the matrix is reduced.
                            Analyze if it is only convinient to check for a potential conflict on all the rows except for the unaffected rows.
                            """
                            conflict = matrix.__check_conflict__(self.__literals, control.assignment)
                            print "Conflict: ", conflict

                            if conflict:
                                ## Return the partial assignment
                                nogood = get_nogood(control.assignment, self.__literals)
                                print "nogood", nogood
                                if not control.add_nogood(nogood) or not control.propagate():
                                    return
                            print ""

                        else:
                            print "Cannot find unnasigned literal... check reason"
                            print "Find implications/conflicts"
                            for lit in self.__literals:
                                print lit, control.assignment.value(lit)

                            print ""
                            unit_clauses, partial = matrix.get_implication(control.assignment, self.__literals)
                            print "unit clauses", unit_clauses, "partial", partial
                            print ""
                            # UP
                            # Here the constraint is either unit, satisfied, or
                            # conflicting. In any case, we can keep the watch because
                            # (*) the current decision level has to be backtracked
                            # before the constraint can become unit again.
                            state[variable].append((xor, unassigned))

                            print "My reason"
                            if unit_clauses is not None:
                                for unit in unit_clauses:
                                    print "nogood:", [-unit]+partial
                                    if not control.add_nogood([-unit]+partial) or not control.propagate():
                                        return
                            else:
                                if not control.add_clause(partial) or not control.propagate():
                                    return


                            clause = xor.reason(control.assignment, unassigned)
                            if clause is not None:
                                print "UP reason"
                                print "clause", clause
                                if not control.add_clause(clause) or not control.propagate():
                                    assert(state[variable])
                                    # reestablish the remaining watches with the same
                                    # reason as in (*)
                                    state[variable].extend(watches[i + 1:])
                                    return

                    else:
                        print "Is not basic, continue"
                        print "Reestablish the watches"
                        # reestablish the remaining watches with the same
                        # reason as in (*)
                        state[variable].append(watches[i])
                        print state
                    print ""
                        
                        
                            
                    # We found an unassigned literal, which is watched next.
                    #self.__add_watch(control, xor, unassigned, (control.thread_id,), self.__states_gje)

                    
            
                if len(state[variable]) == 0:
                    print "remove watches"
                    control.remove_watch( variable)
                    control.remove_watch(-variable)
                    state.pop(variable)
