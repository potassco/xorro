from . import util
from . import gje
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

#    def reason_gje(self, columns, assignment, n_lits, cutoff):
#        state = {}
#        partial = []
#        deduced_literals = []

#        ## Get Partial Assignment
#        state["parity"] = columns["parity"]
#        for lit, column in columns.items():
#            if lit != "parity":
#                value = assignment.value(lit)
#                if value == None:
#                    state[lit] = column
#                elif value == True:
#                    state["parity"] = xor_columns(column, state["parity"])
#                    partial.append( lit)
#                elif value == False:                    
#                    partial.append(-lit)                           

        ## Build the matrix from columns state
#        matrix, xor_lits= gje.columns_state_to_matrix(state)

        ## Percentage of assigned literals
#        assigned_lits_perc = 1.0-float("%.1f"%(len(xor_lits)/n_lits))
        ## If there are more than unary xors perform GJE
#        if len(state) > 2 and assigned_lits_perc >= cutoff:
#            matrix = gje.remove_rows_zeros(matrix)
#            matrix = gje.perform_gauss_jordan_elimination(matrix, False)

        ## Check SATISFIABILITY
#        conflict = gje.check_sat(matrix)
#        if not conflict and xor_lits:
            ## Imply literals 
#            deduced_literals = gje.deduce_clause(matrix, xor_lits)

#        return conflict, partial, deduced_literals


class Simplex_GJE:
    def __init__(self, cutoff):
        self.__states  = []
        self.__states_gje = []
        self.__sat = True
        self.__consequences = []
        self.__cutoff = cutoff
        self.__n_literals = 0
        self.__literals = []
        self.__matrix = []
        self.__basic_lits = []

        
    def __add_watch(self, ctl, xor, unassigned, thread_ids):
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
            self.__states[thread_id].setdefault(variable, []).append((xor, unassigned))

    def init(self, init):
        """
        Initializes xor constraints based on the symbol table to build a binary matrix.
        This propagator is called on fixpoints to perform Gauss-Jordan Elimination after Unit Propagation
        """
        for thread_id in range(len(self.__states), init.number_of_threads):
            self.__states.append({})
            self.__states_gje.append({})

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

            """
            Count the number of XORs of length greater than 2.
            If exist only one XOR of lenght 2, do not do GJE. Add it to the UP state
            Else, if exist more than 1 XOR of length 3 or greater, build the matrix to do GJE
            """
            print "constraints", constraints
            for constraint in constraints:
                for lit in constraint:
                    if abs(lit) not in self.__literals:
                        self.__literals.append(abs(lit))

            print "literals", self.__literals, "\n"
            
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
            print "Initial Matrix"
            gje.print_matrix(self.__matrix)
            self.__matrix = gje.perform_gauss_jordan_elimination(self.__matrix,False)
            print "Reduced Matrix"
            gje.print_matrix(self.__matrix)

            constraints = []
            ## Rebuild XORs after initial GJE
            ## Check cases if XORs of size 1, 2 or greater or equal than 3.
            print "Rebuild xors"
            for row in self.__matrix:
                constraint = []
                for i in range(len(row)-1):
                    if row[i] == 1:
                        constraint.append(self.__literals[i])
                if constraint:
                    if row[-1] == 0:
                        constraint[0] = -constraint[0]
                    constraints.append(constraint)

            print constraints
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
                    for row in self.__matrix:
                        del row[pos]
                    self.__literals.pop(pos)
                elif longer_xor < 2:
                    ## UP
                    xor = XOR(constraint)
                    self.__add_watch(init, xor, 0, range(init.number_of_threads))
                    self.__add_watch(init, xor, 1, range(init.number_of_threads))
                elif longer_xor >= 2:
                    ## For GJE
                    pos = constraints.index(constraint)
                    self.__matrix.append(matrix[pos])
                    #xor = XOR(constraints[i])
                    #self.__add_watch(init, xor, 0, range(init.number_of_threads), self.__states_gje)
                    #self.__add_watch(init, xor, 1, range(init.number_of_threads), self.__states_gje)

            print ""
            print self.__literals
            gje.print_matrix(self.__matrix)
            print constraints

            

                
             #   self.__basic_lits.append(abs(_xor[0]))
            #print "basic"
            #print self.__basic_lits
                                            
        else:
            # NOTE: if the propagator is to be used standalone, this case has to be handled
            pass

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
        state  = self.__states[control.thread_id]
        #print state
        for literal in changes:
            #print literal
            variable = abs(literal)

            state[variable], watches = [], state[variable]
            assert(len(watches) > 0)
            for i in range(len(watches)):
                xor, unassigned = watches[i]
                if xor.propagate(control.assignment, unassigned):
                    # We found an unassigned literal, which is watched next.
                    self.__add_watch(control, xor, unassigned, (control.thread_id,))
                else:
                    # Here the constraint is either unit, satisfied, or
                    # conflicting. In any case, we can keep the watch because
                    # (*) the current decision level has to be backtracked
                    # before the constraint can become unit again.
                    state[variable].append((xor, unassigned))

                    clause = xor.reason(control.assignment, unassigned)
                    if clause is not None:
                        if not control.add_clause(clause) or not control.propagate():
                            assert(state[variable])
                            # reestablish the remaining watches with the same
                            # reason as in (*)
                            state[variable].extend(watches[i + 1:])
                            return

            if len(state[variable]) == 0:
                control.remove_watch( variable)
                control.remove_watch(-variable)
                state.pop(variable)

#    def propagate(self, control, changes):
        """
        Propagates XOR constraints maintaining two watches per constraint.

        Generated conflicts are guaranteed to be asserting (have at least two
        literals from the current decision level).
        """
#        state  = self.__states[control.thread_id]
#        n      = self.__n_literals
#        cutoff = self.__cutoff
#        basic  = self.__basic_lits
#        matrix = self.__matrix
#        update_basic = False
        
#        for literal in changes:
#            variable = abs(literal)
#            print variable
#            basic_index = None
#            for k in range(len(basic)):
#                if variable == basic[k]:
#                    basic_index = k
#            print "state", state
#            state[variable], watches = [], state[variable]
#            assert(len(watches) > 0)
#            for i in range(len(watches)):
#                xor, unassigned = watches[i]
                
#                if xor.propagate(control.assignment, unassigned):
#                    # We found an unassigned literal, which is watched next.
#                    self.__add_watch(control, xor, unassigned, (control.thread_id,))
#                    if basic_index is not None:
#                        print "Update basic"
#                        basic[basic_index] = xor[unassigned]
#                        print basic
#                        print "Update columns"
#                        print self.__literals
#                        gje.print_matrix(matrix)
#                        print ""
#                        for l in range(len(self.__literals)):
#                            if self.__literals[l] == xor[unassigned]:
#                                temp = self.__literals[basic_index]
#                                self.__literals[basic_index] = self.__literals[l]
#                                self.__literals[l] = temp
#                                matrix = gje.swap_columns(matrix, basic_index, l)
#                                print self.__literals
#                                gje.print_matrix(matrix)
#                        print ""
#                        print "Reduce Matrix"
#                        matrix = gje.reduce(matrix,basic_index)

#                else:
                    # Here the constraint is either unit, satisfied, or
                    # conflicting. In any case, we can keep the watch because
                    # (*) the current decision level has to be backtracked
                    # before the constraint can become unit again.
#                    state[variable].append((xor, unassigned))

                    #for lit in xor._XOR__literals:
                    #    print "lit:", lit, control.assignment.value(lit)
                    ## GJE
                    #conflict, partial, clause = xor.reason_gje(columns, control.assignment, n, cutoff)
                    #if clause is not None:
                    #    for lit in clause:
                    #        if not control.add_nogood(partial+[-lit]) or not control.propagate():
                    #            return                                
                    #if conflict:
                    #    if not control.add_nogood(partial) or not control.propagate():
                    #        return

#            if len(state[variable]) == 0:
#                control.remove_watch( variable)
#                control.remove_watch(-variable)
#                state.pop(variable)
