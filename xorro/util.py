from collections import namedtuple
from itertools import *
from functools import *
import sys
from textwrap import dedent as _dedent
from math import log
from random import randint, sample
from . import gje


def attrdef(m, a, b):
    return getattr(m, a if hasattr(m, a) else b)

zip_longest = attrdef(sys.modules[__name__], 'zip_longest', 'izip_longest')
reduce = getattr(sys.modules[__name__], 'reduce')

def get_parity(par):
    if str(par) == "odd": return 1
    else: return 0

def invert_parity(par):
    return int(par) ^ 1

def get_str_parity(par):
    if par == 1: return "odd"
    else: return "even"

def default_get_lit(init):
    value = init.assignment.value
    def get_lit(atom):
        lit = init.solver_literal(atom.literal)
        return lit, value(lit)
    return get_lit

def build_theory_atoms(out_str, xor, parity):
    terms = " ; ".join(str(x)+":"+str(x) for x in sorted(xor))
    out_str  += "&%s{ %s }.\n"%(get_str_parity(parity), terms)
    return out_str

class _XORConstraint:
    def __init__(self, parity):
        self.parity = parity
        self.literals = set()

def symbols_to_xor_r(symbolic_atoms, get_lit):
    """
    Returns None if the constraints are trivially unsatisfiable, otherwise
    returns a list of xor constraints and a list of facts. A xor constraint is
    represented as a list of literals.

    Arguments:
    symbolic_atoms -- The domain having predicates __parity/2 and __parity/3.
    get_lit        -- Function mapping a symbolic atom to a litral and its
                      truth value.
    """
    constraints = {}
    lits = []
    for atom in symbolic_atoms.by_signature("__parity",2):
        cid = atom.symbol.arguments[0].number
        par = atom.symbol.arguments[1].name
        constraints[cid] = _XORConstraint(get_parity(par))

    for atom in symbolic_atoms.by_signature("__parity",3):
        constraint = constraints[atom.symbol.arguments[0].number]
        lit, truth = get_lit(atom)

        if truth:
            constraint.parity = invert_parity(constraint.parity)
        elif truth is None:
            if lit in constraint.literals:
                constraint.literals.remove(lit)
            elif -lit in constraint.literals:
                constraint.literals.remove(-lit)
                constraint.parity = invert_parity(constraint.parity)
            else:
                if lit < 0:
                    constraint.literals.add(abs(lit))
                    constraint.parity = invert_parity(constraint.parity)
                else:
                    constraint.literals.add(lit)
                if abs(lit) not in lits:
                    lits.append(abs(lit))
                
    facts = set()
    result = []
    for constraint in constraints.values():
        literals = sorted(constraint.literals)
        n = len(literals)
        if n == 0:
            if constraint.parity == 1:
                return None
        else:
            if constraint.parity == 0:
                literals[0] = -literals[0]
            if n > 1:
                result.append(literals)
            else:
                facts.add(literals[0])

    return result, sorted(facts)


def generate_random_xors(prg, files, s, q):
    """
    Of course adding the theory may not be the best way to do it. This is just a hack
    Using the AST is a better alternative to extract the symbols to build the xor constraints.
    In the end, we just need the symbols to write a file with random constraints. 
    """
    for f in files:
        prg.load(f)

    prg.add("base", [], _dedent("""\
      #theory parity { 
        element {}; 
        &odd/0 : element, directive; 
        &even/0 : element, directive }.
      """))

    prg.ground([("base", [])])

    estimated_s = s
    constraints = []
    parities = []
    xors  = ""
    symbols = [atom.symbol for atom in prg.symbolic_atoms if atom.is_fact is False and "__parity" not in str(atom.symbol)]
    if len(symbols) > 0:
        if s == 0:
            estimated_s = int(log(len(symbols) + 1, 2))
        print("Random XOR constraints: %s"%estimated_s)
        for i in range(estimated_s):
            range_ = int((len(symbols))*q)
            size = randint(range_, range_)
            xors = build_theory_atoms(xors, sorted(sample(symbols, size)), randint(0,1))

        file_ = open("examples/__temp_xors.lp","w")
        file_.write(xors)
        file_.close()
    return xors


def get_xors(prg, files, add_theory):
    """
    Get XORs from encoding(s)/instance(s)
    """

    ## Load files
    for f in files:
        prg.load(f)

    ## Theory is added when Random XORs are built.
    ## So, if not sampling, theory must be added here.
    ## This must be substitute by using the AST
    if add_theory:        
        prg.add("base", [], _dedent("""\
        #theory parity { 
         element {}; 
         &odd/0 : element, directive; 
         &even/0 : element, directive }.
        """))

    prg.ground([("base", [])])

    ## Get XORS
    all_lits       = []
    xors_parities  = []
    xors_lits      = []

    for atom in prg.theory_atoms:
        xors_parities.append(get_parity(atom.term))
        lits = []
        
        for e in atom.elements:
            if len(e.terms) == 2:
                lits.append(str(e.terms[1]))
                if str(e.terms[1]) not in all_lits:
                    all_lits.append(str(e.terms[1]))
            else:
                lits.append(str(e.terms[0]))
                if str(e.terms[0]) not in all_lits:
                    all_lits.append(str(e.terms[0]))
        xors_lits.append(lits)

    return xors_lits, xors_parities, all_lits


def split_x(data, _split, prev):
    _aux_prefix   = "__aux"
    start = prev
    
    # Slice the first sub_xor of size "_split" -1
    base_xor = data[:(_split-1)]
    rest_xor = data[(_split-1):]

    # Slice the rest chunk from the original xor of size "_split" -2
    xor_chunks = [rest_xor[x:x+(_split-2)] for x in range(0, len(rest_xor), _split-2)]
    # If the last chunk is of size 1, do not add an aux variable and insert this last element in a previous chunk if exist
    if len(xor_chunks) > 1 and len(xor_chunks[-1]) == 1:
        last = xor_chunks[-1]
        xor_chunks[-2].append(last[0])
        del xor_chunks[-1]

    # Add the prev and the following aux variables
    for i in range(len(xor_chunks)-1):
        xor_chunks[i].append("%s_%s"%(_aux_prefix, prev+1))
        xor_chunks[i].insert(0, "%s_%s"%(_aux_prefix, prev))
        prev += 1

    # Add first aux variable in base_xor
    xor_chunks.insert(0, base_xor)
    xor_chunks[0].insert(_split-1, "%s_%s"%(_aux_prefix, start))

    # Add the last aux variable in the last sub xor
    xor_chunks[-1].insert(0, "%s_%s"%(_aux_prefix, prev))

    # Build the choice rule of aux variables
    _auxs = []
    
    for i in range(start,prev+1):
        _auxs.append("%s_%s"%(_aux_prefix, i))

    # Parse string of the choice rule
    terms = " ; ".join(str(x) for x in _auxs)
    choice_rule = "{ %s }. "%(terms)

    return xor_chunks, choice_rule, prev
    

def split(xors, parities, split, display):
    """
    Split XORs
    """
    choice_rule = ""
    sub_pars = []
    splitted_xors = []
    splitted_pars = []
    aux_index = 0
    choices = []
    
    ## If len of xor is less or equal the split value, do not split
    for i in range(len(xors)):
        if len(xors[i]) <= split:
            if display:
                print("XOR %s not splitted. XOR size is less than the split value"%(i+1))
            splitted_xors.append(xors[i])
            splitted_pars.append(parities[i])
            choice_rule = None
        else:
            if display:
                print("Splitting XOR %s"%(i+1))
            sub_xors, choice_rule, aux_index = split_x(xors[i], split, aux_index+1)
            choices.append(choice_rule)
            sub_pars = [0] * len(sub_xors)
            sub_pars[0] = parities[i]

            for i in range(len(sub_xors)):
                splitted_xors.append(sub_xors[i])
                splitted_pars.append(sub_pars[i])

    return splitted_xors, splitted_pars, choices


def pre_gje(xors_lits, xors_parities, all_lits, show):
    # If exist more than one constraint
    """
    xors_lits = [['a','c','d','f'],
                 ['c','d','e','f']]
    xors_pars = [1, 0]
    all_lits  = ['a','b','c','d','e','f','g','h']
    """

    # Build Matrix
    matrix = []
    for i in range(len(xors_parities)):
        row = []
        for lit in all_lits:
            if lit in xors_lits[i]:
                row.append(1)
            else:
                row.append(0)
        row.append(xors_parities[i])
        matrix.append(row)

    if show:
        print "Pre"
        gje.print_matrix(matrix)
    matrix = gje.perform_gauss_jordan_elimination(matrix, False)
    if show:
        print "Post"
        gje.print_matrix(matrix)

    updated_xors, updated_pars = [], []
    for row in matrix:
        updated_row = []
        for i in range(len(row)-1):
            if row[i] == 1:
                updated_row.append(all_lits[i])
        updated_pars.append(row[-1])
        updated_xors.append(updated_row)

    return updated_xors, updated_pars


def write_file(files, xors, add_rules):
    """
    Rewrite input files with preprocessed parity constraints
    """
    ## Create temp file
    file_ = open("examples/__rewritten_program.lp", 'w')

    ## Get lines
    lines = list(chain.from_iterable(open(f) for f in files))
    #print "lines", lines

    ## Write lines excluding theory atoms
    for i in range(len(lines)):
        if "odd{" not in str(lines[i]) and "even{" not in str(lines[i]):
            file_.write("%s"%lines[i])

    ## Write XORs
    file_.write("%s"%xors)

    ## Write additional rules. e.g. choices for split
    for rule in add_rules:
        file_.write("%s"%rule)
        
    ## Close file
    file_.close()

    ## Update files list
    files = ["examples/__rewritten_program.lp"]
    
    return files
