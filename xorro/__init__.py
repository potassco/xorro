"""
The xorro module contains functions to solve logic programs with parity
constraints.

Classes:
Application -- Main application class.

Functions:
main  -- Main function starting an extended clingo application.
"""

from . import util
from . import transformer as _tf
#from . import normal_form as _nf
from .countp import CountCheckPropagator
from .up import UnitPropagator
from .gje_fp import Propagate_GJE
from .gje_prop import Reason_GJE
from .gje_prop_n import State_GJE
from .gje_simplex import Simplex_GJE
#from .gje_xorsat import XorSat_GJE
from .up_fixpoints import UPExtendedPropagator
from .up_total import UPTotalPropagator
from random import sample
import sys as _sys
import os as _os
import clingo as _clingo
from textwrap import dedent as _dedent

def translate_binary_xor(backend, lhs, rhs):
    aux = backend.add_atom()
    backend.add_rule([aux], [ lhs, -rhs])
    backend.add_rule([aux], [-lhs,  rhs])
    return aux

def transform(prg, files):
    with prg.builder() as b:
        files = [open(f) for f in files]
        if len(files) == 0:
            files.append(_sys.stdin)
        _tf.transform((f.read() for f in files), b.add)

def normal_form(prg, files):
    with prg.builder() as b:
        files = [open(f) for f in files]
        if len(files) == 0:
            files.append(_sys.stdin)
        _nf.transform((f.read() for f in files), b.add)
        
class Leaf:
    def __init__(self, atom):
        self.__atom = atom

    def translate(self, backend):
        return self.__atom

class Tree:
    def __init__(self, lhs, rhs):
        self.__lhs = lhs
        self.__rhs = rhs

    def translate(self, backend):
        lhs = self.__lhs.translate(backend)
        rhs = self.__rhs.translate(backend)
        return translate_binary_xor(backend, lhs, rhs)

class List:
    def __init__(self, literals):
        assert(len(literals) > 0)
        self.__literals = literals

    def translate(self, backend):
        return util.reduce(lambda l, r: translate_binary_xor(backend, l, r), self.__literals)

def translate(mode, prg, cutoff):
    if mode == "count":
        prg.add("__count", [], _dedent("""\
            :- { __parity(ID,even,X) } = N, N\\2!=0, __parity(ID,even).
            :- { __parity(ID,odd ,X) } = N, N\\2!=1, __parity(ID,odd).
            """))
        prg.ground([("__count", [])])

    elif mode == "countp":
        prg.register_propagator(CountCheckPropagator())

    elif mode == "up":
        prg.register_propagator(UnitPropagator())

    elif mode == "gje-fp":
        prg.register_propagator(UnitPropagator())
        prg.register_propagator(Propagate_GJE(cutoff))

    elif mode == "gje-prop":
        prg.register_propagator(Reason_GJE(cutoff))

    elif mode == "gje-prop-n":
        prg.register_propagator(State_GJE(cutoff))

    elif mode == "gje-simplex":
        prg.register_propagator(Simplex_GJE(cutoff))

    elif mode == "gje-xorsat":
        prg.register_propagator(XorSat_GJE())

    elif mode == "up-fixpoints":
        prg.register_propagator(UPExtendedPropagator())

    elif mode == "up-total":
        prg.register_propagator(UPTotalPropagator())

    elif mode in ["list", "tree"]:
        def to_tree(constraint):
            layer = [Leaf(literal) for literal in constraint]
            def tree(l, r):
                return l if r is None else Tree(l, r)
            while len(layer) > 1:
                layer = list(util.starmap(tree, util.zip_longest(layer[0::2], layer[1::2])))
            return layer[0]

        def get_lit(atom):
            return atom.literal, True if atom.is_fact else None

        ret = util.symbols_to_xor_r(prg.symbolic_atoms, get_lit)
        with prg.backend() as b:
            if ret is None:
                b.add_rule([], [])
            else:
                constraints, facts = ret
                for fact in facts:
                    b.add_rule([], [-fact])
                for constraint in constraints:
                    tree = List(constraint) if mode == "list" else to_tree(constraint)
                    b.add_rule([], [-tree.translate(b)])

    else:
        raise RuntimeError("unknow transformation mode: {}".format(mode))

class Application:
    """
    Application object as accepted by clingo.clingo_main().

    Rewrites the parity constraints in logic programs into normal ASP programs
    and solves them.
    """
    def __init__(self, name):
        """
        Initializes the application setting the program name.

        See clingo.clingo_main().
        """
        self.program_name = name
        self.version = "1.0"
        self.__approach = "count"
        self.__cutoff = 0.0
        self.__s = 0
        self.__q = 0.5
        self.__sampling = _clingo.Flag(False)
        self.__display  = _clingo.Flag(False)
        self.__split = 0
        self.__pre_gje  = _clingo.Flag(False)

    def __parse_approach(self, value):
        """
        Parse approach argument.
        """
        self.__approach = str(value)
        return self.__approach in ["count", "list", "tree", "countp", "up", "gje-fp", "gje-prop", "gje-prop-n", "gje-simplex", "gje-xorsat", "up-fixpoints", "up-total"]

    def __parse_cutoff(self, value):
        """
        Parse cutoff argument.
        """
        self.__cutoff = float(value)
        return self.__cutoff >=0.0 and self.__cutoff <=1.0

    def __parse_s(self, value):
        """
        Parse s value as the number of xor constraints.
        """
        self.__s = int(value)
        return self.__s >=0

    def __parse_q(self, value):
        """
        Parse the q argument for random xor constraints.
        """
        self.__q = float(value)
        return self.__q >=0.0 and self.__q <=1.0

    def __parse_split(self, value):
        """
        Parse the split integer value
        """
        self.__split = int(value)
        return self.__split >=2
    
    def register_options(self, options):
        """
        Extension point to add options to xorro like choosing the
        transformation to apply.

        """
        group = "Xorro Options"
        options.add(group, "approach", _dedent("""\
        Approach to handle XOR constraints [count]
              <arg>: {count|list|tree|countp|up|gje}
                count      : Add count aggregates modulo 2
                {list,tree}: Translate binary XOR operators to rules
                             (binary operators are arranged in list/tree)
                countp     : Propagator simply counting assigned literals
                up         : Propagator implementing unit propagation
                gje        : Propagator implementing Gauss-Jordan Elimination"""), self.__parse_approach)
        
        options.add(group, "cutoff", _dedent("""\
        Percentage of literals assigned before GJE [0-1]"""), self.__parse_cutoff)

        options.add_flag(group, "sampling", _dedent("""\
        Enable sampling by generating random XOR constraints"""), self.__sampling)

        options.add(group, "s", _dedent("""\
        Number of XOR constraints to generate. Default=0, log(#atoms)"""), self.__parse_s)

        options.add(group, "q", _dedent("""\
        Density of each XOR constraint. Default=0.5"""), self.__parse_q)

        options.add_flag(group, "display", _dedent("""\
        Display the random XOR constraints used in sampling"""), self.__display)

        options.add(group, "split", _dedent("""\
        Split XOR constraints to smaller ones of size <n>. Default=0 (off) """), self.__parse_split)

        options.add_flag(group, "pre-gje", _dedent("""\
        Enable GJE preprocessing for XOR constraints"""), self.__pre_gje)

    def main(self, prg, files):
        """
        Implements the rewriting and solving loop.
        """
        models = []

        """
        Transform each input parity constraints into their normal-form
        A parity constraint is in normal-form if:
        1) all the elements within are positive, and
        2) pairs of duplicate elements are removed
        """
        #normal_form(prg,files)

        """
        Sampling features before grounding/solving
        Building random parity constraints and configure clingo control
        """
        
        if self.__sampling.value:
            selected = []
            requested_models = int(str(prg.configuration.solve.models))
            prg.configuration.solve.models = 0

            s = self.__s
            q = self.__q

            cl = _clingo.Control()
            xors = util.generate_random_xors(cl, files, s, q)
            if self.__display.value:
                print(xors)
            files.append("examples/__temp_xors.lp")

        """
        GJE preprocessing
        """
        if self.__pre_gje.value:
            print("Performing GJE preprocessing")
            cl = _clingo.Control()
            xors_lits, xors_parities, all_lits = util.get_xors(cl, files)
            prepro_xors, prepro_pars = util.pre_gje(xors_lits, xors_parities, all_lits, self.__display.value)

            xors = ""
            for i in range(len(prepro_xors)):
                xors = util.build_theory_atoms(xors,prepro_xors[i], prepro_pars[i])
            if self.__display.value:
                ## Display all the XORs after the GJE preprocessing
                print("Simplified parity constraints after GJE")
                print(xors)

            ## Update the files
            files = util.write_file("examples/__pre_gje_.lp", files, xors, "")
            ## Remove the file
            
        """
        Split preprocessing
        """
        if self.__split >=2:
            print("Splitting XORs")
            choice_rule = [None]
            cl = _clingo.Control()
            xors_lits, xors_parities, all_lits = util.get_xors(cl, files)

            if self.__display.value:
                print("Total number of XORs: %s"%len(xors_lits))

            prepro_xors, prepro_pars, choice_rule, splitted = util.split(xors_lits, xors_parities, self.__split, self.__display.value)

            xors = ""
            for i in range(len(prepro_xors)):
                xors = util.build_theory_atoms(xors,prepro_xors[i], prepro_pars[i])
            if self.__display.value:
                if splitted:
                    ## Display all the XORs after the split
                    print("")
                    print("Splitted parity constraints")
                else:
                    print("")
                    print("No parity constraint was split")
                print(xors)
                for choice in choice_rule:
                    print(choice)

            if splitted:
                ## Update the files
                files = util.write_file("examples/__split_.lp", files, xors, choice_rule)
        
        """
        Standard xorro workflow
        """
        transform(prg,files)
        prg.ground([("base", [])])
        translate(self.__approach, prg, self.__cutoff)
        ret = prg.solve(None, lambda model: models.append(model.symbols(shown=True)))

        ## Remove temp files
        if _os.path.exists("examples/__pre_gje_.lp"):
            _os.remove("examples/__pre_gje_.lp")
        if _os.path.exists("examples/__split_.lp"):
            _os.remove("examples/__split_.lp")
        
        """
        Sample from all answer sets remaining in the cluster
        """
        if self.__sampling.value:            
            _os.remove("examples/__temp_xors.lp")
            if requested_models == -1:
                requested_models = 1
            elif requested_models == 0:
                requested_models = len(models)
            if str(ret) == "SAT":
                if requested_models > len(models):
                    requested_models = len(models)
                selected = sorted(sample(range(1, len(models)+1), requested_models))
                print("")
                print("Sampled Answer Set(s): %s"%str(selected)[1:-1])
                for i in range(requested_models):
                    print("Answer: %s"%selected[i])
                    print(' '.join(map(str, sorted(models[selected[i]-1]))))

def main():
    """
    Run the xorro application.
    """
    _sys.exit(int(_clingo.clingo_main(Application("xorro"), _sys.argv[1:])))
