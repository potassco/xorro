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
from .countp import CountCheckPropagator
from .watches_up import WatchesUnitPropagator
from .propagate_gje import Propagate_GJE

import sys as _sys
import clingo as _clingo
from textwrap import dedent as _dedent

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
        aux = backend.add_atom()
        backend.add_rule([aux], [ lhs, -rhs])
        backend.add_rule([aux], [-lhs,  rhs])
        return aux

def translate(mode, prg):
    if mode == "count":
        prg.add("__count", [], _dedent("""\
            :- { __parity(ID,even,X) } = N, N\\2!=0, __parity(ID,even).
            :- { __parity(ID,odd ,X) } = N, N\\2!=1, __parity(ID,odd).
            """))
        prg.ground([("__count", [])])

    elif mode == "countp":
        prg.register_propagator(CountCheckPropagator())

    elif mode == "up":
        prg.register_propagator(WatchesUnitPropagator())

    elif mode == "gje":
        prg.register_propagator(Propagate_GJE())

    elif mode in ["list", "tree"]:
        def to_list(constraint):
            assert(len(constraint) > 1)
            return util.reduce(Tree, (Leaf(literal) for literal in constraint))

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
                    tree = to_list(constraint) if mode == "list" else to_tree(constraint)
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

    def __parse_approach(self, value):
        """
        Parse approach argument.
        """
        self.__approach = str(value)
        return self.__approach in ["count", "list", "tree", "countp", "up", "gje"]

    def register_options(self, options):
        """
        Extension point to add options to xorro like choosing the
        transformation to apply.

        """
        group = "Xorro Options"
        options.add(group, "approach", _dedent("""\
        Approach to solve XOR constraints [count]
              <arg>: {count|list|tree|countp|up|gje}
        """), self.__parse_approach)

        # TODO: belongs into option documentation not in comments
        #count: count aggregate modulo 2.
        #list: ordered list evaluation.
        #tree: bst evaluation in a bottom-up fashion.
        #countp: count after propagation.
        #up: unit propagation.
        #gje: gauss-jordan elimination.

    def main(self, prg, files):
        """
        Implements the rewriting and solving loop.
        """
        with prg.builder() as b:
            files = [open(f) for f in files]
            if len(files) == 0:
                files.append(_sys.stdin)
            _tf.transform((f.read() for f in files), b.add)

        prg.ground([("base", [])])

        translate(self.__approach, prg)

        prg.solve()

def main():
    """
    Run the xorro application.
    """
    _sys.exit(int(_clingo.clingo_main(Application("xorro"), _sys.argv[1:])))
