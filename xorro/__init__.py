"""
The xorro module contains functions to solve logic programs with parity
constraints.

Classes:
Application -- Main application class.

Functions:
main  -- Main function starting an extended clingo application.
"""

from . import transformer as _tf

import sys as _sys
import clingo as _clingo
from textwrap import dedent as _dedent
from countp import CountCheckPropagator
from watches_up import WatchesUnitPropagator
#from gje import GJEPropagator

class DummyContext:
    def domain2(self):
        return []

    def domain3(self):
        return []
g_dummy_ctx = DummyContext()

def add_domain(prg):
    """
    Adds the domain for the __parity atoms to the program.
    """
    class Context:
        def __init__(self):
            self._domain2 = []
            self._domain3 = []

        def domain2(self):
            return self._domain2

        def domain3(self):
            return self._domain3

    ctx = Context()

    for atom in prg.symbolic_atoms.by_signature(_tf.g_aux_name, 2):
        ctx._domain2.append(_clingo.Tuple(atom.symbol.arguments))
    for atom in prg.symbolic_atoms.by_signature(_tf.g_aux_name, 3):
        ctx._domain3.append(_clingo.Tuple(atom.symbol.arguments))

    prg.add("__domain", [], _dedent("""\
        {name}_dom(Id,Type) :- (Id,Type) = @domain2().
        {name}_dom(Id,Type,Tuple) :- (Id,Type,Tuple) = @domain3().
        """.format(name=_tf.g_aux_name)))

    prg.ground([("__domain", [])], ctx)

def translate(mode, prg):
    if mode == "count":
        add_domain(prg)
        prg.add("__count", [], _dedent("""\
            :- { __parity(ID,even,X) } = N, N\\2!=0, __parity(ID,even).
            :- { __parity(ID,odd ,X) } = N, N\\2!=1, __parity(ID,odd).
            """))
        prg.ground([("__count", [])], g_dummy_ctx)

    elif mode == "countp":
        add_domain(prg)
        prg.register_propagator(CountCheckPropagator())

    elif mode == "up":
        add_domain(prg)
        prg.register_propagator(WatchesUnitPropagator())

    #elif mode == "gje":
    #    add_domain(prg)
    #    prg.register_propagator(GJEPropagator())

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
