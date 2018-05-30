"""
The xorro module contains functions to solve logic programs with parity
constraints.

Classes:
Application -- Main application class.

Functions:
main  -- Main function starting an extended clingo application.
"""

from . import transformer as _tf
from .countp import CountCheckPropagator
from .watches_up import WatchesUnitPropagator
from .propagate_gje import Propagate_GJE

import sys as _sys
import clingo as _clingo
from textwrap import dedent as _dedent

class DummyContext:
    def domain2(self):
        return []

    def domain3(self):
        return []
g_dummy_ctx = DummyContext()

# TODO: Is here more useful to use these classes in both leaf and tree?
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

    elif mode == "gje":
        add_domain(prg)
        prg.register_propagator(Propagate_GJE())

    elif mode == "tree":
        def split(a):            
            if len(a) == 1:
                return [a]
            return [a[i:i+2] for i  in range(0, len(a), 2)]

        def traverse(l, tree):
            if isinstance(tree, Tree):
                if tree._Tree__lhs:
                    l.append(tree._Tree__rhs)
                    traverse(l, tree._Tree__lhs)                                    
            else:
                l.append(tree)
            return l
        
        # TODO: with a little bit of refactoring util.get_xor_constraints can be used
        constraints = {}
        for atom in prg.symbolic_atoms.by_signature(_tf.g_aux_name, 2):
            cid = atom.symbol.arguments[0].number
            par = atom.symbol.arguments[1].name
            constraints[cid] = {"parity": util.get_parity(par), "tree": None}

        for atom in prg.symbolic_atoms.by_signature(_tf.g_aux_name,3):
            constraint = constraints[atom.symbol.arguments[0].number]
            tree = Leaf(atom.literal)
            constraint["tree"] = tree if constraint["tree"] is None else Tree(constraint["tree"], tree)
        
        with prg.backend() as b:
            for constraint in constraints.values():                                
                if constraint["tree"] is None:
                    if constraint["parity"]:
                        b.add_rule([], [])
                else:
                    aux_ = []
                    leaves_ = []
                    leaves_ = traverse(leaves_, constraint["tree"])                    
                    leaves_ = split(leaves_)
                    while True:                    
                        for part in leaves_:
                            if len(part) == 2:
                                tree = Tree(part[0], part[1])
                                aux = tree.translate(b)
                                aux_.append(Leaf(aux))
                            else:
                                aux_+=part
                        if len(aux_) == 1:
                            aux = aux_[0].translate(b)
                            b.add_rule([], [-aux if constraint["parity"] else aux])
                            break                        
                        else:
                            leaves_ = split(aux_)
                            aux_ = []

    elif mode == "list":        

        # TODO: with a little bit of refactoring util.get_xor_constraints can be used
        constraints = {}
        for atom in prg.symbolic_atoms.by_signature(_tf.g_aux_name, 2):
            cid = atom.symbol.arguments[0].number
            par = atom.symbol.arguments[1].name
            constraints[cid] = {"parity": util.get_parity(par), "tree": None}

        for atom in prg.symbolic_atoms.by_signature(_tf.g_aux_name,3):
            constraint = constraints[atom.symbol.arguments[0].number]
            tree = Leaf(atom.literal)
            constraint["tree"] = tree if constraint["tree"] is None else Tree(constraint["tree"], tree)

        with prg.backend() as b:
            for constraint in constraints.values():
                if constraint["tree"] is None:
                    if constraint["parity"]:
                        b.add_rule([], [])
                else:
                    aux = constraint["tree"].translate(b)
                    b.add_rule([], [-aux if constraint["parity"] else aux])

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
