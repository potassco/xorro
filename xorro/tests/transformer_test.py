import unittest
import sys

import xorro
from xorro import transformer
import clingo

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

def solve(s, mode):
    messages = []
    prg = clingo.Control(logger=lambda c, m: messages.append(m))
    with prg.builder() as b:
        transformer.transform([s], b.add)
    prg.ground([("base", [])])

    xorro.translate(mode, prg)

    prg.configuration.solve.models = 0

    models = []
    with prg.solve(yield_=True) as it:
        for m in it:
            models.append([str(sym) for sym in m.symbols(atoms=True) if not sym.name.startswith("__")])
            models[-1].sort()

    models.sort()

    return models

class TestProgramTransformer(TestCase):
    def test_transform(self):
        for mode in ["count"]:
            self.assertEqual(solve("&even{ }.", mode), [[]])
            self.assertEqual(solve("&odd{ }.", mode), [])
            # run one-elementary parity aggregates
            self.assertEqual(solve("{a;b;c}. &even{ a:a;b:b;c:c }.", mode), [[], ["a", "b"], ['a', 'c'], ['b', 'c']])
            # multiple parity aggregates
            # complex conditions
            # ...

