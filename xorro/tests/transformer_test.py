import unittest
import sys

class TestCase(unittest.TestCase):
    def assertRaisesRegex(self, *args, **kwargs):
        return (self.assertRaisesRegexp(*args, **kwargs)
            if sys.version_info[0] < 3
            else unittest.TestCase.assertRaisesRegex(self, *args, **kwargs))

class TestProgramTransformer(TestCase):
    def test_transform(self):
        self.assertFalse("implement a first test case!")
