#!/usr/bin/env python3
"""Regression cases for the fail-closed audit output parser; no Lean execution."""
import unittest
from check_axioms import check_output


def block(name="Example.theorem", axioms="propext, Classical.choice, Quot.sound"):
    return (f'"AXIOM_BEGIN|{name}"\n'
            f"'{name}' depends on axioms: [{axioms}]\n"
            f'"AXIOM_END|{name}"\n')


class AuditParserTests(unittest.TestCase):
    def setUp(self):
        self.names = ["Example.theorem"]
        self.good = block()

    def fails(self, text):
        with self.assertRaises(ValueError):
            check_output(text, self.names)

    def test_allowed_axioms(self):
        self.assertEqual(len(check_output(self.good, self.names)), 1)

    def test_no_axioms(self):
        text = self.good.replace("depends on axioms: [propext, Classical.choice, Quot.sound]", "does not depend on any axioms")
        self.assertEqual(check_output(text, self.names)[self.names[0]], [])

    def test_wrapped_axioms(self):
        self.assertEqual(len(check_output(self.good.replace(", ", ",\n "), self.names)), 1)

    def test_unquoted_markers(self):
        self.assertEqual(len(check_output(self.good.replace('"', ''), self.names)), 1)

    def test_sorry(self):
        self.fails(block(axioms="sorryAx"))

    def test_custom_axiom(self):
        self.fails(block(axioms="User.RH"))

    def test_trust_compiler(self):
        self.fails(block(axioms="Lean.ofReduceBool"))

    def test_empty(self):
        self.fails("")

    def test_missing_end(self):
        self.fails(self.good[:self.good.index('"AXIOM_END')])

    def test_wrong_name(self):
        self.fails(self.good.replace("'Example.theorem'", "'Example.other'"))

    def test_duplicate_block(self):
        self.fails(self.good + self.good)

    def test_missing_record(self):
        self.fails('\n'.join(line for line in self.good.splitlines() if "depends on" not in line))

    def test_duplicate_record(self):
        line = self.good.splitlines()[1]
        self.fails(self.good.replace(line, line + "\n" + line))

    def test_extra_block(self):
        self.fails(self.good + block("Example.other"))

    def test_unframed_record(self):
        self.fails(self.good + "'Sneaky' depends on axioms: [propext]\n")

    def test_error(self):
        self.fails("Example.lean:1:0: error: bad\n" + self.good)

    def test_empty_expected(self):
        with self.assertRaises(ValueError):
            check_output("", [])

    def test_wrong_order(self):
        with self.assertRaises(ValueError):
            check_output(block("A") + block("B"), ["B", "A"])


if __name__ == "__main__":
    unittest.main()
