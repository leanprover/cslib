#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Regression checks for the untrusted relation-algebra certificate tooling.

Run from the repository root with Python 3.10+ and a C++20 compiler:
  python3 scripts/RelationAlgebra/test_count.py
"""

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import count
import count_lean


class ReasonCertificates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        temporary = tempfile.TemporaryDirectory(prefix="cslib-ra-test-")
        cls.addClassCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        subprocess.run(
            [sys.executable, str(Path(__file__).with_name("count.py")),
             "--row", "I1S2N0", "--data-dir", str(directory), "--verify"],
            check=True, stdout=subprocess.DEVNULL,
        )
        cls.valid = json.loads((directory / "I1S2N0.json").read_text())

    def setUp(self):
        self.data = deepcopy(self.valid)

    def node(self, tag):
        return next(node for node in self.data["nodes"] if node[0] == tag)

    def reject(self):
        with self.assertRaises(ValueError):
            count.verify_tree(self.data)

    def test_valid_count(self):
        count.validate_problem(self.data)
        self.assertEqual(count.verify_tree(self.data), 7)
        self.assertEqual(self.data["format"], 3)

    def test_obsolete_format(self):
        self.data["format"] = 1
        with self.assertRaises(ValueError):
            count.validate_problem(self.data)
        with self.assertRaises(ValueError):
            count_lean.render("I1S2N0", self.data)

    def test_unknown_format(self):
        self.data["format"] = 4
        with self.assertRaises(ValueError):
            count.validate_problem(self.data)

    def test_obsolete_unbundled_format(self):
        self.data["format"] = 2
        with self.assertRaises(ValueError):
            count.validate_problem(self.data)

    def test_invalid_reason_index(self):
        self.node(3)[3] = len(self.data["reasons"])
        self.reject()

    def test_invalid_constraint_index(self):
        self.data["reasons"][0][0] = (
            len(self.data["equations"]) + len(self.data["permutations"])
        )
        self.reject()

    def test_incorrect_reason_polarity(self):
        reason = self.data["reasons"][self.node(3)[3]]
        reason[1] = not reason[1]
        self.reject()

    def test_insufficient_reason_requirements(self):
        reason = self.data["reasons"][self.node(3)[3]]
        reason[2:] = [0, 0]
        self.reject()

    def test_unbounded_reason_requirements(self):
        self.data["reasons"][0][2] |= 1 << len(self.data["basis"])
        self.reject()

    def test_positive_reason_cannot_force(self):
        self.node(3)[3] = next(
            index for index, reason in enumerate(self.data["reasons"]) if reason[1]
        )
        self.reject()

    def test_negative_reason_cannot_retire(self):
        self.data["bundles"][0][0][0] = next(
            index for index, reason in enumerate(self.data["reasons"]) if not reason[1]
        )
        self.reject()

    def test_missing_bundles(self):
        del self.data["bundles"]
        self.reject()

    def test_empty_bundle(self):
        self.data["bundles"][0][0] = []
        self.reject()

    def test_invalid_bundled_reason_index(self):
        self.data["bundles"][0][0][0] = len(self.data["reasons"])
        self.reject()

    def test_repeated_bundled_constraint(self):
        sequence = self.data["bundles"][0][0]
        sequence.append(sequence[0])
        self.reject()

    def test_forged_bundle_constraint_mask(self):
        self.data["bundles"][0][1] ^= 1
        self.reject()

    def test_forged_bundle_requirements(self):
        self.data["bundles"][0][2] ^= 1
        self.reject()

    def test_invalid_bundle_index(self):
        self.node(4)[3] = len(self.data["bundles"])
        self.reject()

    def test_bundle_requirements_must_match_current_cube(self):
        root = self.data["nodes"][self.data["root"]]
        self.assertEqual(root[0], 4)
        root[3] = next(index for index, bundle in enumerate(self.data["bundles"])
                       if bundle[2] or bundle[3])
        self.reject()

    def test_inactive_constraint_cannot_be_retired(self):
        root = self.data["root"]
        self.assertEqual(self.data["nodes"][root][0], 4)
        witness = self.data["nodes"][root][3]
        self.data["nodes"].append([4, 0, 0, witness, root, 0, self.data["count"]])
        self.data["root"] = len(self.data["nodes"]) - 1
        self.reject()

    def test_invalid_assignment_index(self):
        self.node(2)[1] = len(self.data["basis"])
        self.reject()

    def test_invalid_forced_value(self):
        self.node(3)[2] = 2
        self.reject()

    def test_cyclic_node(self):
        root = self.data["root"]
        self.data["nodes"][root][4] = root
        self.reject()

    def test_incorrect_node_count(self):
        self.node(0)[6] += 1
        self.reject()

    def test_omitted_associativity_equation(self):
        index = next(i for i, entry in enumerate(self.data["equation_cover"]) if entry >= 0)
        self.data["equation_cover"][index] = -1
        with self.assertRaises(ValueError):
            count.validate_problem(self.data)


if __name__ == "__main__":
    unittest.main()
