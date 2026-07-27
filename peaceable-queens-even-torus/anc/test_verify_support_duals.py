#!/usr/bin/env python3
"""Fail-closed regression tests for the independent E1 verifier."""

from __future__ import annotations

import json
import unittest
from fractions import Fraction

import verify_support_duals as verifier


class E1VerifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rows = verifier.derive_moment_rows()

    def test_exact_simplex_handles_all_three_outcomes(self) -> None:
        self.assertEqual(
            verifier.exact_simplex_self_test(),
            {"passed": True, "tests": 3},
        )

    def test_moment_model_shape_and_geometry(self) -> None:
        self.assertEqual(len(self.rows), 42)
        self.assertTrue(all(len(row.columns) == 64 for row in self.rows))
        audit = verifier.audit_torus_fibers(5)
        self.assertTrue(audit["passed"])
        self.assertEqual(audit["aggregate_DA_determinant"], 2)

    def test_delivered_witness_mutation_is_rejected(self) -> None:
        raw = json.loads(verifier.DEFAULT_NEW_CUTS.read_text(encoding="utf-8"))[0]
        polynomial, alpha, dual = verifier.parse_new_cut_record(raw, 0, len(self.rows))
        self.assertTrue(verifier.verify_witness(self.rows, polynomial, alpha, dual)["passed"])
        mutated = list(dual)
        mutated[0] += 1
        check = verifier.verify_witness(self.rows, polynomial, alpha, mutated)
        self.assertFalse(check["polynomial_consistency"])
        self.assertFalse(check["passed"])

    def test_column_support_violation_is_rejected(self) -> None:
        zero_dual = [Fraction(0) for _ in self.rows]
        check = verifier.verify_witness(
            self.rows,
            {},
            Fraction(1, 2),
            zero_dual,
        )
        self.assertTrue(check["polynomial_consistency"])
        self.assertFalse(check["columnwise_support"])
        self.assertFalse(check["passed"])
        self.assertEqual(check["violating_columns"], [0, 15, 16, 31, 32, 47, 48, 63])

    def test_frozen_legacy_witnesses_reverify(self) -> None:
        raw_polynomials = verifier.load_json_strict(verifier.DEFAULT_BENDERS_CUTS)
        polynomials = verifier.parse_legacy_polynomials(raw_polynomials)
        recovery = verifier.load_json_strict(verifier.DEFAULT_RECOVERED)
        self.assertTrue(recovery["complete"])
        self.assertEqual(len(recovery["cuts"]), 76)
        for index, (polynomial, record) in enumerate(zip(polynomials, recovery["cuts"])):
            alpha, dual, interval = verifier.parse_recovered_record(
                record,
                index,
                polynomial,
                len(self.rows),
            )
            self.assertEqual(interval[0], interval[1])
            self.assertEqual(alpha, interval[0])
            self.assertTrue(
                verifier.verify_witness(self.rows, polynomial, alpha, dual)["passed"],
                f"legacy cut {index}",
            )


if __name__ == "__main__":
    unittest.main()
