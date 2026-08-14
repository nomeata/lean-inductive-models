#!/usr/bin/env python3

import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).with_name("generate_family_adapter_fixtures.py")
SPEC = importlib.util.spec_from_file_location("family_adapter_fixture_generator", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GENERATOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GENERATOR
SPEC.loader.exec_module(GENERATOR)


class FamilyAdapterFixtureGeneratorTest(unittest.TestCase):
    def test_render_is_deterministic(self) -> None:
        matrix = GENERATOR.FixtureMatrix(
            arities=(0, 1, 3),
            member_counts=(1, 3),
            constructor_counts=(0, 3),
            index_arities=(0, 2),
        )
        self.assertEqual(matrix.render(), matrix.render())

    def test_arities_are_samples_not_limits(self) -> None:
        source = GENERATOR.FixtureMatrix(
            arities=(11,),
            member_counts=(7,),
            constructor_counts=(9,),
            index_arities=(4,),
        ).render()
        self.assertIn("GeneratedDirect11", source)
        self.assertIn("child10", source)
        self.assertIn("GeneratedMutual7x11_6", source)
        self.assertIn("GeneratedConstructors9x11", source)
        self.assertIn("GeneratedIndexed4x11", source)

    def test_defaults_cross_former_boundaries(self) -> None:
        source = GENERATOR.FixtureMatrix(
            arities=GENERATOR.DEFAULT_ARITIES,
            member_counts=GENERATOR.DEFAULT_MEMBER_COUNTS,
            constructor_counts=GENERATOR.DEFAULT_CONSTRUCTOR_COUNTS,
            index_arities=GENERATOR.DEFAULT_INDEX_ARITIES,
        ).render()
        for arity in (0, 1, 2, 3, 5, 8):
            self.assertIn(f"GeneratedDirect{arity}", source)
        self.assertIn("GeneratedMutual3x8_2", source)
        self.assertIn("GeneratedConstructors3x8", source)
        self.assertIn("GeneratedIndexed3x8", source)

    def test_zero_cardinalities_remain_well_formed_source_cases(self) -> None:
        source = GENERATOR.FixtureMatrix(
            arities=(0,), member_counts=(0,), constructor_counts=(0,), index_arities=(0,)
        ).render()
        self.assertIn("inductive GeneratedConstructors0x0 : Type", source)
        self.assertIn("inductive GeneratedIndexed0x0 : Type where", source)
        self.assertNotIn("GeneratedMutual0", source)


if __name__ == "__main__":
    unittest.main()
