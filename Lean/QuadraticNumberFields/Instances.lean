/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Field and Number Field Instances for Quadratic Algebras over ℚ

This file provides `NumberField` instances for quadratic extensions of `ℚ`.

## Main Instances

* `IsQuadraticField.instNumberField`: Any quadratic field is a number field.
* `QuadraticAlgebra.instIsQuadraticExtension`: Any `QuadraticAlgebra ℚ a b` that is a field
  is a quadratic extension of `ℚ`.

## Implementation Note

The `Module ℚ` instance from the `Field` algebra structure on `QuadraticAlgebra ℚ a b`
coincides with the `QuadraticAlgebra` module structure. This resolves the diamond between
the two `Algebra ℚ` instances (`DivisionRing.toRatAlgebra` vs `QuadraticAlgebra.instAlgebra`).
-/

/-! ## NumberField Instance -/

/-- A quadratic field is a number field: it has characteristic zero
and is finite-dimensional over `ℚ`. -/
instance IsQuadraticField.instNumberField (K : Type*) [Field K] [Algebra ℚ K]
    [IsQuadraticField K] : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    convert FiniteDimensional.of_finrank_pos (K := ℚ) (V := K) (by
      rw [Algebra.IsQuadraticExtension.finrank_eq_two (R := ℚ) (S := K)]; omega) using 1
    congr 1
    exact Subsingleton.elim _ _

/-! ## Quadratic Extension Instances -/

/-- The `Module ℚ` instance from the `Field` algebra structure on `QuadraticAlgebra ℚ a b`
coincides with the `QuadraticAlgebra` module structure. This resolves the diamond between
the two `Algebra ℚ` instances (`DivisionRing.toRatAlgebra` vs `QuadraticAlgebra.instAlgebra`). -/
private theorem QuadraticAlgebra.module_eq (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    (Algebra.toModule : Module ℚ (QuadraticAlgebra ℚ a b)) =
      QuadraticAlgebra.instModule := by
  refine Module.ext' _ _ ?_
  intro r x
  simpa [Algebra.smul_def, QuadraticAlgebra.algebraMap_eq] using
    (QuadraticAlgebra.C_mul_eq_smul (R := ℚ) (a := a) (b := b) r x)

/-- Any `QuadraticAlgebra ℚ a b` that is a field is automatically a quadratic extension
of `ℚ`, i.e., a degree-2 extension. Combined with `IsQuadraticField.instNumberField`,
this gives `NumberField (QuadraticAlgebra ℚ a b)` for free. -/
instance QuadraticAlgebra.instIsQuadraticExtension (a b : ℚ)
    [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) where
  finrank_eq_two' := QuadraticAlgebra.module_eq a b ▸ QuadraticAlgebra.finrank_eq_two a b
