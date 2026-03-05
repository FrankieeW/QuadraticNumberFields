/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Param
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Field and Number Field Instances

This file equips `QuadraticNumberFields d` with the `Field` and `NumberField`
typeclass instances, establishing that quadratic fields are indeed number fields.

## Main Definitions

* `QuadraticNumberFields d`: Type alias for `Qsqrtd (d : ℚ)` with `[QuadFieldParam d]`.

## Implementation Note

This file is separated from `Basic.lean` for organizational clarity in this
standalone library. If this code is merged into mathlib, these instances
should be moved into `Basic.lean` following mathlib conventions.

## Main Instances

* `Field (QuadraticNumberFields d)`: `Q(√d)` is a field for valid parameters.
* `NumberField (QuadraticNumberFields d)`: `Q(√d)` is a number field
  (characteristic zero, finite-dimensional over ℚ).
* `Algebra.IsQuadraticExtension ℚ (QuadraticNumberFields d)`: `Q(√d)/ℚ` is a
  degree-2 extension, aligning with mathlib's `Algebra.IsQuadraticExtension`.
-/

/-- The quadratic number field `Q(√d)` as a type, for valid parameter `d`. -/
abbrev QuadraticNumberFields (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

/-- `Q(√d)` is a field for any valid parameter `d`. -/
instance {d : ℤ} [QuadFieldParam d] : Field (QuadraticNumberFields d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by nlinarith [hr]⟩
    exact (QuadFieldParam.not_isSquare d) (Rat.isSquare_intCast_iff.mp hsqQ)
  ⟩
  infer_instance

/-- The `Module ℚ` instance from the `Field` algebra structure on `Q(√d)` coincides with
the `QuadraticAlgebra` module structure. This resolves the diamond between the two paths. -/
private theorem module_eq (d : ℤ) [QuadFieldParam d] :
    (Algebra.toModule : Module ℚ (QuadraticNumberFields d)) =
      QuadraticAlgebra.instModule := by
  refine Module.ext' _ _ ?_
  intro r x
  rw [Algebra.smul_def]
  rw [show (algebraMap ℚ (QuadraticNumberFields d) r) = QuadraticAlgebra.C r by
        ext <;> simp [QuadraticNumberFields]]
  rw [QuadraticAlgebra.C_mul_eq_smul]

/-- `Q(√d)` is a number field: characteristic zero and finite-dimensional over ℚ. -/
instance {d : ℤ} [QuadFieldParam d] : NumberField (QuadraticNumberFields d) where
  to_charZero := by infer_instance
  to_finiteDimensional := by
    letI : Module ℚ (QuadraticNumberFields d) := QuadraticAlgebra.instModule
    have hfinite : Module.Finite ℚ (QuadraticNumberFields d) := by
      infer_instance
    exact module_eq d ▸ hfinite

/-- `Q(√d)/ℚ` is a quadratic extension: free of rank 2 over `ℚ`. -/
instance {d : ℤ} [QuadFieldParam d] :
    Algebra.IsQuadraticExtension ℚ (QuadraticNumberFields d) := by
  constructor
  · exact module_eq d ▸ QuadraticAlgebra.finrank_eq_two (d : ℚ) 0
