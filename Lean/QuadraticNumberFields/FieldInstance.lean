/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Param
import Mathlib.NumberTheory.NumberField.Basic

abbrev QuadraticNumberFields (d : ℤ) [QuadFieldParam d] : Type := Qsqrtd (d : ℚ)

instance {d : ℤ} [QuadFieldParam d] : Field (QuadraticNumberFields d) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) := ⟨by
    intro r hr
    have hsqQ : IsSquare ((d : ℤ) : ℚ) := ⟨r, by nlinarith [hr]⟩
    exact (not_isSquare_int d) (Rat.isSquare_intCast_iff.mp hsqQ)
  ⟩
  infer_instance

-- /-- A number field is a field which has characteristic zero and is finite
-- dimensional over ℚ. -/
-- @[stacks 09GA]
-- class NumberField (K : Type*) [Field K] : Prop where
--   [to_charZero : CharZero K]
--   [to_finiteDimensional : FiniteDimensional ℚ K]


instance {d : ℤ} [QuadFieldParam d] : NumberField (QuadraticNumberFields d) where
  to_charZero := by infer_instance
  to_finiteDimensional := by
    have hmod :
        (Algebra.toModule : Module ℚ (QuadraticNumberFields d)) =
          QuadraticAlgebra.instModule := by
      refine Module.ext' _ _ ?_
      intro r x
      rw [Algebra.smul_def]
      rw [show (algebraMap ℚ (QuadraticNumberFields d) r) = QuadraticAlgebra.C r by
            ext <;> simp [QuadraticNumberFields]]
      rw [QuadraticAlgebra.C_mul_eq_smul]
    letI : Module ℚ (QuadraticNumberFields d) := QuadraticAlgebra.instModule
    have hfinite : Module.Finite ℚ (QuadraticNumberFields d) := by
      infer_instance
    exact hmod ▸ hfinite

