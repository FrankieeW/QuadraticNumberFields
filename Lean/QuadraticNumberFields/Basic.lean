/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Trace.Basic
import Init.Data.Rat.Basic

/-!
# Basic Definitions for Quadratic Number Fields

This file provides the fundamental type `Qsqrtd d` representing the quadratic
field `ℚ(√d)` for a rational parameter `d`, along with basic operations:
trace, norm, and the canonical embedding of ℚ.

## Main Definitions

* `IsQuadraticField K`: A predicate asserting that `K` is a quadratic extension of ℚ.
* `Qsqrtd d`: The quadratic algebra `QuadraticAlgebra ℚ d 0`, representing `ℚ(√d)`.
* `Qsqrtd.trace`: The trace `Tr(x)`, defined via mathlib's `Algebra.trace`.
* `Qsqrtd.norm`: The norm `N(x) = x · x̄ = x.re² - d · x.im²`.
* `Qsqrtd.embed`: The canonical embedding `ℚ → Q(√d)`.
* `not_isSquare_ratCast_of_squarefree_ne_one`: squarefree integer parameters
  with `d ≠ 1` give genuine quadratic fields.
-/

/-- A field `K` is a quadratic field if it is a quadratic extension of `ℚ`. -/
abbrev IsQuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  Algebra.IsQuadraticExtension ℚ K

/-- The quadratic field `ℚ(√d)` as a type alias for `QuadraticAlgebra ℚ d 0`. -/
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0
notation "ℚ√" d => Qsqrtd d

namespace Qsqrtd

/-- The trace of an element `x : Q(√d)`, defined via `Algebra.trace`. -/
noncomputable abbrev trace (x : Qsqrtd d) : ℚ := Algebra.trace ℚ (Qsqrtd d) x

/-- `Qsqrtd.trace` is definitionally mathlib's algebra trace. -/
theorem trace_eq_algebra_trace (x : Qsqrtd d) :
    Qsqrtd.trace x = Algebra.trace ℚ (Qsqrtd d) x := rfl

private theorem leftMulMatrix_eq (x : Qsqrtd d) :
    Algebra.leftMulMatrix (QuadraticAlgebra.basis d 0) x = !![x.re, d * x.im; x.im, x.re] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

/-- The trace in `Q(√d)` is `x + x̄`. -/
@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Qsqrtd.trace x = x.re + (star x).re := by
  change Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0), leftMulMatrix_eq,
    Matrix.trace_fin_two_of]
  simp

/-- In the model `Q(√d) = QuadraticAlgebra ℚ d 0`, the trace is `2 * re`. -/
@[simp] theorem trace_eq_two_re (x : Qsqrtd d) :
    Qsqrtd.trace x = 2 * x.re := by
  rw [trace_eq_re_add_re_star]
  simp
  ring

/-- The norm of an element `x : Q(√d)`, defined as `N(x) = x · x̄ = x.re² - d · x.im²`. -/
abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- The canonical embedding of ℚ into `Q(√d)`, mapping `r ↦ r + 0·√d`. -/
abbrev embed (r : ℚ) : Qsqrtd d := algebraMap ℚ (Qsqrtd d) r

end Qsqrtd

/-! ## Parameter Lemmas -/

/-- `Q(√0)` is not reduced because `√0² = 0` but `√0 ≠ 0`. -/
lemma Qsqrtd.zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq
    exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

/-- `Q(√0)` is not a field (it has nilpotents). -/
lemma Qsqrtd.zero_not_isField : ¬ IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact Qsqrtd.zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

/-- `Q(√1) ≅ ℚ × ℚ` is not a field (it has zero divisors). -/
lemma Qsqrtd.one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h
    exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h
    exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

/-- A squarefree integer that is a perfect square must equal `1`. -/
lemma eq_one_of_squarefree_isSquare {d : ℤ} (hd : Squarefree d) (hsq : IsSquare d) : d = 1 := by
  rcases hsq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · simpa [hz1] using hz
    · simpa [hz1] using hz
  · have hsqz2 : Squarefree (z ^ 2) := by
      simpa [hz, pow_two] using hd
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

/-- For a squarefree integer `d ≠ 1`, `d` is not a perfect square in `ℤ`. -/
lemma not_isSquare_int_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare d := by
  intro hdSq
  exact h1 (eq_one_of_squarefree_isSquare hd hdSq)

/-- For a squarefree integer `d ≠ 1`, `(d : ℚ)` is not a perfect square in `ℚ`. -/
lemma not_isSquare_ratCast_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro hsqQ
  exact not_isSquare_int_of_squarefree_ne_one hd h1 (Rat.isSquare_intCast_iff.mp hsqQ)

/-- Bridge squarefree integer parameters to the field-level non-square condition. -/
instance instFact_not_isSquare_ratCast_of_squarefree_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
  ⟨not_isSquare_ratCast_of_squarefree_ne_one
    (d := d) (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
