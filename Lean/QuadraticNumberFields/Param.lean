/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import QuadraticNumberFields.Basic

lemma Qsqrtd_zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq; exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

lemma Qsqrtd_zero_not_isField : ¬ IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact Qsqrtd_zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

/-- Parameters for `Q(√d)`.
`d ≠ 0` is not stored as a field, since it follows from `squarefree`
via `Squarefree.ne_zero`. -/
class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_one : d ≠ 1

/-- For a quadratic parameter, nonzero follows from squarefreeness. -/
lemma QuadFieldParam.ne_zero (d : ℤ) [QuadFieldParam d] : d ≠ 0 :=
  (QuadFieldParam.squarefree (d := d)).ne_zero

lemma not_isSquare_int (d : ℤ) [QuadFieldParam d] : ¬ IsSquare d := by
  intro hdSq
  rcases hdSq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    · have : d = 1 := by simpa [hz1] using hz
      exact (QuadFieldParam.ne_one (d := d)) this
    · have : d = 1 := by simpa [hz1] using hz
      exact (QuadFieldParam.ne_one (d := d)) this
  · have hsqz2 : Squarefree (z ^ 2) := by
      simpa [hz, pow_two] using (QuadFieldParam.squarefree (d := d))
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

lemma Qsqrtd_one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

/-! ## Common Quadratic Field Parameters

Instances for frequently used squarefree integers.
-/
def QuadFieldParam.mk' (d : ℤ) (hs : Squarefree d) (h1 : d ≠ 1) :
    QuadFieldParam d :=
{ squarefree := hs, ne_one := h1 }

/-- Any squarefree `d ≠ 1` is a valid quadratic-field parameter. -/
@[simp]
lemma quadFieldParam_of_squarefree_ne_one (d : ℤ) (hd : Squarefree d) (h1 : d ≠ 1) :
    QuadFieldParam d :=
  QuadFieldParam.mk' d hd h1

/-- A prime integer gives a valid quadratic-field parameter. -/
@[simp]
lemma quadFieldParam_of_prime (d : ℤ) (hd : Prime d) : QuadFieldParam d := by
  refine quadFieldParam_of_squarefree_ne_one d hd.squarefree ?_
  intro h1
  exact hd.not_unit (h1 ▸ isUnit_one)

/-- If `|d|` is prime, then `d` is a valid quadratic-field parameter. -/
@[simp]
lemma quadFieldParam_of_natAbs_prime (d : ℤ) (hd : Nat.Prime d.natAbs) :
    QuadFieldParam d :=
  quadFieldParam_of_prime d (Int.prime_iff_natAbs_prime.2 hd)

instance (d : ℤ) [Fact (Nat.Prime d.natAbs)] : QuadFieldParam d :=
  quadFieldParam_of_natAbs_prime d (Fact.out)

instance (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : QuadFieldParam d :=
  quadFieldParam_of_squarefree_ne_one d (Fact.out) (Fact.out)

instance : QuadFieldParam (-1) where
  squarefree := by simp
  ne_one := by decide

instance : QuadFieldParam (-3 : ℤ) := by
  letI : Fact (Nat.Prime ((-3 : ℤ).natAbs)) := ⟨by decide⟩
  exact inferInstance

