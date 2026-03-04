/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import QuadraticNumberFields.Basic

/-!
# Parameterization of Quadratic Fields

This file defines `QuadFieldParam d`, the class of valid parameters for quadratic
number fields `ℚ(√d)`. A valid parameter is a squarefree integer `d ≠ 1`.

## Main Definitions

* `QuadFieldParam d`: Class asserting that `d` is a squarefree integer with `d ≠ 1`.
* `Qsqrtd.zero_not_isReduced`: `Q(√0)` is not reduced (has nilpotents).
* `Qsqrtd.zero_not_isField`: `Q(√0)` is not a field.
* `Qsqrtd.one_not_isField`: `Q(√1) ≅ ℚ × ℚ` is not a field.

## Main Theorems

* `QuadFieldParam.ne_zero`: Squarefree implies nonzero.
* `QuadFieldParam.not_isSquare`: For a valid parameter `d`, `d` is not a perfect square.
* `QuadFieldParam.of_squarefree_ne_one`: Any squarefree `d ≠ 1` is a valid parameter.
* `QuadFieldParam.of_prime`: Any prime gives a valid parameter.
* `QuadFieldParam.of_natAbs_prime`: If `|d|` is prime, `d` is a valid parameter.

## Instances

We provide instances for common parameters: `-1`, `-3`, and any prime or
squarefree `d ≠ 1` via `Fact`.
-/

/-! ## Non-field degeneracies -/

namespace Qsqrtd

/-- `Q(√0)` is not reduced because `√0² = 0` but `√0 ≠ 0`. -/
lemma zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq; exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

/-- `Q(√0)` is not a field (it has nilpotents). -/
lemma zero_not_isField : ¬ IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

/-- `Q(√1) ≅ ℚ × ℚ` is not a field (it has zero divisors). -/
lemma one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h; exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

end Qsqrtd

/-! ## Quadratic Field Parameters -/

/-- Parameters for `Q(√d)`.
`d ≠ 0` is not stored as a field, since it follows from `squarefree`
via `Squarefree.ne_zero`. -/
class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_one : d ≠ 1

namespace QuadFieldParam

/-- For a quadratic parameter, nonzero follows from squarefreeness. -/
lemma ne_zero (d : ℤ) [QuadFieldParam d] : d ≠ 0 :=
  (QuadFieldParam.squarefree (d := d)).ne_zero

/-- For a valid parameter `d`, the integer `d` is not a perfect square. -/
lemma not_isSquare (d : ℤ) [QuadFieldParam d] : ¬ IsSquare d := by
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

/-- Any squarefree `d ≠ 1` is a valid quadratic-field parameter. -/
lemma of_squarefree_ne_one (d : ℤ) (hd : Squarefree d) (h1 : d ≠ 1) :
    QuadFieldParam d :=
  { squarefree := hd, ne_one := h1 }

/-- A prime integer gives a valid quadratic-field parameter. -/
lemma of_prime (d : ℤ) (hd : Prime d) : QuadFieldParam d := by
  refine of_squarefree_ne_one d hd.squarefree ?_
  intro h1
  exact hd.not_unit (h1 ▸ isUnit_one)

/-- If `|d|` is prime, then `d` is a valid quadratic-field parameter. -/
lemma of_natAbs_prime (d : ℤ) (hd : Nat.Prime d.natAbs) :
    QuadFieldParam d :=
  of_prime d (Int.prime_iff_natAbs_prime.2 hd)

end QuadFieldParam

/-! ## Common Quadratic Field Parameters

Instances for frequently used squarefree integers.
-/

/-- Instance for any `d` where `|d|` is prime (via `Fact`). -/
instance (d : ℤ) [Fact (Nat.Prime d.natAbs)] : QuadFieldParam d :=
  QuadFieldParam.of_natAbs_prime d (Fact.out)

/-- Instance for any squarefree `d ≠ 1` (via `Fact`). -/
instance (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : QuadFieldParam d :=
  QuadFieldParam.of_squarefree_ne_one d (Fact.out) (Fact.out)

/-- The Gaussian field `Q(√(-1)) = Q(i)` has valid parameter `-1`. -/
instance : QuadFieldParam (-1) where
  squarefree := by simp
  ne_one := by decide

/-- The Eisenstein field `Q(√(-3))` has valid parameter `-3`. -/
instance : QuadFieldParam (-3 : ℤ) := by
  letI : Fact (Nat.Prime ((-3 : ℤ).natAbs)) := ⟨by decide⟩
  exact inferInstance
