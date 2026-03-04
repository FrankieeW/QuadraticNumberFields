/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import QuadraticNumberFields.Basic

/-!
# Rescaling Isomorphisms for Quadratic Fields

This file establishes isomorphisms between quadratic fields with related parameters.
The key insight is that `ℚ(√d) ≅ ℚ(√(a²d))` for any nonzero `a ∈ ℚ`, allowing us
to normalize parameters.

## Main Definitions

* `rescale d a ha`: An algebra isomorphism `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` given by
  `⟨r, s⟩ ↦ ⟨r, s·a⁻¹⟩`.

## Main Theorems

* `Qsqrtd_iso_int_param`: Every `Q(√d)` is isomorphic to some `Q(√z)` with `z ∈ ℤ`.
* `Qsqrtd_iso_squarefree_int_param`: Every `Q(√d)` is isomorphic to some `Q(√z)`
  with `z` a squarefree integer.

These results allow us to work exclusively with squarefree integer parameters
when classifying quadratic fields.
-/

/-! ## Rescaling Isomorphism -/

/-- `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` via `⟨r, s⟩ ↦ ⟨r, s·a⁻¹⟩`.

This shows that scaling the parameter by a rational square yields an
isomorphic quadratic field. -/
def rescale (d : ℚ) (a : ℚ) (ha : a ≠ 0) :
    QuadraticAlgebra ℚ d 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (a ^ 2 * d) 0 := by
  have h1d : (1 : QuadraticAlgebra ℚ d 0) = ⟨1, 0⟩ := by ext <;> rfl
  have h1a : (1 : QuadraticAlgebra ℚ (a ^ 2 * d) 0) = ⟨1, 0⟩ := by
    ext <;> rfl
  exact AlgEquiv.ofLinearEquiv
    { toFun := fun x => ⟨x.re, x.im * a⁻¹⟩
      invFun := fun y => ⟨y.re, y.im * a⟩
      map_add' := by intro x y; ext <;> simp [add_mul]
      map_smul' := by intro c x; ext <;> simp [mul_assoc]
      left_inv := by
        intro x; ext <;> simp [mul_assoc, inv_mul_cancel₀ ha]
      right_inv := by
        intro y; ext <;> simp [mul_assoc, mul_inv_cancel₀ ha] }
    (by simp [h1d, h1a])
    (by intro x y; ext <;> simp <;> field_simp)

/-! ## Integer Parameter Normalization -/

/-- Every quadratic field `Q(√d)` is isomorphic to one with an integer parameter:
`∃ z ∈ ℤ, Q(√d) ≃ₐ[ℚ] Q(√z)`. -/
theorem Qsqrtd_iso_int_param (d : ℚ) :
    ∃ z : ℤ, Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨m, n, hn0, hd⟩ : ∃ m n : ℤ, n ≠ 0 ∧ d = m / n := by
    have hd := ne_of_gt (Rat.den_pos d)
    exact ⟨d.num, d.den, Int.ofNat_ne_zero.mpr hd, (Rat.num_div_den d).symm⟩
  use m * n
  have ha : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hrescale : Qsqrtd d ≃ₐ[ℚ] Qsqrtd (n ^ 2 * d) := rescale d n ha
  have heq : (n : ℚ) ^ 2 * d = m * n := by
    rw [hd]
    field_simp [mul_assoc]
  have hcast : (m * n : ℚ) = (m * n : ℤ) := (Int.cast_mul m n).symm
  exact ⟨hrescale.trans (AlgEquiv.cast (by rw [heq, hcast]))⟩

/-- Every quadratic field `Q(√d)` is isomorphic to one with a *squarefree* integer
parameter: `∃ z ∈ ℤ, Squarefree z ∧ Q(√d) ≃ₐ[ℚ] Q(√z)`. -/
theorem Qsqrtd_iso_squarefree_int_param {d : ℤ} (hd : d ≠ 0) :
    ∃ z : ℤ, Squarefree z ∧ Nonempty (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨a, b, heq, ha⟩ := Nat.sq_mul_squarefree d.natAbs
  have hb : b ≠ 0 := by
    intro hb; subst hb; simp at heq
    exact hd (Int.natAbs_eq_zero.mp heq.symm)
  refine ⟨d.sign * ↑a, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs]
    rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hd, Int.natAbs_natCast, one_mul]
  · have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hrescale := rescale (↑d) (↑b)⁻¹ (inv_ne_zero hbQ)
    have hd_int : d = d.sign * (↑b ^ 2 * ↑a) := by
      conv_lhs => rw [(Int.sign_mul_natAbs d).symm]
      congr 1; exact_mod_cast heq.symm
    have hkey : ((↑b : ℚ)⁻¹) ^ 2 * (↑d : ℚ) = ↑(d.sign * (↑a : ℤ)) := by
      have hd_rat : (d : ℚ) = (d.sign : ℚ) * ((b : ℚ) ^ 2 * (a : ℚ)) := by
        exact_mod_cast hd_int
      rw [hd_rat]; field_simp; push_cast; rfl
    exact ⟨hrescale.trans
      (AlgEquiv.cast (A := fun d => QuadraticAlgebra ℚ d 0) hkey)⟩
