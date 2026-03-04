/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import QuadraticNumberFields.Param

/-!
# Uniqueness of Quadratic Field Parameters

This file proves that the squarefree integer parameter `d` of a quadratic field
`ℚ(√d)` is unique up to equality. That is, if `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` with both
`d₁` and `d₂` squarefree, then `d₁ = d₂`.

## Main Results

* `QuadFieldParam.unique`: The main uniqueness theorem.
* `squarefree_eq_of_rat_sq_mul`: Helper lemma relating squarefree integers
  connected by a rational square factor.

## Helper Lemmas

Several technical lemmas about squarefree integers and rational squares support
the main theorem:
* `not_isSquare_neg_one_rat`: `-1` is not a square in `ℚ`.
* `nat_eq_one_of_squarefree_intcast_of_isSquare`: A squarefree integer that is
  a square must be `1`.
* `int_dvd_of_ratio_square`: Divisibility criterion from square ratios.
-/

/-! ## Helper Lemmas -/

/-- `-1` is not a square in `ℚ`. -/
lemma not_isSquare_neg_one_rat : ¬ IsSquare (- (1 : ℚ)) := by
  rintro ⟨r, hr⟩
  have hnonneg : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [hr, hnonneg]

/-- A squarefree integer that is a perfect square (as an integer) must equal `1`. -/
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  rcases hsq with ⟨z, hz⟩
  by_cases huz : IsUnit z
  · rcases Int.isUnit_iff.mp huz with hz1 | hz1
    all_goals
      have hmz : (m : ℤ) = 1 := by simpa [hz1] using hz
      norm_num at hmz
      exact hmz
  · have hsqz2 : Squarefree (z ^ 2) := by simpa [hz, pow_two] using hsm
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 huz
    norm_num at h01

/-- If `d₁/d₂` is a rational square and `d₂` is squarefree, then `d₂ ∣ d₁`. -/
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat

/-- If two squarefree integers are related by `d₁ = d₂ · r²` for rational `r`,
then `d₁ = d₂`. -/
lemma squarefree_eq_of_rat_sq_mul {d₁ d₂ : ℤ}
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂)
    {r : ℚ} (hr : (d₁ : ℚ) = d₂ * r ^ 2) : d₁ = d₂ := by
  have hd₁0 : d₁ ≠ 0 := Squarefree.ne_zero hd₁
  have hd₂0 : d₂ ≠ 0 := Squarefree.ne_zero hd₂
  have hd₁Q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁0
  have hd₂Q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂0
  have hratio : IsSquare ((d₁ : ℚ) / (d₂ : ℚ)) := by
    refine ⟨r, ?_⟩
    calc
      (d₁ : ℚ) / (d₂ : ℚ) = ((d₂ : ℚ) * r ^ 2) / (d₂ : ℚ) := by simp [hr]
      _ = r ^ 2 := by field_simp [hd₂Q]
      _ = r * r := by ring
  have hratio' : IsSquare ((d₂ : ℚ) / (d₁ : ℚ)) := by
    rcases hratio with ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    calc
      (d₂ : ℚ) / (d₁ : ℚ) = ((d₁ : ℚ) / (d₂ : ℚ))⁻¹ := by field_simp [hd₁Q, hd₂Q]
      _ = (s * s)⁻¹ := by simp [hs]
      _ = s⁻¹ * s⁻¹ := by
        have hs0 : s ≠ 0 := by
          intro hs0
          have : ((d₁ : ℚ) / (d₂ : ℚ)) = 0 := by simpa [hs0] using hs
          have hd10 : (d₁ : ℚ) = 0 := by
            field_simp [hd₂Q] at this
            simpa [mul_zero] using this
          exact hd₁Q hd10
        field_simp [hs0]
  have hd21 : d₂ ∣ d₁ := int_dvd_of_ratio_square d₁ d₂ hd₂0 hd₂ hratio
  have hd12 : d₁ ∣ d₂ := int_dvd_of_ratio_square d₂ d₁ hd₁0 hd₁ hratio'
  have hassoc : Associated d₁ d₂ := associated_of_dvd_dvd hd12 hd21
  rcases (Int.associated_iff.mp hassoc) with hEq | hNeg
  · exact hEq
  · have : ((d₁ : ℚ) / d₂) = -1 := by
      rw [hNeg]
      push_cast
      field_simp [hd₂Q]
    exfalso
    exact not_isSquare_neg_one_rat (by rwa [this] at hratio)

/-! ## Main Theorem -/

/-- The squarefree integer parameter of a quadratic field is unique:
    `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` with both squarefree implies `d₁ = d₂`. -/
theorem QuadFieldParam.unique {d₁ d₂ : ℤ}
    [h₁ : QuadFieldParam d₁] [h₂ : QuadFieldParam d₂]
    (φ : Qsqrtd (d₁ : ℚ) ≃ₐ[ℚ] Qsqrtd (d₂ : ℚ)) : d₁ = d₂ := by
  set a := (φ ⟨0, 1⟩).re
  set b := (φ ⟨0, 1⟩).im
  have hε_sq : (⟨0, 1⟩ : Qsqrtd (d₁ : ℚ)) * ⟨0, 1⟩ = ⟨(d₁ : ℚ), 0⟩ := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  have hφ_sq : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = ⟨(d₁ : ℚ), 0⟩ := by
    rw [← map_mul, hε_sq]
    show φ ⟨(d₁ : ℚ), 0⟩ = ⟨(d₁ : ℚ), 0⟩
    have hleft : (⟨(d₁ : ℚ), 0⟩ : Qsqrtd (d₁ : ℚ)) =
        algebraMap ℚ (Qsqrtd (d₁ : ℚ)) (d₁ : ℚ) := by
      ext <;> simp
    have hright : (⟨(d₁ : ℚ), 0⟩ : Qsqrtd (d₂ : ℚ)) =
        algebraMap ℚ (Qsqrtd (d₂ : ℚ)) (d₁ : ℚ) := by
      ext <;> simp
    rw [hleft, hright]
    exact φ.commutes (d₁ : ℚ)
  have hφ_eta : φ ⟨0, 1⟩ = ⟨a, b⟩ := by ext <;> rfl
  have hre : a ^ 2 + (d₂ : ℚ) * b ^ 2 = d₁ := by
    have := congr_arg QuadraticAlgebra.re hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this; simp at this; nlinarith
  have him : 2 * a * b = 0 := by
    have := congr_arg QuadraticAlgebra.im hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this; simp at this; linarith
  have hb : b ≠ 0 := by
    intro hb0; simp [hb0] at hre
    have : IsSquare ((d₁ : ℤ) : ℚ) := ⟨a, by nlinarith⟩
    exact (QuadFieldParam.not_isSquare d₁) (Rat.isSquare_intCast_iff.mp this)
  have ha : a = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact absurd h hb
  have hr : (d₁ : ℚ) = d₂ * b ^ 2 := by nlinarith [hre, ha]
  exact squarefree_eq_of_rat_sq_mul h₁.squarefree h₂.squarefree hr
