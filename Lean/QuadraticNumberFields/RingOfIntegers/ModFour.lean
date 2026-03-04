/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Param

/-!
# `ModFour` Layer

This file is for congruence criteria modulo `4` used by the ring-of-integers
classification.

## TODO (Revised)

1. Port core lemmas from old draft (`ModFourCriteria.lean`)
- [x] Port `squarefree_int_not_dvd_four`.
- [x] Port `squarefree_int_emod_four`.
- [x] Port `dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four`.
- [x] Port `dvd_four_sub_sq_iff_same_parity_of_one_mod_four`.

2. Branch-conversion API used by classification
- [x] `exists_k_of_mod_four_eq_one : d % 4 = 1 → ∃ k : ℤ, d = 1 + 4 * k`.
- [x] `mod_four_eq_one_of_exists_k : (∃ k : ℤ, d = 1 + 4 * k) → d % 4 = 1`.
- [x] `mod_four_branch_split : d % 4 = 1 ∨ d % 4 ≠ 1`.

3. Consumer-facing interfaces
- [x] Expose branch lemmas with names used directly in `Classification.lean`.
- [ ] Add rewriting helpers so branch goals reduce with minimal `omega` boilerplate.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- A squarefree integer is not divisible by `4`. -/
lemma squarefree_int_not_dvd_four (d : ℤ) (hd : Squarefree d) : ¬ (4 : ℤ) ∣ d := by
  intro h
  have h22 : (2 : ℤ) * 2 ∣ d := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by omega⟩
  have hunit : IsUnit (2 : ℤ) := hd 2 h22
  exact absurd (Int.isUnit_iff.mp hunit) (by omega)

/-- A squarefree integer has `d % 4 ∈ {1, 2, 3}`. -/
lemma squarefree_int_emod_four (d : ℤ) (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hd
  omega

/-- The square of an even integer is `0 mod 4`. -/
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega

/-- The square of an odd integer is `1 mod 4`. -/
lemma Int.sq_emod_four_of_odd (n : ℤ) (h : ¬ 2 ∣ n) : n ^ 2 % 4 = 1 := by
  set k := n / 2
  have hk : n = 2 * k + 1 := by omega
  rw [hk]
  ring_nf
  omega

private lemma div4_iff_mod (a' b' d : ℤ) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (a' ^ 2 - d * b' ^ 2) % 4 = 0 := by
  omega

/-- Main mod-4 criterion for `4 ∣ a'² - d*b'²`. -/
theorem dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one (d a' b' : ℤ) (hd : Squarefree d) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      (2 ∣ a' ∧ 2 ∣ b') ∨ (¬ 2 ∣ a' ∧ ¬ 2 ∣ b' ∧ d % 4 = 1) := by
  have hd4 := squarefree_int_emod_four d hd
  constructor
  · intro hdvd
    have hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0 := (div4_iff_mod a' b' d).1 hdvd
    have even_odd_impossible (ha : 2 ∣ a') (hb : ¬ 2 ∣ b') : False := by
      have hmod' := hmod
      have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) := by
        have ha2 : a' ^ 2 % 4 = 0 := Int.sq_emod_four_of_even a' ha
        omega
      have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := by
        have hb2 : b' ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd b' hb
        omega
      rw [hb_eq] at hmod'
      ring_nf at hmod'
      rcases hd4 with hd1 | hd2 | hd3 <;> omega
    have odd_even_impossible (ha : ¬ 2 ∣ a') (hb : 2 ∣ b') : False := by
      have hmod' := hmod
      have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := by
        have ha2 : a' ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd a' ha
        omega
      have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) := by
        have hb2 : b' ^ 2 % 4 = 0 := Int.sq_emod_four_of_even b' hb
        omega
      rw [ha_eq, hb_eq] at hmod'
      ring_nf at hmod'
      rcases hd4 with hd1 | hd2 | hd3 <;> omega
    have odd_odd_mod_four_one (ha : ¬ 2 ∣ a') (hb : ¬ 2 ∣ b') : d % 4 = 1 := by
      have hmod' := hmod
      have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := by
        have ha2 : a' ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd a' ha
        omega
      have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := by
        have hb2 : b' ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd b' hb
        omega
      rw [ha_eq, hb_eq] at hmod'
      ring_nf at hmod'
      omega
    by_cases ha : 2 ∣ a' <;> by_cases hb : 2 ∣ b'
    · exact Or.inl ⟨ha, hb⟩
    · exfalso
      exact even_odd_impossible ha hb
    · exfalso
      exact odd_even_impossible ha hb
    · exact Or.inr ⟨ha, hb, odd_odd_mod_four_one ha hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd1⟩
    · obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p ^ 2 - d * q ^ 2, by ring⟩
    · have ha_eq : a' = 2 * (a' / 2) + 1 := by omega
      have hb_eq : b' = 2 * (b' / 2) + 1 := by omega
      rw [ha_eq, hb_eq]
      ring_nf
      have hd_eq : d = 4 * (d / 4) + 1 := by omega
      rw [hd_eq]
      ring_nf
      omega

/-- If `d % 4 ≠ 1`, divisibility by `4` forces both numerators even. -/
theorem even_even_of_dvd_four_sub_sq_of_ne_one_mod_four (d a' b' : ℤ) (hd : Squarefree d)
    (hd4 : d % 4 ≠ 1) (h : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    2 ∣ a' ∧ 2 ∣ b' := by
  rcases (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).mp h with
      hab | ⟨_, _, hd1⟩
  · exact hab
  · exact absurd hd1 hd4

/-- If `d % 4 ≠ 1`, divisibility by `4` is equivalent to both numerators even. -/
theorem dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four (d a' b' : ℤ) (hd : Squarefree d)
    (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · intro h
    exact even_even_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd hd4 h
  · intro h
    exact (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).2 (Or.inl h)

/-- If `d % 4 = 1`, divisibility by `4` is equivalent to same parity. -/
theorem dvd_four_sub_sq_iff_same_parity_of_one_mod_four (d a' b' : ℤ) (hd : Squarefree d)
    (hd4 : d % 4 = 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ a' % 2 = b' % 2 := by
  rw [dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb, _⟩) <;> omega
  · intro h
    by_cases ha : 2 ∣ a'
    · left
      exact ⟨ha, by omega⟩
    · right
      exact ⟨ha, by omega, hd4⟩

/-- Extract parameterization `d = 1 + 4k` from `d % 4 = 1`. -/
theorem exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k := by
  refine ⟨d / 4, ?_⟩
  omega

/-- The converse of `exists_k_of_mod_four_eq_one`. -/
theorem mod_four_eq_one_of_exists_k {d : ℤ} (h : ∃ k : ℤ, d = 1 + 4 * k) :
    d % 4 = 1 := by
  rcases h with ⟨k, hk⟩
  omega

/-- Canonical branch split by `d % 4 = 1`. -/
theorem mod_four_branch_split (d : ℤ) : d % 4 = 1 ∨ d % 4 ≠ 1 := by
  by_cases h : d % 4 = 1
  · exact Or.inl h
  · exact Or.inr h

end RingOfIntegers
end QuadraticNumberFields
