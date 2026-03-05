/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

Computing ramification index and inertia degree for primes 2 and 3 in ℤ[√-5].
Ported from the ANT project.
-/
import QuadraticNumberFields.Examples.ZsqrtdNeg5.Ideals
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ramification and Inertia in ℤ[√-5]

This file computes the ramification indices and inertia degrees for
the primes 2 and 3 in `ℤ[√-5]`, demonstrating the fundamental identity
`∑ eᵢfᵢ = [K:ℚ]` on a concrete example.

## Main Results

### Ramification Index
* `ramificationIdx_P2`: `e(P2|2) = 2` (ramified)
* `ramificationIdx_P3₁`: `e(P3₁|3) = 1` (unramified)
* `ramificationIdx_P3₂`: `e(P3₂|3) = 1` (unramified)

### Inertia Degree
* `inertiaDeg_P2`: `f(P2|2) = 1`
* `inertiaDeg_P3₁`: `f(P3₁|3) = 1`
* `inertiaDeg_P3₂`: `f(P3₂|3) = 1`

### Summary Table

| Prime | Factorization    | e | f | g |
|-------|-----------------|---|---|---|
| 2     | (2) = P2²       | 2 | 1 | 1 |
| 3     | (3) = P3₁ · P3₂ | 1 | 1 | 2 |

Verification: e × f × g = 2 = [ℚ(√-5) : ℚ] ✓
-/

open Ideal Zsqrtd

namespace QuadraticNumberFields.Examples.ZsqrtdNeg5

/-- The prime ideal (2, 1+√-5) in ℤ[√-5] -/
def P2 : Ideal R := span {2, 1 + sqrtd}

/-- The prime ideal (3, 1+√-5) in ℤ[√-5] -/
def P3₁ : Ideal R := span {3, 1 + sqrtd}

/-- The prime ideal (3, 1-√-5) in ℤ[√-5] -/
def P3₂ : Ideal R := span {3, 1 - sqrtd}

-- ============================================================================
-- Helper lemmas
-- ============================================================================

/-- algebraMap for integers is just coercion -/
@[simp] lemma algebraMap_int_coe (n : ℤ) : algebraMap ℤ R n = n := rfl

/-- span {n} after mapping from ℤ is the same as span {(n : R)} -/
lemma map_span_int_singleton (n : ℤ) :
    map (algebraMap ℤ R) (span {n}) = span {(n : R)} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_int_coe]

/-- Ring hom sending `√-5` to `2` in `ZMod 9`. -/
noncomputable def phiPlus9 : R →+* ZMod 9 :=
  Zsqrtd.lift ⟨(2 : ZMod 9), by decide⟩

/-- Ring hom sending `√-5` to `-2` in `ZMod 9`. -/
noncomputable def phiMinus9 : R →+* ZMod 9 :=
  Zsqrtd.lift ⟨((-2 : ℤ) : ZMod 9), by decide⟩

lemma map_P3₁_le_span3_mod9 :
    map phiPlus9 P3₁ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) := by
  unfold P3₁
  rw [Ideal.map_span, Ideal.span_le]
  intro y hy
  rw [Set.image_pair] at hy
  rcases hy with rfl | rfl
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩

lemma map_P3₂_le_span3_mod9 :
    map phiMinus9 P3₂ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) := by
  unfold P3₂
  rw [Ideal.map_span, Ideal.span_le]
  intro y hy
  rw [Set.image_pair] at hy
  rcases hy with rfl | rfl
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩
  · exact Ideal.mem_span_singleton.mpr ⟨1, by decide⟩

lemma not_span3_le_P3₁_sq : ¬(span ({(3 : R)} : Set R) : Ideal R) ≤ P3₁ ^ (1 + 1) := by
  intro h
  have hmap : map phiPlus9 (span ({(3 : R)} : Set R)) ≤ map phiPlus9 (P3₁ ^ (1 + 1)) :=
    Ideal.map_mono h
  have hsq : map phiPlus9 (P3₁ ^ (1 + 1)) ≤ ⊥ := by
    calc
      map phiPlus9 (P3₁ ^ (1 + 1)) = (map phiPlus9 P3₁) ^ (1 + 1) := by
        simpa using (Ideal.map_pow phiPlus9 P3₁ (1 + 1))
      _ = map phiPlus9 P3₁ * map phiPlus9 P3₁ := by simp [pow_two]
      _ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) * span ({(3 : ZMod 9)} : Set (ZMod 9)) :=
        Ideal.mul_mono map_P3₁_le_span3_mod9 map_P3₁_le_span3_mod9
      _ = (span ({(3 : ZMod 9)} : Set (ZMod 9)) : Ideal (ZMod 9)) ^ (1 + 1) := by
        simp [pow_two]
      _ = ⊥ := by
        have h9 : ((3 : ZMod 9) ^ 2) = 0 := by decide
        rw [Ideal.span_singleton_pow, h9, Ideal.span_singleton_eq_bot]
  have hbot : map phiPlus9 (span ({(3 : R)} : Set R)) = ⊥ :=
    le_bot_iff.mp (hmap.trans hsq)
  have hzero : ((3 : ZMod 9)) = 0 := by
    have hphi3 : (phiPlus9 (3 : R) : ZMod 9) = 3 := by simp [phiPlus9]
    have hzero' : (phiPlus9 (3 : R) : ZMod 9) = 0 := by
      apply (Ideal.span_singleton_eq_bot.mp _)
      simpa [Ideal.map_span] using hbot
    simpa [hphi3] using hzero'
  exact (by decide : (3 : ZMod 9) ≠ 0) hzero

lemma not_span3_le_P3₂_sq : ¬(span ({(3 : R)} : Set R) : Ideal R) ≤ P3₂ ^ (1 + 1) := by
  intro h
  have hmap : map phiMinus9 (span ({(3 : R)} : Set R)) ≤ map phiMinus9 (P3₂ ^ (1 + 1)) :=
    Ideal.map_mono h
  have hsq : map phiMinus9 (P3₂ ^ (1 + 1)) ≤ ⊥ := by
    calc
      map phiMinus9 (P3₂ ^ (1 + 1)) = (map phiMinus9 P3₂) ^ (1 + 1) := by
        simpa using (Ideal.map_pow phiMinus9 P3₂ (1 + 1))
      _ = map phiMinus9 P3₂ * map phiMinus9 P3₂ := by simp [pow_two]
      _ ≤ span ({(3 : ZMod 9)} : Set (ZMod 9)) * span ({(3 : ZMod 9)} : Set (ZMod 9)) :=
        Ideal.mul_mono map_P3₂_le_span3_mod9 map_P3₂_le_span3_mod9
      _ = (span ({(3 : ZMod 9)} : Set (ZMod 9)) : Ideal (ZMod 9)) ^ (1 + 1) := by
        simp [pow_two]
      _ = ⊥ := by
        have h9 : ((3 : ZMod 9) ^ 2) = 0 := by decide
        rw [Ideal.span_singleton_pow, h9, Ideal.span_singleton_eq_bot]
  have hbot : map phiMinus9 (span ({(3 : R)} : Set R)) = ⊥ :=
    le_bot_iff.mp (hmap.trans hsq)
  have hzero : ((3 : ZMod 9)) = 0 := by
    have hphi3 : (phiMinus9 (3 : R) : ZMod 9) = 3 := by simp [phiMinus9]
    have hzero' : (phiMinus9 (3 : R) : ZMod 9) = 0 := by
      apply (Ideal.span_singleton_eq_bot.mp _)
      simpa [Ideal.map_span] using hbot
    simpa [hphi3] using hzero'
  exact (by decide : (3 : ZMod 9) ≠ 0) hzero

/-- Ring hom sending `√-5` to `1` in `ZMod 2`. -/
noncomputable def phi2 : R →+* ZMod 2 :=
  Zsqrtd.lift ⟨(1 : ZMod 2), by decide⟩

lemma phi2_apply (z : R) : phi2 z = (z.re + z.im : ZMod 2) := by
  rcases z with ⟨a, b⟩
  simp [phi2, Zsqrtd.lift, Zsqrtd.decompose]

lemma ker_phi2_eq_P2 : RingHom.ker phi2 = P2 := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, phi2_apply] at hz
    have hz' : ((z.re + z.im : ℤ) : ZMod 2) = 0 := by simpa [Int.cast_add] using hz
    rw [ZMod.intCast_eq_zero_iff_even] at hz'
    simpa [P2, mem_span_two_one_plus_sqrtd_iff] using hz'
  · intro hz
    rw [RingHom.mem_ker, phi2_apply]
    have hz' : Even (z.re + z.im) := by simpa [P2, mem_span_two_one_plus_sqrtd_iff] using hz
    have hz'' : ((z.re + z.im : ℤ) : ZMod 2) = 0 := by
      exact (ZMod.intCast_eq_zero_iff_even).2 hz'
    simpa [Int.cast_add] using hz''

/-- Ring hom sending `√-5` to `2` in `ZMod 3` (i.e. `-1 mod 3`). -/
noncomputable def phi3Plus : R →+* ZMod 3 :=
  Zsqrtd.lift ⟨(2 : ZMod 3), by decide⟩

lemma phi3Plus_apply (z : R) : phi3Plus z = (z.re + 2 * z.im : ZMod 3) := by
  rcases z with ⟨a, b⟩
  simp [phi3Plus, Zsqrtd.lift, Zsqrtd.decompose, mul_comm]

lemma ker_phi3Plus_eq_P3₁ : RingHom.ker phi3Plus = P3₁ := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, phi3Plus_apply] at hz
    have hz'' : ((z.re + 2 * z.im : ℤ) : ZMod 3) = 0 := by
      simpa [Int.cast_add, Int.cast_mul] using hz
    have hz' : (3 : ℤ) ∣ z.re + 2 * z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hz''
    have h3im : (3 : ℤ) ∣ 3 * z.im := ⟨z.im, by ring⟩
    have hdiff : (3 : ℤ) ∣ z.re - z.im := by
      have : (3 : ℤ) ∣ (z.re + 2 * z.im) - 3 * z.im := dvd_sub hz' h3im
      have hcalc : (z.re + 2 * z.im) - 3 * z.im = z.re - z.im := by ring
      exact hcalc ▸ this
    simpa [P3₁, mem_span_three_one_plus_sqrtd_idx] using hdiff
  · intro hz
    rw [RingHom.mem_ker, phi3Plus_apply]
    have hdiff : (3 : ℤ) ∣ z.re - z.im := by
      simpa [P3₁, mem_span_three_one_plus_sqrtd_idx] using hz
    have h3im : (3 : ℤ) ∣ 3 * z.im := ⟨z.im, by ring⟩
    have hsum : (3 : ℤ) ∣ z.re + 2 * z.im := by
      have : (3 : ℤ) ∣ (z.re - z.im) + 3 * z.im := dvd_add hdiff h3im
      have hcalc : (z.re - z.im) + 3 * z.im = z.re + 2 * z.im := by ring
      exact hcalc ▸ this
    have hsum' : ((z.re + 2 * z.im : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hsum
    simpa [Int.cast_add, Int.cast_mul] using hsum'

/-- Ring hom sending `√-5` to `1` in `ZMod 3`. -/
noncomputable def phi3Minus : R →+* ZMod 3 :=
  Zsqrtd.lift ⟨(1 : ZMod 3), by decide⟩

lemma phi3Minus_apply (z : R) : phi3Minus z = (z.re + z.im : ZMod 3) := by
  rcases z with ⟨a, b⟩
  simp [phi3Minus, Zsqrtd.lift, Zsqrtd.decompose]

lemma ker_phi3Minus_eq_P3₂ : RingHom.ker phi3Minus = P3₂ := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, phi3Minus_apply] at hz
    have hz'' : ((z.re + z.im : ℤ) : ZMod 3) = 0 := by simpa [Int.cast_add] using hz
    have hz' : (3 : ℤ) ∣ z.re + z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hz''
    simpa [P3₂, mem_span_three_one_minus_sqrtd_idx] using hz'
  · intro hz
    rw [RingHom.mem_ker, phi3Minus_apply]
    have hz' : (3 : ℤ) ∣ z.re + z.im := by
      simpa [P3₂, mem_span_three_one_minus_sqrtd_idx] using hz
    have hz'' : ((z.re + z.im : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hz'
    simpa [Int.cast_add] using hz''

lemma comap_P2 : Ideal.comap (algebraMap ℤ R) P2 = (span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : R) ∈ P2) at hz
    rw [P2, mem_span_two_one_plus_sqrtd_iff] at hz
    rw [Ideal.mem_span_singleton]
    simpa using even_iff_two_dvd.mp hz
  · intro hz
    change ((z : R) ∈ P2)
    rw [P2, mem_span_two_one_plus_sqrtd_iff]
    exact even_iff_two_dvd.mpr (by simpa [Ideal.mem_span_singleton] using hz)

lemma comap_P3₁ : Ideal.comap (algebraMap ℤ R) P3₁ = (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : R) ∈ P3₁) at hz
    rw [P3₁, mem_span_three_one_plus_sqrtd_idx] at hz
    rw [Ideal.mem_span_singleton]
    simpa using hz
  · intro hz
    change ((z : R) ∈ P3₁)
    rw [P3₁, mem_span_three_one_plus_sqrtd_idx]
    exact (by simpa [Ideal.mem_span_singleton] using hz)

lemma comap_P3₂ : Ideal.comap (algebraMap ℤ R) P3₂ = (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : R) ∈ P3₂) at hz
    rw [P3₂, mem_span_three_one_minus_sqrtd_idx] at hz
    rw [Ideal.mem_span_singleton]
    simpa using hz
  · intro hz
    change ((z : R) ∈ P3₂)
    rw [P3₂, mem_span_three_one_minus_sqrtd_idx]
    exact (by simpa [Ideal.mem_span_singleton] using hz)

noncomputable def quotEquivP2 : (R ⧸ P2) ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq (I := P2) (J := RingHom.ker phi2) ker_phi2_eq_P2.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := phi2) (ZMod.ringHom_surjective phi2))

noncomputable def quotEquivP3₁ : (R ⧸ P3₁) ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq (I := P3₁) (J := RingHom.ker phi3Plus) ker_phi3Plus_eq_P3₁.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := phi3Plus) (ZMod.ringHom_surjective phi3Plus))

noncomputable def quotEquivP3₂ : (R ⧸ P3₂) ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq (I := P3₂) (J := RingHom.ker phi3Minus) ker_phi3Minus_eq_P3₂.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := phi3Minus) (ZMod.ringHom_surjective phi3Minus))

-- ============================================================================
-- Main Results: Ramification Index
-- ============================================================================

/-- The ramification index of P2 over (2) is 2.

Mathematical reason: (2) = P2² in ℤ[√-5], so 2 = e(P2|2) × f(P2|2) = 2 × 1.
This means P2 appears with exponent 2 in the factorization of (2). -/
theorem ramificationIdx_P2 :
    ramificationIdx (algebraMap ℤ R) (span {(2 : ℤ)}) P2 = 2 := by
  rw [ramificationIdx_spec]
  · rw [map_span_int_singleton]
    convert le_refl _ using 1
    exact factorization_of_two.symm
  · intro h
    have hprime : (P2 : Ideal R).IsPrime := by
      simpa [P2] using isPrime_span_two_one_plus_sqrtd
    have hne_top : (P2 : Ideal R) ≠ ⊤ := hprime.ne_top
    have h2ne : (2 : R) ≠ 0 := by norm_num
    have h' : (span ({(2 : R)} : Set R) : Ideal R) * ⊤ ≤
        (span ({(2 : R)} : Set R) : Ideal R) * P2 := by
      rw [map_span_int_singleton] at h
      simpa [pow_succ, factorization_of_two, Ideal.mul_assoc] using h
    have htop_le : (⊤ : Ideal R) ≤ P2 :=
      (Ideal.span_singleton_mul_right_mono (I := (⊤ : Ideal R)) (J := P2) h2ne).1 h'
    exact hne_top (top_le_iff.mp htop_le)

/-- The ramification index of P3₁ over (3) is 1.

Mathematical reason: (3) = P3₁ · P3₂, so P3₁ appears with exponent 1. -/
theorem ramificationIdx_P3₁ :
    ramificationIdx (algebraMap ℤ R) (span {(3 : ℤ)}) P3₁ = 1 := by
  rw [ramificationIdx_spec]
  · rw [map_span_int_singleton, pow_one]
    simpa [P3₁, P3₂] using
      (show (span ({(3 : R)} : Set R) : Ideal R) ≤ P3₁ from by
        rw [factorization_of_three]
        exact Ideal.mul_le_right)
  · intro h
    rw [map_span_int_singleton] at h
    exact not_span3_le_P3₁_sq h

/-- The ramification index of P3₂ over (3) is 1. -/
theorem ramificationIdx_P3₂ :
    ramificationIdx (algebraMap ℤ R) (span {(3 : ℤ)}) P3₂ = 1 := by
  rw [ramificationIdx_spec]
  · rw [map_span_int_singleton, pow_one]
    simpa [P3₁, P3₂] using
      (show (span ({(3 : R)} : Set R) : Ideal R) ≤ P3₂ from by
        rw [factorization_of_three]
        exact Ideal.mul_le_left)
  · intro h
    rw [map_span_int_singleton] at h
    exact not_span3_le_P3₂_sq h

-- ============================================================================
-- Main Results: Inertia Degree
-- ============================================================================

/-- The inertia degree of P2 over (2) is 1.

Mathematical reason: ℤ[√-5]/(2, 1+√-5) ≅ ℤ/2ℤ, so the residue field has size 2,
which as a vector space over ℤ/2ℤ has dimension 1. -/
theorem inertiaDeg_P2 :
    inertiaDeg (span {(2 : ℤ)}) P2 = 1 := by
  letI : Algebra (ℤ ⧸ (span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ)) (R ⧸ P2) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq comap_P2.symm)
  rw [Ideal.inertiaDeg, dif_pos comap_P2]
  have hfin := Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod 2) quotEquivP2 (by
    ext n
    simp [quotEquivP2, phi2, P2])
  exact_mod_cast hfin.trans (by simp [Module.finrank_self])

/-- The inertia degree of P3₁ over (3) is 1. -/
theorem inertiaDeg_P3₁ :
    inertiaDeg (span {(3 : ℤ)}) P3₁ = 1 := by
  letI : Algebra (ℤ ⧸ (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ)) (R ⧸ P3₁) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq comap_P3₁.symm)
  rw [Ideal.inertiaDeg, dif_pos comap_P3₁]
  have hfin := Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod 3) quotEquivP3₁ (by
    ext n
    simp [quotEquivP3₁, phi3Plus, P3₁])
  exact_mod_cast hfin.trans (by simp [Module.finrank_self])

/-- The inertia degree of P3₂ over (3) is 1. -/
theorem inertiaDeg_P3₂ :
    inertiaDeg (span {(3 : ℤ)}) P3₂ = 1 := by
  letI : Algebra (ℤ ⧸ (span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ)) (R ⧸ P3₂) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq comap_P3₂.symm)
  rw [Ideal.inertiaDeg, dif_pos comap_P3₂]
  have hfin := Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod 3) quotEquivP3₂ (by
    ext n
    simp [quotEquivP3₂, phi3Minus, P3₂])
  exact_mod_cast hfin.trans (by simp [Module.finrank_self])

end QuadraticNumberFields.Examples.ZsqrtdNeg5
