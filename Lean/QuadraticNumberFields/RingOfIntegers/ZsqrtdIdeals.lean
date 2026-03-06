/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

General ideal membership, primality, and quotient results for `Zsqrtd d`.
-/
import QuadraticNumberFields.RingOfIntegers.ZsqrtdMathlibInstances
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal Theory for ℤ[√d]

General results about ideals in the quadratic integer ring `ℤ[√d]`, parameterised
by an integer `d` satisfying appropriate arithmetic conditions.

## Main Results

### Key algebraic identities

* `Zsqrtd.Ideal.mul_re_add_im_eq`:
  `(a*b).re + (a*b).im = (a.re+a.im)*(b.re+b.im) + (d-1)*a.im*b.im`
* `Zsqrtd.Ideal.mul_re_sub_im_eq`:
  `(a*b).re - (a*b).im = (a.re-a.im)*(b.re-b.im) + (d-1)*a.im*b.im`

### Membership characterisations

* `Zsqrtd.Ideal.mem_span_two_one_plus_sqrtd_iff`:
  `z ∈ (2, 1+√d) ↔ Even (z.re + z.im)` when `2 ∣ (d - 1)`
* `Zsqrtd.Ideal.mem_span_three_one_plus_sqrtd_iff`:
  `z ∈ (3, 1+√d) ↔ 3 ∣ (z.re - z.im)` when `3 ∣ (d - 1)`
* `Zsqrtd.Ideal.mem_span_three_one_minus_sqrtd_iff`:
  `z ∈ (3, 1-√d) ↔ 3 ∣ (z.re + z.im)` when `3 ∣ (d - 1)`

### Primality

* `Zsqrtd.Ideal.isPrime_span_two_one_plus_sqrtd`:
  `(2, 1+√d)` is prime when `2 ∣ (d - 1)`
* `Zsqrtd.Ideal.isPrime_span_three_one_plus_sqrtd`:
  `(3, 1+√d)` is prime when `3 ∣ (d - 1)`
* `Zsqrtd.Ideal.isPrime_span_three_one_minus_sqrtd`:
  `(3, 1-√d)` is prime when `3 ∣ (d - 1)`

### Comap characterisations

* `Zsqrtd.Ideal.comap_span_two_one_plus_sqrtd`:
  `comap (algebraMap ℤ (Zsqrtd d)) (2, 1+√d) = (2)` when `2 ∣ (d - 1)`
* `Zsqrtd.Ideal.comap_span_three_one_plus_sqrtd`:
  `comap (algebraMap ℤ (Zsqrtd d)) (3, 1+√d) = (3)` when `3 ∣ (d - 1)`
* `Zsqrtd.Ideal.comap_span_three_one_minus_sqrtd`:
  `comap (algebraMap ℤ (Zsqrtd d)) (3, 1-√d) = (3)` when `3 ∣ (d - 1)`

### Ring homomorphisms and quotients

* `Zsqrtd.Ideal.liftMod2`: `Zsqrtd d →+* ZMod 2` when `2 ∣ (d - 1)`
* `Zsqrtd.Ideal.quotEquivZMod2`: `Zsqrtd d ⧸ (2, 1+√d) ≃+* ZMod 2`
* `Zsqrtd.Ideal.liftMod3Plus`: `Zsqrtd d →+* ZMod 3` when `3 ∣ (d - 1)`
* `Zsqrtd.Ideal.liftMod3Minus`: `Zsqrtd d →+* ZMod 3` when `3 ∣ (d - 1)`
* `Zsqrtd.Ideal.quotEquivZMod3Plus`: `Zsqrtd d ⧸ (3, 1+√d) ≃+* ZMod 3`
* `Zsqrtd.Ideal.quotEquivZMod3Minus`: `Zsqrtd d ⧸ (3, 1-√d) ≃+* ZMod 3`

### Utility lemmas

* `Zsqrtd.Ideal.span_le_span_singleton_of_forall_dvd`
* `Zsqrtd.Ideal.ideal_of_prime_norm_is_prime`
-/

open Ideal Zsqrtd

namespace Zsqrtd.Ideal

variable (d : ℤ)

-- ============================================================================
-- Utility lemmas
-- ============================================================================

/-- If `a` divides every element of `S`, then `span S ≤ span {a}`. -/
theorem span_le_span_singleton_of_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α}
    (h : ∀ x ∈ S, a ∣ x) :
    Ideal.span S ≤ Ideal.span {a} :=
  Ideal.span_le.2 fun x hx => Ideal.mem_span_singleton.mpr (h x hx)

/-- An ideal whose absolute norm is a prime number is a prime ideal. -/
theorem ideal_of_prime_norm_is_prime {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] (I : Ideal R) (hI : I.absNorm.Prime) : I.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm hI

@[simp] lemma algebraMap_int_coe (n : ℤ) : algebraMap ℤ (Zsqrtd d) n = n := rfl

lemma map_span_int_singleton (n : ℤ) :
    Ideal.map (algebraMap ℤ (Zsqrtd d)) (Ideal.span {n}) = Ideal.span {(n : Zsqrtd d)} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_int_coe]

-- ============================================================================
-- Key algebraic identities
-- ============================================================================

/-- The fundamental identity for `re + im` of a product in `ℤ[√d]`:
`(a*b).re + (a*b).im = (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im`. -/
lemma mul_re_add_im_eq (a b : Zsqrtd d) :
    (a * b).re + (a * b).im =
      (a.re + a.im) * (b.re + b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

/-- The fundamental identity for `re - im` of a product in `ℤ[√d]`:
`(a*b).re - (a*b).im = (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im`. -/
lemma mul_re_sub_im_eq (a b : Zsqrtd d) :
    (a * b).re - (a * b).im =
      (a.re - a.im) * (b.re - b.im) + (d - 1) * a.im * b.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring

-- ============================================================================
-- Ideal membership characterisations
-- ============================================================================

/-- An element of `ℤ[√d]` belongs to `(2, 1+√d)` iff `re + im` is even,
provided `d` is odd (i.e. `2 ∣ (d - 1)`). -/
lemma mem_span_two_one_plus_sqrtd_iff (hd : 2 ∣ (d - 1)) (z : Zsqrtd d) :
    z ∈ (Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) ↔
      Even (z.re + z.im) := by
  obtain ⟨c, hc⟩ := hd
  constructor
  · -- (⇒) If z = a·2 + b·(1+√d), show re+im is even
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    -- z.re + z.im = 2*(a.re + a.im + b.re) + (d+1)*b.im
    -- Since d+1 = 2*(c+1), this is 2*(a.re + a.im + b.re + (c+1)*b.im)
    have hdb : d * b.im = (2 * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re + a.im + b.re + (c + 1) * b.im, by linarith⟩
  · -- (⇐) Given re+im = 2k, construct witnesses a = ⟨k - im, 0⟩, b = ⟨im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k - z.im, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

/-- An element of `ℤ[√d]` belongs to `(3, 1+√d)` iff `3 ∣ (re - im)`,
provided `3 ∣ (d - 1)`. -/
lemma mem_span_three_one_plus_sqrtd_iff (hd : 3 ∣ (d - 1)) (z : Zsqrtd d) :
    z ∈ (Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) ↔
      3 ∣ (z.re - z.im) := by
  obtain ⟨c, hc⟩ := hd
  constructor
  · -- (⇒) If z = a·3 + b·(1+√d), show 3 ∣ (re - im)
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    -- z.re - z.im = 3*(a.re - a.im) + (d-1)*b.im = 3*(a.re - a.im + c*b.im)
    have hdb : d * b.im = (3 * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re - a.im + c * b.im, by linarith⟩
  · -- (⇐) Given 3 | (re - im), construct a = ⟨k, 0⟩, b = ⟨im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

/-- An element of `ℤ[√d]` belongs to `(3, 1-√d)` iff `3 ∣ (re + im)`,
provided `3 ∣ (d - 1)`. -/
lemma mem_span_three_one_minus_sqrtd_iff (hd : 3 ∣ (d - 1)) (z : Zsqrtd d) :
    z ∈ (Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) ↔
      3 ∣ (z.re + z.im) := by
  obtain ⟨c, hc⟩ := hd
  constructor
  · -- (⇒) If z = a·3 + b·(1-√d), show 3 ∣ (re + im)
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    -- z.re + z.im = 3*(a.re + a.im) + (1-d)*b.im = 3*(a.re + a.im - c*b.im)
    have hdb : d * b.im = (3 * c + 1) * b.im := by congr 1; linarith
    exact ⟨a.re + a.im - c * b.im, by linarith⟩
  · -- (⇐) Given 3 | (re + im), construct a = ⟨k, 0⟩, b = ⟨-im, 0⟩
    -- b*(1-√d) = ⟨-im, im⟩, so a*3 + b*(1-√d) = ⟨3k - im, im⟩ = ⟨re, im⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨-z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

-- ============================================================================
-- Comap characterisations
-- ============================================================================

lemma comap_span_two_one_plus_sqrtd (hd : 2 ∣ (d - 1)) :
    Ideal.comap (algebraMap ℤ (Zsqrtd d))
      (Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d))) =
      (Ideal.span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : Zsqrtd d) ∈ Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d))) at hz
    rw [mem_span_two_one_plus_sqrtd_iff d hd] at hz
    rw [Ideal.mem_span_singleton]
    simpa using even_iff_two_dvd.mp hz
  · intro hz
    change ((z : Zsqrtd d) ∈ Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d)))
    rw [mem_span_two_one_plus_sqrtd_iff d hd]
    exact even_iff_two_dvd.mpr (by simpa [Ideal.mem_span_singleton] using hz)

lemma comap_span_three_one_plus_sqrtd (hd : 3 ∣ (d - 1)) :
    Ideal.comap (algebraMap ℤ (Zsqrtd d))
      (Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d))) =
      (Ideal.span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : Zsqrtd d) ∈ Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d))) at hz
    rw [mem_span_three_one_plus_sqrtd_iff d hd] at hz
    rw [Ideal.mem_span_singleton]
    simpa using hz
  · intro hz
    change ((z : Zsqrtd d) ∈ Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d)))
    rw [mem_span_three_one_plus_sqrtd_iff d hd]
    exact (by simpa [Ideal.mem_span_singleton] using hz)

lemma comap_span_three_one_minus_sqrtd (hd : 3 ∣ (d - 1)) :
    Ideal.comap (algebraMap ℤ (Zsqrtd d))
      (Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d))) =
      (Ideal.span ({(3 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  ext z
  constructor
  · intro hz
    change ((z : Zsqrtd d) ∈ Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d))) at hz
    rw [mem_span_three_one_minus_sqrtd_iff d hd] at hz
    rw [Ideal.mem_span_singleton]
    simpa using hz
  · intro hz
    change ((z : Zsqrtd d) ∈ Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d)))
    rw [mem_span_three_one_minus_sqrtd_iff d hd]
    exact (by simpa [Ideal.mem_span_singleton] using hz)

-- ============================================================================
-- Primality
-- ============================================================================

/-- The ideal `(2, 1+√d)` is prime in `ℤ[√d]` when `d` is odd (equivalently
`2 ∣ (d - 1)`).

The proof reduces ideal primality to an integer parity argument via the
membership characterisation `z ∈ (2, 1+√d) ↔ Even(z.re + z.im)` and
the identity `(ab).re + (ab).im = (a.re+a.im)(b.re+b.im) + (d-1)·a.im·b.im`.
Since `2 ∣ (d-1)`, the correction term is always even, so evenness of the
product implies evenness of at least one factor. -/
theorem isPrime_span_two_one_plus_sqrtd (hd : 2 ∣ (d - 1)) :
    IsPrime (Ideal.span {2, 1 + sqrtd} : Ideal (Zsqrtd d)) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : Zsqrtd d) ∈
        (Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) := by
      rw [h]; trivial
    rw [mem_span_two_one_plus_sqrtd_iff d hd] at h1
    simp at h1
  · intro a b hab
    simp only [mem_span_two_one_plus_sqrtd_iff d hd] at hab ⊢
    rw [mul_re_add_im_eq] at hab
    obtain ⟨c, hc⟩ := hd
    have hcorr : Even ((d - 1) * a.im * b.im) :=
      ⟨c * a.im * b.im, by rw [hc]; ring⟩
    have hprod : Even ((a.re + a.im) * (b.re + b.im)) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := hcorr
      exact ⟨k1 - k2, by linarith⟩
    exact Int.even_mul.mp hprod

/-- The ideal `(3, 1+√d)` is prime in `ℤ[√d]` when `3 ∣ (d - 1)`.

The proof reduces ideal primality to an integer divisibility argument via the
membership characterisation `z ∈ (3, 1+√d) ↔ 3 ∣ (z.re - z.im)` and
the identity `(ab).re - (ab).im = (a.re-a.im)(b.re-b.im) + (d-1)·a.im·b.im`.
Since `3 ∣ (d-1)`, the correction term is always divisible by 3, so
3 dividing the product implies 3 divides at least one factor (Euclid). -/
theorem isPrime_span_three_one_plus_sqrtd (hd : 3 ∣ (d - 1)) :
    IsPrime (Ideal.span {3, 1 + sqrtd} : Ideal (Zsqrtd d)) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : Zsqrtd d) ∈
        (Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) := by
      rw [h]; trivial
    rw [mem_span_three_one_plus_sqrtd_iff d hd] at h1
    norm_num at h1
  · intro a b hab
    simp only [mem_span_three_one_plus_sqrtd_iff d hd] at hab ⊢
    rw [mul_re_sub_im_eq] at hab
    obtain ⟨c, hc⟩ := hd
    have hcorr : (3 : ℤ) ∣ (d - 1) * a.im * b.im :=
      ⟨c * a.im * b.im, by rw [hc]; ring⟩
    have hprod : (3 : ℤ) ∣ (a.re - a.im) * (b.re - b.im) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := hcorr
      exact ⟨k1 - k2, by linarith⟩
    have h3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.2 (by decide)
    exact h3.dvd_or_dvd hprod

/-- The ideal `(3, 1-√d)` is prime in `ℤ[√d]` when `3 ∣ (d - 1)`.

Symmetric to `isPrime_span_three_one_plus_sqrtd`, using the identity for
`re + im` instead of `re - im`. -/
theorem isPrime_span_three_one_minus_sqrtd (hd : 3 ∣ (d - 1)) :
    IsPrime (Ideal.span {3, 1 - sqrtd} : Ideal (Zsqrtd d)) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : Zsqrtd d) ∈
        (Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d)) : Ideal (Zsqrtd d)) := by
      rw [h]; trivial
    rw [mem_span_three_one_minus_sqrtd_iff d hd] at h1
    norm_num at h1
  · intro a b hab
    simp only [mem_span_three_one_minus_sqrtd_iff d hd] at hab ⊢
    rw [mul_re_add_im_eq] at hab
    obtain ⟨c, hc⟩ := hd
    have hcorr : (3 : ℤ) ∣ (d - 1) * a.im * b.im :=
      ⟨c * a.im * b.im, by rw [hc]; ring⟩
    have hprod : (3 : ℤ) ∣ (a.re + a.im) * (b.re + b.im) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := hcorr
      exact ⟨k1 - k2, by linarith⟩
    have h3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.2 (by decide)
    exact h3.dvd_or_dvd hprod

-- ============================================================================
-- Ring homomorphisms and quotient equivalences
-- ============================================================================

private lemma d_cast_zmod2_eq_one (hd : 2 ∣ (d - 1)) : (d : ZMod 2) = 1 := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) from rfl,
      ZMod.intCast_eq_intCast_iff']
  omega

private lemma d_cast_zmod3_eq_one (hd : 3 ∣ (d - 1)) : (d : ZMod 3) = 1 := by
  rw [show (1 : ZMod 3) = ((1 : ℤ) : ZMod 3) from rfl,
      ZMod.intCast_eq_intCast_iff']
  omega

/-- The ring hom `ℤ[√d] →+* ℤ/2ℤ` sending `√d ↦ 1`, valid when `2 ∣ (d - 1)`
(since `1² = 1 ≡ d (mod 2)`). -/
noncomputable def liftMod2 (hd : 2 ∣ (d - 1)) : Zsqrtd d →+* ZMod 2 :=
  Zsqrtd.lift ⟨(1 : ZMod 2), by simp [d_cast_zmod2_eq_one d hd]⟩

lemma liftMod2_apply (hd : 2 ∣ (d - 1)) (z : Zsqrtd d) :
    liftMod2 d hd z = (z.re + z.im : ZMod 2) := by
  rcases z with ⟨a, b⟩
  simp [liftMod2, Zsqrtd.lift, Zsqrtd.decompose]

lemma ker_liftMod2 (hd : 2 ∣ (d - 1)) :
    RingHom.ker (liftMod2 d hd) =
      (Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d))) := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, liftMod2_apply] at hz
    have hz' : ((z.re + z.im : ℤ) : ZMod 2) = 0 := by simpa [Int.cast_add] using hz
    rw [ZMod.intCast_eq_zero_iff_even] at hz'
    simpa [mem_span_two_one_plus_sqrtd_iff d hd] using hz'
  · intro hz
    rw [RingHom.mem_ker, liftMod2_apply]
    have hz' : Even (z.re + z.im) := by simpa [mem_span_two_one_plus_sqrtd_iff d hd] using hz
    have hz'' : ((z.re + z.im : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_eq_zero_iff_even).2 hz'
    simpa [Int.cast_add] using hz''

/-- `ℤ[√d] ⧸ (2, 1+√d) ≃+* ℤ/2ℤ` when `2 ∣ (d - 1)`. -/
noncomputable def quotEquivZMod2 (hd : 2 ∣ (d - 1)) :
    (Zsqrtd d) ⧸ (Ideal.span ({2, 1 + sqrtd} : Set (Zsqrtd d))) ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq (ker_liftMod2 d hd).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := liftMod2 d hd)
      (ZMod.ringHom_surjective (liftMod2 d hd)))

/-- The ring hom `ℤ[√d] →+* ℤ/3ℤ` sending `√d ↦ 2` (i.e. `-1 mod 3`),
valid when `3 ∣ (d - 1)` (since `(-1)² = 1 ≡ d (mod 3)`). -/
noncomputable def liftMod3Plus (hd : 3 ∣ (d - 1)) : Zsqrtd d →+* ZMod 3 :=
  Zsqrtd.lift ⟨(2 : ZMod 3), by rw [d_cast_zmod3_eq_one d hd]; decide⟩

lemma liftMod3Plus_apply (hd : 3 ∣ (d - 1)) (z : Zsqrtd d) :
    liftMod3Plus d hd z = (z.re + 2 * z.im : ZMod 3) := by
  rcases z with ⟨a, b⟩
  simp [liftMod3Plus, Zsqrtd.lift, Zsqrtd.decompose, mul_comm]

lemma ker_liftMod3Plus (hd : 3 ∣ (d - 1)) :
    RingHom.ker (liftMod3Plus d hd) =
      (Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d))) := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, liftMod3Plus_apply] at hz
    have hz'' : ((z.re + 2 * z.im : ℤ) : ZMod 3) = 0 := by
      simpa [Int.cast_add, Int.cast_mul] using hz
    have hz' : (3 : ℤ) ∣ z.re + 2 * z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hz''
    have h3im : (3 : ℤ) ∣ 3 * z.im := ⟨z.im, by ring⟩
    have hdiff : (3 : ℤ) ∣ z.re - z.im := by
      have : (3 : ℤ) ∣ (z.re + 2 * z.im) - 3 * z.im := dvd_sub hz' h3im
      have hcalc : (z.re + 2 * z.im) - 3 * z.im = z.re - z.im := by ring
      exact hcalc ▸ this
    simpa [mem_span_three_one_plus_sqrtd_iff d hd] using hdiff
  · intro hz
    rw [RingHom.mem_ker, liftMod3Plus_apply]
    have hdiff : (3 : ℤ) ∣ z.re - z.im := by
      simpa [mem_span_three_one_plus_sqrtd_iff d hd] using hz
    have h3im : (3 : ℤ) ∣ 3 * z.im := ⟨z.im, by ring⟩
    have hsum : (3 : ℤ) ∣ z.re + 2 * z.im := by
      have : (3 : ℤ) ∣ (z.re - z.im) + 3 * z.im := dvd_add hdiff h3im
      have hcalc : (z.re - z.im) + 3 * z.im = z.re + 2 * z.im := by ring
      exact hcalc ▸ this
    have hsum' : ((z.re + 2 * z.im : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hsum
    simpa [Int.cast_add, Int.cast_mul] using hsum'

/-- `ℤ[√d] ⧸ (3, 1+√d) ≃+* ℤ/3ℤ` when `3 ∣ (d - 1)`. -/
noncomputable def quotEquivZMod3Plus (hd : 3 ∣ (d - 1)) :
    (Zsqrtd d) ⧸ (Ideal.span ({3, 1 + sqrtd} : Set (Zsqrtd d))) ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq (ker_liftMod3Plus d hd).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := liftMod3Plus d hd)
      (ZMod.ringHom_surjective (liftMod3Plus d hd)))

/-- The ring hom `ℤ[√d] →+* ℤ/3ℤ` sending `√d ↦ 1`,
valid when `3 ∣ (d - 1)` (since `1² = 1 ≡ d (mod 3)`). -/
noncomputable def liftMod3Minus (hd : 3 ∣ (d - 1)) : Zsqrtd d →+* ZMod 3 :=
  Zsqrtd.lift ⟨(1 : ZMod 3), by simp [d_cast_zmod3_eq_one d hd]⟩

lemma liftMod3Minus_apply (hd : 3 ∣ (d - 1)) (z : Zsqrtd d) :
    liftMod3Minus d hd z = (z.re + z.im : ZMod 3) := by
  rcases z with ⟨a, b⟩
  simp [liftMod3Minus, Zsqrtd.lift, Zsqrtd.decompose]

lemma ker_liftMod3Minus (hd : 3 ∣ (d - 1)) :
    RingHom.ker (liftMod3Minus d hd) =
      (Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d))) := by
  ext z
  constructor
  · intro hz
    rw [RingHom.mem_ker, liftMod3Minus_apply] at hz
    have hz'' : ((z.re + z.im : ℤ) : ZMod 3) = 0 := by simpa [Int.cast_add] using hz
    have hz' : (3 : ℤ) ∣ z.re + z.im := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hz''
    simpa [mem_span_three_one_minus_sqrtd_iff d hd] using hz'
  · intro hz
    rw [RingHom.mem_ker, liftMod3Minus_apply]
    have hz' : (3 : ℤ) ∣ z.re + z.im := by
      simpa [mem_span_three_one_minus_sqrtd_iff d hd] using hz
    have hz'' : ((z.re + z.im : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hz'
    simpa [Int.cast_add] using hz''

/-- `ℤ[√d] ⧸ (3, 1-√d) ≃+* ℤ/3ℤ` when `3 ∣ (d - 1)`. -/
noncomputable def quotEquivZMod3Minus (hd : 3 ∣ (d - 1)) :
    (Zsqrtd d) ⧸ (Ideal.span ({3, 1 - sqrtd} : Set (Zsqrtd d))) ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq (ker_liftMod3Minus d hd).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := liftMod3Minus d hd)
      (ZMod.ringHom_surjective (liftMod3Minus d hd)))

end Zsqrtd.Ideal
