/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

Ideal factorization and primality results for ℤ[√-5].
Ported from the ANT project.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ideal Factorization in ℤ[√-5]

This file proves the ideal factorization identities and primality results
for the non-UFD ring `ℤ[√-5]`, demonstrating the general theory of
quadratic number fields on a concrete example.

## Main Results

* `factorization_of_two`: `(2) = (2, 1+√-5)²`
* `factorization_of_three`: `(3) = (3, 1+√-5) · (3, 1-√-5)`
* `factorization_of_one_plus_sqrtd`: `(1+√-5) = (2, 1+√-5) · (3, 1+√-5)`
* `factorization_of_one_minus_sqrtd`: `(1-√-5) = (2, 1-√-5) · (3, 1-√-5)`
* `isPrime_span_two_one_plus_sqrtd`: `(2, 1+√-5)` is prime
* `isPrime_span_three_one_plus_sqrtd`: `(3, 1+√-5)` is prime
* `isPrime_span_three_one_minus_sqrtd`: `(3, 1-√-5)` is prime
-/

open Ideal Zsqrtd

namespace QuadraticNumberFields.Examples.ZsqrtdNeg5

/-- The working quadratic integer ring `ℤ[√-5]` used in this file. -/
abbrev R := Zsqrtd (-5)

instance instNoZeroDivisorsR : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : Zsqrtd.norm (a * b) = 0 := by
      simp [hab, Zsqrtd.norm_zero (d := (-5))]
    have hmulnorm : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      simpa [Zsqrtd.norm_mul] using hnorm
    rcases mul_eq_zero.mp hmulnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (d := (-5)) (by decide) a).1 ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (d := (-5)) (by decide) b).1 hb)

instance instIsDomainR : IsDomain R := NoZeroDivisors.to_isDomain R

theorem factorization_of_two :
    span {(2 : R)} = (span {2, 1 + sqrtd}) ^ 2 := by
  -- Expand ⟨2, 1+√-5⟩² into the span of the four pairwise products of generators
  let J : Ideal R :=
    span ({(2 : R) * (2 : R), (2 : R) * (1 + sqrtd), (1 + sqrtd) * (2 : R),
      (1 + sqrtd) * (1 + sqrtd)} : Set R)
  -- Key computation: (1+√-5)² = 2·(-2+√-5), since (√-5)² = -5
  have hsq : (1 + sqrtd : R) * (1 + sqrtd) = (2 : R) * (-2 + sqrtd) := by
    ext <;> norm_num [Zsqrtd.sqrtd]
  -- Rewrite the square as J using `span_pair_mul_span_pair`
  have hpow : (span ({(2 : R), (1 + sqrtd)} : Set R) : Ideal R) ^ 2 = J := by
    simp [J, pow_two, Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · -- Forward inclusion ⟨2⟩ ⊆ J: express 2 as a linear combination of generators
    --   2 = 2·(1+√-5) - (1+√-5)² - 2·2
    rw [Ideal.span_singleton_le_iff_mem, hpow]
    have h21 : (2 : R) * (1 + sqrtd) ∈ J := Ideal.subset_span (by simp)
    have h11 : (1 + sqrtd : R) * (1 + sqrtd) ∈ J := Ideal.subset_span (by simp)
    have h22 : (2 : R) * (2 : R) ∈ J := Ideal.subset_span (by simp)
    -- Ideals are closed under subtraction, so this combination lies in J
    have hmem : (2 : R) * (1 + sqrtd) - (1 + sqrtd) * (1 + sqrtd) - (2 : R) * (2 : R) ∈ J :=
      J.sub_mem (J.sub_mem h21 h11) h22
    -- Verify the combination actually equals 2
    have hcalc :
        (2 : R) * (1 + sqrtd) - (1 + sqrtd) * (1 + sqrtd) - (2 : R) * (2 : R) = (2 : R) := by
      rw [hsq]
      ring
    exact hcalc ▸ hmem
  · -- Reverse inclusion J ⊆ ⟨2⟩: each of the four generators is divisible by 2
    rw [hpow]
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·2 is divisible by 2
      exact Ideal.mem_span_singleton.mpr ⟨(2 : R), rfl⟩
    · -- 2·(1+√-5) is divisible by 2
      exact Ideal.mem_span_singleton.mpr ⟨(1 + sqrtd : R), rfl⟩
    · -- (1+√-5)·2 = 2·(1+√-5) by commutativity
      exact Ideal.mem_span_singleton.mpr ⟨(1 + sqrtd : R), by simp [mul_comm]⟩
    · -- (1+√-5)² = 2·(-2+√-5) by `hsq`
      exact Ideal.mem_span_singleton.mpr ⟨(-2 + sqrtd : R), hsq⟩

lemma principal_eq_of_le_of_le
  {I J : Ideal R} (h₁ : I ≤ J) (h₂ : J ≤ I) :
  I = J :=
le_antisymm h₁ h₂

lemma in_span_of_eq
  {x y : R} (h : x = y) (hy : y ∈ (I : Ideal R)) :
  x ∈ I :=
by simpa [h] using hy

/-- If `a` divides every element of `S`, then `span S ≤ span {a}`. -/
lemma span_le_span_singleton_of_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α}
    (h : ∀ x ∈ S, a ∣ x) :
    span S ≤ span {a} :=
  Ideal.span_le.2 fun x hx => Ideal.mem_span_singleton.mpr (h x hx)

theorem factorization_of_three :
    span {(3 : R)} = (span {3, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
    -- Expand the ideal product into the span of four pairwise products
    rw [Ideal.span_pair_mul_span_pair]
    apply principal_eq_of_le_of_le
    · -- Forward inclusion ⟨3⟩ ⊆ product: 3 = 3·3 - (1+√-5)(1-√-5)
      --   since (1+√-5)(1-√-5) = 1-(-5) = 6, we get 9 - 6 = 3
      rw [Ideal.span_singleton_le_iff_mem]
      have three_eq: (3 : R) = 3 * 3 - (1 + sqrtd) * (1 - sqrtd) := by
        ext <;> norm_num [Zsqrtd.sqrtd]
      exact in_span_of_eq three_eq
        ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
    · -- Reverse inclusion: each of the four generators is divisible by 3
      apply span_le_span_singleton_of_forall_dvd
      intro x hx
      rcases hx with rfl  | rfl | rfl | rfl
      · simp  -- 3·3 is divisible by 3
      · simp  -- 3·(1-√-5) is divisible by 3
      · simp  -- (1+√-5)·3 is divisible by 3
      · -- (1+√-5)(1-√-5) = 6 = 3·2
        exact ⟨2, by ext <;> norm_num [Zsqrtd.sqrtd]⟩

theorem factorization_of_one_plus_sqrtd :
    span {(1 + sqrtd : R)} = (span {2, 1 + sqrtd}) * (span {3, 1 + sqrtd}) := by
  -- Expand the ideal product into the span of four pairwise products
  rw [Ideal.span_pair_mul_span_pair]
  apply principal_eq_of_le_of_le
  · -- Forward inclusion ⟨1+√-5⟩ ⊆ product:
    --   1+√-5 = (1+√-5)·3 - 2·(1+√-5)  (i.e., 3x - 2x = x)
    rw [Ideal.span_singleton_le_iff_mem]
    have one_plus_sqrtd_eq :
        (1 + sqrtd : R) = (1 + sqrtd) * 3 - 2 * (1 + sqrtd) := by ring
    exact in_span_of_eq one_plus_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · -- Reverse inclusion: each of the four generators is divisible by (1+√-5)
    apply span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·3 = 6 = (1+√-5)(1-√-5), so (1+√-5) | 6
      exact ⟨1 - sqrtd, by ext <;> norm_num [Zsqrtd.sqrtd]⟩
    · -- 2·(1+√-5) = (1+√-5)·2
      simp
    · -- (1+√-5)·3
      simp
    · -- (1+√-5)² = (1+√-5)·(1+√-5)
      simp

theorem factorization_of_one_minus_sqrtd :
    span {(1 - sqrtd : R)} = (span {2, 1 - sqrtd}) * (span {3, 1 - sqrtd}) := by
  -- Symmetric to factorization_of_one_plus_sqrtd, replacing √-5 by -√-5
  rw [Ideal.span_pair_mul_span_pair]
  apply principal_eq_of_le_of_le
  · -- Forward inclusion: 1-√-5 = (1-√-5)·3 - 2·(1-√-5)
    rw [Ideal.span_singleton_le_iff_mem]
    have one_mins_sqrtd_eq :
        (1 - sqrtd : R) = (1 - sqrtd) * 3 - 2 * (1 - sqrtd) := by ring
    exact in_span_of_eq one_mins_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · -- Reverse inclusion: each of the four generators is divisible by (1-√-5)
    apply span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·3 = 6 = (1-√-5)(1+√-5), so (1-√-5) | 6
      exact ⟨1 + sqrtd, by ext <;> norm_num [Zsqrtd.sqrtd]⟩
    · simp  -- 2·(1-√-5) = (1-√-5)·2
    · simp  -- (1-√-5)·3
    · simp  -- (1-√-5)² = (1-√-5)·(1-√-5)

-- Alternative approach: primality can be shown via ideal norms — an ideal of prime norm is prime.

/-- An ideal whose absolute norm is a prime number is a prime ideal
(via Mathlib's `isPrime_of_irreducible_absNorm`). -/
theorem ideal_of_prime_norm_is_prime {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] (I : Ideal R) (hI : I.absNorm.Prime) : I.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  exact hI

/-- An element of ℤ[√-5] belongs to span {2, 1 + √(-5)} iff re + im is even. -/
lemma mem_span_two_one_plus_sqrtd_iff (z : R) :
    z ∈ (span ({2, 1 + sqrtd} : Set R) : Ideal R) ↔ Even (z.re + z.im) := by
  constructor
  · -- (⇒) If z = a·2 + b·(1+√-5), expand coordinates to deduce re+im is even
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    -- Extract the real and imaginary part equations from z = a·2 + b·(1+√-5)
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    -- Simplify using re(2)=2, im(2)=0, re(1+√-5)=1, im(1+√-5)=1
    norm_num at hre him
    -- Combine the coordinate equations to express re+im = 2·(...)
    exact ⟨a.re + a.im + b.re - 2 * b.im, by linarith⟩
  · -- (⇐) Given re+im = 2k, construct witnesses a = ⟨k - im, 0⟩, b = ⟨im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k - z.im, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

theorem isPrime_span_two_one_plus_sqrtd :
    IsPrime (span {2, 1 + sqrtd} : Ideal R) := by
  -- Strategy: use the membership criterion z ∈ I ↔ 2 | (re+im) to reduce
  -- primality to a parity argument over the integers
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- Show I ≠ ⊤: 1 ∉ I since 1.re + 1.im = 1 is odd
    intro h
    have h1 : (1 : R) ∈ (span ({2, 1 + sqrtd} : Set R) : Ideal R) := by rw [h]; trivial
    rw [mem_span_two_one_plus_sqrtd_iff] at h1
    simp at h1
  · -- Show ∀ a b, a * b ∈ I → a ∈ I ∨ b ∈ I
    intro a b hab
    -- Translate ideal membership into an evenness condition on integers
    simp only [mem_span_two_one_plus_sqrtd_iff] at hab ⊢
    -- Key identity: (ab).re + (ab).im = (a.re+a.im)(b.re+b.im) - 6·a.im·b.im
    have key : (a * b).re + (a * b).im =
        (a.re + a.im) * (b.re + b.im) - 6 * a.im * b.im := by
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    rw [key] at hab
    -- 6·a.im·b.im is obviously even
    have h6 : Even (6 * a.im * b.im) := ⟨3 * a.im * b.im, by ring⟩
    -- Since the difference is even and 6·(...) is even, the product is even
    have hprod : Even ((a.re + a.im) * (b.re + b.im)) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := h6
      exact ⟨k1 + k2, by linarith⟩
    -- An even product implies at least one even factor (since 2 is prime)
    exact Int.even_mul.mp hprod

/-- An element of ℤ[√-5] belongs to span {3, 1 + √(-5)} iff 3 divides re - im. -/
lemma mem_span_three_one_plus_sqrtd_idx (z : R) :
    z ∈ (span ({3, 1 + sqrtd} : Set R) : Ideal R) ↔ 3 ∣ (z.re - z.im) := by
  constructor
  · -- (⇒) If z = a·3 + b·(1+√-5), extract coordinate equations and show 3 | (re - im)
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    -- Combine coordinate equations: re - im = 3·(a.re - a.im - 2·b.im)
    exact ⟨a.re - a.im - 2 * b.im, by linarith⟩
  · -- (⇐) Given 3 | (re - im), i.e. re - im = 3k, construct a = ⟨k, 0⟩, b = ⟨im, 0⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

theorem isPrime_span_three_one_plus_sqrtd :
    IsPrime (span {3, 1 + sqrtd} : Ideal R) := by
  -- Strategy: use the membership criterion z ∈ I ↔ 3 | (re - im) to reduce
  -- primality to a divisibility argument over ℤ using primality of 3
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- Show I ≠ ⊤: 1 ∉ I since 3 ∤ 1.re - 1.im = 1
    intro h
    have h1 : (1 : R) ∈ (span ({3, 1 + sqrtd} : Set R) : Ideal R) := by rw [h]; trivial
    rw [mem_span_three_one_plus_sqrtd_idx] at h1
    norm_num at h1
  · -- Show ∀ a b, a * b ∈ I → a ∈ I ∨ b ∈ I
    intro a b hab
    -- Translate ideal membership into the divisibility condition 3 | (re - im)
    simp only [mem_span_three_one_plus_sqrtd_idx] at hab ⊢
    -- Key identity: (a*b).re - (a*b).im = (a.re-a.im)*(b.re-b.im) - 6*a.im*b.im
    have key : (a * b).re - (a * b).im =
        (a.re - a.im) * (b.re - b.im) - 6 * a.im * b.im := by
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    rw [key] at hab
    -- 6·a.im·b.im is divisible by 3 (since 6 = 3·2)
    have h6 : (3 : ℤ) ∣ 6 * a.im * b.im := ⟨2 * a.im * b.im, by ring⟩
    -- Since 3 | (difference - 6·a.im·b.im) and 3 | 6·a.im·b.im, we get 3 | product
    have hprod : (3 : ℤ) ∣ (a.re - a.im) * (b.re - b.im) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := h6
      exact ⟨k1 + k2, by linarith⟩
    -- Since 3 is prime, it divides at least one factor (Euclid's lemma)
    have h3 : Prime (3 : ℤ) := by
      exact Int.prime_iff_natAbs_prime.2 (by decide)
    exact h3.dvd_or_dvd hprod

/-- An element of ℤ[√-5] belongs to span {3, 1 - √(-5)} iff 3 divides re + im. -/
lemma mem_span_three_one_minus_sqrtd_idx (z : R) :
    z ∈ (span ({3, 1 - sqrtd} : Set R) : Ideal R) ↔ 3 ∣ (z.re + z.im) := by
  constructor
  · -- (⇒) If z = a·3 + b·(1-√-5), extract coordinate equations and show 3 | (re + im)
    intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    -- Combine coordinate equations: re + im = 3·(a.re + a.im + 2·b.im)
    exact ⟨a.re + a.im + 2 * b.im, by linarith⟩
  · -- (⇐) Given 3 | (re + im), i.e. re + im = 3k, construct a = ⟨k-2·im, 0⟩, b = ⟨0, im⟩
    intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k - 2 * z.im, 0⟩, ⟨0, z.im⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

theorem isPrime_span_three_one_minus_sqrtd :
    IsPrime (span {3, 1 - sqrtd} : Ideal R) := by
  -- Strategy: use the membership criterion z ∈ I ↔ 3 | (re + im) to reduce
  -- primality to a divisibility argument over ℤ using primality of 3
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- Show I ≠ ⊤: 1 ∉ I since 3 ∤ 1.re + 1.im = 2
    intro h
    have h1 : (1 : R) ∈ (span ({3, 1 - sqrtd} : Set R) : Ideal R) := by rw [h]; trivial
    rw [mem_span_three_one_minus_sqrtd_idx] at h1
    norm_num at h1
  · -- Show ∀ a b, a * b ∈ I → a ∈ I ∨ b ∈ I
    intro a b hab
    -- Translate ideal membership into the divisibility condition 3 | (re + im)
    simp only [mem_span_three_one_minus_sqrtd_idx] at hab ⊢
    -- Key identity: (a*b).re + (a*b).im = (a.re+a.im)*(b.re+b.im) - 6*a.im*b.im
    have key : (a * b).re + (a * b).im =
        (a.re + a.im) * (b.re + b.im) - 6 * a.im * b.im := by
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    rw [key] at hab
    -- 6·a.im·b.im is divisible by 3 (since 6 = 3·2)
    have h6 : (3 : ℤ) ∣ 6 * a.im * b.im := ⟨2 * a.im * b.im, by ring⟩
    -- Since 3 | (sum - 6·a.im·b.im) and 3 | 6·a.im·b.im, we get 3 | product
    have hprod : (3 : ℤ) ∣ (a.re + a.im) * (b.re + b.im) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := h6
      exact ⟨k1 + k2, by linarith⟩
    -- Since 3 is prime, it divides at least one factor (Euclid's lemma)
    have h3 : Prime (3 : ℤ) := by
      exact Int.prime_iff_natAbs_prime.2 (by decide)
    exact h3.dvd_or_dvd hprod

end QuadraticNumberFields.Examples.ZsqrtdNeg5
