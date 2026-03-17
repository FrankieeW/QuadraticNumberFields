/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import LeanPrism
import Mathlib.RingTheory.Ideal.Over

/-!
# Splitting Definitions and Trichotomy

This file defines the split/inert/ramified classification for prime ideals
in Dedekind extensions, and proves the trichotomy theorem for degree-2 extensions
(quadratic number fields).

## Main Definitions

* `Ideal.IsSplitIn`: A prime splits if there are ≥ 2 primes above it, each with e = 1.
* `Ideal.IsInertIn`: A prime is inert if there is exactly 1 prime above it, with e = 1.
* `Ideal.IsRamifiedIn`: A prime ramifies if some prime above it has e > 1.

## Main Theorems

* `Ideal.isSplit_or_isInert_or_isRamified`: For a degree-2 extension, every prime
  falls into exactly one of the three categories.
-/

open Ideal

namespace Ideal

variable {R : Type*} [CommRing R]
variable (p : Ideal R) (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
-- Local notation for ramification index, inertia degree, and number of primes
local notation3 "e(" P ")" => ramificationIdx (algebraMap R S) p P
local notation3 "f(" P ")" => p.inertiaDeg P
local notation3 "g" => (primesOverFinset p S).card
-- local notation3 "π(" p ", " S ")" => primesOverFinset p S

section GeneralDefs

/-- A prime `p` **splits** in `S` if at least two primes of `S` lie over `p`,
each with ramification index 1. -/
def IsSplitIn : Prop :=
  1 < g ∧
    ∀ P ∈ primesOverFinset p S, e(P)  = 1

/-- A prime `p` is **inert** in `S` if exactly one prime of `S` lies over `p`,
with ramification index 1. -/
def IsInertIn : Prop :=
  g = 1 ∧
    ∀ P ∈ primesOverFinset p S, e(P) = 1

/-- A prime `p` **ramifies** in `S` if some prime of `S` lying over `p`
has ramification index > 1. -/
def IsRamifiedIn : Prop :=
  ∃ P ∈ primesOverFinset p S, 1 < e(P)

end GeneralDefs

section Trichotomy

/-! ## Trichotomy for degree-2 extensions

For `[L : K] = 2`, `∑ eᵢfᵢ = 2` forces exactly three possibilities:
* `(e, f, g) = (1, 1, 2)` — split
* `(e, f, g) = (1, 2, 1)` — inert
* `(e, f, g) = (2, 1, 1)` — ramified
-/

theorem IsSplitIn.not_isInert :
     p.IsSplitIn S → ¬ p.IsInertIn S :=
    fun hs hi => Nat.lt_irrefl 1 (hi.1 ▸ hs.1)

private theorem not_isRamifiedIn_of_forall_eq_one
      (h : ∀ P ∈ primesOverFinset p S, e(P) = 1) :
      ¬ p.IsRamifiedIn S :=
    fun ⟨P, hP, hlt⟩ => by simp [h P hP] at hlt

theorem IsSplitIn.not_isRamified :
     p.IsSplitIn S → ¬ p.IsRamifiedIn S :=
    fun hs => not_isRamifiedIn_of_forall_eq_one p S hs.2

theorem IsInertIn.not_isRamified :
     p.IsInertIn S → ¬ p.IsRamifiedIn S :=
    fun hi => not_isRamifiedIn_of_forall_eq_one p S hi.2

/-! ## Helper lemmas for trichotomy-/



variable [IsDedekindDomain R]



variable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.IsTorsionFree R S] [p.IsMaximal]

lemma e_ge_one (hp : p ≠ ⊥) :
    ∀ P ∈ primesOverFinset p S, 1 ≤ e(P) := by
  intro P hP
  rw [mem_primesOverFinset_iff hp] at hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  exact Nat.one_le_iff_ne_zero.mpr
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp)

variable [Module.Finite R S]

lemma f_ge_one (hp : p ≠ ⊥) :
  ∀ P ∈ primesOverFinset p S, 1 ≤ f(P) := by
    intro P hP
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rw [mem_primesOverFinset_iff hp] at hP
    have : P.LiesOver p := hP.2
    apply Ideal.inertiaDeg_ne_zero

lemma g_ge_one (hp : p ≠ ⊥) :
      1 ≤ g := by
    have := one_le_primesOver_ncard p S
    rw [← coe_primesOverFinset hp S, Set.ncard_coe_finset] at this
    exact this

-- `sum_ramification_inertia`
theorem isSplit_or_isInert_or_isRamified
    (hp : p ≠ ⊥)
    (h_deg : Module.finrank K L = 2) :
  p.IsSplitIn S ∨ p.IsInertIn S ∨ p.IsRamifiedIn S := by
  -- Apply the sum formula: ∑ e_i * f_i = [L:K] = 2
  classical
  have h_sum := Ideal.sum_ramification_inertia S K L hp
  rw [h_deg] at h_sum
  have hmul_ge_one : ∀ P ∈ primesOverFinset p S, 1 ≤ e(P) * f(P) :=
    fun P hP => Right.one_le_mul (e_ge_one p S hp P hP) (f_ge_one p S hp P hP)
  have hcard_le_sum :
    g ≤ ∑ P ∈ primesOverFinset p S, e(P) * f(P) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun P hP => hmul_ge_one P hP)
  -- Case analysis on g  
  by_cases hg : g = 2
  · -- Case g = 2: split (e, f, g) = (1, 1, 2)
    left
    refine ⟨by omega, ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨P, hP, heP⟩ := h
    have htwoP : 2 ≤ e(P) := by
      have := e_ge_one p S hp P hP
      omega
    have : 1 ≤ ∑ Q ∈ (primesOverFinset p S).erase P, e(Q) * f(Q) := by
      have hterm :
          ∀ Q ∈ (primesOverFinset p S).erase P, 1 ≤ e(Q) * f(Q) :=
          fun Q hQ => hmul_ge_one Q (Finset.mem_of_mem_erase hQ)
      have : 1 = ((primesOverFinset p S).erase P).card := by
        rw [Finset.card_erase_of_mem hP]
        omega
      rw [this, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun P hP => hterm P hP)
    have hsum_ge_three : 3 ≤ ∑ P ∈ primesOverFinset p S, e(P) * f(P) := by
      rw [(Finset.add_sum_erase _ _ hP).symm]
      have : 2 ≤ e(P) * f(P) := by
        calc
          2 ≤ e(P) * 1 := by omega
          _ ≤ e(P) * f(P) := Nat.mul_le_mul_left _ (f_ge_one p S hp P hP)
      omega
    omega
  · -- g ≠ 2, so g = 1
    have hg1 : g = 1 := by
      have : 1 ≤ g := by exact g_ge_one p S hp
      omega
    right
    by_cases hi : ∀ P ∈ primesOverFinset p S, e(P) = 1
    · -- Case g = 1 and e(P) = 1: inert (e, f, g) = (1, 2, 1)
      left
      exact ⟨hg1, hi⟩
    · -- Case g = 1 and ∃ P, e(P) ≠ 1: (e, f, g) = (2, 1, 1) ramified
      right
      push_neg at hi
      obtain ⟨P, hP, _⟩ := hi
      refine ⟨P, hP, ?_⟩
      have h1 : 1 ≤ e(P) := e_ge_one p S hp P hP
      omega



end Trichotomy

end Ideal
