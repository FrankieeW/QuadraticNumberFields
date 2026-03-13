/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
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
variable (p : Ideal R) (S : Type*) [CommRing S] [Algebra R S]
-- Local notation for ramification index, inertia degree, and number of primes
local notation3 "e(" P ")" => ramificationIdx (algebraMap R S) p P
local notation3 "f(" P ")" => p.inertiaDeg P
local notation3 "g" => (p.primesOver S).ncard
section GeneralDefs

/-- A prime `p` **splits** in `S` if at least two primes of `S` lie over `p`,
each with ramification index 1. -/
def IsSplitIn : Prop :=
  1 < g ∧
    ∀ P ∈ p.primesOver S, e(P)  = 1

/-- A prime `p` is **inert** in `S` if exactly one prime of `S` lies over `p`,
with ramification index 1. -/
def IsInertIn : Prop :=
  g = 1 ∧
    ∀ P ∈ p.primesOver S, e(P) = 1

/-- A prime `p` **ramifies** in `S` if some prime of `S` lying over `p`
has ramification index > 1. -/
def IsRamifiedIn : Prop :=
  ∃ P ∈ p.primesOver S, 1 < e(P)

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
      (h : ∀ P ∈ p.primesOver S, e(P) = 1) :
      ¬ p.IsRamifiedIn S :=
    fun ⟨P, hP, hlt⟩ => by simp [h P hP] at hlt

theorem IsSplitIn.not_isRamified :
     p.IsSplitIn S → ¬ p.IsRamifiedIn S :=
    -- rintro ⟨_, h_ram⟩ ⟨P, hP, h_ram'⟩
    -- specialize h_ram P hP
    -- rw [← Eq.symm h_ram] at h_ram'
    -- exact Nat.lt_irrefl 1 h_ram'
    fun hs => not_isRamifiedIn_of_forall_eq_one p S hs.2

theorem IsInertIn.not_isRamified :
     p.IsInertIn S → ¬ p.IsRamifiedIn S :=
    fun hi => not_isRamifiedIn_of_forall_eq_one p S hi.2

/-! ## Helper lemmas for trichotomy

Three mutually exclusive cases from `∑ eᵢfᵢ = [L:K] = 2`:
- `(e, f, g) = (1, 1, 2)` — split
- `(e, f, g) = (1, 2, 1)` — inert
- `(e, f, g) = (2, 1, 1)` — ramified
-/

lemma f_ge_one [p.IsMaximal] [Module.Finite R S] :
  ∀ P ∈ p.primesOver S, 1 ≤ f(P) := by
    intro P hP
    refine Nat.one_le_iff_ne_zero.mpr ?_
    have : P.LiesOver p := hP.2 --see RingTheory/Ideal/Over.lean 369
    apply Ideal.inertiaDeg_ne_zero


variable [IsDedekindDomain R] [IsDedekindDomain S]

lemma e_ge_one [Module.IsTorsionFree R S] (hp : p ≠ ⊥) :
    ∀ P ∈ p.primesOver S, 1 ≤ e(P) := by
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  exact Nat.one_le_iff_ne_zero.mpr
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp)



variable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [Module.IsTorsionFree R S]



-- TODO: prove exhaustivity for degree-2 extensions
-- `sum_ramification_inertia` + Galois uniformity
theorem isSplit_or_isInert_or_isRamified
    [p.IsMaximal] (hp : p ≠ ⊥)
    (h_deg : Module.finrank K L = 2) :
  p.IsSplitIn S ∨ p.IsInertIn S ∨ p.IsRamifiedIn S := by
  -- Apply the sum formula: ∑ e_i * f_i = [L:K] = 2
  have h_sum := Ideal.sum_ramification_inertia S K L hp
  rw [h_deg] at h_sum
  -- Since p.IsMaximal Ideal.inertiaDeg_ne_zero
  have hf_ge_one:
    ∀ P ∈ p.primesOver S, 1 ≤ f(P) := f_ge_one p S
  have he_ge_one:
    ∀ P ∈ p.primesOver S, 1 ≤ e(P) := e_ge_one p S hp
  have hg_ge_one : 1 ≤ g := one_le_primesOver_ncard p S

  have hmul_ge_one : ∀ P ∈ primesOverFinset p S, 1 ≤ e(P) * f(P) := by
    intro P hP
    have hP' : P ∈ p.primesOver S :=
        (mem_primesOverFinset_iff (p := p) (B := S) hp).mp hP
    exact Right.one_le_mul (he_ge_one P hP') (hf_ge_one P hP')

  have hcard_le_sum :
    (primesOverFinset p S).card ≤
      ∑ P ∈ primesOverFinset p S, e(P) * f(P) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun P hP => hmul_ge_one P hP)

  have hfin_le_two : (primesOverFinset p S).card ≤ 2 := by
    simpa [h_sum] using hcard_le_sum

  have hg_le_two : g ≤ 2 := by
    rw [← coe_primesOverFinset (p := p) hp S, Set.ncard_coe_finset]
    exact hfin_le_two

  -- Case analysis on g
  by_cases hg : g = 2
  · -- Case g = 2: split
    -- We have e(P₁)f(P₁) + e(P₂)f(P₂) = 2 with each term ≥ 1
    -- So e(P₁) = e(P₂) = 1 (and f(P₁) = f(P₂) = 1)
    left
    refine ⟨hg.ge, ?_⟩
    rintro P hP
    -- suppose e(P) ≠ 1, then e(P) ≥ 2, so e(P)f(P) ≥ 2, contradicting the sum
    by_contra h
    sorry
  · -- g ≠ 2, so g = 1
    have hg1 : g = 1 := by
      -- ¬g=2 and 1≥g
      sorry
    sorry





end Trichotomy

end Ideal
