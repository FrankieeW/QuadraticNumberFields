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
section GeneralDefs

/-- A prime `p` **splits** in `S` if at least two primes of `S` lie over `p`,
each with ramification index 1. -/
def IsSplitIn : Prop :=
  1 < (p.primesOver S).ncard ∧
    ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1

/-- A prime `p` is **inert** in `S` if exactly one prime of `S` lies over `p`,
with ramification index 1. -/
def IsInertIn : Prop :=
  (p.primesOver S).ncard = 1 ∧
    ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1

/-- A prime `p` **ramifies** in `S` if some prime of `S` lying over `p`
has ramification index > 1. -/
def IsRamifiedIn : Prop :=
  ∃ P ∈ p.primesOver S, 1 < ramificationIdx (algebraMap R S) p P

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
      (h : ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1) :
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

variable (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
-- TODO: prove exhaustivity for degree-2 extensions
theorem isSplit_or_isInert_or_isRamified
    [p.IsMaximal] (hp : p ≠ ⊥)
    (h_deg : Module.finrank K L = 2) :
  p.IsSplitIn S ∨ p.IsInertIn S ∨ p.IsRamifiedIn S := by

    sorry

end Trichotomy

end Ideal
