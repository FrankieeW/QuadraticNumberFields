/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Monogenic
import QuadraticNumberFields.Splitting.MinpolyMod

/-!
# Prime Splitting Classification via the Legendre Symbol

This file proves the main classification theorem: for a squarefree integer `d ≠ 1`
and a prime `p`, the splitting behavior of `(p)` in `𝓞(ℚ(√d))` is determined
by the Legendre symbol `(d/p)`.

## Main Results

### Odd primes (p ≠ 2, p ∤ d)

* `isSplit_iff_legendreSym_eq_one`: `(p)` splits ↔ `legendreSym p d = 1`
* `isInert_iff_legendreSym_eq_neg_one`: `(p)` is inert ↔ `legendreSym p d = -1`
* `isRamified_of_dvd`: `p ∣ d` → `(p)` ramifies

### All primes (unified)

* `splitting_classification`: The complete trichotomy via `legendreSym p d`.

### p = 2

* Handled via `MinpolyMod.splitting_at_two_*` (d mod 4 and d mod 8 case analysis)

## Proof Strategy

```
Classification.lean (𝓞 = ℤ[θ])
         |
Monogenic.lean (exponent θ = 1)
         |
primesOverSpanEquivMonicFactorsMod   ← Kummer-Dedekind from mathlib
         |
monicFactorsMod θ p
= irreducible factors of minpoly ℤ θ mod p
         |
MinpolyMod.lean (X² - d mod p)
         |
legendreSym p d                      ← from mathlib
```
-/

open scoped NumberField
open Ideal

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-! ## Odd primes, p ∤ d -/

-- TODO: split ↔ legendreSym = 1
theorem isSplit_iff_legendreSym_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsSplitIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ legendreSym p d = 1 := by
      
      sorry

-- TODO: inert ↔ legendreSym = -1
-- theorem isInert_iff_legendreSym_eq_neg_one
--     (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
--     (Ideal.span {(p : ℤ)}).IsInertIn (𝓞 (Qsqrtd (d : ℚ)))
--       ↔ legendreSym p d = -1 := ...

-- TODO: p ∣ d → ramified
-- theorem isRamified_of_dvd
--     (p : ℕ) [Fact p.Prime] (hpd : (p : ℤ) ∣ d) :
--     (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ))) := ...

/-! ## Basic trichotomy for `𝓞(ℚ(√d))` -/

instance : Algebra.IsQuadraticExtension ℤ (𝓞 (Qsqrtd (d : ℚ))) :=
  @Algebra.IsQuadraticExtension.mk ℤ _ _ _ _ _
    (inferInstance : Module.Free ℤ (𝓞 (Qsqrtd (d : ℚ))))
    ((NumberField.RingOfIntegers.rank (Qsqrtd (d : ℚ))).trans
      (Algebra.IsQuadraticExtension.finrank_eq_two ℚ _))

/-- For a squarefree `d ≠ 1` and any prime `p`, the ideal `(p)` in `𝓞(ℚ(√d))` is
split, inert, or ramified. -/
theorem isSplit_or_isInert_or_isRamified (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsSplitIn (𝓞 (Qsqrtd (d : ℚ))) ∨
    (Ideal.span {(p : ℤ)}).IsInertIn (𝓞 (Qsqrtd (d : ℚ))) ∨
    (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ))) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.isSplit_or_isInert_or_isRamified _ _ hchar hbot

/-! ## Unified classification -/

-- TODO: complete trichotomy
-- theorem splitting_classification (p : ℕ) [Fact p.Prime] :
--     ((legendreSym p d = 1  ∧ (Ideal.span {(p : ℤ)}).IsSplitIn (𝓞 (Qsqrtd (d : ℚ)))) ∨
--      (legendreSym p d = -1 ∧ (Ideal.span {(p : ℤ)}).IsInertIn (𝓞 (Qsqrtd (d : ℚ)))) ∨
--      (legendreSym p d = 0  ∧ (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ))))) := ...

end Splitting
end QuadraticNumberFields
