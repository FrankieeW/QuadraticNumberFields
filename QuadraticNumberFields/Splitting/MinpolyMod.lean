/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Monogenic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Minimal Polynomial mod p

This file computes the minimal polynomial of the ring-of-integers generator `θ`
and classifies its factorization modulo a prime `p`.

## Main Results

### Minimal polynomial

* `minpoly_generator_mod_four_ne_one`: `minpoly ℤ θ = X² - d` when `d % 4 ≠ 1`
* `minpoly_generator_mod_four_eq_one`: `minpoly ℤ θ = X² - X - (d-1)/4` when `d % 4 = 1`

### Factorization mod p (odd p, p ∤ d)

* `sq_sub_splits_mod_iff`: `X² - d` splits mod `p` ↔ `IsSquare (d : ZMod p)`
* `sq_sub_irreducible_mod_iff`: `X² - d` irreducible mod `p` ↔ `¬ IsSquare (d : ZMod p)`

### Connection to Legendre symbol

* `monicFactorsMod_card_eq_two_iff`: `|monicFactorsMod θ p| = 2 ↔ legendreSym p d = 1`
* `monicFactorsMod_card_eq_one_deg_two_iff`: degree-2 factor ↔ `legendreSym p d = -1`
* `monicFactorsMod_card_eq_one_mult_two_iff`: double root ↔ `legendreSym p d = 0`

### Special case: p = 2

* `splitting_at_two`: `d ≡ 2,3 mod 4` → ramified; `d ≡ 1 mod 8` → split; `d ≡ 5 mod 8` → inert
-/

open Polynomial

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-! ## Minimal polynomials -/

-- TODO: compute minpoly of θ in each case
-- theorem minpoly_generator_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
--     minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - C d := ...

-- theorem minpoly_generator_mod_four_eq_one (hd4 : d % 4 = 1) :
--     minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - X - C ((d - 1) / 4) := ...

/-! ## Factorization mod p (odd primes) -/

-- TODO: X² - d splits mod p iff d is a square mod p
-- theorem sq_sub_splits_mod_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
--     (hpd : ¬ (p : ℤ) ∣ d) :
--     (map (Int.castRingHom (ZMod p)) (X ^ 2 - C d)).Splits (RingHom.id _) ↔
--       IsSquare ((d : ZMod p) : ZMod p) := ...

/-! ## Connection to Legendre symbol -/

-- TODO: translate factorization type to legendreSym value
-- The key bridge: IsSquare (d : ZMod p) ↔ legendreSym p d = 1
-- (from mathlib: legendreSym.eq_one_iff)

/-! ## Special case: p = 2

For p = 2 the Legendre symbol is not defined (p must be odd).
Instead we use direct case analysis on d mod 4 and d mod 8:

  d ≡ 2, 3 mod 4:  X² - d ≡ X² mod 2  (double root)  → ramified
  d ≡ 1 mod 8:     X² - X - (d-1)/4 ≡ X(X-1) mod 2   → split
  d ≡ 5 mod 8:     X² - X - (d-1)/4 ≡ X²+X+1 mod 2   → inert
-/

-- TODO: case analysis for p = 2
-- theorem splitting_at_two_ramified (hd4 : d % 4 ≠ 1) :
--     ... IsRamifiedIn ... := ...

-- theorem splitting_at_two_split (hd8 : d % 8 = 1) :
--     ... IsSplitIn ... := ...

-- theorem splitting_at_two_inert (hd8 : d % 8 = 5) :
--     ... IsInertIn ... := ...

end Splitting
end QuadraticNumberFields
