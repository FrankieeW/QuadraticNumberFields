/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-!
# Monogenicity of the Ring of Integers

This file establishes that `𝓞(ℚ(√d)) = ℤ[θ]` for an explicit generator `θ`,
so that the Kummer–Dedekind theorem applies to **all** primes unconditionally.

## Main Results

* `ringOfIntegersGenerator`: The generator `θ` of `𝓞(ℚ(√d))` as a ℤ-algebra.
  - `θ = √d` when `d % 4 ≠ 1`
  - `θ = (1 + √d)/2` when `d % 4 = 1`
* `isMonogenic`: `Algebra.adjoin ℤ {θ} = ⊤`
* `exponent_eq_one`: `RingOfIntegers.exponent θ = 1`
* `not_dvd_exponent`: `¬ p ∣ exponent θ` for any prime `p`
  (the Kummer–Dedekind conductor condition is trivially satisfied)

## Strategy

Package the ring equivalences from `Classification.lean`:
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`

into a monogenicity statement. Since `𝓞 = ℤ[θ]` exactly (not just finite index),
the conductor is the whole ring, so `exponent = 1`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- TODO: define the generator θ
-- noncomputable def ringOfIntegersGenerator :
--     𝓞 (Qsqrtd (d : ℚ)) := ...

-- TODO: prove monogenicity
-- theorem isMonogenic :
--     Algebra.adjoin ℤ {ringOfIntegersGenerator d} = ⊤ := ...

-- TODO: prove exponent = 1
-- theorem exponent_eq_one :
--     RingOfIntegers.exponent (ringOfIntegersGenerator d) = 1 := ...

-- TODO: Kummer-Dedekind applies unconditionally
-- theorem not_dvd_exponent (p : ℕ) [Fact p.Prime] :
--     ¬ p ∣ RingOfIntegers.exponent (ringOfIntegersGenerator d) := ...

end Splitting
end QuadraticNumberFields
