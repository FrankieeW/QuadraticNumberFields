/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Zsqrtd

/-!
# `HalfInt` Layer

This file is for half-integer representatives `(a + b√d) / 2` and their
structural lemmas.

## TODO (Revised)

1. Canonical half-integer API (reuse existing `Zsqrtd` definitions)
- [x] Expose `halfInt` here as a thin wrapper/alias of `Zsqrtd.halfInt`.
- [x] Add `omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1`.
- [x] Add coordinate simp lemmas for `halfInt` and `omegaHalf`.

2. Port formulas from old draft
- [x] Port `trace_halfInt`.
- [x] Port `norm_halfInt`.
- [ ] Keep theorem names and statement shape compatible with `Integrality.lean`.

3. Classification-facing lemmas
- [ ] Add parity normal-form lemmas for half-integer coordinates.
- [ ] Add lemmas reducing image-membership goals to divisibility-by-2 goals.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- Canonical half-integer representative `(a' + b'√d)/2` in `Q(√d)`. -/
abbrev halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  Zsqrtd.halfInt (d := d) a' b'

/-- The distinguished half-integer generator `(1 + √d)/2`. -/
abbrev omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1

@[simp] theorem halfInt_re (d a' b' : ℤ) :
    (halfInt d a' b').re = (a' : ℚ) / 2 := rfl

@[simp] theorem halfInt_im (d a' b' : ℤ) :
    (halfInt d a' b').im = (b' : ℚ) / 2 := rfl

@[simp] theorem omegaHalf_re (d : ℤ) :
    (omegaHalf d).re = (1 : ℚ) / 2 := rfl

@[simp] theorem omegaHalf_im (d : ℤ) :
    (omegaHalf d).im = (1 : ℚ) / 2 := rfl

/-- Trace of `halfInt` is `a'`. -/
theorem trace_halfInt (d a' b' : ℤ) : Qsqrtd.trace (halfInt d a' b') = a' := by
  simp [halfInt, Qsqrtd.trace]

/-- Norm of `halfInt` is `(a'² - d*b'²)/4`. -/
theorem norm_halfInt (d a' b' : ℤ) :
    Qsqrtd.norm (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  simp [halfInt, Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

end RingOfIntegers
end QuadraticNumberFields
