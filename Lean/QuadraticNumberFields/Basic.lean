/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Init.Data.Rat.Basic

/-!
# Basic Definitions for Quadratic Number Fields

This file provides the fundamental type `Qsqrtd d` representing the quadratic
field `ℚ(√d)` for a rational parameter `d`, along with basic operations:
trace, norm, and the canonical embedding of ℚ.

## Main Definitions

* `Qsqrtd d`: The quadratic algebra `QuadraticAlgebra ℚ d 0`, representing `ℚ(√d)`.
* `Qsqrtd.trace`: The trace `Tr(x) = x + x̄` where `x̄` is the conjugate.
* `Qsqrtd.norm`: The norm `N(x) = x · x̄ = x.re² - d · x.im²`.
* `Qsqrtd.embed`: The canonical embedding `ℚ → Q(√d)`.
-/

/-- The quadratic field `ℚ(√d)` as a type alias for `QuadraticAlgebra ℚ d 0`. -/
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

namespace Qsqrtd

/-- The trace of an element `x : Q(√d)`, defined as `Tr(x) = x + x̄ = 2 · x.re`. -/
abbrev trace (x : Qsqrtd d) : ℚ := x.re + (star x).re

/-- The norm of an element `x : Q(√d)`, defined as `N(x) = x · x̄ = x.re² - d · x.im²`. -/
abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- The canonical embedding of ℚ into `Q(√d)`, mapping `r ↦ r + 0·√d`. -/
abbrev embed (r : ℚ) : Qsqrtd d := algebraMap ℚ (Qsqrtd d) r

end Qsqrtd
