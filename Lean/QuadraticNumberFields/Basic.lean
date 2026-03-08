/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Trace.Basic
import Init.Data.Rat.Basic

/-!
# Basic Definitions for Quadratic Number Fields

This file provides the fundamental type `Qsqrtd d` representing the quadratic
field `ℚ(√d)` for a rational parameter `d`, along with basic operations:
trace, norm, and the canonical embedding of ℚ.

## Main Definitions

* `Qsqrtd d`: The quadratic algebra `QuadraticAlgebra ℚ d 0`, representing `ℚ(√d)`.
* `Qsqrtd.trace`: The trace `Tr(x)`, defined via mathlib's `Algebra.trace`.
* `Qsqrtd.norm`: The norm `N(x) = x · x̄ = x.re² - d · x.im²`.
* `Qsqrtd.embed`: The canonical embedding `ℚ → Q(√d)`.
-/

/-- The quadratic field `ℚ(√d)` as a type alias for `QuadraticAlgebra ℚ d 0`. -/
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

namespace Qsqrtd

/-- The trace of an element `x : Q(√d)`, defined via `Algebra.trace`. -/
noncomputable abbrev trace (x : Qsqrtd d) : ℚ := Algebra.trace ℚ (Qsqrtd d) x

/-- `Qsqrtd.trace` is definitionally mathlib's algebra trace. -/
theorem trace_eq_algebra_trace (x : Qsqrtd d) :
    Qsqrtd.trace x = Algebra.trace ℚ (Qsqrtd d) x := rfl

private theorem leftMulMatrix_eq (x : Qsqrtd d) :
    Algebra.leftMulMatrix (QuadraticAlgebra.basis d 0) x = !![x.re, d * x.im; x.im, x.re] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

/-- The trace in `Q(√d)` is `x + x̄`. -/
@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Qsqrtd.trace x = x.re + (star x).re := by
  change Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0), leftMulMatrix_eq,
    Matrix.trace_fin_two_of]
  simp

/-- In the model `Q(√d) = QuadraticAlgebra ℚ d 0`, the trace is `2 * re`. -/
@[simp] theorem trace_eq_two_re (x : Qsqrtd d) :
    Qsqrtd.trace x = 2 * x.re := by
  rw [trace_eq_re_add_re_star]
  simp
  ring

/-- The norm of an element `x : Q(√d)`, defined as `N(x) = x · x̄ = x.re² - d · x.im²`. -/
abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- The canonical embedding of ℚ into `Q(√d)`, mapping `r ↦ r + 0·√d`. -/
abbrev embed (r : ℚ) : Qsqrtd d := algebraMap ℚ (Qsqrtd d) r

end Qsqrtd
