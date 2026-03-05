/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

General instances for `ℤ[√d]` when `d < 0`: no zero divisors and integral domain.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic

open Zsqrtd

namespace Zsqrtd

instance instNoZeroDivisors {d : ℤ} [Fact (d < 0)] : NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : Zsqrtd.norm (a * b) = 0 := by
      simp [hab, Zsqrtd.norm_zero (d := d)]
    have hmulnorm : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      simpa [Zsqrtd.norm_mul] using hnorm
    rcases mul_eq_zero.mp hmulnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (d := d) Fact.out a).1 ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (d := d) Fact.out b).1 hb)

instance instIsDomain {d : ℤ} [Fact (d < 0)] : IsDomain (Zsqrtd d) :=
  NoZeroDivisors.to_isDomain (Zsqrtd d)

end Zsqrtd
