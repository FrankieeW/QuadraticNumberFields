/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import LeanPrism
import QuadraticNumberFields.RingOfIntegers.Classification

/-!
# Norm Multiplicativity

This file formalizes norm properties for quadratic number fields and their
rings of integers, with sections separating explicit formulas from the
classification-dependent statements.
-/

open scoped NumberField

namespace QuadraticNumberFields

/-! ## Norm Multiplicativity on `Q(√d)` -/

/-- The norm on `Q(√d)` is multiplicative: `N(xy) = N(x) N(y)`. -/
theorem norm_mul (d : ℚ) (x y : Qsqrtd d) :
    Qsqrtd.norm (x * y) = Qsqrtd.norm x * Qsqrtd.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm maps `1` to `1`. -/
theorem norm_one (d : ℚ) : Qsqrtd.norm (1 : Qsqrtd d) = 1 :=
  QuadraticAlgebra.norm.map_one

namespace RingOfIntegers

/-! ## Explicit Norm Formulas -/

/-- The norm of an element of `Zsqrtd d` is an integer: `N(a + b√d) = a² - d·b²`. -/
theorem norm_zsqrtd (d : ℤ) (z : Zsqrtd d) :
    Zsqrtd.norm z = z.re ^ 2 - d * z.im ^ 2 := by
  unfold Zsqrtd.norm QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  ring

/-- The norm on `Zsqrtd d` is multiplicative. -/
theorem norm_mul_zsqrtd (d : ℤ) (x y : Zsqrtd d) :
    Zsqrtd.norm (x * y) = Zsqrtd.norm x * Zsqrtd.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm of `a + b√d` embeds to `a² - d·b²` in `ℚ`. -/
theorem norm_zsqrtd_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    Qsqrtd.norm (Zsqrtd.toQsqrtd z) = (Zsqrtd.norm z : ℚ) := by
  unfold Zsqrtd.norm Qsqrtd.norm Zsqrtd.toQsqrtd QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  push_cast
  ring

/-- For `d % 4 ≠ 1`, elements of `ℤ[√d]` have integer norm after embedding. -/
theorem norm_mem_zsqrtd (d : ℤ) (z : Zsqrtd d) :
    ∃ n : ℤ, Qsqrtd.norm (Zsqrtd.toQsqrtd z) = n := by
  exact ⟨Zsqrtd.norm z, norm_zsqrtd_toQsqrtd d z⟩

/-- The norm on `ZOnePlusSqrtOverTwo k` is multiplicative. -/
theorem norm_mul_zOnePlusSqrtOverTwo (k : ℤ) (x y : ZOnePlusSqrtOverTwo k) :
    QuadraticAlgebra.norm (x * y) =
      QuadraticAlgebra.norm x * QuadraticAlgebra.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm of an element of `ZOnePlusSqrtOverTwo k` is `a² + a·b - k·b²`. -/
theorem norm_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    QuadraticAlgebra.norm z = z.re ^ 2 + z.re * z.im - k * z.im ^ 2 := by
  unfold QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  ring

/-- The norm of `a + b·ω` embeds correctly to `ℚ`. -/
theorem norm_zOnePlusSqrtOverTwo_toQsqrtd (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    Qsqrtd.norm (ZOnePlusSqrtOverTwo.toQsqrtdHom k z) =
      ((QuadraticAlgebra.norm z : ℤ) : ℚ) := by
  have h1 : (ZOnePlusSqrtOverTwo.toQsqrtdHom k z).re = (z.re : ℚ) + (z.im : ℚ) / 2 := rfl
  have h2 : (ZOnePlusSqrtOverTwo.toQsqrtdHom k z).im = (z.im : ℚ) / 2 := rfl
  simp only [Qsqrtd.norm, QuadraticAlgebra.norm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h1, h2]
  simp only [ZOnePlusSqrtOverTwo.qParam]
  push_cast
  ring

/-- For `d % 4 = 1`, elements of `ℤ[(1+√d)/2]` have integer norm after embedding. -/
theorem norm_mem_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    ∃ n : ℤ, Qsqrtd.norm (ZOnePlusSqrtOverTwo.toQsqrtdHom k z) = n := by
  exact ⟨QuadraticAlgebra.norm z, norm_zOnePlusSqrtOverTwo_toQsqrtd k z⟩

section ParamLevel

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- For `α ∈ 𝓞(Q(√d))`, the norm `N(α)` is an integer.

This follows from the classification theorem: elements of the ring of integers
live in either `ℤ[√d]` or `ℤ[(1+√d)/2]`, both of which have integer-valued norm.

TODO: This proof requires establishing that the ring isomorphism from the
classification commutes with the coercion to the number field. -/
theorem norm_mem_ringOfIntegers (α : 𝓞 (Qsqrtd (d : ℚ))) :
    ∃ n : ℤ, Qsqrtd.norm (α : Qsqrtd (d : ℚ)) = n := by
  rcases ringOfIntegers_classification d with ⟨hd4, h_equiv⟩ | ⟨k, hk, h_equiv⟩
  · -- d % 4 ≠ 1 branch: 𝓞 ≃ ℤ[√d]
    let e := Classical.choice h_equiv
    let z : Zsqrtd d := e α
    -- TODO: Prove that (α : Qsqrtd (d : ℚ)) = Zsqrtd.toQsqrtd z
    sorry
  · -- d % 4 = 1 branch: 𝓞 ≃ ℤ[(1 + √d)/2]
    subst hk
    let e := Classical.choice h_equiv
    let z : ZOnePlusSqrtOverTwo k := e α
    -- TODO: Prove that (α : Qsqrtd ...) = toQsqrtdHom k z
    sorry

end ParamLevel

/-! ## Unit Criterion -/

/-- An element of `QuadraticAlgebra ℤ a b` is a unit iff its norm is `±1`. -/
theorem isUnit_iff_norm_eq_one_or_neg_one
    {a b : ℤ} (z : QuadraticAlgebra ℤ a b) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
  constructor
  · intro h
    have h_norm_unit : IsUnit (QuadraticAlgebra.norm z) :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mp h
    rcases Int.isUnit_iff.mp h_norm_unit with h1 | hneg1
    · exact Or.inl h1
    · exact Or.inr hneg1
  · intro h
    rcases h with h1 | hneg1
    · exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (h1 ▸ isUnit_one)
    · exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hneg1 ▸ isUnit_neg_one)

/-- An element of `ℤ[√d]` is a unit iff its norm is `±1`. -/
theorem isUnit_zsqrtd_iff_norm_eq_one_or_neg_one (d : ℤ) (z : Zsqrtd d) :
    IsUnit z ↔ Zsqrtd.norm z = 1 ∨ Zsqrtd.norm z = -1 := by
  simpa using isUnit_iff_norm_eq_one_or_neg_one z

/-- An element of `ℤ[(1+√(1+4k))/2]` is a unit iff its norm is `±1`. -/
theorem isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one
    (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
  simpa using isUnit_iff_norm_eq_one_or_neg_one z

end RingOfIntegers
end QuadraticNumberFields
