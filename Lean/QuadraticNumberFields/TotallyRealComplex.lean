/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Instances
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Totally Real, Totally Complex, and CM Field Classification

This file classifies quadratic number fields `Q(√d)` according to the sign of `d`:

* `d > 0`: `Q(√d)` is **totally real** — all embeddings into `ℂ` have real image.
* `d < 0`: `Q(√d)` is **totally complex** and a **CM field** — no embedding has real image,
  and `Q(√d)` is a quadratic extension of its totally real subfield `ℚ`.

## Main Theorems

* `QuadraticNumberFields.isTotallyReal`: `Q(√d)` is totally real when `0 < d`.
* `QuadraticNumberFields.isTotallyComplex`: `Q(√d)` is totally complex when `d < 0`.
* `QuadraticNumberFields.isCMField`: `Q(√d)` is a CM field when `d < 0`.

## Proof Strategy

For any embedding `φ : Q(√d) →+* ℂ`, we have `φ(ω)² = d` in `ℂ`.
Writing `φ(ω) = a + bi` gives `a² - b² = d` and `2ab = 0`.

* When `d > 0`: the case `a = 0` gives `-b² = d > 0`, a contradiction. So `b = 0`,
  meaning `φ(ω) ∈ ℝ`, hence the embedding is real.
* When `d < 0`: if the embedding were real, then `b = 0`, giving `a² = d < 0`,
  contradicting `a² ≥ 0`.
-/

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and `QuadraticAlgebra.instAlgebra`.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

variable {d : ℤ} [QuadFieldParam d]

/-- With the `ℚ`-algebra diamond resolved, `IsQuadraticExtension` follows directly from
`QuadraticAlgebra.finrank_eq_two`. This re-derives the instance from `Instances.lean` in the
context where `DivisionRing.toRatAlgebra` is disabled. -/
instance : Algebra.IsQuadraticExtension ℚ (QuadraticNumberFields d) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

/-- For any infinite place `v` of `Q(√d)`, the image of `ω` satisfies `φ(ω)² = d`. -/
theorem embedding_omega_sq (v : NumberField.InfinitePlace (QuadraticNumberFields d)) :
    v.embedding QuadraticAlgebra.omega ^ 2 = ((d : ℚ) : ℂ) := by
  rw [sq, ← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [Algebra.smul_def]

/-- The real part of `φ(ω)²` decomposes as `re² - im²`. -/
private theorem embedding_omega_sq_re
    (v : NumberField.InfinitePlace (QuadraticNumberFields d)) :
    (v.embedding QuadraticAlgebra.omega).re ^ 2 -
    (v.embedding QuadraticAlgebra.omega).im ^ 2 = (d : ℝ) := by
  have := congr_arg Complex.re (embedding_omega_sq v)
  simp [sq, Complex.mul_re] at this; linarith

/-- The imaginary part of `φ(ω)²` gives `2 · re · im = 0`. -/
private theorem embedding_omega_sq_im
    (v : NumberField.InfinitePlace (QuadraticNumberFields d)) :
    2 * (v.embedding QuadraticAlgebra.omega).re *
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have := congr_arg Complex.im (embedding_omega_sq v)
  simp [sq, Complex.mul_im] at this; linarith

/-- When `d > 0`, the image of `ω` under any embedding is real (imaginary part is zero).
From `2ab = 0`: if `a = 0` then `-b² = d > 0`, contradiction; so `b = 0`. -/
private theorem embedding_omega_im_eq_zero
    (v : NumberField.InfinitePlace (QuadraticNumberFields d)) (hd : 0 < d) :
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have hre := embedding_omega_sq_re v
  have him := embedding_omega_sq_im v
  rcases mul_eq_zero.mp him with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · rw [h] at hre; simp at hre
      nlinarith [sq_nonneg (v.embedding QuadraticAlgebra.omega).im,
                 (show (d : ℝ) > 0 from by exact_mod_cast hd)]
  · exact h

/-- If `im(φ(ω)) = 0`, then `conj ∘ φ = φ`. We lift both `RingHom`s to `ℚ`-`AlgHom`s and
apply `QuadraticAlgebra.algHom_ext`: they agree on `ω`, hence on all of `Q(√d)`. -/
private theorem conjugate_embedding_eq
    (v : NumberField.InfinitePlace (QuadraticNumberFields d))
    (hω_im : (v.embedding QuadraticAlgebra.omega).im = 0) :
    NumberField.ComplexEmbedding.conjugate v.embedding = v.embedding := by
  rw [← @RingHom.toRatAlgHom_toRingHom (QuadraticNumberFields d) ℂ _ _ _ _
    (NumberField.ComplexEmbedding.conjugate v.embedding),
    ← @RingHom.toRatAlgHom_toRingHom (QuadraticNumberFields d) ℂ _ _ _ _
    v.embedding]
  congr 1
  apply QuadraticAlgebra.algHom_ext
  change (NumberField.ComplexEmbedding.conjugate v.embedding).toRatAlgHom
    QuadraticAlgebra.omega = v.embedding.toRatAlgHom QuadraticAlgebra.omega
  simp only [RingHom.toRatAlgHom_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.mpr hω_im

/-- A real quadratic field `Q(√d)` with `d > 0` is totally real:
all embeddings into `ℂ` have image contained in `ℝ`. -/
theorem isTotallyReal (hd : 0 < d) :
    NumberField.IsTotallyReal (QuadraticNumberFields d) where
  isReal v := by
    rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    exact conjugate_embedding_eq v (embedding_omega_im_eq_zero v hd)

/-- An imaginary quadratic field `Q(√d)` with `d < 0` is totally complex:
no embedding into `ℂ` has image contained in `ℝ`. -/
theorem isTotallyComplex (hd : d < 0) :
    NumberField.IsTotallyComplex (QuadraticNumberFields d) where
  isComplex v := by
    rw [NumberField.InfinitePlace.isComplex_iff, NumberField.ComplexEmbedding.isReal_iff]
    intro hreal
    have hω_real : (v.embedding QuadraticAlgebra.omega).im = 0 := by
      have h := RingHom.congr_fun hreal QuadraticAlgebra.omega
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq] at h
      exact Complex.conj_eq_iff_im.mp h
    have hre := embedding_omega_sq_re v
    rw [hω_real] at hre; simp at hre
    linarith [sq_nonneg (v.embedding QuadraticAlgebra.omega).re,
              (show (d : ℝ) < 0 from by exact_mod_cast hd)]

/-- An imaginary quadratic field `Q(√d)` with `d < 0` is a CM field:
it is totally complex and a quadratic extension of its totally real subfield `ℚ`. -/
theorem isCMField (hd : d < 0) :
    letI := isTotallyComplex hd
    NumberField.IsCMField (QuadraticNumberFields d) :=
  letI := isTotallyComplex hd
  NumberField.IsCMField.ofCMExtension ℚ (QuadraticNumberFields d)

end QuadraticNumberFields
