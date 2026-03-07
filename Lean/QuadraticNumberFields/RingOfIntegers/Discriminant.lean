/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Discriminant of Quadratic Number Fields

This file proves the explicit discriminant formula for `QuadraticNumberFields d`:

* If `d % 4 = 1`, then `NumberField.discr (QuadraticNumberFields d) = d`.
* If `d % 4 ≠ 1`, then `NumberField.discr (QuadraticNumberFields d) = 4 * d`.

## Main Definitions

* `discr_zsqrtd_basis`: The discriminant of the standard ℤ-basis of `ℤ[√d]` is `4 * d`.
* `discr_zOnePlusSqrtOverTwo_basis`: The discriminant of the standard ℤ-basis of
  `ℤ[(1+√d)/2]` is `1 + 4 * k` (i.e., `d` when `d = 1 + 4k`).

## Main Theorems

* `discr_of_mod_four_ne_one`: `NumberField.discr (QuadraticNumberFields d) = 4 * d`
  when `d % 4 ≠ 1`.
* `discr_of_mod_four_eq_one`: `NumberField.discr (QuadraticNumberFields d) = d`
  when `d % 4 = 1`.
* `discr_formula`: Unified discriminant formula combining both cases.

## Strategy

1. Compute `Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im`
   using the left-multiplication matrix and the standard QA basis.
2. Compute `Algebra.discr ℤ (QuadraticAlgebra.basis a b)` via the trace matrix determinant.
3. Transport to `NumberField.discr` using the classification isomorphism
   (`𝓞 K ≃+* R`) lifted to an `AlgEquiv ℤ`.
-/

open scoped NumberField
open Matrix

namespace QuadraticNumberFields
namespace RingOfIntegers

/-! ## Trace formula for QuadraticAlgebra over ℤ -/

/-- The left-multiplication matrix of `x : QuadraticAlgebra ℤ a b` with respect to
the standard basis `{1, ω}` is `[[x.re, a * x.im], [x.im, x.re + b * x.im]]`. -/
theorem leftMulMatrix_qa (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.leftMulMatrix (QuadraticAlgebra.basis a b) x =
      !![x.re, a * x.im; x.im, x.re + b * x.im] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases i <;> fin_cases j <;>
    simp [QuadraticAlgebra.basis,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]

/-- The algebraic trace on `QuadraticAlgebra ℤ a b`:
`Tr(x) = 2 * x.re + b * x.im`. -/
theorem trace_qa (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  rw [leftMulMatrix_qa]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-! ## Discriminant of the standard QuadraticAlgebra basis -/

/-- The trace matrix of the standard basis of `QuadraticAlgebra ℤ a b` is
`[[2, b], [b, 2*a + b²]]`. -/
theorem traceMatrix_qa (a b : ℤ) :
    Algebra.traceMatrix ℤ (QuadraticAlgebra.basis a b) =
      !![2, b; b, 2 * a + b ^ 2] := by
  ext i j
  simp only [Algebra.traceMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trace_qa, QuadraticAlgebra.basis]; ring

/-- The discriminant of the standard basis of `QuadraticAlgebra ℤ a b` is `4a + b²`.

For `ℤ[√d]` (a=d, b=0): discriminant = 4d.
For `ℤ[(1+√d)/2]` (a=k, b=1 where d=1+4k): discriminant = 4k+1 = d. -/
theorem discr_qa_basis (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = 4 * a + b ^ 2 := by
  rw [Algebra.discr_def, traceMatrix_qa]
  simp [Matrix.det_fin_two]
  ring

/-- The discriminant of `ℤ[√d]` is `4 * d`. -/
theorem discr_zsqrtd_basis (d : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis d 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd d)) = 4 * d := by
  rw [discr_qa_basis]
  ring

/-- The discriminant of `ℤ[(1+√(1+4k))/2]` is `1 + 4 * k`. -/
theorem discr_zOnePlusSqrtOverTwo_basis (k : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis k 1 :
      Module.Basis (Fin 2) ℤ (ZOnePlusSqrtOverTwo k)) = 1 + 4 * k := by
  rw [discr_qa_basis]
  ring

/-! ## Transport to NumberField.discr

We lift the `RingEquiv` from the classification to an `AlgEquiv ℤ` and use
`Algebra.discr_eq_discr_of_algEquiv` to transport the discriminant calculation
to the ring of integers `𝓞 K`. -/

/-- Any `RingEquiv` between ℤ-algebras is automatically a ℤ-algebra equivalence,
since there is a unique ring homomorphism `ℤ → R` for any ring `R`. -/
private def ringEquivToIntAlgEquiv
    {R S : Type*} [CommRing R] [Algebra ℤ R] [CommRing S] [Algebra ℤ S]
    (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) (fun n => by
    simp only [eq_intCast, map_intCast])

/-- **Discriminant of `Q(√d)` when `d % 4 ≠ 1`.**

When `d % 4 ≠ 1`, the ring of integers is `𝓞 ≅ ℤ[√d]` with ℤ-basis `{1, √d}`,
giving discriminant `4d`. -/
theorem discr_of_mod_four_ne_one (d : ℤ) [QuadFieldParam d]
    (hd4 : d % 4 ≠ 1) :
    NumberField.discr (QuadraticNumberFields d) = 4 * d := by
  -- Obtain the ring isomorphism 𝓞 K ≃+* Zsqrtd d
  obtain ⟨e⟩ := ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  -- Lift to ℤ-algebra equiv
  let f : Zsqrtd d ≃ₐ[ℤ] 𝓞 (QuadraticNumberFields d) :=
    ringEquivToIntAlgEquiv e.symm
  -- The transported family forms a basis of 𝓞 K
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (QuadraticNumberFields d)) :=
    (QuadraticAlgebra.basis d 0).map f.toLinearEquiv
  -- Use NumberField.discr_eq_discr
  rw [← NumberField.discr_eq_discr (QuadraticNumberFields d) b']
  -- b'.apply = f ∘ (QA.basis) so discr is preserved
  change Algebra.discr ℤ (⇑f ∘ ⇑(QuadraticAlgebra.basis d 0)) = 4 * d
  rw [← Algebra.discr_eq_discr_of_algEquiv _ f]
  exact discr_zsqrtd_basis d

/-- **Discriminant of `Q(√d)` when `d % 4 = 1`.**

When `d % 4 = 1`, writing `d = 1 + 4k`, the ring of integers is
`𝓞 ≅ ℤ[(1+√d)/2]` with ℤ-basis `{1, ω}` where `ω = (1+√d)/2`,
giving discriminant `d`. -/
theorem discr_of_mod_four_eq_one (d : ℤ) [QuadFieldParam d]
    (hd4 : d % 4 = 1) :
    NumberField.discr (QuadraticNumberFields d) = d := by
  -- Obtain the ring isomorphism
  obtain ⟨k, hk, ⟨e⟩⟩ := ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  subst hk
  -- Lift to ℤ-algebra equiv
  let f : ZOnePlusSqrtOverTwo k ≃ₐ[ℤ] 𝓞 (QuadraticNumberFields (1 + 4 * k)) :=
    ringEquivToIntAlgEquiv e.symm
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (QuadraticNumberFields (1 + 4 * k))) :=
    (QuadraticAlgebra.basis k 1).map f.toLinearEquiv
  rw [← NumberField.discr_eq_discr (QuadraticNumberFields (1 + 4 * k)) b']
  change Algebra.discr ℤ (⇑f ∘ ⇑(QuadraticAlgebra.basis k 1)) = 1 + 4 * k
  rw [← Algebra.discr_eq_discr_of_algEquiv _ f]
  exact discr_zOnePlusSqrtOverTwo_basis k

/-- **Unified discriminant formula for `Q(√d)`.**

For squarefree `d`:
* `NumberField.discr (Q(√d)) = d` if `d ≡ 1 (mod 4)`,
* `NumberField.discr (Q(√d)) = 4d` otherwise. -/
theorem discr_formula (d : ℤ) [QuadFieldParam d] :
    NumberField.discr (QuadraticNumberFields d) =
      if d % 4 = 1 then d else 4 * d := by
  split
  · exact discr_of_mod_four_eq_one d ‹_›
  · exact discr_of_mod_four_ne_one d ‹_›

/-! ## Examples

Regression tests for the discriminant formula on small squarefree values. -/

/-- **Gaussian integers**: `disc(Q(√(-1))) = -4`.

Since `-1 % 4 = 3 ≠ 1`, we get `disc = 4 · (-1) = -4`. -/
example : NumberField.discr (QuadraticNumberFields (-1)) = -4 := by
  exact discr_of_mod_four_ne_one (-1) (by decide)

/-- **Eisenstein integers**: `disc(Q(√(-3))) = -3`.

Since `-3 % 4 = 1`, we get `disc = -3`. -/
example : NumberField.discr (QuadraticNumberFields (-3)) = -3 := by
  exact discr_of_mod_four_eq_one (-3) (by decide)

/-- **`Q(√(-5))`**: `disc(Q(√(-5))) = -20`.

Since `-5 % 4 = 3 ≠ 1`, we get `disc = 4 · (-5) = -20`. -/
instance : QuadFieldParam (-5 : ℤ) := by
  letI : Fact (Nat.Prime ((-5 : ℤ).natAbs)) := ⟨by decide⟩
  exact inferInstance

example : NumberField.discr (QuadraticNumberFields (-5)) = -20 :=
  discr_of_mod_four_ne_one (-5) (by decide)

end RingOfIntegers
end QuadraticNumberFields
