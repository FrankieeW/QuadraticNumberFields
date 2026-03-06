/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Integrality
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.RingOfIntegers.ZOnePlusSqrtOverTwo

/-!
# Ring Of Integers Classification

This file contains the final classification theorem for
`𝓞 (QuadraticNumberFields d)`.

## Main Results

* `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  if `d % 4 ≠ 1` then `𝓞 (Q(√d)) ≃+* ℤ√d`.
* `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  if `d % 4 = 1` then `𝓞 (Q(√d)) ≃+* ℤ[(1+√d)/2]`.
* `ringOfIntegers_classification`:
  combines both branches into a single disjunction.

## Design

Integrality ingredients (`IsIntegralClosure` constructions,
half-integer normal form, etc.) live in `Integrality.lean`.
This file assembles the final `𝓞 ≃+* R` isomorphisms and the
top-level classification.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

private theorem ringOfIntegers_equiv_of_embedding
    (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z)) :
    Nonempty (𝓞 K ≃+* R) := by
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := by
        simpa [RingHom.toAlgebra] using h_inj
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, by simpa [RingHom.toAlgebra] using hz⟩
        · rintro ⟨z, rfl⟩
          simpa [RingHom.toAlgebra] using h_integral z }
  exact ringOfIntegers_equiv_of_integralClosure K R

/-- If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`. -/
theorem ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one
    (d : ℤ) [QuadFieldParam d]
    (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (QuadraticNumberFields d) ≃+* Zsqrtd d) :=
  ringOfIntegers_equiv_of_embedding (QuadraticNumberFields d) (Zsqrtd d)
    (Zsqrtd.toQsqrtdHom d)
    (by simpa [QuadraticNumberFields] using (Zsqrtd.toQsqrtdHom_injective d))
    (by
      intro x hx
      rcases exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd4 (x := x) hx with ⟨z, hz⟩
      exact ⟨z, by simpa [QuadraticNumberFields] using hz⟩)
    (by
      intro z
      simpa [QuadraticNumberFields] using isIntegral_toQsqrtd d z)

/-- If `d % 4 = 1`, writing `d = 1 + 4k`,
then `𝓞 (Q(√d)) ≃+* ZOnePlusSqrtOverTwo k`. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (d : ℤ) [QuadFieldParam d]
    (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadraticNumberFields d) ≃+*
        ZOnePlusSqrtOverTwo k) := by
  rcases exists_k_of_mod_four_eq_one (d := d) hd4 with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  subst hk
  exact ringOfIntegers_equiv_of_embedding
    (QuadraticNumberFields (1 + 4 * k)) (ZOnePlusSqrtOverTwo k)
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k)
    (by
      simpa [QuadraticNumberFields] using
        (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom_injective k))
    (by
      intro x hx
      rcases exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four k (x := x) hx with ⟨z, hz⟩
      exact ⟨z, by simpa [QuadraticNumberFields] using hz⟩)
    (by
      intro z
      simpa [QuadraticNumberFields] using isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z)

/-- **Classification of the ring of integers of `Q(√d)`.**

For squarefree `d`, exactly one of the following holds:
* If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`.
* If `d % 4 = 1`, then writing `d = 1 + 4k`,
  `𝓞 (Q(√d)) ≃+* ℤ[(1+√d)/2]`. -/
theorem ringOfIntegers_classification
    (d : ℤ) [QuadFieldParam d]
    :
    (d % 4 ≠ 1 ∧
      Nonempty (𝓞 (QuadraticNumberFields d) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadraticNumberFields d) ≃+*
        ZOnePlusSqrtOverTwo k)) := by
  by_cases hd4 : d % 4 = 1
  · exact Or.inr <| ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  · exact Or.inl ⟨hd4, ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4⟩

/-! ## Example 2.8 (Boxer Notes): Gaussian and Eisenstein Integers

These are classical examples of rings of integers in imaginary quadratic fields.

* **Gaussian integers** `ℤ[i] = ℤ[√(-1)]`: d = -1, d % 4 = 3 ≢ 1
* **Eisenstein integers** `ℤ[ω]` where `ω = (1+√(-3))/2`: d = -3, d % 4 = 1
-/

/-- **Gaussian integers**: `𝓞(Q(√(-1))) ≃ ℤ[i]`.

Since -1 % 4 = 3 ≠ 1, we are in the non-1-mod-4 branch. -/
example : Nonempty (𝓞 (QuadraticNumberFields (-1)) ≃+* Zsqrtd (-1)) :=
  ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (-1) (by decide)

/-- **Eisenstein integers**: `𝓞(Q(√(-3))) ≃ ℤ[ω]` where `ω = (1+√(-3))/2`.

Since -3 % 4 = 1, we are in the 1-mod-4 branch with k = -1
(since -3 = 1 + 4·(-1)). -/
example : ∃ k : ℤ, (-3 : ℤ) = 1 + 4 * k ∧
    Nonempty (𝓞 (QuadraticNumberFields (-3)) ≃+* ZOnePlusSqrtOverTwo k) :=
  ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one (-3) (by decide)

end RingOfIntegers
end QuadraticNumberFields
