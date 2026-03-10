/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.ZOnePlusSqrtOverTwo

/-!
# Embedding Criteria for Quadratic Rings of Integers

This file packages the general embedding criterion used to identify the ring of
integers with a concrete quadratic order, together with basic integrality
transport lemmas for the standard models.

## Main Theorems

* `ringOfIntegers_equiv_of_integralClosure`: identify `𝓞 K` with any explicit
  integral closure.
* `ringOfIntegers_equiv_of_embedding`: identify `𝓞 K` from an injective ring
  hom whose image is exactly the integral elements.
* `isIntegral_toQsqrtd`: elements of `ℤ[√d]` map to integral elements of `Q(√d)`.
* `isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo`: elements of `ℤ[(1+√d)/2]` map
  to integral elements of `Q(√d)`.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

open scoped NumberField

/-- **Generic fact**: the ring of integers `𝓞 K` is ring-isomorphic to any
commutative ring `R` equipped with an `IsIntegralClosure R ℤ K` instance.

This is the universal property of the integral closure, packaged as a `RingEquiv`.
It is **not specific to quadratic fields**. -/
theorem ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    Nonempty (𝓞 K ≃+* R) :=
  ⟨NumberField.RingOfIntegers.equiv (K := K) (R := R)⟩

/-- Any image of an integral element under a ring hom remains integral over `ℤ`. -/
private lemma isIntegral_of_intModel_image
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra.IsIntegral ℤ R] (φ : R →+* S) (z : R) :
    IsIntegral ℤ (φ z) :=
  map_isIntegral_int φ (Algebra.IsIntegral.isIntegral (R := ℤ) z)

/-- Every element in the image of `Zsqrtd d → Q(√d)` is integral over `ℤ`. -/
lemma isIntegral_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    IsIntegral ℤ (Zsqrtd.toQsqrtdHom d z) :=
  isIntegral_of_intModel_image (Zsqrtd d) (Qsqrtd (d : ℚ)) (Zsqrtd.toQsqrtdHom d) z

/-- Every element in the image of `ZOnePlusSqrtOverTwo k → Q(√(1 + 4k))` is
integral over `ℤ`. -/
lemma isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    IsIntegral ℤ (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k z) :=
  isIntegral_of_intModel_image (ZOnePlusSqrtOverTwo k) (Qsqrtd ((1 + 4 * k : ℤ) : ℚ))
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k) z

/-- General criterion identifying `𝓞 K` with a concrete embedded order. -/
theorem ringOfIntegers_equiv_of_embedding
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

end RingOfIntegers
end QuadraticNumberFields
