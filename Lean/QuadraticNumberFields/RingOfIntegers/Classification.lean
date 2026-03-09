/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.CommonInstances
import QuadraticNumberFields.RingOfIntegers.Integrality
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.RingOfIntegers.ZOnePlusSqrtOverTwo
import QuadraticNumberFields.RingEquiv
import QuadraticNumberFields.Instances

/-!
# Ring Of Integers Classification

This file contains the final classification theorem for
`𝓞 (Qsqrtd (d : ℚ))`.

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

section FieldLevel

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

end FieldLevel

section ParamLevel

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`. -/
theorem ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d) := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  exact ringOfIntegers_equiv_of_embedding (Qsqrtd (d : ℚ)) (Zsqrtd d)
    (Zsqrtd.toQsqrtdHom d)
    (Zsqrtd.toQsqrtdHom_injective d)
    (by
      intro x hx
      exact exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd_sf hd_ne hd4 hx)
    (by
      intro z
      exact isIntegral_toQsqrtd d z)

/-- If `d % 4 ≠ 1`, then `ℤ[√d]` is a Dedekind domain because it is the full
ring of integers of `Q(√d)`. -/
theorem isDedekindDomain_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    IsDedekindDomain (Zsqrtd d) := by
  rcases ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4 with ⟨e⟩
  letI : IsDedekindDomain (𝓞 (Qsqrtd (d : ℚ))) := inferInstance
  exact RingEquiv.isDedekindDomain e

/-- If `d % 4 = 1`, then `ℤ[√d]` is not a Dedekind domain. Equivalently,
it is not integrally closed because `(1 + √d) / 2` is integral but does not lie in
`ℤ[√d]`. -/
theorem not_isDedekindDomain_zsqrtd_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    ¬ IsDedekindDomain (Zsqrtd d) := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  letI : Algebra (Zsqrtd d) (Qsqrtd (d : ℚ)) := (Zsqrtd.toQsqrtdHom d).toAlgebra
  letI : FaithfulSMul (Zsqrtd d) (Qsqrtd (d : ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective (Zsqrtd d) (Qsqrtd (d : ℚ))).mpr
      (Zsqrtd.toQsqrtdHom_injective d)
  have hFrac : IsFractionRing (Zsqrtd d) (Qsqrtd (d : ℚ)) := by
    refine IsFractionRing.of_field (R := Zsqrtd d) (K := Qsqrtd (d : ℚ)) ?_
    intro z
    refine ⟨⟨(z.re.num : ℤ) * z.im.den, (z.im.num : ℤ) * z.re.den⟩,
        ((z.re.den * z.im.den : ℕ) : Zsqrtd d), ?_⟩
    refine (eq_div_iff ?_).2 ?_
    · norm_num
    · ext
      · simp only [Nat.cast_mul, map_mul, map_natCast, QuadraticAlgebra.re_mul,
          QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, mul_zero, add_zero,
          QuadraticAlgebra.im_mul, zero_mul]
        calc
          z.re * (↑z.re.den * ↑z.im.den) = z.re * (z.re.den : ℚ) * z.im.den := by ring
          _ = ((z.re.num : ℤ) : ℚ) * z.im.den := by rw [Rat.mul_den_eq_num]
          _ = (((z.re.num : ℤ) * z.im.den : ℤ) : ℚ) := by norm_num
      · simp only [Nat.cast_mul, map_mul, map_natCast, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, mul_zero, zero_mul,
          add_zero, QuadraticAlgebra.re_mul, zero_add]
        calc
          z.im * (↑z.re.den * ↑z.im.den) = z.im * (z.im.den : ℚ) * z.re.den := by ring
          _ = ((z.im.num : ℤ) : ℚ) * z.re.den := by rw [Rat.mul_den_eq_num]
          _ = (((z.im.num : ℤ) * z.re.den : ℤ) : ℚ) := by norm_num
  letI : IsFractionRing (Zsqrtd d) (Qsqrtd (d : ℚ)) := hFrac
  intro hDed
  letI : IsDedekindDomain (Zsqrtd d) := hDed
  letI : Module (Zsqrtd d) (Zsqrtd d) := Semiring.toModule
  have hIC : IsIntegrallyClosed (Zsqrtd d) := IsDedekindRing.toIsIntegralClosure
  letI : IsIntegrallyClosed (Zsqrtd d) := hIC
  rcases exists_k_of_mod_four_eq_one (d := d) hd4 with ⟨k, hk⟩
  subst hk
  let x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ)) := halfInt (1 + 4 * k) 1 1
  have hx_def :
      x = _root_.ZOnePlusSqrtOverTwo.toQsqrtdFun k (⟨0, 1⟩ : _root_.ZOnePlusSqrtOverTwo k) := by
    ext <;> simp [x, halfInt, _root_.ZOnePlusSqrtOverTwo.toQsqrtdFun]
  have hx_integral_Z : IsIntegral ℤ x := by
    rw [hx_def]
    exact isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k
      (z := (⟨0, 1⟩ : _root_.ZOnePlusSqrtOverTwo k))
  have hx_integral : IsIntegral (Zsqrtd (1 + 4 * k)) x := hx_integral_Z.tower_top
  rcases (isIntegrallyClosed_iff (Qsqrtd (((1 + 4 * k : ℤ) : ℚ)))).mp hIC hx_integral with
    ⟨z, hz⟩
  have h_even : 2 ∣ (1 : ℤ) ∧ 2 ∣ (1 : ℤ) :=
    (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even (1 + 4 * k) 1 1).mp
      ⟨z, by
        simpa [x, halfInt, RingHom.toAlgebra] using hz⟩
  omega

/-- For a valid quadratic parameter `d`, `ℤ[√d]` is Dedekind exactly in the
`d % 4 ≠ 1` branch, i.e. precisely when it is the full ring of integers. -/
theorem isDedekindDomain_zsqrtd_iff_mod_four_ne_one
    :
    IsDedekindDomain (Zsqrtd d) ↔ d % 4 ≠ 1 := by
  constructor
  · intro hDed hd4
    exact not_isDedekindDomain_zsqrtd_of_mod_four_eq_one d hd4 hDed
  · exact isDedekindDomain_zsqrtd_of_mod_four_ne_one d

/-- If `d % 4 = 1`, writing `d = 1 + 4k`,
then `𝓞 (Q(√d)) ≃+* ZOnePlusSqrtOverTwo k`. -/
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtOverTwo k) := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  rcases exists_k_of_mod_four_eq_one (d := d) hd4 with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  subst hk
  have hd_ne' : (1 + 4 * k) ≠ 1 := hd_ne
  exact ringOfIntegers_equiv_of_embedding
    (Qsqrtd (((1 + 4 * k : ℤ) : ℚ))) (ZOnePlusSqrtOverTwo k)
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k)
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom_injective k)
    (by
      intro x hx
      exact exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four k hd_sf hd_ne' hx)
    (by
      intro z
      exact isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z)

/-- **Classification of the ring of integers of `Q(√d)`.**

For squarefree `d ≠ 1`, exactly one of the following holds:
* If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`.
* If `d % 4 = 1`, then writing `d = 1 + 4k`,
  `𝓞 (Q(√d)) ≃+* ℤ[(1+√d)/2]`. -/
theorem ringOfIntegers_classification
    :
    (d % 4 ≠ 1 ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtOverTwo k)) := by
  by_cases hd4 : d % 4 = 1
  · exact Or.inr <| ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  · exact Or.inl ⟨hd4, ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4⟩

/-! ## Example 2.8 (Boxer Notes): Gaussian and Eisenstein Integers -/

/-- **Gaussian integers**: `𝓞(Q(√(-1))) ≃ ℤ[i]`. -/
example : Nonempty (𝓞 (Qsqrtd ((-1 : ℤ) : ℚ)) ≃+* Zsqrtd (-1)) :=
  ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (-1) (by decide)


/-- **Eisenstein integers**: `𝓞(Q(√(-3))) ≃ ℤ[(1+√(-3))/2]`. -/
example : ∃ k : ℤ, (-3 : ℤ) = 1 + 4 * k ∧
    Nonempty (𝓞 (Qsqrtd ((-3 : ℤ) : ℚ)) ≃+* ZOnePlusSqrtOverTwo k) :=
  ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one (-3) (by decide)


end ParamLevel

end RingOfIntegers
end QuadraticNumberFields
