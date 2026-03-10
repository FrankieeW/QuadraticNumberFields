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
# Classification of the Ring of Integers of Quadratic Fields

This file proves the classical **ring of integers classification theorem** for
quadratic number fields `ℚ(√d)`, where `d` is a squarefree integer with `d ≠ 1`.

The result is a staple of algebraic number theory (see e.g.
[Marcus, *Number Fields*, Theorem 2.16], [Neukirch, *Algebraic Number Theory*, I.2],
[Boxer, *Algebraic Number Theory Notes*, Example 2.8]):

> **Theorem.** Let `d` be a squarefree integer, `d ≠ 1`. Then
>
> * if `d ≢ 1 (mod 4)`, the ring of integers of `ℚ(√d)` is `ℤ[√d]`;
> * if `d ≡ 1 (mod 4)`, writing `d = 1 + 4k`, it is `ℤ[(1 + √d)/2]`.

## Proof Strategy

An element `x ∈ ℚ(√d)` is integral over `ℤ` iff its trace `Tr(x) = 2·re(x)` and
norm `N(x) = re(x)² − d·im(x)²` are both integers. Writing `x = (a' + b'√d)/2`
in half-integer normal form (see `Integrality.lean`), integrality becomes the
divisibility condition `4 ∣ (a'² − d·b'²)`. The mod-4 arithmetic in `ModFour.lean`
then splits into the two branches above.

## Main Results

* `ringOfIntegers_equiv_of_embedding`: General criterion identifying `𝓞 K` with any
  ring that embeds injectively into `K` and has the correct integral image.
  **mathlib target: `Mathlib.NumberTheory.NumberField.RingOfIntegers`**

* `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`.
  **mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`**

* `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.
  **mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`**

* `isDedekindDomain_zsqrtd_iff_mod_four_ne_one`:
  `ℤ[√d]` is Dedekind iff `d % 4 ≠ 1`.
  **mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`**

* `ringOfIntegers_classification`: The combined classification disjunction.
  **mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`**

## Design

Integrality ingredients (`IsIntegralClosure` constructions, half-integer normal form,
etc.) live in `Integrality.lean`. This file assembles the final `𝓞 ≃+* R`
isomorphisms and the top-level classification.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

section FieldLevel

/-! ## General Criterion for Ring of Integers Identification -/

/-- **Generic fact**: the ring of integers `𝓞 K` is ring-isomorphic to any
commutative ring `R` equipped with an `IsIntegralClosure R ℤ K` instance. -/
theorem ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    Nonempty (𝓞 K ≃+* R) :=
  ⟨NumberField.RingOfIntegers.equiv (K := K) (R := R)⟩

/-- **General criterion for identifying the ring of integers.** -/
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

end FieldLevel

section ParamLevel

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-! ## The `d % 4 ≠ 1` Branch: `𝓞(ℚ(√d)) = ℤ[√d]`

When `d` is squarefree and `d ≢ 1 (mod 4)`, every integral element of `ℚ(√d)` has
integer coordinates in the `{1, √d}` basis. In the half-integer normal form
`(a' + b'√d)/2`, the condition `4 ∣ (a'² − d·b'²)` forces both `a'` and `b'` to be
even (see `dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four`), so the element already
lies in `ℤ[√d]`. -/

/-- If `d % 4 ≠ 1`, then `𝓞(ℚ(√d)) ≃+* ℤ[√d]`.

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
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

/-! ## Dedekind Domain Properties of `ℤ[√d]`

A key application of the classification is determining when `ℤ[√d]` is a Dedekind
domain. Since `𝓞 K` is always Dedekind for a number field `K`, and Dedekind-ness
transfers across ring isomorphisms, `ℤ[√d]` is Dedekind precisely when it equals
the full ring of integers — i.e., when `d ≢ 1 (mod 4)`.

Conversely, when `d ≡ 1 (mod 4)`, `ℤ[√d]` is a *proper* suborder of `𝓞(ℚ(√d))`:
the element `(1 + √d)/2` is integral but does not belong to `ℤ[√d]`. Since a
Dedekind domain is integrally closed in its fraction field, this gives a
contradiction. -/

/-- If `d % 4 ≠ 1`, then `ℤ[√d]` is a Dedekind domain — it is the full ring of
integers of `ℚ(√d)`, and Dedekind-ness transfers from `𝓞(ℚ(√d))` via the ring
isomorphism.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`** -/
theorem isDedekindDomain_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    IsDedekindDomain (Zsqrtd d) := by
  rcases ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4 with ⟨e⟩
  letI : IsDedekindDomain (𝓞 (Qsqrtd (d : ℚ))) := inferInstance
  exact RingEquiv.isDedekindDomain e

/-- If `d % 4 = 1`, then `ℤ[√d]` is **not** a Dedekind domain.

The obstruction is that `ℤ[√d]` is not integrally closed in its fraction field
`ℚ(√d)`: the element `ω = (1 + √d)/2` satisfies `ω² − ω − k = 0` (where
`d = 1 + 4k`), so it is integral over `ℤ`, but its half-integer coordinates
`(1, 1)` are both odd, hence `ω ∉ ℤ[√d]`. Since every Dedekind domain is
integrally closed, `ℤ[√d]` cannot be Dedekind.

The proof requires `ℚ(√d)` to be the fraction field of `ℤ[√d]`, which is
established by a clearing-denominators argument: for `z = r + s√d` with
`r = p/q, s = u/v`, the product `qv · z` lies in `ℤ[√d]`.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`** — the fraction
field construction `IsFractionRing (ℤ√d) (ℚ√d)` would also be useful as a
standalone result in `Mathlib.NumberTheory.Zsqrtd.Basic`. -/
theorem not_isDedekindDomain_zsqrtd_of_mod_four_eq_one
    (hd4 : d % 4 = 1) :
    ¬ IsDedekindDomain (Zsqrtd d) := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  -- Set up `ℚ(√d)` as an algebra over `ℤ[√d]` via the canonical embedding.
  letI : Algebra (Zsqrtd d) (Qsqrtd (d : ℚ)) := (Zsqrtd.toQsqrtdHom d).toAlgebra
  letI : FaithfulSMul (Zsqrtd d) (Qsqrtd (d : ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective (Zsqrtd d) (Qsqrtd (d : ℚ))).mpr
      (Zsqrtd.toQsqrtdHom_injective d)
  -- Establish `ℚ(√d) = Frac(ℤ[√d])` by clearing denominators coordinate-wise.
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
  -- A Dedekind domain is integrally closed in its fraction field.
  have hIC : IsIntegrallyClosed (Zsqrtd d) := IsDedekindRing.toIsIntegralClosure
  letI : IsIntegrallyClosed (Zsqrtd d) := hIC
  -- Write `d = 1 + 4k` and consider `ω = (1 + √d)/2`.
  rcases exists_k_of_mod_four_eq_one (d := d) hd4 with ⟨k, hk⟩
  subst hk
  let x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ)) := halfInt (1 + 4 * k) 1 1
  -- Show `ω` is integral: it lies in `ℤ[(1+√d)/2]`, which is an integral extension.
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
  -- If `ω ∈ ℤ[√d]`, the half-integer criterion would force the numerators
  -- `(1, 1)` to both be even — a contradiction.
  have h_even : 2 ∣ (1 : ℤ) ∧ 2 ∣ (1 : ℤ) :=
    (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even (1 + 4 * k) 1 1).mp
      ⟨z, by
        simpa [x, halfInt, RingHom.toAlgebra] using hz⟩
  omega

/-- For a squarefree `d ≠ 1`, `ℤ[√d]` is a Dedekind domain if and only if
`d ≢ 1 (mod 4)` — equivalently, if and only if `ℤ[√d]` is the full ring of
integers of `ℚ(√d)`.

This characterizes exactly when the order `ℤ[√d]` coincides with the maximal
order `𝓞(ℚ(√d))`.

**mathlib target: `Mathlib.NumberTheory.Zsqrtd.DedekindDomain`** -/
theorem isDedekindDomain_zsqrtd_iff_mod_four_ne_one :
    IsDedekindDomain (Zsqrtd d) ↔ d % 4 ≠ 1 := by
  constructor
  · intro hDed hd4
    exact not_isDedekindDomain_zsqrtd_of_mod_four_eq_one d hd4 hDed
  · exact isDedekindDomain_zsqrtd_of_mod_four_ne_one d

/-! ## The `d % 4 = 1` Branch: `𝓞(ℚ(√d)) = ℤ[(1+√d)/2]`

When `d ≡ 1 (mod 4)`, the half-integer `ω = (1 + √d)/2` satisfies
`ω² = ω + k` (where `d = 1 + 4k`), so it is integral. The condition
`4 ∣ (a'² − d·b'²)` now allows `a', b'` to be both odd (same parity),
enlarging the integral closure from `ℤ[√d]` to `ℤ[ω]`.

The ring `ℤ[ω]` is modeled as `QuadraticAlgebra ℤ k 1` (the relation `ω² = ω + k`),
which we call `ZOnePlusSqrtOverTwo k`. -/

/-- If `d % 4 = 1`, writing `d = 1 + 4k`, then `𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

The existential `∃ k` witnesses the parametrization; the caller typically already
knows `k` from `exists_k_of_mod_four_eq_one`.

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
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

/-! ## Combined Classification -/

/-- **Classification of the ring of integers of `ℚ(√d)`.**

For squarefree `d ≠ 1`, exactly one of the following holds:
* If `d ≢ 1 (mod 4)`, then `𝓞(ℚ(√d)) ≃+* ℤ[√d]`.
* If `d ≡ 1 (mod 4)`, then writing `d = 1 + 4k`, `𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

This is the classical result found in [Marcus, Theorem 2.16],
[Neukirch, I.2], [Stewart–Tall, Theorem 4.6].

**mathlib target: `Mathlib.NumberTheory.QuadraticField.RingOfIntegers`** -/
theorem ringOfIntegers_classification
    :
    (d % 4 ≠ 1 ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (Qsqrtd (d : ℚ)) ≃+* ZOnePlusSqrtOverTwo k)) := by
  by_cases hd4 : d % 4 = 1
  · exact Or.inr <| ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  · exact Or.inl ⟨hd4, ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4⟩

/-! ## Concrete Examples

### Example 2.8 (Boxer Notes): Gaussian and Eisenstein Integers

The Gaussian integers `ℤ[i]` and Eisenstein integers `ℤ[ω₃]` are the two
most classical examples. Since `-1 % 4 = 3 ≠ 1` the Gaussian integers fall
in the first branch, while `-3 % 4 = 1` places the Eisenstein integers in
the second. -/

/-- **Gaussian integers**: `𝓞(ℚ(√(-1))) ≃+* ℤ[i]`.

Since `-1 ≡ 3 (mod 4)`, the ring of integers is `ℤ[√(-1)] = ℤ[i]`. -/
example : Nonempty (𝓞 (Qsqrtd ((-1 : ℤ) : ℚ)) ≃+* Zsqrtd (-1)) :=
  ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (-1) (by decide)

/-- **Eisenstein integers**: `𝓞(ℚ(√(-3))) ≃+* ℤ[(1+√(-3))/2]`.

Since `-3 ≡ 1 (mod 4)`, the ring of integers is `ℤ[ω]` where `ω = (1+√(-3))/2`
is a primitive cube root of unity. -/
example : ∃ k : ℤ, (-3 : ℤ) = 1 + 4 * k ∧
    Nonempty (𝓞 (Qsqrtd ((-3 : ℤ) : ℚ)) ≃+* ZOnePlusSqrtOverTwo k) :=
  ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one (-3) (by decide)

end ParamLevel

end RingOfIntegers
end QuadraticNumberFields
