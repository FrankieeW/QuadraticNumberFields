/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.HalfInt
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.RingOfIntegers.ZOnePlusSqrtOverTwo
import QuadraticNumberFields.Parameters

/-!
# Integrality Criteria for Quadratic Fields

This file develops integrality criteria for elements of quadratic number fields
and proves that integral elements have specific normal forms.

## Main Results

### Half-Integer Normal Form
* `exists_halfInt_with_div_four_of_isIntegral`: Any integral element of `Q(√d)`
  can be written as `halfInt d a' b'` with `4 ∣ (a'² - d·b'²)`.

### Non-`1 mod 4` Branch
* `exists_zsqrtd_of_isIntegral_of_ne_one_mod_four`: If `d % 4 ≠ 1`, integral
  elements lie in the image of `Zsqrtd d`.

### `1 mod 4` Branch
* `exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four`: If `d = 1 + 4k`,
  integral elements lie in the image of `ZOnePlusSqrtOverTwo k`.

## Supporting Lemmas

The file provides equivalence theorems connecting divisibility by 4 with
membership in various carrier sets, used by `Classification.lean`.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

open scoped NumberField

/-! ## Divisibility-Carrier Equivalences -/

/-- In the non-`1 mod 4` branch, divisibility by `4` is equivalent to representability
in the image of `Zsqrtd d` under the canonical embedding into `Q(√d)`. -/
theorem dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' := by
  -- Away from the `d ≡ 1 (mod 4)` case, divisibility by `4` forces both
  -- half-integer coordinates to be even, so the element already comes from `ℤ[√d]`.
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4]
  simpa using (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even d a' b').symm

/-- Forward direction in the non-`1 mod 4` branch. -/
theorem exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv

/-- Reverse direction in the non-`1 mod 4` branch. -/
theorem dvd_four_sub_sq_of_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hz : ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b') :
    4 ∣ (a' ^ 2 - d * b' ^ 2) :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).2 hz

/-- In the `1 mod 4` branch (`d = 1 + 4k`), divisibility by `4` is equivalent to
representability in the image of `ZOnePlusSqrtOverTwo k`. -/
theorem dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four
    (k a' b' : ℤ) (hd : Squarefree (1 + 4 * k)) :
    4 ∣ (a' ^ 2 - (1 + 4 * k) * b' ^ 2) ↔
      ∃ z : ZOnePlusSqrtOverTwo k,
        ZOnePlusSqrtOverTwo.toQsqrtdFun k z =
          QuadraticNumberFields.RingOfIntegers.halfInt (1 + 4 * k) a' b' := by
  -- In the `1 mod 4` case, integrality is controlled by parity agreement
  -- of the two numerator coordinates, matching the carrier of `ℤ[(1 + √d)/2]`.
  have hd4 : (1 + 4 * k) % 4 = 1 :=
    mod_four_eq_one_of_exists_k (d := 1 + 4 * k) ⟨k, by ring⟩
  rw [dvd_four_sub_sq_iff_same_parity_of_one_mod_four (d := 1 + 4 * k) a' b' hd hd4]
  simpa using (ZOnePlusSqrtOverTwo.halfInt_mem_carrierSet_iff_same_parity k a' b').symm

/-- Forward direction in the `1 mod 4` branch. -/
theorem exists_zOnePlusSqrtOverTwo_image_of_dvd_four_sub_sq_of_one_mod_four
    (k a' b' : ℤ) (hd : Squarefree (1 + 4 * k))
    (hdiv : 4 ∣ (a' ^ 2 - (1 + 4 * k) * b' ^ 2)) :
    ∃ z : ZOnePlusSqrtOverTwo k,
      ZOnePlusSqrtOverTwo.toQsqrtdFun k z =
        QuadraticNumberFields.RingOfIntegers.halfInt (1 + 4 * k) a' b' :=
  (dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four k a' b' hd).1 hdiv

/-- Reverse direction in the `1 mod 4` branch. -/
theorem dvd_four_sub_sq_of_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four
    (k a' b' : ℤ) (hd : Squarefree (1 + 4 * k))
    (hz : ∃ z : ZOnePlusSqrtOverTwo k,
      ZOnePlusSqrtOverTwo.toQsqrtdFun k z =
        QuadraticNumberFields.RingOfIntegers.halfInt (1 + 4 * k) a' b') :
    4 ∣ (a' ^ 2 - (1 + 4 * k) * b' ^ 2) :=
  (dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four k a' b' hd).2 hz

/-- **Generic fact**: the ring of integers `𝓞 K` is ring-isomorphic to any
commutative ring `R` equipped with an `IsIntegralClosure R ℤ K` instance.

This is the universal property of the integral closure, packaged as a `RingEquiv`.
It is **not specific to quadratic fields**.

**mathlib target: already in mathlib as `NumberField.RingOfIntegers.equiv`,
but this wrapper with explicit algebra argument is more ergonomic.** -/
theorem ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    Nonempty (𝓞 K ≃+* R) :=
  -- The ring of integers is characterized by the integral-closure universal property.
  ⟨NumberField.RingOfIntegers.equiv (K := K) (R := R)⟩

/-- Any image of an integral element under a ring hom remains integral over `ℤ`.

This is a **general integrality-transport lemma**: if `R` is an integral `ℤ`-algebra
(i.e., every element of `R` is integral over `ℤ`), then ring homomorphisms preserve
integrality. The proof uses `map_isIntegral_int`.

**mathlib target: `Mathlib.RingTheory.IntegralClosure.IsIntegral`** -/
private lemma isIntegral_of_intModel_image
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra.IsIntegral ℤ R] (φ : R →+* S) (z : R) :
    IsIntegral ℤ (φ z) :=
  -- Integrality is preserved by ring homomorphisms.
  map_isIntegral_int φ (Algebra.IsIntegral.isIntegral (R := ℤ) z)

/-- Every element in the image of `Zsqrtd d → Q(√d)` is integral over `ℤ`. -/
lemma isIntegral_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    IsIntegral ℤ (Zsqrtd.toQsqrtdHom d z) :=
  isIntegral_of_intModel_image (Zsqrtd d) (Qsqrtd (d : ℚ)) (Zsqrtd.toQsqrtdHom d) z

/-! ## Half-Integer Normal Form -/

/-- Trace in `Q(√d)` is `2 * re`. -/
private theorem trace_eq_two_re {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    Algebra.trace ℚ (Qsqrtd d) x = 2 * x.re :=
  Qsqrtd.trace_eq_two_re x

/-- Norm in `Q(√d)` is `re² - d * im²`. -/
private theorem norm_eq_sqr_minus_d_sqr {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    Qsqrtd.norm x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

/-- Any element of `Q(√d)` integral over `ℤ` has half-integer coordinates with
`4 ∣ (a'^2 - d * b'^2)`. -/
lemma exists_halfInt_with_div_four_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (_hd_ne : d ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' b' : ℤ,
      x = Zsqrtd.halfInt (d := d) a' b' ∧
      (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  have hd0 : d ≠ 0 := hd_sf.ne_zero
  have hd0Q : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  -- We first show that both trace and norm of `x` are integers.
  -- These will recover the numerators `a'` and `b'` of the half-integer form.
  let cHom : ℚ →+* Qsqrtd (d : ℚ) :=
    { toFun := QuadraticAlgebra.C (a := (d : ℚ)) (b := (0 : ℚ))
      map_one' := by
        simp [QuadraticAlgebra.C_one]
      map_mul' := by
        intro r s
        simp [QuadraticAlgebra.C_mul]
      map_zero' := by
        simp [QuadraticAlgebra.C_zero]
      map_add' := by
        intro r s
        simp [QuadraticAlgebra.C_add] }
  have hc_inj : Function.Injective cHom := by
    intro r s hrs
    exact (QuadraticAlgebra.C_inj (R := ℚ) (a := (d : ℚ)) (b := (0 : ℚ))).1 hrs
  have hstar : IsIntegral ℤ (star x) := map_isIntegral_int (starRingEnd (Qsqrtd (d : ℚ))) hx
  have htraceAlg :
      IsIntegral ℤ
        (QuadraticAlgebra.C (a := (d : ℚ)) (b := (0 : ℚ))
          (Algebra.trace ℚ (Qsqrtd d) x)) := by
    have hsum : IsIntegral ℤ (x + star x) := hx.add hstar
    have hsum_eq :
        x + star x =
          QuadraticAlgebra.C (a := (d : ℚ)) (b := (0 : ℚ))
            (Algebra.trace ℚ (Qsqrtd d) x) := by
      ext
      · simp [Qsqrtd.trace_eq_re_add_re_star, star, QuadraticAlgebra.C]
      · simp [star, QuadraticAlgebra.C]
    simpa [hsum_eq] using hsum
  have htraceRat : IsIntegral ℤ (Algebra.trace ℚ (Qsqrtd d) x) :=
    (isIntegral_algHom_iff cHom.toIntAlgHom hc_inj).1 htraceAlg
  obtain ⟨a', ha'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 htraceRat
  have ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x := by simpa using ha'
  -- So `a'` is the integral trace, and therefore `x.re = a'/2`.
  have hnormAlg : IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x)) := by
    have hmul : algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x) = x * star x := by
      simpa [Qsqrtd.norm, mul_comm] using
        (QuadraticAlgebra.algebraMap_norm_eq_mul_star (a := (d : ℚ)) (b := (0 : ℚ)) x)
    have hprod : IsIntegral ℤ (x * star x) := hx.mul hstar
    simpa [hmul] using hprod
  have hnormRat : IsIntegral ℤ (Qsqrtd.norm x) :=
    (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
      (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 hnormAlg
  obtain ⟨n', hn'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hnormRat
  have hn'norm : (n' : ℚ) = Qsqrtd.norm x := by simpa using hn'
  let q : ℚ := 2 * x.im
  let m : ℤ := a' ^ 2 - 4 * n'
  have hre : x.re = (a' : ℚ) / 2 := by
    have htr : 2 * x.re = (a' : ℚ) := by
      calc
        2 * x.re = Algebra.trace ℚ (Qsqrtd d) x := (trace_eq_two_re x).symm
        _ = (a' : ℚ) := ha'trace.symm
    nlinarith
  -- Rearranging the norm identity shows that `q = 2 * x.im` satisfies
  -- `d * q² = a'² - 4 n'`, hence `q² = m / d` for an integer `m`.
  have hqmul : (d : ℚ) * q ^ 2 = (m : ℚ) := by
    have hnorm' :
        (n' : ℚ) = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by
      calc
        (n' : ℚ) = Qsqrtd.norm x := hn'norm
        _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := norm_eq_sqr_minus_d_sqr x
        _ = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by simp [hre]
    have haux : (a' : ℚ) ^ 2 - 4 * (n' : ℚ) = 4 * (d : ℚ) * x.im ^ 2 := by
      nlinarith [hnorm']
    have hmcast : (m : ℚ) = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
      dsimp [m]
      norm_cast
    dsimp [q]
    calc
      (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
      _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
      _ = (m : ℚ) := hmcast.symm
  have hqratio : q ^ 2 = (m : ℚ) / (d : ℚ) := by
    calc
      q ^ 2 = ((d : ℚ) * q ^ 2) / (d : ℚ) := by field_simp [hd0Q]
      _ = (m : ℚ) / (d : ℚ) := by simp [hqmul]
  have hsqratio : IsSquare ((m : ℚ) / (d : ℚ)) := ⟨q, by simpa [pow_two] using hqratio.symm⟩
  -- Since `d` is squarefree and `(m : ℚ) / d` is a square, the denominator obstruction
  -- disappears: `d` must divide `m`.
  have hdm : d ∣ m := int_dvd_of_ratio_square m d hd0 hd_sf hsqratio
  rcases hdm with ⟨k, hk⟩
  have hq2 : q ^ 2 = (k : ℚ) := by
    have hmk : (m : ℚ) = (d : ℚ) * k := by
      exact_mod_cast hk
    calc
      q ^ 2 = (m : ℚ) / (d : ℚ) := hqratio
      _ = (((d : ℚ) * k) / (d : ℚ)) := by simp [hmk]
      _ = (k : ℚ) := by field_simp [hd0Q]
  -- Therefore `q` is itself integral over `ℤ`; as `ℤ` is integrally closed in `ℚ`,
  -- `q` must actually be an integer `b'`.
  have hqInt : IsIntegral ℤ q := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C k,
      Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) k (show (2 : ℕ) ≠ 0 by decide), ?_⟩
    have hC : Polynomial.eval₂ (Int.castRingHom ℚ) q (Polynomial.C k) = (k : ℚ) := by
      simpa using (Polynomial.eval₂_C (f := Int.castRingHom ℚ) (x := q) (a := k))
    calc
      Polynomial.eval₂ (Int.castRingHom ℚ) q (Polynomial.X ^ 2 - Polynomial.C k)
          = q ^ 2 - Polynomial.eval₂ (Int.castRingHom ℚ) q (Polynomial.C k) := by
            simp [Polynomial.eval₂_sub]
      _ = q ^ 2 - (k : ℚ) := by simpa [hC]
      _ = 0 := by simp [hq2]
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hqInt
  have hb'q : (b' : ℚ) = q := by simpa using hb'
  have him : x.im = (b' : ℚ) / 2 := by
    have : (b' : ℚ) = 2 * x.im := by simpa [q] using hb'q
    nlinarith [this]
  -- Now both coordinates match the half-integer representative `(a' + b'√d)/2`.
  have hxHalf : x = Zsqrtd.halfInt (d := d) a' b' := by
    ext <;> simp [Zsqrtd.halfInt, hre, him]
  have hnormHalf : (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by
    calc
      (n' : ℚ) = Qsqrtd.norm x := hn'norm
      _ = Qsqrtd.norm (Zsqrtd.halfInt (d := d) a' b') := by simp [hxHalf]
      _ = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := norm_halfInt d a' b'
      _ = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by norm_num
  have hhalf : ((((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) = (n' : ℚ)) := by
    simpa using hnormHalf.symm
  have hden : ((((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)).den = 1) := by
    rw [hhalf]
    simp
  -- The norm is an integer, so the denominator of `(a'² - d b'²) / 4` is `1`,
  -- which is exactly the desired divisibility by `4`.
  have hdiv : (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
    (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 hden
  exact ⟨a', b', hxHalf, hdiv⟩

/-! ## Classification Lemmas -/

private lemma exists_intModel_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1)
    (R : Type*) [CommRing R]
    (φ : R →+* Qsqrtd (d : ℚ))
    (h_lift :
      ∀ a' b' : ℤ, 4 ∣ (a' ^ 2 - d * b' ^ 2) →
        ∃ z : R, φ z = Zsqrtd.halfInt (d := d) a' b')
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : R, φ z = x := by
  -- First put `x` into half-integer normal form, then use the branch-specific
  -- lifting criterion supplied by `h_lift`.
  rcases exists_halfInt_with_div_four_of_isIntegral d hd_sf hd_ne (x := x) hx with
    ⟨a', b', hxHalf, hdiv⟩
  rcases h_lift a' b' hdiv with ⟨z, hz⟩
  exact ⟨z, by simpa [hxHalf] using hz⟩

/-- Integrality classification in the `d % 4 ≠ 1` branch: integral elements of `Q(√d)`
lie in the image of `Zsqrtd d`. -/
lemma exists_zsqrtd_of_isIntegral_of_ne_one_mod_four
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1) (hd4 : d % 4 ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = x :=
  exists_intModel_of_isIntegral d hd_sf hd_ne (Zsqrtd d) (Zsqrtd.toQsqrtdHom d)
    (fun a' b' hdiv =>
      exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd_sf hd4 hdiv)
    hx

/-- Every element in the image of `ZOnePlusSqrtOverTwo k → Q(√(1 + 4k))` is integral over `ℤ`. -/
lemma isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    IsIntegral ℤ (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k z) :=
  isIntegral_of_intModel_image (ZOnePlusSqrtOverTwo k) (Qsqrtd ((1 + 4 * k : ℤ) : ℚ))
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k) z

/-- Integrality classification in the `1 mod 4` branch model (`d = 1 + 4k`):
integral elements of `Q(√(1 + 4k))` lie in the image of `ZOnePlusSqrtOverTwo k`. -/
lemma exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four
    (k : ℤ) (hd_sf : Squarefree (1 + 4 * k)) (hd_ne : (1 + 4 * k) ≠ 1)
    {x : Qsqrtd (((1 + 4 * k : ℤ) : ℚ))} (hx : IsIntegral ℤ x) :
    ∃ z : ZOnePlusSqrtOverTwo k, _root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k z = x :=
  exists_intModel_of_isIntegral (1 + 4 * k) hd_sf hd_ne (ZOnePlusSqrtOverTwo k)
    (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k)
    (fun a' b' hdiv =>
      exists_zOnePlusSqrtOverTwo_image_of_dvd_four_sub_sq_of_one_mod_four k a' b' hd_sf hdiv)
    hx

end RingOfIntegers
end QuadraticNumberFields
