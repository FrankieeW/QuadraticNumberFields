/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.HalfInt
import QuadraticNumberFields.RingOfIntegers.ModFour
import QuadraticNumberFields.RingOfIntegers.TraceNorm
import QuadraticNumberFields.RingOfIntegers.ZOnePlusSqrtOverTwo

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
          halfInt (1 + 4 * k) a' b' := by
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

/-! ## Half-Integer Normal Form -/

/-- Coordinates determine the corresponding half-integer element. -/
private lemma eq_halfInt_of_re_im
    (d a' b' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hre : x.re = (a' : ℚ) / 2) (him : x.im = (b' : ℚ) / 2) :
    x = Zsqrtd.halfInt (d := d) a' b' := by
  ext <;> simp [Zsqrtd.halfInt, hre, him]

/-- The chosen integral norm matches the half-integer norm formula. -/
private lemma int_norm_eq_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by
  calc
    (n' : ℚ) = Qsqrtd.norm x := hn'norm
    _ = Qsqrtd.norm (Zsqrtd.halfInt (d := d) a' b') := by simp [hxHalf]
    _ = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := norm_halfInt d a' b'
    _ = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by norm_num

/-- The chosen integral norm yields the required divisibility for the half-integer coordinates. -/
private lemma dvd_four_sub_sq_of_int_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  exact (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 <| by
    rw [← int_norm_eq_norm_halfInt d a' b' n' hxHalf hn'norm]
    simp

/-- Any element of `Q(√d)` integral over `ℤ` has half-integer coordinates with
`4 ∣ (a'^2 - d * b'^2)`. -/
lemma exists_halfInt_with_div_four_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (_hd_ne : d ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' b' : ℤ,
      x = Zsqrtd.halfInt (d := d) a' b' ∧
      (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  obtain ⟨a', ha'trace⟩ := TraceNorm.exists_int_trace hx
  obtain ⟨n', hn'norm⟩ := TraceNorm.exists_int_norm hx
  obtain ⟨b', him⟩ := TraceNorm.exists_int_double_im d hd_sf ha'trace hn'norm
  have hxHalf : x = Zsqrtd.halfInt (d := d) a' b' :=
    eq_halfInt_of_re_im d a' b'
      (TraceNorm.re_eq_half_trace_int ha'trace) him
  exact ⟨a', b', hxHalf, dvd_four_sub_sq_of_int_norm_halfInt d a' b' n' hxHalf hn'norm⟩

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
