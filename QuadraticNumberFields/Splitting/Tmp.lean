/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.NormalClosure

open Ideal

variable {R : Type*} [CommRing R]
variable (p : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

local notation3 "g(" p ")" => (primesOver p S).ncard



/-- If `S` is a quadratic extension of `R`, then the fraction field of `S` is a quadratic
extension of the fraction field of `R`. -/
theorem _root_.Algebra.IsQuadraticExtension.fractionRing
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
    [IsDomain R] [IsDomain S] [IsFractionRing R K] [IsFractionRing S L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsQuadraticExtension R S] :
    Algebra.IsQuadraticExtension K L := by
  letI : Algebra.IsAlgebraic R S := Algebra.IsAlgebraic.of_finite R S
  refine ⟨?_⟩
  calc
    Module.finrank K L = Module.finrank R S := by
      simpa using
        (Algebra.IsAlgebraic.finrank_of_isFractionRing (R := R) (R' := K) (S := S) (S' := L))
    _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two R S

/-- If `K` is a quadratic extension of a field `F` of characteristic not equal to `2`,
then `K/F` is separable. -/
theorem _root_.Algebra.IsQuadraticExtension.isSeparable_of_field_of_char_ne_two
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra.IsQuadraticExtension F K]
    (hchar : ringChar F ≠ 2) : Algebra.IsSeparable F K := by
  rw [isSeparable_iff_finInsepDegree_eq_one] -- [Field F, Field K, Algebra F K]
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (F := F) (E := K) (q := ringExpChar F)
  have hdiv : Field.finInsepDegree F K ∣ 2 := by
    refine ⟨Field.finSepDegree F K, ?_⟩
    rw [Nat.mul_comm, Field.finSepDegree_mul_finInsepDegree,
      Algebra.IsQuadraticExtension.finrank_eq_two F K]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
  · exact h1
  · have hexp : ringExpChar F ≠ 2 := by
      rw [ringExpChar]
      intro h
      omega
    rw [hn] at h2
    cases n with
    | zero => simp at h2
    | succ n =>
        have hq_dvd : ringExpChar F ∣ 2 := by
          rw [pow_succ] at h2
          exact ⟨(ringExpChar F) ^ n, by simpa [Nat.mul_comm] using h2.symm⟩
        rcases (Nat.dvd_prime Nat.prime_two).1 hq_dvd with hq1 | hq2
        · simp [hq1] at h2
        · exact (hexp hq2).elim




section Trichotomy

variable [IsDedekindDomain S]

local notation3 "e(" p ")" => ramificationIdxIn p S
local notation3 "f(" p ")" => Ideal.inertiaDegIn p S
local notation3 "τ(" p ")" => (e(p), f(p), g(p))

/-! ## Trichotomy for degree-2 extensions

For `[L : K] = 2`, `∑ eᵢfᵢ = 2` forces exactly three possibilities:
* `(e, f, g) = (1, 1, 2)` — split
* `(e, f, g) = (1, 2, 1)` — inert
* `(e, f, g) = (2, 1, 1)` — ramified
-/
-- Set L is List of ℕ , Σ A = p → ∀ a ∈ A, a = 1 or a = p
lemma eq_one_or_p_if_list_prod_eq_p {p : ℕ} (hp : Nat.Prime p) {L : List ℕ}
      (h : L.prod = p) : ∀ a ∈ L, a = 1 ∨ a = p := by
    intro a ha
    have hdiv : a ∣ p := by
      rw [← h]
      exact List.dvd_prod ha
    exact (Nat.dvd_prime hp).1 hdiv

theorem foo (a b c : ℕ) (h : a * b * c = 2) :
      (a = 2 ∧ b = 1 ∧ c = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 1) := by
    have hL : [a, b, c].prod = 2 := by
      simpa [Nat.mul_assoc] using h
    have H := eq_one_or_p_if_list_prod_eq_p Nat.prime_two hL
    rcases H a (by simp) with (rfl | rfl)
    <;> rcases H b (by simp) with (rfl | rfl)
    <;> rcases H c (by simp) with (rfl | rfl)
    <;> simp_all

theorem efg_trichotomy [Nontrivial R] [IsDedekindDomain R] [Algebra.IsQuadraticExtension R S]
    -- [CharZero R] -- char≠ 2 is enough
    (hchar : ringChar R ≠ 2) (hp : p ≠ ⊥) [p.IsMaximal] :
    (g(p) = 2 ∧ e(p) = 1 ∧ f(p) = 1) ∨
    (g(p) = 1 ∧ e(p) = 1 ∧ f(p) = 2) ∨
    (g(p) = 1 ∧ e(p) = 2 ∧ f(p) = 1) := by
  let K:=FractionRing R
  let L:=FractionRing S
  let := Ring.instAlgebraFractionRing
  let := IsIntegralClosure.MulSemiringAction R K L S
  have : Algebra.IsQuadraticExtension K L :=
    Algebra.IsQuadraticExtension.fractionRing (R := R) (S := S)
  -- have : Algebra.IsSeparable K L := sorry  add char≠2 to assumptions or [CharZero R]
  have : ringChar K ≠ 2 := by
    have : CharP K (ringChar R) :=
      IsFractionRing.charP_of_isFractionRing (R := R) (K := K) (ringChar R)
    simpa [ringChar.eq K (ringChar R)] using hchar
  have : Algebra.IsSeparable K L :=
    Algebra.IsQuadraticExtension.isSeparable_of_field_of_char_ne_two this
  have := IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
  have h_mul:= Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S Gal(L/K)
  have : Nat.card Gal(L/K) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two K L]
    exact IsGaloisGroup.card_eq_finrank Gal(L/K) K L
  rw [this] at h_mul
  apply foo
  rw [mul_assoc]
  assumption

end Trichotomy
