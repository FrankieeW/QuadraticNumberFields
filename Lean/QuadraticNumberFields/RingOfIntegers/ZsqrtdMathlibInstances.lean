/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Zsqrtd
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Additional Instances for mathlib `Zsqrtd`

This module adds generic algebraic instances for mathlib's `_root_.Zsqrtd d`
under useful arithmetic hypotheses.

## Main Definitions

* `Zsqrtd.instNoZeroDivisors`: `NoZeroDivisors (Zsqrtd d)` for `d < 0`.
* `Zsqrtd.instIsDomain`: `IsDomain (Zsqrtd d)` for `d < 0`.
* `Zsqrtd.instIsDedekindDomainOfModFourNeOne`: `IsDedekindDomain (Zsqrtd d)`
  for valid quadratic parameters with `d % 4 ≠ 1`.

## Main Theorems

* No new named theorems are introduced in this file.
-/

namespace Zsqrtd

instance instNoZeroDivisors {d : ℤ} [Fact (d < 0)] : NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : Zsqrtd.norm (a * b) = 0 := by
      simp [hab, Zsqrtd.norm_zero (d := d)]
    have hmulnorm : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      simpa [Zsqrtd.norm_mul] using hnorm
    rcases mul_eq_zero.mp hmulnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (d := d) Fact.out a).1 ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (d := d) Fact.out b).1 hb)

instance instIsDomain {d : ℤ} [Fact (d < 0)] : IsDomain (Zsqrtd d) :=
  NoZeroDivisors.to_isDomain (Zsqrtd d)

theorem isDedekindDomain_of_mod_four_ne_one
    (d : ℤ) [QuadFieldParam d]
    (hd4 : d % 4 ≠ 1) :
    IsDedekindDomain (Zsqrtd d) := by
  let e := QuadraticNumberFields.RingOfIntegers.Zsqrtd.equivMathlib d
  letI : IsDedekindDomain (QuadraticNumberFields.RingOfIntegers.Zsqrtd d) :=
    QuadraticNumberFields.RingOfIntegers.isDedekindDomain_zsqrtd_of_mod_four_ne_one d hd4
  letI : Module
      (QuadraticNumberFields.RingOfIntegers.Zsqrtd d)
      (QuadraticNumberFields.RingOfIntegers.Zsqrtd d) := Semiring.toModule
  letI : IsNoetherianRing (QuadraticNumberFields.RingOfIntegers.Zsqrtd d) :=
    show
      IsNoetherian
        (QuadraticNumberFields.RingOfIntegers.Zsqrtd d)
        (QuadraticNumberFields.RingOfIntegers.Zsqrtd d) from
      IsDedekindRing.toIsNoetherian
  letI : IsDomain (Zsqrtd d) := e.toMulEquiv.isDomain_iff.mp inferInstance
  letI : IsNoetherianRing (Zsqrtd d) :=
    isNoetherianRing_of_ringEquiv (QuadraticNumberFields.RingOfIntegers.Zsqrtd d) e
  letI : IsIntegrallyClosed (Zsqrtd d) := IsIntegrallyClosed.of_equiv e
  letI : Ring.DimensionLEOne (Zsqrtd d) :=
    { maximalOfPrime := by
        intro p hp0 hp
        have hcomapPrime : (Ideal.comap e p).IsPrime := Ideal.comap_isPrime e p
        have hcomapNeBot : Ideal.comap e p ≠ ⊥ := by
          intro hbot
          have hmap := Ideal.map_comap_eq_self_of_equiv e p
          rw [hbot, Ideal.map_bot] at hmap
          exact hp0 hmap.symm
        have hcomapMax : (Ideal.comap e p).IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime hcomapNeBot hcomapPrime
        letI : (Ideal.comap e p).IsMaximal := hcomapMax
        have hmapMax : (Ideal.map e (Ideal.comap e p)).IsMaximal :=
          Ideal.map_isMaximal_of_equiv e
        simpa [Ideal.map_comap_eq_self_of_equiv] using hmapMax }
  letI : Module (Zsqrtd d) (Zsqrtd d) := Semiring.toModule
  letI : IsDedekindRing (Zsqrtd d) :=
    { toIsNoetherian := show IsNoetherian (Zsqrtd d) (Zsqrtd d) from inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure :=
        show IsIntegralClosure (Zsqrtd d) (Zsqrtd d) (FractionRing (Zsqrtd d)) from
          inferInstance }
  infer_instance

instance instIsDedekindDomainOfModFourNeOne
    (d : ℤ) [QuadFieldParam d] [Fact (d % 4 ≠ 1)] :
    IsDedekindDomain (Zsqrtd d) :=
  isDedekindDomain_of_mod_four_ne_one d Fact.out

end Zsqrtd
