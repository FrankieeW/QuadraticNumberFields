/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Ring Equivalence Transport Lemmas

This file contains generic lemmas for transporting algebraic properties across
ring equivalences.

## Main Definitions

* `RingEquiv.dimensionLEOne`: transport `Ring.DimensionLEOne` across a ring
  equivalence.
* `RingEquiv.isDedekindDomain`: transport `IsDedekindDomain` across a ring
  equivalence.

## Main Theorems

* `RingEquiv.isDedekindDomain_iff`: `IsDedekindDomain` is invariant under ring
  equivalence.
-/

namespace RingEquiv

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Transport `Ring.DimensionLEOne` across a ring equivalence. -/
theorem dimensionLEOne (e : R ≃+* S) [Ring.DimensionLEOne R] :
    Ring.DimensionLEOne S := by
  refine ⟨?_⟩
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
  simpa [Ideal.map_comap_eq_self_of_equiv] using hmapMax

/-- Transport `IsDedekindDomain` across a ring equivalence. -/
theorem isDedekindDomain (e : R ≃+* S) [IsDedekindDomain R] :
    IsDedekindDomain S := by
  letI : Module R R := Semiring.toModule
  letI : IsNoetherianRing R :=
    show IsNoetherian R R from IsDedekindRing.toIsNoetherian
  letI : IsDomain S := e.toMulEquiv.isDomain_iff.mp inferInstance
  letI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  letI : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e
  letI : Ring.DimensionLEOne S := dimensionLEOne e
  letI : Module S S := Semiring.toModule
  letI : IsDedekindRing S :=
    { toIsNoetherian := show IsNoetherian S S from inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure :=
        show IsIntegralClosure S S (FractionRing S) from inferInstance }
  infer_instance

/-- `IsDedekindDomain` is invariant under ring equivalence. -/
theorem isDedekindDomain_iff (e : R ≃+* S) :
    IsDedekindDomain R ↔ IsDedekindDomain S := by
  constructor
  · intro h
    letI : IsDedekindDomain R := h
    exact isDedekindDomain e
  · intro h
    letI : IsDedekindDomain S := h
    exact isDedekindDomain e.symm

end CommRing

end RingEquiv
