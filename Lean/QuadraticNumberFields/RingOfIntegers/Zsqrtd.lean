/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.FieldInstance
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# QA Framework for `Zsqrtd`

This module is a QA-owned scaffold around `ℤ[√d]`.
Current phase: API shape only; no property proofs.

## TODO (Revised Phase Plan)

1. API cleanup and stability
- [x] Base model and `toMathlib/ofMathlib/equivMathlib` are in place.
- [ ] Add focused `[simp]` lemmas for coordinates under these maps.
- [ ] Add transport lemmas for `trace`, `norm`, `conj`, and `sqrtd` across `equivMathlib`.

2. Embedding into `Q(√d)`
- [x] Upgrade `toQsqrtd` from a function to a ring hom
  `toQsqrtdHom : Zsqrtd d →+* Qsqrtd (d : ℚ)`.
- [x] Prove injectivity for the embedding and add cast-coordinate simp lemmas.
- [ ] Replace `Set.range` placeholders by carrier APIs built from the ring hom.

3. Classification support
- [ ] Add bridge theorem: QA carrier in `Q(√d)` corresponds to mathlib `ℤ√d` image.
- [ ] Expose lemmas consumed by `Integrality.lean` for the non-`1 mod 4` branch.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- QA base model of `ℤ[√d]` reusing `QuadraticAlgebra`. -/
abbrev Zsqrtd (d : ℤ) : Type := QuadraticAlgebra ℤ d 0

namespace Zsqrtd

variable {d : ℤ}

/-- Integer embedding into `Zsqrtd`. -/
abbrev ofInt (n : ℤ) : Zsqrtd d := algebraMap ℤ (Zsqrtd d) n

/-- The distinguished square-root element `√d`. -/
abbrev sqrtd : Zsqrtd d := ⟨0, 1⟩

/-- Conjugation `(a + b√d) ↦ (a - b√d)`. -/
abbrev conj (z : Zsqrtd d) : Zsqrtd d := star z

/-- Trace API on `Zsqrtd`. -/
abbrev trace (z : Zsqrtd d) : ℤ := z.re + (star z).re

/-- Norm API on `Zsqrtd`. -/
abbrev norm (z : Zsqrtd d) : ℤ := QuadraticAlgebra.norm z

/-- Rational embedding into `Q(√d)`. -/
def toQsqrtd (z : Zsqrtd d) : Qsqrtd (d : ℚ) := ⟨(z.re : ℚ), (z.im : ℚ)⟩

/-- Rational embedding into `Q(√d)` as a ring hom. -/
def toQsqrtdHom (d : ℤ) : Zsqrtd d →+* Qsqrtd (d : ℚ) where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    change ({ re := ((1 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 1
    rfl
  map_mul' := by
    intro x y
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by
    change ({ re := ((0 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 0
    rfl
  map_add' := by
    intro x y
    ext <;> simp

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : Zsqrtd d) :
    toQsqrtdHom d z = toQsqrtd z := rfl

/-- The canonical map `toQsqrtdHom` is injective. -/
theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  ext
  · have hre : ((x.re : ℚ) : ℚ) = (y.re : ℚ) := by
      simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.re hxy
    exact_mod_cast hre
  · have him : ((x.im : ℚ) : ℚ) = (y.im : ℚ) := by
      simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.im hxy
    exact_mod_cast him

/-- Coordinate map from QA `Zsqrtd` to mathlib's `ℤ√d`. -/
def toMathlib (d : ℤ) : Zsqrtd d →+* ℤ√d where
  toFun := fun z => ⟨z.re, z.im⟩
  map_one' := by ext <;> rfl
  map_mul' := by
    intro x y
    ext <;> simp
  map_zero' := by ext <;> rfl
  map_add' := by
    intro x y
    ext <;> rfl

/-- Coordinate map from mathlib's `ℤ√d` to QA `Zsqrtd`. -/
def ofMathlib (d : ℤ) : ℤ√d →+* Zsqrtd d where
  toFun := fun z => ⟨z.re, z.im⟩
  map_one' := by ext <;> rfl
  map_mul' := by
    intro x y
    ext <;> simp
  map_zero' := by ext <;> rfl
  map_add' := by
    intro x y
    ext <;> rfl

@[simp] theorem toMathlib_ofMathlib (d : ℤ) (z : ℤ√d) :
    toMathlib d (ofMathlib d z) = z := by
  ext <;> rfl

@[simp] theorem ofMathlib_toMathlib (d : ℤ) (z : Zsqrtd d) :
    ofMathlib d (toMathlib d z) = z := by
  ext <;> rfl

/-- Ring isomorphism between QA `Zsqrtd` and mathlib's `ℤ√d`. -/
def equivMathlib (d : ℤ) : Zsqrtd d ≃+* ℤ√d where
  toFun := toMathlib d
  invFun := ofMathlib d
  left_inv := ofMathlib_toMathlib d
  right_inv := toMathlib_ofMathlib d
  map_mul' := by
    intro x y
    ext <;> simp [mul_comm, mul_left_comm]
  map_add' := by
    intro x y
    rfl

/-- Pair conversion helper for interoperability. -/
abbrev toPair (z : Zsqrtd d) : ℤ × ℤ := (z.re, z.im)

/-- Pair conversion helper for interoperability. -/
abbrev fromPair (p : ℤ × ℤ) : Zsqrtd d := ⟨p.1, p.2⟩

/-- Half-integer representative `(a' + b'√d)/2` in `Q(√d)`. -/
def halfInt (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  ⟨(a' : ℚ) / 2, (b' : ℚ) / 2⟩

/-- `halfInt` is in the image of `Zsqrtd d` iff both numerators are even. -/
theorem halfInt_mem_range_toQsqrtdHom_iff_even_even (d a' b' : ℤ) :
    (∃ z : Zsqrtd d, toQsqrtdHom d z = halfInt (d := d) a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.im hz.symm
    refine ⟨?_, ?_⟩
    · refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    · refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [toQsqrtdHom, halfInt, hm, hn]

end Zsqrtd

/-- Candidate carrier of `ℤ[√d]` inside `Q(√d)` as a set. -/
def zsqrtdCarrierInQ (d : ℤ) : Set (Qsqrtd (d : ℚ)) :=
  Set.range (Zsqrtd.toQsqrtd (d := d))

end RingOfIntegers
end QuadraticNumberFields
