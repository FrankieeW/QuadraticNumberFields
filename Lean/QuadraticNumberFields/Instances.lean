/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Field and Number Field Instances for `Qsqrtd`

This file equips `Qsqrtd d` (i.e., `QuadraticAlgebra ℚ d 0`) with `Field` and
`NumberField` typeclass instances, gated by `[Fact (¬ IsSquare d)]`.

## Main Instances

* `Field (Qsqrtd d)`: `Q(√d)` is a field when `d` is not a perfect square.
* `NumberField (Qsqrtd d)`: `Q(√d)` is a number field.
* `Algebra.IsQuadraticExtension ℚ (Qsqrtd d)`: `Q(√d)/ℚ` is a degree-2 extension.

## Implementation Note

`Field (QuadraticAlgebra R a b)` requires `Fact (∀ r, r^2 ≠ a + b*r)`.
For `b = 0` this simplifies to `¬ IsSquare d`. We provide a bridge instance
`Qsqrtd.instFact_of_not_isSquare` so that `[Fact (¬ IsSquare d)]` suffices.
-/

namespace Qsqrtd

/-- Bridge: `¬ IsSquare d` implies the technical `Fact` needed by
`QuadraticAlgebra.instField`. -/
instance instFact_of_not_isSquare (d : ℚ) [Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  ⟨by intro r hr; exact (Fact.out : ¬ IsSquare d) ⟨r, by nlinarith [hr]⟩⟩

/-- The `Module ℚ` instance from the `Field` algebra structure on `Qsqrtd d` coincides
with the `QuadraticAlgebra` module structure. This resolves the diamond. -/
private theorem module_eq (d : ℚ) [Fact (¬ IsSquare d)] :
    (Algebra.toModule : Module ℚ (Qsqrtd d)) =
      QuadraticAlgebra.instModule := by
  refine Module.ext' _ _ ?_
  intro r x
  simpa [Algebra.smul_def, QuadraticAlgebra.algebraMap_eq] using
    (QuadraticAlgebra.C_mul_eq_smul (R := ℚ) (a := d) (b := (0 : ℚ)) r x)

/-- `Q(√d)` is a number field: characteristic zero and finite-dimensional over ℚ. -/
instance instNumberField (d : ℚ) [Fact (¬ IsSquare d)] : NumberField (Qsqrtd d) where
  to_charZero := by infer_instance
  to_finiteDimensional := by
    letI : Module ℚ (Qsqrtd d) := QuadraticAlgebra.instModule
    exact module_eq d ▸ (inferInstance : Module.Finite ℚ (Qsqrtd d))

/-- `Q(√d)/ℚ` is a quadratic extension: free of rank 2 over `ℚ`. -/
instance instIsQuadraticExtension (d : ℚ) [Fact (¬ IsSquare d)] :
    Algebra.IsQuadraticExtension ℚ (Qsqrtd d) where
  finrank_eq_two' := module_eq d ▸ QuadraticAlgebra.finrank_eq_two d 0

end Qsqrtd
