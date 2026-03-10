/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.ExplicitNorm

/-!
# Norm Integrality via Classification

This file contains norm statements that depend on the ring-of-integers
classification. Explicit norm formulas for the concrete quadratic orders live in
`ExplicitNorm.lean`.
-/

open scoped NumberField

namespace QuadraticNumberFields

namespace RingOfIntegers

section ParamLevel

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- For `α ∈ 𝓞(Q(√d))`, the norm `N(α)` is an integer.

This follows from the classification theorem: elements of the ring of integers
live in either `ℤ[√d]` or `ℤ[(1+√d)/2]`, both of which have integer-valued norm.

TODO: This proof requires establishing that the ring isomorphism from the
classification commutes with the coercion to the number field. -/
theorem norm_mem_ringOfIntegers (α : 𝓞 (Qsqrtd (d : ℚ))) :
    ∃ n : ℤ, Qsqrtd.norm (α : Qsqrtd (d : ℚ)) = n := by
  rcases ringOfIntegers_classification d with ⟨hd4, h_equiv⟩ | ⟨k, hk, h_equiv⟩
  · -- d % 4 ≠ 1 branch: 𝓞 ≃ ℤ[√d]
    let e := Classical.choice h_equiv
    let z : Zsqrtd d := e α
    -- TODO: Prove that (α : Qsqrtd (d : ℚ)) = Zsqrtd.toQsqrtd z
    sorry
  · -- d % 4 = 1 branch: 𝓞 ≃ ℤ[(1 + √d)/2]
    subst hk
    let e := Classical.choice h_equiv
    let z : ZOnePlusSqrtOverTwo k := e α
    -- TODO: Prove that (α : Qsqrtd ...) = toQsqrtdHom k z
    sorry

end ParamLevel

end RingOfIntegers
end QuadraticNumberFields
