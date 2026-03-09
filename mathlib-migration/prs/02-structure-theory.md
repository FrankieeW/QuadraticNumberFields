# PR #36387 — Parameter Uniqueness for Quadratic Fields

**Status:** 🔍 Review (OPEN)
**Depends on:** #36347
**Created:** 2026-03-09
**URL:** https://github.com/leanprover-community/mathlib4/pull/36387

---

## Summary

Prove that every quadratic field `ℚ(√d)` can be normalized to have a squarefree integer parameter, and that this parameter is unique.

## Main Results

| Theorem | Statement |
|---------|-----------|
| `Qsqrtd.rescale` | Rescaling isomorphism `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` for `a ≠ 0` |
| `Qsqrtd_iso_int_param` | Every `ℚ(√d)` is isomorphic to one with an integer parameter |
| `Qsqrtd_iso_squarefree_int_param` | Every `ℚ(√d)` is isomorphic to one with a squarefree integer parameter |
| `Qsqrtd.param_unique` | If `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` with both squarefree and `≠ 1`, then `d₁ = d₂` |

## Helper Lemmas

- `squarefree_eq_of_rat_sq_mul`: if `d₁ = d₂ · r²` with both squarefree, then `d₁ = d₂`
- `int_dvd_of_ratio_square`: if `d₁/d₂` is a rational square and `d₂` is squarefree, then `d₂ ∣ d₁`
- `not_isSquare_neg_one_rat`: `-1` is not a square in `ℚ`

## Target Location

```
Mathlib/NumberTheory/QuadraticField/Basic.lean
```

---

## Review History

### Review 1 — (in progress)

**Date:** (ongoing)

#### Comments

(pending review feedback)

#### Action Items

- [ ] (pending)

---

## Changes Made

| Date | Commit | Description |
|------|--------|-------------|
| 2026-03-09 | initial | PR submitted |

---

## Notes

- This PR depends on #36347 being merged first
- Forms the foundation for ring of integers classification (PR 3, PR 4)
