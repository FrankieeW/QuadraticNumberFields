# PR #36347 — Quadratic Number Fields: Foundation

**Status:** 🔍 Review (OPEN)
**Depends on:** Nothing
**Created:** 2026-03-08
**URL:** https://github.com/leanprover-community/mathlib4/pull/36347

---

## Commit Message

```
feat(NumberTheory/QuadraticField): define quadratic number fields as QuadraticAlgebra ℚ d 0

Define `Qsqrtd d` as `QuadraticAlgebra ℚ d 0`, representing the quadratic number field `ℚ(√d)`.
Prove trace and norm results, show `Qsqrtd d` is a number field and a quadratic extension
when `d` is not a perfect square, and prove that `ℚ(√0)` and `ℚ(√1)` are not fields.
Include `IsQuadraticField` as a predicate for quadratic extensions of `ℚ`, and bridge lemmas
connecting squarefree integer parameters to the non-square condition.
```

---

## Main Definitions

- `Qsqrtd d := QuadraticAlgebra ℚ d 0` — quadratic number field `ℚ(√d)`
- `IsQuadraticField K` — predicate for quadratic extensions of `ℚ`

## Main Theorems

- Trace and norm results for `Qsqrtd d`
- `Qsqrtd d` is a `NumberField` when `d` is not a perfect square
- `Qsqrtd d` is a quadratic extension when `d` is not a perfect square
- `ℚ(√0)` and `ℚ(√1)` are not fields
- Bridge lemmas: squarefree integer parameters → non-square condition

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
| 2026-03-08 | initial | PR submitted |

---

## Links

- [Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields)
