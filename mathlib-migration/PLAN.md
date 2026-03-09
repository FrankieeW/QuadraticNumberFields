# Mathlib Migration Plan

**Author:** Frankie Wang
**Status:** In Progress
**Created:** 2026-03-08
**Updated:** 2026-03-09

---

## Overview

Upstreaming the [QuadraticNumberFields](https://github.com/FrankieeW/QuadraticNumberFields) project into [mathlib4](https://github.com/leanprover-community/mathlib4).

### Main Result (Target)

For squarefree `d ≠ 1`:
- `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`
- `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`

### Guiding Principles

1. **Dependency order** — later PRs build on earlier ones
2. **Mathlib conventions** — naming, style, documentation
3. **No `sorry`** — defer incomplete files to future work
4. **Reuse mathlib API** — avoid duplication

---

## PR Series

| # | Title | Status | Number | Tracking |
|---|-------|--------|--------|----------|
| 1 | Define quadratic number fields as `QuadraticAlgebra ℚ d 0` | 🔍 Review | [#36347](https://github.com/leanprover-community/mathlib4/pull/36347) | [prs/01-foundation.md](./prs/01-foundation.md) |
| 2 | Parameter uniqueness for quadratic fields | 🔍 Review | [#36387](https://github.com/leanprover-community/mathlib4/pull/36387) | [prs/02-structure-theory.md](./prs/02-structure-theory.md) |
| 3 | Ring of integers models (Mod4, Zsqrtd, ZOnePlusSqrtOverTwo) | ⏳ Pending | — | [prs/03-ring-models.md](./prs/03-ring-models.md) |
| 4 | Classification theorem + Ideal theory | ⏳ Pending | — | [prs/04-classification.md](./prs/04-classification.md) |

### Status Legend
- 🔍 Review — Submitted, awaiting/under review
- 🔄 Revisions — Addressing feedback
- ✅ Merged — Merged into mathlib
- ⏳ Pending — Not yet submitted

---

## Dependency Graph

```
PR #36347 (Foundation)
└── PR #36387 (Parameter Uniqueness)
    └── PR 3 (Ring Models)
        └── PR 4 (Classification)
```

---

## PR Details

### PR #36347 — Foundation

**Main content:**
- `Qsqrtd d := QuadraticAlgebra ℚ d 0`
- `IsQuadraticField K` predicate
- Trace/norm results
- Number field and quadratic extension instances
- Bridge lemmas: squarefree integer → non-square

### PR #36387 — Parameter Uniqueness

**Main content:**
- `Qsqrtd.rescale`: `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))`
- `Qsqrtd_iso_int_param`, `Qsqrtd_iso_squarefree_int_param`
- `Qsqrtd.param_unique`
- Helpers: `squarefree_eq_of_rat_sq_mul`, `int_dvd_of_ratio_square`, `not_isSquare_neg_one_rat`

### PR 3 — Ring of Integers Models (Planned)

**Content:**
- Mod-4 arithmetic lemmas
- `Zsqrtd d` as `QuadraticAlgebra ℤ d 0` with mathlib equivalence
- `ZOnePlusSqrtOverTwo k` as `QuadraticAlgebra ℤ k 1`
- Half-integer normal form

### PR 4 — Classification (Planned)

**Content:**
- Integrality criteria (~250 line proof)
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- Discriminant formula
- Ideal theory: quotients by prime ideals

---

## Target Location in Mathlib

```
Mathlib/NumberTheory/QuadraticField/
├── Basic.lean           -- PR 1, 2: Qsqrtd, rescale, uniqueness
└── RingOfIntegers/
    ├── ModFour.lean
    ├── Zsqrtd.lean
    ├── ZsqrtdInstances.lean
    ├── HalfInt.lean
    ├── ZOnePlusSqrtOverTwo.lean
    ├── Integrality.lean
    ├── Classification.lean
    ├── Norm.lean
    └── ZsqrtdIdeals.lean
```

---

## Pre-Migration Checklist

- [x] Create migration tracking structure
- [ ] **Fix `sorry`** in `Norm.lean`: `norm_mem_ringOfIntegers`
- [ ] **Bump to latest mathlib** before PR 3
- [ ] **Run `#lint`** on all files
- [ ] **Add copyright headers**
- [ ] **Add module docstrings**
- [ ] **Remove ANCHOR comments**

---

## References

- [Zulip: quadratic number fields](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)
- [Zulip: Z[(1+sqrt(1+4k))/2]](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [mathlib contributing guide](https://leanprover-community.github.io/contribute/)
