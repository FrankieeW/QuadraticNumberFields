# Mathlib Migration Plan — QuadraticNumberFields

**Author:** Frankie Wang
**Date:** 2026-03-08
**Status:** Draft

---

## Overview

This document outlines a series of PRs to upstream the `QuadraticNumberFields` project
into [mathlib4](https://github.com/leanprover-community/mathlib4). The project
formalizes quadratic number fields `ℚ(√d)` and the classification of their ring of
integers, totaling ~1650 lines of code across 18 source files.

### Guiding Principles

1. **Dependency order** — later PRs build on earlier ones
2. **Mathlib conventions** — rewrite naming, style, and documentation to match mathlib
3. **No `sorry`** — defer incomplete files (Euclidean skeleton) to future work
4. **Reuse existing mathlib API** — avoid duplicating `Zsqrtd`, `GaussianInt`, etc.

### What Already Exists in Mathlib

| Mathlib Module | Content |
|---|---|
| `Mathlib.NumberTheory.Zsqrtd.Basic` | `ℤ√d` structure, norm, units |
| `Mathlib.NumberTheory.Zsqrtd.GaussianInt` | `ℤ[i]` as `ℤ√(-1)` |
| `Mathlib.Algebra.QuadraticAlgebra.Basic` | `QuadraticAlgebra R a b` |
| `Mathlib.NumberTheory.NumberField.Basic` | `NumberField`, `𝓞 K` |
| `Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex` | Totally real/complex |
| `Mathlib.NumberTheory.NumberField.CMField` | CM field definition |
| `Mathlib.NumberTheory.RamificationInertia.Basic` | `e`, `f`, ramification |

### Target Location in Mathlib

```
Mathlib/NumberTheory/QuadraticField/
  Basic.lean                  -- PR 1
  Param.lean                  -- PR 1
  Instances.lean              -- PR 1
  Rescale.lean                -- PR 2
  ParamUniqueness.lean        -- PR 2
  TotallyRealComplex.lean     -- PR 2
  RingOfIntegers/
    ModFour.lean              -- PR 3
    Zsqrtd.lean               -- PR 3
    ZsqrtdInstances.lean      -- PR 3
    HalfInt.lean              -- PR 3
    ZOnePlusSqrtOverTwo.lean  -- PR 3
    Integrality.lean          -- PR 4
    Classification.lean       -- PR 4
    Norm.lean                 -- PR 4
    ZsqrtdIdeals.lean         -- PR 4
```

---

## PR Series

### PR 1 — Quadratic Number Fields: Foundation

**Source files:** `Basic.lean`, `Param.lean`, `Instances.lean`
**Depends on:** nothing (only mathlib)
**Size:** ~230 lines

**Content:**

`Qsqrtd` type and basic operations:
- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0` — type alias for `ℚ(√d)`
- `Qsqrtd.trace`, `Qsqrtd.norm`, `Qsqrtd.embed` with simp lemmas

`QuadFieldParam` parameter typeclass:
- `QuadFieldParam (d : ℤ)`: bundles `squarefree : Squarefree d` and `ne_one : d ≠ 1`
- Constructors: `of_squarefree_ne_one`, `of_prime`, `of_natAbs_prime`
- Instances for `d = -1`, `d = -3`
- Degeneracy lemmas: `zero_not_isReduced`, `one_not_isField`

`QuadraticNumberFields` and algebra instances:
- `QuadraticNumberFields (d : ℤ) [QuadFieldParam d] := Qsqrtd (d : ℚ)`
- `Field`, `NumberField`, `IsQuadraticExtension` instances
- Module diamond resolution

**Migration notes:**
- Discuss on Zulip whether `QuadFieldParam` should be a typeclass or separate hypotheses
- Check whether `trace`/`norm` should use mathlib's `Algebra.trace`/`Algebra.norm` with
  compatibility proofs instead of standalone definitions
- Module diamond resolution needs careful review

**Review risk:** Medium — design discussion expected.

---

### PR 2 — Structure Theory: Rescale, Uniqueness, and Places

**Source files:** `Rescale.lean`, `ParamUniqueness.lean`, `TotallyRealComplex.lean`
**Depends on:** PR 1
**Size:** ~300 lines

**Content:**

Rescaling:
- `rescale d a ha`: algebra isomorphism `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))`
- `Qsqrtd_iso_int_param`, `Qsqrtd_iso_squarefree_int_param`: normalization results

Parameter uniqueness:
- `QuadFieldParam.unique`: `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` with both squarefree implies `d₁ = d₂`
- `squarefree_eq_of_rat_sq_mul`: `d₁ = d₂ · r²` with both squarefree implies `d₁ = d₂`

Infinite places:
- `isTotallyReal`: `ℚ(√d)` is totally real when `d > 0`
- `isTotallyComplex`: `ℚ(√d)` is totally complex when `d < 0`
- `isCMField`: `ℚ(√d)` is a CM field when `d < 0`

**Migration notes:**
- `TotallyRealComplex.lean` uses `attribute [-instance] DivisionRing.toRatAlgebra`
  to resolve a diamond — check whether this is still needed on latest mathlib
- Rescale and ParamUniqueness are independent and can be reviewed in parallel

**Review risk:** Medium — instance management.

---

### PR 3 — Ring of Integers: Models and Mod-4 Infrastructure

**Source files:** `RingOfIntegers/ModFour.lean`, `RingOfIntegers/Zsqrtd.lean`,
`RingOfIntegers/ZsqrtdMathlibInstances.lean`, `RingOfIntegers/HalfInt.lean`,
`RingOfIntegers/ZOnePlusSqrtOverTwo.lean`
**Depends on:** PR 1
**Size:** ~550 lines

**Content:**

Mod-4 arithmetic:
- `squarefree_int_emod_four`: squarefree integers have remainder in `{1, 2, 3}` mod 4
- `dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one`: main criterion
  `4 ∣ (a'² - d·b'²) ↔ (2∣a' ∧ 2∣b') ∨ (both odd ∧ d ≡ 1 mod 4)`
- `exists_k_of_mod_four_eq_one`: `d % 4 = 1 ↔ ∃ k, d = 1 + 4k`

`ℤ[√d]` as QuadraticAlgebra:
- `Zsqrtd d := QuadraticAlgebra ℤ d 0`
- `equivMathlib`: ring equivalence with mathlib's `ℤ√d`
- `toQsqrtdHom`: embedding into `ℚ(√d)` + injectivity
- `NoZeroDivisors`, `IsDomain` instances (for `d < 0`)
- `halfInt_mem_range_toQsqrtdHom_iff_even_even`

Half-integer form and `ℤ[(1+√d)/2]`:
- `halfInt d a' b'`: element `(a' + b'√d) / 2`
- `ZOnePlusSqrtOverTwo k := QuadraticAlgebra ℤ k 1` (since `ω² = ω + k`)
- `toQsqrtdHom` + injectivity
- `halfInt_mem_carrierSet_iff_same_parity`

**Migration notes:**
- **Key design decision:** keep our own `Zsqrtd` (as `QuadraticAlgebra ℤ d 0`) or extend
  mathlib's `ℤ√d` directly? Recommendation: contribute `NoZeroDivisors`/`IsDomain`
  directly to `Mathlib.NumberTheory.Zsqrtd.Basic`, and add the `QuadraticAlgebra`
  equivalence as a compatibility layer
- Some mod-4 lemmas (e.g. `Int.sq_emod_four_of_even`) may already exist or belong in
  `Mathlib.Data.Int.Parity`
- The `ZOnePlusSqrtOverTwo` parameterization via `QuadraticAlgebra ℤ k 1` needs clear
  documentation

**Review risk:** High — largest PR, `Zsqrtd` duplication discussion.

---

### PR 4 — Ring of Integers: Classification Theorem

**Source files:** `RingOfIntegers/Integrality.lean`, `RingOfIntegers/Classification.lean`,
`RingOfIntegers/Norm.lean`, `RingOfIntegers/ZsqrtdIdeals.lean`
**Depends on:** PR 2 (ParamUniqueness), PR 3
**Size:** ~800 lines

**Content:**

Integrality criteria:
- `exists_halfInt_with_div_four_of_isIntegral`: every integral element has form
  `(a' + b'√d)/2` with `4 ∣ (a'² - d·b'²)` (~250 line proof)
- `exists_zsqrtd_of_isIntegral_of_ne_one_mod_four`: forward direction for `d % 4 ≠ 1`
- `exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four`: forward direction for `d % 4 = 1`
- `isIntegral_toQsqrtd`, `isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo`: reverse directions

**Main Classification Theorem:**
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`
- `ringOfIntegers_classification`: combined statement
- Concrete examples: Gaussian integers (`d = -1`), Eisenstein integers (`d = -3`)

Norm computations:
- `norm_mul`, `norm_zsqrtd`, `norm_zOnePlusSqrtOverTwo`: explicit formulas
- `isUnit_zsqrtd_iff_norm_eq_one_or_neg_one`: unit criterion for `ℤ[√d]`
- `isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one`: unit criterion for `ℤ[(1+√d)/2]`

Ideal theory (general framework for any squarefree `d` and prime `p ∣ (d-1)`):
- `liftModP`, `liftModPNeg`: ring homs `ℤ[√d] →+* ZMod p`
- `quotEquivZModP`, `quotEquivZModPNeg`: quotient ring equivalences
- `isPrime_span_p_one_minus_sqrtd`, `isPrime_span_p_one_plus_sqrtd`: primality

**Migration notes:**
- `Integrality.lean` is the most complex file; reviewers may request simplification
- **Must fix** the `sorry` in `norm_mem_ringOfIntegers` in `Norm.lean` before submitting
- This is the core theorem of the project
- `ZsqrtdIdeals.lean` has no dependency on Classification but is included in this PR
  to reduce the total number of PRs

**Pre-work required:**
- [ ] Fix `sorry` in `norm_mem_ringOfIntegers`

**Review risk:** High — main theorem, large proof.

---

## Excluded from Migration

| File | Reason |
|---|---|
| `Euclidean/Basic.lean` | Skeleton file with all proofs `sorry` — deferred to future work |
| `Examples/ZsqrtdNeg5/` | Concrete examples (`ℤ[√-5]` factorization/ramification); better suited for the external project or a future `Mathlib.Archive` submission |
| `Verso/` | Documentation tooling, not mathematical content |
| `site/` | Website, not relevant to mathlib |

---

## Pre-Migration Checklist

- [ ] **Fix `sorry`** in `Norm.lean`: `norm_mem_ringOfIntegers`
- [ ] **Zulip discussion** — post to `#mathlib4 > new PR` or `#Is there code for X?`
  - Topic: "Quadratic number fields: ring of integers classification"
  - Key design questions:
    1. `QuadFieldParam` as typeclass vs. separate hypotheses?
    2. Own `Zsqrtd` vs. extend mathlib's `ℤ√d` directly?
    3. Target directory `Mathlib.NumberTheory.QuadraticField` — acceptable?
- [ ] **Bump to latest mathlib** — ensure compatibility with `master`
- [ ] **Run `#lint`** on all files
- [ ] **Add copyright headers** — `Copyright (c) 2026 Frankie Wang. All rights reserved.`
- [ ] **Add module docstrings** — `/-! ... -/` with `## Main Definitions` / `## Main Theorems`
- [ ] **Remove ANCHOR comments** — not needed for mathlib
- [ ] **Remove `repl` dependency** — not needed for mathlib PRs

---

## Dependency Graph

```
PR 1 (Foundation: Qsqrtd + Param + Instances)
├── PR 2 (Structure Theory: Rescale + Uniqueness + Places)
├── PR 3 (Ring of Integers Models: Mod4 + Zsqrtd + ZOnePlusSqrtOverTwo)
│   └── PR 4 (Classification + Ideals)  ← also depends on PR 2
```

## Estimated Timeline

| Phase | PRs | Description |
|---|---|---|
| Phase 1 | PR 1 | Foundation (open first) |
| Phase 2 | PR 2, PR 3 | Structure theory + ring models (in parallel) |
| Phase 3 | PR 4 | Classification theorem + ideal theory |

Expected review cycle: 2–4 weeks per PR. Overall migration: ~2–3 months.

---

## PR Description Template

Each PR description should include the following to give reviewers full context:

```markdown
## Context

This PR is part of a series upstreaming the [QuadraticNumberFields](https://github.com/FrankieeW/QuadraticNumberFields) project, which formalizes quadratic number fields `ℚ(√d)` and classifies their ring of integers.

The full migration consists of 4 PRs:
1. **Foundation** — `Qsqrtd` type, `QuadFieldParam` typeclass, `Field`/`NumberField` instances *(this PR / merged as #XXXX)*
2. **Structure theory** — Rescaling isomorphisms, parameter uniqueness, totally real/complex/CM classification
3. **Ring of integers models** — Mod-4 arithmetic, `ℤ[√d]` as `QuadraticAlgebra`, `ℤ[(1+√d)/2]` ring
4. **Classification theorem** — Integrality criteria, `𝓞(ℚ(√d)) ≃+* ℤ[√d]` or `ℤ[(1+√d)/2]`, norm/unit criteria, ideal theory

### Main result (PR 4)

For squarefree `d ≠ 1`:
- `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`
- `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`

## This PR

*(describe this PR's specific content here)*
```

Update the list as PRs are merged (replace `this PR` / fill in merged PR numbers).

---

## References

- [Lean Zulip: Z[(1+sqrt(1+4k))/2]](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [mathlib contributing guide](https://leanprover-community.github.io/contribute/)
- [mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
