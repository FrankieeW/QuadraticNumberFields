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

| Definition | Description |
|------------|-------------|
| `Qsqrtd d` | `QuadraticAlgebra ℚ d 0` — quadratic number field `ℚ(√d)` |
| `IsQuadraticField K` | Predicate for quadratic extensions of `ℚ` |

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

### Review 1 — 2026-03-09

#### Reviewers
- @wwylele (COLLABORATOR)
- @tb65536 (CONTRIBUTOR)
- @riccardobrasca (MEMBER)
- @eric-wieser (MEMBER)

---

### @riccardobrasca — Generalization & Diamond

> Can you generalize as many results as possible to `QuadraticAlgebra ℚ a b`? For example it is always a number field. Also please pay attention to the diamond mentioned in https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/QuadraticAlgebra/Defs.html

**Response:** Thanks for the review! I'll think about generalizing the results to QuadraticAlgebra ℚ a b and look into the diamond issue. Also, I noticed there's an existing formalization blueprint for quadratic integers at https://pitmonticone.github.io/QuadraticIntegers/ — I'll study it to see how it relates to this work and whether it suggests any generalizations.

**Action Items:**
- [ ] Generalize results to `QuadraticAlgebra ℚ a b`
- [ ] Address the diamond issue mentioned in QuadraticAlgebra docs
- [ ] Review QuadraticIntegers blueprint for relevant patterns

---

### @wwylele — Trace Abbreviation

> I think this reduces discoverability for trace-related lemma and doesn't provide much benefit. How about making this a local notation, if the purpose is to shorten the spelling?

**Response:** I've removed the trace abbreviation entirely and now use `Algebra.trace ℚ (Qsqrtd d)` directly, which also aligns with the convention in `RingTheory/Complex.lean`. This also fixed the `simpNF` lint failure on `trace_eq_two_re`.

**Resolution:** ✅ Fixed — Removed trace abbreviation, using full `Algebra.trace` instead

---

### @tb65536 — IsQuadraticField Design

> I think just `finrank = 2` makes more sense here since you're working with fields.
>
> Should this be a class with a `NumberField` instance?

**Response:**
1. Regarding `finrank = 2`: I actually started with `finrank ℚ K = 2` as the definition, but later discovered `IsQuadraticExtension` in mathlib, which captures exactly the same notion for degree-2 extensions. I switched to it following the pattern of reusing existing canonical abstractions.

2. Regarding `NumberField` instance: I've now added `IsQuadraticField.instNumberField` which derives `NumberField K` from `[Field K] [Algebra ℚ K] [IsQuadraticField K]`, so `NumberField` is a consequence rather than a prerequisite. The ℚ-algebra diamond is resolved via `Subsingleton.elim` (using `Rat.algebra_rat_subsingleton`).

**Resolution:** ✅ Addressed — Using `IsQuadraticExtension` pattern; added `NumberField` instance

---

### @tb65536 — Squarefree Lemmas Location

> This should be in an earlier file (and probably generalized to arbitrary rings or even monoids?).
>
> Can you prove this without `CommMonoid`?
>
> And can you first prove that `Squarefree (a * a)` implies that `a` is a unit?

**Response:** Done, see f83e675, 4da160d

**Action Items:**
- [x] Prove `Squarefree (a * a)` implies `a` is a unit first
- [ ] Consider generalizing to arbitrary rings/monoids
- [ ] Consider moving to earlier file in algebra hierarchy

**Suggestion Applied:**
```lean
-- Before:
  fun hsq ↦ ha (hsf.isUnit_of_isSquare hsq)

-- After (per @tb65536 suggestion):
  obtain ⟨z, rfl⟩ := hsq
```

---

### @eric-wieser — Basis Lemma Generalization

> Is there a more general version of this for `QuadraticAlgebra.basis d1 d2` that could go in the `QuadraticAlgebra` file?

**Action Items:**
- [ ] Consider generalizing basis lemmas to `QuadraticAlgebra.basis`

---

## Changes Made

| Date | Commit | Description |
|------|--------|-------------|
| 2026-03-08 | initial | PR submitted |
| 2026-03-09 | e1782ad | Addressed trace abbreviation feedback |
| 2026-03-09 | 9e56e9b | Added `IsQuadraticField.instNumberField` |
| 2026-03-09 | f83e675 | Proved `Squarefree (a * a)` → `IsUnit` first |
| 2026-03-09 | 4da160d | Applied suggestion: `obtain ⟨z, rfl⟩` |

---

## Open Questions

1. **Generalization to `QuadraticAlgebra ℚ a b`** — How much can be generalized?
2. **Diamond issue** — Need to investigate the specific diamond mentioned in docs
3. **File organization** — Where should squarefree lemmas go?
4. **Basis generalization** — Can `leftMulMatrix_eq` be generalized?

---

## Links

- [Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/quadratic.20number.20fields/)
- [QuadraticAlgebra diamond docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/QuadraticAlgebra/Defs.html)
- [QuadraticIntegers blueprint](https://pitmonticone.github.io/QuadraticIntegers/)
