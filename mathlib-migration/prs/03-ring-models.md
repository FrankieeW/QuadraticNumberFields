# PR 3 — Ring of Integers: Models and Mod-4 Infrastructure

**Status:** ⏳ Pending (blocked on PR 1)
**Depends on:** PR 1
**Size:** ~550 lines
**Created:** 2026-03-09

---

## Links

- **mathlib PR:** (pending)
- **Project source files:**
  - `Lean/QuadraticNumberFields/RingOfIntegers/ModFour.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/Zsqrtd.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/ZsqrtdMathlibInstances.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/HalfInt.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/ZOnePlusSqrtOverTwo.lean`

---

## Content Summary

### Mod-4 arithmetic
- `squarefree_int_emod_four`: squarefree integers have remainder in `{1, 2, 3}` mod 4
- `dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one`: main criterion
  `4 ∣ (a'² - d·b'²) ↔ (2∣a' ∧ 2∣b') ∨ (both odd ∧ d ≡ 1 mod 4)`
- `exists_k_of_mod_four_eq_one`: `d % 4 = 1 ↔ ∃ k, d = 1 + 4k`

### `ℤ[√d]` as QuadraticAlgebra
- `Zsqrtd d := QuadraticAlgebra ℤ d 0`
- `equivMathlib`: ring equivalence with mathlib's `ℤ√d`
- `toQsqrtdHom`: embedding into `ℚ(√d)` + injectivity
- `NoZeroDivisors`, `IsDomain` instances (for `d < 0`)
- `halfInt_mem_range_toQsqrtdHom_iff_even_even`

### Half-integer form and `ℤ[(1+√d)/2]`
- `halfInt d a' b'`: element `(a' + b'√d) / 2`
- `ZOnePlusSqrtOverTwo k := QuadraticAlgebra ℤ k 1` (since `ω² = ω + k`)
- `toQsqrtdHom` + injectivity
- `halfInt_mem_carrierSet_iff_same_parity`

---

## Design Questions for Review

1. **`Zsqrtd` duplication:** Keep our own `Zsqrtd` (as `QuadraticAlgebra ℤ d 0`) or extend mathlib's `ℤ√d` directly?
   - **Recommendation:** Contribute `NoZeroDivisors`/`IsDomain` directly to `Mathlib.NumberTheory.Zsqrtd.Basic`, add `QuadraticAlgebra` equivalence as compatibility layer

2. **Mod-4 lemmas location:** Some (e.g. `Int.sq_emod_four_of_even`) may already exist or belong in `Mathlib.Data.Int.Parity`

3. **`ZOnePlusSqrtOverTwo` parameterization:** Via `QuadraticAlgebra ℤ k 1` needs clear documentation

---

## Review History

### Review 1 — (pending)

**Reviewer:** (pending)
**Date:** (pending)

#### Comments

(pending)

#### Action Items

- [ ] (pending)

---

## Changes Made

| Date | Commit | Description |
|------|--------|-------------|
| (pending) | - | Initial PR submission |

---

## Notes

- Review risk: **High** — largest PR, `Zsqrtd` duplication discussion expected
- This PR can be prepared in parallel with PR 2 after PR 1 is submitted
