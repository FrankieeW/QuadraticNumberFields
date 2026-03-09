# PR 4 — Ring of Integers: Classification Theorem

**Status:** ⏳ Pending (blocked on PR 2, PR 3)
**Depends on:** PR 2 (ParamUniqueness), PR 3
**Size:** ~800 lines
**Created:** 2026-03-09

---

## Links

- **mathlib PR:** (pending)
- **Project source files:**
  - `Lean/QuadraticNumberFields/RingOfIntegers/Integrality.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/Classification.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/Norm.lean`
  - `Lean/QuadraticNumberFields/RingOfIntegers/ZsqrtdIdeals.lean`

---

## Content Summary

### Integrality criteria
- `exists_halfInt_with_div_four_of_isIntegral`: every integral element has form
  `(a' + b'√d)/2` with `4 ∣ (a'² - d·b'²)` (~250 line proof)
- `exists_zsqrtd_of_isIntegral_of_ne_one_mod_four`: forward direction for `d % 4 ≠ 1`
- `exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four`: forward direction for `d % 4 = 1`
- `isIntegral_toQsqrtd`, `isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo`: reverse directions

### Main Classification Theorem
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`
- `ringOfIntegers_classification`: combined statement
- Concrete examples: Gaussian integers (`d = -1`), Eisenstein integers (`d = -3`)

### Norm computations
- `norm_mul`, `norm_zsqrtd`, `norm_zOnePlusSqrtOverTwo`: explicit formulas
- `isUnit_zsqrtd_iff_norm_eq_one_or_neg_one`: unit criterion for `ℤ[√d]`
- `isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one`: unit criterion for `ℤ[(1+√d)/2]`

### Ideal theory (general framework for any squarefree `d` and prime `p ∣ (d-1)`)
- `liftModP`, `liftModPNeg`: ring homs `ℤ[√d] →+* ZMod p`
- `quotEquivZModP`, `quotEquivZModPNeg`: quotient ring equivalences
- `isPrime_span_p_one_minus_sqrtd`, `isPrime_span_p_one_plus_sqrtd`: primality

---

## Pre-work Required

- [ ] **Fix `sorry`** in `norm_mem_ringOfIntegers` (`Norm.lean`)

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

- Review risk: **High** — main theorem, large proof in `Integrality.lean`
- This is the core theorem of the project
- `ZsqrtdIdeals.lean` has no dependency on Classification but is included in this PR to reduce total number of PRs
