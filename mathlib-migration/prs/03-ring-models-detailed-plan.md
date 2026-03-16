# PR 3 — Detailed Migration Plan

**Status:** Planning
**Created:** 2026-03-10
**Updated:** 2026-03-10

---

## Overview

This document provides a detailed analysis of each theorem/definition in PR 3,
determining:
1. Target location in mathlib
2. Generalization opportunities
3. Dependencies
4. Mathlib conventions compliance

---

## File-by-File Analysis

### 1. ModFour.lean (196 lines)

#### Type: General Number Theory

**Location:** Most lemmas belong in `Mathlib/Data/Int/Parity.lean` or similar.

#### Lemmas Analysis

| Lemma | Lines | Target Location | Generalization | Priority |
|-------|-------|-----------------|----------------|----------|
| `squarefree_int_not_dvd_four` | 44-50 | `NumberTheory/QuadraticField/Basic.lean` | ❌ Specific to squarefree | 🟢 Keep |
| `squarefree_int_emod_four` | 52-56 | `NumberTheory/QuadraticField/Basic.lean` | ❌ Specific to squarefree | 🟢 Keep |
| `Int.sq_emod_four_of_even` | 58-62 | `Data/Int/Parity.lean` | ✅ **Generalize**: move to `Int` namespace | 🔴 **Move** |
| `Int.sq_emod_four_of_odd` | 64-70 | `Data/Int/Parity.lean` | ✅ **Generalize**: move to `Int` namespace | 🔴 **Move** |
| `div4_iff_mod` (private) | 72-74 | - | ❌ Private helper | ⚪ Inline |
| `sq_eq_four_mul_div_of_even` (private) | 76-79 | - | ❌ Private helper | ⚪ Inline |
| `sq_eq_four_mul_div_add_one_of_odd` (private) | 81-84 | - | ❌ Private helper | ⚪ Inline |
| `odd_eq_two_mul_div_add_one` (private) | 86-88 | - | ❌ Private helper | ⚪ Inline |
| `even_odd_impossible_of_mod_eq_zero` (private) | 90-100 | - | ❌ Private, quadratic-specific | ⚪ Keep |
| `odd_even_impossible_of_mod_eq_zero` (private) | 102-110 | - | ❌ Private, quadratic-specific | ⚪ Keep |
| `mod_four_eq_one_of_odd_odd_of_mod_eq_zero` (private) | 112-120 | - | ❌ Private, quadratic-specific | ⚪ Keep |
| `dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one` | 122-146 | `NumberTheory/QuadraticField/ModFour.lean` | ❌ Quadratic-specific | 🟢 Keep |
| `even_even_of_dvd_four_sub_sq_of_ne_one_mod_four` | 148-155 | `NumberTheory/QuadraticField/ModFour.lean` | ❌ Quadratic-specific | 🟢 Keep |
| `dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four` | 157-163 | `NumberTheory/QuadraticField/ModFour.lean` | ❌ Quadratic-specific | 🟢 Keep |
| `dvd_four_sub_sq_iff_same_parity_of_one_mod_four` | 165-177 | `NumberTheory/QuadraticField/ModFour.lean` | ❌ Quadratic-specific | 🟢 Keep |
| `exists_k_of_mod_four_eq_one` | 179-183 | `Data/Int/Parity.lean` | ✅ **Generalize**: generic `n % m = r → ∃ k, n = r + m*k` | 🔴 **Generalize** |
| `mod_four_eq_one_of_exists_k` | 185-189 | `Data/Int/Parity.lean` | ✅ **Generalize**: converse | 🔴 **Generalize** |
| `mod_four_branch_split` | 191-193 | - | ❌ Trivial, inline | ⚪ Delete |

#### Generalization Opportunities

##### 🔴 HIGH PRIORITY: Move to `Data/Int/Parity.lean`

```lean
-- Current (ModFour.lean:58-62)
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0

-- Generalization: Already exists in mathlib?
-- Check: Int.sq_mod_four_eq_zero_of_even (might exist)
```

**Action:**
1. Search mathlib for existing `Int.sq_*_mod_four` lemmas
2. If missing, contribute to `Data/Int/Parity.lean`
3. If exists, use existing lemma and delete ours

##### 🔴 HIGH PRIORITY: Generalize parameterization lemmas

```lean
-- Current (ModFour.lean:179-183)
theorem exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k

-- Generalization to propose:
theorem Int.exists_div_add_of_mod_eq {n m r : ℤ} (h : n % m = r) (hm : m ≠ 0) :
    ∃ k : ℤ, n = r + m * k := by
  exact ⟨n / m, by omega⟩

-- Special case:
theorem Int.exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k :=
  Int.exists_div_add_of_mod_eq hd4 (by norm_num)
```

**Action:**
1. Check if `Int.exists_div_add_of_mod_eq` exists in mathlib
2. If not, propose it as a separate PR to `Data/Int/Basic.lean`
3. Specialize in our code

---

### 2. Zsqrtd.lean (174 lines)

#### Type: Quadratic Algebra Infrastructure

**Location:** Split between:
- `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (mathlib compatibility)
- `Mathlib/NumberTheory/QuadraticField/Zsqrtd.lean` (new file)

#### Definitions & Theorems

| Item | Lines | Target Location | Generalization | Action |
|------|-------|-----------------|----------------|--------|
| `Zsqrtd d` (abbrev) | 36 | Keep as `QuadraticField.Zsqrtd` | ❌ Project-specific | 🟢 New file |
| `ofInt` | 42-43 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `sqrtd` | 45-46 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `conj` | 48-49 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `trace` | 51-52 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `norm` | 54-55 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtd` | 57-58 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdHom` | 60-74 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdHom_apply` | 76-77 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdHom_injective` | 79-88 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `toMathlib` | 90-100 | `NumberTheory/Zsqrtd/Basic.lean` | ✅ **Contribute** to mathlib's Zsqrtd | 🔴 **PR to Zsqrtd** |
| `ofMathlib` | 102-112 | `NumberTheory/Zsqrtd/Basic.lean` | ✅ **Contribute** to mathlib's Zsqrtd | 🔴 **PR to Zsqrtd** |
| `toMathlib_ofMathlib` | 114-116 | `NumberTheory/Zsqrtd/Basic.lean` | ✅ **Contribute** to mathlib's Zsqrtd | 🔴 **PR to Zsqrtd** |
| `ofMathlib_toMathlib` | 118-120 | `NumberTheory/Zsqrtd/Basic.lean` | ✅ **Contribute** to mathlib's Zsqrtd | 🔴 **PR to Zsqrtd** |
| `equivMathlib` | 122-134 | `NumberTheory/Zsqrtd/Basic.lean` | ✅ **Contribute** to mathlib's Zsqrtd | 🔴 **PR to Zsqrtd** |
| `toPair` | 135-136 | Delete (trivial) | - | ⚪ Delete |
| `fromPair` | 138-139 | Delete (trivial) | - | ⚪ Delete |
| `halfInt` | 141-143 | `NumberTheory/QuadraticField/HalfInt.lean` | ❌ Specific | 🟢 Move |
| `halfInt_mem_range_toQsqrtdHom_iff_even_even` | 145-165 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |
| `zsqrtdCarrierInQ` | 169-171 | `NumberTheory/QuadraticField/Zsqrtd.lean` | ❌ Specific | 🟢 Keep |

#### Critical Design Decision

**Question:** Should we contribute `QuadraticAlgebra ℤ d 0` ↔ mathlib `Zsqrtd d` equivalence to mathlib?

**Option A: Contribute to mathlib's `NumberTheory/Zsqrtd/Basic.lean`**
```lean
-- In mathlib's Zsqrtd/Basic.lean
namespace Zsqrtd

/-- Equivalence between QuadraticAlgebra model and Zsqrtd. -/
def equivQuadraticAlgebra (d : ℤ) : Zsqrtd d ≃+* QuadraticAlgebra ℤ d 0 where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := by -- proof
  map_add' := by -- proof

end Zsqrtd
```

**Pros:**
- Makes mathlib's `Zsqrtd` compatible with `QuadraticAlgebra`
- Benefits all users of `Zsqrtd`
- Cleaner architecture

**Cons:**
- Requires mathlib review
- May need to wait for PR merge

**Option B: Keep in QuadraticNumberFields project**
```lean
-- In our project only
def Zsqrtd.equivMathlib (d : ℤ) : QuadraticAlgebra ℤ d 0 ≃+* Zsqrtd d
```

**Pros:**
- No dependency on mathlib review
- Faster iteration

**Cons:**
- Duplication
- Doesn't benefit mathlib users

**Recommendation:** **Option A** - Contribute to mathlib, but **after PR 1 merges**.

**Action Items:**
1. PR 3A (mini-PR): Add `Zsqrtd.equivQuadraticAlgebra` to mathlib
2. PR 3B (main): QuadraticField infrastructure

---

### 3. ZsqrtdMathlibInstances.lean (88 lines)

#### Type: Mathlib Compatibility Layer

**Location:** `Mathlib/NumberTheory/Zsqrtd/Instances.lean` (new file)

| Item | Lines | Target Location | Generalization | Action |
|------|-------|-----------------|----------------|--------|
| `instNoZeroDivisors` | 33-42 | `NumberTheory/Zsqrtd/Instances.lean` | ❌ Specific to Zsqrtd | 🔴 **PR to Zsqrtd** |
| `instIsDomain` | 44-45 | `NumberTheory/Zsqrtd/Instances.lean` | ❌ Specific to Zsqrtd | 🔴 **PR to Zsqrtd** |
| `isDedekindDomain_of_mod_four_ne_one` | 51-57 | `NumberTheory/QuadraticField/RingOfIntegers.lean` | ❌ Project-specific | 🟢 Keep in project |
| `instIsDedekindDomain_*` | 58-61 | `NumberTheory/QuadraticField/RingOfIntegers.lean` | ❌ Project-specific | 🟢 Keep in project |
| `not_isDedekindDomain_of_mod_four_eq_one` | 64-74 | `NumberTheory/QuadraticField/RingOfIntegers.lean` | ❌ Project-specific | 🟢 Keep in project |
| `isDedekindDomain_iff_mod_four_ne_one` | 78-84 | `NumberTheory/QuadraticField/RingOfIntegers.lean` | ❌ Project-specific | 🟢 Keep in project |

**Split Strategy:**

```
PR 3A (to mathlib):
├── Zsqrtd/Instances.lean
│   ├── instNoZeroDivisors (for d < 0)
│   └── instIsDomain (for d < 0)

PR 3B (to mathlib QuadraticField):
└── QuadraticField/RingOfIntegers.lean
    ├── isDedekindDomain_of_mod_four_ne_one
    ├── not_isDedekindDomain_of_mod_four_eq_one
    └── isDedekindDomain_iff_mod_four_ne_one
```

**Why split?**
- `NoZeroDivisors`/`IsDomain` are general properties of `Zsqrtd`
- Dedekind domain classification is specific to quadratic field theory

---

### 4. HalfInt.lean (61 lines)

#### Type: Quadratic Field Specific

**Location:** `Mathlib/NumberTheory/QuadraticField/HalfInt.lean`

| Item | Lines | Target Location | Generalization | Action |
|------|-------|-----------------|----------------|--------|
| `halfInt` | 31-33 | `QuadraticField/HalfInt.lean` | ❌ Specific | 🟢 Keep |
| `omegaHalf` | 35-36 | `QuadraticField/HalfInt.lean` | ❌ Specific | 🟢 Keep |
| `halfInt_re/im` | 38-48 | `QuadraticField/HalfInt.lean` | ❌ Specific | 🟢 Keep |
| `trace_halfInt` | 50-52 | `QuadraticField/HalfInt.lean` | ❌ Specific | 🟢 Keep |
| `norm_halfInt` | 54-58 | `QuadraticField/HalfInt.lean` | ❌ Specific | 🟢 Keep |

**Analysis:** All items are quadratic field-specific. No generalization opportunities.

---

### 5. ZOnePlusSqrtOverTwo.lean (141 lines)

#### Type: Quadratic Field Specific

**Location:** `Mathlib/NumberTheory/QuadraticField/ZOnePlusSqrtOverTwo.lean`

| Item | Lines | Target Location | Generalization | Action |
|------|-------|-----------------|----------------|--------|
| `d_of_k` | 33-34 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `omega` | 36-37 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `Zomega` | 39-41 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `omega_mem_Zomega` | 43-44 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `ZOnePlusSqrtOverTwo` | 51 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `qParam` | 55-56 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdFun` | 58-60 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdHom` | 62-77 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdHom_apply` | 79-80 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `toQsqrtdHom_injective` | 82-95 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `carrierSet` | 97-98 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `halfInt_mem_carrierSet_iff_same_parity` | 102-121 | `QuadraticField/ZOnePlusSqrtOverTwo.lean` | ❌ Specific | 🟢 Keep |
| `halfInt_mem_carrierSet_iff_same_parity_set` | 136-139 | Delete (duplicate) | - | ⚪ Delete |

**Analysis:** All items are quadratic field-specific. No generalization opportunities.

---

## Summary: Generalization Opportunities

### 🔴 HIGH PRIORITY - Move to mathlib core

1. **`Int.sq_emod_four_of_even/odd`** → `Data/Int/Parity.lean`
   - Check if exists first
   - If not, small separate PR

2. **`Int.exists_div_add_of_mod_eq`** → `Data/Int/Basic.lean`
   - General version of `exists_k_of_mod_four_eq_one`
   - Small separate PR or part of general Int cleanup

### 🟡 MEDIUM PRIORITY - Contribute to mathlib Zsqrtd

3. **`Zsqrtd.equivQuadraticAlgebra`** → `NumberTheory/Zsqrtd/Basic.lean`
   - Bridge between QuadraticAlgebra and Zsqrtd
   - Separate mini-PR (PR 3A)

4. **`Zsqrtd.instNoZeroDivisors/IsDomain`** → `NumberTheory/Zsqrtd/Instances.lean`
   - General instances for negative d
   - Part of PR 3A or separate

### 🟢 LOW PRIORITY - Keep in QuadraticField

5. **All ModFour specific criteria** → `NumberTheory/QuadraticField/ModFour.lean`
6. **Half-integer infrastructure** → `NumberTheory/QuadraticField/HalfInt.lean`
7. **ZOnePlusSqrtOverTwo** → `NumberTheory/QuadraticField/ZOnePlusSqrtOverTwo.lean`

---

## Proposed PR Structure

### PR 3A: Zsqrtd Infrastructure (Small, Fast-Track)

**Target:** `NumberTheory/Zsqrtd/`

**Files:**
- `Basic.lean` — Add `equivQuadraticAlgebra`
- `Instances.lean` (new) — Add `NoZeroDivisors`, `IsDomain`

**Size:** ~50 lines
**Review Risk:** Low
**Dependencies:** None (standalone)

### PR 3B: QuadraticField Ring Models (Main PR)

**Target:** `NumberTheory/QuadraticField/`

**Files:**
- `ModFour.lean` — Mod-4 arithmetic (keep specific lemmas)
- `Zsqrtd.lean` (new) — QuadraticAlgebra model, Q(√d) embedding
- `HalfInt.lean` (new) — Half-integer representatives
- `ZOnePlusSqrtOverTwo.lean` (new) — ℤ[(1+√d)/2] model

**Size:** ~500 lines
**Review Risk:** Medium
**Dependencies:** PR 1, PR 2, (PR 3A helps but not required)

---

## Next Steps

### Immediate Actions

1. ✅ **Search mathlib** for existing `Int.sq_*_mod_four` lemmas
2. ✅ **Search mathlib** for `Int.exists_div_add_of_mod_eq` or similar
3. ✅ **Decide** on PR 3A vs PR 3B strategy

### Before Submitting PR 3A

- [ ] Verify `Zsqrtd.equivQuadraticAlgebra` doesn't exist in mathlib
- [ ] Test instances with `lake build`
- [ ] Write docstrings following mathlib format
- [ ] Add `#lint` checks

### Before Submitting PR 3B

- [ ] Wait for PR 1 to merge
- [ ] Remove/inline trivial lemmas (`mod_four_branch_split`, `toPair/fromPair`)
- [ ] Verify all dependencies available
- [ ] Add comprehensive module docstrings
- [ ] Run `#lint` on all files

---

## Code Examples: Generalizations

### Example 1: Int.sq_emod_four_of_even

**Before (ModFour.lean):**
```lean
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega
```

**After (Data/Int/Parity.lean):**
```lean
/-- The square of an even integer is divisible by 4. -/
lemma Int.sq_mod_four_eq_zero_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega
```

**Usage in ModFour.lean:**
```lean
-- Replace Int.sq_emod_four_of_even with Int.sq_mod_four_eq_zero_of_even
-- (or create local alias if names differ)
```

### Example 2: Int.exists_div_add_of_mod_eq

**Proposed for Data/Int/Basic.lean:**
```lean
/-- Any integer can be written as `r + m * k` when `n % m = r`. -/
theorem Int.exists_div_add_of_mod_eq {n m r : ℤ} (h : n % m = r) (hm : m ≠ 0) :
    ∃ k : ℤ, n = r + m * k :=
  ⟨n / m, by omega⟩

/-- Special case for `n % m = r`. -/
theorem Int.mod_eq_iff_exists_div_add {n m r : ℤ} (hm : m ≠ 0) :
    n % m = r ↔ ∃ k : ℤ, n = r + m * k :=
  ⟨Int.exists_div_add_of_mod_eq · hm, fun ⟨k, hk⟩ => by omega⟩
```

**Usage in ModFour.lean:**
```lean
-- Before
theorem exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k := by
  refine ⟨d / 4, ?_⟩
  omega

-- After
theorem exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k :=
  Int.exists_div_add_of_mod_eq hd4 (by norm_num)
```

---

## Questions for mathlib Reviewers

1. **Naming:** Is `Zsqrtd.equivQuadraticAlgebra` the right name, or should it be `Zsqrtd.toQuadraticAlgebraEquiv`?

2. **Location:** Should `Int.sq_mod_four_eq_zero_of_even` go in `Data/Int/Parity.lean` or `Data/Int/Modeq.lean`?

3. **Scoping:** Should we create `NumberTheory/QuadraticField/RingOfIntegers/` subdirectory, or keep flat structure?

4. **Dependencies:** Can we assume PR 1 is merged before PR 3B, or should we make PR 3B self-contained?

---

## Tracking

- [ ] Search for existing lemmas in mathlib
- [ ] Decide PR 3A vs 3B strategy
- [ ] Draft PR 3A (if chosen)
- [ ] Draft PR 3B
- [ ] Address review feedback
- [ ] Merge
