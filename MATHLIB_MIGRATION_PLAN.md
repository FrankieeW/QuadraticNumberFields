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

`Qsqrtd` 类型与基本操作:
- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0` — `ℚ(√d)` 的类型别名
- `Qsqrtd.trace`, `Qsqrtd.norm`, `Qsqrtd.embed` 及其 simp lemmas

`QuadFieldParam` 参数类型类:
- `QuadFieldParam (d : ℤ)`: 包含 `squarefree : Squarefree d` 和 `ne_one : d ≠ 1`
- 构造器: `of_squarefree_ne_one`, `of_prime`, `of_natAbs_prime`
- `d = -1`, `d = -3` 的实例
- 退化情况: `zero_not_isReduced`, `one_not_isField`

`QuadraticNumberFields` 及代数实例:
- `QuadraticNumberFields (d : ℤ) [QuadFieldParam d] := Qsqrtd (d : ℚ)`
- `Field`, `NumberField`, `IsQuadraticExtension` instances
- Module diamond resolution

**Migration notes:**
- 需要在 Zulip 讨论 `QuadFieldParam` 的设计: typeclass vs. 分开的假设
- `trace`/`norm` 是否应该使用 mathlib 的 `Algebra.trace`/`Algebra.norm` 并证明兼容性
- Module diamond 的解决方案需要仔细审查

**Review risk:** Medium — design discussion expected.

---

### PR 2 — Structure Theory: Rescale, Uniqueness, and Places

**Source files:** `Rescale.lean`, `ParamUniqueness.lean`, `TotallyRealComplex.lean`
**Depends on:** PR 1
**Size:** ~300 lines

**Content:**

Rescaling:
- `rescale d a ha`: algebra isomorphism `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))`
- `Qsqrtd_iso_int_param`, `Qsqrtd_iso_squarefree_int_param`: 正规化结果

参数唯一性:
- `QuadFieldParam.unique`: `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` + 两边 squarefree ⟹ `d₁ = d₂`
- `squarefree_eq_of_rat_sq_mul`: `d₁ = d₂ · r²` + 两边 squarefree ⟹ `d₁ = d₂`

无穷素位:
- `isTotallyReal`: `d > 0` 时 `ℚ(√d)` totally real
- `isTotallyComplex`: `d < 0` 时 `ℚ(√d)` totally complex
- `isCMField`: `d < 0` 时 `ℚ(√d)` 是 CM field

**Migration notes:**
- `TotallyRealComplex.lean` 使用 `attribute [-instance] DivisionRing.toRatAlgebra`
  来解决 diamond — 需要检查最新 mathlib 是否已修复
- Rescale 和 ParamUniqueness 是独立的, 可以并行审查

**Review risk:** Medium — instance management.

---

### PR 3 — Ring of Integers: Models and Mod-4 Infrastructure

**Source files:** `RingOfIntegers/ModFour.lean`, `RingOfIntegers/Zsqrtd.lean`,
`RingOfIntegers/ZsqrtdMathlibInstances.lean`, `RingOfIntegers/HalfInt.lean`,
`RingOfIntegers/ZOnePlusSqrtOverTwo.lean`
**Depends on:** PR 1
**Size:** ~550 lines

**Content:**

Mod-4 算术:
- `squarefree_int_emod_four`: squarefree 整数模 4 余数属于 `{1, 2, 3}`
- `dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one`: 主判据
  `4 ∣ (a'² - d·b'²) ↔ (2∣a' ∧ 2∣b') ∨ (both odd ∧ d ≡ 1 mod 4)`
- `exists_k_of_mod_four_eq_one`: `d % 4 = 1 ↔ ∃ k, d = 1 + 4k`

`ℤ[√d]` 作为 QuadraticAlgebra:
- `Zsqrtd d := QuadraticAlgebra ℤ d 0`
- `equivMathlib`: 与 mathlib `ℤ√d` 的 ring equivalence
- `toQsqrtdHom`: embedding into `ℚ(√d)` + injectivity
- `NoZeroDivisors`, `IsDomain` instances (for `d < 0`)
- `halfInt_mem_range_toQsqrtdHom_iff_even_even`

Half-integer 与 `ℤ[(1+√d)/2]`:
- `halfInt d a' b'`: `(a' + b'√d) / 2`
- `ZOnePlusSqrtOverTwo k := QuadraticAlgebra ℤ k 1` (因为 `ω² = ω + k`)
- `toQsqrtdHom` + injectivity
- `halfInt_mem_carrierSet_iff_same_parity`

**Migration notes:**
- **关键设计决策:** 保留自己的 `Zsqrtd` (作为 `QuadraticAlgebra ℤ d 0`) 还是直接
  扩展 mathlib 的 `ℤ√d`? 建议: `NoZeroDivisors`/`IsDomain` 直接贡献给
  `Mathlib.NumberTheory.Zsqrtd.Basic`, `QuadraticAlgebra` equivalence 作为兼容层
- 部分 mod-4 引理 (e.g. `Int.sq_emod_four_of_even`) 可能已经存在或应放在
  `Mathlib.Data.Int.Parity`
- `ZOnePlusSqrtOverTwo` 使用 `QuadraticAlgebra ℤ k 1` 的参数化需要清楚文档化

**Review risk:** High — largest PR, `Zsqrtd` duplication discussion.

---

### PR 4 — Ring of Integers: Classification Theorem

**Source files:** `RingOfIntegers/Integrality.lean`, `RingOfIntegers/Classification.lean`,
`RingOfIntegers/Norm.lean`, `RingOfIntegers/ZsqrtdIdeals.lean`
**Depends on:** PR 2 (ParamUniqueness), PR 3
**Size:** ~800 lines

**Content:**

Integrality 判据:
- `exists_halfInt_with_div_four_of_isIntegral`: 每个整元都有形式
  `(a' + b'√d)/2` 且 `4 ∣ (a'² - d·b'²)` (~250 行证明)
- `exists_zsqrtd_of_isIntegral_of_ne_one_mod_four`: `d % 4 ≠ 1` 的前向方向
- `exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four`: `d % 4 = 1` 的前向方向
- `isIntegral_toQsqrtd`, `isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo`: 反向方向

**Main Classification Theorem:**
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`:
  `d % 4 ≠ 1 → 𝓞(ℚ(√d)) ≃+* ℤ[√d]`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`:
  `d % 4 = 1 → 𝓞(ℚ(√d)) ≃+* ℤ[(1+√d)/2]`
- `ringOfIntegers_classification`: 合并版本
- 具体例子: Gaussian integers (`d = -1`), Eisenstein integers (`d = -3`)

Norm 计算:
- `norm_mul`, `norm_zsqrtd`, `norm_zOnePlusSqrtOverTwo`: 显式公式
- `isUnit_zsqrtd_iff_norm_eq_one_or_neg_one`: `ℤ[√d]` 的 unit 判据
- `isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one`: `ℤ[(1+√d)/2]` 的 unit 判据

Ideal 理论 (一般框架, 任意 squarefree `d`, prime `p ∣ (d-1)`):
- `liftModP`, `liftModPNeg`: ring homs `ℤ[√d] →+* ZMod p`
- `quotEquivZModP`, `quotEquivZModPNeg`: quotient ring equivalences
- `isPrime_span_p_one_minus_sqrtd`, `isPrime_span_p_one_plus_sqrtd`: primality

**Migration notes:**
- `Integrality.lean` 是最复杂的文件, 审查者可能要求简化
- **必须先修复** `Norm.lean` 中 `norm_mem_ringOfIntegers` 的 `sorry`
- 这是项目的核心定理
- `ZsqrtdIdeals.lean` 与 Classification 无依赖, 但放在同一 PR 以减少 PR 数量

**Pre-work required:**
- [ ] Fix `sorry` in `norm_mem_ringOfIntegers`

**Review risk:** High — main theorem, large proof.

---

## Excluded from Migration

| File | Reason |
|---|---|
| `Euclidean/Basic.lean` | 骨架文件, 所有证明都是 `sorry` — 留待将来完成 |
| `Examples/ZsqrtdNeg5/` | 具体例子 (`ℤ[√-5]` 分解/ramification), 适合留在外部项目或后续提交到 `Mathlib.Archive` |
| `Verso/` | 文档生成工具, 非数学内容 |
| `site/` | 网站, 与 mathlib 无关 |

---

## Pre-Migration Checklist

- [ ] **Fix `sorry`** in `Norm.lean`: `norm_mem_ringOfIntegers`
- [ ] **Zulip 讨论** — 发帖到 `#mathlib4 > new PR` 或 `#Is there code for X?`
  - 主题: "Quadratic number fields: ring of integers classification"
  - 关键设计问题:
    1. `QuadFieldParam` typeclass vs. 分开的假设?
    2. 自己的 `Zsqrtd` vs. 直接扩展 mathlib 的 `ℤ√d`?
    3. 目标目录 `Mathlib.NumberTheory.QuadraticField` 是否合适?
- [ ] **Bump to latest mathlib** — 确保与 `master` 兼容
- [ ] **Run `#lint`** on all files
- [ ] **Add copyright headers** — `Copyright (c) 2026 Frankie Wang. All rights reserved.`
- [ ] **Add module docstrings** — `/-! ... -/` 包含 `## Main Definitions` / `## Main Theorems`
- [ ] **Remove ANCHOR comments** — mathlib 不需要
- [ ] **Remove `repl` dependency** — mathlib PR 不需要

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
| Phase 1 | PR 1 | Foundation (先开) |
| Phase 2 | PR 2, PR 3 | Structure theory + ring models (并行) |
| Phase 3 | PR 4 | Classification theorem + ideal theory |

每个 PR 预计 2–4 周审查周期, 整体 ~2–3 个月完成迁移。

---

## References

- [Lean Zulip: Z[(1+sqrt(1+4k))/2]](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
- [mathlib contributing guide](https://leanprover-community.github.io/contribute/)
- [mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
