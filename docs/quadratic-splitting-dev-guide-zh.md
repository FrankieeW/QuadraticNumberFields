# 二次域素数分裂开发指南

手动开发 Q(sqrt d) 中素数分裂分类定理的参考文档。

## 目标

证明：对无平方因子 d != 1 和素数 p，

```
legendreSym p d =  1   =>  (p) = P1 * P2,  e=1, f=1, g=2   (分裂)
legendreSym p d = -1   =>  (p) = P,         e=1, f=2, g=1   (惰性)
legendreSym p d =  0   =>  (p) = P^2,       e=2, f=1, g=1   (分歧)
```

以及等价关系：p 分歧 <=> p | disc(Q(sqrt d))。

## 文件结构（已搭建）

```
QuadraticNumberFields/Splitting/
  Defs.lean            -- 第1阶段: IsSplitIn / IsInertIn / IsRamifiedIn + 三分性
  Monogenic.lean       -- 第2阶段: O_K = Z[theta], exponent = 1
  MinpolyMod.lean      -- 第3阶段: X^2 - d mod p 的分解 + Legendre 联系
  Classification.lean  -- 第4阶段: Legendre 符号判据（主定理）
  Discriminant.lean    -- 第5阶段: 分歧 <=> p | disc
```

均在 `QuadraticNumberFields.Splitting` 命名空间下。

## 依赖图

```
                Defs.lean
               (定义 + 三分性)
                    |
          +---------+---------+
          |                   |
    Monogenic.lean      MinpolyMod.lean
    (O_K = Z[theta],    (X^2 - d mod p
     exponent = 1)       的分解)
          |                   |
          +---------+---------+
                    |
            Classification.lean
            (Legendre 符号判据)
                    |
            Discriminant.lean
            (分歧 <=> p | disc)
```

导入链：
- `Defs.lean` — 仅依赖 mathlib（无项目依赖）
- `Monogenic.lean` — `RingOfIntegers/Classification.lean` + mathlib Kummer-Dedekind
- `MinpolyMod.lean` — `Monogenic.lean` + mathlib Legendre 符号
- `Classification.lean` — `Defs.lean` + `Monogenic.lean` + `MinpolyMod.lean`
- `Discriminant.lean` — `Classification.lean` + `RingOfIntegers/Discriminant.lean`

---

## 第1阶段：定义 (`Defs.lean`) — 已完成

### 当前状态

定义编译通过，零错误零警告。

### 已实现

对任意 Dedekind 扩张 R -> S 的通用定义：

```lean
def Ideal.IsSplitIn (p : Ideal R) (S : Type*) ... : Prop :=
  1 < (p.primesOver S).ncard ∧
    ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1

def Ideal.IsInertIn (p : Ideal R) (S : Type*) ... : Prop :=
  (p.primesOver S).ncard = 1 ∧
    ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1

def Ideal.IsRamifiedIn (p : Ideal R) (S : Type*) ... : Prop :=
  ∃ P ∈ p.primesOver S, 1 < ramificationIdx (algebraMap R S) p P
```

### 待完成

- [ ] 互斥性：`IsSplitIn.not_isInert`, `IsSplitIn.not_isRamified`, `IsInertIn.not_isRamified`
- [ ] 度2穷举性：`isSplit_or_isInert_or_isRamified`（用 `sum_ramification_inertia` + Galois 一致性）

### 三分性的证明思路

由 `sum_ramification_inertia`：`∑ eᵢfᵢ = 2`。因为 eᵢ >= 1, fᵢ >= 1，2 的唯一拆分是：
- 1·1 + 1·1 = 2 → g=2, e=1, f=1 → 分裂
- 1·2 = 2 → g=1, e=1, f=2 → 惰性
- 2·1 = 2 → g=1, e=2, f=1 → 分歧

对 Galois 扩张（二次域总是 Galois 的），所有 eᵢ 相等、fᵢ 相等（`ramificationIdx_eq_of_isGalois`, `inertiaDeg_eq_of_isGaloisGroup`），排除混合情况。

### 需要的 mathlib API

| 需要 | mathlib |
|------|---------|
| efg 恒等式 | `Ideal.sum_ramification_inertia` |
| p 上方的素理想 | `Ideal.primesOver`, `primesOverFinset` |
| Galois 一致性 | `ramificationIdx_eq_of_isGalois`, `inertiaDeg_eq_of_isGaloisGroup` |
| efg = \|G\| | `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` |

---

## 第2阶段：单生成性 (`Monogenic.lean`) — 待做

### 目标

建立 `𝓞(ℚ(√d)) = ℤ[θ]`，使 Kummer-Dedekind 定理对所有素数无条件成立。

### 已有资源

来自 `RingOfIntegers/Classification.lean`：
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`: `d % 4 ≠ 1 → 𝓞 ≃+* ℤ[√d]`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`: `d % 4 = 1 → 𝓞 ≃+* ℤ[(1+√d)/2]`

### 需要构建

```lean
-- 𝓞_K 的生成元 θ
noncomputable def ringOfIntegersGenerator (d : ℤ) :
    𝓞 (Qsqrtd (d : ℚ)) := ...

-- θ 生成 𝓞_K（ℤ-代数意义下）
theorem isMonogenic :
    Algebra.adjoin ℤ {ringOfIntegersGenerator d} = ⊤

-- 推论：exponent θ = 1（conductor 平凡）
theorem exponent_eq_one :
    RingOfIntegers.exponent (ringOfIntegersGenerator d) = 1

-- 因此：对所有素数 p，Kummer-Dedekind 无条件适用
theorem not_dvd_exponent (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent (ringOfIntegersGenerator d)
```

### 核心洞察

因为 `𝓞_K = ℤ[θ]` 精确成立（不仅仅是有限指标），conductor 是整个环 `(1) = ℤ[θ]`，
所以 `exponent = 1`，`¬ p ∣ 1` 对任何素数平凡成立。这是二次域相比一般数域的主要优势。

### 提示

- 将环等价包装为 `Algebra.adjoin = ⊤` — 寻找 `Subalgebra.eq_top_of_equiv` 或从 `QuadraticAlgebra.basis` 构建
- `RingOfIntegers.exponent` 通过 conductor 理想定义；若 `ℤ[θ] = 𝓞`，conductor = `⊤`，annihilator = `⊤`，exponent = 1

---

## 第3阶段：最小多项式 mod p (`MinpolyMod.lean`) — 待做

### 目标

显式计算 `minpoly ℤ θ` 并分类其 mod p 的分解行为。

### 最小多项式

```
d % 4 ≠ 1:  θ = √d,          minpoly = X² - d
d % 4 = 1:  θ = (1+√d)/2,    minpoly = X² - X - (d-1)/4
```

### 需要证明的定理

```lean
theorem minpoly_generator_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - C d

theorem minpoly_generator_mod_four_eq_one (hd4 : d % 4 = 1) :
    minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - X - C ((d - 1) / 4)
```

### mod p 分解（奇素数 p, p ∤ d）

对 `X² - d mod p`：

```lean
-- 分裂 ↔ d 是 mod p 的二次剩余
theorem sq_sub_splits_mod_iff (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (map (Int.castRingHom (ZMod p)) (X ^ 2 - C d)).Splits (RingHom.id _)
    ↔ IsSquare ((d : ZMod p) : ZMod p)

-- 不可约 ↔ d 不是 mod p 的二次剩余
theorem sq_sub_irreducible_mod_iff (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    Irreducible (map (Int.castRingHom (ZMod p)) (X ^ 2 - C d))
    ↔ ¬ IsSquare ((d : ZMod p) : ZMod p)

-- 重根 ↔ p ∣ d
theorem sq_sub_double_root_iff :
    ... ↔ (p : ℤ) ∣ d
```

### 与 Legendre 符号的联系

核心桥梁：`IsSquare (d : ZMod p) ↔ legendreSym p d = 1`（来自 `legendreSym.eq_one_iff`）。

| `monicFactorsMod θ p` | 多项式行为 | Legendre 符号 |
|---|---|---|
| 2 个一次因子 | `(X-a)(X+a)`, a ≠ 0 | `legendreSym p d = 1` |
| 1 个二次因子 | 不可约 | `legendreSym p d = -1` |
| 1 个一次因子，重数 2 | `(X-a)²` | `legendreSym p d = 0` |

### mathlib API

| 需要 | mathlib |
|------|---------|
| Legendre 符号 | `legendreSym p d` |
| 二次剩余 ↔ legendreSym = 1 | `legendreSym.eq_one_iff` |
| 非二次剩余 ↔ legendreSym = -1 | `legendreSym.eq_neg_one_iff` |
| 多项式分裂 | `Polynomial.splits_iff_card_roots`，度2引理 |
| `ZMod p` 是域 | `ZMod.instField`（由 `Fact p.Prime` 提供） |

### 特殊情况：p = 2

Legendre 符号要求 p 为奇素数。对 p = 2，用直接分情况讨论：

```
d ≡ 2, 3 mod 4:
  minpoly = X² - d,  mod 2: X² - 1 = (X-1)²  →  分歧

d ≡ 1 mod 8:
  minpoly = X² - X - (d-1)/4,  mod 2: X² - X = X(X-1)  →  分裂

d ≡ 5 mod 8:
  minpoly = X² - X - (d-1)/4,  mod 2: X² + X + 1, 不可约  →  惰性
```

总结：
| d mod 8 | p = 2 的行为 |
|---------|-------------|
| d ≡ 2, 3 mod 4 | 分歧 |
| d ≡ 1 mod 8 | 分裂 |
| d ≡ 5 mod 8 | 惰性 |

---

## 第4阶段：通过 Legendre 符号分类 (`Classification.lean`) — 待做

### 目标

主定理——将所有部件连接起来。

### 需要证明的定理

```lean
-- 奇素数, p ∤ d
theorem isSplit_iff_legendreSym_eq_one (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsSplitIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ legendreSym p d = 1

theorem isInert_iff_legendreSym_eq_neg_one (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsInertIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ legendreSym p d = -1

-- 整除 d 的素数
theorem isRamified_of_dvd (hpd : (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))

-- 统一版本
theorem splitting_classification (p : ℕ) [Fact p.Prime] :
    ((legendreSym p d = 1  ∧ ... IsSplitIn ...) ∨
     (legendreSym p d = -1 ∧ ... IsInertIn ...) ∨
     (legendreSym p d = 0  ∧ ... IsRamifiedIn ...))
```

### 证明链条

```
RingOfIntegers/Classification.lean  (𝓞 = ℤ[θ])
              ↓
Monogenic.lean  (exponent θ = 1)
              ↓
primesOverSpanEquivMonicFactorsMod  (mathlib Kummer-Dedekind)
              ↓
monicFactorsMod θ p = minpoly mod p 的不可约因子
              ↓
MinpolyMod.lean  (X² - d mod p ↔ Legendre)
              ↓
legendreSym p d  (mathlib)
```

### 关键 Kummer-Dedekind API

```lean
-- 核心等价
primesOverSpanEquivMonicFactorsMod (hp : ¬p ∣ exponent θ)
  : (Ideal.span {↑p}).primesOver 𝓞 K ≃ monicFactorsMod θ p

-- 读取 e 和 f
ramificationIdx ... = multiplicity q̄ (minpoly ℤ θ mod p)
inertiaDeg ... = q̄.natDegree
```

翻译为 IsSplit/IsInert/IsRamified：
- `|monicFactorsMod| = 2` → g = 2 → 分裂
- `|monicFactorsMod| = 1`，度为 2 → f = 2 → 惰性
- `|monicFactorsMod| = 1`，重数为 2 → e = 2 → 分歧

---

## 第5阶段：判别式判据 (`Discriminant.lean`) — 待做

### 目标

```lean
theorem isRamified_iff_dvd_disc (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ))
```

### 已有资源

来自 `RingOfIntegers/Discriminant.lean`：
- `discr_of_mod_four_ne_one`: `disc = 4d`（当 `d % 4 ≠ 1`）
- `discr_of_mod_four_eq_one`: `disc = d`（当 `d % 4 = 1`）
- `discr_formula`: 统一版

### 证明策略

**正方向**（分歧 → p ∣ disc）：
```
分歧 → p ∣ d  (由第4阶段 / legendreSym = 0)
     → p ∣ disc  (disc = 4d 或 d；p ∣ d 蕴含 p ∣ 两者)
```

**反方向**（p ∣ disc → 分歧）：
```
p ∣ disc → p ∣ 4d  (d ≢ 1 mod 4 的情况) 或 p ∣ d  (d ≡ 1 mod 4 的情况)
         → p ∣ d   (奇素数 p: gcd(p,4)=1; p=2: d ≢ 1 mod 4 直接意味着分歧)
         → 分歧
```

### 显式刻画

```lean
-- 奇素数
theorem ramified_odd_iff (hp : p ≠ 2) :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn ... ↔ (p : ℤ) ∣ d

-- p = 2
theorem ramified_two_iff :
    (Ideal.span {(2 : ℤ)}).IsRamifiedIn ... ↔ d % 4 ≠ 1
```

---

## 可复用的项目代码

| 文件 | 可复用内容 |
|------|----------|
| `RingOfIntegers/Classification.lean` | `ringOfIntegers_equiv_zsqrtd_*`, `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_*` |
| `RingOfIntegers/Discriminant.lean` | `discr_formula`, `discr_of_mod_four_*` |
| `RingOfIntegers/ZsqrtdIdeals.lean` | `quotEquivZModP`, `quotEquivZModPNeg`, `comap_span_p_*`, `isPrime_span_p_*` |
| `RingOfIntegers/ZsqrtdMathlibInstances.lean` | `IsDedekindDomain` (Zsqrtd 的 Dedekind 整环实例) |
| `Examples/ZsqrtdNeg5/RamificationInertia.lean` | 手动计算 e, f 的模式——可推广 |
| `Instances.lean` | Qsqrtd 的 `NumberField` 实例 |
| `Parameters.lean` | `Fact (Squarefree d)`, `Fact (d ≠ 1)` |

## 关键 mathlib 导入

```lean
-- 分歧/惰性
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois

-- Kummer-Dedekind
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

-- Legendre 符号
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.Basic

-- 上方素理想
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

-- 判别式
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
```

## 难度估计

| 阶段 | 难度 | 备注 |
|------|------|------|
| 1. Defs | 简单 | 定义已完成；三分性 = 2 的拆分的组合论证 |
| 2. Monogenic | 中等 | 将环等价包装为 `Algebra.adjoin = ⊤`，计算 exponent |
| 3. MinpolyMod | 中等 | 多项式 mod p 分解；p=2 分情况讨论 |
| 4. Classification | 中等偏难 | 将 Kummer-Dedekind 等价连接到 IsSplit/IsInert/IsRamified |
| 5. Discriminant | 简单-中等 | 利用已有判别式公式的整除性算术 |

第4阶段最难：需要展开 Kummer-Dedekind 等价，将 `monicFactorsMod` 的基数和度数连接到定义。

## 备选方案：直接法（绕过 Kummer-Dedekind）

如果 Kummer-Dedekind API 难以使用，可以直接证明分裂定理：

1. 显式构造素理想（如 `ZsqrtdIdeals.lean` 中所做的）
2. 手动计算 e, f（如 `Examples/ZsqrtdNeg5/RamificationInertia.lean`）
3. 证明唯一性（它们是 p 上方*仅有的*素理想）

`ZsqrtdIdeals.lean` 的基础设施已经关于 p 和 d 参数化——只需将 `p ∣ (d-1)` 假设推广为处理所有分裂类型。这种方法更手动，但避免了 Kummer-Dedekind 的抽象开销。
