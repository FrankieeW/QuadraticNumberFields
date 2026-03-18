# 二次域分裂理论的两条形式化路线：技术报告

本文总结 `QuadraticNumberFields/Splitting/Defs.lean` 当前设计中两条不同的形式化路线，并比较它们在数学语义、Lean 假设、API 形状和项目适配度上的差别。

结论先行：

- 若目标是 `Qsqrtd`、二次域、以及后续数论判据（Legendre 符号、判别式、`p = 2` 的分类），那么以全局 `e(p), f(p), g(p)` 为核心的 Galois 路线已经足够，而且更适合作为主线。
- 若目标是做更一般的 mathlib 风格 API，或尽量少用 Galois/可分假设，则应保留局部 `e(p, P), f(p, P)` 的一般路线，作为定义层和桥接层。
- 最合理的组织不是二选一，而是“General 作底层，Gal 作用户层”。

## 1. 背景

对二次扩张，素数分裂的三种情形可以统一写成三元组：

```text
(e, f, g) = (1, 1, 2)  split
(e, f, g) = (1, 2, 1)  inert
(e, f, g) = (2, 1, 1)  ramified
```

问题不在数学内容，而在于：Lean 里究竟应当把 `split / inert / ramified` 定义成哪一层的对象。

目前可以区分两条路线：

1. 一般局部路线：以某个上方素理想 `P` 的 `e(p, P), f(p, P)` 为原始对象。
2. Galois 全局路线：在 Galois 情形下直接使用不依赖 `P` 的 `e(p), f(p), g(p)`。

## 2. 路线 A：一般局部路线

### 2.1 核心对象

这条路线以局部数据为原始定义：

```text
e(p, P) := ramificationIdx (algebraMap R S) p P
f(p, P) := inertiaDeg p P
```

在这个层面上，`split / inert / ramified` 都直接通过上方素理想来描述。

当前文件中的一般定义对应为：

- `Ideal.IsCompletelySplitIn`
- `Ideal.IsInertInGeneral`
- `Ideal.IsRamifiedInGeneral`

其特点是：

- 数学语义最原始。
- 不需要先假设所有上方素理想上的 `e`、`f` 相同。
- 可以直接对接 `Ideal.sum_ramification_inertia`。

### 2.2 优点

- 假设最少。基础恒等式 `sum_ramification_inertia` 本身不需要 Galois。
- 定义最贴近教材和 mathlib 现有 API。
- 对以后抽取到 mathlib 更自然，因为它不把“Galois 下的均匀性”硬编码进定义。
- 对非 Galois 扩张也有效，因此适用范围最大。

### 2.3 缺点

- 用户层 statement 不够简洁，常常要写 `∀ P ∈ primesOver p S, ...` 或 `∃ P ∈ primesOver p S, ...`。
- 对二次三分法来说，表达方式不够贴合最终目标。你真正想写的是 `(e,f,g) = ...`，而不是每次重新枚举 `P`。
- 很多后续数论叙述，如“分裂等价于 `e=1,f=1,g=2`”，在这一层都要额外包装。

### 2.4 适合的使用场景

- 做底层定义。
- 做一般 Dedekind 扩张的 statement。
- 做将来可能送入 mathlib 的通用 API。
- 当你想完全避免使用 Galois 或可分假设时，这条路线最稳。

## 3. 路线 B：Galois 全局路线

### 3.1 核心对象

这条路线直接把 Galois 情形下的公共值当作原始对象：

```text
e(p) := ramificationIdxIn p S
f(p) := inertiaDegIn p S
g(p) := (primesOver p S).ncard
```

然后把分裂类型定义成全局条件：

- `IsSplitIn := e(p) = 1 ∧ f(p) = 1`
- `IsInertIn := g(p) = 1 ∧ e(p) = 1`
- `IsRamifiedIn := 1 < e(p)`

这是当前 `GalDefs` 的方向。

### 3.2 优点

- 完全贴合二次域的最终分类语言。
- 后续 theorem 的 statement 更短，更接近数论直觉。
- 与 `efg_trichotomy`、Legendre 符号判据、判别式判据天然兼容。
- 对 `Qsqrtd` 这种本质上就是二次 Galois 语境的对象，工程效率更高。

### 3.3 缺点

- `e(p), f(p)` 只有在 Galois 语境下才真正有“与 `P` 无关”的数学内容。
- 一旦坚持用这套全局语言，就必须额外处理分式域层面的 Galois/可分问题。
- 因为 `ramificationIdxIn` 与 `inertiaDegIn` 的定义是通过“任选一个上方素理想”实现的，所以若没有 Galois 统一性，定义虽然可写，语义却不应当被当作 primitive API。

### 3.4 适合的使用场景

- 二次扩张。
- `Qsqrtd` 与素数分裂判据。
- 以 `e,f,g` 三元组作为主要用户接口的文件。
- 需要和后续数论叙述保持一致的部分。

## 4. 两条路线的关键数学差异

### 4.1 一般路线只依赖基本分解理论

一般路线的主工具是：

- `Ideal.sum_ramification_inertia`

它直接给出

```text
∑_P e(p, P) f(p, P) = [Frac(S) : Frac(R)]
```

这条恒等式本身不要求 Galois，也不要求把所有 `P` 上的数据压缩成一个全局值。

### 4.2 全局路线额外依赖均匀性

全局路线要把所有 `P` 上的数据压成一个 `e(p)` 和一个 `f(p)`，需要：

- Galois 群对 `primesOver p S` 的传递作用；
- `ramificationIdx_eq_of_isGaloisGroup`；
- `inertiaDeg_eq_of_isGaloisGroup`。

这是它和一般路线最本质的分界。

### 4.3 当前 `sorry` 争议反映的正是这点

在 `efg_trichotomy` 中，若坚持走全局 `e(p), f(p), g(p)`，就需要把分式域扩张放到 Galois 框架中。

这带来两个额外技术问题：

1. `R ⊆ S` 为 quadratic，如何推出 `Frac(R) ⊆ Frac(S)` 也是 quadratic。
2. 如何推出 `Frac(R) ⊆ Frac(S)` 可分，从而得到 Galois。

第一个问题是一个 mathlib 风格的缺失 bridge lemma，目前已实现为：

- `Algebra.IsQuadraticExtension.fractionRing`

第二个问题不是“自动成立”，因为特征 `2` 下存在纯不可分二次扩张。当前已实现两个可用 bridge：

- `Algebra.IsQuadraticExtension.isSeparable_fractionRing`
  需要 `PerfectField K`
- `Algebra.IsQuadraticExtension.isSeparable_of_char_ne_two`
  需要 `ringChar K ≠ 2`

这说明：全局路线的代价不是 `CharZero` 本身，而是“必须控制可分性”。

## 5. 对 `Qsqrtd` 项目的实际影响

### 5.1 为什么对 `Qsqrtd` 来说，全局路线是够用的

本项目的最终目标不是一般 Dedekind 扩张，而是二次数域上的分裂分类。此时：

- 扩张次数固定为 `2`。
- 最终 statement 本来就要写成 split / inert / ramified 三分。
- 后续主定理要和 Legendre 符号、判别式、`p = 2` 的特殊分类连接。

这些内容天然都使用 `(e,f,g) = (1,1,2), (1,2,1), (2,1,1)` 的语言，而不是“对每个 `P` 如何如何”的语言。

因此在 `Qsqrtd` 主线里，Galois 全局路线并不是“偷懒”，而是与最终数论目标对齐的接口设计。

### 5.2 为什么一般路线仍然值得保留

尽管如此，一般路线仍然有三个重要价值：

1. 它提供数学上最原始的定义层。
2. 它让 `GalDefs` 可以通过 `iff` 明确地回连到一般定义。
3. 它保留了将来向更一般扩张推广的可能性。

因此，一般路线最适合作为基础层，而不是被删掉。

## 6. 推荐的架构

推荐采用三层结构：

### 第一层：GeneralDefs

使用局部记号 `e(p, P), f(p, P)`，给出最原始定义：

- `IsCompletelySplitIn`
- `IsInertInGeneral`
- `IsRamifiedInGeneral`

这是“数学定义层”。

### 第二层：GalDefs

使用全局记号 `e(p), f(p), g(p)`，给出用户更容易使用的定义：

- `IsSplitIn`
- `IsInertIn`
- `IsRamifiedIn`

再通过 bridge lemma 证明：

- `IsRamifiedIn ↔ IsRamifiedInGeneral`
- `IsInertIn ↔ IsInertInGeneral`
- `IsSplitIn ↔ IsCompletelySplitIn`

这是“接口层”。

### 第三层：Quadratic / Qsqrtd applications

在二次扩张、特别是 `Qsqrtd` 的实际定理中，直接使用全局 `e(p), f(p), g(p)`。

原因是：

- statement 最短；
- 与数论判据最一致；
- 可以直接服务于 Legendre、判别式、`p = 2` 分类。

这是“应用层”。

## 7. 两条路线的优劣对照表

| 维度 | 一般局部路线 | Galois 全局路线 |
|---|---|---|
| 原始数学语义 | 最强 | 次一级，需要解释其 Galois 含义 |
| 假设强度 | 最弱 | 更强，需要 Galois/可分控制 |
| Lean 中的 statement 简洁性 | 较差 | 最好 |
| 与 `efg_trichotomy` 的贴合度 | 一般 | 极高 |
| 与 `Qsqrtd` 后续数论判据的贴合度 | 一般 | 极高 |
| 向一般 mathlib API 推广 | 最好 | 较弱 |
| 项目当前工程效率 | 中等 | 最好 |

## 8. 最终建议

对于本项目，最合理的决策是：

- 保留一般路线作为定义层和桥接层；
- 把 Galois 全局路线作为 `Qsqrtd` 主线的用户接口；
- 在真正的二次域分类定理中优先使用全局 `e(p), f(p), g(p)`。

换句话说：

- 若问“哪条路线更数学本源”，答案是一般局部路线。
- 若问“哪条路线更适合这个项目最终目标”，答案是 Galois 全局路线。

这两者并不冲突。最好的做法不是在两条路线中删掉一条，而是让前者做基础、后者做主接口。

## 9. 对后续开发的直接建议

对 `Qsqrtd` 主线，可按以下原则推进：

1. `Defs.lean` 继续保持双层结构。
2. `efg_trichotomy` 优先沿全局 `e,f,g` 语言完成。
3. 若需要最弱假设版本，再另外保留一般局部版本，不强行把两者合并成一个 theorem。
4. 对数论文件，如 `Classification.lean` 与 `Discriminant.lean`，优先让 statement 直接落在 split / inert / ramified 上，而不是暴露局部 `P`。

这会让整个 `Splitting/` 子目录形成清晰分工：

- `GeneralDefs`: 基础语义
- `GalDefs`: 项目主接口
- `Quadratic/Qsqrtd theorems`: 最终用户结果
