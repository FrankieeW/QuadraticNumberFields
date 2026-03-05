---
layout: default
title: API Documentation
---

# API Documentation

## Core Definitions

### `QuadraticNumberFields`

The main type representing the quadratic field $\mathbb{Q}(\sqrt{d})$.

```lean
def QuadraticNumberFields (d : ℤ) := Qsqrtd d
```

### `QuadFieldParam`

Parameters for quadratic fields: square-free integers not equal to 1.

```lean
class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_one : d ≠ 1
```

### `Qsqrtd`

Abbreviation for `QuadraticAlgebra ℚ d 0`, representing elements $a + b\sqrt{d}$.

```lean
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0
```

## Ring of Integers

### `Zsqrtd`

The ring $\mathbb{Z}[\sqrt{d}] = \{a + b\sqrt{d} : a, b \in \mathbb{Z}\}$.

### `ZOnePlusSqrtOverTwo`

The ring $\mathbb{Z}[\omega]$ where $\omega = \frac{1 + \sqrt{1+4k}}{2}$.

## Main Theorems

### Classification

```lean
theorem ringOfIntegers_classification (d : ℤ) [QuadFieldParam d] :
    (d % 4 ≠ 1 ∧ Nonempty (𝓞 (QuadraticNumberFields d) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadraticNumberFields d) ≃+* ZOnePlusSqrtOverTwo k))
```

The complete classification of rings of integers for quadratic fields.

### Case 1: $d \not\equiv 1 \pmod{4}$

```lean
theorem ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one
    (d : ℤ) [QuadFieldParam d] (hd4 : d % 4 ≠ 1) :
    Nonempty (𝓞 (QuadraticNumberFields d) ≃+* Zsqrtd d)
```

### Case 2: $d \equiv 1 \pmod{4}$

```lean
theorem ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    (d : ℤ) [QuadFieldParam d] (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadraticNumberFields d) ≃+* ZOnePlusSqrtOverTwo k)
```

## Norm Properties

### Multiplicativity

```lean
theorem norm_mul (d : ℚ) (x y : Qsqrtd d) :
    Qsqrtd.norm (x * y) = Qsqrtd.norm x * Qsqrtd.norm y
```

### Norm Formula for $\mathbb{Z}[\sqrt{d}]$

```lean
theorem norm_zsqrtd (d : ℤ) (z : Zsqrtd d) :
    Zsqrtd.norm z = z.re ^ 2 - d * z.im ^ 2
```

### Norm Formula for $\mathbb{Z}[\omega]$

```lean
theorem norm_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    QuadraticAlgebra.norm z = z.re ^ 2 + z.re * z.im - k * z.im ^ 2
```

## Unit Criterion

### For $\mathbb{Z}[\sqrt{d}]$

```lean
theorem isUnit_zsqrtd_iff_norm_eq_one_or_neg_one (d : ℤ) (z : Zsqrtd d) :
    IsUnit z ↔ Zsqrtd.norm z = 1 ∨ Zsqrtd.norm z = -1
```

### For $\mathbb{Z}[\omega]$

```lean
theorem isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one
    (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1
```

## File Structure

| File | Contents |
|------|----------|
| `Basic.lean` | Core definitions (`Qsqrtd`, trace, norm) |
| `Def.lean` | Main `QuadraticNumberFields` definition |
| `Param.lean` | `QuadFieldParam` class and instances |
| `ParamUniqueness.lean` | Uniqueness proofs |
| `FieldInstance.lean` | Field typeclass instances |
| `Rescale.lean` | Rescaling operations |
| `RingOfIntegers/Classification.lean` | Main classification theorem |
| `RingOfIntegers/Integrality.lean` | Integrality proofs |
| `RingOfIntegers/Norm.lean` | Norm properties and unit criterion |
| `RingOfIntegers/Zsqrtd.lean` | $\mathbb{Z}[\sqrt{d}]$ definitions |
| `RingOfIntegers/ZOnePlusSqrtOverTwo.lean` | $\mathbb{Z}[\omega]$ definitions |
| `Euclidean/Basic.lean` | Euclidean domain structure |
| `Examples/ZsqrtdNeg5/Basic.lean` | `NoZeroDivisors`/`IsDomain` instances for $\mathbb{Z}[\sqrt{d}]$ when $d < 0$ |
| `Examples/ZsqrtdNeg5/Ideals.lean` | Ideal factorizations in $\mathbb{Z}[\sqrt{-5}]$: $(2)=\mathfrak{p}_2^2$, $(3)=\mathfrak{p}_{3,1}\cdot\mathfrak{p}_{3,2}$, $(1\pm\sqrt{-5})=\mathfrak{p}_2\cdot\mathfrak{p}_{3,i}$; primality and membership criteria |
| `Examples/ZsqrtdNeg5/RamificationInertia.lean` | Ramification indices $e(\mathfrak{p}_2\mid 2)=2$, $e(\mathfrak{p}_{3,i}\mid 3)=1$; inertia degrees $f=1$; quotient ring isomorphisms; $efg=2$ verification |

## See Also

- [Mathematical Background](math.html) - Theory and mathematical context
- [Formalization Details](formalization.html) - Design decisions and implementation
- [Getting Started](getting-started.html) - How to use this formalization

[← Back to Home](index.html)
