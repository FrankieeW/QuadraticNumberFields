---
layout: default
title: Mathematical Background
---

# Mathematical Background

## Quadratic Number Fields

A **quadratic number field** is an extension of $\mathbb{Q}$ of degree 2. Every such field can be written as $\mathbb{Q}(\sqrt{d})$ for some square-free integer $d \neq 0, 1$.

### Definition

$$\mathbb{Q}(\sqrt{d}) = \{a + b\sqrt{d} : a, b \in \mathbb{Q}\}$$

### Properties

- $\mathbb{Q}(\sqrt{d})$ is a field with addition and multiplication defined naturally
- The dimension $[\mathbb{Q}(\sqrt{d}) : \mathbb{Q}] = 2$
- Elements have the form $a + b\sqrt{d}$ with $a, b \in \mathbb{Q}$

## Ring of Integers

The **ring of integers** $\mathcal{O}_K$ of a number field $K$ consists of all elements of $K$ that are roots of monic polynomials with integer coefficients:

$$\mathcal{O}_K = \{\alpha \in K : \exists \text{ monic } f \in \mathbb{Z}[x], f(\alpha) = 0\}$$

### Classification Theorem

For quadratic fields, the ring of integers has a beautiful classification:

**Theorem:** Let $d$ be a square-free integer.

1. If $d \equiv 2, 3 \pmod{4}$, then $\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}[\sqrt{d}] = \{a + b\sqrt{d} : a, b \in \mathbb{Z}\}$

2. If $d \equiv 1 \pmod{4}$, then $\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}\left[\frac{1 + \sqrt{d}}{2}\right] = \left\{a + b \cdot \frac{1 + \sqrt{d}}{2} : a, b \in \mathbb{Z}\right\}$

### Proof Sketch

An element $\alpha = a + b\sqrt{d} \in \mathbb{Q}(\sqrt{d})$ is integral iff its trace and norm are integers.

- **Trace:** $\text{Tr}(\alpha) = 2a$
- **Norm:** $N(\alpha) = a^2 - db^2$

For $\alpha$ to be integral:
- $2a \in \mathbb{Z}$ and $a^2 - db^2 \in \mathbb{Z}$

The analysis of these conditions leads to the classification.

## Norm

The **norm** of an element $\alpha = a + b\sqrt{d}$ is:

$$N(\alpha) = \alpha \cdot \bar{\alpha} = (a + b\sqrt{d})(a - b\sqrt{d}) = a^2 - db^2$$

### Properties

1. **Multiplicativity:** $N(\alpha\beta) = N(\alpha)N(\beta)$
2. **Unit criterion:** $\alpha \in \mathcal{O}_K^\times \iff N(\alpha) = \pm 1$

### Norm Formulas by Case

| Ring | Element | Norm |
|------|---------|------|
| $\mathbb{Z}[\sqrt{d}]$ | $a + b\sqrt{d}$ | $a^2 - db^2$ |
| $\mathbb{Z}[\omega]$, $\omega = \frac{1+\sqrt{d}}{2}$ | $a + b\omega$ | $a^2 + ab - kb^2$ where $d = 1 + 4k$ |

## Examples

### Example 1: Gaussian Integers ($d = -1$)

- $-1 \equiv 3 \pmod{4}$, so case 1 applies
- $\mathcal{O}_{\mathbb{Q}(i)} = \mathbb{Z}[i] = \{a + bi : a, b \in \mathbb{Z}\}$
- Norm: $N(a + bi) = a^2 + b^2$
- Units: $\pm 1, \pm i$ (elements with norm 1)

### Example 2: Eisenstein Integers ($d = -3$)

- $-3 \equiv 1 \pmod{4}$, so case 2 applies
- Let $\omega = \frac{1 + \sqrt{-3}}{2}$, a primitive cube root of unity
- $\mathcal{O}_{\mathbb{Q}(\sqrt{-3})} = \mathbb{Z}[\omega]$
- Norm: $N(a + b\omega) = a^2 - ab + b^2$
- Units: $\pm 1, \pm \omega, \pm \omega^2$ (6 units)

### Example 3: Real Quadratic Field ($d = 2$)

- $2 \equiv 2 \pmod{4}$, so case 1 applies
- $\mathcal{O}_{\mathbb{Q}(\sqrt{2})} = \mathbb{Z}[\sqrt{2}]$
- Norm: $N(a + b\sqrt{2}) = a^2 - 2b^2$
- Units: infinitely many (Pell's equation)

## Lean Formalization

In this project, we formalize:

- `QuadraticNumberFields d`: The quadratic field $\mathbb{Q}(\sqrt{d})$
- `ringOfIntegers_classification`: The main classification theorem
- `norm_mul`: Norm multiplicativity
- `isUnit_zsqrtd_iff_norm_eq_one_or_neg_one`: Unit criterion

[← Back to Home](index.html)
