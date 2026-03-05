/-
QuadraticNumberFields Verso Site Content
-/

import Berso.Main

-- This gets access to most of the blog genre
open Verso Genre Blog

-- This gets access to Lean code that's in code blocks
open Verso.Code.External

set_option pp.rawOnError true

-- Source of code examples
set_option verso.exampleProject "../Lean"

-- Module for example code
set_option verso.exampleModule "QuadraticNumberFields"

#doc (Page) "Quadratic Number Fields" =>

# Quadratic Number Fields

A formalization of quadratic number fields $`\mathbb{Q}(\sqrt{d})` and the classification of their ring of integers in Lean 4.

## Overview

Given a square-free integer $`d`, the **quadratic number field** $`\mathbb{Q}(\sqrt{d})` is the smallest field containing $`\mathbb{Q}` and $`\sqrt{d}`. The **ring of integers** $`\mathcal{O}_K` of a number field $`K` is the set of all algebraic integers in $`K`.

This project formalizes the complete classification theorem:

: **Case 1** ($`d \equiv 2, 3 \pmod{4}`)

  $`\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}[\sqrt{d}]`

: **Case 2** ($`d \equiv 1 \pmod{4}`)

  $`\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}\left[\frac{1 + \sqrt{d}}{2}\right]`

# Mathematical Background

## Definition of Quadratic Fields

A **quadratic number field** is an extension of $`\mathbb{Q}` of degree 2. Every such field can be written as $`\mathbb{Q}(\sqrt{d})` for some square-free integer $`d \neq 0, 1`.

$$`\mathbb{Q}(\sqrt{d}) = \{a + b\sqrt{d} : a, b \in \mathbb{Q}\}`$$

## Ring of Integers

The **ring of integers** $`\mathcal{O}_K` of a number field $`K` consists of all elements that are roots of monic polynomials with integer coefficients.

For quadratic fields, determining which elements are integral leads to the classification theorem above.

## Norm

The **norm** of $`\alpha = a + b\sqrt{d}` is:

$$`N(\alpha) = \alpha \cdot \bar{\alpha} = a^2 - db^2`$$

Key properties:
- **Multiplicativity:** $`N(\alpha\beta) = N(\alpha)N(\beta)`
- **Unit criterion:** $`\alpha \in \mathcal{O}_K^\times \iff N(\alpha) = \pm 1`

# Examples

## Gaussian Integers

For $`d = -1`: Since $`-1 \equiv 3 \pmod{4}`, we have $`\mathcal{O}_{\mathbb{Q}(i)} = \mathbb{Z}[i]`.

- Elements: $`a + bi` where $`a, b \in \mathbb{Z}`
- Norm: $`N(a + bi) = a^2 + b^2`
- Units: $`\pm 1, \pm i`

## Eisenstein Integers

For $`d = -3`: Since $`-3 \equiv 1 \pmod{4}`, we have $`\mathcal{O}_{\mathbb{Q}(\sqrt{-3})} = \mathbb{Z}[\omega]` where $`\omega = \frac{1 + \sqrt{-3}}{2}`.

- Elements: $`a + b\omega` where $`a, b \in \mathbb{Z}`
- Norm: $`N(a + b\omega) = a^2 - ab + b^2`
- Units: $`\pm 1, \pm \omega, \pm \omega^2` (6 units)

## Ideal Theory in $`\mathbb{Z}[\sqrt{-5}]` (Formally Verified)

For $`d = -5`: Since $`-5 \equiv 3 \pmod{4}`, the ring of integers is $`\mathbb{Z}[\sqrt{-5}]`. This ring is *not* a UFD — the classic example being $`6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5})`.

The project includes complete formal verification of ideal factorization and ramification theory for this ring:

**Ideal Factorizations:**
- $`(2) = \mathfrak{p}_2^2` where $`\mathfrak{p}_2 = (2, 1 + \sqrt{-5})`
- $`(3) = \mathfrak{p}_{3,1} \cdot \mathfrak{p}_{3,2}` where $`\mathfrak{p}_{3,1} = (3, 1 + \sqrt{-5})`, $`\mathfrak{p}_{3,2} = (3, 1 - \sqrt{-5})`
- $`(1 + \sqrt{-5}) = \mathfrak{p}_2 \cdot \mathfrak{p}_{3,1}`
- $`(1 - \sqrt{-5}) = \mathfrak{p}_2 \cdot \mathfrak{p}_{3,2}`

**Primality:** All three ideals $`\mathfrak{p}_2`, $`\mathfrak{p}_{3,1}`, $`\mathfrak{p}_{3,2}` are proved to be prime.

**Ramification and Inertia:**

| Prime | Factorization | $`e` | $`f` | $`g` |
|-------|--------------|------|------|------|
| 2 | $`(2) = \mathfrak{p}_2^2` | 2 | 1 | 1 |
| 3 | $`(3) = \mathfrak{p}_{3,1} \cdot \mathfrak{p}_{3,2}` | 1 | 1 | 2 |

Verification: $`\sum e_i f_i = 2 = [\mathbb{Q}(\sqrt{-5}) : \mathbb{Q}]` ✓

See `Examples/ZsqrtdNeg5/` for the Lean source.

# Repository Structure

: `Lean/QuadraticNumberFields/`

  Core definitions and proofs:
  - `Basic.lean`: Core definitions (`Qsqrtd`, trace, norm)
  - `Param.lean`: `QuadFieldParam` class
  - `Def.lean`: Main field definition

: `Lean/QuadraticNumberFields/RingOfIntegers/`

  Classification theorems:
  - `Classification.lean`: Main theorem
  - `Integrality.lean`: Integrality proofs
  - `Norm.lean`: Norm properties
  - `Zsqrtd.lean`: $`\mathbb{Z}[\sqrt{d}]` definitions
  - `ZOnePlusSqrtOverTwo.lean`: $`\mathbb{Z}[\omega]` definitions

: `Lean/QuadraticNumberFields/Examples/ZsqrtdNeg5/`

  Concrete verified examples for $`\mathbb{Z}[\sqrt{-5}]`:
  - `Basic.lean`: `NoZeroDivisors`/`IsDomain` instances for negative $`d`
  - `Ideals.lean`: Ideal factorization and primality proofs
  - `RamificationInertia.lean`: Ramification indices and inertia degrees

: `Verso/`

  Documentation generation using Verso framework

: `site/`

  Jekyll website source files

# Build Instructions

```bash
cd Lean
lake exe cache get
lake build
```

# References

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
