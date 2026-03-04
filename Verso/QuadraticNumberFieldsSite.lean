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

# Overview

This repository provides a formalisation in the Lean 4 theorem prover of results related to
quadratic number fields $\mathbb{Q}(\sqrt{d})$ and the classification of their ring of integers.

Given a square-free integer $d$, the quadratic number field $\mathbb{Q}(\sqrt{d})$ is the smallest
field containing $\mathbb{Q}$ and $\sqrt{d}$. The ring of integers $\mathcal{O}_K$ of a number field
$K$ is the set of all algebraic integers in $K$.

For quadratic fields, the ring of integers has a particularly nice classification:

- If $d \equiv 2, 3 \pmod{4}$, then $\mathcal{O}_K = \mathbb{Z}[\sqrt{d}]$
- If $d \equiv 1 \pmod{4}$, then $\mathcal{O}_K = \mathbb{Z}\left[\frac{1 + \sqrt{d}}{2}\right]$

# Repository Structure

The repository is organised as follows:

: `Lean`

  The formal Lean 4 proofs, including:
  - `QuadraticNumberFields/Def.lean`: Core definitions of quadratic number fields
  - `QuadraticNumberFields/Basic.lean`: Basic properties
  - `QuadraticNumberFields/Param.lean`: Parameterization
  - `QuadraticNumberFields/RingOfIntegers/`: Classification theorems

: `Verso`

  Lean code for generating this documentation website using the Verso framework.

: `site`

  Jekyll website source files, completed by the Verso-generated content.

# Mathematical Background

## Quadratic Number Fields

A quadratic number field is an extension of $\mathbb{Q}$ of degree 2. Every such field can be written
as $\mathbb{Q}(\sqrt{d})$ for some square-free integer $d$.

## Ring of Integers

The ring of integers $\mathcal{O}_K$ of a number field $K$ consists of all elements of $K$ that
are roots of monic polynomials with integer coefficients.

For quadratic fields, we have the following classification theorem:

**Theorem**: Let $d$ be a square-free integer. Then:

1. If $d \equiv 2, 3 \pmod{4}$, then $\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}[\sqrt{d}]$
2. If $d \equiv 1 \pmod{4}$, then $\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}\left[\frac{1 + \sqrt{d}}{2}\right]$

## Norm

The norm of an element $\alpha = a + b\sqrt{d}$ in $\mathbb{Q}(\sqrt{d})$ is defined as:

$$N(\alpha) = \alpha \cdot \bar{\alpha} = (a + b\sqrt{d})(a - b\sqrt{d}) = a^2 - db^2$$

The norm is multiplicative: $N(\alpha\beta) = N(\alpha)N(\beta)$.

# References

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
