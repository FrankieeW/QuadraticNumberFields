---
layout: default
title: Home
---

# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields $\mathbb{Q}(\sqrt{d})$ and the classification of their ring of integers.

## Overview

Given a square-free integer $d$, the **quadratic number field** $\mathbb{Q}(\sqrt{d})$ is the smallest field containing $\mathbb{Q}$ and $\sqrt{d}$. The **ring of integers** $\mathcal{O}_K$ of a number field $K$ is the set of all algebraic integers in $K$.

This project formalizes the complete classification of rings of integers for quadratic fields in Lean 4.

## Main Theorem

For a square-free integer $d$:

| Case | Condition | Ring of Integers |
|------|-----------|------------------|
| 1 | $d \equiv 2, 3 \pmod{4}$ | $\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}[\sqrt{d}]$ |
| 2 | $d \equiv 1 \pmod{4}$ | $\mathcal{O}_{\mathbb{Q}(\sqrt{d})} = \mathbb{Z}\left[\frac{1 + \sqrt{d}}{2}\right]$ |

## Examples

### Gaussian Integers
For $d = -1$: Since $-1 \equiv 3 \pmod{4}$, we have $\mathcal{O}_{\mathbb{Q}(i)} = \mathbb{Z}[i]$.

### Eisenstein Integers
For $d = -3$: Since $-3 \equiv 1 \pmod{4}$, we have $\mathcal{O}_{\mathbb{Q}(\sqrt{-3})} = \mathbb{Z}[\omega]$ where $\omega = \frac{1 + \sqrt{-3}}{2}$.

## Project Structure

| Directory | Description |
|-----------|-------------|
| `Lean/QuadraticNumberFields/` | Core definitions and proofs |
| `Lean/QuadraticNumberFields/RingOfIntegers/` | Classification theorems |
| `Verso/` | Documentation generation |
| `site/` | Jekyll website |

## Build Instructions

```bash
cd Lean
lake exe cache get
lake build
```

## Quick Links

- [GitHub Repository](https://github.com/FrankieeW/QuadraticNumberFields)
- [Mathematical Background](math.html)
- [API Documentation](api.html)
- [Lean](https://leanprover.github.io/)
- [mathlib](https://github.com/leanprover-community/mathlib)

## Reference

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
