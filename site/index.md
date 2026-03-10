---
layout: default
title: Home
---

# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields $\mathbb{Q}(\sqrt{d})$ and the classification of their ring of integers.

## Overview

Given a square-free integer $d$, the **quadratic number field** $\mathbb{Q}(\sqrt{d})$ is the smallest field containing $\mathbb{Q}$ and $\sqrt{d}$. The **ring of integers** $\mathcal{O}_K$ of a number field $K$ is the set of all algebraic integers in $K$.

This project provides a complete formalization in Lean 4 of:
- The structure of quadratic number fields
- The classification of their rings of integers
- Norm and trace properties
- Integrality criteria and unit structures
- Concrete examples including ideal factorization and ramification in $\mathbb{Z}[\sqrt{-5}]$

The formalization is fully verified and integrates with mathlib's algebraic hierarchy.

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
For $d = -3$: Since $-3 \equiv 1 \pmod{4}$, we have
$\mathcal{O}_{\mathbb{Q}(\sqrt{-3})} = \mathbb{Z}[\omega]$ where
$\omega = \frac{-1 + \sqrt{-3}}{2}$ in the standard convention.
The formal model also uses the equivalent generator $\frac{1 + \sqrt{-3}}{2} = 1 + \omega$.

## Project Structure

| Directory | Description |
|-----------|-------------|
| `Lean/QuadraticNumberFields/` | Core definitions and proofs |
| `Lean/QuadraticNumberFields/RingOfIntegers/` | Classification theorems |
| `Lean/QuadraticNumberFields/Examples/ZsqrtdNeg5/` | Concrete examples for $\mathbb{Z}[\sqrt{-5}]$: ideal factorization, primality, ramification and inertia |
| `Verso/` | Documentation generation |
| `site/` | Jekyll website |

## Build Instructions

```bash
cd Lean
lake exe cache get
lake build
```

## Navigation

### Getting Started
- [Getting Started Guide](getting-started.html) - Installation and first steps

### Theory and Examples
- [Blueprint](blueprint.html) - The theorem pipeline and module-stage roadmap for the whole formalization
- [Mathematical Background](math.html) - Detailed mathematical theory and proofs
- [Examples and Applications](examples.html) - Gaussian integers, Eisenstein integers, and more

### Technical Documentation
- [API Atlas](api.html) - Every named declaration with mathematical form, Lean motivation, and dependency context
- [Formalization Details](formalization.html) - Design decisions and proof techniques
- [Resources](resources.html) - Learning materials, tools, and references

## Documentation Portal

If you want the site entry point used in projects like `QuadraticIntegers`, start here:

<div class="portal-links">
  <div class="portal-card">
    <h3>Blueprint</h3>
    <p>Open <a href="blueprint.html">Blueprint</a> for the theorem roadmap, staged dependency layers, and reader paths through the project.</p>
  </div>
  <div class="portal-card">
    <h3>API Atlas</h3>
    <p>Open <a href="api.html">API Atlas</a> for the source-driven declaration map of <code>Lean/QuadraticNumberFields</code>.</p>
  </div>
  <div class="portal-card">
    <h3>Generated Lean Docs</h3>
    <p>Open <a href="docs/">docs</a> when you want searchable symbol pages and doc-comment lookup.</p>
  </div>
</div>

<div class="portal-links">
  <div class="portal-card">
    <h3>Dependency Map</h3>
    <p>Jump directly to <a href="api.html#module-dependency-map">module dependencies</a> to see how the proof layers stack.</p>
  </div>
  <div class="portal-card">
    <h3>Declaration Atlas</h3>
    <p>Jump directly to <a href="api.html#declaration-atlas">declaration tables</a> to inspect every named top-level declaration.</p>
  </div>
  <div class="portal-card">
    <h3>Formalization Rationale</h3>
    <p>Open <a href="formalization.html">Formalization Details</a> for the design choices behind the Lean architecture.</p>
  </div>
</div>

## Quick Links

- [GitHub Repository](https://github.com/FrankieeW/QuadraticNumberFields)
- [Lean 4](https://leanprover.github.io/)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

## Reference

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
