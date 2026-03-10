---
layout: default
title: API Atlas
---

# API Atlas

This page is the source-driven declaration atlas for `QuadraticNumberFields`.
It is designed around four questions for each named declaration:

1. What mathematical object or statement is this encoding?
2. Why does this declaration exist in Lean rather than only on paper?
3. Which module layer does it depend on?
4. What is the actual Lean signature exported by the file?

## How To Read This Page

- `Module Dependency Map` gives the local import graph inside this repository.
- `Declaration Atlas` expands module by module and lists every named top-level declaration found under `QuadraticNumberFields`.
- `Mathematical Form` is taken from the declaration docstring when available, otherwise inferred from the declaration name and module role.
- `Lean Motivation` explains why the declaration is packaged the way it is for reuse in proofs, typeclass inference, rewriting, or transport across equivalences.
- `Dependency Focus` highlights the nearest symbols or module layer the declaration sits on top of.

## Why This View Exists

The old API page only listed a handful of core names. That was too thin for a project whose proofs are organized as a dependency pipeline:

- `Basic` fixes the quadratic field model.
- `Parameters` normalizes and classifies admissible parameters.
- `Zsqrtd`, `HalfInt`, `TraceNorm`, `ModFour`, and `Integrality` build the arithmetic machinery for integral elements.
- `Classification`, `Norm`, `Discriminant`, and `ZsqrtdMathlibInstances` expose the final number-theoretic consequences.
- `Examples/ZsqrtdNeg5` shows the theory in a fully formalized concrete case.

This page makes that pipeline visible directly from the website.

## Generated Content

{% include generated/api-catalog.html %}

## See Also

- [Mathematical Background](math.html) - Theory and mathematical context
- [Formalization Details](formalization.html) - Design decisions and implementation
- [Getting Started](getting-started.html) - How to use this formalization

[← Back to Home](index.html)
