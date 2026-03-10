---
layout: default
title: Blueprint
---

# Blueprint

This page turns the formalization into a website-level blueprint: a guided map from the mathematics to the Lean architecture.

## What This Blueprint Tracks

The project has two parallel stories:

- the mathematical story: classify the ring of integers of $\mathbb{Q}(\sqrt{d})$;
- the Lean story: choose concrete carriers, package embeddings and equivalences, and split the proof into reusable layers.

The blueprint keeps those two stories aligned.

<div class="blueprint-grid">
  <div class="blueprint-card">
    <h3>Mathematical Goal</h3>
    <p>Show that the integral closure of $\mathbb{Z}$ inside $\mathbb{Q}(\sqrt{d})$ is either $\mathbb{Z}[\sqrt{d}]$ or $\mathbb{Z}\left[\frac{1 + \sqrt{d}}{2}\right]$, depending on <code>d mod 4</code>.</p>
  </div>
  <div class="blueprint-card">
    <h3>Lean Goal</h3>
    <p>Factor that theorem through reusable declarations: field models, parameter normalization, half-integer normal forms, mod-4 lemmas, and final ring equivalences.</p>
  </div>
  <div class="blueprint-card">
    <h3>Navigation Goal</h3>
    <p>Let readers move from the high-level theorem pipeline here to the full declaration-level breakdown in the <a href="api.html">API Atlas</a>.</p>
  </div>
</div>

## Theorem Pipeline

```text
Basic / Instances / Parameters
        ↓
Zsqrtd / HalfInt / TraceNorm / ModFour / ZOnePlusSqrtOverTwo
        ↓
Integrality
        ↓
Classification
        ↓
Norm / Discriminant / Dedekind criteria / Worked examples
```

## Blueprint Stages

<div class="blueprint-stage">
  <h3>Stage 1. Foundational Field Model</h3>
  <p><strong>Mathematics:</strong> Fix a concrete model for quadratic fields and identify which parameters define a genuine quadratic extension.</p>
  <p><strong>Lean modules:</strong> <code>Basic</code>, <code>Instances</code>, <code>Parameters</code>, <code>FieldClassification</code>, <code>RingEquiv</code>.</p>
  <p><strong>Why Lean needs this:</strong> the later files need a stable carrier <code>Qsqrtd d</code>, explicit <code>Fact</code> assumptions, and transport tools for moving algebraic structure across equivalences.</p>
</div>

<div class="blueprint-stage">
  <h3>Stage 2. Integral Basis Candidates</h3>
  <p><strong>Mathematics:</strong> isolate the two classical order candidates $\mathbb{Z}[\sqrt{d}]$ and $\mathbb{Z}\left[\frac{1+\sqrt{d}}{2}\right]$, then express elements in half-integer coordinates.</p>
  <p><strong>Lean modules:</strong> <code>RingOfIntegers/Zsqrtd</code>, <code>RingOfIntegers/HalfInt</code>, <code>RingOfIntegers/ZOnePlusSqrtOverTwo</code>.</p>
  <p><strong>Why Lean needs this:</strong> once the two candidate rings are explicit types with embeddings into <code>Qsqrtd</code>, later theorems can use ring homomorphisms and integral-closure APIs instead of ad hoc coercions.</p>
</div>

<div class="blueprint-stage">
  <h3>Stage 3. Arithmetic Criteria For Integrality</h3>
  <p><strong>Mathematics:</strong> convert integrality into trace and norm conditions, then reduce those conditions to divisibility and parity constraints modulo 4.</p>
  <p><strong>Lean modules:</strong> <code>RingOfIntegers/TraceNorm</code>, <code>RingOfIntegers/ModFour</code>, <code>RingOfIntegers/Integrality</code>.</p>
  <p><strong>Why Lean needs this:</strong> the classification proof becomes a pipeline of reusable lemmas: normal form, integer trace/norm, divisibility by 4, and branch-specific existence in the correct order.</p>
</div>

<div class="blueprint-stage">
  <h3>Stage 4. Final Classification</h3>
  <p><strong>Mathematics:</strong> prove the two ring-of-integers cases and combine them into the final disjunction.</p>
  <p><strong>Lean modules:</strong> <code>RingOfIntegers/Classification</code>.</p>
  <p><strong>Outputs:</strong> <code>ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one</code>, <code>ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one</code>, <code>ringOfIntegers_classification</code>.</p>
</div>

<div class="blueprint-stage">
  <h3>Stage 5. Arithmetic Consequences And Examples</h3>
  <p><strong>Mathematics:</strong> extract norm formulas, discriminants, Dedekind-domain criteria, totally real/complex behavior, Euclideanity, and concrete ideal factorizations.</p>
  <p><strong>Lean modules:</strong> <code>RingOfIntegers/Norm</code>, <code>RingOfIntegers/Discriminant</code>, <code>RingOfIntegers/ZsqrtdMathlibInstances</code>, <code>TotallyRealComplex</code>, <code>Euclidean/Basic</code>, <code>Examples/ZsqrtdNeg5/*</code>.</p>
  <p><strong>Why Lean needs this:</strong> these files show the classification theorem is not an endpoint; it is infrastructure for downstream number theory.</p>
</div>

## Reader Paths

<div class="portal-links">
  <div class="portal-card">
    <h3>Start From Mathematics</h3>
    <p>Read <a href="math.html">Mathematical Background</a>, then this blueprint, then jump into the final declarations on <a href="api.html">API Atlas</a>.</p>
  </div>
  <div class="portal-card">
    <h3>Start From Lean Architecture</h3>
    <p>Read <a href="formalization.html">Formalization Details</a>, then open the generated <a href="api.html">API Atlas</a> to inspect signatures and dependency context module by module.</p>
  </div>
  <div class="portal-card">
    <h3>Start From Concrete Arithmetic</h3>
    <p>Open <a href="examples.html">Examples</a> and the <code>ZsqrtdNeg5</code> files, then walk backward through this blueprint to see which general lemmas power the example.</p>
  </div>
</div>

## Website Integration

This blueprint page is the high-level portal. The declaration-level counterpart is the [API Atlas](api.html), which is generated directly from the Lean source tree and lists every named declaration together with its mathematical form, Lean motivation, and dependency context.

[← Back to Home](index.html)
