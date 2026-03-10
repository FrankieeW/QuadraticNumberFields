---
layout: default
title: Blueprint
---

# Blueprint

This page is the proof blueprint for the ring-of-integers classification in `QuadraticNumberFields`. It is intentionally closer to the `QuadraticIntegers` style: one route follows the mathematics, the other follows the Lean declarations and their dependency chain.

## Blueprint Purpose

<div class="blueprint-grid">
  <div class="blueprint-card">
    <h3>Human-Oriented Route</h3>
    <p>Track the mathematical proof of
    $\mathcal{O}_{\mathbb{Q}(\sqrt{d})}$ by reducing integrality to trace, norm, half-integer coordinates, and parity mod 4.</p>
  </div>
  <div class="blueprint-card">
    <h3>Formalisation-Oriented Route</h3>
    <p>Track how the proof is decomposed into reusable Lean declarations, with explicit module boundaries and theorem dependencies.</p>
  </div>
  <div class="blueprint-card">
    <h3>Navigation Route</h3>
    <p>Use this page for the theorem spine, then open the <a href="api.html">API Atlas</a> for every declaration and the generated <a href="docs/">Lean docs</a> for symbol lookup.</p>
  </div>
</div>

## Main Target

For squarefree integers $d \neq 1$, the project proves:

$$
\mathcal{O}_{\mathbb{Q}(\sqrt{d})}
=
\begin{cases}
\mathbb{Z}[\sqrt{d}] & \text{if } d \not\equiv 1 \pmod 4, \\
\mathbb{Z}\left[\dfrac{1+\sqrt{d}}{2}\right] & \text{if } d \equiv 1 \pmod 4.
\end{cases}
$$

The final Lean endpoints are:

- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- `ringOfIntegers_classification`

## Human-Oriented Blueprint

This is the mathematical proof route, written as a chain of proof obligations.

<div class="blueprint-stage">
  <h3>H1. Fix The Quadratic Field And The Two Candidate Orders</h3>
  <p><strong>Field:</strong> model $\mathbb{Q}(\sqrt{d})$ as a quadratic algebra over $\mathbb{Q}$.</p>
  <p><strong>Orders:</strong> compare the two classical candidates $\mathbb{Z}[\sqrt{d}]$ and $\mathbb{Z}\left[\frac{1+\sqrt{d}}{2}\right]$.</p>
  <p><strong>Lean files:</strong> <code>Basic</code>, <code>Parameters</code>, <code>RingOfIntegers/Zsqrtd</code>, <code>RingOfIntegers/ZOnePlusSqrtOverTwo</code>.</p>
</div>

<div class="blueprint-stage">
  <h3>H2. Reduce Integrality To Trace And Norm</h3>
  <p>For an integral element $x = a + b\sqrt{d}$, trace and norm must lie in $\mathbb{Z}$. In this model:
  $\mathrm{Tr}(x) = 2a$ and $N(x) = a^2 - db^2$.</p>
  <p><strong>Key idea:</strong> once trace and norm are integral, the coordinates of <code>x</code> are forced into a half-integer normal form.</p>
  <p><strong>Lean declarations:</strong> <code>trace_eq_two_re</code>, <code>TraceNorm.exists_int_trace</code>, <code>TraceNorm.exists_int_norm</code>.</p>
</div>

<div class="blueprint-stage">
  <h3>H3. Put Every Integral Element Into Half-Integer Normal Form</h3>
  <p>Every integral element can be written as
  $x = \dfrac{a' + b'\sqrt{d}}{2}$ with
  $4 \mid (a'^2 - d b'^2)$.</p>
  <p><strong>Meaning:</strong> the whole classification is reduced to a divisibility problem for the quadratic form
  $a'^2 - d b'^2$ modulo 4.</p>
  <p><strong>Lean declaration:</strong> <code>exists_halfInt_with_div_four_of_isIntegral</code>.</p>
</div>

<div class="blueprint-stage">
  <h3>H4. Split By <code>d mod 4</code></h3>
  <p>If <code>d % 4 ≠ 1</code>, divisibility by 4 forces both numerators even, so the element already lies in $\mathbb{Z}[\sqrt{d}]$.</p>
  <p>If <code>d % 4 = 1</code>, divisibility by 4 is equivalent to the two numerators having the same parity, which is exactly the carrier condition for $\mathbb{Z}\left[\frac{1+\sqrt{d}}{2}\right]$.</p>
  <p><strong>Lean declarations:</strong> <code>dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four</code>, <code>dvd_four_sub_sq_iff_same_parity_of_one_mod_four</code>.</p>
</div>

<div class="blueprint-stage">
  <h3>H5. Identify The Full Ring Of Integers</h3>
  <p>Once every integral element lands in the correct candidate order, the universal property of the ring of integers upgrades that containment into a ring equivalence.</p>
  <p><strong>Lean endpoint:</strong> first prove branchwise equivalences, then package the final classification disjunction.</p>
</div>

## Formalisation-Oriented Blueprint

This is the Lean route. Each step says what declaration exists, where it lives, and what earlier results it depends on.

| Stage | Lean declaration | File | Uses | Role |
|------|------|------|------|------|
| F1 | `Qsqrtd` | `Basic.lean` | mathlib `QuadraticAlgebra` | Fixes the concrete field model for `ℚ(√d)` |
| F2 | `Qsqrtd.param_unique` | `Parameters.lean` | rescaling + squarefree rigidity | Shows squarefree integer parameters classify the field up to isomorphism |
| F3 | `Zsqrtd.toQsqrtdHom`, `ZOnePlusSqrtOverTwo.toQsqrtdHom` | `Zsqrtd.lean`, `ZOnePlusSqrtOverTwo.lean` | explicit carrier models | Embeds candidate orders into the field |
| F4 | `TraceNorm.exists_int_trace`, `TraceNorm.exists_int_norm`, `TraceNorm.exists_int_double_im` | `TraceNorm.lean` | trace/norm formulas + integrality transport | Produces integer witnesses from an integral field element |
| F5 | `exists_halfInt_with_div_four_of_isIntegral` | `Integrality.lean` | F4 | Rewrites every integral element into half-integer coordinates |
| F6a | `dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four` | `Integrality.lean` | `ModFour.lean` + `Zsqrtd.lean` | Converts the mod-4 condition into membership in `ℤ[√d]` |
| F6b | `dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four` | `Integrality.lean` | `ModFour.lean` + `ZOnePlusSqrtOverTwo.lean` | Converts the mod-4 condition into membership in `ℤ[(1+√d)/2]` |
| F7a | `exists_zsqrtd_of_isIntegral_of_ne_one_mod_four` | `Integrality.lean` | F5 + F6a | Every integral element lifts to the `ℤ[√d]` model |
| F7b | `exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four` | `Integrality.lean` | F5 + F6b | Every integral element lifts to the `ℤ[(1+√d)/2]` model |
| F8 | `ringOfIntegers_equiv_of_embedding` | `Classification.lean` | generic integral-closure criterion | Abstract bridge from “correct integral image” to `𝓞 K ≃+* R` |
| F9a | `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one` | `Classification.lean` | F7a + F8 | Branch theorem for `d % 4 ≠ 1` |
| F9b | `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one` | `Classification.lean` | F7b + F8 | Branch theorem for `d % 4 = 1` |
| F10 | `ringOfIntegers_classification` | `Classification.lean` | F9a + F9b + `mod_four_branch_split` | Final dichotomy theorem |

## Dependency Spine

The proof spine is the formal analogue of the `uses` clauses in a blueprint:

```text
Qsqrtd / parameter lemmas
        ↓
candidate orders + embeddings
        ↓
trace and norm integrality witnesses
        ↓
half-integer normal form
        ↓
mod-4 divisibility criteria
        ↓
branchwise lifting to the correct order
        ↓
generic ring-of-integers identification
        ↓
final classification
```

## Branch Blueprints

### Branch A. `d % 4 ≠ 1`

<div class="blueprint-stage">
  <h3>Formal chain</h3>
  <p><code>exists_halfInt_with_div_four_of_isIntegral</code>
  → <code>dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four</code>
  → <code>exists_zsqrtd_of_isIntegral_of_ne_one_mod_four</code>
  → <code>ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one</code>.</p>
  <p><strong>Mathematical reading:</strong> the mod-4 condition forces both half-integer numerators to be even, so the integral element already comes from $\mathbb{Z}[\sqrt{d}]$.</p>
</div>

### Branch B. `d % 4 = 1`

<div class="blueprint-stage">
  <h3>Formal chain</h3>
  <p><code>exists_halfInt_with_div_four_of_isIntegral</code>
  → <code>dvd_four_sub_sq_iff_exists_zOnePlusSqrtOverTwo_image_of_one_mod_four</code>
  → <code>exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four</code>
  → <code>ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one</code>.</p>
  <p><strong>Mathematical reading:</strong> same parity of the numerators is exactly the coordinate condition for the larger order $\mathbb{Z}\left[\frac{1+\sqrt{d}}{2}\right]$.</p>
</div>

## From Classification To Downstream Arithmetic

Like a formal blueprint, this page should also show where the main theorem is used afterward.

<div class="blueprint-grid">
  <div class="blueprint-card">
    <h3>Norm And Units</h3>
    <p><code>Norm.lean</code> uses the classification to state norm formulas and unit criteria for the actual ring of integers.</p>
  </div>
  <div class="blueprint-card">
    <h3>Discriminant</h3>
    <p><code>Discriminant.lean</code> packages the two branches into the explicit discriminant formula.</p>
  </div>
  <div class="blueprint-card">
    <h3>Dedekind Behaviour</h3>
    <p><code>Classification.lean</code> and <code>ZsqrtdMathlibInstances.lean</code> derive when <code>ℤ[√d]</code> is Dedekind.</p>
  </div>
  <div class="blueprint-card">
    <h3>Worked Example</h3>
    <p><code>Examples/ZsqrtdNeg5</code> turns the abstract theory into concrete factorization, ramification, and inertia statements.</p>
  </div>
</div>

## Reading Paths

<div class="portal-links">
  <div class="portal-card">
    <h3>Mathematics First</h3>
    <p>Read <a href="math.html">Mathematical Background</a>, then the Human-Oriented blueprint above, then inspect the final declarations in the <a href="api.html">API Atlas</a>.</p>
  </div>
  <div class="portal-card">
    <h3>Lean First</h3>
    <p>Read the Formalisation-Oriented blueprint above, then open <a href="api.html#declaration-atlas">Declaration Atlas</a> for full signatures and module context.</p>
  </div>
  <div class="portal-card">
    <h3>Example First</h3>
    <p>Read <a href="examples.html">Examples</a>, especially the `ZsqrtdNeg5` story, then walk backward through the branch blueprints to the general theorem.</p>
  </div>
</div>

## Relationship To The API Atlas

This page is the theorem blueprint. The [API Atlas](api.html) is the declaration inventory. The intended workflow is:

1. Understand the proof skeleton here.
2. Open the matching module in the API Atlas.
3. Use the generated Lean docs for symbol-level details.

[← Back to Home](index.html)
