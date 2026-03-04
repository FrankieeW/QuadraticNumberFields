---
layout: default
title: Formalization Details
---

# Formalization Details

## Design Principles

This formalization follows several key design principles:

1. **Type Safety:** Lean's dependent type system ensures that our definitions are well-formed
2. **Computational Content:** Definitions include explicit algorithms when possible
3. **Generality:** We work at the appropriate level of abstraction
4. **Compatibility:** Seamless integration with mathlib's algebraic hierarchy

## Key Design Decisions

### Parameterization

We define quadratic fields through the `QuadFieldParam` typeclass:

```lean
class QuadFieldParam (d : ℤ) : Prop where
  squarefree : Squarefree d
  ne_one : d ≠ 1
```

This ensures:
- $d$ is square-free (no repeated prime factors)
- $d \neq 1$ (to avoid the trivial case $\mathbb{Q}(\sqrt{1}) = \mathbb{Q}$)

**Rationale:** Using a typeclass allows us to automatically infer these properties and write cleaner theorem statements.

### Representation via QuadraticAlgebra

We represent $\mathbb{Q}(\sqrt{d})$ using mathlib's `QuadraticAlgebra`:

```lean
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

abbrev QuadraticNumberFields (d : ℤ) [QuadFieldParam d] : Type :=
  Qsqrtd (d : ℚ)
```

**Rationale:** This leverages existing infrastructure for:
- Field operations
- Norm and trace computations
- Embeddings and homomorphisms

### Two Cases for Ring of Integers

The classification theorem distinguishes two cases based on $d \bmod 4$:

**Case 1:** $d \not\equiv 1 \pmod{4}$
```lean
abbrev Zsqrtd (d : ℤ) : Type := QuadraticAlgebra ℤ d 0
```
Ring of integers: $\mathbb{Z}[\sqrt{d}]$

**Case 2:** $d \equiv 1 \pmod{4}$
```lean
abbrev ZOnePlusSqrtOverTwo (k : ℤ) : Type :=
  QuadraticAlgebra ℤ k 1
```
Ring of integers: $\mathbb{Z}\left[\frac{1+\sqrt{d}}{2}\right]$ where $d = 1 + 4k$

**Rationale:** Separate definitions allow us to:
- Provide optimal computational behavior for each case
- State case-specific properties cleanly
- Match mathematical practice

## Proof Techniques

### Integrality via Norm and Trace

To prove an element is integral, we show its characteristic polynomial has integer coefficients. For $\alpha = a + b\sqrt{d}$:

**Characteristic polynomial:**
$$(X - \alpha)(X - \overline{\alpha}) = X^2 - \text{Tr}(\alpha) X + N(\alpha)$$

**Integrality conditions:**
- $\text{Tr}(\alpha) = 2a \in \mathbb{Z}$
- $N(\alpha) = a^2 - db^2 \in \mathbb{Z}$

### Modular Arithmetic Arguments

The proof heavily relies on analyzing congruences modulo 4:

**Key lemma:** If $d$ is square-free and $d \neq 1$, then:
- Either $d \equiv 2, 3 \pmod{4}$, or
- $d \equiv 1 \pmod{4}$

**Proof technique:** Case analysis on $d \bmod 4$, using:
- Properties of square-free integers
- Quadratic residues modulo 4

### Ring Isomorphisms

We establish the classification through explicit ring isomorphisms:

```lean
def ringOfIntegers_equiv_zsqrtd (d : ℤ) [QuadFieldParam d]
    (hd4 : d % 4 ≠ 1) :
    𝓞 (QuadraticNumberFields d) ≃+* Zsqrtd d
```

**Construction:** Define forward and inverse maps, then verify:
1. Both are ring homomorphisms
2. They compose to the identity

## Computational Content

Our formalization includes computable functions where possible:

### Norm Computation

```lean
def norm (z : ℤ√d) : ℤ := z.re ^ 2 - d * z.im ^ 2
```

**Complexity:** $O(1)$ arithmetic operations

### Basis Elements

For $d \equiv 1 \pmod{4}$, the basis $\{1, \omega\}$ where $\omega = \frac{1+\sqrt{d}}{2}$:

```lean
def omega (k : ℤ) : Qsqrtd (1 + 4 * k) :=
  ⟨(1 : ℚ) / 2, (1 : ℚ) / 2⟩  -- represents (1 + √(1 + 4 * k)) / 2
```

## Connections to mathlib

### Algebraic Structures

Our definitions inherit structures from mathlib:

- **Field:** `QuadraticNumberFields d` is a `Field`
- **Integral domain:** `Zsqrtd d` is an `IntegralDomain`
- **Algebra:** Both are `ℤ`-algebras

### Number Theory

We connect to general number theory:

- `IsDedekindDomain` instance
- `IsIntegralClosure` proofs
- Norm maps and ideal theory

### Integration Example

```lean
instance : Field (QuadraticNumberFields d) := inferInstance

instance : Algebra ℤ (Zsqrtd d) := inferInstance

instance : IsDedekindDomain (𝓞 (QuadraticNumberFields d)) :=
  inferInstance
```

## Verification Strategy

### Test Cases

We verify our implementation with concrete examples:

```lean
example : 𝓞 (QuadraticNumberFields (-1)) ≃+* Zsqrtd (-1) :=
  ringOfIntegers_equiv_zsqrtd (-1) (by norm_num)

example : ∃ k, (-3) = 1 + 4 * k := ⟨-1, by norm_num⟩
```

### Automated Tactics

We use automation for routine proofs:
- `norm_num` for numerical computations
- `ring` for polynomial identities
- `field_simp` for field manipulations

## Future Extensions

Potential directions for extending this formalization:

1. **Euclidean domains:** Formalize which quadratic fields are Euclidean
2. **Class groups:** Define and compute class numbers
3. **Unit groups:** Structure theorem for units in real quadratic fields
4. **Continued fractions:** Connection to Pell's equation
5. **Factorization:** Algorithms for factoring in rings of integers

## Performance Considerations

### Computational Efficiency

- **Norm computation:** Direct formula, no polynomial evaluation
- **Basis representation:** Minimal data structure overhead
- **Type checking:** Efficient due to definitional equalities

### Proof Size

- **Modularity:** Lemmas are reused across different cases
- **Abstraction:** Generic proofs when possible
- **Specialization:** Case-specific proofs when needed for clarity

[← Back to Home](index.html)
