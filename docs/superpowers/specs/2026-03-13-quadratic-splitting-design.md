# QuadraticSplitting Module Design

**Date:** 2026-03-13
**Status:** Approved
**Module:** QuadraticSplitting

## 1. Overview

This document specifies the design for the `QuadraticSplitting` module, which formalizes the classification of prime splitting in quadratic number fields Q(√d).

## 2. Goals

Formalize the theorem that describes how rational primes p split, remain inert, or ramify in quadratic extensions Q(√d), using the Legendre symbol (d|p).

## 3. File Structure

```
QuadraticSplitting/
├── Split.lean      -- Split primes: definition and properties
├── Inert.lean      -- Inert primes: definition and properties
├── Ramified.lean   -- Ramified primes: definition and properties
└── Basic.lean      -- Unified entry point with common definitions
```

## 4. Core Definitions

### 4.1 Prime Split Type

```lean
inductive PrimeSplitType (d : ℤ) (p : ℕ) [Fact p.Prime]
  | Split    -- p splits in Q(√d)
  | Inert    -- p remains inert in Q(√d)
  | Ramified -- p ramifies in Q(√d)
```

### 4.2 Legendre Symbol

Use the existing `LegendreSymbol` from mathlib for the Legendre symbol (d|p), where:
- p is an odd prime
- d is a squarefree integer (parameter of the quadratic field)

### 4.3 Classification Predicates

```lean
def isSplit (p : ℕ) (d : ℤ) [Fact p.Prime] : Prop
def isInert (p : ℕ) (d : ℤ) [Fact p.Prime] : Prop
def isRamified (p : ℕ) (d : ℤ) [Fact p.Prime] : Prop
```

## 5. Main Theorems

### 5.1 Basic.lean - Classification Theorem

```lean
-- Primary classification via Legendre symbol
theorem primeSplitType_of_legendre (d : ℤ) (hd : IsSquarefree d)
    (p : ℕ) [hp : Fact p.Prime] (hp' : p ≠ 2) :
    PrimeSplitType d p :=
    match legendreSym d p with
    | 1   => .Split
    | -1  => .Inert

-- Ramified case
theorem primeSplitType_of_divides (d : ℤ) (hd : IsSquarefree d)
    (p : ℕ) [hp : Fact p.Prime] (hp' : p ∣ d) :
    PrimeSplitType d p = .Ramified

-- Connection to discriminant
theorem ramified_of_divides_discriminant {K : Type*} [Field K]
    [Algebra ℚ K] (d : ℤ) (hd : IsSquarefree d)
    (p : ℕ) [hp : Fact p.Prime] (hK : K ≅ QuadraticField d) :
    p ∣ discriminant K → PrimeSplitType d p = .Ramified
```

### 5.2 Split.lean - Split Primes

```lean
-- Definition via Legendre symbol = 1
theorem isSplit_def {d : ℤ} {p : ℕ} [Fact p.Prime] :
    isSplit p d ↔ legendreSym d p = 1

-- Split if and only if p is a quadratic residue modulo d
theorem split_is_quadratic_residue {d : ℤ} {p : ℕ} [Fact p.Prime] :
    isSplit p d ↔ IsQuadraticResidue p d

-- Example: p splits in Q(√d) for specific d
```

### 5.3 Inert.lean - Inert Primes

```lean
-- Definition via Legendre symbol = -1
theorem isInert_def {d : ℤ} {p : ℕ} [Fact p.Prime] :
    isInert p d ↔ legendreSym d p = -1

-- Inert if and only if p is a quadratic non-residue
theorem inert_is_quadratic_nonresidue {d : ℤ} {p : ℕ} [Fact p.Prime] :
    isInert p d ↔ ¬IsQuadraticResidue p d
```

### 5.4 Ramified.lean - Ramified Primes

```lean
-- Definition: p divides the discriminant
theorem isRamified_def {d : ℤ} {p : ℕ} [Fact p.Prime] :
    isRamified p d ↔ p ∣ discriminant (QuadraticField d)

-- For odd p: p ramifies iff p | d
theorem ramified_of_divides_d {d : ℤ} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    isRamified p d ↔ p � d

-- Special case: p = 2
theorem ramified_2 {d : ℤ} (hd : IsSquarefree d) :
    isRamified 2 d ↔ d ≡ 2,3 (mod 4)
```

## 6. Dependencies

- **QuadraticNumberFields**: Core library
  - `QuadraticNumberFields.Parameters` - squarefree parameter d
  - `QuadraticNumberFields.RingOfIntegers.Discriminant` - discriminant concepts
- **mathlib**:
  - `NumberTheory.LegendreSymbol`
  - `NumberTheory.QuadraticReciprocity`
  - `Algebra.Field.QuadraticField`

## 7. Export Structure

```lean
import QuadraticSplitting

-- Available:
open QuadraticSplitting
#check isSplit
#check isInert
#check isRamified
#check PrimeSplitType
#check primeSplitType_of_legendre
```

## 8. Integration with lakefile.toml

Add new library to the project:

```toml
[[lean_lib]]
name = "QuadraticSplitting"
```

With dependency on QuadraticNumberFields:

```toml
[[lean_lib]]
name = "QuadraticSplitting"
[[lean_lib]]
name = "QuadraticNumberFields"

[dependencies.QuadraticSplitting]
path = "QuadraticSplitting"
requires = ["QuadraticNumberFields"]
```

## 9. Implementation Notes

### 9.1 Parameter d Requirements

- d must be squarefree (non-square integer)
- Cases: d > 0 (imaginary) and d < 0 (real)

### 9.2 Special Cases

- p = 2 requires separate treatment (different from odd primes)
- p dividing d must be handled as ramified case
- d = -1 (Gaussian integers) should work as special case

### 9.3 Style Guidelines

Follow mathlib naming conventions:
- `isX` for predicates
- `X_def` for definitional equivalences
- `X_of_Y` for implications

## 10. Acceptance Criteria

1. Module compiles without errors
2. Main classification theorem is proven
3. All three cases (Split, Inert, Ramified) are formalized
4. Basic.lean exports all main definitions and theorems
5. Integration with lakefile.toml is complete
