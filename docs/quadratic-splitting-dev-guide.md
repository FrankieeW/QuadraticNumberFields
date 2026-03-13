# Quadratic Splitting Development Guide

Reference document for hand-developing the prime splitting classification in Q(sqrt d).

## Goal

Prove: for squarefree d != 1 and prime p,

```
legendreSym p d =  1   =>  (p) = P1 * P2,  e=1, f=1, g=2   (split)
legendreSym p d = -1   =>  (p) = P,         e=1, f=2, g=1   (inert)
legendreSym p d =  0   =>  (p) = P^2,       e=2, f=1, g=1   (ramified)
```

and the equivalence: p ramifies <=> p | disc(Q(sqrt d)).

## File Structure (implemented)

```
QuadraticNumberFields/Splitting/
  Defs.lean            -- Phase 1: IsSplitIn / IsInertIn / IsRamifiedIn + trichotomy
  Monogenic.lean       -- Phase 2: O_K = Z[theta], exponent = 1
  MinpolyMod.lean      -- Phase 3: X^2 - d mod p factorization + Legendre connection
  Classification.lean  -- Phase 4: Legendre symbol criterion (main theorem)
  Discriminant.lean    -- Phase 5: ramified <=> p | disc
```

All under the `QuadraticNumberFields.Splitting` namespace.

## Dependency Graph

```
                Defs.lean
               (definitions, trichotomy)
                    |
          +---------+---------+
          |                   |
    Monogenic.lean      MinpolyMod.lean
    (O_K = Z[theta],    (X^2 - d mod p
     exponent = 1)       factorization)
          |                   |
          +---------+---------+
                    |
            Classification.lean
            (Legendre symbol criterion)
                    |
            Discriminant.lean
            (ramified <=> p | disc)
```

Import chains:
- `Defs.lean` — only mathlib (no project dependency)
- `Monogenic.lean` — `RingOfIntegers/Classification.lean` + mathlib Kummer-Dedekind
- `MinpolyMod.lean` — `Monogenic.lean` + mathlib Legendre symbol
- `Classification.lean` — `Defs.lean` + `Monogenic.lean` + `MinpolyMod.lean`
- `Discriminant.lean` — `Classification.lean` + `RingOfIntegers/Discriminant.lean`

---

## Phase 1: Definitions (`Defs.lean`) — DONE

### Current status

Definitions compile clean with zero errors/warnings.

### Implemented

General definitions for any Dedekind extension `R -> S`:

```lean
def Ideal.IsSplitIn (p : Ideal R) (S : Type*) ... : Prop :=
  1 < (p.primesOver S).ncard ∧
    ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1

def Ideal.IsInertIn (p : Ideal R) (S : Type*) ... : Prop :=
  (p.primesOver S).ncard = 1 ∧
    ∀ P ∈ p.primesOver S, ramificationIdx (algebraMap R S) p P = 1

def Ideal.IsRamifiedIn (p : Ideal R) (S : Type*) ... : Prop :=
  ∃ P ∈ p.primesOver S, 1 < ramificationIdx (algebraMap R S) p P
```

### TODO in this file

- [ ] Mutual exclusivity: `IsSplitIn.not_isInert`, `IsSplitIn.not_isRamified`, `IsInertIn.not_isRamified`
- [ ] Exhaustivity for degree-2: `isSplit_or_isInert_or_isRamified` (uses `sum_ramification_inertia` + Galois uniformity)

### Proof strategy for trichotomy

From `sum_ramification_inertia`: `∑ eᵢfᵢ = 2`. Since eᵢ >= 1, fᵢ >= 1, the only partitions of 2 are:
- 1·1 + 1·1 = 2 → g=2, e=1, f=1 → split
- 1·2 = 2 → g=1, e=1, f=2 → inert
- 2·1 = 2 → g=1, e=2, f=1 → ramified

For Galois extensions (quadratic is always Galois), all eᵢ are equal and all fᵢ are equal (`ramificationIdx_eq_of_isGalois`, `inertiaDeg_eq_of_isGaloisGroup`), which eliminates mixed cases.

### mathlib API

| Need | mathlib |
|------|---------|
| efg identity | `Ideal.sum_ramification_inertia` |
| Primes over p | `Ideal.primesOver`, `primesOverFinset` |
| Galois uniformity | `ramificationIdx_eq_of_isGalois`, `inertiaDeg_eq_of_isGaloisGroup` |
| efg = \|G\| | `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` |

---

## Phase 2: Monogenicity (`Monogenic.lean`) — TODO

### Goal

Establish `𝓞(ℚ(√d)) = ℤ[θ]` so Kummer-Dedekind applies to all primes unconditionally.

### What you already have

From `RingOfIntegers/Classification.lean`:
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`: `d % 4 ≠ 1 → 𝓞 ≃+* ℤ[√d]`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`: `d % 4 = 1 → 𝓞 ≃+* ℤ[(1+√d)/2]`

### What to build

```lean
-- The generator θ as an element of 𝓞_K
noncomputable def ringOfIntegersGenerator (d : ℤ) :
    𝓞 (Qsqrtd (d : ℚ)) := ...

-- θ generates 𝓞_K as a ℤ-algebra
theorem isMonogenic :
    Algebra.adjoin ℤ {ringOfIntegersGenerator d} = ⊤

-- Consequence: exponent θ = 1 (conductor is trivial)
theorem exponent_eq_one :
    RingOfIntegers.exponent (ringOfIntegersGenerator d) = 1

-- Therefore: for ALL primes p, Kummer-Dedekind applies
theorem not_dvd_exponent (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent (ringOfIntegersGenerator d)
```

### Key insight

Because `𝓞_K = ℤ[θ]` exactly (not just finite index), the conductor is `(1) = ℤ[θ]`, so `exponent = 1`, and `¬ p ∣ 1` is trivial for any prime. This is the main advantage of quadratic fields over general number fields.

### Tips

- Package the ring equiv as `Algebra.adjoin = ⊤` — look for `Subalgebra.eq_top_of_equiv` or build from `QuadraticAlgebra.basis`
- `RingOfIntegers.exponent` is defined via the conductor ideal; if `ℤ[θ] = 𝓞`, conductor = `⊤`, annihilator = `⊤`, exponent = 1

---

## Phase 3: Minpoly mod p (`MinpolyMod.lean`) — TODO

### Goal

Compute `minpoly ℤ θ` explicitly and classify its factorization mod p.

### Minimal polynomials

```
d % 4 ≠ 1:  θ = √d,          minpoly = X² - d
d % 4 = 1:  θ = (1+√d)/2,    minpoly = X² - X - (d-1)/4
```

### Theorems to prove

```lean
theorem minpoly_generator_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - C d

theorem minpoly_generator_mod_four_eq_one (hd4 : d % 4 = 1) :
    minpoly ℤ (ringOfIntegersGenerator d) = X ^ 2 - X - C ((d - 1) / 4)
```

### Factorization mod p (odd p, p ∤ d)

For `X² - d mod p`:

```lean
-- Splits ↔ d is a square mod p
theorem sq_sub_splits_mod_iff (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (map (Int.castRingHom (ZMod p)) (X ^ 2 - C d)).Splits (RingHom.id _)
    ↔ IsSquare ((d : ZMod p) : ZMod p)

-- Irreducible ↔ d is not a square mod p
theorem sq_sub_irreducible_mod_iff (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    Irreducible (map (Int.castRingHom (ZMod p)) (X ^ 2 - C d))
    ↔ ¬ IsSquare ((d : ZMod p) : ZMod p)

-- Double root ↔ p ∣ d
theorem sq_sub_double_root_iff :
    ... ↔ (p : ℤ) ∣ d
```

### Connection to Legendre symbol

The bridge: `IsSquare (d : ZMod p) ↔ legendreSym p d = 1` (from `legendreSym.eq_one_iff`).

| `monicFactorsMod θ p` | Polynomial behavior | Legendre |
|---|---|---|
| 2 linear factors | `(X-a)(X+a)`, a ≠ 0 | `legendreSym p d = 1` |
| 1 quadratic factor | irreducible | `legendreSym p d = -1` |
| 1 linear factor, mult 2 | `(X-a)²` | `legendreSym p d = 0` |

### mathlib API

| Need | mathlib |
|------|---------|
| Legendre symbol | `legendreSym p d` |
| Square ↔ legendreSym = 1 | `legendreSym.eq_one_iff` |
| Non-square ↔ legendreSym = -1 | `legendreSym.eq_neg_one_iff` |
| Polynomial splitting | `Polynomial.splits_iff_card_roots`, degree-2 lemmas |
| `ZMod p` is a field | `ZMod.instField` (from `Fact p.Prime`) |

### Special case: p = 2

Legendre symbol requires odd p. For p = 2, use direct case analysis:

```
d ≡ 2, 3 mod 4:
  minpoly = X² - d,  mod 2: X² - 1 = (X-1)²  →  ramified

d ≡ 1 mod 8:
  minpoly = X² - X - (d-1)/4,  mod 2: X² - X = X(X-1)  →  split

d ≡ 5 mod 8:
  minpoly = X² - X - (d-1)/4,  mod 2: X² + X + 1, irreducible  →  inert
```

Summary:
| d mod 8 | p = 2 behavior |
|---------|---------------|
| d ≡ 2, 3 mod 4 | ramified |
| d ≡ 1 mod 8 | split |
| d ≡ 5 mod 8 | inert |

---

## Phase 4: Classification via Legendre Symbol (`Classification.lean`) — TODO

### Goal

The main theorem connecting everything.

### Theorems to prove

```lean
-- Odd primes, p ∤ d
theorem isSplit_iff_legendreSym_eq_one (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsSplitIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ legendreSym p d = 1

theorem isInert_iff_legendreSym_eq_neg_one (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsInertIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ legendreSym p d = -1

-- Any prime dividing d
theorem isRamified_of_dvd (hpd : (p : ℤ) ∣ d) :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))

-- Unified
theorem splitting_classification (p : ℕ) [Fact p.Prime] :
    ((legendreSym p d = 1  ∧ ... IsSplitIn ...) ∨
     (legendreSym p d = -1 ∧ ... IsInertIn ...) ∨
     (legendreSym p d = 0  ∧ ... IsRamifiedIn ...))
```

### Proof chain

```
RingOfIntegers/Classification.lean  (𝓞 = ℤ[θ])
              ↓
Monogenic.lean  (exponent θ = 1)
              ↓
primesOverSpanEquivMonicFactorsMod  (mathlib Kummer-Dedekind)
              ↓
monicFactorsMod θ p = irred factors of minpoly mod p
              ↓
MinpolyMod.lean  (X² - d mod p ↔ Legendre)
              ↓
legendreSym p d  (mathlib)
```

### Key Kummer-Dedekind API

```lean
-- The core equivalence
primesOverSpanEquivMonicFactorsMod (hp : ¬p ∣ exponent θ)
  : (Ideal.span {↑p}).primesOver 𝓞 K ≃ monicFactorsMod θ p

-- Reading off e and f
ramificationIdx ... = multiplicity q̄ (minpoly ℤ θ mod p)
inertiaDeg ... = q̄.natDegree
```

Translation to IsSplit/IsInert/IsRamified:
- `|monicFactorsMod| = 2` → g = 2 → split
- `|monicFactorsMod| = 1`, degree 2 → f = 2 → inert
- `|monicFactorsMod| = 1`, multiplicity 2 → e = 2 → ramified

---

## Phase 5: Discriminant criterion (`Discriminant.lean`) — TODO

### Goal

```lean
theorem isRamified_iff_dvd_disc (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn (𝓞 (Qsqrtd (d : ℚ)))
      ↔ (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ))
```

### What you already have

From `RingOfIntegers/Discriminant.lean`:
- `discr_of_mod_four_ne_one`: `disc = 4d` when `d % 4 ≠ 1`
- `discr_of_mod_four_eq_one`: `disc = d` when `d % 4 = 1`
- `discr_formula`: unified

### Proof strategy

**Forward** (ramified → p ∣ disc):
```
ramified → p ∣ d  (from Phase 4 / legendreSym = 0)
         → p ∣ disc  (disc = 4d or d; p ∣ d implies p ∣ both)
```

**Backward** (p ∣ disc → ramified):
```
p ∣ disc → p ∣ 4d  (case d ≢ 1 mod 4) or p ∣ d  (case d ≡ 1 mod 4)
         → p ∣ d   (odd p: gcd(p,4)=1; p=2: d ≢ 1 mod 4 means 2 ramifies directly)
         → ramified
```

### Explicit characterization

```lean
-- Odd primes
theorem ramified_odd_iff (hp : p ≠ 2) :
    (Ideal.span {(p : ℤ)}).IsRamifiedIn ... ↔ (p : ℤ) ∣ d

-- p = 2
theorem ramified_two_iff :
    (Ideal.span {(2 : ℤ)}).IsRamifiedIn ... ↔ d % 4 ≠ 1
```

---

## Existing Project Code to Reuse

| File | What to reuse |
|------|---------------|
| `RingOfIntegers/Classification.lean` | `ringOfIntegers_equiv_zsqrtd_*`, `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_*` |
| `RingOfIntegers/Discriminant.lean` | `discr_formula`, `discr_of_mod_four_*` |
| `RingOfIntegers/ZsqrtdIdeals.lean` | `quotEquivZModP`, `quotEquivZModPNeg`, `comap_span_p_*`, `isPrime_span_p_*` |
| `RingOfIntegers/ZsqrtdMathlibInstances.lean` | `IsDedekindDomain` for Zsqrtd |
| `Examples/ZsqrtdNeg5/RamificationInertia.lean` | Pattern for computing e, f — generalize this |
| `Instances.lean` | `NumberField` instance for Qsqrtd |
| `Parameters.lean` | `Fact (Squarefree d)`, `Fact (d ≠ 1)` |

## Key mathlib Imports

```lean
-- Ramification/inertia
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois

-- Kummer-Dedekind
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

-- Legendre symbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.Basic

-- Primes over
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

-- Discriminant
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
```

## Estimated Difficulty

| Phase | Difficulty | Notes |
|-------|-----------|-------|
| 1. Defs | Easy | Definitions done; trichotomy = combinatorics on partitions of 2 |
| 2. Monogenic | Medium | Package ring equiv as `Algebra.adjoin = ⊤`, compute exponent |
| 3. MinpolyMod | Medium | Polynomial factorization mod p; p=2 case analysis |
| 4. Classification | Medium-Hard | Connecting Kummer-Dedekind ≃ to IsSplit/IsInert/IsRamified |
| 5. Discriminant | Easy-Medium | Divisibility arithmetic using existing disc formula |

Phase 4 is the hardest: unwrapping the Kummer-Dedekind equiv and connecting `monicFactorsMod` cardinality/degrees to the definitions.

## Alternative Approach: Direct (bypass Kummer-Dedekind)

If the Kummer-Dedekind API proves unwieldy, prove splitting directly by:

1. Constructing prime ideals explicitly (as in `ZsqrtdIdeals.lean`)
2. Computing e, f by hand (as in `Examples/ZsqrtdNeg5/RamificationInertia.lean`)
3. Showing uniqueness (these are the *only* primes over p)

The `ZsqrtdIdeals.lean` infrastructure is already parametric in p and d — it just needs `p ∣ (d-1)` generalized to all splitting types. This approach is more manual but avoids Kummer-Dedekind abstraction overhead.
