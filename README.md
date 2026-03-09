# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields `Q(√d)` and the classification
of their ring of integers, centered on the Lean objects `Qsqrtd`,
`QuadraticNumberFields`, and `QuadFieldParam`.

**[Documentation site](https://frankieew.github.io/QuadraticNumberFields)**

## Main Results

### Ring of Integers Classification

(`RingOfIntegers/Classification.lean`)

For squarefree `d ≠ 1`, the ring of integers `𝓞 (ℚ(√d))` is classified as:

- If `d % 4 ≠ 1`, then `𝓞 (ℚ(√d)) ≃+* ℤ√d`.
- If `d % 4 = 1`, writing `d = 1 + 4k`, then `𝓞 (ℚ(√d)) ≃+* ℤ[(1+√d)/2]`.

Key declarations: `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`,
`ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`,
`ringOfIntegers_classification`.

Classical examples:
- **Gaussian integers** (`d = -1`): `𝓞 (ℚ(√(-1))) ≃+* ℤ[i]`
- **Eisenstein integers** (`d = -3`): `𝓞 (ℚ(√(-3))) ≃+* ℤ[ω]` where `ω = (1+√(-3))/2`

### Discriminant Formula

(`RingOfIntegers/Discriminant.lean`)

The number field discriminant of `ℚ(√d)` is computed as:

- `discr_formula`: `Δ(ℚ(√d)) = if d % 4 = 1 then d else 4 * d`

Examples: `Δ(ℚ(√(-1))) = -4`, `Δ(ℚ(√(-3))) = -3`, `Δ(ℚ(√(-5))) = -20`.

### Dedekind Domain Characterization

(`RingOfIntegers/ZsqrtdMathlibInstances.lean`)

For squarefree `d ≠ 1`:

- `isDedekindDomain_iff_mod_four_ne_one`: `ℤ√d` is a Dedekind domain if and only if `d % 4 ≠ 1`

This follows from the ring of integers classification — `ℤ√d` is a Dedekind domain
precisely when it equals the full ring of integers `𝓞 (ℚ(√d))`.

## Core Lean Objects

- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0`
  (`Lean/QuadraticNumberFields/Basic.lean`)
- `QuadFieldParam (d : ℤ)` with fields `squarefree : Squarefree d` and `ne_one : d ≠ 1`
  (`Lean/QuadraticNumberFields/Param.lean`)
- `QuadraticNumberFields (d : ℤ) [QuadFieldParam d] := Qsqrtd (d : ℚ)`
  (`Lean/QuadraticNumberFields/Instances.lean`)
- `Zsqrtd d` and `ZOnePlusSqrtOverTwo k` as the two candidate integral models
  (`Lean/QuadraticNumberFields/RingOfIntegers/`)

## Mathematical Content

This project formalizes:
- Quadratic number fields through `Qsqrtd` / `QuadraticNumberFields`
- `QuadFieldParam`: typeclass for squarefree `d ≠ 1` parameters
- Parametrization and uniqueness of the quadratic field structure
- Ring of integers classification (`ringOfIntegers_classification`)
- Discriminant formula (`discr_formula`)
- Dedekind domain characterization (`isDedekindDomain_iff_mod_four_ne_one`)
- Integrality criteria via trace and norm
- Ideal theory in `ℤ√d`: quotient by prime ideals, ramification
- Concrete verified examples for `ℤ[√-5]`: ideal factorization, primality, ramification/inertia

## Project Structure

```
QuadraticNumberFields/
├── Lean/                  # Lean formal proofs
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── QuadraticNumberFields.lean    # Root module
│   └── QuadraticNumberFields/
│       ├── Basic.lean               # Qsqrtd type, norm and trace
│       ├── Instances.lean           # QuadraticNumberFields alias + field/number field instances
│       ├── Param.lean               # QuadFieldParam typeclass and instances
│       ├── ParamUniqueness.lean     # Uniqueness of the quadratic structure
│       ├── Rescale.lean             # Rescaling between Q(√d) forms
│       ├── TotallyRealComplex.lean  # Totally real / complex place behavior
│       ├── RingEquiv.lean           # Dedekind domain transfer via ring equivalences
│       ├── Euclidean/
│       │   └── Basic.lean           # Euclidean domain classification framework
│       ├── Examples/
│       │   └── ZsqrtdNeg5/
│       │       ├── Ideals.lean          # Ideal factorization and primality in ℤ[√-5]
│       │       └── RamificationInertia.lean  # Ramification indices and inertia degrees
│       └── RingOfIntegers/
│           ├── Classification.lean  # Main classification theorem
│           ├── Discriminant.lean    # Discriminant formula for quadratic fields
│           ├── HalfInt.lean         # Half-integer normal form
│           ├── Integrality.lean     # Integrality criteria
│           ├── ModFour.lean         # Modulo-4 arithmetic lemmas
│           ├── Norm.lean            # Norm computations and unit criteria
│           ├── ZOnePlusSqrtOverTwo.lean  # ℤ[(1+√d)/2] ring
│           ├── Zsqrtd.lean          # ℤ√d ring as QuadraticAlgebra
│           ├── ZsqrtdIdeals.lean    # Ideal theory: quotients by prime ideals
│           └── ZsqrtdMathlibInstances.lean  # Dedekind domain characterization
├── Verso/                 # Documentation generation
└── site/                  # Jekyll website (GitHub Pages)
```


## Code Statistics

| Module | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `QuadraticNumberFields/RingOfIntegers` | 1203 | 428 | 1934 |
| `QuadraticNumberFields` | 400 | 165 | 662 |
| `QuadraticNumberFields/Examples` | 274 | 106 | 449 |
| `QuadraticNumberFields/Euclidean` | 52 | 25 | 93 |
| `Root` | 18 | 0 | 18 |
| **Total** | **1947** | **724** | **2671** |

## Prerequisites

- [Lean 4](https://leanprover.github.io/) `v4.29.0-rc2`
- [mathlib](https://github.com/leanprover-community/mathlib4) `v4.29.0-rc2`
- [elan](https://github.com/leanprover/elan) (Lean version manager)

## Build Instructions

```bash
cd Lean
lake exe cache get  # Download mathlib cache (required, speeds up build significantly)
lake build
```

## Worktree
```bash
git worktree add .worktrees/<prefix>/<feature> main -b <prefix>/<feature>
```

## History

This project was originally developed at [ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields). It has since been restructured and expanded in this repository.

## References

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
