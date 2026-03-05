# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields `Q(√d)` and the classification
of their ring of integers, centered on the Lean objects `Qsqrtd`,
`QuadraticNumberFields`, and `QuadFieldParam`.

**[Documentation site](https://frankieew.github.io/QuadraticNumberFields)**

## Main Result

The final classification lives in
`Lean/QuadraticNumberFields/RingOfIntegers/Classification.lean`:

- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- `ringOfIntegers_classification`

Mathematically, for `d : ℤ` with `[QuadFieldParam d]`, the ring of integers
`𝓞 (Q(√d))` is classified as follows:

- If `d % 4 ≠ 1`, then `𝓞 (Q(√d)) ≃+* ℤ√d`.
- If `d % 4 = 1`, writing `d = 1 + 4k`, then `𝓞 (Q(√d)) ≃+* ℤ[(1+√d)/2]`.

Classical examples:
- **Gaussian integers** (`d = -1`): `𝓞 (Q(√(-1))) ≃+* ℤ[i]`
- **Eisenstein integers** (`d = -3`): `𝓞 (Q(√(-3))) ≃+* ℤ[ω]` where `ω = (1+√(-3))/2`

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
- Integrality criteria via trace and norm
- Euclidean domain classification framework: for squarefree `d < 0`, the ring `𝓞 (Q(√d))` is norm-Euclidean iff `d ∈ {-1, -2, -3, -7, -11}`
- Concrete verified examples for ℤ[√-5]: domain properties, ideal factorization, primality, and ramification/inertia computations

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
│       ├── Euclidean/
│       │   └── Basic.lean           # Euclidean domain classification framework
│       ├── Examples/
│       │   └── ZsqrtdNeg5/
│       │       ├── Basic.lean           # NoZeroDivisors/IsDomain for negative d
│       │       ├── Ideals.lean          # Ideal factorization and primality in ℤ[√-5]
│       │       └── RamificationInertia.lean  # Ramification indices and inertia degrees
│       └── RingOfIntegers/
│           ├── Classification.lean  # Main classification theorem
│           ├── HalfInt.lean         # Half-integer normal form
│           ├── Integrality.lean     # Integrality criteria
│           ├── ModFour.lean         # Modulo-4 arithmetic lemmas
│           ├── Norm.lean            # Norm computations
│           ├── ZOnePlusSqrtOverTwo.lean  # ℤ[(1+√d)/2] ring
│           └── Zsqrtd.lean          # ℤ√d ring
├── Verso/                 # Documentation generation
└── site/                  # Jekyll website (GitHub Pages)
```


## Code Statistics

| Module | Code Lines | Comment Lines | Total Lines |
|--------|------------|---------------|-------------|
| `QuadraticNumberFields/RingOfIntegers` | 758 | 299 | 1241 |
| `QuadraticNumberFields/Examples` | 519 | 124 | 718 |
| `QuadraticNumberFields` | 337 | 195 | 631 |
| `QuadraticNumberFields/Euclidean` | 48 | 25 | 89 |
| `Root` | 16 | 0 | 16 |
| **Total** | **1678** | **643** | **2321** |

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

## Template

This repository follows the structure of [Polychromatic](https://github.com/b-mehta/Polychromatic).

## History

This project was originally developed at [ClassificationOfIntegersOfQuadraticNumberFields](https://github.com/FrankieeW/ClassificationOfIntegersOfQuadraticNumberFields). It has since been restructured and expanded in this repository.

## References

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
