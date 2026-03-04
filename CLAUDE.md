# CLAUDE.md

This file provides guidance to Claude Code when working with this repository.

## Project Overview

A Lean 4 formalization of quadratic number fields Q(√d) and the classification of their ring of integers. Based on work extracted from `DedekindDomain`.

## Build Commands

```bash
cd Lean
lake exe cache get  # Download mathlib cache (required!)
lake build
```

## Architecture

```
QuadraticNumberFields/
├── Lean/                        # Lean formal proofs
│   ├── QuadraticNumberFields.lean    # Root module (imports Def)
│   └── QuadraticNumberFields/
│       ├── Basic.lean           # Basic definitions
│       ├── Def.lean             # Main definition of quadratic fields
│       ├── Param.lean           # Parameterization
│       ├── ParamUniqueness.lean # Uniqueness proofs
│       ├── FieldInstance.lean   # Field typeclass instances
│       ├── Rescale.lean         # Rescaling operations
│       ├── Euclidean/
│       │   └── Basic.lean       # Euclidean domain structure
│       └── RingOfIntegers/
│           ├── Classification.lean  # Main classification theorem
│           ├── HalfInt.lean
│           ├── Integrality.lean
│           ├── ModFour.lean
│           ├── Norm.lean
│           ├── ZOnePlusSqrtOverTwo.lean
│           └── Zsqrtd.lean
├── Verso/                       # Documentation generation
└── site/                        # Jekyll website
```

## Dependencies

- Lean 4 (v4.29.0-rc2)
- mathlib (v4.29.0-rc2)
- repl (v4.29.0-rc2)

## Status

Lean formalization complete - includes ring of integers classification for quadratic fields.
