# QuadraticNumberFields

A Lean 4 formalization of quadratic number fields Q(√d) and the classification of their ring of integers.

## Project Structure

```
QuadraticNumberFields/
├── README.md              # This file
├── CLAUDE.md              # Development guidance
├── Lean/                  # Lean formal proofs
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── QuadraticNumberFields.lean    # Root module
│   └── QuadraticNumberFields/        # Library modules
│       ├── Basic.lean
│       ├── Def.lean
│       ├── Param.lean
│       ├── ParamUniqueness.lean
│       ├── FieldInstance.lean
│       ├── Rescale.lean
│       ├── Euclidean/                # Euclidean domain proofs
│       └── RingOfIntegers/           # Ring of integers classification
├── Verso/                 # Documentation generation
└── site/                  # Jekyll website
```

## Build Instructions

```bash
cd Lean
lake exe cache get  # Download mathlib cache (required!)
lake build
```

## Mathematical Content

This project formalizes:
- Definition of quadratic number fields Q(√d)
- Ring of integers classification for quadratic fields
- Euclidean domain structure
- Norm computations

## Template

This repository follows the structure of [Polychromatic](https://github.com/b-mehta/Polychromatic).

## Quick Links

- [Lean](https://leanprover.github.io/)
- [mathlib](https://github.com/leanprover-community/mathlib)
- [Verso](https://github.com/leanprover/verso)

## Reference

- [Z[(1+sqrt(1+4k))/2] discussion (Lean Zulip)](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Z.5B.281.2Bsqrt.281.2B4k.29.29.2F2.5D/near/520523635)
