# AGENTS.md

Main rules and guidelines for AI agents working on this repository.

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

## Authors

- Name: Frankie Wang
- Email: git@frankie.wang
- GitHub: FrankieeW

## Workflow Guidelines

### Git Worktree
- Use `git worktree` to create a separate branch for each new feature or bug fix
- Follow the standard GitHub flow: create a pull request for such branches, get code review, and merge into main after approval

### Commit Messages
- Do not include Claude session URLs in commit messages
- Use conventional commit format: `type: description`

### Documentation
- Add module docstrings (`/-! ... -/`) to all source files
- Add definition docstrings (`/-- ... -/`) to public definitions
- Document main definitions and main theorems in module docstrings

### Lean Code Quality

1. **Always verify with lean-lsp-mcp first**: Run `lean_diagnostic_messages` on modified files until there are no errors or warnings
2. **Build only when needed**: Only run `lake build` if Lean files were actually modified
3. **Commit after verification**: Commit only after both lean-lsp-mcp passes AND (if applicable) `lake build` succeeds

### Website Documentation Anchors

- **Preserve** `-- ANCHOR: name --` and `-- ANCHOR_END:` comments - they mark sections extracted for website documentation
- Do not remove or modify these anchor comments
