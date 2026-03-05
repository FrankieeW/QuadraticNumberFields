# AGENTS.md

Main rules and guidelines for AI agents working on this repository.

## Project Overview

A Lean 4 formalization of quadratic number fields Q(√d) and the classification of their ring of integers. The main result: for squarefree `d ≠ 1`, `𝓞(Q(√d)) ≃+* ℤ√d` when `d % 4 ≠ 1`, and `𝓞(Q(√d)) ≃+* ℤ[(1+√d)/2]` when `d % 4 = 1`.

## Build Commands

```bash
cd Lean
lake exe cache get    # Download mathlib cache (required before first build)
lake build            # Build the project
```

Only run `lake build` if Lean files were actually modified. Use `lean_diagnostic_messages` (lean-lsp MCP) to check individual files first.

## Key Architecture

The Lean source lives under `Lean/QuadraticNumberFields/`. The core type is `Qsqrtd d := QuadraticAlgebra ℚ d 0` (from mathlib). Everything flows through the `QuadFieldParam d` typeclass which gates the squarefree/non-one requirements.

- **`Basic.lean`** — Defines `Qsqrtd d` with trace, norm, and ℚ-embedding
- **`Param.lean`** — `QuadFieldParam d` typeclass (squarefree `d ≠ 1`), instances for `-1`, `-3`, primes
- **`Def.lean`** — Root import aggregating Basic, Rescale, Param, FieldInstance, ParamUniqueness
- **`FieldInstance.lean`** — Field typeclass instances for `Qsqrtd d`
- **`Rescale.lean`** — Isomorphisms between `Q(√d)` and `Q(√(c²d))`
- **`ParamUniqueness.lean`** — Uniqueness of the quadratic field parameter
- **`RingOfIntegers/`** — Classification theorem:
  - `Integrality.lean` — `IsIntegralClosure` constructions, half-integer normal form
  - `ModFour.lean` — Modulo-4 arithmetic lemmas
  - `Zsqrtd.lean` — ℤ√d ring and its embedding into Q(√d)
  - `ZOnePlusSqrtOverTwo.lean` — ℤ[(1+√d)/2] ring
  - `HalfInt.lean` — Half-integer normal form
  - `Norm.lean` — Norm computations
  - `Classification.lean` — Final `ringOfIntegers_classification` theorem
- **`Euclidean/Basic.lean`** — Norm-Euclidean classification: `d ∈ {-1, -2, -3, -7, -11}` iff norm-Euclidean
- **`Examples/`** — Concrete verified examples:
  - `ZsqrtdNeg5/Basic.lean` — General `NoZeroDivisors`/`IsDomain` for negative `d`
  - `ZsqrtdNeg5/Ideals.lean` — Ideal factorization and primality in ℤ[√-5]
  - `ZsqrtdNeg5/RamificationInertia.lean` — Ramification indices and inertia degrees

### Other Components

- **`Verso/`** — Documentation generation using Verso/Subverso (separate Lake project: `cd Verso && lake build docs`)
- **`site/`** — Jekyll website for GitHub Pages

## Dependencies

- Lean 4 v4.29.0-rc2, mathlib v4.29.0-rc2, repl v4.29.0-rc2
- Linter options: `weak.linter.mathlibStandardSet = true`, `relaxedAutoImplicit = false` (in `lakefile.toml`)

## Authors

- Name: Frankie Wang
- Email: git@frankie.wang
- GitHub: FrankieeW
- Should check gh and git config and status after every session to ensure commits are properly attributed

## Workflow Guidelines

### Git Worktree
- Use `git worktree` to create a separate branch for each new feature or bug fix
- Follow standard GitHub flow: PR, code review, merge into main

### Commit Messages
- Do not include Claude session URLs in commit messages
- Use conventional commit format: `type: description`

### Documentation
- Add module docstrings (`/-! ... -/`) to all source files with `## Main Definitions` and `## Main Theorems` sections
- Add definition docstrings (`/-- ... -/`) to public definitions

### Lean Code Quality

1. **Always verify with lean-lsp-mcp first**: Run `lean_diagnostic_messages` on modified files until there are no errors or warnings
2. **Build only when needed**: Only run `lake build` if Lean files were actually modified
3. **Commit after verification**: Commit only after both lean-lsp-mcp passes AND (if applicable) `lake build` succeeds

### Website Documentation Anchors

- **Preserve** `-- ANCHOR: name --` and `-- ANCHOR_END:` comments — they mark sections extracted for website documentation
- Do not remove or modify these anchor comments
