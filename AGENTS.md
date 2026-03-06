# AGENTS.md

Main rules and guidelines for AI agents working on this repository.

## Project Overview

A Lean 4 formalization of quadratic number fields `Q(√d)` and the
classification of their ring of integers.

Core objects:
- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0`
- `QuadFieldParam d`: stores `Squarefree d` and `d ≠ 1`
- `QuadraticNumberFields (d : ℤ) [QuadFieldParam d] := Qsqrtd (d : ℚ)`

Main ring-of-integers theorems (`RingOfIntegers/Classification.lean`):
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- `ringOfIntegers_classification`

## Build Commands

```bash
cd Lean
lake exe cache get    # Download mathlib cache (required before first build)
lake build            # Build the project
```

Only run `lake build` if Lean files were actually modified. Use `lean_diagnostic_messages` (lean-lsp MCP) to check individual files first.

## Key Architecture

The Lean source lives under `Lean/QuadraticNumberFields/`. The base type is
`Qsqrtd`; `QuadraticNumberFields d` is the integer-parameter alias used by the
main theorems, with parameter validity gated by `QuadFieldParam d`.

- **`Basic.lean`** — Defines `Qsqrtd d` with trace, norm, and ℚ-embedding
- **`Instances.lean`** — Defines `QuadraticNumberFields d` and `Field`/`NumberField` instances
- **`Param.lean`** — `QuadFieldParam d` typeclass (squarefree `d ≠ 1`), instances for `-1`, `-3`, primes
- **`Rescale.lean`** — Isomorphisms between `Q(√d)` and `Q(√(c²d))`
- **`ParamUniqueness.lean`** — Uniqueness of the quadratic field parameter
- **`TotallyRealComplex.lean`** — Totally real / complex place behavior for `Q(√d)`
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

<!-- BEGIN BEADS INTEGRATION -->
## Issue Tracking with bd (beads)

This repository uses **bd (beads)** for local issue tracking and persistent
agent memory. Run `bd prime` for the current workflow context.

### Quick Reference

```bash
bd ready --json
bd create "Title" -t task -p 2 --json
bd show <id> --json
bd update <id> --claim --json
bd comments add <id> "note"
bd close <id> --reason "Completed" --json
bd dolt pull
bd dolt push
```

### Agent Rules

- Prefer `bd` over markdown TODO lists for active task tracking
- Use `bd` issue bodies and comments for durable working memory
- Use `bd update` and `bd comments add`; do not use `bd edit` in agent sessions
- Link newly discovered follow-up work with `--deps discovered-from:<parent-id>`
- Check `bd ready` before starting unclaimed work
- Prefer `--json` when a command will be parsed programmatically
- Do not rely on manual export/import for routine usage; Dolt is the primary backend

### Issue Conventions

- `task` for implementation, proofs, tests, docs, and refactors
- `bug` for broken behavior or regressions
- `feature` for new capabilities
- `epic` for larger parent work split into children
- Priorities use `0`-`4`, where `0` is the highest urgency

### Session Completion

When ending a work session:

1. Update or close the relevant `bd` issues
2. Run the required verification for any code changes
3. Push git changes normally
4. If Dolt remotes are configured, sync with `bd dolt push`
5. Check `git status`, `git config`, and `gh auth status` before wrapping up

For a fresh repository setup, use `bd init` as a human or `bd init --quiet` in
non-interactive agent workflows.

<!-- END BEADS INTEGRATION -->
