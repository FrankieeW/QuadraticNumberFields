# AGENTS.md

Main rules and guidelines for AI agents working on this repository.

## Project Overview

A Lean 4 formalization of quadratic number fields `Q(√d)` and the
classification of their ring of integers.

Core objects:
- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0`
- Parameters: `[Fact (Squarefree d)] [Fact (d ≠ 1)]` (explicit Fact instances)

Main ring-of-integers theorems (`RingOfIntegers/Classification.lean`):
- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- `ringOfIntegers_classification`

## Build Commands

```bash
lake exe cache get    # Download mathlib cache (required before first build)
lake build            # Build the project
```

Only run `lake build` if Lean files were actually modified. Use `lean_diagnostic_messages` (lean-lsp MCP) to check individual files first.

## Key Architecture

The Lean source lives under `QuadraticNumberFields/`. The base type is
`Qsqrtd`; parameters are provided via explicit `[Fact (Squarefree d)]` and
`[Fact (d ≠ 1)]` instances rather than a bundled typeclass.

- **`Basic.lean`** — Defines `Qsqrtd d` with trace, norm, and ℚ-embedding
- **`Instances.lean`** — `Field`/`NumberField` instances for `Qsqrtd`
- **`Parameters.lean`** — Common `Fact` instances (squarefree, `d ≠ 1`), rescaling isomorphisms, and parameter uniqueness
- **`TotallyRealComplex.lean`** — Totally real / complex place behavior for `Q(√d)`
- **`RingEquiv.lean`** — Dedekind domain transfer via ring equivalences
- **`RingOfIntegers/`** — Classification theorem:
  - `Integrality.lean` — `IsIntegralClosure` constructions, half-integer normal form
  - `ModFour.lean` — Modulo-4 arithmetic lemmas
  - `Zsqrtd.lean` — ℤ√d ring and its embedding into Q(√d)
  - `ZOnePlusSqrtOverTwo.lean` — ℤ[(1+√d)/2] ring
  - `HalfInt.lean` — Half-integer normal form
  - `Norm.lean` — Norm computations
  - `Discriminant.lean` — Discriminant formula for quadratic fields
  - `Classification.lean` — Final `ringOfIntegers_classification` theorem
  - `ZsqrtdMathlibInstances.lean` — Dedekind domain characterization for mathlib's `Zsqrtd`
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

### mathlib Contributions (Bidirectional Sync)

This project maintains a **bidirectional sync** with mathlib PRs:

#### Active PRs

| PR | Topic | Status | Key Files |
|----|-------|--------|-----------|
| [#36347](https://github.com/leanprover-community/mathlib4/pull/36347) | `Qsqrtd` definition, `IsQuadraticField` | OPEN | `NumberTheory/QuadraticField/Basic.lean` |
| [#36387](https://github.com/leanprover-community/mathlib4/pull/36387) | Parameter uniqueness | OPEN | `NumberTheory/QuadraticField/Basic.lean` |

#### Project → mathlib Flow

When adding features that belong in mathlib:

1. **Develop in this project first** — iterate faster with local builds
2. **Identify mathlib-scope content**:
   - ✅ Basic definitions: `Qsqrtd`, `IsQuadraticField`, trace/norm
   - ✅ General lemmas: squarefree, rescaling, parameter uniqueness
   - ❌ Project-specific: ring of integers classification, discriminant formula (too advanced)
3. **Port to PR**: Copy relevant code to mathlib PR, adapt to mathlib style
4. **Update PR description** with link to project commit

```bash
# Check PR diff vs project
gh pr diff 36347 --repo leanprover-community/mathlib4 > /tmp/pr.diff
diff QuadraticNumberFields/Basic.lean <(gh pr view 36347 --repo leanprover-community/mathlib4 --json files --jq '.files[].path' | xargs cat)
```

#### mathlib PR → Project Flow

When PR receives review feedback:

1. **Address review in PR first** — mathlib standards take priority
2. **Sync back to project** after changes are approved:
   ```bash
   # After addressing review in PR, sync the change pattern back
   # Example: if reviewer asked to generalize trace, update project's trace definition too
   ```
3. **Document sync**: Note in project commit which PR review was addressed

#### Sync Checklist

Before syncing, verify:
- [ ] Definition signatures match (type parameters, instances)
- [ ] Docstrings are compatible (mathlib uses stricter format)
- [ ] No project-only dependencies (e.g., `CommonInstances.lean`)
- [ ] Test with `lake build` in both repos

#### Content Classification

| Content | mathlib? | Project-only? |
|---------|----------|---------------|
| `Qsqrtd d = QuadraticAlgebra ℚ d 0` | ✅ | — |
| `IsQuadraticField` predicate | ✅ | — |
| Trace/norm basic lemmas | ✅ | — |
| Rescale isomorphisms | ✅ | — |
| Parameter uniqueness | ✅ | — |
| Ring of integers classification | ❌ | ✅ (future separate PR) |
| Discriminant formula | ❌ | ✅ (future separate PR) |
| Dedekind domain for `Zsqrtd` | ❌ | ✅ (future separate PR) |
| Euclidean domain classification | ❌ | ✅ |
| Ideal theory examples | ❌ | ✅ |

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

## Lean 4 & mathlib Style

Use the `lean4` and `mathlib-style` skills.
