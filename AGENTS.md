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

**IMPORTANT**: This project uses **bd (beads)** for ALL issue tracking. Do NOT use markdown TODOs, task lists, or other tracking methods.

### Why bd?

- Dependency-aware: Track blockers and relationships between issues
- Git-friendly: Dolt-powered version control with native sync
- Agent-optimized: JSON output, ready work detection, discovered-from links
- Prevents duplicate tracking systems and confusion

### Quick Start

**Check for ready work:**

```bash
bd ready --json
```

**Create new issues:**

```bash
bd create "Issue title" --description="Detailed context" -t bug|feature|task -p 0-4 --json
bd create "Issue title" --description="What this issue is about" -p 1 --deps discovered-from:bd-123 --json
```

**Claim and update:**

```bash
bd update <id> --claim --json
bd update bd-42 --priority 1 --json
```

**Complete work:**

```bash
bd close bd-42 --reason "Completed" --json
```

### Issue Types

- `bug` - Something broken
- `feature` - New functionality
- `task` - Work item (tests, docs, refactoring)
- `epic` - Large feature with subtasks
- `chore` - Maintenance (dependencies, tooling)

### Priorities

- `0` - Critical (security, data loss, broken builds)
- `1` - High (major features, important bugs)
- `2` - Medium (default, nice-to-have)
- `3` - Low (polish, optimization)
- `4` - Backlog (future ideas)

### Workflow for AI Agents

1. **Check ready work**: `bd ready` shows unblocked issues
2. **Claim your task atomically**: `bd update <id> --claim`
3. **Work on it**: Implement, test, document
4. **Discover new work?** Create linked issue:
   - `bd create "Found bug" --description="Details about what was found" -p 1 --deps discovered-from:<parent-id>`
5. **Complete**: `bd close <id> --reason "Done"`

### Auto-Sync

bd automatically syncs via Dolt:

- Each write auto-commits to Dolt history
- Use `bd dolt push`/`bd dolt pull` for remote sync
- No manual export/import needed!

### Important Rules

- ✅ Use bd for ALL task tracking
- ✅ Always use `--json` flag for programmatic use
- ✅ Link discovered work with `discovered-from` dependencies
- ✅ Check `bd ready` before asking "what should I work on?"
- ❌ Do NOT create markdown TODO lists
- ❌ Do NOT use external issue trackers
- ❌ Do NOT duplicate tracking systems

For more details, see README.md and docs/QUICKSTART.md.

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds

<!-- END BEADS INTEGRATION -->
