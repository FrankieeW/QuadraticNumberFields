---
layout: default
title: Getting Started
---

# Getting Started

This guide will help you get started with the QuadraticNumberFields formalization project.

## Prerequisites

### Required Software

1. **Lean 4** (v4.29.0-rc2)
   - Install via [elan](https://github.com/leanprover/elan)
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Git**
   - For cloning the repository
   ```bash
   # Ubuntu/Debian
   sudo apt-get install git

   # macOS
   brew install git
   ```

3. **VS Code** (recommended)
   - Download from [code.visualstudio.com](https://code.visualstudio.com/)
   - Install the [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

### Recommended Background

**Mathematics:**
- Basic abstract algebra (groups, rings, fields)
- Elementary number theory
- Familiarity with $\mathbb{Q}(\sqrt{d})$ notation

**Lean:**
- Basic familiarity with dependent types (helpful but not required)
- Willingness to learn!

## Installation

### Quick Start

```bash
# Clone the repository
git clone https://github.com/FrankieeW/QuadraticNumberFields.git
cd QuadraticNumberFields

# Navigate to Lean directory
cd Lean

# Download mathlib cache (important!)
lake exe cache get

# Build the project
lake build
```

### Expected Output

The build should complete without errors:
```
Building QuadraticNumberFields
...
Build completed successfully
```

**Note:** The first `lake exe cache get` may take several minutes as it downloads precompiled mathlib binaries.

## Project Structure

```
QuadraticNumberFields/
├── Lean/                          # Main formalization
│   ├── QuadraticNumberFields.lean # Entry point
│   └── QuadraticNumberFields/
│       ├── Basic.lean             # Core definitions
│       ├── Def.lean               # Main type definition
│       ├── RingOfIntegers/        # Classification theorem
│       │   ├── Classification.lean
│       │   ├── Zsqrtd.lean
│       │   └── ...
│       └── ...
├── site/                          # Documentation website
└── README.md
```

## Your First Exploration

### Opening in VS Code

```bash
cd QuadraticNumberFields
code .
```

### Navigate to Key Files

1. **Start with the main definition:**
   - Open `Lean/QuadraticNumberFields/Def.lean`
   - This defines `QuadraticNumberFields d`

2. **Explore the classification theorem:**
   - Open `Lean/QuadraticNumberFields/RingOfIntegers/Classification.lean`
   - See the main result: `ringOfIntegers_classification`

3. **Check out examples:**
   - Gaussian integers: Look for `Zsqrtd (-1)`
   - See norm computations and unit criteria

### Interactive Theorem Proving

Lean provides **interactive feedback** as you navigate:

1. **Hover over definitions** to see their types
2. **Click on theorem names** to jump to their proofs
3. **See goals** in the Lean Infoview panel (right side in VS Code)

### Example: Exploring a Definition

Open `Lean/QuadraticNumberFields/Def.lean`:

```lean
/-- The quadratic number field Q(√d) -/
def QuadraticNumberFields (d : ℤ) := Qsqrtd d
```

**Try:**
- Hover over `QuadraticNumberFields` to see its type
- Ctrl+click (Cmd+click on Mac) on `Qsqrtd` to jump to its definition
- See how it's defined in terms of `QuadraticAlgebra`

## Building Intuition

### Understanding the Classification

The main theorem states:

```lean
theorem ringOfIntegers_classification (d : ℤ) [QuadFieldParam d] :
    (d % 4 ≠ 1 ∧ Nonempty (𝓞 (QuadraticNumberFields d) ≃+* Zsqrtd d)) ∨
    (∃ k : ℤ, d = 1 + 4 * k ∧
      Nonempty (𝓞 (QuadraticNumberFields d) ≃+* ZOnePlusSqrtOverTwo k))
```

**Reading this:**
- `d % 4 ≠ 1` means $d \not\equiv 1 \pmod{4}$
- `≃+*` denotes a ring isomorphism
- `𝓞` is the ring of integers
- `Zsqrtd d` represents $\mathbb{Z}[\sqrt{d}]$
- `ZOnePlusSqrtOverTwo k` represents $\mathbb{Z}\left[\frac{1+\sqrt{1+4k}}{2}\right]$

### Working with Examples

#### Gaussian Integers

```lean
-- d = -1, so -1 % 4 = 3 ≠ 1
-- Therefore: 𝓞(ℚ(i)) ≃ ℤ[i]
example : 𝓞 (QuadraticNumberFields (-1)) ≃+* Zsqrtd (-1) :=
  sorry  -- Proved in the formalization!
```

#### Eisenstein Integers

```lean
-- d = -3, so -3 % 4 = 1
-- Therefore: 𝓞(ℚ(√-3)) ≃ ℤ[(1+√-3)/2]
example : ∃ k, (-3) = 1 + 4 * k := ⟨-1, by norm_num⟩
```

## Next Steps

### Learning Path

1. **Read the documentation:**
   - [Mathematical Background](math.html) - Theory behind quadratic fields
   - [Examples](examples.html) - Concrete examples to build intuition
   - [API Documentation](api.html) - Reference for all definitions

2. **Explore the code:**
   - Read through the Lean files
   - Try modifying examples
   - Add `#check` and `#eval` commands to experiment

3. **Try exercises:**
   - Verify the norm formula for $\mathbb{Z}[i]$
   - Show $\phi = \frac{1+\sqrt{5}}{2}$ is in $\mathcal{O}_{\mathbb{Q}(\sqrt{5})}$
   - Find the units in $\mathbb{Z}[\sqrt{2}]$

### Useful Commands

**In Lean files:**

```lean
#check QuadraticNumberFields  -- See the type
#print QuadraticNumberFields  -- See the definition

-- Evaluate norms
#eval (3 : ℤ) ^ 2 - 2 * (2 : ℤ) ^ 2  -- Norm of 3 + 2√2

-- Check theorem statements
#check ringOfIntegers_classification
```

### Common Patterns

**Type classes for automatic instance resolution:**
```lean
variable (d : ℤ) [QuadFieldParam d]
-- This automatically knows d is square-free and d ≠ 1
```

**Constructing elements:**
```lean
-- Element of ℤ[√d]
def z : Zsqrtd 2 := ⟨3, 2⟩  -- represents 3 + 2√2

-- Compute norm
#check Zsqrtd.norm z  -- Should be 3² - 2·2² = 9 - 8 = 1
```

## Getting Help

### Resources

- **Lean Zulip Chat:** [leanprover.zulipchat.com](https://leanprover.zulipchat.com/)
  - #new members - For beginners
  - #maths - For mathematical formalization
  - Very responsive and helpful community!

- **Lean 4 Documentation:**
  - [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
  - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

- **This Project:**
  - [GitHub Issues](https://github.com/FrankieeW/QuadraticNumberFields/issues) - Ask questions or report issues
  - [Resources Page](resources.html) - Additional references

### Troubleshooting

**Build fails:**
```bash
# Clear cache and rebuild
lake clean
lake exe cache get
lake build
```

**VS Code extension not working:**
1. Ensure Lean 4 extension is installed
2. Restart VS Code
3. Check that `lean-toolchain` file exists in project root

**Slow performance:**
- Make sure you ran `lake exe cache get` to download precompiled mathlib
- Close other applications to free up memory
- Consider increasing VS Code memory limit

## Contributing

Interested in contributing? Great! See [Resources](resources.html#contributing) for areas where we need help.

**Quick contribution workflow:**
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run `lake build` to verify
5. Submit a pull request

## What's Next?

After getting comfortable with the basics:

1. **Explore advanced topics:**
   - [Formalization Details](formalization.html) - Design decisions and techniques
   - Study the proofs in `Classification.lean`

2. **Try extending the formalization:**
   - Add more examples
   - Prove additional properties
   - Compute class numbers

3. **Connect with the community:**
   - Share your findings on Zulip
   - Write about your experience
   - Help others get started!

[← Back to Home](index.html)
