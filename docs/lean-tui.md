# Lean-TUI Setup

[lean-tui](https://codeberg.org/wvhulle/lean-tui) provides a standalone terminal UI for visualizing Lean proofs and programs.

## Prerequisites

- Rust toolchain ([rustup](https://rustup.rs/))
- A code editor with Lean LSP support (Zed, VS Code, Helix, Neovim)

## Installation

```bash
cargo install lean-tui
```

Ensure `~/.cargo/bin` is in your `PATH`.

## Project Configuration

The `LeanPrism` dependency is already configured in `Lean/lakefile.toml`:

```toml
[[require]]
name = "LeanPrism"
git = "https://codeberg.org/wvhulle/lean-prism.git"
rev = "main"
```

The root module (`Lean/QuadraticNumberFields.lean`) imports `LeanPrism`, making it available to all submodules.

To fetch and build:

```bash
cd Lean
lake update LeanPrism
lake build LeanPrism
```

## Usage

1. Open a `.lean` file in your editor
2. Wait for the Lean LSP to finish loading
3. In a separate terminal, run:

```bash
lean-tui
```

4. Move your cursor in the editor -- lean-tui will display proof states and program visualizations automatically

## Editor-Specific Notes

| Editor | Trigger |
|--------|---------|
| Zed | Configure `lake serve` as LSP or install Lean extension |
| VS Code | Install [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4); cursor movement triggers updates |
| Helix | Works out of the box; `ctrl+x` or `space,k` triggers updates |
| Neovim | Configure `lake serve` as language server for `.lean` files |

## Keyboard Shortcuts (in lean-tui)

| Key | Action |
|-----|--------|
| `h/j/k/l` or arrows | Navigate hypotheses and goals |
| `[` / `]` | Switch display mode |
| `f` | File selection |
| `F` | Toggle follow mode |
| `g` | Go to definition |
| `y` | Copy to clipboard |
| `?` | Help |
| `q` | Quit |
