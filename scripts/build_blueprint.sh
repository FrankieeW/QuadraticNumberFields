#!/bin/bash

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="$REPO_ROOT/Lean"
BLUEPRINT_ROOT="$REPO_ROOT/blueprint"
BUILD_ROOT="$(mktemp -d)"

cleanup() {
  rm -rf "$BUILD_ROOT"
}

trap cleanup EXIT

if ! command -v uv >/dev/null 2>&1; then
  echo "uv is required to build the blueprint" >&2
  exit 1
fi

EXPECTED_VENV="VIRTUAL_ENV='$BLUEPRINT_ROOT/.venv'"
if [ ! -x "$BLUEPRINT_ROOT/.venv/bin/python3" ] || \
   [ ! -f "$BLUEPRINT_ROOT/.venv/bin/activate" ] || \
   ! grep -Fq "$EXPECTED_VENV" "$BLUEPRINT_ROOT/.venv/bin/activate"; then
  rm -rf "$BLUEPRINT_ROOT/.venv"
  uv venv "$BLUEPRINT_ROOT/.venv" --python 3.12
fi

# shellcheck disable=SC1091
source "$BLUEPRINT_ROOT/.venv/bin/activate"

export CFLAGS="${CFLAGS:-$(pkg-config --cflags graphviz 2>/dev/null || true)}"
export LDFLAGS="${LDFLAGS:-$(pkg-config --libs graphviz 2>/dev/null || true)}"

uv pip install pygraphviz leanblueprint plastex invoke

cp "$BLUEPRINT_ROOT/.venv"/lib/python*/site-packages/leanblueprint/templates/blueprint.sty "$BLUEPRINT_ROOT/src/"
cp "$BLUEPRINT_ROOT/.venv"/lib/python*/site-packages/leanblueprint/templates/extra_styles.css "$BLUEPRINT_ROOT/src/"

cp "$LEAN_ROOT/lakefile.toml" "$BUILD_ROOT/"
[ -f "$LEAN_ROOT/lake-manifest.json" ] && cp "$LEAN_ROOT/lake-manifest.json" "$BUILD_ROOT/"
cp "$LEAN_ROOT/lean-toolchain" "$BUILD_ROOT/"
cp "$LEAN_ROOT/QuadraticNumberFields.lean" "$BUILD_ROOT/"
cp -R "$LEAN_ROOT/QuadraticNumberFields" "$BUILD_ROOT/"
mkdir -p "$BUILD_ROOT/blueprint/src"
cp -R "$BLUEPRINT_ROOT/src/." "$BUILD_ROOT/blueprint/src/"
cp "$BLUEPRINT_ROOT/.venv"/lib/python*/site-packages/leanblueprint/templates/blueprint.sty "$BUILD_ROOT/blueprint/src/"
cp "$BLUEPRINT_ROOT/.venv"/lib/python*/site-packages/leanblueprint/templates/extra_styles.css "$BUILD_ROOT/blueprint/src/"

git -C "$BUILD_ROOT" init >/dev/null 2>&1

cd "$BUILD_ROOT"
leanblueprint web

rm -rf "$BLUEPRINT_ROOT/web" "$BLUEPRINT_ROOT/src/web"

if [ -d "$BUILD_ROOT/blueprint/web" ]; then
  cp -R "$BUILD_ROOT/blueprint/web" "$BLUEPRINT_ROOT/"
elif [ -d "$BUILD_ROOT/blueprint/src/web" ]; then
  rm -rf "$BLUEPRINT_ROOT/web"
  cp -R "$BUILD_ROOT/blueprint/src/web" "$BLUEPRINT_ROOT/web"
else
  echo "Blueprint build succeeded but no web output directory was found." >&2
  exit 1
fi
