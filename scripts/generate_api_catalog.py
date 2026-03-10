#!/usr/bin/env python3
"""Generate a source-driven API atlas for the Jekyll site."""

from __future__ import annotations

import html
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "QuadraticNumberFields"
OUTPUT = ROOT / "site" / "_includes" / "generated" / "api-catalog.html"

DECL_RE = re.compile(
    r"^(def|abbrev|theorem|lemma|class|structure|inductive)\s+([A-Za-z0-9_'.`₀₁₂₃₄₅₆₇₈₉⁻₊ₐ-ₜℤℚ𝓞ω]+)"
)
IMPORT_RE = re.compile(r"^import\s+(QuadraticNumberFields(?:\.[A-Za-z0-9_']+)+)\s*$")
TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_'.]*")


@dataclass
class Decl:
    kind: str
    name: str
    signature: str
    doc: str
    module: str
    file_path: str
    dependencies: list[str]
    math_form: str
    motivation: str


@dataclass
class ModuleInfo:
    name: str
    file_path: str
    summary: str
    imports: list[str]
    decls: list[Decl]


def module_name_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT)
    return ".".join(rel.with_suffix("").parts)


def clean_doc(doc: str) -> str:
    text = doc.replace("/--", "").replace("-/", "")
    lines = [line.strip(" -*") for line in text.splitlines()]
    return " ".join(part for part in lines if part)


def split_doc(doc: str) -> tuple[str, str]:
    if not doc:
        return "", ""
    parts = re.split(r"(?<=[.!?])\s+", doc, maxsplit=1)
    head = parts[0].strip()
    tail = parts[1].strip() if len(parts) > 1 else ""
    return head, tail


def should_use_doc_tail(tail: str) -> bool:
    if not tail:
        return False
    lowered = tail.lower()
    bad_prefixes = ("pr#", "**mathlib target", "mathlib target")
    return not lowered.startswith(bad_prefixes)


def fallback_math_form(kind: str, name: str, module: str) -> str:
    lname = name.lower()
    if name.endswith("Hom") or ".to" in name or lname.startswith("to"):
        return "A structure-preserving map between two quadratic-field models."
    if "equiv" in lname or "iso" in lname:
        return "An isomorphism identifying two mathematically equivalent models."
    if "norm" in lname:
        return "A norm formula or norm compatibility statement."
    if "trace" in lname:
        return "A trace formula for the quadratic extension."
    if "discr" in lname:
        return "A discriminant formula for the quadratic order."
    if "integral" in lname:
        return "An integrality criterion inside the quadratic field."
    if "mod_four" in lname or "dvd_four" in lname:
        return "A mod-4 arithmetic statement controlling the integral basis."
    if "dedekind" in lname:
        return "A criterion for when the order is Dedekind."
    if "factorization" in lname or "prime" in lname:
        return "An ideal-theoretic factorization or primality statement."
    if kind in {"def", "abbrev", "class", "structure", "inductive"}:
        return f"A Lean definition packaged in `{module}`."
    return f"A proved statement exported by `{module}`."


def fallback_motivation(kind: str, name: str, module: str) -> str:
    lname = name.lower()
    if kind in {"def", "abbrev"}:
        return "Introduces reusable notation or a concrete carrier so later proofs can stay in the algebraic hierarchy."
    if kind in {"class", "structure", "inductive"}:
        return "Packages assumptions as a first-class object that Lean can infer and transport automatically."
    if "equiv" in lname or "iso" in lname or name.endswith("Hom"):
        return "Packages the construction as a map Lean can reuse through `RingHom`, `AlgEquiv`, or rewriting lemmas."
    if "classification" in lname or "dedekind" in lname:
        return "Turns the classical theorem into a reusable endpoint for later algebraic and arithmetic arguments."
    if "integral" in lname or "norm" in lname or "trace" in lname:
        return "Bridges the textbook invariant with a form that is convenient for downstream automation and rewriting."
    return f"Provides a named lemma in `{module}` so later files can depend on it without reproving the argument."


def extract_module_summary(lines: list[str]) -> str:
    inside = False
    block: list[str] = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("/-!"):
            inside = True
            if stripped not in {"/-!", "/-! ", "/-!#"}:
                block.append(stripped[3:].strip())
            continue
        if inside and stripped == "-/":
            break
        if inside:
            block.append(stripped)
    prose: list[str] = []
    for line in block:
        if not line or line.startswith("#") or line.startswith("*"):
            if prose:
                break
            continue
        prose.append(line)
    summary = " ".join(prose).strip()
    return summary or "Source module in the quadratic number fields development."


def extract_imports(lines: list[str]) -> list[str]:
    imports = []
    for line in lines:
        match = IMPORT_RE.match(line.strip())
        if match:
            imports.append(match.group(1))
    return imports


def extract_signature(lines: list[str], start: int) -> str:
    parts: list[str] = []
    for idx in range(start, min(len(lines), start + 12)):
        stripped = lines[idx].strip()
        if idx > start and not stripped:
            break
        parts.append(stripped)
        if ":=" in stripped or stripped.endswith("where") or stripped.endswith(":") and idx > start:
            break
    signature = " ".join(parts)
    signature = re.sub(r"\s+", " ", signature).strip()
    return signature


def collect_modules() -> list[ModuleInfo]:
    files = sorted(LEAN_ROOT.rglob("*.lean"))
    raw_decls: list[tuple[Path, str, list[str], str, str, str]] = []
    simple_names: list[str] = []
    modules: list[ModuleInfo] = []

    for path in files:
        lines = path.read_text(encoding="utf-8").splitlines()
        summary = extract_module_summary(lines)
        imports = extract_imports(lines)
        pending_doc = ""
        decl_infos: list[tuple[str, str, str, str]] = []
        i = 0
        while i < len(lines):
            stripped = lines[i].strip()
            if stripped.startswith("/--"):
                doc_lines = [stripped]
                while not stripped.endswith("-/"):
                    i += 1
                    stripped = lines[i].strip()
                    doc_lines.append(stripped)
                pending_doc = clean_doc("\n".join(doc_lines))
                i += 1
                continue
            match = DECL_RE.match(lines[i])
            if match:
                kind, name = match.groups()
                signature = extract_signature(lines, i)
                decl_infos.append((kind, name, signature, pending_doc))
                simple_names.append(name.split(".")[-1])
                pending_doc = ""
            elif stripped and not stripped.startswith("/-") and not stripped.startswith("--"):
                pending_doc = ""
            i += 1

        module_name = module_name_from_path(path)
        modules.append(
            ModuleInfo(
                name=module_name,
                file_path=str(path.relative_to(ROOT)),
                summary=summary,
                imports=imports,
                decls=[],
            )
        )
        for kind, name, signature, doc in decl_infos:
            raw_decls.append((path, module_name, imports, kind, name, signature, doc))

    unique_simple_names = sorted({name for name in simple_names if len(name) >= 4}, key=len, reverse=True)
    simple_name_set = set(unique_simple_names)
    decls_by_module: dict[str, list[Decl]] = {module.name: [] for module in modules}

    for path, module_name, imports, kind, name, signature, doc in raw_decls:
        math_form, motivation = split_doc(doc)
        if not math_form:
            math_form = fallback_math_form(kind, name, module_name)
        if not should_use_doc_tail(motivation):
            motivation = fallback_motivation(kind, name, module_name)
        haystack = f"{signature} {doc}"
        dependencies: list[str] = []
        tokens = TOKEN_RE.findall(haystack)
        seen = set()
        for token in tokens:
            if token == name.split(".")[-1]:
                continue
            if token in simple_name_set and token not in seen:
                dependencies.append(token)
                seen.add(token)
            if len(dependencies) == 3:
                break
        if not dependencies:
            dependencies = [imp.split(".")[-1] for imp in imports[:3]]
        decls_by_module[module_name].append(
            Decl(
                kind=kind,
                name=name,
                signature=signature,
                doc=doc,
                module=module_name,
                file_path=str(path.relative_to(ROOT)),
                dependencies=dependencies,
                math_form=math_form,
                motivation=motivation,
            )
        )

    for module in modules:
        module.decls = decls_by_module[module.name]

    return modules


def tag(text: str, class_name: str = "api-chip") -> str:
    return f'<span class="{class_name}">{html.escape(text)}</span>'


def render_module_card(module: ModuleInfo) -> str:
    imports_html = "".join(tag(imp) for imp in module.imports) or tag("Mathlib-only")
    rows = []
    for decl in module.decls:
        deps = "".join(tag(dep, "api-chip api-chip-soft") for dep in decl.dependencies) or tag(
            "Foundational", "api-chip api-chip-soft"
        )
        source_path = html.escape(decl.file_path)
        rows.append(
            f"""
            <tr>
              <td>
                <div class="api-decl-name"><code>{html.escape(decl.name)}</code></div>
                <div class="api-decl-meta">{html.escape(decl.kind)} · <code>{source_path}</code></div>
                <details class="api-signature">
                  <summary>Lean signature</summary>
                  <pre><code>{html.escape(decl.signature)}</code></pre>
                </details>
              </td>
              <td>{html.escape(decl.math_form)}</td>
              <td>{html.escape(decl.motivation)}</td>
              <td>{deps}</td>
            </tr>
            """
        )

    return f"""
    <details class="api-module" open>
      <summary>
        <span class="api-module-title"><code>{html.escape(module.name)}</code></span>
        <span class="api-module-count">{len(module.decls)} declarations</span>
      </summary>
      <p class="api-module-summary">{html.escape(module.summary)}</p>
      <div class="api-module-meta">
        <span><strong>Source:</strong> <code>{html.escape(module.file_path)}</code></span>
        <span><strong>Depends on:</strong> {imports_html}</span>
      </div>
      <table class="api-table">
        <thead>
          <tr>
            <th>Declaration</th>
            <th>Mathematical Form</th>
            <th>Lean Motivation</th>
            <th>Dependency Focus</th>
          </tr>
        </thead>
        <tbody>
          {''.join(rows)}
        </tbody>
      </table>
    </details>
    """


def render(modules: list[ModuleInfo]) -> str:
    decl_counter = Counter()
    total_decls = 0
    for module in modules:
        for decl in module.decls:
            decl_counter[decl.kind] += 1
            total_decls += 1

    summary_cards = [
        ("Modules", str(len(modules))),
        ("Named declarations", str(total_decls)),
        ("Definitions", str(decl_counter["def"] + decl_counter["abbrev"])),
        ("Theorems and lemmas", str(decl_counter["theorem"] + decl_counter["lemma"])),
    ]
    cards_html = "".join(
        f'<div class="api-stat"><div class="api-stat-label">{html.escape(label)}</div>'
        f'<div class="api-stat-value">{html.escape(value)}</div></div>'
        for label, value in summary_cards
    )

    module_cards = "".join(render_module_card(module) for module in modules)
    dependency_cards = []
    for module in modules:
        imported = "".join(tag(imp, "api-chip api-chip-soft") for imp in module.imports) or tag(
            "Mathlib foundations", "api-chip api-chip-soft"
        )
        dependency_cards.append(
            f"""
            <div class="api-dependency-card">
              <h3><code>{html.escape(module.name)}</code></h3>
              <p>{html.escape(module.summary)}</p>
              <div class="api-chip-row">{imported}</div>
            </div>
            """
        )

    return f"""<!-- Auto-generated by scripts/generate_api_catalog.py. Do not edit by hand. -->
<div class="api-atlas">
  <div class="api-stat-grid">
    {cards_html}
  </div>

  <h2>Module Dependency Map</h2>
  <p>
    The dependency graph below is extracted from local project imports. Each declaration entry later
    adds a more focused dependency hint based on the symbols that appear in its source signature and docstring.
  </p>
  <div class="api-dependency-grid">
    {''.join(dependency_cards)}
  </div>

  <h2>Declaration Atlas</h2>
  <p>
    This section is generated from <code>QuadraticNumberFields</code>. Each module folds into a declaration table
    with four views of the same item: the Lean name, the mathematical form it captures, the reason it exists in Lean,
    and the dependency context it lives in.
  </p>
  {module_cards}
</div>
"""


def main() -> None:
    modules = collect_modules()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(render(modules), encoding="utf-8")


if __name__ == "__main__":
    main()
