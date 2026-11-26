# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate the WCAG 2.2 AA Lean 4.35.0 Six-Kernel Proof Blueprint DAG at docs/site/blueprint.html."""

from __future__ import annotations

import html
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT_PATH = ROOT / "docs" / "site" / "blueprint.html"

NODES = [
    ("B0", "CDTerrace.Basic", "Foundational Sign Cocycle & Left Alternativity",
     "Defines cdSign, cdSignGamma, blockDelta, twobladeNullity, nullityHistGamma, rightCompat, hurwitzRadon; proves all-n ±1 valuation, anti-commutativity, and left alternativity e_i(e_i e_k) = -e_k.",
     [], "LEAN-6K"),
    ("T1a", "CDTerrace.MirrorConservation", "T1a: Sign-Cocycle Factorization",
     "∀ n flip i j < 2^n, σ_n^γ(i, j) = σ_n^std(i, j) · (-1)^popcount(i & j & flip).",
     ["B0"], "LEAN-6K"),
    ("T1b", "CDTerrace.MirrorConservation", "T1b: k-Independent Block-Sign Flip",
     "∀ n flip i j k, δ_n^γ(i, j, k) = (-1)^popcount((i⊕j) & flip) · δ_n^std(i, j, k).",
     ["T1a"], "LEAN-6K"),
    ("T1c", "CDTerrace.MirrorConservation", "T1c: Exact Nilpotency Equivalence",
     "(e_i + e_j)^2 = 0 ⇔ parityBits n ((i⊕j) & flip) = true for all n ≥ 1.",
     ["T1a"], "LEAN-6K"),
    ("T1d", "CDTerrace.MirrorConservation", "T1d: Nilpotent Mirror-Inversion Law",
     "Non-nilpotent ⇒ ν_n^γ = ν_n^std; nilpotent ⇒ ν_n^γ + ν_n^std = 2^(n-1).",
     ["T1b", "T1c"], "LEAN-6K"),
    ("T1e", "CDTerrace.MirrorConservation", "T1e: Mirror-Pair Conservation & Midpoint Invariance",
     "∀ n ≥ 1, flip, v ≤ 2^(n-1): H_n^γ(v) + H_n^γ(2^(n-1)-v) = H_n^std(v) + H_n^std(2^(n-1)-v), and H_n^γ(2^(n-2)) = H_n^std(2^(n-2)).",
     ["T1d"], "LEAN-6K"),
    ("T2a", "CDTerrace.TerraceLaw", "T2a: Six Pointwise Block-Sign Doubling Identities",
     "Exact doubling identities across lower-lo/hi, upper-lo/hi, three axis families, and cross-half complement.",
     ["B0"], "LEAN-6K"),
    ("T2b", "CDTerrace.TerraceLaw", "T2b: 4-Case 2-Blade Nullity Doubling Recurrence",
     "ν_{n+1}(i,j)=2ν_n(i,j); ν_{n+1}(i+h,j+h)=2ν_n(i,j); axis=0; cross ν_{n+1}(i,b+h)=2^n-4-2ν_n(i,b).",
     ["T2a"], "LEAN-6K"),
    ("T2c", "CDTerrace.TerraceLaw", "T2c: Mod-4 Quantization & BDI Separation (n ≥ 6)",
     "4 | ν_n(i,j), ν_n(i,j) ≤ 2^(n-1)-4, and strict 2-blade vs. Biss-Dugger-Isaksen gap 2^(n-1)-4 < 2^n-4n+4 for all n ≥ 6.",
     ["T2b"], "LEAN-6K"),
    ("T2d", "CDTerrace.TerraceLaw", "T2d: Exact All-n Total Nullity Mass (+4M_n - 4M_n)",
     "∀ n ≥ 3, M_n = 8(2^(n-1)-1)(2^(n-2)-1)(2^(n-3)-1) = 4 · #(bad affine 2-planes).",
     ["T2b", "T2c"], "LEAN-6K"),
    ("T2e", "CDTerrace.TerraceLaw", "T2e: Exact All-n Zero-Divisor-Free 2-Blade Count",
     "∀ n ≥ 3, H_n^std(0) = (6n - 9) · 2^(n-2) + 3.",
     ["T2b", "T2c"], "LEAN-6K"),
    ("T2f", "CDTerrace.TerraceLaw", "T2f: Interleaved Palindromic Terrace & Universal Split Midpoint 42",
     "H_{n+1}(8m)=2H_n(4m), H_{n+1}(2^n-4-8m)=2H_n(4m), exact interior palindrome, top jump 3(2^n-2), and ∀ n ≥ 4, ∀ γ: H_n^γ(2^(n-2)) = 42 · 2^(n-4).",
     ["T1e", "T2e"], "LEAN-6K"),
    ("T3a", "CDTerrace.HurwitzRupture", "T3a: Exact Graph-Nullity Unification",
     "For all n ≥ 1 and 1 ≤ j ≠ x < 2^n, rightCompat n j x = true ⇔ twobladeNullity n j x = 0.",
     ["T2a"], "LEAN-6K"),
    ("T3b", "CDTerrace.HurwitzRupture", "T3b: Universal Right-Multipliers = {e_0, e_{2^(n-1)}}",
     "For all n ≥ 4, a basis index is universally right-compatible iff j = 0 or j = 2^(n-1).",
     ["T3a", "T2b"], "LEAN-6K"),
    ("T3c", "CDTerrace.HurwitzRupture", "T3c: Exact Clique Number ω(G_n^comp) = n + 5",
     "For all n ≥ 3, every compatibility clique has size ≤ n + 5, attained by {0..7} ∪ {2^3, ..., 2^(n-1)}.",
     ["T3b"], "LEAN-6K"),
    ("T3d", "CDTerrace.HurwitzRupture", "T3d: Dimension-64 Hurwitz-Radon Bott Rupture",
     "Saturates ρ(2^n) at n ∈ {3,4,5} (8,9,10); strictly ruptures n + 5 < ρ(2^n) with gap ≥ n - 5 for ALL n ≥ 6.",
     ["T3c"], "LEAN-6K"),
    ("T3e", "CDTerrace.HurwitzRupture", "T3e: Universal Asymmetric Doubling Tower [2^(n-1), 2(n+4), 2^n]",
     "Constructs exact norm-multiplicative integer composition pairs [2^(n-1), 2(n+4), 2^n] inside CD_n for all n ≥ 4.",
     ["T3c"], "LEAN-6K"),
    ("T4a", "CDTerrace.FiniteCertificates", "T4a: Sedenion Triple-42 & Fano 7+28+7 Duality",
     "Over all 2^16 = 65,536 subspaces of S_16: 42/140 bad planes, 42 maximal 10D subspaces (7+28+7), 0 of dim ≥ 11.",
     ["B0"], "LEAN-6K"),
    ("T4b", "CDTerrace.FiniteCertificates", "T4b: 42 Box-Kites = 7 × K_{2,2,2} & 9D Subspace O ⊕ R e_8",
     "42 assessors, 4-regular, 7 disjoint octahedra by XOR signature 9..15, plus 9D norm-multiplicative O ⊕ R e_8.",
     ["B0"], "LEAN-6K"),
    ("T4c", "CDTerrace.FiniteCertificates", "T4c: Exhaustive Split-Phase Classifications CD_4(γ) & CD_5(γ)",
     "16 signatures of CD_4(γ) → 4 classes (1:1:7:7); 32 signatures of CD_5(γ) → 8 classes (4×1 + 4×7).",
     ["T1e", "T2b", "T2f"], "LEAN-6K"),
    ("T4d", "CDTerrace.FiniteCertificates", "T4d: [14,14,32] & [16,16,64] Witnesses + Pillar 4 Field Rigidity",
     "Certified Pathion 14D & Chingon 16D witnesses + pure-intercalate base-field rigidity over Z, Z[i], and any integral domain.",
     ["B0"], "LEAN-6K"),
    ("ALL", "PalomarSolution", "Master Palomar Conjunction (All 4 Pillars + 6 Adversarial Refutations)",
     "Checked across Lean 4.35.0 C++, leanchecker-paranoid, lean4lean, nanoda, con-leche, and con-ron.",
     ["T1e", "T2f", "T3d", "T3e", "T4a", "T4b", "T4c", "T4d"], "LEAN-6K"),
]


def build_html() -> str:
    cards = []
    for nid, mod, title, desc, deps, badge in NODES:
        deps_str = ", ".join(deps) if deps else "None (Foundational)"
        cards.append(
            f"""      <article class="node" data-id="{html.escape(nid)}" tabindex="0">
        <div class="node-head">
          <span class="nid">{html.escape(nid)}</span>
          <span class="badge">{html.escape(badge)}</span>
        </div>
        <h3>{html.escape(title)}</h3>
        <p class="mod"><code>{html.escape(mod)}</code></p>
        <p class="desc">{html.escape(desc)}</p>
        <p class="deps"><strong>Depends on:</strong> {html.escape(deps_str)}</p>
      </article>"""
        )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Proof Blueprint — Cayley-Dickson Terrace Frontier (Lean 4.35.0, 6 Kernels)</title>
  <style>
    :root {{
      --bg: #0b1020;
      --panel: #141c33;
      --border: #2a3960;
      --text: #eef2ff;
      --muted: #b8c4e0;
      --accent: #38bdf8;
      --ok: #34d399;
      --focus: #fbbf24;
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif;
      background: var(--bg);
      color: var(--text);
      line-height: 1.55;
    }}
    header {{
      padding: 2rem 1.5rem 1.25rem;
      border-bottom: 1px solid var(--border);
      background: linear-gradient(180deg, #10172c 0%, var(--bg) 100%);
    }}
    .wrap {{ max-width: 1180px; margin: 0 auto; }}
    h1 {{ margin: 0 0 0.4rem; font-size: 1.85rem; }}
    .sub {{ color: var(--muted); margin: 0 0 1rem; }}
    nav a {{
      color: var(--accent);
      text-decoration: none;
      margin-right: 1.25rem;
      font-weight: 600;
    }}
    nav a:hover, nav a:focus {{ text-decoration: underline; outline: 2px solid var(--focus); outline-offset: 2px; }}
    .summary {{
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(210px, 1fr));
      gap: 0.9rem;
      margin: 1.5rem 0;
    }}
    .stat {{
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 0.9rem 1rem;
    }}
    .stat strong {{ display: block; font-size: 1.35rem; color: var(--ok); }}
    .stat span {{ color: var(--muted); font-size: 0.9rem; }}
    .grid {{
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(320px, 1fr));
      gap: 1rem;
      padding: 0.5rem 0 3rem;
    }}
    .node {{
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 1rem 1.1rem;
      transition: border-color 0.15s ease;
    }}
    .node:hover, .node:focus {{ border-color: var(--accent); outline: none; }}
    .node-head {{ display: flex; justify-content: space-between; align-items: center; margin-bottom: 0.35rem; }}
    .nid {{ font-weight: 800; color: var(--accent); font-size: 0.95rem; }}
    .badge {{
      background: #064e3b;
      color: #a7f3d0;
      border: 1px solid #10b981;
      border-radius: 999px;
      padding: 0.12rem 0.6rem;
      font-size: 0.78rem;
      font-weight: 700;
    }}
    h3 {{ margin: 0.25rem 0 0.35rem; font-size: 1.05rem; }}
    .mod {{ margin: 0 0 0.45rem; color: #93c5fd; font-size: 0.86rem; }}
    .desc {{ margin: 0 0 0.6rem; color: var(--text); font-size: 0.93rem; }}
    .deps {{ margin: 0; color: var(--muted); font-size: 0.84rem; }}
    footer {{
      border-top: 1px solid var(--border);
      padding: 1.25rem 1.5rem;
      color: var(--muted);
      font-size: 0.88rem;
    }}
  </style>
</head>
<body>
  <header>
    <div class="wrap">
      <h1>Lean 4.35.0 Six-Kernel Proof Blueprint</h1>
      <p class="sub">Cayley-Dickson Terrace Frontier (0TH-2026-019) — Zero-Mathlib Constructive Dependency Graph</p>
      <nav aria-label="Primary navigation">
        <a href="index.html">← Interactive 3D Observatory</a>
        <a href="https://github.com/0thernes/cayley-dickson-terrace-frontier">GitHub Repository</a>
        <a href="https://github.com/0thernes/cayley-dickson-terrace-frontier/blob/main/docs/statement-fidelity.md">Statement Fidelity Audit</a>
      </nav>
    </div>
  </header>
  <main class="wrap">
    <section class="summary" aria-label="Verification metrics">
      <div class="stat"><strong>6 Kernels</strong><span>Lean C++, leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron</span></div>
      <div class="stat"><strong>Zero Mathlib</strong><span>Pure Lean 4.35.0 module system, 0 sorry, 0 native_decide</span></div>
      <div class="stat"><strong>22 DAG Nodes</strong><span>4 infinite all-n pillars + finite kernel certificates + 6 adversarial refutations</span></div>
      <div class="stat"><strong>Standard Axioms</strong><span>Strictly within {{propext, Classical.choice, Quot.sound}}</span></div>
    </section>
    <section class="grid" aria-label="Theorem dependency graph">
{chr(10).join(cards)}
    </section>
  </main>
  <footer>
    <div class="wrap">
      Author: Alexander Stephen Donahue (ORCID 0009-0006-8168-9648) · Code: Apache-2.0 · Docs: CC-BY-4.0
    </div>
  </footer>
</body>
</html>
"""


def main() -> None:
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_bytes(build_html().encode("utf-8"))
    print(f"Generated {OUT_PATH.relative_to(ROOT)} ({OUT_PATH.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
