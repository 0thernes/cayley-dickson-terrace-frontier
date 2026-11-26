# Cayley–Dickson Terrace Frontier (`0TH-2026-019`)

[![CI](https://github.com/0thernes/cayley-dickson-terrace-frontier/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/cayley-dickson-terrace-frontier/actions/workflows/ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20(Zero--Mathlib%20%C2%B7%206%20Kernels)-0072B2)](lean/formalization.yaml)
[![License: Apache-2.0 / CC-BY-4.0](https://img.shields.io/badge/License-Apache--2.0%20%2F%20CC--BY--4.0-009E73)](REUSE.toml)
[![Interactive 3D Observatory](https://img.shields.io/badge/WebGL%20Observatory-GitHub%20Pages-D55E00)](https://0thernes.github.io/cayley-dickson-terrace-frontier/)

**The Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation, and the Dimension-64 Hurwitz–Radon Rupture Across Generalized Cayley–Dickson Algebras**

*Author:* **Alexander Stephen Donahue** (Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`)  
*Maintenance status:* **Active** (v1.0.0 — frozen proof & manuscript archive; errata and community verification issues welcomed).

---

## Executive Highlights

This repository presents a **zero-Mathlib, six-kernel Lean 4.35.0 formalization**, **tri-language differential engine suite (Rust, strict ISO C11, Python)**, **interactive 3D WebGL observatory + Proof Blueprint**, and **17-page AMS-LaTeX white paper** proving four tightly coupled structural laws across the entire infinite tower of generalized Cayley–Dickson algebras $\mathrm{CD}_n(\gamma)$ ($\dim = 2^n$, $\gamma \in \{\pm 1\}^n$):

1. **Pillar 1 — Nilpotent Mirror Conservation (`T1a`–`T1e`, `[LEAN-6K]`):**
   - Every generalized basis sign cocycle factorizes as $\sigma_n^\gamma(i,j) = \sigma_n^{\mathrm{std}}(i,j)\,(-1)^{\mathrm{popcount}(i\,\&\,j\,\&\,\mathrm{flip}(\gamma))}$.
   - Every $2\times 2$ zero-divisor block determinant sign $\delta_n^\gamma(i,j,k)$ flips by $(-1)^{\mathrm{popcount}((i\oplus j)\,\&\,\mathrm{flip}(\gamma))}$, completely independent of $k$.
   - Non-nilpotent 2-blades keep their Euclidean nullity while nilpotent 2-blades undergo exact mirror inversion $\nu_n^\gamma(i,j) = 2^{n-1} - \nu_n^{\mathrm{std}}(i,j)$, conserving every mirror-pair histogram sum $H_n^\gamma(v) + H_n^\gamma(2^{n-1}-v)$ and pinning $H_n^\gamma(2^{n-2})$ across all $2^n$ signatures.
2. **Pillar 2 — The Dyadic-Palindromic Terrace Law & Sharp BDI Separation (`T2a`–`T2f`, `[LEAN-6K]`):**
   - Exact four-branch doubling recurrence for $\nu_{n+1}^{\mathrm{std}}$, yielding closed-form all-$n$ laws for total nullity mass $M_n = 8(2^{n-1}-1)(2^{n-2}-1)(2^{n-3}-1)$, zero-divisor-free counts $H_n^{\mathrm{std}}(0) = (6n-9)2^{n-2}+3$, exact even/odd bin interleaving $H_{n+1}^{\mathrm{std}}(8m) = H_{n+1}^{\mathrm{std}}(2^n-4-8m) = 2 H_n^{\mathrm{std}}(4m)$, interior palindromic symmetry, and exact top-bin jump $+3(2^n-2)$.
   - Sharp separation from the Biss–Dugger–Isaksen ceiling $2^n - 4n + 4$: equality holds **uniquely** at $n = 4$ ($4 = 4$) and strict separation holds for **all $n \ge 5$** ($12 < 16$ at $n = 5$, $28 < 44$ at $n = 6$).
   - **Universal All-Signature Midpoint 42 Law:** $H_n^\gamma(2^{n-2}) = 42 \cdot 2^{n-4}$ for **every $n \ge 4$** and **every signature $\gamma \in \{\pm 1\}^n$**.
3. **Pillar 3 — The Dimension-64 Hurwitz–Radon Bott Rupture (`T3a`–`T3d`, `[LEAN-6K]`):**
   - Exact doubling law of the right-compatibility graph $G_n^{\mathrm{comp}}$, uniqueness of the two universal right-multipliers $\{e_0, e_{2^{n-1}}\}$ ($\forall n \ge 4$), and exact clique number $\omega(G_n^{\mathrm{comp}}) = n + 5$ ($\forall n \ge 3$).
   - Saturates the Hurwitz–Radon ceiling $\rho(2^n)$ at dimensions $8, 16, 32$ ($8, 9, 10$), then ruptures irrevocably at **dimension 64** ($11 < 12 = \rho(64)$) with diverging deficit $\rho(2^n) - (n + 5) \ge n - 5$ for all $n \ge 6$, while an explicit doubling tower constructs $[2^{n-1}, 2(n+4), 2^n]$ pairs for all $n \ge 4$.
4. **Pillar 4 — Sedenion Triple-42 Duality, Pathion Symmetric Rupture & Base-Field Rigidity (`T4a`–`T4d`, `[LEAN-6K]` + `[EXACT-COMP]`):**
   - Exhaustive classification over all $2^{16} = 65{,}536$ sedenion coordinate subspaces: **42** bad affine 2-planes, **42** Box-Kite assessors forming $7 \times K_{2,2,2}$ (spectrum $\{4^7, 0^{21}, (-2)^{14}\}$), and **42** maximal 10D norm-multiplicative subspaces with exact Fano split $7 + 28 + 7 = 42$ and **0** subspaces of dimension $\ge 11$.
   - Exhaustive split-phase tables for $\mathrm{CD}_4(\gamma)$ ($1{:}1{:}7{:}7$) and $\mathrm{CD}_5(\gamma)$ ($4{\times}1 + 4{\times}7$) in Lean (`[LEAN-6K]`), extended to all 448 algebras of $\mathrm{CD}_6(\gamma)$–$\mathrm{CD}_8(\gamma)$ (discovering interior spectral gaps starting at $\dim = 64$) across Rust, C11, and Python (`[EXACT-COMP]`).
   - Exact HiGHS MILP certificate proving Pathion symmetric coordinate rupture $r_{\max}(\mathrm{CD}_5) = 14 < 16$ relative to Yiu's integral $[16,16,32]$ form (`[EXACT-COMP]`), certified $[14,14,32]$ and $[16,16,64]$ witnesses, and pure-intercalate integral-domain / Gaussian-integer ($\mathbb{Z}[i] \subset \mathbb{Q}(i)$) rigidity illuminating Zhang–Zhu (2026) (`[LEAN-6K]`).

> **Explore Live:** Open the zero-CDN interactive 3D Box-Kite & Terrace Observatory at **[0thernes.github.io/cayley-dickson-terrace-frontier](https://0thernes.github.io/cayley-dickson-terrace-frontier/)** or the interactive [Proof Dependency Blueprint](https://0thernes.github.io/cayley-dickson-terrace-frontier/blueprint.html).

---

## Usage Examples

### 1. Verify All 20 Lean 4.35.0 Targets & Strict Axiom Footprint
```bash
cd lean
lake build
lake build PalomarChallenge
lake env lean VerifyAxioms.lean
lake env leanchecker --fresh PalomarSolution
lake env leanchecker-paranoid --fresh PalomarSolution
```

### 2. Exhaustive 496-Algebra Audit in Rust (`CD_4`–`CD_8`, up to 256D)
```bash
cd rust
cargo clippy --all-targets -- -D warnings
cargo test --release
cargo run --release -- --verify-all
```

### 3. Strict ISO C11 Engine, Sanitizers (ASan/UBSan) & 100k Fuzzing
```bash
cd c
make clean test sanitize fuzz
./build/fuzz_cd_terrace 100000
./build/cd_terrace_cli --verify-all
```

### 4. Python Quickstart, Exact $\mathbb{Q}$ Oracle & Differential Test Suite
```bash
PYTHONPATH=src:. python examples/quickstart_demo.py
PYTHONPATH=src:. pytest -v tests/test_all.py
python scripts/check_readme_axioms.py
python scripts/check_citations.py
```

### 5. Reproduce Figures, Paper PDF & Checksums End-to-End
```bash
just reproduce
```

---

## Verbatim Lean 4.35.0 Kernel Axiom Audit (`results/lean_axioms.txt`)

Every one of the 20 Palomar Comparator headline targets (`T1a`–`T4d` + master conjunction), 4 pillar non-vacuity witnesses, and 6 adversarial boundary refutations (30 declarations total) depends **exclusively** on a subset of `{propext, Classical.choice, Quot.sound}` — zero `sorryAx`, zero `Lean.ofReduceBool`, zero `native_decide`, zero custom axioms:

```text
'CDTerrace.Palomar.prove_t1a' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t1b' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t1c' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t1d' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t1e' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t2a' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t2b' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t2c' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t2d' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t2e' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t2f' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t3a' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t3b' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t3c' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t3d' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t4a' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t4b' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t4c' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_t4d' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.Palomar.prove_all_terrace_theorems' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.nonvacuity_pillar1_split_sedenion' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.nonvacuity_pillar2_terrace_instances' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.nonvacuity_pillar3_dim64_rupture' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.nonvacuity_pillar4_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.refute_hurwitz_saturation_at_64' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.refute_sedenion_11d_coord_subspace' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.refute_twoblade_reaches_bdi_at_64' does not depend on any axioms
'CDTerrace.refute_split_preserves_individual_bins' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.refute_third_universal_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'CDTerrace.refute_gaussian_imaginary_intercalate' depends on axioms: [propext, Quot.sound]
```

---

## Repository Map

| Path | Description |
| --- | --- |
| [`lean/`](lean/) | Zero-Mathlib Lean 4.35.0 proof suite (`CDTerrace/`, `Challenge.lean`, `PalomarChallenge.lean`, `Solution.lean`, `PalomarSolution.lean`, `VerifyAxioms.lean`, `comparator.json`, `formalization.yaml`) |
| [`rust/`](rust/) | Zero-dependency Rust differential engine auditing all 496 algebras $\mathrm{CD}_4(\gamma)$–$\mathrm{CD}_8(\gamma)$ |
| [`c/`](c/) | Strict ISO C11 (`-Wall -Wextra -Wpedantic -Werror -Wshadow -Wconversion`) verifier, ASan/UBSan suite, 100k + libFuzzer harnesses |
| [`src/cd_terrace/`](src/cd_terrace/) & [`reference/`](reference/) | Exact Python engine + independent naive recursive / exact $\mathbb{Q}$ Gaussian elimination oracle |
| [`paper/`](paper/) & [`dist/`](dist/) | 17-page zero-warning AMS-LaTeX white paper, 5 Okabe-Ito vector figures, 24 live-verified BibTeX entries, frozen PDF & clean-room `arxiv_submission.tar.gz` |
| [`docs/site/`](docs/site/) | Zero-CDN interactive 3D Sedenion Box-Kite & Terrace Observatory (`index.html`) + Proof Blueprint (`blueprint.html`) |
| [`data/`](data/) & [`results/`](results/) | Frozen JSON computational certificates, `data/MANIFEST.sha256`, and `results/lean_axioms.txt` |
| [`CLAIMS.md`](CLAIMS.md) & [`LIMITATIONS.md`](LIMITATIONS.md) | Granular theorem-to-evidence ledger and explicit epistemic boundaries |

---

## Citation & Licensing

- **Code** (`lean/`, `rust/`, `c/`, `src/`, `reference/`, `tests/`, `scripts/`, `examples/`): **Apache-2.0** ([`LICENSE`](LICENSE)).
- **Paper, Figures, Data & Documentation** (`paper/`, `dist/`, `docs/`, `data/`, `*.md`): **CC-BY-4.0** ([`LICENSE-DOCS`](LICENSE-DOCS)).
- Machine-readable copyright & license coverage declared in [`REUSE.toml`](REUSE.toml) and citation metadata in [`CITATION.cff`](CITATION.cff).
