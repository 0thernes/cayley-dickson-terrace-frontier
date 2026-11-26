# Cayley–Dickson Terrace Frontier (`0TH-2026-019`)

[![CI](https://github.com/0thernes/cayley-dickson-terrace-frontier/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/cayley-dickson-terrace-frontier/actions/workflows/ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20(Zero--Mathlib%20%C2%B7%206%20Kernels)-0072B2)](lean/formalization.yaml)
[![License: Apache-2.0 / CC-BY-4.0](https://img.shields.io/badge/License-Apache--2.0%20%2F%20CC--BY--4.0-009E73)](REUSE.toml)
[![Interactive 3D Observatory](https://img.shields.io/badge/WebGL%20Observatory-GitHub%20Pages-D55E00)](https://0thernes.github.io/cayley-dickson-terrace-frontier/)

**The Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation, and the Dimension-64 Hurwitz–Radon Rupture Across Generalized Cayley–Dickson Algebras**

*This is the title of the frozen v1.0.0 manuscript.* The "dimension-64 rupture" in the title concerns coordinate right-multiplier families in the Euclidean $\mathrm{CD}_n$ only. It compares the bound $n+5$ with the classical formula for $\rho(2^n)$; it says nothing about general bilinear maps. See [Scope of the Lean statements](#scope-of-the-lean-statements) and [`ERRATA.md`](ERRATA.md).

*Author:* **Alexander Stephen Donahue** (Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`)  
*Maintenance status:* **Active** (v1.0.0 — frozen proof & manuscript archive; errata and community verification issues welcomed).

---

## Summary

This repository contains a zero-Mathlib Lean 4.35.0 formalization, differential checkers in Rust, ISO C11 and Python, an interactive WebGL page with a proof blueprint, and a 17-page manuscript. The results are all-$n$ counting identities for the nullities of 2-blades $e_i+e_j$ in the explicit Cayley–Dickson sign table of $\mathrm{CD}_n(\gamma)$ ($\dim = 2^n$, $\gamma \in \{\pm 1\}^n$), the bound $n+5$ for coordinate right-multiplier families in the Euclidean $\mathrm{CD}_n$, and finite certificates for the sedenions, pathions and chingons. Pillar 1 and the midpoint law `T2f` hold for every signature $\gamma$; the rest of Pillar 2 and all of Pillar 3 concern the Euclidean signature only.

### Scope of the Lean statements

- The Lean development defines no algebra, linear map or kernel. It proves statements about the explicit sign table (`cdSign`, `cdSignGamma`) and about block counts. `twobladeNullity` is half the number of indices $k$ for which the $2\times 2$ block of left multiplication by $e_i+e_j$ on $\{e_k, e_{k\oplus i\oplus j}\}$ is singular. That this count equals $\dim \mathrm{Ann}(e_i+e_j)$ is a lemma proved in the paper (the $2\times 2$ block argument), not in Lean.
- Results tagged `[LEAN-6K]` are kernel-checked by Lean (`lake build`, `leanchecker`, `leanchecker-paranoid`); CI also replays them with `lake check --paranoid` and `lake comparator --paranoid` on 6 kernels. The 30 audited declarations use at most `propext`, `Classical.choice` and `Quot.sound` (listed below).
- Results tagged `[EXACT-COMP]` rest on exact computation outside Lean (Rust, C11, Python and a HiGHS MILP certificate).
- Prior work. The divisibility $4 \mid \nu$ is the 2-blade case of Moreno's theorem that only multiples of four occur as annihilator dimensions in Cayley–Dickson algebras (as stated by Biss, Dugger and Isaksen, arXiv:math/0511691); the Lean proof is an independent re-proof for 2-blades. The 42 sedenion assessors and their 7 box-kites are due to de Marrais (arXiv:math/0011260). Zhilina (Int. J. Algebra Comput. 31 (2021); arXiv:2608.28176) classifies the zero divisors whose two components are standard basis elements up to sign; the overlap with `T1c`, `T2a` and `T2c` has not been assessed. The manuscript cites neither the Moreno divisibility for `T2b` nor Zhilina; see [`ERRATA.md`](ERRATA.md).

### Results

1. **Pillar 1 — Signature change and 2-blade nullities (`T1a`–`T1e`, `[LEAN-6K]`, all $n$, all $\gamma$):**
   - The generalized sign table factorizes as $\sigma_n^\gamma(i,j) = \sigma_n^{\mathrm{std}}(i,j)\,(-1)^{\mathrm{popcount}(i\,\&\,j\,\&\,\mathrm{flip}(\gamma))}$.
   - The sign $\delta_n^\gamma(i,j,k)$ of each $2\times 2$ block determinant flips by $(-1)^{\mathrm{popcount}((i\oplus j)\,\&\,\mathrm{flip}(\gamma))}$, independently of $k$.
   - Hence the block-count nullity is either kept, $\nu_n^\gamma(i,j) = \nu_n^{\mathrm{std}}(i,j)$, or replaced by $2^{n-1} - \nu_n^{\mathrm{std}}(i,j)$. The mirror-pair sums $H_n^\gamma(v) + H_n^\gamma(2^{n-1}-v)$ and the midpoint bin $H_n^\gamma(2^{n-2})$ do not depend on $\gamma$.
   - `T1c` states only the scalar part of $(e_i+e_j)^2$: $\sigma_n^\gamma(i,i)+\sigma_n^\gamma(j,j) = 0 \iff \mathrm{parity}_n((i\oplus j)\,\&\,\mathrm{flip}(\gamma)) = 1$. The cross term is not part of the Lean statement.
2. **Pillar 2 — Euclidean nullity recurrence and closed forms (`T2a`–`T2e`) and the midpoint law (`T2f`), `[LEAN-6K]`:**
   - A four-branch doubling recurrence for $\nu_{n+1}^{\mathrm{std}}$ gives closed forms for all $n$: total nullity mass $M_n = 8(2^{n-1}-1)(2^{n-2}-1)(2^{n-3}-1)$, the count $H_n^{\mathrm{std}}(0) = (6n-9)2^{n-2}+3$ of 2-blades with nullity $0$, the bin interleaving $H_{n+1}^{\mathrm{std}}(8m) = H_{n+1}^{\mathrm{std}}(2^n-4-8m) = 2 H_n^{\mathrm{std}}(4m)$, an interior palindrome, and the top-bin jump $+3(2^n-2)$.
   - For $n \ge 3$, $4 \mid \nu_n^{\mathrm{std}}$ (Moreno's divisibility in the 2-blade case, re-proved in Lean), and for $n \ge 4$, $\nu_n^{\mathrm{std}} \le 2^{n-1}-4$, attained. This ceiling is below the Biss–Dugger–Isaksen bound $2^n - 4n + 4$ for every $n \ge 5$ ($12 < 16$ at $n = 5$, $28 < 44$ at $n = 6$); among $n \ge 4$ the two are equal only at $n = 4$ ($4 = 4$). In Lean this comparison is arithmetic on the two closed formulas; the Biss–Dugger–Isaksen theorem itself is not formalized.
   - **Midpoint law (`T2f`):** $H_n^\gamma(2^{n-2}) = 42 \cdot 2^{n-4}$ for every $n \ge 4$ and every signature $\gamma \in \{\pm 1\}^n$. The case $n = 4$ is de Marrais's count of 42 assessors.
3. **Pillar 3 — Coordinate right-multiplier families in the Euclidean $\mathrm{CD}_n$ (`T3a`–`T3d`, `[LEAN-6K]`):**
   - Doubling law of the right-compatibility graph $G_n^{\mathrm{comp}}$; for $n \ge 4$ only $e_0$ and $e_{2^{n-1}}$ are compatible with every index; for $n \ge 3$ the largest pairwise compatible coordinate set has $n + 5$ elements (attained), and each such set gives a norm-multiplicative $[2^n, n+5, 2^n]$ coordinate pair; an explicit doubling tower gives $[2^{n-1}, 2(n+4), 2^n]$ coordinate pairs for $n \ge 4$.
   - `T3c` is arithmetic on the formula $\rho(2^n) = 8\lfloor n/4\rfloor + 2^{n \bmod 4}$: $n + 5 = \rho(2^n)$ for $n = 3, 4, 5$, and $n + 5 < \rho(2^n)$ with gap $\ge n - 5$ for all $n \ge 6$ (first at dimension 64: $11 < 12$). With `T3b`, coordinate right-multiplier families in the Euclidean $\mathrm{CD}_n$ fall short of $\rho(2^n)$ from dimension 64 on. That the formula is the Hurwitz–Radon number is classical and not proved in Lean. Nothing is shown about non-coordinate subspaces.
4. **Pillar 4 — Sedenion, pathion and chingon finite certificates (`T4a`–`T4d` `[LEAN-6K]`; `C1`, `C2` `[EXACT-COMP]`):**
   - Exhaustive check over all $2^{16} = 65{,}536$ sedenion coordinate subsets: 42 of the 140 affine 2-planes are bad; exactly 42 coordinate subsets of size 10 are norm-multiplicative, split $7 + 28 + 7$ by their overlap with $e_0,\dots,e_7$; none has size $\ge 11$.
   - The 42 sedenion box-kite assessors form de Marrais's 7 box-kites, each an octahedron $K_{2,2,2}$ (4-regular, 84 edges in total; spectrum $\{4^7, 0^{21}, (-2)^{14}\}$). This is a formal re-verification of a known result (de Marrais 2000).
   - Over all signatures, the histogram profiles of $\mathrm{CD}_4(\gamma)$ and $\mathrm{CD}_5(\gamma)$ occur with multiplicities $1{:}1{:}7{:}7$ and $4{\times}1 + 4{\times}7$ (Lean). For the 448 algebras $\mathrm{CD}_6(\gamma)$–$\mathrm{CD}_8(\gamma)$ the tables were computed in Rust, C11 and Python (`[EXACT-COMP]`); interior spectral gaps first occur at dimension 64.
   - Norm-multiplicative coordinate sets of size 14 in $\mathrm{CD}_5$ and 16 in $\mathrm{CD}_6$ exist (Lean), giving $[14,14,32]$ and $[16,16,64]$ coordinate pairs. A HiGHS MILP certificate outside Lean shows that no symmetric norm-multiplicative coordinate subset of $\mathrm{CD}_5$ has 16 elements, so $r_{\max}(\mathrm{CD}_5) = 14$ (`[EXACT-COMP]`). This bound concerns coordinate subsets of $\mathrm{CD}_5$ and is not comparable with Yiu's general integral $[16,16,32]$ formula.
   - `T4d` also contains elementary lemmas: $c^2 = 1$ forces $c = \pm 1$ in an integral domain (with the factorization $(c-1)(c+1) = 0$ taken as a hypothesis), in $\mathbb{Z}$ and in $\mathbb{Z}[i]$. These are textbook facts and do not bear on the result of Zhang and Zhu (2026).

What remains open is listed in [`LIMITATIONS.md`](LIMITATIONS.md); corrections to the frozen manuscript and known issues in the formal code are in [`ERRATA.md`](ERRATA.md).

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
| [`paper/`](paper/) & [`dist/`](dist/) | 17-page zero-warning AMS-LaTeX white paper, 5 Okabe-Ito vector figures, 24 BibTeX entries (22 carry a DOI or arXiv identifier that resolves live; the checker does not compare titles), frozen PDF & clean-room `arxiv_submission.tar.gz` |
| [`docs/site/`](docs/site/) | Zero-CDN interactive 3D Sedenion Box-Kite & Terrace Observatory (`index.html`) + Proof Blueprint (`blueprint.html`) |
| [`data/`](data/) & [`results/`](results/) | Frozen JSON computational certificates, `data/MANIFEST.sha256`, and `results/lean_axioms.txt` |
| [`CLAIMS.md`](CLAIMS.md) & [`LIMITATIONS.md`](LIMITATIONS.md) | Granular theorem-to-evidence ledger and explicit epistemic boundaries |

---

## Citation & Licensing

- **Code** (`lean/`, `rust/`, `c/`, `src/`, `reference/`, `tests/`, `scripts/`, `examples/`): **Apache-2.0** ([`LICENSE`](LICENSE)).
- **Paper, Figures, Data & Documentation** (`paper/`, `dist/`, `docs/`, `data/`, `*.md`): **CC-BY-4.0** ([`LICENSE-DOCS`](LICENSE-DOCS)).
- Machine-readable copyright & license coverage declared in [`REUSE.toml`](REUSE.toml) and citation metadata in [`CITATION.cff`](CITATION.cff).
