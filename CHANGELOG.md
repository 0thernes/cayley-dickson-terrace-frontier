# Changelog (`CHANGELOG.md`)

All notable changes to `cayley-dickson-terrace-frontier` are documented here following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning.

## [Unreleased] - 2026-11-26

### Changed
- **Claim documents corrected to match the 2026-11-26 statement audit** ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)). `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `CITATION.cff` (abstract) and `docs/` now state that the Lean nullity results concern the explicit sign table and block counts (the link to annihilator dimensions is a paper lemma); describe Pillar 3 as coordinate right-multiplier families in the Euclidean $\mathrm{CD}_n$ and `T3c` as arithmetic on the $\rho(2^n)$ formula; credit Moreno for $4 \mid \nu$ and de Marrais for the 42 assessors and 7 box-kites, and cite Zhilina (2021); restrict "equality only at $n = 4$" to $n \ge 4$; describe `T4d`'s rigidity conjuncts as elementary lemmas unrelated to Zhang–Zhu; drop the comparison of $r_{\max}(\mathrm{CD}_5)$ with Yiu's formula; and replace "24 live-verified / title-verified citations" with "22 of 24 identifiers resolve live; titles not compared".
- **`ERRATA.md`** now lists the corresponding errors in the frozen manuscript, known issues in the Lean code and CI, and the wrong `hurwitz1898` DOI. No Lean, paper, data or CI file was changed. `MANIFEST.sha256` and `llms-full.txt` were regenerated with `scripts/generate_manifests.py`.

## [1.0.0] - 2026-11-26

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):** Complete proofs of all 19 headline theorems (`T1a`–`T4d`) and master conjunction across 7 modules (`Basic`, `MirrorConservation`, `TerraceLaw`, `HurwitzRupture`, `FiniteCertificates`, `NonVacuity`, `AdversarialTests`), Palomar Comparator statement-fidelity contract (`Challenge`, `PalomarChallenge`, `Solution`, `PalomarSolution`, `comparator.json`, `formalization.yaml`), and `VerifyAxioms.lean` auditing all 30 declarations strictly within `{propext, Classical.choice, Quot.sound}`.
- **Tri-Language Differential Verifiers:** Zero-dependency Rust engine (`rust/`), strict ISO C11 engine + ASan/UBSan + 100k fuzz + libFuzzer target (`c/`), and Python exact engine + independent naive recursive / exact $\mathbb{Q}$ linear algebra oracle + Hypothesis test suite (`src/`, `reference/`, `tests/`).
- **Frozen Computational Datasets (`data/`):** Exact JSON certificates for $\mathrm{CD}_3$–$\mathrm{CD}_8$ Euclidean terraces, all 496 split-signature algebras $\mathrm{CD}_4(\gamma)$–$\mathrm{CD}_8(\gamma)$, Sedenion Triple-42 & Pathion HiGHS MILP symmetric rupture, and Dimension-64 Hurwitz–Radon Bott rupture table ($n = 3\dots 12$).
- **Interactive WebGL 3D Observatory & Proof Blueprint (`docs/site/`):** Zero-CDN WCAG 2.2 AA observatory (`index.html`) and interactive theorem dependency blueprint (`blueprint.html`).
- **AMS-LaTeX White Paper & Figures (`paper/`, `dist/`):** 17-page zero-warning manuscript, 5 Okabe-Ito publication figures, 24 live-verified Crossref/arXiv references, frozen PDF, and clean-room verified `arxiv_submission.tar.gz`.
- **Build Standard v1.2.0 Governance, CI & Provenance:** Six-kernel GitHub Actions CI, GitHub Pages deployment, SLSA build provenance attestation, dual licensing (`Apache-2.0` + `CC-BY-4.0`, `REUSE.toml`), and SHA-256 manifests (`data/MANIFEST.sha256`, `MANIFEST.sha256`).
