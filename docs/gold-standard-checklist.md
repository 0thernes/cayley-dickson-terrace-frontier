# Gold Standard Release Checklist (`docs/gold-standard-checklist.md`)

Transparent item-by-item disposition against the **43-item Gold Standard Release Checklist** in *Defensible Independent AI Research Playbook v1.3* for `cayley-dickson-terrace-frontier` (`0TH-2026-019`, `v3.0.0`). External human-operated submissions are tracked transparently and never fabricated or bypassed.

## A. Identity & Infrastructure (Items 1–6)

| # | Requirement | Status | Evidence / Artifact |
| --- | --- | --- | --- |
| 1 | ORCID iD registered and linked | **PASS** | `0009-0006-8168-9648` in `paper/main.tex`, `CITATION.cff`, `README.md`, `lean/formalization.yaml`, `.zenodo.json` |
| 2 | Dedicated public GitHub repo with `CITATION.cff` & dual license | **PASS** | `github.com/0thernes/cayley-dickson-terrace-frontier`; Apache-2.0 (`LICENSE`) + CC-BY-4.0 (`LICENSE-DOCS`) + `REUSE.toml` |
| 3 | Independent archival deposit (Zenodo / OSF / Archive.org) | **MANUAL PENDING** | `.zenodo.json` and frozen `dist/` artifacts prepared; external deposit requires manual depositor review against platform AI-disclosure policies (no fabricated DOI) |
| 4 | Cryptographic provenance (RFC 3161 + Bitcoin OTS + SLSA) | **PASS** | `data/MANIFEST.sha256.tsr` (DigiCert RFC 3161), `data/MANIFEST.sha256.ots` (3 Bitcoin calendars), GitHub SLSA attestation (`actions/attest-build-provenance@v4`) |
| 5 | Reproducible GitHub Actions CI + pinned lockfiles | **PASS** | `.github/workflows/ci.yml` (10 jobs, 6 Lean kernels + 3-OS Rust/Python + C11 ASan/UBSan/fuzz + Tectonic + SLSA); `requirements.lock.txt`, `lean/lean-toolchain` |
| 6 | Software Heritage preservation (SWHID) | **MANUAL PENDING** | Public repo ready for `archive.softwareheritage.org/save/`; automated triggering is blocked by Anubis PoW bot protection (never bypassed) |

## B. Epistemic Hygiene & Prior Art (Items 7–13)

| # | Requirement | Status | Evidence / Artifact |
| --- | --- | --- | --- |
| 7 | Structured literature search log | **PASS** | `docs/literature-search-log.md` (100% programmatically generated from live Crossref/arXiv APIs, bijective across all 30 BibTeX keys) |
| 8 | Every citation verified live (title, author, year, zero retraction) | **PASS** | `scripts/check_citations.py --live` (`28/30` live API verified + `2` print-only classics `hurwitz1898`, `adem1975` reported transparently) |
| 9 | Honest novelty & prior-work attribution | **PASS** | Credits Moreno (1998, 2004), de Marrais (2000, 2002), Albuquerque–Majid (1999), Morier-Genoud–Ovsienko (2011), Biss–Dugger–Isaksen (2007–2009), Zhilina (2021 I–II), Yiu (1990), Zhang–Zhu (2026) |
| 10 | Explicit verification tags on every claim | **PASS** | `[LEAN-6K]`, `[EXACT-COMP]`, `[OPEN]` consistently applied in `paper/main.tex`, `CLAIMS.md`, `README.md`, `LIMITATIONS.md` |
| 11 | Explicit limitations & open problems section | **PASS** | `paper/main.tex` Section 8 (`sec:boundaries`), `LIMITATIONS.md`, `lean/formalization.yaml` (`grand_problems_retired = 0`) |
| 12 | No overstated scope or hidden solver assumptions | **PASS** | Pathion $r_{\max}(\mathrm{CD}_5)=14$ proved purely in Lean (`T4e`, retiring MILP); Pillar 3 strictly scoped to Euclidean coordinate subsets vs. $\rho(2^n)$ |
| 13 | Public errata & withdrawal policy | **PASS** | `ERRATA.md` (23/23 v1.0.0 entries + 34/34 v2.1.0 findings resolved) and Withdrawal Policy subsection in `paper/main.tex` |

## C. Formal Proof Verification & Palomar Rules (Items 14–23)

| # | Requirement | Status | Evidence / Artifact |
| --- | --- | --- | --- |
| 14 | Zero `sorry` / `admit` in all production proofs | **PASS** | Zero `sorry` outside statement-only `PalomarChallenge.lean` (excluded from `defaultTargets`) |
| 15 | Zero `native_decide`, `unsafe`, `partial`, `@[extern]`, custom axioms | **PASS** | Verified by `VerifyAxioms.lean` (45/45 strictly within `[propext, Classical.choice, Quot.sound]`) and automated AST/grep tests |
| 16 | Zero `maxRecDepth` / `maxHeartbeats` overrides | **PASS** | Pure C-primitive arithmetic, `Vtx` O(1) match, balanced binary trees, and fraction-free elimination; zero overrides anywhere in `lean/` |
| 17 | Pinned Lean toolchain & zero-Mathlib minimal TCB | **PASS** | `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`), `autoImplicit = false`, `relaxedAutoImplicit = false`, zero Mathlib |
| 18 | Independent multi-kernel replay | **PASS** | 6 independent kernels in CI (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) |
| 19 | Palomar Comparator statement contract (`comparator.json`) | **PASS** | 29 targets (`T1a`–`T6c` + `ALL`), `Challenge.lean` (< 400 lines / < 25 KiB < 1,000-line / 100 KiB cap), `lake comparator --paranoid` |
| 20 | Real tamper-injecting negative gate in CI | **PASS** | `.github/workflows/ci.yml` injects both `sorry` and `public axiom` into a copy of `PalomarSolution.lean` and asserts non-zero rejection |
| 21 | Statement-fidelity mapping with zero unformalized clauses | **PASS** | `docs/statement-fidelity.md` + automated `tests/test_all.py` symbol-existence & bijection checks |
| 22 | Concrete non-vacuity witnesses & adversarial refutations | **PASS** | `CDTerrace.NonVacuity` (6 pillar witnesses) + `CDTerrace.AdversarialTests` (10 refutations `A1`–`A10`) |
| 23 | `lean/formalization.yaml` complete Palomar metadata | **PASS** | Includes `authorship`, `origin`, `sources`, `automation` (tools/models/human_role/verification), `limitations`, `review_status` |

## D. Independent Computational Falsifiability (Items 24–30)

| # | Requirement | Status | Evidence / Artifact |
| --- | --- | --- | --- |
| 24 | Independent multi-language differential verifiers | **PASS** | Rust (`#![forbid(unsafe_code)]`), ISO C11 (`-Werror -Wconversion -Wshadow`), Python (`src/cd_terrace/`) |
| 25 | Slow first-principles naive oracle | **PASS** | `reference/oracle.py` (naive recursive doubling + exact `fractions.Fraction` Gaussian elimination) |
| 26 | Property-based & negative boundary testing | **PASS** | Hypothesis property tests, `test_t1f_explicit_z_basis_annihilates_and_spans_kernel`, out-of-bounds guards, and Rust `T1f` test |
| 27 | Surgical mutation testing | **PASS** | 10/10 surgical mutants killed in `tests/test_all.py` |
| 28 | Memory-safety sanitizers & fuzzing on native code | **PASS** | C11 ASan + UBSan (`make sanitize`), 100k fuzz across `CD_1..CD_7` (`fuzz_cd_terrace`), zero-stride 496-algebra audit |
| 29 | Deterministic frozen JSON datasets with SHA-256 manifest | **PASS** | 4 datasets in `data/*.json` verified by `data/MANIFEST.sha256` and root `MANIFEST.sha256` |
| 30 | Cross-language CLI differential check in tests | **PASS** | `tests/test_all.py` cross-checks Python vs. compiled Rust CLI `--json`; C11 CLI `--verify-all` runs in CI and locally |

## E. Manuscript, Figures, Accessibility & Governance (Items 31–43)

| # | Requirement | Status | Evidence / Artifact |
| --- | --- | --- | --- |
| 31 | Zero-warning AMS-LaTeX compilation | **PASS** | Tectonic compile of `paper/main.tex`: 0 Overfull, 0 Underfull, 0 Undefined, 0 Error |
| 32 | Deterministic clean-room arXiv tarball verified | **PASS** | `dist/arxiv_submission.tar.gz` compiled cleanly in isolated temp directory (`main.tex`, `references.bib`, `main.bbl`, `00README.XXX`, `figures/*.pdf`) |
| 33 | Publication-grade Okabe-Ito colorblind-safe vector figures | **PASS** | 6 PDF+PNG figures (`paper/figures/fig1..fig6`) + 1280×640 `docs/media/social-preview.{svg,png}`, visually inspected page-by-page |
| 34 | Transparent AI-assistance disclosure | **PASS** | `paper/main.tex` (Section 8), `docs/submission-packet.md`, `lean/formalization.yaml` |
| 35 | CRediT author contribution statement | **PASS** | `paper/main.tex` (Section 8) and `docs/submission-packet.md` |
| 36 | Conflict-of-interest & funding statement | **PASS** | `paper/main.tex` (Section 8) and `docs/submission-packet.md` |
| 37 | Export-control / dual-use self-screen | **PASS** | 15 CFR 734.8 fundamental research statement in `paper/main.tex` (Section 8) and `docs/submission-packet.md` |
| 38 | Zero-CDN strict-CSP WCAG 2.2 AA web observatory & blueprint | **PASS** | `docs/site/index.html` (keyboard-accessible 3D Canvas observatory) + `docs/site/blueprint.html` (32-node DAG) live on GitHub Pages |
| 39 | Strict Build Standard v1.2.0 schema & 90-item audit | **PASS** | `repo.yaml` validates cleanly against `repo-standard.schema.json`; `Audit-Repo.ps1` / `audit-repo.sh` score 100.0% |
| 40 | Adversarial red-team review & 10-pass review documented | **PASS** | `docs/reviews/adversarial-red-team-review.md`, `docs/10-pass-review.md`, `HARDENING_LOG.md`, `HARDENING_INDEX.md` |
| 41 | Cold clean-clone reproduction executed & logged | **PASS** | Fresh `git clone` verification recorded in `REPLICATION.md` and `docs/run-log.md` |
| 42 | Master archive synchronization (`0thernes-research-archive`) | **PASS** | Registered under `0TH-2026-019` with frozen PDF, SHA-256 checksum, pinned commit, and sealed archive timestamp |
| 43 | External scholarly submission (arXiv / Palomar / journal) | **MANUAL PENDING** | `docs/submission-packet.md` and clean-room `dist/arxiv_submission.tar.gz` prepared for manual human submission & endorsement; never fabricated |
