# Changelog (`CHANGELOG.md`)

All notable changes to `cayley-dickson-terrace-frontier` are documented here following [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning.

## [2.0.0] - 2026-11-26

### Added
- **Theorem `T1f` (`twoblade_left_annihilator_basis_exact`, `[LEAN-6K]`):** Formalized the literal bilinear product `cdMulCoordGamma` in `CDTerrace.Basic` and proved inside Lean that `twobladeNullityGamma` equals the exact cardinality of an explicit 2-sparse linearly independent spanning $\mathbb{Z}$-basis of $\ker L_{e_i + e_j}$ across all $n \ge 1$ and all $2^n$ signatures (`ERRATA.md` M1/F1).
- **Theorem `T4e` (`pathion_exact_ceiling_14_and_7_7_rigidity`, `[LEAN-6K]`):** Pure-kernel Lean 4.35.0 proof over ALL $2^{32} = 4{,}294{,}967{,}296$ coordinate subsets of $\mathrm{CD}_5$ (and all duplicate-free lists `isNormMultPair 5 S S`) using universal all-$n$ half-swap symmetry (`cdSign_halfSwap`, `pairingCancels_halfSwap`) and a zero-backtracking binary-tree greedy clique-cover certificate (`0/2,995` failures, 16 `rfl` blocks) establishing $r_{\max}(\mathrm{CD}_5) = 14$ (retiring external HiGHS MILP solvers from the proof trust base!) and strict $7 + 7$ half-balance rigidity (`|S| = 14 -> |S_lo| = 7 ∧ |S_hi| = 7`).
- **Theorem `T4f` (`cd6_split56_interior_spectral_gap`, `[LEAN-6K]`):** Pure-kernel Lean 4.35.0 certification of the complete 9-bin 2-blade nullity histogram `{0:257, 4:422, 8:364, 12:336, 16:168, 20:0, 24:56, 28:172, 32:178}` at $\mathrm{CD}_6(\mathrm{flip}=56)$, proving the emergence of an interior spectral gap at dimension 64 ($H_6^{56}(20) = 0$).
- **Two New Formal Adversarial Refutations (`A7`–`A8`):** `refute_pathion_15d_or_unbalanced_14d` and `refute_cd6_split56_contiguous_bins` in `AdversarialTests.lean` (expanding `VerifyAxioms.lean` from 30 to **35** strictly audited declarations and Palomar Comparator targets from 20 to **23**).
- **Exact 280-Subspace Pathion Census (`C2`, `[EXACT-COMP]`):** Exhaustive branch-and-bound enumeration in both Rust (`#![forbid(unsafe_code)]`) and Python certifying exactly **280** 14-dimensional norm-multiplicative coordinate subspaces in $\mathrm{CD}_5$ (100% $7+7$ balanced, 100% containing $\{e_0, e_{16}\}$).
- **Cryptographic Timestamps (`scripts/stamp_timestamps.py`):** DigiCert RFC 3161 TSA (`data/MANIFEST.sha256.tsr`) and 3-calendar Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots`) proofs with built-in verification and tamper negative test.
- **Six New Live-Verified Primary References (`paper/references.bib`):** `albuquerque1999`, `demarrais2002`, `moreno2004`, `moriergenoud2011`, `zhilina2021i`, `zhilina2021ii`, plus verified DOI `10.1090/conm/058.2/893847` for `lamyiu1987` (`28/30` live title+author+year+retraction verified + `2` print-only classics).
- **Playbook v1.3 Scholarly Disclosures & Documentation:** Added CRediT, Competing Interests/Funding, Data/Code Availability, Export-Control Self-Screen (15 CFR 734.8), Withdrawal/Errata Policy, `HARDENING_INDEX.md`, `docs/literature-search-log.md`, and `docs/submission-packet.md`.

### Changed & Fixed (Resolving 23/23 `ERRATA.md` Items + 9 Deep-Audit Fixes)
- **Lean Statement Strengthenings (`ERRATA.md` F1–F8):** Upgraded `T1cStmt` to full bilinear nilpotency + cross-term cancellation; upgraded `T2bStmt` with explicit ceiling attainment and `twoblade_bdi_eq_iff_four` ($n \ge 4$); added `sedenion_bad_planes_split_2_2` into `T4aStmt`; replaced XOR-prefiltered `boxKiteAdj` with pure algebraic vanishing-product adjacency in `T4b`; replaced pre-factored domain lemma with ring-axiom-derived `domain_sq_eq_one_imp` in `T4d`; aligned all module labels and docstrings.
- **Rust, ISO C11 & Python Hardening:** Added `#![forbid(unsafe_code)]`, underflow guards, and pure algebraic sedenion adjacency in `rust/`; added `n > CD_MAX_N` shift-UB guards and removed `sig_step = 8` stride in `c/` so all 496 algebras $\mathrm{CD}_4$–$\mathrm{CD}_8$ are verified exhaustively; added 8 surgical mutation-killing tests and WCAG/CSP/version-drift tests to `tests/test_all.py`.
- **Real Tamper-Injecting CI Negative Gate (`ERRATA.md` Tooling #1):** Replaced `/tmp` throwaway test in `.github/workflows/ci.yml` with a real copy of `lean/` injecting both `sorry` and a custom axiom into `PalomarSolution.lean` and asserting non-zero rejection by `lake comparator --config comparator.json --paranoid` and the axiom diff gate.
- **3D Canvas Observatory & Synchronized 26-Node Blueprint (`docs/site/`):** Replaced "WebGL" misnomer with honest "3D Canvas", fixed raw LaTeX string, added strict CSP, WCAG 2.2 AA skip-link, keyboard Arrow/Home/End tablist, `prefers-reduced-motion`, deterministic BigInt seed, and pure algebraic `bladeAnnihilates4`.
- **Build Standard v1.2.0 Honest Flags:** Enabled `visual: true`, `ui: true`, `deployed: true` in `repo.yaml`, added `deploy` / `rollback` recipes in `justfile`, embedded visual preview in `README.md`, and added inline SPDX headers to all remaining YAML/shell scripts.

## [1.0.0] - 2026-11-26

### Added
- Initial zero-Mathlib Lean 4.35.0 formalization (19 headline theorems `T1a`–`T4d`, 20 Palomar targets, 30 audited decls), tri-language Rust/C11/Python engines, 17-page AMS-LaTeX preprint, interactive 3D observatory, GitHub Actions 6-kernel CI, and SLSA attestation. Post-release audit findings logged in `ERRATA.md` and fully resolved in `v2.0.0`.
