# Hardening & Audit Log (`HARDENING_LOG.md`)

Comprehensive record of all hardening cycles executed across every folder, file, theorem, engine, figure, citation, web UI, CI workflow, and governance check in `cayley-dickson-terrace-frontier` (`0TH-2026-019`).

---

## v2.0.0 Hardening Cycles (Resolving 23/23 `ERRATA.md` Items + 9 Deep-Audit Findings)

### Cycle 1 — Mathematical Upgrades, Zero-MILP Pathion Exhaustion & Kernel Speed Engineering
- **Theorem `T1f` (`twoblade_left_annihilator_basis_exact`):** Formalized exact integer bilinear multiplication `cdMulCoordGamma` and left multiplication `leftMulTwoBladeCoord` in `Basic.lean`, and proved an explicit $\mathbb{Z}$-basis isomorphism in `MirrorConservation.lean` establishing $\dim \ker L_{e_i+e_j} = \nu_n^\gamma(i,j)$ for all $n, \gamma, 1 \le i < j < 2^n$, closing the primary statement-fidelity gap from the 2026-11-26 audit.
- **Theorem `T4e` (`pathion_exact_ceiling_14_and_7_7_rigidity`):** Eliminated HiGHS MILP completely from the proof trust base by exhausting all $2^{32} = 4{,}294{,}967{,}296$ coordinate subsets of $\mathrm{CD}_5$ (and all duplicate-free lists `isNormMultPair 5 S S`) purely inside the Lean 4.35.0 kernel via universal half-swap symmetry (`cdSign_halfSwap`, `pairingCancels_halfSwap`), `Forb8` branch-and-bound pruning, odd-byte symmetry (`lo8 = 2k + 1`), and an O(1) constructor-dispatched `Vtx` clique-cover pigeonhole certificate (`popcount16_le_clique_cover`), simultaneously proving strict $7+7$ half-balance rigidity.
- **Theorem `T4f` (`cd6_split56_interior_spectral_gap`):** Certified the complete 9-bin histogram `{0:257, 4:422, 8:364, 12:336, 16:168, 20:0, 24:56, 28:172, 32:178}` at $\mathrm{CD}_6(\mathrm{flip}=56)$ via depth-12 balanced binary-tree kernel reduction (`cd6QuadTree56`) + algebraic mirror conservation, proving $H_6^{56}(20) = 0$ purely in Lean.
- **Closed All Remaining Statement-Fidelity Gaps (`T1c`, `T2b`, `T3c`, `T4a`, `T4b`, `T4d`):** Added full cross-term vanishing of $(e_i+e_j)^2$ (`T1c`), uniqueness of equality at $n=4$ among $n \ge 4$ (`T2b`), explicit coordinate-subset scoping (`T3c`), sedenion $2+2$ bad affine 2-plane splitting (`T4a`), non-circular box-kite inter-strut disjointness (`T4b`), unfactored `c * c = 1 → c = 1 ∨ c = -1` in $\mathbb{Z}[i]$ (`T4d`), and adversarial refutations `A7` and `A8` (`35/35` declarations strictly within `[propext, Classical.choice, Quot.sound]`).
- **Kernel Optimization & Zero Warnings:** Replaced nested `Nat` `if`-dispatch in `hasCrossEdgeFast` with 15-constructor `Vtx` O(1) matching, precomputed `Forb8`, odd-byte symmetry, and fixed unused variable `_hhi`, reducing `PathionRupture.lean` from 107s to 69s (0 errors, 0 warnings) and total dual `leanchecker` + `leanchecker-paranoid` replay from 674s to 473s.

### Cycle 2 — Tri-Language Hardening, Mutation Testing, Live Citations & 21-Page 0-Warning Paper
- **Rust & ISO C11 Hardening:** Added `#![forbid(unsafe_code)]` and exhaustive 280-subspace Pathion 14D enumeration ($100\%$ $7+7$ and containing $\{0, 16\}$) in `rust/`; removed the $\mathrm{CD}_8$ `gamma` stride of 4 in `c/` so C11 verifies all 496 generalized algebras zero-stride under `-std=c11 -Werror -Wconversion -Wshadow`.
- **8-Mutant Surgical Mutation Suite (`tests/test_all.py`):** Added 8 targeted mutation kills across cocycles, block determinants, nullity formulas, Hurwitz--Radon ceilings, Pathion/Chingon witnesses, and timestamp verification, achieving 12/12 `pytest` pass (1.02s), 0 `ruff`, 0 `mypy`.
- **Upgraded Live Citation & Retraction Audit (`scripts/check_citations.py --live`):** Upgraded from HTTP-200-only to full Crossref/arXiv title, primary author, year, retraction, and 100% bijective `\cite{}` verification across all 30 BibTeX entries (`28/28` live verified + `2` print-only classics `hurwitz1898`, `adem1975`; removed misdirected `hurwitz1898` 1922 Werke DOI, added `lamyiu1987` DOI).
- **21-Page AMS-LaTeX Manuscript, Figures & Clean-Room arXiv Tarball:** Updated `paper/main.tex` for `T1f`/`T4e`/`T4f` and honest epistemic framing; replaced `xurl` with clean breakable `\nolinkurl` + `\cmd`; audited all 5 Okabe-Ito figures and rendered PDF pages pixel-by-pixel (fixing Fig. 5 left/right annotation clearance); verified **0 Tectonic warnings** and deterministic clean-room `dist/arxiv_submission.tar.gz` compile exit 0.
- **3D Canvas Observatory & Blueprint (`docs/site/`):** Removed dishonest "WebGL" labeling across UI and metadata, added strict `<meta http-equiv="Content-Security-Policy">`, keyboard accessibility, `prefers-reduced-motion`, and live `T1f`/`T4e`/`T4f` panels; regenerated 26-node `blueprint.html`.

### Cycle 3 — Cryptographic Timestamps, Real Tamper CI Gate, Governance & Cold Reproduction
- **Dual Independent Timestamps (`scripts/stamp_timestamps.py`):** Stamped `data/MANIFEST.sha256` with DigiCert RFC 3161 TSA (`data/MANIFEST.sha256.tsr`, 5,995 bytes) and 3 Bitcoin OpenTimestamps calendars (`alice`, `bob`, `finney` -> `data/MANIFEST.sha256.ots`, 845 bytes) with automated 1-byte tamper rejection testing.
- **Real Tamper-Injecting CI Negative Gate (`.github/workflows/ci.yml`):** Replaced the v1.0.0 throwaway axiom check with live `sorry` and `public axiom` injections into a copy of `PalomarSolution.lean`, verifying that `lake comparator --config comparator.json --paranoid` and the `VerifyAxioms.lean` diff gate reject both.
- **Honest Build Standard v1.2.0 Compliance (`100.0%`, `71/71`):** Enabled `visual: true, ui: true, deployed: true` in `repo.yaml`, added `A38` accessibility + `A36` `deploy`/`rollback` recipes in `justfile`, added inline SPDX headers to 100% of files, added `docs/literature-search-log.md`, `docs/submission-packet.md`, `docs/adr/README.md`, `docs/adr/0004-*`, and `HARDENING_INDEX.md`, normalized LF, regenerated manifests, and passed clean-clone cold reproduction.

---

## v1.0.0 Hardening Cycles (Historical Baseline)
- **Cycle 1:** Upgraded BDI separation threshold to $n \ge 5$, built C-primitive `FiniteCertificates.lean` evaluators with zero overrides, eliminated `NonVacuity` WHNF blowup, and fixed an 11D sedenion test witness.
- **Cycle 2:** Caught and fixed Cawagas 2004 DOI (`1087` -> `1088`), aligned Carneiro 2024 title, audited all 5 figures and 17-page PDF, and verified clean-room `arxiv_submission.tar.gz`.
- **Cycle 3:** Resolved all `clippy`/`ruff`/`mypy` issues, added `check_readme_axioms.py`, normalized LF, and reached 100.0% Build Standard v1.2.0 compliance (68/68).
