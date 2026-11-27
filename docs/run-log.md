# Verification Run Log (`docs/run-log.md`)

All local verification runs executed prior to the `v2.0.0` freeze on a Windows 11 workstation (ReFS Dev Drive):

| Check | Toolchain / Command | Outcome | Notes |
| --- | --- | --- | --- |
| Lean 4.35.0 full build | `lake build` + `lake build PalomarChallenge` | **PASS (0 errors, 0 warnings, 81.75s)** | 17 jobs (`CDTerrace`, `PathionRupture` 69s, `Challenge`, `Solution`, `PalomarSolution`) + 10 jobs (`PalomarChallenge`) |
| Lean axiom audit | `lake env lean VerifyAxioms.lean` | **PASS (35/35 strict)** | Strictly subset of `[propext, Classical.choice, Quot.sound]`; 0 `sorryAx`, 0 `Lean.ofReduceBool` |
| Standalone kernel replay | `lake env leanchecker --fresh PalomarSolution` | **PASS (exit 0, 171.54s)** | Fresh environment replay of all 23 Palomar targets (`T1a`–`T4f` + `ALL`) |
| Paranoid kernel replay | `lake env leanchecker-paranoid --fresh PalomarSolution` | **PASS (exit 0, 218.35s)** | Strict paranoid typecheck with zero `maxRecDepth`/`maxHeartbeats` overrides |
| Rust clippy, tests & 496-algebra audit | `cargo clippy --all-targets -- -D warnings`, `cargo test --release`, `cargo run --release -- --verify-all` | **PASS (0 warnings, 3/3 tests)** | `#![forbid(unsafe_code)]`; all 496 algebras $\mathrm{CD}_4(\gamma)$–$\mathrm{CD}_8(\gamma)$ + exhaustive 280 Pathion 14D subspaces ($7+7$ & $\{0,16\}$) + $\mathrm{CD}_6(56)$ gap |
| ISO C11 strict verifier | `gcc -std=c11 -O3 -Wall -Wextra -Werror -Wpedantic -Wconversion -Wshadow` + `--verify-all` | **PASS (0 warnings)** | Zero-stride audit of all 496 algebras $\mathrm{CD}_4(\gamma)$–$\mathrm{CD}_8(\gamma)$ + Pathion $r_{\max}=14$ + $\mathrm{CD}_6(56)$ gap (ASan/UBSan + 100k fuzz run in Ubuntu CI) |
| Python oracle, Hypothesis, differential & 8 mutants | `pytest -v tests/test_all.py`, `examples/quickstart_demo.py`, `ruff check`, `mypy` | **PASS (12/12 tests in 1.02s, 0 lint/type issues)** | Cross-checked Python exact $\mathbb{Q}$ oracle vs. Rust CLI `--json`; 8/8 surgical mutants killed; WCAG/CSP & version consistency verified |
| Frozen datasets | `scripts/generate_data.py` | **PASS** | 4 frozen JSON datasets (`exact_14d_subspace_count: 280`, `lean_kernel_proved: true`) |
| Live Crossref / arXiv citation & retraction audit | `scripts/check_citations.py --live` | **PASS (30/30 bijective, 28/28 live IDs verified)** | Title, primary author, year, and retraction checks live via Crossref/arXiv (`2` print-only classics: `hurwitz1898`, `adem1975`) |
| AMS-LaTeX manuscript & clean-room arXiv tarball | `tectonic -X compile paper/main.tex` + clean-room extract compile | **PASS (0 warnings, 21 pages)** | 0 Overfull/Underfull/Undefined/Error; visual pixel QA on all 5 Okabe-Ito figures & rendered pages; deterministic `dist/arxiv_submission.tar.gz` (229,401 bytes) |
| Dual cryptographic timestamps | `scripts/stamp_timestamps.py --stamp --verify --negative-test` | **PASS** | DigiCert RFC 3161 `.tsr` (5,995 bytes) + 3-calendar Bitcoin OTS `.ots` (845 bytes) over `data/MANIFEST.sha256`; 1-byte tamper rejected by both |
| Axiom README anti-drift & Blueprint | `scripts/check_readme_axioms.py`, `scripts/build_blueprint.py` | **PASS (35/35 verbatim)** | Verbatim 35-line `#print axioms` match; `docs/site/blueprint.html` generated (25,418 bytes) |
| Build Standard v1.2.0 Audit | `scripts/Audit-Repo.ps1 -Path .` | **PASS (100.0%, 71/71)** | `visual: true, ui: true, deployed: true`; 0 FAIL, 0 PART, 0 UNKNOWN |
