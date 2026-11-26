# Verification Run Log (`docs/run-log.md`)

All local verification runs executed prior to `v1.0.0` freeze on Windows 11 (ReFS Dev Drive `Z:\[Vibe Coded (AI)]\ANTIGRAVITY\cayley-dickson-terrace-frontier`):

| Check | Toolchain / Command | Outcome | Notes |
| --- | --- | --- | --- |
| Lean 4.35.0 full build | `lake build` + `lake build PalomarChallenge` | **PASS (0 errors, 0 warnings)** | 16 jobs (`CDTerrace`, `Challenge`, `Solution`, `PalomarSolution`) + 9 jobs (`PalomarChallenge`) |
| Lean axiom audit | `lake env lean VerifyAxioms.lean` | **PASS (30/30 strict)** | Strictly subset of `[propext, Classical.choice, Quot.sound]`; 0 `sorryAx`, 0 `Lean.ofReduceBool` |
| Standalone kernel replay | `lake env leanchecker --fresh PalomarSolution` | **PASS (exit 0)** | Fresh environment replay of all 20 Palomar targets |
| Paranoid kernel replay | `lake env leanchecker-paranoid --fresh PalomarSolution` | **PASS (exit 0)** | Strict paranoid typecheck with zero overrides |
| Rust clippy, tests & 496-algebra audit | `cargo clippy --all-targets -- -D warnings`, `cargo test --release`, `cargo run --release -- --verify-all` | **PASS (0 warnings, 3/3 tests)** | All 496 generalized algebras $\mathrm{CD}_4(\gamma)$–$\mathrm{CD}_8(\gamma)$ verified bit-for-bit |
| Python oracle, Hypothesis & differential tests | `pytest -v tests/test_all.py`, `examples/quickstart_demo.py`, `ruff check`, `mypy` | **PASS (9/9 tests, 0 lint/type issues)** | Cross-checked Python exact $\mathbb{Q}$ oracle vs. Rust CLI `--json` |
| Frozen dataset generation & HiGHS MILP | `scripts/generate_data.py` | **PASS** | 4 frozen JSON datasets + certified zero-gap HiGHS MILP proving $r_{\max}(\mathrm{CD}_5) = 14 < 16$ |
| Live Crossref / arXiv citation audit | `scripts/check_citations.py --live` | **PASS (24/24 HTTP 200 OK)** | Every DOI & arXiv ID title-verified live; fixed Cawagas 2004 DOI `1087` -> `1088` |
| AMS-LaTeX manuscript & clean-room arXiv tarball | `tectonic -X compile paper/main.tex` + temp extract compile | **PASS (0 warnings, 17 pages)** | Visually audited all 5 Okabe-Ito figures & rendered PDF pages via PyMuPDF |
| Axiom README anti-drift & Blueprint | `scripts/check_readme_axioms.py`, `scripts/build_blueprint.py` | **PASS** | Verbatim 30-line `#print axioms` match; `docs/site/blueprint.html` generated |
| Build Standard v1.2.0 Audit | `scripts/Audit-Repo.ps1` | **PASS (100.0%)** | 0 FAIL, 0 PART, 0 placeholders |
