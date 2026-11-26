# Third-Party Notices (`THIRD_PARTY_NOTICES.md`)

This repository contains zero vendored third-party source code in `lean/`, `rust/`, `c/`, `src/`, `reference/`, or `docs/site/` (zero Mathlib, zero Cargo crates, zero external C libraries, zero web CDN scripts).

## Build, Verification & Typesetting Toolchains (External)
- **Lean 4.35.0 & Lake** (Apache-2.0): https://github.com/leanprover/lean4
- **External Lean 4 Proof Checkers in CI (`lean4lean`, `nanoda`, `con-leche`, `con-ron`)**: invoked via Lean 4.35.0 `lake check --paranoid` / `lake comparator --paranoid` under their respective open-source licenses.
- **Rust Compiler & Cargo** (Apache-2.0 / MIT): https://www.rust-lang.org/
- **Python Test/Figure Toolchain (`requirements.lock.txt`)**: `pytest` (MIT), `hypothesis` (MPL-2.0), `numpy` (BSD-3-Clause), `scipy` / HiGHS (BSD-3-Clause / MIT), `matplotlib` (PSF-based), `ruff` (MIT), `mypy` (MIT).
- **Tectonic TeX Engine** (MIT): https://tectonic-typesetting.github.io/
- **Build Standard Audit Scripts (`scripts/Audit-Repo.ps1`, `scripts/audit-repo.sh`, `scripts/audit-checks.tsv`, `repo-standard.schema.json`)**: Build Standard for LLMs v1.2.0 (Apache-2.0).
