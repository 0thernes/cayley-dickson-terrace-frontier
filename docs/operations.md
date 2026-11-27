# Operations & Verification Runbook (`docs/operations.md`)

## Standard Verification Ladder (`v2.0.0`)

1. **Lean 4.35.0 Build, Axiom Audit & Kernel Replay:**
   ```bash
   cd lean
   lake build
   lake build PalomarChallenge
   lake env lean VerifyAxioms.lean > ../results/lean_axioms_local.txt
   diff -u ../results/lean_axioms.txt ../results/lean_axioms_local.txt
   lake env leanchecker --fresh PalomarSolution
   lake env leanchecker-paranoid --fresh PalomarSolution
   ```
2. **Rust Engine Audit (`#![forbid(unsafe_code)]`):**
   `cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all`
3. **ISO C11 Engine, Zero-Stride 496-Algebra Audit & Sanitizers:**
   `make -C c clean test sanitize fuzz && ./c/build/fuzz_cd_terrace 100000 && ./c/build/cd_terrace_cli --verify-all`
4. **Python Suite, Mutation Harness, Citation & Anti-Drift Checks:**
   ```bash
   PYTHONPATH=src:. pytest -v tests/test_all.py
   ruff check src/ reference/ scripts/ tests/ examples/
   mypy --ignore-missing-imports --explicit-package-bases src/ reference/ scripts/ tests/ examples/
   python scripts/check_readme_axioms.py
   python scripts/check_citations.py --live
   ```
5. **Figures, 21-Page White Paper, Manifests & Cryptographic Timestamps:**
   ```bash
   PYTHONPATH=src:. python scripts/generate_figures.py
   tectonic -X compile paper/main.tex --outdir paper/build --keep-logs
   python scripts/generate_manifests.py
   python scripts/stamp_timestamps.py --verify --negative-test
   sha256sum -c data/MANIFEST.sha256
   sha256sum -c MANIFEST.sha256
   ```
6. **Build Standard v1.2.0 Audit:**
   `pwsh -File scripts/Audit-Repo.ps1` (Windows) or `bash scripts/audit-repo.sh .` (Linux/macOS).

## Deployment, Rollback & Preservation (`justfile`)
- **Deploy GitHub Pages:** `just deploy` triggers `.github/workflows/pages.yml` (also runs automatically on pushes to `main` touching `docs/site/`).
- **Rollback GitHub Pages / Release:** `just rollback <git-ref>` restores `docs/site/` to a verified tag or commit (e.g. `v2.0.0` or `v1.0.0`) after confirmation and redeploys cleanly.
- **Refresh Cryptographic Timestamps:** `just timestamps` stamps `data/MANIFEST.sha256` against DigiCert RFC 3161 TSA and 3 Bitcoin OpenTimestamps calendars and runs the tamper verification test.
- **Offline Git Bundle Backup:** `git bundle create cayley-dickson-terrace-frontier-v2.0.0.bundle --all`
- **Master Research Archive Mirror:** Every frozen PDF, pinned commit hash, SHA-256 manifest, and timestamp is mirrored and registered under `0TH-2026-019` (`v2.0.0`) in [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive).
- **Software Heritage Mirror:** Public repository snapshot archived via Software Heritage for permanent SWHID preservation.

## Troubleshooting
- **Windows bracketed paths:** When working under paths containing `[...]` (such as `Z:\[Vibe Coded (AI)]\...`), always pass `-LiteralPath` to PowerShell file cmdlets (`Get-Content`, `Test-Path`, `Set-Location`, `Copy-Item`), and stage files in a bracket-free temp directory before passing paths to `openssl` or `gh release create`.
- **Lean toolchain version:** Pin Lean 4.35.0 via `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`).
