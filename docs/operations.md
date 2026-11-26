# Operations & Verification Runbook (`docs/operations.md`)

## Standard Verification Ladder

1. **Lean 4.35.0 Build & Kernel Audit:**
   ```bash
   cd lean
   lake build
   lake build PalomarChallenge
   lake env lean VerifyAxioms.lean > ../results/lean_axioms_local.txt
   diff -u ../results/lean_axioms.txt ../results/lean_axioms_local.txt
   lake env leanchecker --fresh PalomarSolution
   lake env leanchecker-paranoid --fresh PalomarSolution
   ```
2. **Rust Engine Audit:** `cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all`
3. **ISO C11 Engine & Sanitizers:** `make -C c clean test sanitize fuzz && ./c/build/fuzz_cd_terrace 100000 && ./c/build/cd_terrace_cli --verify-all`
4. **Python Suite & Anti-Drift Checks:** `PYTHONPATH=src:. pytest -v tests/test_all.py && ruff check src/ reference/ scripts/ tests/ examples/ && mypy src/ reference/ scripts/ tests/ examples/ && python scripts/check_readme_axioms.py && python scripts/check_citations.py`
5. **Figures, White Paper & Manifests:** `PYTHONPATH=src:. python scripts/generate_figures.py && tectonic -X compile paper/main.tex --outdir paper/build --keep-logs && python scripts/generate_manifests.py && sha256sum -c data/MANIFEST.sha256 && sha256sum -c MANIFEST.sha256`
6. **Build Standard v1.2.0 Audit:** `pwsh -File scripts/Audit-Repo.ps1` (Windows) or `bash scripts/audit-repo.sh .` (Linux/macOS).

## Offsite Mirror, Backup Bundle & Preservation
- **Offline Git Bundle Backup:** Create a full self-contained backup bundle with `git bundle create cayley-dickson-terrace-frontier-v1.0.0.bundle --all`.
- **Master Research Archive Mirror:** Every frozen PDF, pinned commit hash, and SHA-256 manifest is mirrored and registered under `0TH-2026-019` in [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive).
- **Software Heritage Mirror:** The public repository is archived via Software Heritage Save Code Now for permanent SWHID preservation.

## Troubleshooting
- **Windows bracketed paths:** When working under paths containing `[...]` (such as `Z:\[Vibe Coded (AI)]\...`), always pass `-LiteralPath` to PowerShell file cmdlets (`Get-Content`, `Test-Path`, `Set-Location`, `Copy-Item`).
- **GitHub Pages update:** Editing `docs/site/index.html` or `docs/site/blueprint.html` and pushing to `main` triggers `.github/workflows/pages.yml` automatically.
