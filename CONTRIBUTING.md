# Contributing (`CONTRIBUTING.md`)

Contributions, independent proof audits, external kernel replays, and mathematical extensions (such as lifting the $n = 5$ MILP symmetric rupture certificate into Lean or investigating $k$-blade annihilators for $k \ge 3$) are welcome!

## Verification Requirements
Before proposing changes, verify locally:
1. **Lean 4.35.0:** `cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker-paranoid --fresh PalomarSolution` (zero `sorry` outside `PalomarChallenge.lean`, zero `admit`, zero `native_decide`, zero custom axioms, zero Mathlib).
2. **Rust:** `cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all`.
3. **C11:** `make -C c clean test sanitize fuzz`.
4. **Python:** `PYTHONPATH=src:. pytest -v tests/test_all.py && ruff check src/ reference/ scripts/ tests/ examples/ && mypy src/ reference/ scripts/ tests/ examples/`.
5. **Anti-Drift & Paper:** `python scripts/check_readme_axioms.py && python scripts/check_citations.py` and zero-warning `tectonic -X compile paper/main.tex --outdir paper/build --keep-logs`.

## Licensing
By contributing, you agree that code contributions are licensed under **Apache-2.0** (`LICENSE`) and documentation/paper/data contributions under **CC-BY-4.0** (`LICENSE-DOCS`).
