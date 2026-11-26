# Upgrading (`UPGRADING.md`)

## Current Version: `1.0.0`

`1.0.0` is the initial frozen release of `cayley-dickson-terrace-frontier` (`0TH-2026-017`).

### Upgrading Lean Toolchains in Future Releases
- This repository pins `leanprover/lean4:v4.35.0` in [`lean/lean-toolchain`](lean/lean-toolchain) with zero Mathlib dependencies.
- Because all 7 Lean modules rely solely on Lean core (`Nat`, `Int`, `List`, `Bool`) and avoid `native_decide` and custom axioms, upgrading to a newer Lean 4 toolchain requires only updating `lean/lean-toolchain` and re-running `lake build`, `VerifyAxioms.lean`, `lake check --paranoid`, and `lake comparator --config comparator.json --paranoid`.

### Frozen Artifact Compatibility
- JSON dataset schemas in `data/` carry explicit `"schema_version": "1.0"`. Breaking schema changes will increment the major version and preserve compatibility notes here.
