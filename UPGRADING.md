# Upgrading (`UPGRADING.md`)

## Current Version: `3.0.0`

`3.0.0` is the current major release of `cayley-dickson-terrace-frontier` (`0TH-2026-019`), expanding the formalization from 4 pillars (22 theorems / 23 Palomar targets / 35 audited declarations in `v2.1.0`) to **6 pillars (28 headline theorems `T1a`–`T6c` / 29 Palomar targets / 45 audited declarations)** by adding Pillar V (`SpectralGaps.lean`, `T5a`–`T5c`) and Pillar VI (`OddBladeExclusion.lean`, `T6a`–`T6c`).

### Upgrading from `v2.x` to `v3.0.0`
- **Lean 4 API (`lean/`):** Additive — all 22 `T1a`–`T4f` statements remain intact; 6 new theorem abbreviations (`T5aStmt`–`T6cStmt`), 2 new non-vacuity witnesses (`NV5`–`NV6`), and 2 new adversarial refutations (`A9`–`A10`) are added. `AllTerraceTheoremsStmt` now conjoins all 28 headline theorems.
- **Python / Rust / C11 APIs:** Additive — adds `gray_lock_bit` / `cd_gray_lock_bit`, `is_gapped_mask` / `cd_is_gapped_mask`, `cd_mul_gamma_vec` / `cd_mul_gamma_vec`, and Python `odd_pivot_integral_inv`. All existing `v2.x` functions remain backwards-compatible.
- **Frozen Datasets (`data/`):** Unchanged (`"schema_version": "1.0"`); `data/MANIFEST.sha256` and its DigiCert `.tsr` / Bitcoin `.ots` proofs remain byte-identical and valid.

### Upgrading Lean Toolchains in Future Releases
- This repository pins `leanprover/lean4:v4.35.0` in [`lean/lean-toolchain`](lean/lean-toolchain) with zero Mathlib dependencies.
- Because all 9 Lean modules rely solely on Lean core (`Nat`, `Int`, `List`, `Bool`) and avoid `native_decide` and custom axioms, upgrading to a newer Lean 4 toolchain requires only updating `lean/lean-toolchain` and re-running `lake build`, `VerifyAxioms.lean`, `lake check --paranoid`, and `lake comparator --config comparator.json --paranoid`.

### Frozen Artifact Compatibility
- JSON dataset schemas in `data/` carry explicit `"schema_version": "1.0"`. Breaking schema changes will increment the major version and preserve compatibility notes here.
