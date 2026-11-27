# Clean-Clone Replication Guide (`REPLICATION.md`)

Every theorem, dataset, figure, PDF page, cryptographic timestamp, and SHA-256 checksum in `cayley-dickson-terrace-frontier` (`v2.0.0`) can be independently reproduced from a fresh clone without hidden dependencies or external databases.

## Prerequisites
- **Lean 4.35.0** via `elan` (`lean/lean-toolchain` pins `leanprover/lean4:v4.35.0`; zero Mathlib downloads required).
- **Rust** stable toolchain (`cargo`, `clippy`; zero crate dependencies).
- **ISO C11 compiler** (`gcc` or `clang`, with ASan/UBSan support on Linux/macOS).
- **Python 3.11+** with pinned dependencies in `requirements.lock.txt`.
- **Tectonic** (`0.15+`) for AMS-LaTeX PDF compilation and **OpenSSL** for RFC 3161 `.tsr` verification.

## Step-by-Step Clean-Clone Verification

```bash
git clone https://github.com/0thernes/cayley-dickson-terrace-frontier.git
cd cayley-dickson-terrace-frontier

# 1. Lean 4.35.0 zero-Mathlib build, 35-declaration axiom audit & standalone kernels
cd lean
lake build
lake build PalomarChallenge
lake env lean VerifyAxioms.lean > ../results/lean_axioms_local.txt
diff -u ../results/lean_axioms.txt ../results/lean_axioms_local.txt
lake env leanchecker --fresh PalomarSolution
lake env leanchecker-paranoid --fresh PalomarSolution
# On Linux with bubblewrap + Lean 4.35.0 external kernels:
# lake check --paranoid
# lake comparator --config comparator.json --paranoid
cd ..

# 2. Rust differential engine (all 496 generalized algebras CD_4..CD_8 + 280 Pathion 14D subspaces)
cd rust
cargo clippy --all-targets -- -D warnings
cargo test --release
cargo run --release -- --verify-all
cd ..

# 3. Strict ISO C11 engine + ASan/UBSan + 100k fuzzing (all 496 algebras zero-stride)
make -C c clean test sanitize fuzz
./c/build/fuzz_cd_terrace 100000
./c/build/cd_terrace_cli --verify-all

# 4. Python exact Q-oracle, Hypothesis, surgical mutations, differential, axiom, citation & timestamp checks
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.lock.txt
PYTHONPATH=src:. python examples/quickstart_demo.py
PYTHONPATH=src:. pytest -v tests/test_all.py
python scripts/check_readme_axioms.py
python scripts/check_citations.py --live
python scripts/stamp_timestamps.py --verify --negative-test
python scripts/build_blueprint.py

# 5. Figures, zero-warning AMS-LaTeX white paper & clean-room arXiv tarball
PYTHONPATH=src:. python scripts/generate_figures.py
mkdir -p paper/build
tectonic -X compile paper/main.tex --outdir paper/build --keep-logs
! grep -E "Overfull|Underfull|Undefined|Error" paper/build/main.log

# 6. Cryptographic SHA-256 verification
sha256sum -c data/MANIFEST.sha256
sha256sum -c MANIFEST.sha256
```

Or run `just reproduce` via [`justfile`](justfile).

## Replication Ledger

| Date (UTC) | Environment | Scope Verified | Outcome |
| --- | --- | --- | --- |
| 2026-11-26 | Windows 11 (ReFS Dev Drive), Lean 4.35.0, Rust 1.94.1, GCC (WinLibs C11), Python 3.12, Tectonic 0.17.0, OpenSSL 3.5.9 | Clean-clone cold reproduction of `v2.0.0`: `lake build` + `VerifyAxioms.lean` (35/35 strict) + `leanchecker --fresh` + `leanchecker-paranoid --fresh` + Rust 496-algebra & 280-subspace audit + C11 `-Werror -Wconversion -Wshadow` 496-algebra audit + Python exact $\mathbb{Q}$ oracle/Hypothesis/mutations/differential + live 28/30 citations + RFC 3161/OTS negative tamper tests + 0-warning 21-page PDF + clean-room arXiv tarball + Build Standard 100% | **PASS (100%)** |
| 2026-11-26 | GitHub Actions Ubuntu / macOS / Windows CI (`ci.yml`) | 6 independent Lean 4.35.0 kernels (23 Palomar targets + real tamper-injecting negative comparator gate), strict ISO C11 (`-Werror`, ASan/UBSan, 100k fuzz), 3-OS Rust & Python matrices, Tectonic + clean-room arXiv + RFC 3161/OTS + SLSA attestation | **Verified on GitHub Actions CI** |
