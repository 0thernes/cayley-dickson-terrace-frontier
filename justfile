# SPDX-License-Identifier: Apache-2.0
set shell := ["bash", "-cu"]

default: verify

# Build and strictly audit all Lean 4.35.0 proofs (23 Palomar targets, 35 audited decls)
lean:
    cd lean && lake build && lake build PalomarChallenge && lake env lean VerifyAxioms.lean > ../results/lean_axioms_local.txt
    ! grep -E "sorryAx|_native|Lean\.ofReduceBool|Lean\.trustCompiler" results/lean_axioms_local.txt
    diff -u results/lean_axioms.txt results/lean_axioms_local.txt
    cd lean && lake env leanchecker --fresh PalomarSolution && lake env leanchecker-paranoid --fresh PalomarSolution

# Build and test stdlib-only Rust engine (verifies all 496 algebras CD_4..CD_8 + 280 Pathion 14D subspaces)
rust:
    cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all

# Build and test zero-warning ISO C11 independent verifier (+ ASan/UBSan & 100k fuzz)
c11:
    make -C c clean test sanitize fuzz
    ./c/build/fuzz_cd_terrace 100000
    ./c/build/cd_terrace_cli --verify-all

# Run Python exact oracle, pytest, Hypothesis, mutation, differential, axiom-drift, citation & blueprint checks
python:
    PYTHONPATH=src:. python examples/quickstart_demo.py
    PYTHONPATH=src:. pytest tests/test_all.py -v
    python scripts/check_readme_axioms.py
    python scripts/check_citations.py
    python scripts/build_blueprint.py

# Verify DigiCert RFC 3161 (.tsr) and Bitcoin OpenTimestamps (.ots) cryptographic proofs
timestamps:
    python scripts/stamp_timestamps.py --verify --negative-test

# Regenerate vector PDF/PNG figures and compile AMS-LaTeX white paper with Tectonic
paper:
    PYTHONPATH=src:. python scripts/generate_figures.py
    mkdir -p paper/build
    tectonic -X compile paper/main.tex --outdir paper/build --keep-logs
    ! grep -E "Overfull|Underfull|Undefined|Error" paper/build/main.log

# Deploy interactive 3D Canvas observatory & blueprint to GitHub Pages (via pages.yml)
deploy:
    python scripts/build_blueprint.py
    gh workflow run pages.yml

# Roll back GitHub Pages deployment to a known-good git tag or commit SHA
rollback tag="v1.0.0":
    git rev-parse --verify "{{tag}}"
    git checkout "{{tag}}" -- docs/site/
    git status -s docs/site/
    @echo "Staged docs/site/ from {{tag}}; commit and push to main to trigger pages.yml rollback."

# End-to-end clean-clone reproduction entry point (Build Standard B01)
reproduce: lean rust python timestamps paper
    sha256sum -c data/MANIFEST.sha256
    sha256sum -c MANIFEST.sha256

# Full verification ladder
verify: lean rust c11 python timestamps paper
