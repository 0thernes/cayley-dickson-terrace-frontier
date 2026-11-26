# Threat Model & Soundness Surface (`docs/threat-model.md`)

## Assets & Integrity Goals
1. **Mathematical Soundness:** Guarantee that every `[LEAN-6K]` theorem proves the exact mathematical statement advertised in `paper/main.tex` and `README.md`, with zero `sorry`, `admit`, `native_decide`, custom axioms, or kernel bugs.
2. **Computational Correctness & Memory Safety:** Guarantee that the Rust, ISO C11, and Python engines agree bit-for-bit with zero undefined behavior, integer overflows, or floating-point rounding contamination.
3. **Artifact & Citation Provenance:** Guarantee that frozen JSON datasets, the white paper PDF, `arxiv_submission.tar.gz`, and all 24 bibliography entries are tamper-evident and authentic.

## Threat Matrix & Mitigations

| Threat Vector | Attack / Failure Mode | Concrete Mitigation |
| --- | --- | --- |
| Single Lean kernel bug | Unsoundness in Lean 4 C++ kernel | Replay full proof export across **6 independent kernels** (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) |
| Statement drift / vacuous proofs | Proving a weaker or vacuous Lean theorem | Palomar Comparator (`comparator.json --paranoid`) + `NonVacuity.lean` (4 witnesses) + `AdversarialTests.lean` (6 refutations) |
| Hidden `native_decide` / `sorryAx` / README drift | Silent axiom creep between Lean and docs | `VerifyAxioms.lean` + CI `diff -u` + `scripts/check_readme_axioms.py` + live negative axiom-rejection test in CI |
| C11 memory corruption or integer overflow | UB in native verifier | Strict `-std=c11 -Wall -Wextra -Wpedantic -Werror -Wshadow -Wconversion`, ASan + UBSan, 100k fuzzing, libFuzzer harness, differential cross-check against Rust & Python |
| Citation hallucination or wrong DOI | Broken or mismatched BibTeX entry | Live Crossref + arXiv title-verified audit (`scripts/check_citations.py --live`); caught and fixed `cawagas2004` DOI (`1087` -> `1088`) |
| Artifact tampering or CRLF checksum drift | Corrupted PDF, dataset, or tarball | LF normalization before hashing, `data/MANIFEST.sha256`, root `MANIFEST.sha256`, CI `sha256sum -c`, SLSA build provenance attestation |
| Web observatory supply-chain / XSS | External CDN compromise or script injection | Zero-CDN self-contained `docs/site/index.html` and `blueprint.html`; pure deterministic local Canvas/JS math with no user-submitted HTML rendering |
