# Threat Model & Soundness Surface (`docs/threat-model.md`)

## Assets & Integrity Goals
1. **Mathematical Soundness:** Guarantee that every `[LEAN-6K]` theorem proves the exact mathematical statement advertised in `paper/main.tex` and `README.md`, with zero `sorry`, `admit`, `native_decide`, custom axioms, or kernel bugs.
2. **Computational Correctness & Memory Safety:** Guarantee that the Rust (`#![forbid(unsafe_code)]`), ISO C11, and Python engines agree bit-for-bit across all 496 generalized algebras $\mathrm{CD}_4(\gamma)$–$\mathrm{CD}_8(\gamma)$ with zero undefined behavior, integer overflows, or floating-point rounding contamination.
3. **Artifact, Timestamp & Citation Provenance:** Guarantee that frozen JSON datasets, the 21-page white paper PDF, `arxiv_submission.tar.gz`, dual independent timestamps (DigiCert RFC 3161 + Bitcoin OTS), and all 30 bibliography entries are tamper-evident and authentically verified.

## Threat Matrix & Mitigations

| Threat Vector | Attack / Failure Mode | Concrete Mitigation (`v2.0.0`) |
| --- | --- | --- |
| Single Lean kernel bug | Unsoundness in Lean 4 C++ kernel | Replay full proof export across **6 independent kernels** (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) |
| Statement drift / vacuous proofs | Proving a weaker or vacuous Lean theorem | Palomar Comparator (`comparator.json --paranoid`, 23 targets) + `T1f` full linear-algebra kernel isomorphism + `NonVacuity.lean` (4 witnesses) + `AdversarialTests.lean` (8 refutations) |
| Hidden `native_decide` / `sorryAx` / README drift | Silent axiom creep between Lean and docs | `VerifyAxioms.lean` (35 decls) + CI `diff -u` + `scripts/check_readme_axioms.py` + **real tamper-injecting negative gate** verifying that CI rejects injected axioms in `PalomarSolution` |
| Solver trust in finite upper bounds | Unverified floating-point MILP bug | `T4e` proves $r_{\max}(\mathrm{CD}_5) = 14$ and $7+7$ rigidity directly inside the pure Lean kernel over all $2^{32}$ subsets (retiring HiGHS MILP from the proof trust base), cross-checked by exhaustive Rust enumeration of all 280 subspaces |
| C11 memory corruption / stride omission | UB or silent skipping in native verifier | Strict `-std=c11 -Wall -Wextra -Wpedantic -Werror -Wshadow -Wconversion`, ASan + UBSan, 100k fuzzing, libFuzzer harness, zero-stride 496-algebra verification |
| Weak test assertions | Undetected regression in Python/Rust/C11 | Tri-language differential cross-check against naive $\mathbb{Q}$ Gaussian elimination oracle + Hypothesis + **8 surgical mutation tests** (`tests/test_all.py`) |
| Citation hallucination / wrong DOI / retraction | Broken, misdirected, or retracted BibTeX entry | Live Crossref + arXiv title, primary author, year, retraction, and 100% bijective `\cite{}` audit (`scripts/check_citations.py --live`: `28/30` live verified, `2` print-only classics) |
| Artifact tampering / backdating / CRLF drift | Corrupted or backdated PDF, dataset, or tarball | LF normalization before hashing, `data/MANIFEST.sha256`, DigiCert RFC 3161 `.tsr` + 3-calendar Bitcoin `.ots` (with negative tamper test), root `MANIFEST.sha256`, CI `sha256sum -c`, SLSA build provenance attestation |
| Web observatory supply-chain / XSS | External CDN compromise or script injection | Zero-CDN self-contained `docs/site/index.html` and `blueprint.html` with strict `<meta http-equiv="Content-Security-Policy">` (`default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src 'self' data:`) and pure local deterministic 3D Canvas/JS math |
