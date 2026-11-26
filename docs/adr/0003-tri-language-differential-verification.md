# ADR-0003: Tri-Language Differential Verification & First-Principles Oracle

- **Status:** Accepted (2026-11-26)
- **Context:** Computational certificates extending beyond the Lean finite-kernel envelope (such as all 448 algebras of $\mathrm{CD}_6(\gamma)$–$\mathrm{CD}_8(\gamma)$ and the Pathion HiGHS MILP certificate $r_{\max}(\mathrm{CD}_5) = 14 < 16$) must be insulated against implementation bugs, subtle indexing errors, or silent overflow.
- **Decision:** Implement three completely independent exact engines—zero-dependency Rust (`rust/`), strict ISO C11 with ASan/UBSan and 100k + libFuzzer fuzzing (`c/`), and Python (`src/`)—plus a fourth slow first-principles oracle (`reference/oracle.py`) using naive recursive Cayley–Dickson multiplication and exact `fractions.Fraction` Gaussian elimination, cross-checked differentially in `tests/test_all.py` and GitHub Actions CI.
- **Consequences:**
  - *Positive:* Independently caught an early $n = 5$ BDI boundary assumption and an 11D sedenion test witness bug before release; gives high confidence in all `[EXACT-COMP]` claims up to 256D.
  - *Trade-off:* Requires maintaining API parity across Rust, C11, and Python whenever new invariant queries are added.
