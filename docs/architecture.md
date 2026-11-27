# Architecture & Proof System Design (`docs/architecture.md`)

## System Overview

`cayley-dickson-terrace-frontier` (`v2.0.0`) integrates five orthogonal verification and preservation layers around a single canonical mathematical model of generalized Cayley--Dickson algebras $\mathrm{CD}_n(\gamma)$:

```text
                +----------------------------------------------------------+
                |   Canonical Mathematical Model: CD_n(gamma)              |
                |   sigma_n^gamma(i,j), cdMulCoordGamma, ker L_{e_i+e_j},  |
                |   blockDelta, nu_n^gamma, G_n^comp, norm-multiplicativity|
                +------------+---------------------------+-----------------+
                             |                           |
          +------------------+                           +------------------+
          v                                                                 v
+-----------------------------------+                       +----------------------------------+
|  Lean 4.35.0 (Zero-Mathlib)       |                       | Tri-Language Exact Engines       |
|  lean/CDTerrace/*.lean            |                       |  - rust/ (#![forbid(unsafe_code)]|
|  - Basic.lean (cdMulCoordGamma)   |                       |    496 algebras + 280 Pathion 14)|
|  - MirrorConservation.lean (T1a-f)|                       |  - c/ (ISO C11, ASan/UBSan,      |
|  - TerraceLaw.lean (T2a-d)        |                       |    100k + libFuzzer, 496 zero-   |
|  - HurwitzRupture.lean (T3a-d)    |                       |    stride algebras)              |
|  - FiniteCertificates.lean (T4a-d)|                       |  - src/ + reference/oracle       |
|  - PathionRupture.lean (T4e, T4f) |                       |    (naive Q Gauss elim + 8 mut.) |
|  - NonVacuity.lean (4 witnesses)  |                       +----------------+-----------------+
|  - AdversarialTests.lean (A1-A8)  |                                        |
+----------------+------------------+                                        v
                 |                                          +----------------------------------+
                 v                                          | Frozen Cryptographic Artifacts   |
+-----------------------------------+                       |  - data/*.json + MANIFEST.sha256 |
| Palomar 6-Kernel Contract         |                       |  - DigiCert RFC 3161 (.tsr)      |
| Challenge / PalomarChallenge (23) |                       |  - 3-Cal Bitcoin OTS (.ots)      |
| Solution / PalomarSolution (35)   |                       |  - dist/*.pdf & arXiv.tar.gz     |
| 6 Kernels + Tamper-Injecting Gate |                       |  - docs/site/{index,blueprint}   |
+-----------------------------------+                       +----------------------------------+
```

## Key Architectural Decisions

1. **Zero-Mathlib Lean 4.35.0 Core (`ADR-0001`):** Zero external Lean dependencies minimize the trusted computing base and enable deterministic replay across all 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
2. **Full Bilinear Linear Algebra in Zero-Mathlib Lean (`T1f`):** `Basic.lean` defines exact integer coordinate multiplication `cdMulCoordGamma` and left multiplication `leftMulTwoBladeCoord`; `MirrorConservation.lean` constructs an explicit $\mathbb{Z}$-basis isomorphism proving $\dim \ker L_{e_i+e_j} = \nu_n^\gamma(i,j)$ without importing a linear-algebra library.
3. **Pure-Kernel C-Primitive Exhaustion over $2^{16}$ and $2^{32}$ (`FiniteCertificates.lean`, `PathionRupture.lean`):**
   - Sedenion $2^{16}$ counts (`T4a`) and Pathion $2^{32}$ ceiling + $7+7$ rigidity (`T4e`) use provably sound C-primitive (`Nat.div`/`Nat.mod`/`Nat.add`) branch-and-bound + clique-cover pigeonhole bounds (`popcount16_le_clique_cover`) proved equal to the raw textbook predicate `isNormMultMask` and `isNormMultPair`, eliminating `native_decide`, `maxRecDepth`/`maxHeartbeats` overrides, and external MILP solvers from the proof trust base.
   - Dimension-64 split-signature interior spectral gap (`T4f`) computes the complete 9-bin histogram at $\mathrm{CD}_6(56)$ via depth-12 balanced binary-tree reduction (`cd6QuadTree56`) and exact algebraic mirror conservation (`cd6_std_mirror_sums`).
4. **Independent First-Principles Oracle & Mutation Suite (`reference/oracle.py`, `tests/test_all.py`):** `reference/oracle.py` builds full $2^n \times 2^n$ exact `fractions.Fraction` matrices from the textbook recursive doubling formula and runs rational Gaussian elimination; 8 surgical mutants confirm the test suite catches subtle algebraic and provenance defects.
5. **Zero-CDN Interactive 3D Canvas Observatory (`docs/site/index.html`, `blueprint.html`):** Self-contained HTML/CSS/JS under a strict `<meta http-equiv="Content-Security-Policy">` with 3D-projected HTML5 2D Canvas visualizations, keyboard navigation, `prefers-reduced-motion`, and an auto-generated Lean dependency DAG blueprint.
