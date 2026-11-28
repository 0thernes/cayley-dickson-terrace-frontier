# Architecture & Proof System Design (`docs/architecture.md`)

## System Overview

`cayley-dickson-terrace-frontier` (`v3.0.0`) integrates five orthogonal verification and preservation layers around a single canonical mathematical model of generalized Cayley--Dickson algebras $\mathrm{CD}_n(\gamma)$:

```text
                +----------------------------------------------------------+
                |   Canonical Mathematical Model: CD_n(gamma)              |
                |   sigma_n^gamma(i,j), cdMulCoordGamma, ker L_{e_i+e_j},  |
                |   blockDelta, nu_n^gamma, G_n^comp, norm-multiplicativity|
                |   Gray bit-locking, twisted group algebra Z[Z_2^n]^sigma |
                +------------+---------------------------+-----------------+
                             |                           |
          +------------------+                           +------------------+
          v                                                                 v
+-----------------------------------+                       +----------------------------------+
|  Lean 4.35.0 (Zero-Mathlib)       |                       | Tri-Language Exact Engines       |
|  lean/CDTerrace/*.lean            |                       |  - rust/ (#![forbid(unsafe_code)]|
|  - Basic.lean (cdMulCoordGamma)   |                       |    496 alg + 280 Pathion + V-VI) |
|  - MirrorConservation.lean (T1a-f)|                       |  - c/ (ISO C11, ASan/UBSan,      |
|  - TerraceLaw.lean (T2a-f)        |                       |    100k CD_1..CD_7 fuzz, 496     |
|  - HurwitzRupture.lean (T3a-d)    |                       |    zero-stride + Pillars V-VI)   |
|  - FiniteCertificates.lean (T4a-d)|                       |  - src/ + reference/oracle       |
|  - PathionRupture.lean (T4e, T4f) |                       |    (naive Q Gauss elim + 10 mut.)|
|  - SpectralGaps.lean (T5a-c)      |                       +----------------+-----------------+
|  - OddBladeExclusion.lean (T6a-c) |                                        |
|  - NonVacuity.lean (NV1-NV6)      |                                        v
|  - AdversarialTests.lean (A1-A10) |                       +----------------------------------+
+----------------+------------------+                       | Frozen Cryptographic Artifacts   |
                 |                                          |  - data/*.json + MANIFEST.sha256 |
                 v                                          |  - DigiCert RFC 3161 (.tsr)      |
+-----------------------------------+                       |  - 3-Cal Bitcoin OTS (.ots)      |
| Palomar 6-Kernel Contract         |                       |  - dist/*.pdf & arXiv.tar.gz     |
| Challenge / PalomarChallenge (29) |                       |  - docs/site/{index,blueprint}   |
| Solution / PalomarSolution (45)   |                       +----------------------------------+
| 6 Kernels + Tamper-Injecting Gate |
+-----------------------------------+
```

## Key Architectural Decisions

1. **Zero-Mathlib Lean 4.35.0 Core (`ADR-0001`):** Zero external Lean dependencies minimize the trusted computing base and enable deterministic replay across all 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
2. **Full Bilinear Linear Algebra in Zero-Mathlib Lean (`T1f`, `T6b`):** `Basic.lean` defines exact integer coordinate multiplication `cdMulCoordGamma`, singular orbit representatives `singularOrbitRepsGamma`, and 2-sparse kernel basis vectors `twobladeKernelBasisVec`; `MirrorConservation.lean` proves `twoblade_left_annihilator_basis_exact` ($\dim_{\mathbb{Z}} \ker L_{e_i+e_j} = \nu_n^\gamma(i,j)$); `OddBladeExclusion.lean` builds a self-contained fraction-free odd-pivot Gauss–Jordan matrix inverter (`odd_mod2_inv_matrix_integral_inv`) proving `B_L L_x = Δ_L I` and `B_R R_x = Δ_R I` with odd $\Delta \ne 0$ for all odd-sum $x \in \mathbb{Z}^{2^n}$ and arbitrary $\{\pm 1\}$ cocycle $\sigma$.
3. **All-$n$ Spectral-Gap Dichotomy via Gray-Code Bit-Locking (`SpectralGaps.lean`, `T5a`–`T5c`):** Proves directly by bit-level induction over $n \ge 4$ and all $2^n$ signatures that $2$-blade nullities lock onto the Binary Reflected Gray code `gray(f) = f ^^^ (f >>> 1)`, yielding an exponential band gap of width $2^{n-3}-1$ consecutive mod-4 bins at $\mathrm{flip}=2^n-8$ (`T5b`) and an exact iff classification of all $2^{n-3}-4$ gapped masks (`T5c`).
4. **Pure-Kernel C-Primitive Exhaustion over $2^{16}$ and $2^{32}$ (`FiniteCertificates.lean`, `PathionRupture.lean`):**
   - Sedenion $2^{16}$ counts (`T4a`) and Pathion $2^{32}$ ceiling + $7+7$ rigidity (`T4e`) use provably sound C-primitive (`Nat.div`/`Nat.mod`/`Nat.add`) branch-and-bound + clique-cover pigeonhole bounds (`popcount16_le_clique_cover`) proved equal to the raw textbook predicate `isNormMultMask` and `isNormMultPair`, eliminating `native_decide`, `maxRecDepth`/`maxHeartbeats` overrides, and external MILP solvers from the proof trust base.
   - Dimension-64 split-signature interior spectral gap (`T4f`) computes the complete 9-bin histogram at $\mathrm{CD}_6(56)$ via depth-12 balanced binary-tree reduction (`cd6QuadTree56`) and exact algebraic mirror conservation (`cd6_std_mirror_sums`).
5. **Independent First-Principles Oracle & Mutation Suite (`reference/oracle.py`, `tests/test_all.py`):** `reference/oracle.py` builds full $2^n \times 2^n$ exact `fractions.Fraction` matrices from the textbook recursive doubling formula and runs rational Gaussian elimination; 10 surgical mutants confirm the test suite catches subtle algebraic, Gray-code, parity, and provenance defects.
6. **Zero-CDN Interactive 3D Canvas Observatory (`docs/site/index.html`, `blueprint.html`):** Self-contained HTML/CSS/JS under a strict `<meta http-equiv="Content-Security-Policy">` with 3D-projected HTML5 2D Canvas visualizations, keyboard navigation, `prefers-reduced-motion`, and an auto-generated 32-node Lean dependency DAG blueprint.
