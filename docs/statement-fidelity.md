# Statement Fidelity Audit (`docs/statement-fidelity.md`)

This document maps every mathematical definition and theorem in the white paper (`paper/main.tex`, `v2.0.0`) directly to its formal Lean 4.35.0 specification in `lean/Challenge.lean` and `lean/PalomarChallenge.lean`. All seven statement-fidelity gaps logged by the 2026-11-26 audit (see [`ERRATA.md`](../ERRATA.md)) are closed in `v2.0.0`, and every scope restriction is stated identically in the manuscript and the Lean signatures.

## Core Definition Alignment

| Paper Symbol | Mathematical Meaning | Lean 4.35.0 Definition | Module |
| --- | --- | --- | --- |
| $\sigma_n^{\mathrm{std}}(i, j)$ | Euclidean Cayley--Dickson basis sign cocycle | `CDTerrace.cdSign` | `CDTerrace.Basic` |
| $\sigma_n^{\gamma}(i, j)$ | Generalized sign cocycle for flip mask `flipMask` | `CDTerrace.cdSignGamma` | `CDTerrace.Basic` |
| $(x \cdot y)_k$ in $\mathrm{CD}_n(\gamma)$ | Exact bilinear coordinate multiplication over $\mathbb{Z}$ | `CDTerrace.cdMulCoordGamma` | `CDTerrace.Basic` |
| $L_{e_i + e_j}(x)$ | Left-multiplication operator by the 2-blade $e_i + e_j$ | `CDTerrace.leftMulTwoBladeCoord` | `CDTerrace.Basic` |
| $\delta_n^{\gamma}(i, j, k)$ | $2\times 2$ block determinant sign | `CDTerrace.blockDeltaGamma` | `CDTerrace.Basic` |
| $\nu_n^{\gamma}(i, j)$ | Exact annihilator dimension $\dim \ker L_{e_i + e_j}$ (proved equal to block count via explicit $\mathbb{Z}$-basis isomorphism in `T1f`) | `CDTerrace.twobladeNullityGamma` | `CDTerrace.Basic` |
| $H_n^{\gamma}(v)$ | Count of $1 \le i < j < 2^n$ with $\nu_n^{\gamma}(i,j) = v$ | `CDTerrace.nullityHistGamma` | `CDTerrace.Basic` |
| $M_n$ | Total Euclidean 2-blade nullity mass | `CDTerrace.totalNullityMass` | `CDTerrace.Basic` |
| $G_n^{\mathrm{comp}}$ | Basis right-compatibility graph (Euclidean coordinate subsets) | `CDTerrace.rightCompat`, `isCompatClique` | `Basic`, `HurwitzRupture` |
| $\rho(2^n)$ | Closed Hurwitz--Radon formula $8\lfloor n/4\rfloor + 2^{n \bmod 4}$ (identification with maximal real $[2^n, r, 2^n]$ composition dimension cited from Hurwitz 1922 / Radon 1922) | `CDTerrace.hurwitzRadon` | `CDTerrace.Basic` |
| $[|S_L|, |S_R|, 2^n]$ | Coordinate norm-multiplicative pair in Euclidean $\mathrm{CD}_n$ | `CDTerrace.isNormMultPair`, `isNormMultMask` | `HurwitzRupture`, `FiniteCertificates` |

## Complete Theorem Fidelity Map (22 Headline Theorems, 23 Palomar Targets)

| ID | Paper Theorem | Lean Target (`PalomarChallenge` / `Challenge`) | Scope & Fidelity Notes |
| --- | --- | --- | --- |
| `T1a` | Generalized Sign Factorization | `prove_t1a` / `T1aStmt` | Exact $\forall n, f, i, j < 2^n$ identity |
| `T1b` | $k$-Independent Block-Sign Flip Law | `prove_t1b` / `T1bStmt` | Exact $\forall n, f, i, j, k < 2^n$ identity |
| `T1c` | Split-Signature Involution (Full Bilinear Square) | `prove_t1c` / `T1cStmt` | States full scalar part AND cross-term vanishing of $(e_i+e_j)^2$ |
| `T1d` | Universal Annihilator-Mirror Dichotomy | `prove_t1d` / `T1dStmt` | Exact $\forall n, f, i, j$ trichotomy ($0$, $\nu^{\mathrm{std}}$, $2^{n-1}-\nu^{\mathrm{std}}$) |
| `T1e` | Nilpotent Mirror Conservation & Midpoint-$42$ Invariance | `prove_t1e` / `T1eStmt` | Exact mirror-pair sum invariance across all $2^n$ signatures |
| `T1f` | Exact 2-Blade Left-Annihilator $\mathbb{Z}$-Basis Isomorphism | `prove_t1f` / `T1fStmt` | Full bilinear product `cdMulCoordGamma`: explicit $\mathbb{Z}$-basis of $\ker L_{e_i+e_j}$ of exact cardinality `twobladeNullityGamma` |
| `T2a` | Exact Euclidean 2-Blade Nullity Formula | `prove_t2a` / `T2aStmt` | All $n \ge 1$, $1 \le i < j < 2^n$ |
| `T2b` | Dyadic-Palindromic Terrace Law & Sharp BDI Separation | `prove_t2b` / `T2bStmt` | Exact histogram recursion, $4 \mid \nu$, exact ceiling $2^{n-1}-4$, strict separation `< bdiMaxAnnihilator n` for all $n \ge 5$, AND uniqueness of equality at $n = 4$ among $n \ge 4$ |
| `T2c` | Closed-Form Total 2-Blade Nullity Mass | `prove_t2c` / `T2cStmt` | Exact $M_n = 2^{n-2}(2^{n-1}-1)(2^{n-2}-1)$ for all $n \ge 2$ |
| `T2d` | Non-Zero-Divisor 2-Blade Count | `prove_t2d` / `T2dStmt` | Exact $H_n^{\mathrm{std}}(0) = \frac{1}{3}(4^n + 3\cdot 2^n - 4)$ for all $n \ge 1$ |
| `T3a` | Universal Right-Compatibility Classification | `prove_t3a` / `T3aStmt` | Exact Euclidean classification of all right-compatible basis pairs |
| `T3b` | Exact Compatibility-Graph Clique Number | `prove_t3b` / `T3bStmt` | Exact $\omega(G_n^{\mathrm{comp}}) = n + 5$ for all $n \ge 3$ |
| `T3c` | Dimension-64 Hurwitz--Radon Coordinate Rupture | `prove_t3c` / `T3cStmt` | Explicitly scoped to Euclidean coordinate families vs. closed formula `hurwitzRadon n`: equality on $n \in \{3,4,5\}$ and strict deficit $\ge n-5$ for all $n \ge 6$ |
| `T3d` | Asymmetric Doubling Tower | `prove_t3d` / `T3dStmt` | Constructive $[2^{n-1}, 2(n+4), 2^n]$ Euclidean coordinate pairs for all $n \ge 4$ |
| `T4a` | Sedenion 42-Subspace Fano Duality & $2+2$ Bad-Plane Splitting | `prove_t4a` / `T4aStmt` | All $2^{16}$ masks: exact 42 10D subspaces, 0 at $\ge 11$D, 7/28/7 split, AND every bad sedenion affine 2-plane splits $2+2$ across $\{0..7\}$ and $\{8..15\}$ |
| `T4b` | Sedenion Box-Kite Structural Classification | `prove_t4b` / `T4bStmt` | 42 assessors, 7 disjoint $K_{2,2,2}$ struts derived directly from `isBoxKiteAssessor` without circularity |
| `T4c` | Constructive High-Dimensional Symmetric Coordinate Witnesses | `prove_t4c` / `T4cStmt` | Verified $[14,14,32]$ Pathion and $[16,16,64]$ Chingon Euclidean coordinate witnesses |
| `T4d` | Real/Complex Norm-Multiplicativity vs. Complexification Rigidity | `prove_t4d` / `T4dStmt` | Derives $(c-1)(c+1)=0$ directly from $c^2=1$ in $\mathbb{Z}[i]$ (no pre-factored hypothesis) |
| `T4e` | Pathion Exact Ceiling $r_{\max}(\mathrm{CD}_5)=14$ & $7+7$ Rigidity | `prove_t4e` / `T4eStmt` | Pure-kernel exhaustion over all $2^{32}$ masks and all duplicate-free lists `isNormMultPair 5 S S`: $|S| \le 14$, and $|S|=14 \implies (|S_{\mathrm{lo}}|=7 \land |S_{\mathrm{hi}}|=7)$ |
| `T4f` | Dimension-64 Split-Signature Interior Spectral Gap | `prove_t4f` / `T4fStmt` | Complete 9-bin histogram at $\mathrm{CD}_6(\mathrm{flip}=56)$ proving $H_6^{56}(20) = 0$ and mirror conservation $H_6^{56}(12)+H_6^{56}(20) = 336$ |
| `ALL` | Unified 22-Theorem Master Bundle | `prove_all_terrace_theorems` | Conjunction of all 22 headline theorems (23rd Palomar target) |

## Resolution of All 7 Audit Findings from 2026-11-26

1. **Full algebra & linear map kernel (`T1f`):** Added `cdMulCoordGamma`, `leftMulTwoBladeCoord`, and `twoblade_left_annihilator_basis_exact` proving an explicit $\mathbb{Z}$-basis isomorphism between $\ker L_{e_i+e_j}$ and the singular $2 \times 2$ blocks counted by `twobladeNullityGamma`.
2. **Cross term of $(e_i+e_j)^2$ (`T1c`):** Upgraded `T1cStmt` to assert both the scalar part and explicit cross-term cancellation $e_i e_j + e_j e_i = 0$ under `cdMulCoordGamma`.
3. **Uniqueness of BDI equality at $n=4$ (`T2b`):** Added the explicit uniqueness conjunct `∀ n, 4 ≤ n → (twobladeMaxNullity n = bdiMaxAnnihilator n ↔ n = 4)` directly into `T2bStmt`.
4. **Hurwitz--Radon scope alignment (`T3c`):** Manuscript and Lean both explicitly distinguish the algebraic coordinate-clique bound $\omega(G_n^{\mathrm{comp}}) = n + 5$ (`T3b`), the arithmetic comparison against the closed formula $\rho(2^n)$ (`T3c`), and Hurwitz/Radon's classical identification of $\rho(2^n)$ with maximal real composition dimensions.
5. **Sedenion $2+2$ bad-plane splitting (`T4a`):** Proved directly in `FiniteCertificates.lean` and included in `T4aStmt`.
6. **Non-circular box-kite inter-strut disjointness (`T4b`):** Proved directly from zero-divisor product orthogonality (`isBoxKiteAssessor`) rather than by syntactic definition of `boxKiteAdj`.
7. **Unfactored $\mathbb{Z}[i]$ square root of unity (`T4d`):** Proved `c * c = 1 → c = 1 ∨ c = -1` directly from Gaussian integer multiplication without assuming `(c - 1) * (c + 1) = 0`.

## Palomar Comparator Contract (`lean/comparator.json`)
- **Challenge module:** `PalomarChallenge` (imports `Challenge.lean`, states all 23 targets `CDTerrace.Palomar.prove_t1a` .. `prove_t4f` and `prove_all_terrace_theorems` with intentional `sorry`; excluded from `defaultTargets`).
- **Solution module:** `PalomarSolution` (discharges all 23 targets from `Solution.lean` with zero `sorry` and strictly standard axioms).
- **Comparator enforcement:** `lake comparator --config comparator.json --paranoid` verifies definitional equivalence of all 23 theorem types between `PalomarChallenge` and `PalomarSolution` across all 6 independent kernels and enforces `permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]`. CI also runs a real tamper-injecting negative test on `PalomarSolution` verifying that both comparator and axiom gates reject injected axioms.

## Non-Vacuity & Boundary Sharpness Guardrails
- `CDTerrace.NonVacuity` instantiates 4 concrete non-vacuous witnesses covering all four pillars (`n = 4, 5, 6`, `flipMask = 8` and `56`, `cdMaxClique 6`, `doubledRightWitness 6`, `1023`, `pathionWitness14`, `chingonWitness16`, `GaussInt ⟨0, 1⟩`).
- `CDTerrace.AdversarialTests` proves 8 explicit refutations (`A1`–`A8`), including `refute_pathion_15d_or_unbalanced_14d` (`A7`) and `refute_cd6_split56_contiguous_bins` (`A8`).
