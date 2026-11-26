# Explicit Epistemic Boundaries & Limitations (`LIMITATIONS.md`)

This project adheres to strict epistemic separation. The following problems, extensions, and hypotheses are **explicitly NOT claimed solved or formally proved** by this repository:

1. **General Real Sums-of-Squares Outside Coordinate Subspaces (`ALG-035`, `[OPEN]`):**
   - Theorems `T3c` (Dimension-64 Hurwitz–Radon Bott Rupture) and `C2` (Pathion symmetric rupture $14 < 16$) characterize *coordinate subspaces* under native Cayley–Dickson multiplication. They do **not** settle the general real Hurwitz sums-of-squares problem $[r, s, N]$ over $\mathbb{R}$ for arbitrary bilinear maps, nor do they rule out non-coordinate real subspaces of $\mathrm{CD}_n$ exceeding coordinate bounds.
2. **Higher-Blade ($k \ge 3$) Zero-Divisor Varieties (`ALG-039`, `[OPEN]`):**
   - Pillars 1 and 2 classify all basis *2-blades* $e_i + e_j$ across all $n$ and all $2^n$ signatures. As Theorem `T2b` proves, 2-blades strictly underperform the Biss–Dugger–Isaksen annihilator ceiling $2^n - 4n + 4$ for every $n \ge 5$ ($12 < 16$ at $n = 5$). Full stratification of $k$-blades ($k \ge 3$) and general zero divisors in $\mathrm{CD}_n(\gamma)$ remains open.
3. **Exact Symmetric Coordinate Subspace Ceiling $r_{\max}(\mathrm{CD}_n)$ for $n \ge 6$ (`COMB-040`, `[OPEN]`):**
   - We formally certify $r_{\max}(\mathrm{CD}_3) = 8$, $r_{\max}(\mathrm{CD}_4) = 10$ (`[LEAN-6K]`), computationally certify $r_{\max}(\mathrm{CD}_5) = 14$ via zero-gap HiGHS MILP (`[EXACT-COMP]`), and formally certify the witness lower bound $r_{\max}(\mathrm{CD}_6) \ge 16$ (`[LEAN-6K]`). The exact value of $r_{\max}(\mathrm{CD}_n)$ for $n \ge 6$, as well as lifting the $n = 5$ MILP upper bound into a pure Lean kernel proof, remain open.
4. **All-$n$ Asymptotic Phase Count & Spectral-Gap Theorem for Split Signatures (`[OPEN]`):**
   - Exhaustive audits establish distinct phase counts $4, 8, 16, 32, 64 = 2^{n-2}$ and interior spectral-gap phase counts $0, 0, 2, 6, 14$ for $n = 4, 5, 6, 7, 8$ (`n = 4, 5` in Lean `[LEAN-6K]`; `n = 6, 7, 8` in Rust/C11/Python `[EXACT-COMP]`). Proving the phase count $2^{n-2}$ and classifying all interior spectral-gap signatures for arbitrary $n \ge 6$ remain open.
5. **Mega-Atlas Accounting:**
   - This paper advances research adjacent to Mega-Atlas entries `ALG-035`, `ALG-039`, `XGEOM-031`, and `COMB-040` with **0 grand open problems claimed retired** (`grand_problems_retired = 0`).
6. **External Peer Review Status:**
   - This is an independent, machine-checked research preprint and software artifact; it has not undergone external journal peer review. Its mathematical validity rests transparently on reproducible six-kernel Lean 4.35.0 verification and open-source exact differential code.
