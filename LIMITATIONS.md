# Explicit Epistemic Boundaries & Limitations (`LIMITATIONS.md`)

This project keeps proved, computed and open statements separate. The following problems, extensions and hypotheses are **not claimed solved or formally proved** by this repository. Items 7–12 were added after the 2026-11-26 statement audit ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)).

1. **General Real Sums-of-Squares Outside Coordinate Subspaces (`ALG-035`, `[OPEN]`):**
   - Theorems `T3b`–`T3c` (the coordinate gap $n+5 < \rho(2^n)$ for $n \ge 6$ in the Euclidean $\mathrm{CD}_n$) and `C2` ($r_{\max}(\mathrm{CD}_5) = 14$) concern *coordinate subsets* under native Cayley–Dickson multiplication. They do **not** settle the general real Hurwitz sums-of-squares problem $[r, s, N]$ over $\mathbb{R}$ for arbitrary bilinear maps, nor do they rule out non-coordinate real subspaces of $\mathrm{CD}_n$ exceeding coordinate bounds.
2. **Higher-Blade ($k \ge 3$) Zero-Divisor Varieties (`ALG-039`, `[OPEN]`):**
   - Pillars 1 and 2 treat the basis *2-blades* $e_i + e_j$ for all $n$ (Pillar 1 and `T2f` for all $2^n$ signatures, `T2a`–`T2e` for the Euclidean signature). The 2-blade ceiling $2^{n-1}-4$ lies below the Biss–Dugger–Isaksen annihilator bound $2^n - 4n + 4$ for every $n \ge 5$ ($12 < 16$ at $n = 5$). Full stratification of $k$-blades ($k \ge 3$) and of general zero divisors in $\mathrm{CD}_n(\gamma)$ remains open.
3. **Exact Symmetric Coordinate Subspace Ceiling $r_{\max}(\mathrm{CD}_n)$ for $n \ge 6$ (`COMB-040`, `[OPEN]`):**
   - We formally certify $r_{\max}(\mathrm{CD}_3) = 8$, $r_{\max}(\mathrm{CD}_4) = 10$ (`[LEAN-6K]`), computationally certify $r_{\max}(\mathrm{CD}_5) = 14$ via zero-gap HiGHS MILP (`[EXACT-COMP]`), and formally certify the witness lower bound $r_{\max}(\mathrm{CD}_6) \ge 16$ (`[LEAN-6K]`). The exact value of $r_{\max}(\mathrm{CD}_n)$ for $n \ge 6$, as well as lifting the $n = 5$ MILP upper bound into a pure Lean kernel proof, remain open.
4. **All-$n$ Asymptotic Phase Count & Spectral-Gap Theorem for Split Signatures (`[OPEN]`):**
   - Exhaustive audits establish distinct phase counts $4, 8, 16, 32, 64 = 2^{n-2}$ and interior spectral-gap phase counts $0, 0, 2, 6, 14$ for $n = 4, 5, 6, 7, 8$ (`n = 4, 5` in Lean `[LEAN-6K]`; `n = 6, 7, 8` in Rust/C11/Python `[EXACT-COMP]`). Proving the phase count $2^{n-2}$ and classifying all interior spectral-gap signatures for arbitrary $n \ge 6$ remain open.
5. **Mega-Atlas Accounting:**
   - This paper advances research adjacent to Mega-Atlas entries `ALG-035`, `ALG-039`, `XGEOM-031`, and `COMB-040` with **0 grand open problems claimed retired** (`grand_problems_retired = 0`). The four questions posed in the manuscript are the author's own; they are not taken from a published source.
6. **External Peer Review Status:**
   - This is an independent research preprint and software artifact; it has not undergone external journal peer review. The `[LEAN-6K]` results rest on Lean kernel checking; the link between the Lean counts and annihilator dimensions (item 7) and the `[EXACT-COMP]` results rest on the paper's arguments and on exact computation.
7. **What the Lean statements are about:**
   - The Lean development defines no algebra, linear map or kernel. It proves statements about the explicit Cayley–Dickson sign table (`cdSign`, `cdSignGamma`) and about block counts (`twobladeNullity` is half the number of singular $2\times 2$ blocks). That this count equals $\dim \mathrm{Ann}(e_i+e_j)$ is a lemma proved in the paper, not in Lean.
8. **Statements narrower than their names:**
   - `T1c` states only the scalar part of $(e_i+e_j)^2$; the cross term is not part of the statement.
   - `T2b`'s comparison with Biss–Dugger–Isaksen compares two closed formulas; the BDI theorem is not formalized. "Equality only at $n = 4$" holds among $n \ge 4$ and is not stated in Lean.
   - `T3c` is arithmetic on the formula $8\lfloor n/4\rfloor + 2^{n \bmod 4}$; that this formula is the Hurwitz–Radon number $\rho(2^n)$ is classical and not proved in Lean. Pillar 3 covers the Euclidean signature only, although the manuscript title says "Across Generalized Cayley–Dickson Algebras".
   - `T4b`'s "no edges between box-kites" conjunct holds by the definition of the adjacency predicate; the other conjuncts already force the 7 × $K_{2,2,2}$ structure.
   - `T4d`'s rigidity conjuncts ($c^2 = 1 \Rightarrow c = \pm 1$ in integral domains, $\mathbb{Z}$, $\mathbb{Z}[i]$) are textbook facts with the factorization taken as a hypothesis; no intercalate matrix or composition formula appears, and they do not bear on Zhang–Zhu (2026).
9. **Prior work not compared in full:**
   - `T2b`'s $4 \mid \nu$ is the 2-blade case of Moreno's theorem (stated in Biss–Dugger–Isaksen, arXiv:math/0511691). The 42 assessors and 7 box-kites are de Marrais's (arXiv:math/0011260).
   - Zhilina (Int. J. Algebra Comput. 31 (2021); arXiv:2608.28176) classifies zero divisors whose components are standard basis elements up to sign; its overlap with `T1c`, `T2a` and `T2c` has not been assessed.
   - Not compared: Moreno on alternative elements (arXiv:math/0404395), de Marrais's later papers on higher $2^n$-ion assessors, Adem (1975) on normed maps from Cayley–Dickson algebras, and the twisted group-algebra description of Cayley–Dickson algebras (Albuquerque–Majid; Morier-Genoud–Ovsienko); a prior statement of the `T1a` cocycle formula there is not ruled out.
10. **Citation checking:**
    - `scripts/check_citations.py --live` checks that each DOI or arXiv identifier resolves; it does not compare titles, authors or years. Two of the 24 BibTeX entries (`adem1975`, `lamyiu1987`) have no identifier and are not checked. The `hurwitz1898` DOI resolves to the Werke reprint of Hurwitz's 1922 paper, not the 1898 paper (see [`ERRATA.md`](ERRATA.md)).
11. **CI negative test:**
    - The CI step "Live negative Lean audit" checks that `#print axioms` reports an axiom injected into a throwaway file under `/tmp`. It does not modify a project file and does not exercise the axiom-diff or comparator steps.
12. **Six-kernel replay evidence:**
    - The six-kernel replay is recorded only as CI step results; per-kernel logs are not published as artifacts, and the 2026-11-26 audit did not re-run it.
