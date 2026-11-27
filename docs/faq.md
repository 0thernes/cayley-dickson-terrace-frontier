# Frequently Asked Questions (`docs/faq.md`)

### Why is the Lean 4.35.0 formalization completely zero-Mathlib?
Zero-Mathlib guarantees a minimal trusted computing base (only Lean 4.35.0 core), fast clean-clone builds without multi-gigabyte oleans, and deterministic replay across all six independent external proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).

### Does Lean prove the actual linear-algebraic annihilator dimension $\dim \ker L_{e_i+e_j}$?
Yes (new in `v2.0.0`). Theorem `T1f` (`twoblade_left_annihilator_basis_exact`) formalizes the full bilinear coordinate product `cdMulCoordGamma` of $\mathrm{CD}_n(\gamma)$ and constructs an explicit $\mathbb{Z}$-basis isomorphism for $\ker L_{e_i+e_j}$ of exact cardinality `twobladeNullityGamma n flipMask i j`.

### Is the Pathion ceiling $r_{\max}(\mathrm{CD}_5) = 14$ proved in Lean, or only by MILP?
As of `v2.0.0`, it is **proved purely inside the Lean 4.35.0 kernel (`T4e`)** across all $2^{32} = 4{,}294{,}967{,}296$ coordinate subsets and all duplicate-free lists (`isNormMultPair 5 S S`), together with strict $7+7$ half-balance rigidity (`|S| = 14 → |S_lo| = 7 ∧ |S_hi| = 7`). HiGHS MILP is retired from the proof trust base, and Rust independently enumerates all `280` 14D subspaces.

### Does the coordinate gap $n + 5 < \rho(2^n)$ (the "dimension-64 rupture") contradict Hurwitz--Radon?
No. The Hurwitz--Radon theorem yields an orthogonal $[2^n, \rho(2^n), 2^n]$ real bilinear map via Clifford modules. Theorem `T3b` proves that in Euclidean $\mathrm{CD}_n$ the largest pairwise right-compatible coordinate basis clique has size $n + 5$, and `T3c` proves that $n + 5 = \rho(2^n)$ on $n \in \{3,4,5\}$ and $n + 5 < \rho(2^n)$ (with deficit $\ge n - 5$) for all $n \ge 6$. Thus canonical coordinate families in Euclidean $\mathrm{CD}_n$ fail to attain $\rho(2^n)$ starting at dimension 64; nothing is claimed against non-coordinate bilinear maps.

### Why does 2-blade nullity separate from the Biss--Dugger--Isaksen ceiling at $n = 5$ instead of $n = 6$?
The exact 2-blade ceiling for $n \ge 4$ is $2^{n-1} - 4$, whereas the Biss--Dugger--Isaksen general annihilator ceiling is $2^n - 4n + 4$. At $n = 4$ (sedenions), both equal $4$, and `T2b` proves equality holds uniquely at $n = 4$ among $n \ge 4$. Already at $n = 5$ (pathions, $\dim = 32$), $2^{4} - 4 = 12 < 16 = 32 - 20 + 4$, and strict separation holds for every $n \ge 5$.

### Does this paper solve Mega-Atlas `ALG-035`, `ALG-039`, or `COMB-040`?
No (`grand_problems_retired = 0`). It proves 22 all-$n$ and exact finite structural theorems adjacent to those open problems while explicitly documenting all remaining open frontiers in [`LIMITATIONS.md`](../LIMITATIONS.md).

### Why are there `sorry` statements in `lean/PalomarChallenge.lean`?
`PalomarChallenge.lean` is the statement-only challenge contract for `lake comparator --config comparator.json --paranoid`. It is deliberately excluded from `defaultTargets` in `lean/lakefile.toml`, while every theorem in `CDTerrace`, `Solution`, and `PalomarSolution` is `sorry`-free.
