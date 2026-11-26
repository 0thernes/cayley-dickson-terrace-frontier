# Frequently Asked Questions (`docs/faq.md`)

### Why is the Lean 4.35.0 formalization completely zero-Mathlib?
Zero-Mathlib guarantees a minimal trusted computing base (only Lean 4.35.0 core), fast clean-clone builds (~90 seconds without multi-gigabyte oleans), and smooth deterministic replay across all six independent external proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).

### Does the coordinate gap $n + 5 < \rho(2^n)$ (the manuscript's "dimension-64 rupture") contradict Hurwitz–Radon?
No. The Hurwitz–Radon theorem gives an orthogonal $[2^n, \rho(2^n), 2^n]$ real bilinear map via Clifford modules. Theorem `T3b` shows that in the Euclidean $\mathrm{CD}_n$ the largest set of basis elements with pairwise compatible right multiplications has $n + 5$ elements. `T3c` is arithmetic on the formula $\rho(2^n) = 8\lfloor n/4\rfloor + 2^{n \bmod 4}$: $n + 5$ equals it for $n = 3, 4, 5$ (dimensions $8, 16, 32$) and is smaller for every $n \ge 6$ (first at dimension 64: $11 < 12$). So coordinate families in the Euclidean $\mathrm{CD}_n$ do not reach $\rho(2^n)$ from dimension 64 on; nothing is claimed about non-coordinate subspaces or general bilinear maps.

### Why does 2-blade nullity separate from the Biss–Dugger–Isaksen ceiling at $n = 5$ instead of $n = 6$?
The 2-blade ceiling (for $n \ge 4$, attained) is $2^{n-1} - 4$, whereas the Biss–Dugger–Isaksen general annihilator ceiling is $2^n - 4n + 4$. At $n = 4$ (sedenions), both equal $4$. Already at $n = 5$ (pathions, $\dim = 32$), $2^{4} - 4 = 12 < 16 = 32 - 20 + 4$, and strict separation holds for every $n \ge 5$ (`twoblade_strictly_below_bdi`, which compares the two closed formulas; the BDI theorem itself is not formalized). The divisibility $4 \mid \nu$ is the 2-blade case of Moreno's multiple-of-four theorem (stated in Biss–Dugger–Isaksen, arXiv:math/0511691).

### Does this paper solve Mega-Atlas `ALG-035`, `ALG-039`, or `COMB-040`?
No (`grand_problems_retired = 0`). It proves new all-$n$ structural theorems and exact finite classifications adjacent to those problems while explicitly documenting all remaining open frontiers in [`LIMITATIONS.md`](../LIMITATIONS.md).

### Why are there `sorry` statements in `lean/PalomarChallenge.lean`?
`PalomarChallenge.lean` is the statement-only challenge contract for `lake comparator --config comparator.json --paranoid`. It is deliberately excluded from `defaultTargets` in `lean/lakefile.toml`, while every theorem in `CDTerrace`, `Solution`, and `PalomarSolution` is `sorry`-free.
