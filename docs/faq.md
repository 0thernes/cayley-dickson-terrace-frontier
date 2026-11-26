# Frequently Asked Questions (`docs/faq.md`)

### Why is the Lean 4.35.0 formalization completely zero-Mathlib?
Zero-Mathlib guarantees a minimal trusted computing base (only Lean 4.35.0 core), fast clean-clone builds (~90 seconds without multi-gigabyte oleans), and smooth deterministic replay across all six independent external proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).

### Does the Dimension-64 Hurwitz–Radon Bott Rupture contradict Hurwitz–Radon–Adams?
No! Hurwitz–Radon–Adams guarantees the existence of an orthogonal $[2^n, \rho(2^n), 2^n]$ real bilinear map via Clifford algebra modules. Our Theorem `T3c` proves that *native Cayley–Dickson coordinate multiplication* saturates $\rho(2^n)$ at dimensions $8, 16, 32$ ($8, 9, 10$), but its right-compatibility clique number grows only linearly as $n + 5$, strictly falling behind the Bott-periodic ceiling $\rho(2^n) \ge 2n$ starting at dimension $64$ ($11 < 12 = \rho(64)$).

### Why does 2-blade nullity separate from the Biss–Dugger–Isaksen ceiling at $n = 5$ instead of $n = 6$?
The exact 2-blade ceiling is $2^{n-1} - 4$, whereas the Biss–Dugger–Isaksen general annihilator ceiling is $2^n - 4n + 4$. At $n = 4$ (sedenions), both equal $4$. Already at $n = 5$ (pathions, $\dim = 32$), $2^{4} - 4 = 12 < 16 = 32 - 20 + 4$, and strict separation holds for every $n \ge 5$ (proved in `twoblade_strictly_below_bdi`).

### Does this paper solve Mega-Atlas `ALG-035`, `ALG-039`, or `COMB-040`?
No (`grand_problems_retired = 0`). It proves new all-$n$ structural theorems and exact finite classifications adjacent to those problems while explicitly documenting all remaining open frontiers in [`LIMITATIONS.md`](../LIMITATIONS.md).

### Why are there `sorry` statements in `lean/PalomarChallenge.lean`?
`PalomarChallenge.lean` is the statement-only challenge contract for `lake comparator --config comparator.json --paranoid`. It is deliberately excluded from `defaultTargets` in `lean/lakefile.toml`, while every theorem in `CDTerrace`, `Solution`, and `PalomarSolution` is 100% `sorry`-free.
