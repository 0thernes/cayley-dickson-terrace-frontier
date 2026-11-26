# Statement Fidelity Audit (`docs/statement-fidelity.md`)

This document maps every mathematical definition and theorem in the white paper (`paper/main.tex`) directly to its formal Lean 4.35.0 specification in `lean/Challenge.lean` and `lean/PalomarChallenge.lean`, and records where the Lean statement is narrower than the paper's wording. The known gaps found by the 2026-11-26 statement audit are listed at the end and in [`ERRATA.md`](../ERRATA.md).

## Core Definition Alignment

| Paper Symbol | Mathematical Meaning | Lean 4.35.0 Definition | Module |
| --- | --- | --- | --- |
| $\sigma_n^{\mathrm{std}}(i, j)$ | Euclidean Cayley–Dickson basis sign cocycle | `CDTerrace.cdSign` | `CDTerrace.Basic` |
| $\sigma_n^{\gamma}(i, j)$ | Generalized sign cocycle for flip mask `flipMask` | `CDTerrace.cdSignGamma` | `CDTerrace.Basic` |
| $\delta_n^{\gamma}(i, j, k)$ | $2\times 2$ block determinant sign | `CDTerrace.blockDeltaGamma` | `CDTerrace.Basic` |
| $\nu_n^{\gamma}(i, j)$ | Block-count 2-blade nullity: half the number of singular $2\times 2$ blocks of left multiplication by $e_i + e_j$ (equals $\dim \mathrm{Ann}(e_i+e_j)$ by the paper's block lemma, not formalized) | `CDTerrace.twobladeNullityGamma` | `CDTerrace.Basic` |
| $H_n^{\gamma}(v)$ | Count of $1 \le i < j < 2^n$ with $\nu_n^{\gamma}(i,j) = v$ | `CDTerrace.nullityHistGamma` | `CDTerrace.Basic` |
| $M_n$ | Total Euclidean 2-blade nullity mass | `CDTerrace.totalNullityMass` | `CDTerrace.Basic` |
| $G_n^{\mathrm{comp}}$ | Basis right-compatibility graph | `CDTerrace.rightCompat`, `isCompatClique` | `Basic`, `HurwitzRupture` |
| $\rho(2^n)$ | Closed formula $8\lfloor n/4\rfloor + 2^{n \bmod 4}$ (classically the Hurwitz–Radon number; not proved in Lean) | `CDTerrace.hurwitzRadon` | `CDTerrace.Basic` |
| $[|S_L|, |S_R|, 2^n]$ | Coordinate norm-multiplicative pair | `CDTerrace.isNormMultPair`, `isNormMultMask` | `HurwitzRupture`, `FiniteCertificates` |

## Palomar Comparator Contract (`lean/comparator.json`)
- **Challenge module:** `PalomarChallenge` (imports `Challenge.lean`, states all 20 target signatures `CDTerrace.Palomar.prove_t1a` .. `prove_t4d` and `prove_all_terrace_theorems` with intentional `sorry`; excluded from `defaultTargets`).
- **Solution module:** `PalomarSolution` (discharges all 20 targets from `Solution.lean` with zero `sorry` and strictly standard axioms).
- **Comparator enforcement:** `lake comparator --config comparator.json --paranoid` checks definitional equivalence of all 20 theorem types between `PalomarChallenge` and `PalomarSolution` across all 6 independent kernels and enforces `permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]`.

## Non-Vacuity & Boundary Sharpness Guardrails
- `CDTerrace.NonVacuity` instantiates concrete non-vacuous witnesses for every universal pillar (`n = 4, 5, 6`, `flipMask = 8`, `cdMaxClique 6`, `doubledRightWitness 6`, `1023`, `pathionWitness14`, `chingonWitness16`, `GaussInt ⟨0, 1⟩`).
- `CDTerrace.AdversarialTests` proves 6 explicit negations showing that every bound (`n >= 5` for BDI separation, `n >= 6` for Hurwitz–Radon rupture, `dim <= 10` for sedenion coordinate subspaces, `{0, 2^(n-1)}` for universal multipliers, mirror-sum vs. individual-bin invariance, and `{+1, -1}` in `Z[i]`) is sharp.

## Known Fidelity Gaps (2026-11-26 statement audit)
- No algebra, linear map or kernel is defined in Lean; all nullity statements concern the sign table and block counts (see the table above).
- `T1cStmt` states only the scalar part of $(e_i+e_j)^2$; the cross term is not stated.
- `T2bStmt`'s comparison with Biss–Dugger–Isaksen compares the closed formulas `twobladeMaxNullity` and `bdiMaxAnnihilator`; "equality only at $n = 4$" (among $n \ge 4$) is not stated.
- `T3cStmt` contains no algebra; it is arithmetic on the formula for $\rho(2^n)$. Pillar 3 covers the Euclidean signature and coordinate subsets only.
- `T4aStmt` does not contain the paper's clause that every bad affine 2-plane splits $2 + 2$.
- `T4bStmt`'s "no edges between classes" conjunct holds by the definition of `boxKiteAdj`.
- `T4dStmt` part 2 takes the factorization $(c-1)(c+1) = 0$ as a hypothesis; the rigidity conjuncts are elementary unit facts.
- Audit log: https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md
