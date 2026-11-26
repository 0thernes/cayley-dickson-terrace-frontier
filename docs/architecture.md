# Architecture & Proof System Design (`docs/architecture.md`)

## System Overview

`cayley-dickson-terrace-frontier` integrates four orthogonal verification layers around a single canonical mathematical model of generalized Cayley–Dickson algebras $\mathrm{CD}_n(\gamma)$:

```text
                +-----------------------------------------------------+
                |   Canonical Mathematical Model: CD_n(gamma)         |
                |   sigma_n^gamma(i,j), blockDelta, nu_n^gamma,       |
                |   G_n^comp, affine 2-planes, norm-multiplicativity  |
                +------------+-------------------+--------------------+
                             |                   |
          +------------------+                   +------------------+
          v                                                         v
+-----------------------------+                       +------------------------------+
|  Lean 4.35.0 (Zero-Mathlib) |                       | Tri-Language Exact Engines   |
|  lean/CDTerrace/*.lean      |                       |  - rust/ (stdlib only)       |
|  - Basic.lean               |                       |  - c/ (ISO C11, ASan/UBSan,  |
|  - MirrorConservation.lean  |                       |    100k + libFuzzer fuzz)    |
|  - TerraceLaw.lean          |                       |  - src/ + reference/oracle   |
|  - HurwitzRupture.lean      |                       |    (naive Q Gauss elim)      |
|  - FiniteCertificates.lean  |                       +--------------+---------------+
|  - NonVacuity.lean          |                                      |
|  - AdversarialTests.lean    |                                      v
+--------------+--------------+                       +------------------------------+
               |                                      | Frozen SHA-256 Artifacts     |
               v                                      |  - data/*.json               |
+-----------------------------+                       |  - paper/figures/*.pdf       |
| Palomar 6-Kernel Contract   |                       |  - dist/*.pdf & arXiv.tar.gz |
| Challenge / PalomarChallenge|                       |  - docs/site/{index,blue...} |
| Solution / PalomarSolution  |                       +------------------------------+
| 6 Independent Proof Kernels |
+-----------------------------+
```

## Key Architectural Decisions

1. **Zero-Mathlib Lean 4.35.0 Core (`ADR-0001`):** Avoiding Mathlib cuts build time to ~90s, removes transitive dependency supply-chain risk, and guarantees clean export to all 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
2. **C-Primitive Pure-Kernel Reduction (`FiniteCertificates.lean`):** Standard `Nat.land`/`Nat.lor` trigger unary `Nat.bitwise` recursion inside MetaM `decide` and hit `maxRecDepth = 512` over $2^{16}$ subspaces. By writing `popcount8`, `disjointBelow`, `forbMask4Direct`, and depth-8 `sumTree` purely via C-primitive `Nat.div`/`Nat.mod`/`Nat.add`, proving them algebraically equal to the textbook definitions, and closing finite evaluations with pure kernel `rfl`, both `leanchecker --fresh` and `leanchecker-paranoid --fresh` pass with zero overrides.
3. **Explicit Arithmetic Rewriting in Witness Modules (`NonVacuity.lean`, `AdversarialTests.lean`):** Numeric arguments inside `@[expose] def` predicates (such as `nullityHist 6 28` vs `nullityHist (5 + 1) (2 ^ 5 - 4)` or `isNormMultMask 4 2047` vs `255 + 256 * 7`) are rewritten explicitly with `rw [show ... from rfl]` prior to theorem application, preventing kernel WHNF from unfolding large finite sums.
4. **Independent First-Principles Oracle (`reference/oracle.py`):** Rather than sharing the fast bitwise formulas, `reference/oracle.py` builds full $2^n \times 2^n$ exact `fractions.Fraction` multiplication matrices from the textbook Cayley–Dickson recursive formula $(a,b)(c,d) = (ac + \gamma_n \bar{d}b, da + b\bar{c})$ and computes nullities via exact rational Gaussian elimination.
