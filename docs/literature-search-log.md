# Literature Search & Live Verification Log (`docs/literature-search-log.md`)

*Generated programmatically by `scripts/check_citations.py --live --write-log` on 2026-11-27 17:57 UTC (version `v2.1.0`).*

## Search Scope & Databases Queried
- **Primary Databases:** Crossref REST API (`https://api.crossref.org/works/{doi}`), arXiv Export API (`https://export.arxiv.org/api/query`), and mathematical historical primary sources.
- **Queries & Thematic Clusters:**
  1. *Cayley–Dickson algebras, twisted group algebras & sign cocycles:* `hurwitz1898`, `dickson1919`, `schafer1954`, `albuquerque1999`, `baez2002`, `moriergenoud2011`.
  2. *Zero divisors, annihilator bounds, box-kites, alternative elements & orthogonality graphs:* `moreno1998`, `demarrais2000`, `demarrais2002`, `cawagas2004`, `moreno2004`, `biss2007ii`, `biss2008i`, `biss2009eigen`, `zhilina2021i`, `zhilina2021ii`, `reggiani2024sedenions`.
  3. *Hurwitz–Radon theorem & sums-of-squares composition of quadratic forms:* `hurwitz1922`, `radon1922`, `adams1962`, `adem1975`, `lam1985`, `yiu1987`, `lamyiu1987`, `yiu1990`, `yiu1994`, `shapiro2000`, `zhangzhu2026hurwitz`.
  4. *Formal proof systems & independent kernel replay:* `demoura2021lean4`, `carneiro2024lean4lean`.

## Live Verification Summary
- **Total BibTeX entries (`paper/references.bib`):** `30` (100% bijective with `\cite{}` keys in `paper/main.tex`).
- **Live API verified (title overlap, primary author surname, year, zero retraction):** `28/30`.
- **Print-only classical works without DOI/arXiv (explicitly reported, never counted as live-verified):** `2` (`hurwitz1898`, `adem1975`).

## Complete 30-Entry Verification Table

| BibTeX Key | Year | First Author | Identifier(s) | Live Check Result |
| --- | --- | --- | --- | --- |
| `hurwitz1898` | 1898 | Hurwitz, Adolf | Print-only classic (no DOI/arXiv) | Print-only classic (no DOI/arXiv; not counted as live-verified) |
| `dickson1919` | 1919 | Dickson, Leonard Eugene | DOI `10.2307/1967865` | Crossref OK: 200 OK (On Quaternions and Their Generalization and the History of the Eight S) |
| `hurwitz1922` | 1922 | Hurwitz, Adolf | DOI `10.1007/BF01448439` | Crossref OK: 200 OK (�ber die Komposition der quadratischen Formen) |
| `radon1922` | 1922 | Radon, Johann | DOI `10.1007/BF02940576` | Crossref OK: 200 OK (Lineare scharen orthogonaler matrizen) |
| `schafer1954` | 1954 | Schafer, Richard D. | DOI `10.2307/2372583` | Crossref OK: 200 OK (On the Algebras Formed by the Cayley-Dickson Process) |
| `adams1962` | 1962 | Adams, J. Frank | DOI `10.2307/1970213` | Crossref OK: 200 OK (Vector Fields on Spheres) |
| `adem1975` | 1975 | Adem, Jos{\'e} | Print-only classic (no DOI/arXiv) | Print-only classic (no DOI/arXiv; not counted as live-verified) |
| `lam1985` | 1985 | Lam, Kee Yuen | DOI `10.1007/BF01388517` | Crossref OK: 200 OK (Some new results on composition of quadratic forms) |
| `yiu1987` | 1987 | Yiu, Paul Y. H. | DOI `10.4153/CMB-1987-045-6` | Crossref OK: 200 OK (Sums of Squares Formulae With Integer Coefficients) |
| `lamyiu1987` | 1987 | Lam, Kee Yuen | DOI `10.1090/conm/058.2/893847` | Crossref OK: 200 OK (Sums of squares formulae near the Hurwitz-Radon range) |
| `yiu1990` | 1990 | Yiu, Paul Y. H. | DOI `10.1093/qmath/41.4.463` | Crossref OK: 200 OK (ON THE PRODUCT OF TWO SUMS OF 16 SQUARES AS A SUM OF SQUARES OF INTEGR) |
| `yiu1994` | 1994 | Yiu, Paul Y. H. | DOI `10.1007/978-94-011-1896-5_2` | Crossref OK: 200 OK (Composition of Sums of Squares with Integer Coefficients) |
| `moreno1998` | 1998 | Moreno, R. Guillermo | arXiv `q-alg/9710013` | arXiv OK: 200 OK (The zero divisors of the Cayley-Dickson algebras over the real numbers) |
| `shapiro2000` | 2000 | Shapiro, Daniel B. | DOI `10.1515/9783110824834` | Crossref OK: 200 OK (Compositions of Quadratic Forms) |
| `demarrais2000` | 2000 | de Marrais, Robert P. C. | arXiv `math/0011260` | arXiv OK: 200 OK (The 42 Assessors and the Box-Kites they fly: Diagonal Axis-Pair System) |
| `baez2002` | 2002 | Baez, John C. | DOI `10.1090/S0273-0979-01-00934-X` | Crossref OK: 200 OK (The octonions) |
| `cawagas2004` | 2004 | Cawagas, Raoul E. | DOI `10.7151/dmgaa.1088` | Crossref OK: 200 OK (On the structure and zero divisors of the Cayley-Dickson sedenion alge) |
| `biss2007ii` | 2007 | Biss, Daniel K. | arXiv `math/0702075` | arXiv OK: 200 OK (Large annihilators in Cayley-Dickson algebras II) |
| `biss2008i` | 2008 | Biss, Daniel K. | DOI `10.1080/00927870701724094`; arXiv `math/0511691` | Crossref OK: 200 OK (Large Annihilators in Cayley–Dickson Algebras); arXiv OK: 200 OK (Large annihilators in Cayley-Dickson algebras) |
| `biss2009eigen` | 2009 | Biss, Daniel K. | DOI `10.1515/FORUM.2009.041`; arXiv `0905.2987` | Crossref OK: 200 OK (Eigentheory of Cayley-Dickson algebras); arXiv OK: 200 OK (Eigentheory of Cayley-Dickson algebras) |
| `demoura2021lean4` | 2021 | de Moura, Leonardo | DOI `10.1007/978-3-030-79876-5_37` | Crossref OK: 200 OK (The Lean 4 Theorem Prover and Programming Language) |
| `carneiro2024lean4lean` | 2024 | Carneiro, Mario | arXiv `2403.14064` | arXiv OK: 200 OK (Lean4Lean: Verifying a Typechecker for Lean, in Lean) |
| `reggiani2024sedenions` | 2024 | Reggiani, Silvio | arXiv `2411.18881` | arXiv OK: 200 OK (The geometry of sedenion zero divisors) |
| `zhangzhu2026hurwitz` | 2026 | Zhang, Chi | arXiv `2605.00590` | arXiv OK: 200 OK (The Hurwitz sum-of-squares problem depends on the base field) |
| `albuquerque1999` | 1999 | Albuquerque, Helena | DOI `10.1006/jabr.1998.7850` | Crossref OK: 200 OK (Quasialgebra Structure of the Octonions) |
| `demarrais2002` | 2002 | de Marrais, Robert P. C. | arXiv `math/0207003` | arXiv OK: 200 OK (Flying Higher Than a Box-Kite: Kite-Chain Middens, Sand Mandalas, and ) |
| `moreno2004` | 2004 | Moreno, R. Guillermo | arXiv `math/0404395` | arXiv OK: 200 OK (Alternative elements in the Cayley-Dickson algebras) |
| `moriergenoud2011` | 2011 | Morier-Genoud, Sophie | DOI `10.1007/s00220-011-1279-9` | Crossref OK: 200 OK (A Series of Algebras Generalizing the Octonions and Hurwitz-Radon Iden) |
| `zhilina2021i` | 2021 | Zhilina, Svetlana | DOI `10.1142/S0218196721500326` | Crossref OK: 200 OK (Orthogonality graphs of real Cayley–Dickson algebras. Part I: Doubly a) |
| `zhilina2021ii` | 2021 | Zhilina, Svetlana | DOI `10.1142/S0218196721500338` | Crossref OK: 200 OK (Orthogonality graphs of real Cayley–Dickson algebras. Part II: The sub) |
