# Errata (`ERRATA.md`)

This file records errors and overstatements found after the **v1.0.0** release (`0TH-2026-019`). The frozen manuscript (`paper/main.tex`, `paper/references.bib`, `dist/`) and the Lean sources are not changed in place; each entry gives the location, the problem, the correction, and whether a theorem statement is affected. The repository's Markdown claim documents (`README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `docs/`) already use the corrected wording.

To report an issue, open a structured report via GitHub Issues or contact `0_0@0thernes.art`.

## 2026-11-26 statement audit

Source: independent statement audit of the commit `f1a3ff375a945923b48a7f8fca5fb06f3ae93e88` ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)). The audit re-ran `lake build` and `VerifyAxioms.lean` (pass; the 30 audited declarations use at most `propext`, `Classical.choice`, `Quot.sound`). None of the items below makes a Lean proof wrong; they concern what the statements mean, what is credited, and how they are described.

### Manuscript (`paper/main.tex`, `paper/references.bib`, frozen PDF)

1. **Meaning of "nullity" (all of Pillars 1–2).**
   - *Where:* `paper/main.tex`, definition of $\nu_n^\gamma$ and the statements of `T1d`–`T2f`; `lean/CDTerrace/Basic.lean` lines 93–99.
   - *What is wrong:* The paper presents the Lean theorems as statements about left-annihilator dimensions. Lean defines $\nu$ as half the number of singular $2\times 2$ blocks in the sign table; the identification with $\dim \mathrm{Ann}(e_i+e_j)$ is the paper's $2\times 2$ block lemma and is not formalized.
   - *Correction:* State that the Lean results concern the explicit sign table and block counts, and that "count = annihilator dimension" is a paper lemma. (The audit checked the block argument by hand and found it correct.)
   - *Affects a theorem statement:* No (affects the reading of every nullity theorem).
2. **"Resolves all four questions."**
   - *Where:* `paper/main.tex` line 211 (Introduction).
   - *What is wrong:* The four questions are posed by the author (lines 193–209), and parts of them stay open (`LIMITATIONS.md` items 3–4).
   - *Correction:* "This work addresses these questions; Section 7 lists what remains open."
   - *Affects a theorem statement:* No.
3. **Moreno's multiple-of-four theorem not credited for `T2b`.**
   - *Where:* `paper/main.tex` lines 553–566 (Theorem `T2b`).
   - *What is wrong:* $4 \mid \nu$ is the 2-blade case of Moreno's theorem that only multiples of four occur as annihilator dimensions (stated in Biss, Dugger, Isaksen, arXiv:math/0511691). The paper cites Moreno only for the $V_{7,2}$/$G_2$ identification (line 172).
   - *Correction:* Attribute the divisibility to Moreno and describe the Lean proof as an independent re-proof for 2-blades.
   - *Affects a theorem statement:* No (credit only).
4. **"Equality holds uniquely at $n = 4$."**
   - *Where:* `paper/main.tex` line 562 (Theorem `T2b`) and line 1011 (Figure 5 caption).
   - *What is wrong:* At $n = 3$ the true 2-blade maximum and the BDI bound are both $0$, so uniqueness fails without a range; uniqueness is also not part of the Lean statement `T2bStmt`, whose second conjunct compares the closed formulas `twobladeMaxNullity` and `bdiMaxAnnihilator` (`lean/CDTerrace/Basic.lean` lines 167–172).
   - *Correction:* "Among $n \ge 4$, equality holds only at $n = 4$." Describe the BDI comparison as arithmetic on two formulas; the BDI theorem is not formalized.
   - *Affects a theorem statement:* Yes (the paper's `T2b` claims more than `T2bStmt` states).
5. **Uncited prior classification (Zhilina).**
   - *Where:* `paper/main.tex` lines 167–211 (related work); `paper/references.bib`.
   - *What is wrong:* Zhilina, *Orthogonality graphs of real Cayley–Dickson algebras. Part I*, Int. J. Algebra Comput. 31 (2021) (arXiv:2608.28176), classifies zero divisors whose components are standard basis elements up to sign. It is not cited, and line 193 says these questions "remained unified only in fragments".
   - *Correction:* Cite Zhilina and state what is new relative to her results. The overlap with `T1c`, `T2a` and `T2c` has not been assessed.
   - *Affects a theorem statement:* No (novelty claim).
6. **Other related work not cited.**
   - *Where:* `paper/references.bib`; related-work section.
   - *What is wrong:* Moreno, arXiv:math/0404395 (alternative elements of the Cayley–Dickson algebras), and de Marrais's later papers on assessors in higher $2^n$-ions are not cited. Only `moreno1998` and `demarrais2000` appear.
   - *Correction:* Cite and compare. Moreno's paper concerns a related but different condition from `T3a`.
   - *Affects a theorem statement:* No.
7. **"Dimension-64 Hurwitz–Radon (Bott) Rupture" (`T3c`), title and Pillar 3 heading.**
   - *Where:* `paper/main.tex` lines 70–72 (title), 115–120 (abstract), 243 (Table 1), 704 (Section heading), 797 (Theorem `T3c`), 849 (Figure 3 caption); `lean/Challenge.lean` lines 115–119.
   - *What is wrong:* `T3cStmt` is arithmetic on the formula `hurwitzRadon n = 8*(n/4) + 2^(n % 4)`; no Bott-periodicity argument is formalized, and that the formula equals $\rho(2^n)$ is classical, not proved. The meaning comes from `T3b`, which concerns coordinate subsets in the Euclidean $\mathrm{CD}_n$ only, while the title says "Across Generalized Cayley–Dickson Algebras".
   - *Correction:* "The largest coordinate right-multiplier family in the Euclidean $\mathrm{CD}_n$ has $n + 5$ elements; this equals $\rho(2^n)$ for $n = 3, 4, 5$ and is smaller for every $n \ge 6$ (first at dimension 64: $11 < 12$)." Label `T3c` an arithmetic corollary.
   - *Affects a theorem statement:* No (description and scope).
8. **`T4d` "base-field rigidity illuminating Zhang–Zhu".**
   - *Where:* `paper/main.tex` lines 131–133 (abstract), 996–1002 (Remark on Yiu and Zhang–Zhu); `lean/Challenge.lean` lines 186–195.
   - *What is wrong:* The rigidity conjuncts of `T4dStmt` are elementary unit facts ($c^2 = 1 \Rightarrow c = \pm 1$ in integral domains, $\mathbb{Z}$, $\mathbb{Z}[i]$), with the factorization $(c-1)(c+1) = 0$ taken as a hypothesis. No intercalate matrix, sum-of-squares formula or base field appears. The sentence "genuine multi-term superposition is algebraically mandatory for base-field dependence" (lines 1001–1002) is not implied by `T4d`.
   - *Correction:* Describe these conjuncts as "$c^2 = 1$ forces $c = \pm 1$ in integral domains, $\mathbb{Z}$ and $\mathbb{Z}[i]$", and delete the Zhang–Zhu inference and the sentence at lines 1001–1002.
   - *Affects a theorem statement:* No (the Lean statement is correct; its description is not).
9. **Comparison with Yiu's $[16,16,32]$ formula.**
   - *Where:* `paper/main.tex` lines 130–131 (abstract), 978 (Proposition), 996–997 (Remark).
   - *What is wrong:* $r_{\max}(\mathrm{CD}_5) = 14$ is a maximum over symmetric coordinate subsets of $\mathrm{CD}_5$ (MILP certificate, outside Lean); Yiu's $[16,16,32]$ is a general integral bilinear formula. "Strictly below Yiu" compares different objects.
   - *Correction:* "No 16-element symmetric norm-multiplicative coordinate subset of $\mathrm{CD}_5$ exists (MILP certificate)."
   - *Affects a theorem statement:* No.
10. **`T4a`(1) clause not formalized.**
    - *Where:* `paper/main.tex` lines 878–880 (Theorem `T4a`(1)); `lean/Challenge.lean` `T4aStmt`.
    - *What is wrong:* The clause "every bad affine 2-plane splits $2 + 2$ across $\{1,\dots,7\} \times \{9,\dots,15\}$" is not part of `T4aStmt`, which counts planes and masks only.
    - *Correction:* Tag the clause `[paper]` (or add it to `T4aStmt` in a later version).
    - *Affects a theorem statement:* Yes (the paper's `T4a` is stronger than the Lean statement).
11. **"42 Box-Kites".**
    - *Where:* paper and earlier `CLAIMS.md` row `T4b`.
    - *What is wrong:* There are 7 box-kites and 42 assessors; the structure is de Marrais's (arXiv:math/0011260).
    - *Correction:* "42 box-kite assessors forming de Marrais's 7 box-kites, each $K_{2,2,2}$ (formal re-verification of a known result)."
    - *Affects a theorem statement:* No.
12. **Wrong DOI for `hurwitz1898`.**
    - *Where:* `paper/references.bib` lines 4–11.
    - *What is wrong:* DOI `10.1007/978-3-0348-4160-3_46` resolves (Crossref) to *Über die Komposition der quadratischen Formen*, Mathematische Werke (1963), pp. 641–666, which is the reprint of Hurwitz's 1922 paper, not the 1898 paper.
    - *Correction:* Remove the DOI or replace it with one for the 1898 paper.
    - *Affects a theorem statement:* No.
13. **"24 live-verified / title-verified citations".**
    - *Where:* earlier `README.md` repository map, `CHANGELOG.md` 1.0.0 entry, `ROADMAP.md`, `docs/run-log.md`, `docs/threat-model.md`, `docs/reviews/adversarial-red-team-review.md`.
    - *What is wrong:* `scripts/check_citations.py` only checks that a DOI or arXiv identifier resolves; it never compares titles. `adem1975` and `lamyiu1987` have no identifier and are skipped silently, yet the script prints "PASS: 24 BibTeX entries verified".
    - *Correction:* "22 of 24 bibliography identifiers resolve live (titles are not compared; 2 entries have no identifier)." The script should compare title, first author and year and report identifier-less entries as unverified.
    - *Affects a theorem statement:* No.

### Known issues in the formal code (not yet fixed)

1. **`lean/CDTerrace/Basic.lean` lines 93–99.** The docstrings of `twobladeNullityGamma` and `twobladeNullity` say "Exact 2-blade left-annihilator nullity". The definitions are block counts. *Correction:* "Block-count 2-blade nullity (equals the left-annihilator dimension by the 2×2 block lemma in the paper)." *Affects a theorem statement:* No (docstring only).
2. **`lean/Challenge.lean` lines 34–37 (`T1cStmt`).** States only that the diagonal signs cancel, $\sigma^\gamma(i,i) + \sigma^\gamma(j,j) = 0$; the cross term of $(e_i+e_j)^2$ is not stated, although the docstring calls it an "exact 2-blade nilpotency criterion". *Correction:* add $\sigma^\gamma(i,j) + \sigma^\gamma(j,i) = 0$ for distinct nonzero $i, j$ (true by `T1a` and anticommutativity). *Affects a theorem statement:* Yes (`T1c` is weaker than its name).
3. **`lean/Challenge.lean` lines 70–73 (`T2bStmt`).** The second conjunct compares two closed-form definitions; attainment of the ceiling and "equality only at $n = 4$" are not in the statement. *Correction:* state the maximum over pairs directly and restrict the equality claim to $n \ge 4$. *Affects a theorem statement:* Yes (narrower than the paper's `T2b`).
4. **`lean/CDTerrace/FiniteCertificates.lean` lines 1620–1623 (`boxKiteAdj`).** The adjacency predicate begins with the XOR-class test `p.1 ^^^ p.2 == q.1 ^^^ q.2`, so the `T4b` conjunct "no edges between classes" holds by definition. Conjuncts 2–3 still force 7 × $K_{2,2,2}$. *Correction:* define adjacency by the vanishing product only. *Affects a theorem statement:* Yes (one conjunct of `T4b` is vacuous).
5. **`lean/Challenge.lean` lines 186–195 (`T4dStmt`, part 2).** The factorization $(c-1)(c+1) = 0$ for $c^2 = 1$ is taken as a hypothesis, so the conclusion $c = \pm 1$ is immediate from the no-zero-divisor hypothesis. *Correction:* describe as an elementary lemma, or prove a theorem about signed intercalate formulas. *Affects a theorem statement:* No (statement is correct; it is weaker than its description).
6. **`lean/Challenge.lean` lines 115–117 (`T3c` docstring).** Calls an inequality on the formula `hurwitzRadon` a "Dimension-64 Hurwitz–Radon Bott Rupture". *Correction:* "arithmetic comparison of $n + 5$ with the formula $8\lfloor n/4\rfloor + 2^{n \bmod 4}$". *Affects a theorem statement:* No.
7. **`lean/CDTerrace/FiniteCertificates.lean` lines 10–11.** The module docstring says "instant on all 6 kernels"; the module takes about 99 s to build. *Correction:* remove "instant". *Affects a theorem statement:* No.
8. **Label drift.** `lean/CDTerrace/HurwitzRupture.lean` docstrings use labels `T3a`–`T3e`; `Challenge.lean` and `CLAIMS.md` use `T3a`–`T3d`. *Correction:* align the labels. *Affects a theorem statement:* No.

### Tooling (not yet fixed)

1. **`.github/workflows/ci.yml` lines 62–67.** The step "Live negative Lean audit (verify injected sorry/axiom fails rejection check)" writes `axiom bogus : False` to `/tmp/neg_test.lean` and checks that `#print axioms` reports it. It tests no project file, no `sorry`, and neither the axiom diff nor the comparator. *Correction:* inject an axiom into a copy of a project file and assert that the axiom-diff or comparator step fails, or describe the step as a sanity check of `#print axioms`.
2. **`scripts/check_citations.py`.** See manuscript item 13.
