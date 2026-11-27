# Errata & Resolution Ledger (`ERRATA.md`)

This file maintains the permanent public record of every error, overstatement, statement-fidelity gap, and tooling defect logged against **v1.0.0** (`0TH-2026-019`) and documents its exact resolution in **v2.0.0** (2026-11-26).

To report a new issue or mathematical discrepancy, open a structured finding report via GitHub Issues or contact `0_0@0thernes.art`.

---

## Summary Status

- **v1.0.0 audit entries total:** 23 (13 manuscript, 8 formal Lean, 2 tooling).
- **Resolved in v2.0.0:** **23 / 23 (100%)** — every item resolved directly in the Lean 4.35.0 proofs, manuscript (`paper/main.tex`, `paper/references.bib`, `dist/`), multi-language engines, and GitHub Actions CI.
- **Open errata in v2.0.0:** **0**.

---

## Resolution of 2026-11-26 Statement Audit (v1.0.0 -> v2.0.0)

Source audit: independent statement audit of v1.0.0 commit `f1a3ff375a945923b48a7f8fca5fb06f3ae93e88` ([audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)).

### Manuscript Items (`M1`–`M13`) — All Resolved in `v2.0.0`

| ID | v1.0.0 Finding | Status | Exact Resolution in `v2.0.0` |
| --- | --- | --- | --- |
| M1 | Meaning of "nullity": Lean defined block counts; identification with $\dim \ker L_{e_i+e_j}$ was a paper lemma only. | **RESOLVED** | Formalized literal bilinear product `cdMulCoordGamma` in `CDTerrace.Basic` and proved **Theorem `T1f` (`twoblade_left_annihilator_basis_exact`)** in `CDTerrace.MirrorConservation`, establishing an explicit 2-sparse linearly independent spanning $\mathbb{Z}$-basis of $\ker L_{e_i+e_j}$ of exact cardinality `twobladeNullityGamma`. |
| M2 | Introduction claimed "resolves all four questions" even though parts remain open. | **RESOLVED** | Reworded `paper/main.tex` to "addresses these four questions through four formally verified algebraic pillars... Section 8 states explicitly what remains open." |
| M3 | Moreno's multiple-of-four theorem not credited for `T2b` ($4 \mid \nu$). | **RESOLVED** | Explicitly credited Moreno (1998) and Biss–Dugger–Isaksen (2008) in `paper/main.tex`, `TerraceLaw.lean`, `CLAIMS.md`, and `README.md`, framing the Lean proof as an independent 2-blade proof. |
| M4 | "Equality holds uniquely at $n = 4$" omitted $n \ge 4$ range and was not formalized in `T2bStmt`. | **RESOLVED** | Added `twoblade_ceiling_attained` ($\nu_n^{\mathrm{std}}(1, 2+2^{n-1}) = 2^{n-1}-4$) and `twoblade_bdi_eq_iff_four` ($n \ge 4 \implies (\text{eq} \iff n = 4)$) directly into `T2bStmt`; updated `paper/main.tex` and Fig. 5 to state "among $n \ge 4$, equality holds iff $n = 4$." |
| M5 | Zhilina (2021) not cited in related work. | **RESOLVED** | Added verified DOIs for Zhilina Parts I & II (`zhilina2021i`, `zhilina2021ii`) in `paper/references.bib` and compared explicitly in Section 1 of `paper/main.tex` (noting overlap with Euclidean basis-pair zero divisors). |
| M6 | Moreno (2004), de Marrais (2002), Albuquerque–Majid (1999), and Morier-Genoud–Ovsienko (2011) not cited. | **RESOLVED** | Added all four live-verified references (`moreno2004`, `demarrais2002`, `albuquerque1999`, `moriergenoud2011`) to `paper/references.bib` and integrated explicit comparisons in `paper/main.tex`. |
| M7 | Pillar 3 / `T3c` title & description overstated Bott periodicity and generalized-signature scope. | **RESOLVED** | Updated title, abstract, Section 5, and `Challenge.lean`: explicitly scoped Pillar 3 to Euclidean $\mathrm{CD}_n$ coordinate right-multiplier families and labeled `T3c` an arithmetic corollary comparing $n + 5$ against the classical formula $\rho(2^n)$. |
| M8 | `T4d` rigidity conjunct took factorization as hypothesis and overstated connection to Zhang–Zhu (2026). | **RESOLVED** | Replaced pre-factored lemma with ring-axiom-derived `domain_sq_eq_one_imp` in `FiniteCertificates.lean`; deleted the unsupported Zhang–Zhu inference in `paper/main.tex` and described `T4d`(2) accurately as an elementary unit-square lemma. |
| M9 | Comparison of $r_{\max}(\mathrm{CD}_5) = 14$ with Yiu's $[16,16,32]$ compared different object classes and relied on external MILP. | **RESOLVED** | Proved **`T4e` (`pathion_exact_ceiling_14_and_7_7_rigidity`)** purely inside the Lean kernel across all $2^{32}$ subsets (retiring HiGHS MILP from the proof trust base!) and stated explicitly in `paper/main.tex` that `T4e` bounds coordinate subsets of $\mathrm{CD}_5$ whereas Yiu's $[16,16,32]$ is a general non-Cayley–Dickson integral bilinear form. |
| M10 | `T4a`(1) clause "every bad affine 2-plane splits $2 + 2$" was not in `T4aStmt`. | **RESOLVED** | Formalized `sedenion_bad_planes_split_2_2` in `FiniteCertificates.lean` and added it directly to `T4aStmt`. |
| M11 | Wording "42 Box-Kites" blurred 7 box-kites vs. 42 assessors and lacked de Marrais attribution. | **RESOLVED** | Corrected everywhere to "42 assessors forming de Marrais's 7 box-kites ($7 \times K_{2,2,2}$), formal re-verification of a known result." |
| M12 | Wrong DOI (`10.1007/978-3-0348-4160-3_46`, 1922 Werke reprint) on `hurwitz1898`. | **RESOLVED** | Removed mismatched 1922 DOI from `hurwitz1898` (reported cleanly as print-only classic); added verified DOI `10.1090/conm/058.2/893847` to `lamyiu1987`. |
| M13 | Citation checker skipped title/author/year comparison and counted identifier-less entries as live-verified. | **RESOLVED** | Upgraded `scripts/check_citations.py --live` to verify Crossref/arXiv title overlap, author surname, year tolerance, Crossref retraction metadata, bijective `\cite{}` coverage vs. `paper/main.tex`, and explicit reporting of print-only entries (`28/30` live-verified + `2` print-only classics). |

### Formal Lean Items (`F1`–`F8`) — All Resolved in `v2.0.0`

| ID | v1.0.0 Finding | Status | Exact Resolution in `v2.0.0` |
| --- | --- | --- | --- |
| F1 | `Basic.lean` docstrings called `twobladeNullityGamma` left-annihilator dimension without formal proof. | **RESOLVED** | Updated docstrings to cross-reference the newly formalized kernel-basis theorem `T1f` (`twoblade_left_annihilator_basis_exact`). |
| F2 | `T1cStmt` stated only diagonal cancellation, omitting cross-term cancellation of $(e_i+e_j)^2$. | **RESOLVED** | Added `cdSignGamma_anticomm` and `twoblade_nilpotent_full_iff` (all $2^n$ coordinates of `cdMulCoordGamma` vanish) directly into `T1cStmt`. |
| F3 | `T2bStmt` omitted ceiling attainment and uniqueness at $n = 4$ among $n \ge 4$. | **RESOLVED** | Added `twoblade_ceiling_attained` and `twoblade_bdi_eq_iff_four` directly into `T2bStmt`. |
| F4 | `boxKiteAdj` pre-filtered by `p.1 ^^^ p.2 == q.1 ^^^ q.2`, making the zero-cross-edge conjunct vacuous. | **RESOLVED** | Replaced `boxKiteAdj` with pure algebraic vanishing-product predicate across all 16 coordinates (`bladeProdCoord4`, proved equal to full `cdMulCoordGamma`), making `T4b`'s zero-cross-edge conjunct genuinely non-vacuous. |
| F5 | `T4dStmt` part 2 assumed factorization `(c - 1)(c + 1) = 0` as a hypothesis. | **RESOLVED** | Replaced with `domain_sq_eq_one_imp` deriving $(c-1)(c+1)=0$ from the commutative-domain ring axioms directly. |
| F6 | `T3cStmt` docstring called arithmetic comparison a "Bott Rupture". | **RESOLVED** | Updated `Challenge.lean` docstring to describe `T3cStmt` accurately as an arithmetic comparison of $n + 5$ against `hurwitzRadon n = 8*(n/4) + 2^(n % 4)`. |
| F7 | `FiniteCertificates.lean` docstring claimed "instant on all 6 kernels". | **RESOLVED** | Updated docstring with honest build-time note (~90–150s local build, deterministic replay on all 6 kernels). |
| F8 | Label drift (`T3a`–`T3e` in `HurwitzRupture.lean` vs. `T3a`–`T3d` in `Challenge.lean`). | **RESOLVED** | Aligned every theorem docstring in `HurwitzRupture.lean`, `TerraceLaw.lean`, `MirrorConservation.lean`, `FiniteCertificates.lean`, and `PathionRupture.lean` to canonical `T1a`–`T4f`. |

### Tooling Items (`T1`–`T2`) — All Resolved in `v2.0.0`

| ID | v1.0.0 Finding | Status | Exact Resolution in `v2.0.0` |
| --- | --- | --- | --- |
| Tooling 1 | CI negative test only checked a throwaway `/tmp` file, never exercising `comparator.json` or project files. | **RESOLVED** | Upgraded `.github/workflows/ci.yml` to clone `lean/` into `/tmp/neg_lean_test`, inject BOTH `sorry` AND an unpermitted custom axiom into `PalomarSolution.lean`, and assert that BOTH `lake comparator --config comparator.json --paranoid` and the axiom diff gate exit non-zero. |
| Tooling 2 | `scripts/check_citations.py` only checked HTTP 200 without title/author/year/retraction/citation checks. | **RESOLVED** | Rebuilt `scripts/check_citations.py` (see `M13` above); verified live `28/30` + `2` print-only classics + 100% bijective `\cite{}` coverage. |
