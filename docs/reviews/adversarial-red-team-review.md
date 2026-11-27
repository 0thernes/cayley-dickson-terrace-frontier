# Adversarial Red-Team Review (`docs/reviews/adversarial-red-team-review.md`)

An adversarial skeptic audit was performed against every theorem, proof architecture, computational engine, citation, CI gate, and epistemic boundary in `cayley-dickson-terrace-frontier` (`0TH-2026-019`, `v2.0.0`).

## Attack Vectors Tested & Dispositions

1. **Attack 1 — Does Lean actually prove the algebraic annihilator dimension $\dim \ker L_{e_i+e_j}$, or only a combinatorially defined block count?**
   - *v1.0.0 Finding:* `v1.0.0` defined `twobladeNullityGamma` via singular $2 \times 2$ block counts without formalizing algebra multiplication or linear maps.
   - *v2.0.0 Disposition:* **Formally Closed in Lean (`T1f`).** `Basic.lean` defines the exact bilinear coordinate product `cdMulCoordGamma` and left-multiplication map `leftMulTwoBladeCoord`, and `MirrorConservation.lean` proves `twoblade_left_annihilator_basis_exact`: an explicit $\mathbb{Z}$-basis isomorphism proving $\dim \ker L_{e_i+e_j} = \nu_n^\gamma(i, j)$ for all $n, \gamma, 1 \le i < j < 2^n$.
2. **Attack 2 — Does the Pathion upper bound $r_{\max}(\mathrm{CD}_5) = 14$ still depend on an unverified floating-point MILP solver (HiGHS)?**
   - *v1.0.0 Finding:* `v1.0.0` relied on SciPy/HiGHS MILP (`[EXACT-COMP]`) to claim $r_{\max}(\mathrm{CD}_5) = 14$.
   - *v2.0.0 Disposition:* **Formally Closed in Lean (`T4e`) & Independently Enumerated in Rust.** `PathionRupture.lean` exhausts all $2^{32} = 4{,}294{,}967{,}296$ subsets of $\mathrm{CD}_5$ and all duplicate-free lists (`isNormMultPair 5 S S`) inside the pure Lean kernel (zero `native_decide`, zero overrides, 6 independent kernels), proving $|S| \le 14$ and strict $7+7$ half-balance rigidity. Rust independently enumerates all `280` 14D subspaces and confirms 100% satisfy $|S_{\mathrm{lo}}|=|S_{\mathrm{hi}}|=7$ and $\{0, 16\} \subset S$. HiGHS MILP is retired from the proof trust base.
3. **Attack 3 — Is the dimension-64 interior spectral gap $H_6^{56}(20) = 0$ purely computational, or machine-checked?**
   - *v2.0.0 Disposition:* **Formally Closed in Lean (`T4f`).** `PathionRupture.lean` proves the complete 9-bin histogram `{0:257, 4:422, 8:364, 12:336, 16:168, 20:0, 24:56, 28:172, 32:178}` at $\mathrm{CD}_6(\mathrm{flip}=56)$ via balanced binary-tree kernel reduction (`cd6QuadTree56`) + algebraic mirror conservation, proving $H_6^{56}(20) = 0$ across all 6 kernels.
4. **Attack 4 — Does Theorem `T2b` prove uniqueness of equality with the BDI ceiling at $n=4$, and are all 7 statement-fidelity gaps closed?**
   - *Disposition:* **Formally Closed.** `T2bStmt` proves strict separation for all $n \ge 5$ AND `twobladeMaxNullity n = bdiMaxAnnihilator n ↔ n = 4` for all $n \ge 4$. All 7 statement-fidelity gaps (`T1c` cross term, `T1f` kernel basis, `T2b` uniqueness, `T3c` explicit scope, `T4a` $2+2$ bad-plane split, `T4b` non-circular disjointness, `T4d` unfactored $c^2=1$) are closed (`docs/statement-fidelity.md`).
5. **Attack 5 — Could `PalomarChallenge` `sorry`s leak, or is the CI negative axiom test merely a throwaway toy check?**
   - *v1.0.0 Finding:* `v1.0.0`'s CI negative test only printed axioms on a throwaway file rather than exercising the real comparator/axiom gate.
   - *v2.0.0 Disposition:* **Hardened.** `PalomarChallenge` remains excluded from `defaultTargets`, `VerifyAxioms.lean` audits all 35 declarations strictly within `[propext, Classical.choice, Quot.sound]`, AND `.github/workflows/ci.yml` executes a real tamper-injecting negative test that mutates a temporary copy of `PalomarSolution` / `VerifyAxioms` with a custom axiom and verifies that the actual CI comparator and axiom-diff gates reject it with non-zero exit code.
6. **Attack 6 — Could tests pass on buggy code (weak assertions or untested logic)?**
   - *Disposition:* **Tested via 8 Surgical Mutants.** `tests/test_all.py` runs an automated mutation-testing harness injecting 8 realistic bugs across sign cocycles, block determinants, nullity formulas, Hurwitz--Radon ceilings, sedenion/Pathion norm-multiplicativity checks, and timestamp manifests — verifying 8/8 mutants are killed.
7. **Attack 7 — Could any citation DOI/arXiv ID be misdirected, retracted, or uncited?**
   - *v1.0.0 Finding:* `v1.0.0` only checked HTTP 200 status and carried a misdirected 1922 Werke DOI on `hurwitz1898`.
   - *v2.0.0 Disposition:* **Fixed & Upgraded.** `scripts/check_citations.py --live` enforces title, primary author, year, retraction absence, and 100% bijective `\cite{}` coverage across all 30 BibTeX entries (`28/30` live verified, `2` print-only classics).
8. **Attack 8 — Could the C11 CLI silently skip signatures at $\mathrm{CD}_8$, or could timestamps / manifests be forged silently?**
   - *v1.0.0 Finding:* `v1.0.0`'s C11 CLI strided `gamma` by 4 at $\mathrm{CD}_8$.
   - *v2.0.0 Disposition:* **Fixed & Upgraded.** C11 `--verify-all` now audits all 496 algebras (`CD_4`–`CD_8`, zero stride) plus Pathion $r_{\max}=14$ and $\mathrm{CD}_6(56)$ spectral gap. `data/MANIFEST.sha256` carries dual independent cryptographic timestamps (DigiCert RFC 3161 `.tsr` + 3-calendar Bitcoin `.ots`), verified with an automated negative tamper test.
9. **Attack 9 — Could `grand_problems_retired`, `WebGL` labeling, or Mega-Atlas scope be overstated?**
   - *Disposition:* **Verified Honest.** Explicitly states `grand_problems_retired = 0`, labels the interactive observatory accurately as a **3D-projected HTML5 2D Canvas** (never WebGL), separates `[LEAN-6K]` from `[EXACT-COMP]` (`CD_7`–`CD_8` split phases) and `[OPEN]` (`ALG-035`, `ALG-039`, `COMB-040`), and sets `visual: true, ui: true, deployed: true` honestly in `repo.yaml`.
