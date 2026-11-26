# Adversarial Red-Team Review (`docs/reviews/adversarial-red-team-review.md`)

An adversarial skeptic audit was performed against every theorem, computational claim, script, and epistemic boundary in `cayley-dickson-terrace-frontier` (`0TH-2026-017`).

## Attack Vectors Tested & Dispositions

1. **Attack 1 — Does Theorem `T2b` overstate or understate BDI separation?**
   - *Finding:* Initial draft checked `6 <= n`, missing that $n = 5$ already separates strictly (`12 < 16`).
   - *Disposition:* **Fixed & Formalized.** Upgraded `twoblade_strictly_below_bdi` to `5 <= n`, added `refute_twoblade_reaches_bdi_at_64` asserting `twobladeMaxNullity 4 = bdiMaxAnnihilator 4 ∧ twobladeMaxNullity 5 < bdiMaxAnnihilator 5 ∧ twobladeMaxNullity 6 < bdiMaxAnnihilator 6`, and locked in `tests/test_all.py`.
2. **Attack 2 — Could `sedenion_42_fano_duality` hide a bug in its fast branch-and-bound counter?**
   - *Finding:* `cd4Count10Fast` uses `forbMask4Direct` and pruned `countIndepHi` rather than brute-forcing all $2^{16}$ masks inside `decide`.
   - *Disposition:* **Formally Closed in Kernel.** `FiniteCertificates.lean` proves exact algebraic equivalence `forbMask4Direct_eq_forbMask4`, `isNormMultMask4_eq_hiAvoidsBad`, `hiAvoidsBad_eq_isIndepForb`, `countIndepHi_sound`, and `countPred_256x256` directly against the unoptimized textbook `isNormMultMask 4 m` predicate over all `65536` masks, discharging the theorem statement on the raw textbook definition with zero trusted shortcuts.
3. **Attack 3 — Could `PalomarChallenge` `sorry`s leak into `defaultTargets` or `VerifyAxioms.lean`?**
   - *Disposition:* **Verified Safe.** `PalomarChallenge` is excluded from `defaultTargets` in `lean/lakefile.toml`; `VerifyAxioms.lean` imports `PalomarSolution` (never `PalomarChallenge`) and prints all 30 declarations strictly within `[propext, Classical.choice, Quot.sound]`; CI includes a live negative test proving an injected custom axiom is caught.
4. **Attack 4 — Are any `[EXACT-COMP]` claims falsely labeled `[LEAN-6K]`?**
   - *Disposition:* **Verified Clean.** Both `C1` ($\mathrm{CD}_6$–$\mathrm{CD}_8$ split phases) and `C2` (Pathion MILP exact upper bound $r_{\max}(\mathrm{CD}_5) = 14 < 16$) are explicitly tagged `[EXACT-COMP]` everywhere in `paper/main.tex`, `CLAIMS.md`, `LIMITATIONS.md`, and `README.md`, and Open Problem 8.2 explicitly lists lifting the MILP upper bound into Lean as open.
5. **Attack 5 — Could any citation DOI/arXiv ID be fabricated or point to the wrong paper?**
   - *Finding:* Live Crossref verification caught that `10.7151/dmgaa.1087` pointed to a different article in the same 2004 issue rather than Cawagas's sedenion paper (`10.7151/dmgaa.1088`).
   - *Disposition:* **Fixed & Re-verified.** Corrected to `10.7151/dmgaa.1088` and confirmed 24/24 BibTeX entries return HTTP 200 OK with exact title match on Crossref/arXiv.
6. **Attack 6 — Could `grand_problems_retired` or Mega-Atlas scope be overstated?**
   - *Disposition:* **Verified Honest.** Explicitly states `grand_problems_retired = 0` and separates coordinate-subspace / 2-blade theorems from open problems `ALG-035`, `ALG-039`, and `COMB-040`.
