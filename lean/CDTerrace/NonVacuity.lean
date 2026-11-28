module
-- SPDX-License-Identifier: Apache-2.0
public import CDTerrace.Basic
public import CDTerrace.MirrorConservation
public import CDTerrace.TerraceLaw
public import CDTerrace.HurwitzRupture
public import CDTerrace.FiniteCertificates
public import CDTerrace.PathionRupture
public import CDTerrace.SpectralGaps
public import CDTerrace.OddBladeExclusion

/-!
# CDTerrace.NonVacuity — Explicit Non-Vacuity & Witness Instantiation Checks

Proves that every hypothesis and headline theorem in `CDTerrace` is non-vacuously inhabited
with concrete instantiated witnesses across $\mathrm{CD}_3$ (octonions), $\mathrm{CD}_4$
(sedenions), $\mathrm{CD}_5$ (pathions), and $\mathrm{CD}_6$ (chingons), eliminating any
possibility of vacuous quantification or inconsistent premises.
-/

namespace CDTerrace

public section

/-- Non-vacuity witness for Pillar 1 (`cdSignGamma_factorization`, `nilpotent_mirror_law`,
    `mirror_sum_conservation`, `midpoint_stratum_invariance`, `twoblade_left_annihilator_basis_exact`):
    In split sedenions $\mathrm{CD}_4$ with `flipMask = 8` (split signature $(-,-,-,+)$),
    `e_1 + e_9` has `1 ^^^ 9 = 8` so it is nilpotent, inverting $\nu_4^{\mathrm{std}}(1, 9) = 0$
    to $\nu_4^{\gamma}(1, 9) = 8$, while $H_4^{\gamma}(0) + H_4^{\gamma}(8) = 49 + 14 = 63$,
    $H_4^{\gamma}(4) = 42$, and in standard $\mathbb{S}_{16}$ the left-annihilator basis of
    $e_1 + e_{10}$ has exact cardinality `4`. -/
theorem nonvacuity_pillar1_split_sedenion :
    parityBits 4 ((1 ^^^ 9) &&& 8) = true ∧
    twobladeNullity 4 1 9 = 0 ∧
    twobladeNullityGamma 4 8 1 9 = 8 ∧
    nullityHistGamma 4 8 0 + nullityHistGamma 4 8 8 = 63 ∧
    nullityHistGamma 4 8 4 = 42 ∧
    (singularOrbitRepsGamma 4 0 1 10).length = 4 := by
  have h19 : twobladeNullity 4 1 9 = 0 := by
    rw [← nu4Closed_eq 1 9 (by omega) (by omega) (by omega)]; rfl
  refine ⟨by decide, h19, ?_, ?_, ?_, ?_⟩
  · have h := (nilpotent_mirror_law 4 8 1 9 (by omega) (by omega) (by omega) (by omega)).2 (by decide)
    omega
  · have h := mirror_sum_conservation 4 8 0 (by omega) (by omega)
    have hstd : nullityHist 4 0 + nullityHist 4 8 = 63 := by
      unfold nullityHist
      rw [cd4HistFast_eq, cd4HistFast_eq]; rfl
    rw [show (8 : Nat) = 2 ^ (4 - 1) - 0 from rfl]
    rw [show (8 : Nat) = 2 ^ (4 - 1) - 0 from rfl] at hstd
    exact h.trans hstd
  · rw [show (4 : Nat) = 2 ^ (4 - 2) from rfl]
    exact (universal_split_midpoint_42 4 8 (by omega)).trans rfl
  · have hlen := (twoblade_left_annihilator_basis_exact 4 0 1 10 (by omega) (by omega) (by omega)).1
    have h10 : twobladeNullityGamma 4 0 1 10 = 4 := by
      have hmir := (nilpotent_mirror_law 4 0 1 10 (by omega) (by omega) (by omega) (by omega)).1 (by decide)
      rw [hmir, ← nu4Closed_eq 1 10 (by omega) (by omega) (by omega)]; rfl
    exact hlen.trans h10

/-- Non-vacuity witness for Pillar 2 (`totalNullityMass_all_n`, `nonZDCount_all_n`,
    `terrace_top_bin_all_n`, `terrace_top_jump_all_n`, `terrace_midpoint_std_all_n`,
    `twoblade_strictly_below_bdi`, `twoblade_ceiling_attained`):
    Concrete instantiated numerical invariants for $n = 4, 5, 6$. -/
theorem nonvacuity_pillar2_terrace_instances :
    totalNullityMass 4 = 168 ∧
    totalNullityMass 5 = 2520 ∧
    totalNullityMass 6 = 26040 ∧
    nullityHist 4 0 = 63 ∧
    nullityHist 5 0 = 171 ∧
    nullityHist 6 0 = 435 ∧
    nullityHist 5 12 = 126 ∧
    nullityHist 6 28 = 342 ∧
    nullityHist 6 28 = nullityHist 6 4 + 3 * (32 - 2) ∧
    nullityHist 6 16 = 168 ∧
    twobladeMaxNullity 6 = 28 ∧
    bdiMaxAnnihilator 6 = 44 ∧
    twobladeMaxNullity 6 < bdiMaxAnnihilator 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · exact (totalNullityMass_all_n 4 (by omega)).trans rfl
  · exact (totalNullityMass_all_n 5 (by omega)).trans rfl
  · exact (totalNullityMass_all_n 6 (by omega)).trans rfl
  · exact (nonZDCount_all_n 4 (by omega)).trans rfl
  · exact (nonZDCount_all_n 5 (by omega)).trans rfl
  · exact (nonZDCount_all_n 6 (by omega)).trans rfl
  · rw [show (5 : Nat) = 4 + 1 from rfl, show (12 : Nat) = 2 ^ 4 - 4 from rfl]
    exact (terrace_top_bin_all_n 4 (by omega)).trans rfl
  · rw [show (6 : Nat) = 5 + 1 from rfl, show (28 : Nat) = 2 ^ 5 - 4 from rfl]
    exact (terrace_top_bin_all_n 5 (by omega)).trans rfl
  · rw [show (6 : Nat) = 5 + 1 from rfl, show (28 : Nat) = 2 ^ 5 - 4 from rfl,
        show (32 : Nat) = 2 ^ 5 from rfl]
    exact terrace_top_jump_all_n 5 (by omega)
  · rw [show (16 : Nat) = 2 ^ (6 - 2) from rfl]
    exact (terrace_midpoint_std_all_n 6 (by omega)).trans rfl
  · exact twoblade_strictly_below_bdi 6 (by omega)

/-- Non-vacuity witness for Pillar 3 (`cdMaxClique_valid`, `hurwitz_radon_rupture_all_ge6`,
    `asymmetric_doubling_tower_all_n`):
    At dimension 64 ($n = 6$), `cdMaxClique 6` has exact size `11` strictly below $\rho(64) = 12$,
    and the asymmetric doubling tower yields an exact `[32, 20, 64]` norm-multiplicative pair. -/
theorem nonvacuity_pillar3_dim64_rupture :
    isCompatClique 6 (cdMaxClique 6) ∧
    (cdMaxClique 6).length = 11 ∧
    hurwitzRadon 6 = 12 ∧
    (cdMaxClique 6).length < hurwitzRadon 6 ∧
    isNormMultPair 6 (List.range 32) (doubledRightWitness 6) ∧
    (doubledRightWitness 6).length = 20 := by
  have hcl := cdMaxClique_valid 6 (by omega)
  have hru := hurwitz_radon_rupture_all_ge6 6 (by omega)
  have has := asymmetric_doubling_tower_all_n 6 (by omega)
  exact ⟨hcl.1, hcl.2, rfl, by omega, has.1, has.2.2⟩

/-- Non-vacuity witness for Pillar 4 (`sedenion_42_fano_duality`, `sedenion_box_kites_7x6`,
    `pathion_14_and_chingon_16_witnesses`, `pathion_exact_ceiling_14_and_7_7_rigidity`,
    `cd6_split56_interior_spectral_gap`, `gaussInt_sq_eq_one_iff`):
    Concrete 10D sedenion witness, 14D $7 + 7$ pathion witness, 16D chingon witness,
    `CD_6(56)` interior spectral gap witness, and Gaussian integer rigidity on `i`. -/
theorem nonvacuity_pillar4_witnesses :
    popcount16 1023 = 10 ∧
    isNormMultMask 4 1023 = true ∧
    isNormMultList 5 pathionWitness14 = true ∧
    (pathionWitness14.filter (fun x => decide (x < 16))).length = 7 ∧
    (pathionWitness14.filter (fun x => decide (16 ≤ x))).length = 7 ∧
    isNormMultList 6 chingonWitness16 = true ∧
    nullityHistGamma 6 56 16 = 168 ∧
    nullityHistGamma 6 56 20 = 0 ∧
    nullityHistGamma 6 56 24 = 56 ∧
    GaussInt.mul ⟨0, 1⟩ ⟨0, 1⟩ ≠ GaussInt.one := by
  have hgap := cd6_split56_interior_spectral_gap
  refine ⟨rfl, ?_, pathion_14_and_chingon_16_witnesses.2.2.2.1, rfl, rfl,
          pathion_14_and_chingon_16_witnesses.2.2.2.2.2.2.2,
          hgap.2.2.2.2.1, hgap.2.2.2.2.2.1, hgap.2.2.2.2.2.2.1, ?_⟩
  · rw [show (1023 : Nat) = 255 + 256 * 3 from rfl, isNormMultMask4_eq_hiAvoidsBad 255 3 (by omega)]
    rfl
  · intro h; injection h with hre; cases hre

/-- Non-vacuity witness for Pillar 5 (`gray_code_bit_locking_all_n`,
    `exponential_spectral_band_gap_all_n`, `complete_spectral_gap_dichotomy_all_n`):
    In $\mathrm{CD}_7$ ($\dim = 128$) at `flipMask = 120 = 2^7 - 8`, `isGappedMask 7 120 = true`,
    exact count of gapped masks is `12 = 2^4 - 4`, and the three consecutive interior bins
    `36, 40, 44` are all empty (`0`) between populated edges $H_7^{120}(32) = 336$ and
    $H_7^{120}(48) > 0$. -/
theorem nonvacuity_pillar5_spectral_gaps :
    isGappedMask 7 120 = true ∧
    countPred (isGappedMask 7) (2 ^ 7) = 12 ∧
    nullityHistGamma 7 120 32 = 336 ∧
    nullityHistGamma 7 120 36 = 0 ∧
    nullityHistGamma 7 120 40 = 0 ∧
    nullityHistGamma 7 120 44 = 0 ∧
    0 < nullityHistGamma 7 120 48 := by
  have hbg := exponential_spectral_band_gap_all_n 7 (by omega)
  have hdi := complete_spectral_gap_dichotomy_all_n 7 (by omega)
  exact ⟨by decide, hdi.2, hbg.2.1,
         hbg.1 36 (by omega) (by omega),
         hbg.1 40 (by omega) (by omega),
         hbg.1 44 (by omega) (by omega),
         hbg.2.2⟩

/-- Non-vacuity witness for Pillar 6 (`twisted_frobenius_mod2_involution`,
    `odd_parity_zero_divisor_exclusion_all_n`, `odd_support_unit_blades_non_zd_all_n`):
    In standard sedenions $\mathrm{CD}_4$ (`flipMask = 0`), the signed unit 3-blade
    $x = e_1 + e_2 + e_{10}$ has odd coordinate sum (`3 % 2 = 1`) and trivial left and right
    annihilators across all of $\mathbb{Z}^{16}$. -/
theorem nonvacuity_pillar6_odd_blades :
    let x := signedBladeSum [1, 2, 10] (fun _ => 1)
    oddCoordSum 4 x ∧
    (∀ y, (∀ t, t < 16 → cdMulCoordGamma 4 0 x y t = 0) → ∀ t, t < 16 → y t = 0) ∧
    (∀ y, (∀ t, t < 16 → cdMulCoordGamma 4 0 y x t = 0) → ∀ t, t < 16 → y t = 0) := by
  have h := (odd_support_unit_blades_non_zd_all_n 4 0).1 [1, 2, 10] (fun _ => 1)
    (by decide)
    (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
    (by intro _ _; exact Or.inl rfl)
  exact h

end

end CDTerrace
