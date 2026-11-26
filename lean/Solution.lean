module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import Challenge
public import CDTerrace

/-!
# Complete Zero-`sorry` Solution (`Solution.lean`)

Discharges all 19 headline statements (`T1a`–`T4d`) and their master conjunction
`prove_all_terrace_theorems` from `CDTerrace`, using strictly standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Solution

open Challenge
open CDTerrace

@[expose] public section

theorem prove_t1a : T1aStmt := cdSignGamma_factorization
theorem prove_t1b : T1bStmt := blockDeltaGamma_eq
theorem prove_t1c : T1cStmt := twoblade_nilpotent_iff
theorem prove_t1d : T1dStmt := nilpotent_mirror_law
theorem prove_t1e : T1eStmt := ⟨mirror_sum_conservation, midpoint_stratum_invariance⟩

theorem prove_t2a : T2aStmt :=
  ⟨nullity_doubling_lower, nullity_doubling_upper, nullity_doubling_axis, nullity_doubling_cross⟩
theorem prove_t2b : T2bStmt := ⟨nullity_mod4_and_bound, twoblade_strictly_below_bdi⟩
theorem prove_t2c : T2cStmt := ⟨totalNullityMass_all_n, nonZDCount_all_n⟩
theorem prove_t2d : T2dStmt :=
  ⟨terrace_interleave_even, terrace_interleave_odd, terrace_palindrome_all_n⟩
theorem prove_t2e : T2eStmt := ⟨terrace_top_bin_all_n, terrace_top_jump_all_n⟩
theorem prove_t2f : T2fStmt := ⟨terrace_midpoint_std_all_n, universal_split_midpoint_42⟩

theorem prove_t3a : T3aStmt :=
  ⟨rightCompat_doubling_lower, rightCompat_doubling_upper,
   rightCompat_doubling_cross, universal_right_multipliers_all_n⟩
theorem prove_t3b : T3bStmt := ⟨compat_clique_le_all_n, cdMaxClique_valid⟩
theorem prove_t3c : T3cStmt := ⟨hurwitz_radon_saturation_345, hurwitz_radon_rupture_all_ge6⟩
theorem prove_t3d : T3dStmt := ⟨compatClique_implies_full_normMult, asymmetric_doubling_tower_all_n⟩

theorem prove_t4a : T4aStmt := ⟨sedenion_42_fano_duality, sedenion_no_11d_coord_subspace⟩
theorem prove_t4b : T4bStmt := sedenion_box_kites_7x6
theorem prove_t4c : T4cStmt := ⟨split_sedenion_4_phases, split_pathion_8_phases⟩
theorem prove_t4d : T4dStmt :=
  ⟨pathion_14_and_chingon_16_witnesses,
   fun zero one negOne mul sub hfac hdom hsub => pure_intercalate_field_rigidity zero one negOne mul sub hfac hdom hsub,
   int_sq_eq_one_iff,
   gaussInt_sq_eq_one_iff⟩

theorem prove_all_terrace_theorems : AllTerraceTheoremsStmt :=
  ⟨prove_t1a, prove_t1b, prove_t1c, prove_t1d, prove_t1e,
   prove_t2a, prove_t2b, prove_t2c, prove_t2d, prove_t2e, prove_t2f,
   prove_t3a, prove_t3b, prove_t3c, prove_t3d,
   prove_t4a, prove_t4b, prove_t4c, prove_t4d⟩

end
end Solution
