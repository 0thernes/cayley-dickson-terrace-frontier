module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

import PalomarSolution
import CDTerrace.NonVacuity
import CDTerrace.AdversarialTests

/-!
# Strict Kernel Axiom Audit (`VerifyAxioms.lean`)

Prints exact transitive axiom footprints for all 29 Palomar headline targets
(`T1a`–`T6c` + `ALL`), all 6 pillar non-vacuity witnesses, and all 10 adversarial
boundary refutations (45 declarations total). Every single declaration must depend
ONLY on a subset of `{propext, Classical.choice, Quot.sound}` (zero `sorryAx`, zero
`Lean.ofReduceBool`, zero custom axioms).
-/

#print axioms CDTerrace.Palomar.prove_t1a
#print axioms CDTerrace.Palomar.prove_t1b
#print axioms CDTerrace.Palomar.prove_t1c
#print axioms CDTerrace.Palomar.prove_t1d
#print axioms CDTerrace.Palomar.prove_t1e
#print axioms CDTerrace.Palomar.prove_t1f
#print axioms CDTerrace.Palomar.prove_t2a
#print axioms CDTerrace.Palomar.prove_t2b
#print axioms CDTerrace.Palomar.prove_t2c
#print axioms CDTerrace.Palomar.prove_t2d
#print axioms CDTerrace.Palomar.prove_t2e
#print axioms CDTerrace.Palomar.prove_t2f
#print axioms CDTerrace.Palomar.prove_t3a
#print axioms CDTerrace.Palomar.prove_t3b
#print axioms CDTerrace.Palomar.prove_t3c
#print axioms CDTerrace.Palomar.prove_t3d
#print axioms CDTerrace.Palomar.prove_t4a
#print axioms CDTerrace.Palomar.prove_t4b
#print axioms CDTerrace.Palomar.prove_t4c
#print axioms CDTerrace.Palomar.prove_t4d
#print axioms CDTerrace.Palomar.prove_t4e
#print axioms CDTerrace.Palomar.prove_t4f
#print axioms CDTerrace.Palomar.prove_t5a
#print axioms CDTerrace.Palomar.prove_t5b
#print axioms CDTerrace.Palomar.prove_t5c
#print axioms CDTerrace.Palomar.prove_t6a
#print axioms CDTerrace.Palomar.prove_t6b
#print axioms CDTerrace.Palomar.prove_t6c
#print axioms CDTerrace.Palomar.prove_all_terrace_theorems

#print axioms CDTerrace.nonvacuity_pillar1_split_sedenion
#print axioms CDTerrace.nonvacuity_pillar2_terrace_instances
#print axioms CDTerrace.nonvacuity_pillar3_dim64_rupture
#print axioms CDTerrace.nonvacuity_pillar4_witnesses
#print axioms CDTerrace.nonvacuity_pillar5_spectral_gaps
#print axioms CDTerrace.nonvacuity_pillar6_odd_blades

#print axioms CDTerrace.refute_hurwitz_saturation_at_64
#print axioms CDTerrace.refute_sedenion_11d_coord_subspace
#print axioms CDTerrace.refute_twoblade_reaches_bdi_at_64
#print axioms CDTerrace.refute_split_preserves_individual_bins
#print axioms CDTerrace.refute_third_universal_multiplier
#print axioms CDTerrace.refute_gaussian_imaginary_intercalate
#print axioms CDTerrace.refute_pathion_15d_or_unbalanced_14d
#print axioms CDTerrace.refute_cd6_split56_contiguous_bins
#print axioms CDTerrace.refute_even_4blade_non_zd
#print axioms CDTerrace.refute_naive_div8_gap_rule
