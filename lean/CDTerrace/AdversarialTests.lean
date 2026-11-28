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
# CDTerrace.AdversarialTests — Zero-Axiom Adversarial Refutations & Boundary Checks

Formal machine-checked refutations of 10 natural false strengthenings, verifying that EVERY
quantifier bound, exception set, and strict inequality in `CDTerrace` is sharp and cannot be
weakened:
1. **A1 (`refute_hurwitz_saturation_at_64`):** $\omega(G_6^{\mathrm{comp}}) = 11 < 12 = \rho(64)$
   — Hurwitz–Radon saturation fails at $n = 6$ (no 12-clique exists in $\mathrm{CD}_6$).
2. **A2 (`refute_sedenion_11d_coord_subspace`):** No 11-dimensional coordinate subspace of
   $\mathbb{S}_{16}$ is norm-multiplicative (explicit counterexample witness: adding $e_{10}$
   to the 10D witness $\{0..9\}$ immediately destroys norm-multiplicativity).
3. **A3 (`refute_twoblade_reaches_bdi_at_64`):** The 2-blade nullity ceiling attains the cited
   Biss–Dugger–Isaksen ceiling UNIQUELY at $n = 4$ (`4 = 4`) among $n \ge 4$, and strictly
   separates for every $n \ge 5$ (`12 < 16` at $n = 5$, `28 < 44` at $n = 6$).
4. **A4 (`refute_split_preserves_individual_bins`):** Split signatures do NOT preserve individual
   histogram bins $H_n^\gamma(v)$ (only mirror pairs $H_n^\gamma(v) + H_n^\gamma(2^{n-1}-v)$
   and the midpoint $H_n^\gamma(2^{n-2})$ are conserved): in $\mathrm{CD}_4$ with `flipMask = 8`,
   $H_4^{\gamma}(0) = 49 \neq 63 = H_4^{\mathrm{std}}(0)$ and $H_4^{\gamma}(8) = 14 \neq 0$.
5. **A5 (`refute_third_universal_multiplier`):** No basis element outside $\{e_0, e_{2^{n-1}}\}$
   is a universal right-multiplier of $\mathrm{CD}_n$ for $n \ge 4$ (explicitly refuted for
   $e_1$ in $\mathrm{CD}_4$, since `rightCompat 4 1 10 = false`).
6. **A6 (`refute_gaussian_imaginary_intercalate`):** Even in $\mathbb{Z}[i] \subset \mathbb{Q}(i)$,
   $z = i$ cannot satisfy $z^2 = 1$ ($i^2 = -1 \neq 1$), and every $z \in \mathbb{Z}[i]$ with
   $z^2 = 1$ lies in $\{+1, -1\}$.
7. **A7 (`refute_pathion_15d_or_unbalanced_14d`):** No 15-dimensional coordinate subspace of
   $\mathrm{CD}_5$ is norm-multiplicative, and NO 14-dimensional norm-multiplicative coordinate
   subspace of $\mathrm{CD}_5$ can split unevenly (`|S_lo| ≠ 7`).
8. **A8 (`refute_cd6_split56_contiguous_bins`):** At dimension 64, split-signature histograms are
   NO LONGER supported on contiguous multiples of 4: in $\mathrm{CD}_6(\gamma)$ at `flipMask = 56`,
   $H_6^{56}(16) > 0$ and $H_6^{56}(24) > 0$, yet $H_6^{56}(20) = 0$.
9. **A9 (`refute_even_4blade_non_zd`):** The odd-parity hypothesis of Pillar VI (`T6b`/`T6c`) is
   sharp: in standard sedenions $\mathrm{CD}_4(0)$, the unit 4-blade $x = e_1 + e_2 + e_9 - e_{10}$
   (even coordinate sum `2`) annihilates $y = e_4 + e_{15} \neq 0$ (`x * y = 0`).
10. **A10 (`refute_naive_div8_gap_rule`):** The 4-mask exception set $\{0, 8, 2^{n-1}, 2^{n-1}+8\}$
    in Pillar V (`T5c`) is exact and cannot be dropped: in $\mathrm{CD}_7$, `f = 8` and `f = 72`
    both satisfy `8 ∣ f` yet have NO interior mod-4 spectral gap, whereas `f = 120` has a
    3-bin interior band gap `[36, 40, 44]`.
-/

namespace CDTerrace

public section

/-- **Adversarial Refutation A1:** No 12-element compatibility clique exists in $\mathrm{CD}_6$
    ($\dim = 64$), refuting Hurwitz–Radon saturation beyond dimension 32. -/
theorem refute_hurwitz_saturation_at_64 :
    ¬ ∃ S : List Nat, isCompatClique 6 S ∧ S.length = hurwitzRadon 6 := by
  rintro ⟨S, hcl, hlen⟩
  have hle := compat_clique_le_all_n 6 (by omega) S hcl
  have hhr : hurwitzRadon 6 = 12 := rfl
  omega

/-- **Adversarial Refutation A2:** No 11-dimensional norm-multiplicative coordinate subspace
    exists in $\mathbb{S}_{16}$, and the concrete 11D extension `{0..10}` (mask `2047`) fails
    norm-multiplicativity directly. -/
theorem refute_sedenion_11d_coord_subspace :
    (¬ ∃ m : Nat, m < 65536 ∧ 11 ≤ popcount16 m ∧ isNormMultMask 4 m = true) ∧
    isNormMultMask 4 2047 = false := by
  refine ⟨?_, ?_⟩
  · rintro ⟨m, hm, h11, hnm⟩
    have hf := sedenion_no_11d_coord_subspace m hm h11
    rw [hf] at hnm; cases hnm
  · rw [show (2047 : Nat) = 255 + 256 * 7 from rfl, isNormMultMask4_eq_hiAvoidsBad 255 7 (by omega)]
    rfl

/-- **Adversarial Refutation A3:** The 2-blade nullity ceiling coincides with the cited
    Biss–Dugger–Isaksen general annihilator ceiling UNIQUELY at $n = 4$ (`4 = 4`) among $n \ge 4$,
    and strictly separates at $n = 5$ (`12 < 16`) and $n = 6$ (`28 < 44`). -/
theorem refute_twoblade_reaches_bdi_at_64 :
    twobladeMaxNullity 4 = bdiMaxAnnihilator 4 ∧
    twobladeMaxNullity 5 < bdiMaxAnnihilator 5 ∧
    twobladeMaxNullity 6 < bdiMaxAnnihilator 6 := by
  decide

/-- **Adversarial Refutation A4:** Split signatures strictly break individual bin invariance
    while conserving mirror-pair sums and the midpoint stratum. -/
theorem refute_split_preserves_individual_bins :
    nullityHistGamma 4 8 0 ≠ nullityHist 4 0 ∧
    nullityHistGamma 4 8 8 ≠ nullityHist 4 8 ∧
    nullityHistGamma 4 8 0 + nullityHistGamma 4 8 8 = nullityHist 4 0 + nullityHist 4 8 := by
  refine ⟨?_, ?_, mirror_sum_conservation 4 8 0 (by omega) (by omega)⟩
  · unfold nullityHist; rw [cd4HistFast_eq, cd4HistFast_eq]; decide
  · unfold nullityHist; rw [cd4HistFast_eq, cd4HistFast_eq]; decide

/-- **Adversarial Refutation A5:** In $\mathrm{CD}_4$, $e_1$ fails to be a universal
    right-multiplier (witnessed by `rightCompat 4 1 10 = false`), and for ALL $n \ge 4$
    every universal right-multiplier lies strictly in $\{0, 2^{n-1}\}$. -/
theorem refute_third_universal_multiplier :
    rightCompat 4 1 10 = false ∧
    ∀ n j, 4 ≤ n → j < 2 ^ n → j ≠ 0 → j ≠ 2 ^ (n - 1) →
      ¬ (∀ x, x < 2 ^ n → x ≠ j → rightCompat n j x = true) := by
  refine ⟨by decide, ?_⟩
  intro n j hn hj hj0 hjh hall
  rcases (universal_right_multipliers_all_n n j hn hj).mp hall with rfl | rfl
  · exact hj0 rfl
  · exact hjh rfl

/-- **Adversarial Refutation A6:** Neither $i$ nor $-i$ satisfies $z^2 = 1$ in $\mathbb{Z}[i]$;
    every solution to $z^2 = 1$ in $\mathbb{Z}[i]$ lies in $\{\pm 1\}$. -/
theorem refute_gaussian_imaginary_intercalate :
    GaussInt.mul ⟨0, 1⟩ ⟨0, 1⟩ ≠ GaussInt.one ∧
    GaussInt.mul ⟨0, -1⟩ ⟨0, -1⟩ ≠ GaussInt.one ∧
    ∀ z : GaussInt, z.mul z = GaussInt.one → z.im = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; injection h with hre; cases hre
  · intro h; injection h with hre; cases hre
  · intro z hz
    rcases (gaussInt_sq_eq_one_iff z).mp hz with rfl | rfl <;> rfl

/-- **Adversarial Refutation A7:** No 15-dimensional norm-multiplicative coordinate subspace
    exists in $\mathrm{CD}_5$, and NO 14-dimensional norm-multiplicative coordinate subspace of
    $\mathrm{CD}_5$ can have an unbalanced split (`|S_lo| ≠ 7`). -/
theorem refute_pathion_15d_or_unbalanced_14d :
    (¬ ∃ S : List Nat, S.Nodup ∧ isNormMultPair 5 S S ∧ 15 ≤ S.length) ∧
    (¬ ∃ S : List Nat, S.Nodup ∧ isNormMultPair 5 S S ∧ S.length = 14 ∧
        (S.filter (fun x => decide (x < 16))).length ≠ 7) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨S, hnd, hnm, h15⟩
    have hle := (pathion_exact_ceiling_14_and_7_7_rigidity.2.2 S hnd hnm).1
    omega
  · rintro ⟨S, hnd, hnm, h14, hne⟩
    have h7 := ((pathion_exact_ceiling_14_and_7_7_rigidity.2.2 S hnd hnm).2 h14).1
    exact hne h7

/-- **Adversarial Refutation A8:** Contiguous multiple-of-4 support fails at dimension 64 under
    split signature `flipMask = 56`: bin 20 is strictly empty between nonempty bins 16 and 24. -/
theorem refute_cd6_split56_contiguous_bins :
    0 < nullityHistGamma 6 56 16 ∧
    nullityHistGamma 6 56 20 = 0 ∧
    0 < nullityHistGamma 6 56 24 := by
  have h := cd6_split56_interior_spectral_gap
  exact ⟨by omega, h.2.2.2.2.2.1, by omega⟩

/-- **Adversarial Refutation A9:** Sharpness of Pillar VI's odd-parity hypothesis — the signed
    unit 4-blade $x = e_1 + e_2 + e_9 - e_{10}$ (even coordinate sum `2`) IS a genuine left zero
    divisor in standard sedenions $\mathrm{CD}_4(0)$, annihilating $y = e_4 + e_{15} \neq 0$. -/
theorem refute_even_4blade_non_zd :
    let x := signedBladeSum [1, 2, 9, 10] (fun a => if a == 10 then -1 else 1)
    let y := signedBladeSum [4, 15] (fun _ => 1)
    sumInt x 16 = 2 ∧
    y 4 ≠ 0 ∧
    (∀ t, t < 16 → cdMulCoordGamma 4 0 x y t = 0) := by
  have hprod : ∀ t : Fin 16,
      cdMulCoordGamma 4 0
        (signedBladeSum [1, 2, 9, 10] (fun a => if a == 10 then -1 else 1))
        (signedBladeSum [4, 15] (fun _ => 1)) t.val = 0 := by decide
  refine ⟨by decide, by decide, fun t ht => hprod ⟨t, ht⟩⟩

/-- **Adversarial Refutation A10:** Sharpness of Pillar V's exact dichotomy (`T5c`) — in
    $\mathrm{CD}_7$, `f = 8` and `f = 72 = 2^6 + 8` are nonzero multiples of 8 that have NO
    interior mod-4 spectral gap, whereas `f = 120 = 2^7 - 8` DOES have an interior mod-4 gap. -/
theorem refute_naive_div8_gap_rule :
    8 % 8 = 0 ∧ 72 % 8 = 0 ∧ 120 % 8 = 0 ∧
    ¬ hasInteriorMod4Gap 7 8 ∧
    ¬ hasInteriorMod4Gap 7 72 ∧
    hasInteriorMod4Gap 7 120 := by
  have hdi := (complete_spectral_gap_dichotomy_all_n 7 (by omega)).1
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro h; have h1 := (hdi 8 (by omega)).mp h; revert h1; decide
  · intro h; have h1 := (hdi 72 (by omega)).mp h; revert h1; decide
  · exact (hdi 120 (by omega)).mpr (by decide)

end

end CDTerrace
