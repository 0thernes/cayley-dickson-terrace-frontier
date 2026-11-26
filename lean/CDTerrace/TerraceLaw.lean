module
-- SPDX-License-Identifier: Apache-2.0
public import CDTerrace.Basic
public import CDTerrace.MirrorConservation

/-!
# CDTerrace.TerraceLaw — Universal All-$n$ Dyadic-Palindromic Terrace Law

Proves universally for every $n \ge 3$ in zero-Mathlib, strictly constructive Lean 4.35.0:
- **T2a (`blockDelta_doubling_*`):** All 6 exact pointwise block-sign doubling identities.
- **T2b (`nullity_doubling_*`):** Exact 4-case 2-blade nullity doubling recurrence:
  $\nu_{n+1}(i, j) = 2\nu_n(i, j)$, $\nu_{n+1}(i+h, j+h) = 2\nu_n(i, j)$, axis-pinned $= 0$,
  and cross-half $\nu_{n+1}(i, b+h) = 2^n - 4 - 2\nu_n(i, b)$.
- **T2c (`nullity_mod4_and_bound`, `twoblade_strictly_below_bdi`):**
  $4 \mid \nu_n(i, j)$, $\nu_n(i, j) \le 2^{n-1} - 4$, and strict separation
  $2^{n-1} - 4 < 2^n - 4n + 4$ for all $n \ge 6$.
- **T2d (`totalNullityMass_all_n`):** Exact $+4M_n - 4M_n$ cancellation proving
  $M_n = 8(2^{n-1}-1)(2^{n-2}-1)(2^{n-3}-1)$ for all $n \ge 3$.
- **T2e (`nonZDCount_all_n`):** $H_n^{\mathrm{std}}(0) = (6n - 9)2^{n-2} + 3$ for all $n \ge 3$.
- **T2f (`terrace_interleave_even`, `terrace_interleave_odd`, `terrace_palindrome_all_n`,
  `terrace_top_bin_all_n`, `terrace_top_jump_all_n`, `universal_split_midpoint_42`):**
  Complete fractal interleaved dyadic-palindromic terrace law and universal split-signature
  midpoint law $H_n^\gamma(2^{n-2}) = 42 \cdot 2^{n-4}$ for ALL $n \ge 4$ and ALL $\gamma \in \{\pm 1\}^n$.
-/

namespace CDTerrace

public section

/-! ### Clean One-Step Unfolding Lemmas for `cdSign (n + 1)` & Powers of 2 -/

theorem two_pow_mul_split (n k : Nat) (h : k ≤ n) :
    2 ^ n = 2 ^ k * 2 ^ (n - k) := by
  have hadd : k + (n - k) = n := by omega
  rw [← Nat.pow_add, hadd]

theorem cdSign_succ_ll (n i j : Nat) (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    cdSign (n + 1) i j = cdSign n i j := by
  show (if i < 2 ^ n then if j < 2 ^ n then cdSign n i j else cdSign n (j - 2 ^ n) i
        else if j < 2 ^ n then if j == 0 then cdSign n (i - 2 ^ n) 0 else -(cdSign n (i - 2 ^ n) j)
        else if j - 2 ^ n == 0 then -(cdSign n 0 (i - 2 ^ n)) else cdSign n (j - 2 ^ n) (i - 2 ^ n)) = _
  simp only [hi, hj, ↓reduceIte]

theorem cdSign_succ_lh (n i b : Nat) (hi : i < 2 ^ n) :
    cdSign (n + 1) i (b + 2 ^ n) = cdSign n b i := by
  have hge : ¬(b + 2 ^ n < 2 ^ n) := by omega
  have hsub : b + 2 ^ n - 2 ^ n = b := by omega
  show (if i < 2 ^ n then if b + 2 ^ n < 2 ^ n then cdSign n i (b + 2 ^ n) else cdSign n (b + 2 ^ n - 2 ^ n) i
        else _) = _
  simp only [hi, hge, hsub, ↓reduceIte]

theorem cdSign_succ_hl (n a j : Nat) (hj : j < 2 ^ n) :
    cdSign (n + 1) (a + 2 ^ n) j = if j = 0 then cdSign n a 0 else -(cdSign n a j) := by
  have hge : ¬(a + 2 ^ n < 2 ^ n) := by omega
  have hsub : a + 2 ^ n - 2 ^ n = a := by omega
  show (if a + 2 ^ n < 2 ^ n then _
        else if j < 2 ^ n then if j == 0 then cdSign n (a + 2 ^ n - 2 ^ n) 0 else -(cdSign n (a + 2 ^ n - 2 ^ n) j)
        else _) = _
  simp only [hge, hj, hsub, beq_iff_eq, ↓reduceIte]

theorem cdSign_succ_hh (n a b : Nat) :
    cdSign (n + 1) (a + 2 ^ n) (b + 2 ^ n) = if b = 0 then -(cdSign n 0 a) else cdSign n b a := by
  have hge1 : ¬(a + 2 ^ n < 2 ^ n) := by omega
  have hge2 : ¬(b + 2 ^ n < 2 ^ n) := by omega
  have hs1 : a + 2 ^ n - 2 ^ n = a := by omega
  have hs2 : b + 2 ^ n - 2 ^ n = b := by omega
  show (if a + 2 ^ n < 2 ^ n then _
        else if b + 2 ^ n < 2 ^ n then _
        else if b + 2 ^ n - 2 ^ n == 0 then -(cdSign n 0 (a + 2 ^ n - 2 ^ n))
             else cdSign n (b + 2 ^ n - 2 ^ n) (a + 2 ^ n - 2 ^ n)) = _
  simp only [hge1, hge2, hs1, hs2, beq_iff_eq, ↓reduceIte]

theorem cdSign_right_alt_basis (n i k : Nat) (hi0 : 0 < i) (hi : i < 2 ^ n) (hk : k < 2 ^ n) :
    cdSign n k i * cdSign n (i ^^^ k) i = -1 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [Nat.xor_zero, cdSign_zero_left n i hi, cdSign_diag n i hi0 hi]; rfl
  · by_cases hki : k = i
    · subst hki
      rw [Nat.xor_self, cdSign_diag n k hi0 hi, cdSign_zero_left n k hi]; rfl
    · have hxne0 : i ^^^ k ≠ 0 := fun hz => hki (Eq.symm (eq_of_xor_eq_zero hz))
      have hxne : i ^^^ k ≠ i := by
        intro heq
        have : (i ^^^ k) ^^^ i = 0 := by rw [heq, Nat.xor_self]
        rw [Nat.xor_comm i k, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
        exact hk0 this
      have hxlt : i ^^^ k < 2 ^ n := Nat.xor_lt_two_pow hi hk
      rw [cdSign_anticomm n k i (by omega) hi0 hk hi hki,
          cdSign_anticomm n (i ^^^ k) i (by omega) hi0 hxlt hi hxne,
          Int.neg_mul_neg]
      exact cdSign_left_alt_basis n i k hi0 hi hk

theorem blockDelta_symm_ij (n i j k : Nat) :
    blockDelta n i j k = blockDelta n j i k := by
  unfold blockDelta; dsimp only
  rw [Nat.xor_comm i j]
  ac_rfl

theorem twobladeNullity_symm (n i j : Nat) :
    twobladeNullity n i j = twobladeNullity n j i := by
  unfold twobladeNullity
  congr 1
  rw [countSingularIdx_eq_countPred, countSingularIdx_eq_countPred]
  apply countPred_ext
  intro k _
  simp [blockDelta_symm_ij]

/-! ### Nonsingularity of the 4 Special Indices $\{0, i, j, i \oplus j\}$ -/

theorem blockDelta_special_nonsing (n i j k : Nat)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j)
    (hk : k = 0 ∨ k = i ∨ k = j ∨ k = i ^^^ j) :
    blockDelta n i j k = -1 := by
  have h0 : blockDelta n i j 0 = -1 := by
    unfold blockDelta; dsimp only
    rw [Nat.zero_xor, cdSign_zero_right n i hi, cdSign_zero_right n j hj,
        Int.one_mul, Int.mul_one]
    have hd0 : i ^^^ j ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
    have hdlt : i ^^^ j < 2 ^ n := Nat.xor_lt_two_pow hi hj
    have hdi : i ≠ i ^^^ j := by
      intro heq
      have : i ^^^ i = (i ^^^ j) ^^^ i := congrArg (· ^^^ i) heq
      rw [Nat.xor_self, Nat.xor_comm i j, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
      omega
    have hdj : j ≠ i ^^^ j := by
      intro heq
      have : j ^^^ j = (i ^^^ j) ^^^ j := congrArg (· ^^^ j) heq
      rw [Nat.xor_self, xor_sub_self_cancel] at this
      omega
    rw [cdSign_anticomm n i (i ^^^ j) hi0 (by omega) hi hdlt hdi,
        cdSign_anticomm n j (i ^^^ j) hj0 (by omega) hj hdlt hdj,
        Int.neg_mul_neg]
    have hxj : (i ^^^ j) ^^^ i = j := by rw [Nat.xor_comm i j, xor_sub_self_cancel]
    have := cdSign_left_alt_basis n (i ^^^ j) i (by omega) hdlt hi
    rw [hxj] at this
    exact this
  have hi_case : blockDelta n i j i = -1 := by
    unfold blockDelta; dsimp only
    have hx : i ^^^ (i ^^^ j) = j := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [hx, cdSign_diag n i hi0 hi, cdSign_diag n j hj0 hj,
        cdSign_anticomm n j i hj0 hi0 hj hi (Ne.symm hne)]
    rcases cdSign_val_pm1 n i j with h | h <;> simp [h]
  rcases hk with hk0 | hki | hkj | hkd
  · rw [hk0]; exact h0
  · rw [hki]; exact hi_case
  · rw [hkj]
    have := blockDelta_pair_symm n i j i
    have hx : i ^^^ (i ^^^ j) = j := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [hx] at this
    rw [this, hi_case]
  · rw [hkd]
    have := blockDelta_pair_symm n i j 0
    rw [Nat.zero_xor] at this
    rw [this, h0]

/-! ### Theorem T2a: The Six Pointwise Block-Sign Doubling Identities -/

theorem blockDelta_doubling_lower_lo (n i j k : Nat)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hk : k < 2 ^ n) :
    blockDelta (n + 1) i j k = blockDelta n i j k := by
  unfold blockDelta; dsimp only
  have hkp : k ^^^ (i ^^^ j) < 2 ^ n := Nat.xor_lt_two_pow hk (Nat.xor_lt_two_pow hi hj)
  rw [cdSign_succ_ll n i k hi hk, cdSign_succ_ll n i _ hi hkp,
      cdSign_succ_ll n j k hj hk, cdSign_succ_ll n j _ hj hkp]

theorem blockDelta_doubling_lower_hi (n i j k : Nat)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j)
    (hk : k < 2 ^ n) :
    blockDelta (n + 1) i j (k + 2 ^ n) = blockDelta n i j k := by
  unfold blockDelta; dsimp only
  have hd : i ^^^ j < 2 ^ n := Nat.xor_lt_two_pow hi hj
  have hkp_eq : (k + 2 ^ n) ^^^ (i ^^^ j) = (k ^^^ (i ^^^ j)) + 2 ^ n := xor_add_left hk hd
  have hkp_lt : k ^^^ (i ^^^ j) < 2 ^ n := Nat.xor_lt_two_pow hk hd
  rw [hkp_eq, cdSign_succ_lh n i k hi, cdSign_succ_lh n i _ hi,
      cdSign_succ_lh n j k hj, cdSign_succ_lh n j _ hj]
  by_cases hspec : k = 0 ∨ k = i ∨ k = j ∨ k = i ^^^ j
  · have hrhs : cdSign n i k * cdSign n i (k ^^^ (i ^^^ j)) *
                cdSign n j k * cdSign n j (k ^^^ (i ^^^ j)) = -1 :=
      blockDelta_special_nonsing n i j k hi0 hj0 hi hj hne hspec
    rw [hrhs]
    rcases hspec with hk0 | hki | hkj | hkd
    · rw [hk0, Nat.zero_xor, cdSign_zero_left n i hi, cdSign_zero_left n j hj, Int.one_mul, Int.mul_one]
      have hd0 : i ^^^ j ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
      have hxj : (i ^^^ j) ^^^ i = j := by rw [Nat.xor_comm i j, xor_sub_self_cancel]
      have := cdSign_left_alt_basis n (i ^^^ j) i (by omega) hd hi
      rw [hxj] at this; exact this
    · rw [hki]
      have hx : i ^^^ (i ^^^ j) = j := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [hx, cdSign_diag n i hi0 hi, cdSign_diag n j hj0 hj,
          cdSign_anticomm n j i hj0 hi0 hj hi (Ne.symm hne)]
      rcases cdSign_val_pm1 n i j with h | h <;> simp [h]
    · rw [hkj]
      have hx : j ^^^ (i ^^^ j) = i := by rw [Nat.xor_comm i j, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [hx, cdSign_diag n i hi0 hi, cdSign_diag n j hj0 hj,
          cdSign_anticomm n j i hj0 hi0 hj hi (Ne.symm hne)]
      rcases cdSign_val_pm1 n i j with h | h <;> simp [h]
    · rw [hkd, Nat.xor_self, cdSign_zero_left n i hi, cdSign_zero_left n j hj, Int.mul_one, Int.mul_one]
      have hd0 : i ^^^ j ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
      have hxj : (i ^^^ j) ^^^ i = j := by rw [Nat.xor_comm i j, xor_sub_self_cancel]
      have := cdSign_left_alt_basis n (i ^^^ j) i (by omega) hd hi
      rw [hxj] at this; exact this
  · have hk0 : k ≠ 0 := fun h => hspec (Or.inl h)
    have hki : k ≠ i := fun h => hspec (Or.inr (Or.inl h))
    have hkj : k ≠ j := fun h => hspec (Or.inr (Or.inr (Or.inl h)))
    have hkd : k ≠ i ^^^ j := fun h => hspec (Or.inr (Or.inr (Or.inr h)))
    have hkp0 : k ^^^ (i ^^^ j) ≠ 0 := fun hz => hkd (eq_of_xor_eq_zero hz)
    have hkpi : k ^^^ (i ^^^ j) ≠ i := by
      intro heq
      have : (k ^^^ (i ^^^ j)) ^^^ (i ^^^ j) = i ^^^ (i ^^^ j) := congrArg (· ^^^ (i ^^^ j)) heq
      rw [xor_sub_self_cancel, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; exact hkj this
    have hkpj : k ^^^ (i ^^^ j) ≠ j := by
      intro heq
      have : (k ^^^ (i ^^^ j)) ^^^ (i ^^^ j) = j ^^^ (i ^^^ j) := congrArg (· ^^^ (i ^^^ j)) heq
      rw [xor_sub_self_cancel, Nat.xor_comm i j, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; exact hki this
    rw [cdSign_anticomm n k i (by omega) hi0 hk hi hki,
        cdSign_anticomm n (k ^^^ (i ^^^ j)) i (by omega) hi0 hkp_lt hi hkpi,
        cdSign_anticomm n k j (by omega) hj0 hk hj hkj,
        cdSign_anticomm n (k ^^^ (i ^^^ j)) j (by omega) hj0 hkp_lt hj hkpj]
    simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]

theorem blockDelta_doubling_upper_lo (n i j k : Nat)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j) (hk : k < 2 ^ n) :
    blockDelta (n + 1) (i + 2 ^ n) (j + 2 ^ n) k = blockDelta n i j k := by
  unfold blockDelta; dsimp only
  have hd : (i + 2 ^ n) ^^^ (j + 2 ^ n) = i ^^^ j := xor_add_both hi hj
  have hkp : k ^^^ (i ^^^ j) < 2 ^ n := Nat.xor_lt_two_pow hk (Nat.xor_lt_two_pow hi hj)
  rw [hd, cdSign_succ_hl n i k hk, cdSign_succ_hl n i _ hkp,
      cdSign_succ_hl n j k hk, cdSign_succ_hl n j _ hkp]
  by_cases hk0 : k = 0
  · subst hk0
    have hd0 : i ^^^ j ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
    simp only [Nat.zero_xor, hd0, ↓reduceIte, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  · by_cases hkp0 : k ^^^ (i ^^^ j) = 0
    · simp only [hk0, hkp0, ↓reduceIte, Int.mul_neg, Int.neg_mul, Int.neg_neg]
    · simp only [hk0, hkp0, ↓reduceIte, Int.mul_neg, Int.neg_mul, Int.neg_neg]

theorem blockDelta_doubling_upper_hi (n i j k : Nat)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j)
    (hk : k < 2 ^ n) :
    blockDelta (n + 1) (i + 2 ^ n) (j + 2 ^ n) (k + 2 ^ n) = blockDelta n i j k := by
  have hlo := blockDelta_doubling_lower_hi n i j k hi0 hj0 hi hj hne hk
  rw [← hlo]
  unfold blockDelta; dsimp only
  have hd : (i + 2 ^ n) ^^^ (j + 2 ^ n) = i ^^^ j := xor_add_both hi hj
  have hdlt : i ^^^ j < 2 ^ n := Nat.xor_lt_two_pow hi hj
  have hkp_eq : (k + 2 ^ n) ^^^ (i ^^^ j) = (k ^^^ (i ^^^ j)) + 2 ^ n := xor_add_left hk hdlt
  rw [hd, hkp_eq, cdSign_succ_hh, cdSign_succ_hh, cdSign_succ_hh, cdSign_succ_hh,
      cdSign_succ_lh n i k hi, cdSign_succ_lh n i _ hi,
      cdSign_succ_lh n j k hj, cdSign_succ_lh n j _ hj]
  by_cases hk0 : k = 0
  · subst hk0
    have hd0 : i ^^^ j ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
    simp only [Nat.zero_xor, hd0, ↓reduceIte, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  · by_cases hkp0 : k ^^^ (i ^^^ j) = 0
    · simp only [hk0, hkp0, ↓reduceIte, Int.mul_neg, Int.neg_mul, Int.neg_neg]
    · simp only [hk0, hkp0, ↓reduceIte]

theorem cdSign_succ_h0_l (n j : Nat) (hj : j < 2 ^ n) :
    cdSign (n + 1) (2 ^ n) j = if j = 0 then 1 else -1 := by
  have h := cdSign_succ_hl n 0 j hj
  rw [Nat.zero_add, cdSign_zero_left n 0 (Nat.two_pow_pos n), cdSign_zero_left n j hj] at h
  exact h

theorem cdSign_succ_h0_h (n b : Nat) (hb : b < 2 ^ n) :
    cdSign (n + 1) (2 ^ n) (b + 2 ^ n) = if b = 0 then -1 else 1 := by
  have h := cdSign_succ_hh n 0 b
  rw [Nat.zero_add, cdSign_zero_left n 0 (Nat.two_pow_pos n), cdSign_zero_right n b hb] at h
  exact h

theorem blockDelta_doubling_axis_upper (n b k : Nat)
    (hb0 : 0 < b) (hb : b < 2 ^ n) (hk : k < 2 ^ (n + 1)) :
    blockDelta (n + 1) (2 ^ n) (b + 2 ^ n) k = -1 := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold blockDelta; dsimp only
  have hd : 2 ^ n ^^^ (b + 2 ^ n) = b := by
    have := xor_add_both (Nat.two_pow_pos n) hb; simpa using this
  rw [hd]
  by_cases hkh : k < 2 ^ n
  · have hkp : k ^^^ b < 2 ^ n := Nat.xor_lt_two_pow hkh hb
    rw [cdSign_succ_h0_l n k hkh, cdSign_succ_h0_l n _ hkp,
        cdSign_succ_hl n b k hkh, cdSign_succ_hl n b _ hkp,
        cdSign_zero_right n b hb]
    by_cases hk0 : k = 0
    · subst hk0
      have hbne : b ≠ 0 := by omega
      simp only [Nat.zero_xor, hbne, ↓reduceIte, cdSign_diag n b hb0 hb]; rfl
    · by_cases hkb0 : k ^^^ b = 0
      · have hkeq : k = b := eq_of_xor_eq_zero hkb0
        have hbne : b ≠ 0 := by omega
        rw [hkeq, Nat.xor_self, cdSign_diag n b hb0 hb]
        simp only [hbne, ↓reduceIte]; rfl
      · simp only [hk0, hkb0, ↓reduceIte]
        have := cdSign_left_alt_basis n b k hb0 hb hkh
        rw [Nat.xor_comm b k] at this
        simpa [Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.one_mul, Int.mul_one] using this
  · let c := k - 2 ^ n
    have hck : k = c + 2 ^ n := by omega
    have hclt : c < 2 ^ n := by omega
    have hkp_eq : (c + 2 ^ n) ^^^ b = (c ^^^ b) + 2 ^ n := xor_add_left hclt hb
    have hkp_lt : c ^^^ b < 2 ^ n := Nat.xor_lt_two_pow hclt hb
    rw [hck, hkp_eq, cdSign_succ_h0_h n c hclt, cdSign_succ_h0_h n _ hkp_lt,
        cdSign_succ_hh n b c, cdSign_succ_hh n b _, cdSign_zero_left n b hb]
    by_cases hc0 : c = 0
    · rw [hc0]
      have hbne : b ≠ 0 := by omega
      simp only [Nat.zero_xor, hbne, ↓reduceIte, cdSign_diag n b hb0 hb]; rfl
    · by_cases hcb0 : c ^^^ b = 0
      · have hceq : c = b := eq_of_xor_eq_zero hcb0
        have hbne : b ≠ 0 := by omega
        rw [hceq, Nat.xor_self, cdSign_diag n b hb0 hb]
        simp only [hbne, ↓reduceIte]; rfl
      · simp only [hc0, hcb0, ↓reduceIte]
        have := cdSign_right_alt_basis n b c hb0 hb hclt
        rw [Nat.xor_comm b c] at this
        simpa [Int.one_mul, Int.mul_one] using this

theorem blockDelta_doubling_axis_left (n i k : Nat)
    (hi0 : 0 < i) (hi : i < 2 ^ n) (hk : k < 2 ^ (n + 1)) :
    blockDelta (n + 1) i (2 ^ n) k = -1 := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd : i ^^^ 2 ^ n = i + 2 ^ n := by
    have := xor_add_right hi (Nat.two_pow_pos n); simpa using this
  have hlo : ∀ m, m < 2 ^ n → blockDelta (n + 1) i (2 ^ n) m = -1 := by
    intro m hm
    unfold blockDelta; dsimp only
    have hkp_eq : m ^^^ (i + 2 ^ n) = (m ^^^ i) + 2 ^ n := xor_add_right hm hi
    have hkp_lt : m ^^^ i < 2 ^ n := Nat.xor_lt_two_pow hm hi
    rw [hd, hkp_eq, cdSign_succ_ll n i m hi hm, cdSign_succ_lh n i _ hi,
        cdSign_succ_h0_l n m hm, cdSign_succ_h0_h n _ hkp_lt]
    by_cases hm0 : m = 0
    · subst hm0
      have hine : i ≠ 0 := by omega
      simp only [Nat.zero_xor, hine, ↓reduceIte,
                 cdSign_zero_right n i hi, cdSign_diag n i hi0 hi]; rfl
    · by_cases hmi : m ^^^ i = 0
      · have hmeq : m = i := eq_of_xor_eq_zero hmi
        have hine : i ≠ 0 := by omega
        rw [hmeq, Nat.xor_self, cdSign_diag n i hi0 hi, cdSign_zero_left n i hi]
        simp only [hine, ↓reduceIte]; rfl
      · simp only [hm0, hmi, ↓reduceIte]
        have hmi_ne : m ^^^ i ≠ i := by
          intro heq
          have : (m ^^^ i) ^^^ i = 0 := by rw [heq, Nat.xor_self]
          rw [xor_sub_self_cancel] at this; exact hm0 this
        rw [cdSign_anticomm n (m ^^^ i) i (by omega) hi0 hkp_lt hi hmi_ne]
        have := cdSign_left_alt_basis n i m hi0 hi hm
        rw [Nat.xor_comm i m] at this
        simpa [Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_one, Int.one_mul] using this
  by_cases hkh : k < 2 ^ n
  · exact hlo k hkh
  · rw [← blockDelta_pair_symm (n + 1) i (2 ^ n) k]
    have hkp : k ^^^ (i ^^^ 2 ^ n) < 2 ^ n := by
      let c := k - 2 ^ n
      have hck : k = c + 2 ^ n := by omega
      have hclt : c < 2 ^ n := by omega
      rw [hd, hck, xor_add_both hclt hi]
      exact Nat.xor_lt_two_pow hclt hi
    exact hlo _ hkp

theorem blockDelta_doubling_axis_diag (n i k : Nat)
    (_hi0 : 0 < i) (hi : i < 2 ^ n) (hk : k < 2 ^ (n + 1)) :
    blockDelta (n + 1) i (i + 2 ^ n) k = -1 := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd : i ^^^ (i + 2 ^ n) = 2 ^ n := by
    rw [xor_add_right hi hi, Nat.xor_self, Nat.zero_add]
  have hlo : ∀ m, m < 2 ^ n → blockDelta (n + 1) i (i + 2 ^ n) m = -1 := by
    intro m hm
    unfold blockDelta; dsimp only
    have hkp_eq : m ^^^ 2 ^ n = m + 2 ^ n := by
      have := xor_add_right hm (Nat.two_pow_pos n); simpa using this
    rw [hd, hkp_eq, cdSign_succ_ll n i m hi hm, cdSign_succ_lh n i m hi,
        cdSign_succ_hl n i m hm, cdSign_succ_hh n i m]
    by_cases hm0 : m = 0
    · subst hm0
      simp only [↓reduceIte, cdSign_zero_right n i hi, cdSign_zero_left n i hi]; rfl
    · simp only [hm0, ↓reduceIte]
      rcases cdSign_val_pm1 n i m with h1 | h1 <;> rcases cdSign_val_pm1 n m i with h2 | h2 <;>
        simp [h1, h2]
  by_cases hkh : k < 2 ^ n
  · exact hlo k hkh
  · rw [← blockDelta_pair_symm (n + 1) i (i + 2 ^ n) k]
    have hkp : k ^^^ (i ^^^ (i + 2 ^ n)) < 2 ^ n := by
      let c := k - 2 ^ n
      have hck : k = c + 2 ^ n := by omega
      have hclt : c < 2 ^ n := by omega
      rw [hd, hck]
      have h0 := xor_add_both hclt (Nat.two_pow_pos n)
      simp only [Nat.zero_add, Nat.xor_zero] at h0
      rw [h0]; exact hclt
    exact hlo _ hkp

theorem blockDelta_doubling_cross_lo (n i b k : Nat)
    (hi0 : 0 < i) (hb0 : 0 < b) (hi : i < 2 ^ n) (hb : b < 2 ^ n) (hne : i ≠ b)
    (hk : k < 2 ^ n) :
    blockDelta (n + 1) i (b + 2 ^ n) k =
      if (k = 0 ∨ k = i ∨ k = b ∨ k = i ^^^ b) then -1 else -(blockDelta n i b k) := by
  unfold blockDelta; dsimp only
  have hd : i ^^^ (b + 2 ^ n) = (i ^^^ b) + 2 ^ n := xor_add_right hi hb
  have hdlt : i ^^^ b < 2 ^ n := Nat.xor_lt_two_pow hi hb
  have hkp_eq : k ^^^ ((i ^^^ b) + 2 ^ n) = (k ^^^ (i ^^^ b)) + 2 ^ n := xor_add_right hk hdlt
  have hkp_lt : k ^^^ (i ^^^ b) < 2 ^ n := Nat.xor_lt_two_pow hk hdlt
  rw [hd, hkp_eq, cdSign_succ_ll n i k hi hk, cdSign_succ_lh n i _ hi,
      cdSign_succ_hl n b k hk, cdSign_succ_hh n b _]
  by_cases hspec : k = 0 ∨ k = i ∨ k = b ∨ k = i ^^^ b
  · simp only [hspec, ↓reduceIte]
    rcases hspec with hk0 | hki | hkb | hkd
    · rw [hk0]
      have hd0 : i ^^^ b ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
      simp only [Nat.zero_xor, hd0, ↓reduceIte,
                 cdSign_zero_right n i hi, cdSign_zero_right n b hb, Int.one_mul, Int.mul_one]
      have hxb : (i ^^^ b) ^^^ i = b := by rw [Nat.xor_comm i b, xor_sub_self_cancel]
      have := cdSign_left_alt_basis n (i ^^^ b) i (by omega) hdlt hi
      rw [hxb] at this; exact this
    · rw [hki]
      have hx : i ^^^ (i ^^^ b) = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hine : i ≠ 0 := by omega
      have hbne : b ≠ 0 := by omega
      rw [hx, cdSign_diag n i hi0 hi, cdSign_diag n b hb0 hb]
      simp only [hine, hbne, ↓reduceIte]
      rcases cdSign_val_pm1 n b i with h | h <;> simp [h]
    · rw [hkb]
      have hx : b ^^^ (i ^^^ b) = i := by rw [Nat.xor_comm i b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hine : i ≠ 0 := by omega
      have hbne : b ≠ 0 := by omega
      rw [hx, cdSign_diag n i hi0 hi, cdSign_diag n b hb0 hb]
      simp only [hine, hbne, ↓reduceIte]
      rcases cdSign_val_pm1 n i b with h | h <;> simp [h]
    · rw [hkd]
      have hd0 : i ^^^ b ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
      simp only [hd0, Nat.xor_self, ↓reduceIte,
                 cdSign_zero_left n i hi, cdSign_zero_left n b hb, Int.mul_one]
      have hdi : i ^^^ b ≠ i := by
        intro heq
        have : (i ^^^ b) ^^^ i = 0 := by rw [heq, Nat.xor_self]
        rw [Nat.xor_comm i b, xor_sub_self_cancel] at this; omega
      have hdb2 : i ^^^ b ≠ b := by
        intro heq
        have : (i ^^^ b) ^^^ b = 0 := by rw [heq, Nat.xor_self]
        rw [xor_sub_self_cancel] at this; omega
      rw [cdSign_anticomm n i (i ^^^ b) hi0 (by omega) hi hdlt (Ne.symm hdi),
          cdSign_anticomm n b (i ^^^ b) hb0 (by omega) hb hdlt (Ne.symm hdb2)]
      have hxb : (i ^^^ b) ^^^ i = b := by rw [Nat.xor_comm i b, xor_sub_self_cancel]
      have := cdSign_left_alt_basis n (i ^^^ b) i (by omega) hdlt hi
      rw [hxb] at this
      simpa [Int.mul_neg, Int.neg_mul, Int.neg_neg] using this
  · simp only [hspec, ↓reduceIte]
    have hk0 : k ≠ 0 := fun h => hspec (Or.inl h)
    have hki : k ≠ i := fun h => hspec (Or.inr (Or.inl h))
    have hkb : k ≠ b := fun h => hspec (Or.inr (Or.inr (Or.inl h)))
    have hkd : k ≠ i ^^^ b := fun h => hspec (Or.inr (Or.inr (Or.inr h)))
    have hkp0 : k ^^^ (i ^^^ b) ≠ 0 := fun hz => hkd (eq_of_xor_eq_zero hz)
    have hkpi : k ^^^ (i ^^^ b) ≠ i := by
      intro heq
      have : (k ^^^ (i ^^^ b)) ^^^ (i ^^^ b) = i ^^^ (i ^^^ b) := congrArg (· ^^^ (i ^^^ b)) heq
      rw [xor_sub_self_cancel, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; exact hkb this
    have hkpb : k ^^^ (i ^^^ b) ≠ b := by
      intro heq
      have : (k ^^^ (i ^^^ b)) ^^^ (i ^^^ b) = b ^^^ (i ^^^ b) := congrArg (· ^^^ (i ^^^ b)) heq
      rw [xor_sub_self_cancel, Nat.xor_comm i b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; exact hki this
    simp only [hk0, hkp0, ↓reduceIte]
    rw [cdSign_anticomm n (k ^^^ (i ^^^ b)) i (by omega) hi0 hkp_lt hi hkpi,
        cdSign_anticomm n (k ^^^ (i ^^^ b)) b (by omega) hb0 hkp_lt hb hkpb]
    simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]

/-! ### Theorem T2b: Universal All-$n$ 2-Blade Nullity Doubling Recurrence -/

theorem countSingularIdx_split (n i j : Nat) :
    countSingularIdx (n + 1) i j (2 ^ (n + 1)) =
      countSingularIdx (n + 1) i j (2 ^ n) +
      countPred (fun k => blockDelta (n + 1) i j (2 ^ n + k) == 1) (2 ^ n) := by
  rw [countSingularIdx_eq_countPred, countSingularIdx_eq_countPred]
  have h2n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
  rw [h2n, countPred_add]

theorem nullity_doubling_lower (n i j : Nat)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j) :
    twobladeNullity (n + 1) i j = 2 * twobladeNullity n i j := by
  unfold twobladeNullity
  rw [countSingularIdx_split]
  have h1 : countSingularIdx (n + 1) i j (2 ^ n) = countSingularIdx n i j (2 ^ n) := by
    rw [countSingularIdx_eq_countPred, countSingularIdx_eq_countPred]
    apply countPred_ext; intro k hk
    simp [blockDelta_doubling_lower_lo n i j k hi hj hk]
  have h2 : countPred (fun k => blockDelta (n + 1) i j (2 ^ n + k) == 1) (2 ^ n) =
            countSingularIdx n i j (2 ^ n) := by
    rw [countSingularIdx_eq_countPred]
    apply countPred_ext; intro k hk
    rw [Nat.add_comm (2 ^ n) k]
    simp [blockDelta_doubling_lower_hi n i j k hi0 hj0 hi hj hne hk]
  rw [h1, h2]
  rcases countSingularIdx_even_aux n i j hi hj hne with ⟨c, hc⟩
  rw [hc]; omega

theorem nullity_doubling_upper (n i j : Nat)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j) :
    twobladeNullity (n + 1) (i + 2 ^ n) (j + 2 ^ n) = 2 * twobladeNullity n i j := by
  unfold twobladeNullity
  rw [countSingularIdx_split]
  have h1 : countSingularIdx (n + 1) (i + 2 ^ n) (j + 2 ^ n) (2 ^ n) =
            countSingularIdx n i j (2 ^ n) := by
    rw [countSingularIdx_eq_countPred, countSingularIdx_eq_countPred]
    apply countPred_ext; intro k hk
    simp [blockDelta_doubling_upper_lo n i j k hi hj hne hk]
  have h2 : countPred (fun k => blockDelta (n + 1) (i + 2 ^ n) (j + 2 ^ n) (2 ^ n + k) == 1) (2 ^ n) =
            countSingularIdx n i j (2 ^ n) := by
    rw [countSingularIdx_eq_countPred]
    apply countPred_ext; intro k hk
    rw [Nat.add_comm (2 ^ n) k]
    simp [blockDelta_doubling_upper_hi n i j k hi0 hj0 hi hj hne hk]
  rw [h1, h2]
  rcases countSingularIdx_even_aux n i j hi hj hne with ⟨c, hc⟩
  rw [hc]; omega

theorem nullity_doubling_axis (n a : Nat) (ha0 : 0 < a) (ha : a < 2 ^ n) :
    twobladeNullity (n + 1) (2 ^ n) (a + 2 ^ n) = 0 ∧
    twobladeNullity (n + 1) a (2 ^ n) = 0 ∧
    twobladeNullity (n + 1) a (a + 2 ^ n) = 0 := by
  have helper : ∀ x y, (∀ k, k < 2 ^ (n + 1) → blockDelta (n + 1) x y k = -1) →
      twobladeNullity (n + 1) x y = 0 := by
    intro x y hall
    unfold twobladeNullity
    have hz : ∀ m, m ≤ 2 ^ (n + 1) → countSingularIdx (n + 1) x y m = 0 := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ih =>
        unfold countSingularIdx
        rw [ih (by omega), hall m (by omega)]
        rfl
    rw [hz _ (Nat.le_refl _)]
  refine ⟨helper _ _ (fun k hk => blockDelta_doubling_axis_upper n a k ha0 ha hk),
          helper _ _ (fun k hk => blockDelta_doubling_axis_left n a k ha0 ha hk),
          helper _ _ (fun k hk => blockDelta_doubling_axis_diag n a k ha0 ha hk)⟩

theorem countPred_single (a : Nat) :
    ∀ lim, countPred (fun k => decide (k = a)) lim = if a < lim then 1 else 0 := by
  intro lim
  induction lim with
  | zero => simp [countPred]
  | succ m ih =>
    unfold countPred
    rw [ih]
    by_cases h : m = a
    · subst h; simp
    · by_cases hlt : a < m
      · have hlt2 : a < m + 1 := by omega
        simp [h, hlt, hlt2]
      · have hlt2 : ¬(a < m + 1) := by omega
        simp [h, hlt, hlt2]

theorem nullity_doubling_cross (n i b : Nat) (_hn : 2 ≤ n)
    (hi0 : 0 < i) (hb0 : 0 < b) (hi : i < 2 ^ n) (hb : b < 2 ^ n) (hne : i ≠ b) :
    twobladeNullity (n + 1) i (b + 2 ^ n) = 2 ^ n - 4 - 2 * twobladeNullity n i b := by
  unfold twobladeNullity
  rw [countSingularIdx_split]
  have hd : i ^^^ (b + 2 ^ n) = (i ^^^ b) + 2 ^ n := xor_add_right hi hb
  have hdlt : i ^^^ b < 2 ^ n := Nat.xor_lt_two_pow hi hb
  have hhi_eq : countPred (fun k => blockDelta (n + 1) i (b + 2 ^ n) (2 ^ n + k) == 1) (2 ^ n) =
                countSingularIdx (n + 1) i (b + 2 ^ n) (2 ^ n) := by
    rw [countSingularIdx_eq_countPred]
    rw [countPred_xor_bijection n (fun k => blockDelta (n + 1) i (b + 2 ^ n) k == 1) (i ^^^ b) hdlt]
    apply countPred_ext; intro k hk
    have hsym := blockDelta_pair_symm (n + 1) i (b + 2 ^ n) (2 ^ n + k)
    have hkp : (2 ^ n + k) ^^^ (i ^^^ (b + 2 ^ n)) = k ^^^ (i ^^^ b) := by
      rw [hd, Nat.add_comm (2 ^ n) k, xor_add_both hk hdlt]
    rw [hkp] at hsym
    simp [hsym]
  rw [hhi_eq]
  have hdiv2 : (countSingularIdx (n + 1) i (b + 2 ^ n) (2 ^ n) +
                countSingularIdx (n + 1) i (b + 2 ^ n) (2 ^ n)) / 2 =
               countSingularIdx (n + 1) i (b + 2 ^ n) (2 ^ n) := by omega
  rw [hdiv2]
  let isSpec : Nat → Bool := fun k => decide (k = 0 ∨ k = i ∨ k = b ∨ k = i ^^^ b)
  have hsum_all : ∀ m, m ≤ 2 ^ n →
      countSingularIdx (n + 1) i (b + 2 ^ n) m +
      countSingularIdx n i b m +
      countPred isSpec m = m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      unfold countSingularIdx countPred
      have hih := ih (by omega)
      have hcross := blockDelta_doubling_cross_lo n i b m hi0 hb0 hi hb hne (by omega)
      by_cases hsp : m = 0 ∨ m = i ∨ m = b ∨ m = i ^^^ b
      · have hstd := blockDelta_special_nonsing n i b m hi0 hb0 hi hb hne hsp
        have hisp : isSpec m = true := by simp [isSpec, hsp]
        rw [hcross, hstd, hisp]
        simp only [hsp, ↓reduceIte]
        have hne1 : ((-1 : Int) == 1) = false := rfl
        simp only [hne1, Bool.false_eq_true, ↓reduceIte]
        omega
      · have hisp : isSpec m = false := decide_eq_false hsp
        rw [hcross, hisp]
        simp only [hsp, ↓reduceIte, Bool.false_eq_true]
        rcases blockDelta_val_pm1 n i b m with h1 | h1 <;> simp [h1] <;> omega
  have hd0 : i ^^^ b ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
  have hdi : i ^^^ b ≠ i := by
    intro heq
    have : (i ^^^ b) ^^^ i = 0 := by rw [heq, Nat.xor_self]
    rw [Nat.xor_comm i b, xor_sub_self_cancel] at this; omega
  have hdb : i ^^^ b ≠ b := by
    intro heq
    have : (i ^^^ b) ^^^ b = 0 := by rw [heq, Nat.xor_self]
    rw [xor_sub_self_cancel] at this; omega
  have hspec4 : countPred isSpec (2 ^ n) = 4 := by
    have hsplit4 : ∀ m,
        countPred isSpec m =
        countPred (fun k => decide (k = 0)) m +
        countPred (fun k => decide (k = i)) m +
        countPred (fun k => decide (k = b)) m +
        countPred (fun k => decide (k = i ^^^ b)) m := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        unfold countPred; rw [ih]
        by_cases h0 : m = 0
        · rw [h0]
          have h1 : (0 : Nat) ≠ i := by omega
          have h2 : (0 : Nat) ≠ b := by omega
          have h3 : (0 : Nat) ≠ i ^^^ b := Ne.symm hd0
          simp [isSpec, h1, h2, h3]; omega
        · by_cases h1 : m = i
          · rw [h1]
            have h0i : i ≠ 0 := by omega
            have h2 : i ≠ b := hne
            have h3 : i ≠ i ^^^ b := Ne.symm hdi
            have hsp : isSpec i = true := by simp [isSpec]
            simp only [hsp, h0i, h2, h3, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
            omega
          · by_cases h2 : m = b
            · rw [h2]
              have h0b : b ≠ 0 := by omega
              have h1b : b ≠ i := Ne.symm hne
              have h3 : b ≠ i ^^^ b := Ne.symm hdb
              have hsp : isSpec b = true := by simp [isSpec]
              simp only [hsp, h0b, h1b, h3, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
              omega
            · by_cases h3 : m = i ^^^ b
              · rw [h3]
                simp [isSpec, hd0, hdi, hdb]; omega
              · simp [isSpec, h0, h1, h2, h3]
    rw [hsplit4 (2 ^ n), countPred_single, countPred_single, countPred_single, countPred_single]
    have h0lt : 0 < 2 ^ n := Nat.two_pow_pos n
    simp [h0lt, hi, hb, hdlt]
  have htot := hsum_all (2 ^ n) (Nat.le_refl _)
  rw [hspec4] at htot
  rcases countSingularIdx_even_aux n i b hi hb hne with ⟨c, hc⟩
  rw [hc] at htot ⊢
  omega

/-! ### Base Case $n = 3$ (Octonions $\mathbb{O}_8$): Pure Kernel Certification -/

theorem octonion_no_twoblade_zd :
    ∀ i j, 0 < i → i < j → j < 8 → twobladeNullity 3 i j = 0 := by
  have h : (List.range 8).all (fun i =>
      (List.range 8).all (fun j =>
        !(0 < i && i < j) || twobladeNullity 3 i j == 0)) = true := by decide
  intro i j hi0 hij hj
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
             decide_eq_false_iff_not, beq_iff_eq] at h2
  rcases h2 with (hnot | hnot) | heq
  · omega
  · omega
  · exact heq

theorem octonion_nullity_all_zero (i j : Nat) (hi0 : 0 < i) (hj0 : 0 < j)
    (hi : i < 8) (hj : j < 8) (hne : i ≠ j) :
    twobladeNullity 3 i j = 0 := by
  by_cases h : i < j
  · exact octonion_no_twoblade_zd i j hi0 h hj
  · rw [twobladeNullity_symm]
    exact octonion_no_twoblade_zd j i hj0 (by omega) hi

theorem octonion_nonZD_21 : nullityHist 3 0 = 21 := by decide
theorem octonion_mass_zero : totalNullityMass 3 = 0 := by decide
theorem sedenion_hist_42 : nullityHist 4 4 = 42 := by decide

/-! ### Theorem T2c: Universal Divisibility by 4, $2^{n-1} - 4$ Ceiling & BDI Separation -/

theorem nullity_mod4_and_bound :
    ∀ n, 3 ≤ n → ∀ i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
      4 ∣ twobladeNullity n i j ∧ (4 ≤ n → twobladeNullity n i j ≤ 2 ^ (n - 1) - 4) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro i j hi0 hj0 hi hj hne
    by_cases hn3 : n = 2
    · subst hn3
      have hz := octonion_nullity_all_zero i j hi0 hj0 hi hj hne
      exact ⟨by rw [hz]; exact ⟨0, rfl⟩, fun h4 => by omega⟩
    · have hn_ge3 : 3 ≤ n := by omega
      have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpow_ge8 : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_ge3
      have h4pow : 2 ^ n = 4 * 2 ^ (n - 2) := two_pow_mul_split n 2 (by omega)
      have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
      by_cases hih : i < 2 ^ n <;> by_cases hjh : j < 2 ^ n
      · rw [nullity_doubling_lower n i j hi0 hj0 hih hjh hne]
        rcases ih hn_ge3 i j hi0 hj0 hih hjh hne with ⟨⟨k, hk⟩, hbd⟩
        refine ⟨⟨2 * k, by omega⟩, fun _ => ?_⟩
        by_cases hn4 : n = 3
        · subst hn4
          have hz := octonion_nullity_all_zero i j hi0 hj0 hih hjh hne
          rw [hz]; omega
        · have hb := hbd (by omega)
          have hsub : n + 1 - 1 = n := by omega
          rw [hsub]; omega
      · let b := j - 2 ^ n
        have hbj : j = b + 2 ^ n := by omega
        have hblt : b < 2 ^ n := by omega
        by_cases hb0 : b = 0
        · have hj_eq : j = 2 ^ n := by omega
          rw [hj_eq, (nullity_doubling_axis n i hi0 hih).2.1]
          exact ⟨⟨0, rfl⟩, fun _ => Nat.zero_le _⟩
        · by_cases hbi : i = b
          · have hj_eq : j = i + 2 ^ n := by omega
            rw [hj_eq, (nullity_doubling_axis n i hi0 hih).2.2]
            exact ⟨⟨0, rfl⟩, fun _ => Nat.zero_le _⟩
          · rw [hbj, nullity_doubling_cross n i b (by omega) hi0 (by omega) hih hblt hbi]
            rcases ih hn_ge3 i b hi0 (by omega) hih hblt hbi with ⟨⟨k, hk⟩, hbd⟩
            have hle : 2 * twobladeNullity n i b ≤ 2 ^ n - 4 := by
              by_cases hn4 : n = 3
              · subst hn4; rw [octonion_nullity_all_zero i b hi0 (by omega) hih hblt hbi]; omega
              · have hb' := hbd (by omega); omega
            refine ⟨⟨2 ^ (n - 2) - 1 - 2 * k, by omega⟩, fun _ => ?_⟩
            have hsub : n + 1 - 1 = n := by omega
            rw [hsub]; omega
      · rw [twobladeNullity_symm]
        let a := i - 2 ^ n
        have hai : i = a + 2 ^ n := by omega
        have halt : a < 2 ^ n := by omega
        by_cases ha0 : a = 0
        · have hi_eq : i = 2 ^ n := by omega
          rw [hi_eq, (nullity_doubling_axis n j hj0 hjh).2.1]
          exact ⟨⟨0, rfl⟩, fun _ => Nat.zero_le _⟩
        · by_cases haj : j = a
          · have hi_eq : i = j + 2 ^ n := by omega
            rw [hi_eq, (nullity_doubling_axis n j hj0 hjh).2.2]
            exact ⟨⟨0, rfl⟩, fun _ => Nat.zero_le _⟩
          · rw [hai, nullity_doubling_cross n j a (by omega) hj0 (by omega) hjh halt haj]
            rcases ih hn_ge3 j a hj0 (by omega) hjh halt haj with ⟨⟨k, hk⟩, hbd⟩
            have hle : 2 * twobladeNullity n j a ≤ 2 ^ n - 4 := by
              by_cases hn4 : n = 3
              · subst hn4; rw [octonion_nullity_all_zero j a hj0 (by omega) hjh halt haj]; omega
              · have hb' := hbd (by omega); omega
            refine ⟨⟨2 ^ (n - 2) - 1 - 2 * k, by omega⟩, fun _ => ?_⟩
            have hsub : n + 1 - 1 = n := by omega
            rw [hsub]; omega
      · let a := i - 2 ^ n
        let b := j - 2 ^ n
        have hai : i = a + 2 ^ n := by omega
        have hbj : j = b + 2 ^ n := by omega
        have halt : a < 2 ^ n := by omega
        have hblt : b < 2 ^ n := by omega
        by_cases ha0 : a = 0
        · have hi_eq : i = 2 ^ n := by omega
          rw [hi_eq, hbj, (nullity_doubling_axis n b (by omega) hblt).1]
          exact ⟨⟨0, rfl⟩, fun _ => Nat.zero_le _⟩
        · by_cases hb0 : b = 0
          · have hj_eq : j = 2 ^ n := by omega
            rw [twobladeNullity_symm, hj_eq, hai, (nullity_doubling_axis n a (by omega) halt).1]
            exact ⟨⟨0, rfl⟩, fun _ => Nat.zero_le _⟩
          · rw [hai, hbj, nullity_doubling_upper n a b (by omega) (by omega) halt hblt (by omega)]
            rcases ih hn_ge3 a b (by omega) (by omega) halt hblt (by omega) with ⟨⟨k, hk⟩, hbd⟩
            refine ⟨⟨2 * k, by omega⟩, fun _ => ?_⟩
            by_cases hn4 : n = 3
            · subst hn4; rw [octonion_nullity_all_zero a b (by omega) (by omega) halt hblt (by omega)]; omega
            · have hb' := hbd (by omega)
              have hsub : n + 1 - 1 = n := by omega
              rw [hsub]; omega

/-- **Theorem T2c (Strict Separation from Biss-Dugger-Isaksen Max Annihilator):**
    For EVERY $n \ge 5$ ($\dim \ge 32$), $2^{n-1} - 4 < 2^n - 4n + 4$ (with equality uniquely at $n = 4$: $4 = 4$). -/
theorem twoblade_strictly_below_bdi (n : Nat) (hn : 5 ≤ n) :
    twobladeMaxNullity n < bdiMaxAnnihilator n := by
  unfold twobladeMaxNullity bdiMaxAnnihilator
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
  have hlin : ∀ m, 4 ≤ m → 4 * (m + 1) < 2 ^ m + 8 := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hm4 : m = 3
      · subst hm4; decide
      · have := ih (by omega); rw [Nat.pow_succ]; omega
  have h5 := hlin (n - 1) (by omega)
  have hsub : n - 1 + 1 = n := by omega
  rw [hsub] at h5
  omega

/-! ### Clean Reusable 1D & 2D Summation Helpers -/

/-- General finite sum $\sum_{k=0}^{m-1} f(k)$. -/
@[expose] def sumNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumNat f m + f m

theorem sumNat_ext (f g : Nat → Nat) (m : Nat) (h : ∀ k, k < m → f k = g k) :
    sumNat f m = sumNat g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold sumNat; rw [ih (fun k hk => h k (by omega)), h m (by omega)]

theorem sumNat_add (f : Nat → Nat) (a b : Nat) :
    sumNat f (a + b) = sumNat f a + sumNat (fun k => f (a + k)) b := by
  induction b with
  | zero => simp [sumNat]
  | succ b ih =>
    rw [Nat.add_succ]
    show sumNat f (a + b) + f (a + b) = sumNat f a + (sumNat (fun k => f (a + k)) b + f (a + b))
    rw [ih]; omega

theorem sumNat_pointwise_add (f g : Nat → Nat) (m : Nat) :
    sumNat (fun k => f k + g k) m = sumNat f m + sumNat g m := by
  induction m with
  | zero => rfl
  | succ m ih => unfold sumNat; rw [ih]; omega

theorem sumNat_const (c m : Nat) : sumNat (fun _ => c) m = m * c := by
  induction m with
  | zero => simp [sumNat]
  | succ m ih => unfold sumNat; rw [ih, Nat.succ_mul]

theorem sumNat_scale (c : Nat) (f : Nat → Nat) (m : Nat) :
    sumNat (fun k => c * f k) m = c * sumNat f m := by
  induction m with
  | zero => simp [sumNat]
  | succ m ih => unfold sumNat; rw [ih, Nat.mul_add]

theorem sumNat_zero (m : Nat) : sumNat (fun _ => 0) m = 0 := by
  rw [sumNat_const, Nat.mul_zero]

theorem sumNat_transpose (f : Nat → Nat → Nat) (m k : Nat) :
    sumNat (fun i => sumNat (fun j => f i j) k) m =
    sumNat (fun j => sumNat (fun i => f i j) m) k := by
  induction m with
  | zero =>
    simp only [sumNat]
    exact (sumNat_zero k).symm
  | succ m ihm =>
    show sumNat (fun i => sumNat (fun j => f i j) k) m + sumNat (fun j => f m j) k =
         sumNat (fun j => sumNat (fun i => f i j) m + f m j) k
    rw [ihm, ← sumNat_pointwise_add]

theorem countPred_eq_sumNat (Q : Nat → Bool) (m : Nat) :
    countPred Q m = sumNat (fun k => if Q k then 1 else 0) m := by
  induction m with
  | zero => rfl
  | succ m ih => unfold countPred sumNat; rw [ih]

/-- Unordered pair sum $\sum_{1 \le i < j < h} f(i, j)$. -/
@[expose] def sumUnordered (f : Nat → Nat → Nat) (h : Nat) : Nat :=
  sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then f i j else 0) h) h

/-- Ordered off-diagonal pair sum $\sum_{1 \le i \neq j < h} f(i, j)$. -/
@[expose] def sumOrderedOffDiag (f : Nat → Nat → Nat) (h : Nat) : Nat :=
  sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if 0 < j ∧ i ≠ j then f i j else 0) h) h

theorem sumUnordered_ext (f g : Nat → Nat → Nat) (h : Nat)
    (hext : ∀ i j, 0 < i → i < j → j < h → f i j = g i j) :
    sumUnordered f h = sumUnordered g h := by
  unfold sumUnordered
  apply sumNat_ext; intro i hi
  by_cases hi0 : i = 0
  · simp [hi0]
  · simp only [hi0, ↓reduceIte]
    apply sumNat_ext; intro j hj
    by_cases hij : i < j
    · simp [hij, hext i j (by omega) hij hj]
    · simp [hij]

theorem sumOrderedOffDiag_symm (f : Nat → Nat → Nat) (h : Nat)
    (hsym : ∀ i j, 0 < i → 0 < j → i < h → j < h → f i j = f j i) :
    sumOrderedOffDiag f h = 2 * sumUnordered f h := by
  have hu : sumUnordered f h =
      sumNat (fun i => sumNat (fun j => if 0 < i ∧ i < j then f i j else 0) h) h := by
    unfold sumUnordered
    apply sumNat_ext; intro i _
    by_cases hi0 : i = 0
    · subst hi0; simp [sumNat_zero]
    · simp only [hi0, ↓reduceIte]
      apply sumNat_ext; intro j _
      have hip : 0 < i := by omega
      by_cases hij : i < j <;> simp [hip, hij]
  have ho : sumOrderedOffDiag f h =
      sumNat (fun i => sumNat (fun j => if 0 < i ∧ 0 < j ∧ i ≠ j then f i j else 0) h) h := by
    unfold sumOrderedOffDiag
    apply sumNat_ext; intro i _
    by_cases hi0 : i = 0
    · subst hi0; simp [sumNat_zero]
    · simp only [hi0, ↓reduceIte]
      apply sumNat_ext; intro j _
      have hip : 0 < i := by omega
      simp [hip]
  rw [ho, hu]
  have hsplit :
      sumNat (fun i => sumNat (fun j => if 0 < i ∧ 0 < j ∧ i ≠ j then f i j else 0) h) h =
      sumNat (fun i => sumNat (fun j => if 0 < i ∧ i < j then f i j else 0) h) h +
      sumNat (fun i => sumNat (fun j => if 0 < j ∧ j < i then f i j else 0) h) h := by
    rw [← sumNat_pointwise_add]
    apply sumNat_ext; intro i _
    rw [← sumNat_pointwise_add]
    apply sumNat_ext; intro j _
    by_cases h1 : 0 < i <;> by_cases h2 : 0 < j <;> by_cases h3 : i < j <;> by_cases h4 : j < i <;>
      simp [h1, h2, h3, h4] <;> omega
  rw [hsplit, sumNat_transpose (fun i j => if 0 < j ∧ j < i then f i j else 0) h h]
  have htr : sumNat (fun j => sumNat (fun i => if 0 < j ∧ j < i then f i j else 0) h) h =
             sumNat (fun i => sumNat (fun j => if 0 < i ∧ i < j then f i j else 0) h) h := by
    apply sumNat_ext; intro a ha
    apply sumNat_ext; intro b hb
    by_cases h1 : 0 < a <;> by_cases h2 : a < b
    · simp [h1, h2, hsym b a (by omega) h1 hb ha]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [htr]; omega

theorem nullityHist_eq_sumUnordered (n v : Nat) :
    nullityHist n v = sumUnordered (fun i j => if twobladeNullity n i j = v then 1 else 0) (2 ^ n) := by
  unfold nullityHist nullityHistGamma sumUnordered
  have hrow : ∀ i lim, i < 2 ^ n → lim ≤ 2 ^ n →
      nullityHistRow n 0 v i lim =
      sumNat (fun j => if i < j then (if twobladeNullity n i j = v then 1 else 0) else 0) lim := by
    intro i lim hi hlim
    induction lim with
    | zero => rfl
    | succ j ih =>
      unfold nullityHistRow sumNat
      rw [ih (by omega)]
      have hstd0 : twobladeNullityGamma n 0 i j = twobladeNullity n i j := by
        unfold twobladeNullityGamma twobladeNullity
        have hp : parityBits n ((i ^^^ j) &&& 0) = false := by simp [parityBits_zero]
        exact congrArg (· / 2) (countSingularIdxGamma_eq_std n 0 i j hi (by omega) hp (2 ^ n) (Nat.le_refl _))
      rw [hstd0]
      by_cases hij : i < j <;> by_cases hv : twobladeNullity n i j = v <;> simp [hij, hv]
  suffices ∀ limI, limI ≤ 2 ^ n →
      nullityHistRange n 0 v limI (2 ^ n) =
      sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then (if twobladeNullity n i j = v then 1 else 0) else 0) (2 ^ n)) limI by
    exact this (2 ^ n) (Nat.le_refl _)
  intro limI hI
  induction limI with
  | zero => rfl
  | succ i ih =>
    unfold nullityHistRange sumNat
    rw [ih (by omega)]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · simp only [hi0, beq_iff_eq, ↓reduceIte, hrow i (2 ^ n) (by omega) (Nat.le_refl _)]

theorem totalNullityMass_eq_sumUnordered (n : Nat) :
    totalNullityMass n = sumUnordered (fun i j => twobladeNullity n i j) (2 ^ n) := by
  unfold totalNullityMass sumUnordered
  have hrow : ∀ i lim, totalNullityMassRow n i lim =
      sumNat (fun j => if i < j then twobladeNullity n i j else 0) lim := by
    intro i lim
    induction lim with
    | zero => rfl
    | succ j ih => unfold totalNullityMassRow sumNat; rw [ih]
  suffices ∀ limI, totalNullityMassRange n limI (2 ^ n) =
      sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then twobladeNullity n i j else 0) (2 ^ n)) limI by
    exact this (2 ^ n)
  intro limI
  induction limI with
  | zero => rfl
  | succ i ih =>
    unfold totalNullityMassRange sumNat
    rw [ih]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · simp only [hi0, beq_iff_eq, ↓reduceIte, hrow]

/-! ### Universal Unordered-Pair Splitting Theorem for Any Function of `twobladeNullity (n + 1)` -/

/-- Master 4-region splitting identity for $\sum_{1 \le i < j < 2^{n+1}} F(\nu_{n+1}(i, j))$:
    lower-lower + upper-upper + $3(2^n - 1)$ axis-pinned zeros + ordered cross-half pairs. -/
theorem sumUnordered_nullity_doubling (n : Nat) (hn : 3 ≤ n) (F : Nat → Nat) :
    sumUnordered (fun i j => F (twobladeNullity (n + 1) i j)) (2 ^ (n + 1)) =
      2 * sumUnordered (fun i j => F (2 * twobladeNullity n i j)) (2 ^ n) +
      3 * (2 ^ n - 1) * F 0 +
      2 * sumUnordered (fun i b => F (2 ^ n - 4 - 2 * twobladeNullity n i b)) (2 ^ n) := by
  have h2n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  unfold sumUnordered
  rw [h2n, sumNat_add]
  -- Part 1: i < 2^n
  have hpart1 :
      sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then F (twobladeNullity (n + 1) i j) else 0) (2 ^ n + 2 ^ n)) (2 ^ n) =
      sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then F (2 * twobladeNullity n i j) else 0) (2 ^ n)) (2 ^ n) +
      sumOrderedOffDiag (fun i b => F (2 ^ n - 4 - 2 * twobladeNullity n i b)) (2 ^ n) +
      2 * (2 ^ n - 1) * F 0 := by
    -- Split inner j ∈ [0, 2^n + 2^n) for each 0 < i < 2^n:
    have hrow : ∀ i, i < 2 ^ n →
        (if i = 0 then 0 else sumNat (fun j => if i < j then F (twobladeNullity (n + 1) i j) else 0) (2 ^ n + 2 ^ n)) =
        (if i = 0 then 0 else sumNat (fun j => if i < j then F (2 * twobladeNullity n i j) else 0) (2 ^ n)) +
        (if i = 0 then 0 else sumNat (fun b => if 0 < b ∧ i ≠ b then F (2 ^ n - 4 - 2 * twobladeNullity n i b) else 0) (2 ^ n)) +
        (if i = 0 then 0 else 2 * F 0) := by
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceIte]
        rw [sumNat_add]
        have hlo : sumNat (fun j => if i < j then F (twobladeNullity (n + 1) i j) else 0) (2 ^ n) =
                   sumNat (fun j => if i < j then F (2 * twobladeNullity n i j) else 0) (2 ^ n) := by
          apply sumNat_ext; intro j hj
          by_cases hij : i < j
          · simp [hij, nullity_doubling_lower n i j (by omega) (by omega) hi hj (by omega)]
          · simp [hij]
        have hhi : sumNat (fun b => if i < 2 ^ n + b then F (twobladeNullity (n + 1) i (2 ^ n + b)) else 0) (2 ^ n) =
                   sumNat (fun b => if 0 < b ∧ i ≠ b then F (2 ^ n - 4 - 2 * twobladeNullity n i b) else 0) (2 ^ n) + 2 * F 0 := by
          have hcomb : ∀ lim, lim ≤ 2 ^ n →
              sumNat (fun b => if i < 2 ^ n + b then F (twobladeNullity (n + 1) i (2 ^ n + b)) else 0) lim =
              sumNat (fun b => if 0 < b ∧ i ≠ b then F (2 ^ n - 4 - 2 * twobladeNullity n i b) else 0) lim +
              sumNat (fun b => if b = 0 then F 0 else 0) lim +
              sumNat (fun b => if b = i then F 0 else 0) lim := by
            intro lim hlim
            induction lim with
            | zero => rfl
            | succ b ihb =>
              unfold sumNat; rw [ihb (by omega)]
              have hilt : i < 2 ^ n + b := by omega
              by_cases hb0 : b = 0
              · subst hb0
                have hax := (nullity_doubling_axis n i (by omega) hi).2.1
                have h0ne : (0 : Nat) ≠ i := by omega
                have hnot : ¬(0 < 0 ∧ i ≠ 0) := by omega
                simp only [Nat.add_zero, hi, hax, hnot, h0ne, ↓reduceIte]; omega
              · by_cases hbi : b = i
                · subst hbi
                  have hax := (nullity_doubling_axis n b (by omega) hi).2.2
                  have hnot : ¬(0 < b ∧ b ≠ b) := by omega
                  simp only [hilt, ↓reduceIte]
                  rw [Nat.add_comm (2 ^ n) b]
                  simp only [hax, hnot, hb0, ↓reduceIte]; omega
                · have hcr := nullity_doubling_cross n i b (by omega) (by omega) (by omega) hi (by omega) (Ne.symm hbi)
                  have hposb : 0 < b := by omega
                  have hneib : i ≠ b := Ne.symm hbi
                  simp only [hilt, ↓reduceIte]
                  rw [Nat.add_comm (2 ^ n) b]
                  simp only [hcr, hposb, eq_true hneib, true_and, hb0, hbi, ↓reduceIte]; omega
          have hsingle : ∀ a, a < 2 ^ n → sumNat (fun b => if b = a then F 0 else 0) (2 ^ n) = F 0 := by
            intro a ha
            have h1 : ∀ m, sumNat (fun b => if b = a then F 0 else 0) m = if a < m then F 0 else 0 := by
              intro m; induction m with
              | zero => simp [sumNat]
              | succ m ihm =>
                unfold sumNat; rw [ihm]
                by_cases hma : m = a
                · subst hma; simp
                · by_cases hlt : a < m
                  · have hlt2 : a < m + 1 := by omega
                    simp only [hma, hlt, hlt2, ↓reduceIte, Nat.add_zero]
                  · have hlt2 : ¬(a < m + 1) := by omega
                    simp only [hma, hlt, hlt2, ↓reduceIte, Nat.add_zero]
            rw [h1 (2 ^ n)]; simp [ha]
          rw [hcomb (2 ^ n) (Nat.le_refl _), hsingle 0 hpos, hsingle i hi]; omega
        rw [hlo, hhi]; omega
    have hsum2 : sumNat (fun i => if i = 0 then 0 else 2 * F 0) (2 ^ n) = 2 * (2 ^ n - 1) * F 0 := by
      have h1 : ∀ m, sumNat (fun i => if i = 0 then 0 else 2 * F 0) m = (m - 1) * (2 * F 0) := by
        intro m; induction m with
        | zero => simp [sumNat]
        | succ m ihm =>
          unfold sumNat; rw [ihm]
          by_cases hm0 : m = 0
          · subst hm0; simp
          · simp only [hm0, ↓reduceIte, Nat.add_sub_cancel]
            have hm_eq : m = (m - 1) + 1 := by omega
            calc (m - 1) * (2 * F 0) + 2 * F 0
                = ((m - 1) + 1) * (2 * F 0) := (Nat.succ_mul (m - 1) (2 * F 0)).symm
              _ = m * (2 * F 0) := by rw [← hm_eq]
      rw [h1 (2 ^ n)]; rw [Nat.mul_comm 2 (2 ^ n - 1), Nat.mul_assoc]
    unfold sumOrderedOffDiag
    rw [sumNat_ext _ _ (2 ^ n) hrow, sumNat_pointwise_add, sumNat_pointwise_add, hsum2]
  -- Part 2: i = 2^n + a (a < 2^n)
  have hpart2 :
      sumNat (fun a => if 2 ^ n + a = 0 then 0 else sumNat (fun j => if 2 ^ n + a < j then F (twobladeNullity (n + 1) (2 ^ n + a) j) else 0) (2 ^ n + 2 ^ n)) (2 ^ n) =
      sumNat (fun a => if a = 0 then 0 else sumNat (fun b => if a < b then F (2 * twobladeNullity n a b) else 0) (2 ^ n)) (2 ^ n) +
      (2 ^ n - 1) * F 0 := by
    have hrow : ∀ a, a < 2 ^ n →
        (if 2 ^ n + a = 0 then 0 else sumNat (fun j => if 2 ^ n + a < j then F (twobladeNullity (n + 1) (2 ^ n + a) j) else 0) (2 ^ n + 2 ^ n)) =
        (if a = 0 then 0 else sumNat (fun b => if a < b then F (2 * twobladeNullity n a b) else 0) (2 ^ n)) +
        (if a = 0 then (2 ^ n - 1) * F 0 else 0) := by
      intro a ha
      have hne0 : 2 ^ n + a ≠ 0 := by omega
      simp only [hne0, ↓reduceIte]
      rw [sumNat_add]
      have hlo0 : sumNat (fun j => if 2 ^ n + a < j then F (twobladeNullity (n + 1) (2 ^ n + a) j) else 0) (2 ^ n) = 0 := by
        apply Eq.trans _ (sumNat_zero (2 ^ n))
        apply sumNat_ext; intro j hj
        have hnot : ¬(2 ^ n + a < j) := by omega
        simp only [hnot, ↓reduceIte]
      rw [hlo0, Nat.zero_add]
      by_cases ha0 : a = 0
      · subst ha0
        simp only [Nat.add_zero, ↓reduceIte, Nat.zero_add]
        have hax_sum : ∀ m, m ≤ 2 ^ n →
            sumNat (fun b => if 2 ^ n < 2 ^ n + b then F (twobladeNullity (n + 1) (2 ^ n) (2 ^ n + b)) else 0) m =
            (m - 1) * F 0 := by
          intro m hm
          induction m with
          | zero => simp [sumNat]
          | succ b ihb =>
            unfold sumNat; rw [ihb (by omega)]
            by_cases hb0 : b = 0
            · subst hb0; simp
            · have hlt : 2 ^ n < 2 ^ n + b := by omega
              have hax := (nullity_doubling_axis n b (by omega) (by omega)).1
              simp only [hlt, ↓reduceIte, Nat.add_sub_cancel]
              rw [Nat.add_comm (2 ^ n) b, hax]
              have hbeq : b = (b - 1) + 1 := by omega
              calc (b - 1) * F 0 + F 0
                  = ((b - 1) + 1) * F 0 := (Nat.succ_mul (b - 1) (F 0)).symm
                _ = b * F 0 := by rw [← hbeq]
        exact hax_sum (2 ^ n) (Nat.le_refl _)
      · simp only [ha0, ↓reduceIte, Nat.add_zero]
        apply sumNat_ext; intro b hb
        by_cases hab : a < b
        · have hab2 : 2 ^ n + a < 2 ^ n + b := by omega
          have hup := nullity_doubling_upper n a b (by omega) (by omega) ha hb (by omega)
          simp only [hab, hab2, ↓reduceIte]
          rw [Nat.add_comm (2 ^ n) a, Nat.add_comm (2 ^ n) b, hup]
        · have hab2 : ¬(2 ^ n + a < 2 ^ n + b) := by omega
          simp only [hab, hab2, ↓reduceIte]
    have hsingle0 : sumNat (fun a => if a = 0 then (2 ^ n - 1) * F 0 else 0) (2 ^ n) = (2 ^ n - 1) * F 0 := by
      have h1 : ∀ m, sumNat (fun a => if a = 0 then (2 ^ n - 1) * F 0 else 0) m =
          if 0 < m then (2 ^ n - 1) * F 0 else 0 := by
        intro m; induction m with
        | zero => simp [sumNat]
        | succ m ihm =>
          unfold sumNat; rw [ihm]
          by_cases hm0 : m = 0
          · subst hm0; simp
          · simp only [hm0, (by omega : 0 < m), (by omega : 0 < m + 1), ↓reduceIte, Nat.add_zero]
      rw [h1 (2 ^ n)]; simp [hpos]
    rw [sumNat_ext _ _ (2 ^ n) hrow, sumNat_pointwise_add, hsingle0]
  rw [hpart1, hpart2]
  have hsym : sumOrderedOffDiag (fun i b => F (2 ^ n - 4 - 2 * twobladeNullity n i b)) (2 ^ n) =
              2 * sumUnordered (fun i b => F (2 ^ n - 4 - 2 * twobladeNullity n i b)) (2 ^ n) := by
    apply sumOrderedOffDiag_symm
    intro i j _ _ _ _
    rw [twobladeNullity_symm]
  rw [hsym]
  unfold sumUnordered
  have h3f : 2 * (2 ^ n - 1) * F 0 + (2 ^ n - 1) * F 0 = 3 * (2 ^ n - 1) * F 0 := by
    have : 2 * (2 ^ n - 1) + (2 ^ n - 1) = 3 * (2 ^ n - 1) := by omega
    rw [← Nat.add_mul, this]
  let A := sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then F (2 * twobladeNullity n i j) else 0) (2 ^ n)) (2 ^ n)
  let B := 2 * sumNat (fun i => if i = 0 then 0 else sumNat (fun j => if i < j then F (2 ^ n - 4 - 2 * twobladeNullity n i j) else 0) (2 ^ n)) (2 ^ n)
  show (A + B + 2 * (2 ^ n - 1) * F 0) + (A + (2 ^ n - 1) * F 0) =
       2 * A + 3 * (2 ^ n - 1) * F 0 + B
  omega

/-! ### Theorem T2d: Exact All-$n$ Total 2-Blade Nullity Mass (via $+4M_n - 4M_n$ Cancellation!) -/

theorem count_unordered_pairs_formula (h : Nat) (hge : 1 ≤ h) :
    2 * sumUnordered (fun _ _ => 1) h = (h - 1) * (h - 2) := by
  unfold sumUnordered
  have hrow : ∀ i, i < h →
      (if i = 0 then 0 else sumNat (fun j => if i < j then 1 else 0) h) =
      if i = 0 then 0 else h - 1 - i := by
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · simp only [hi0, ↓reduceIte]
      have h1 : ∀ m, sumNat (fun j => if i < j then 1 else 0) m = if i < m then m - 1 - i else 0 := by
        intro m; induction m with
        | zero => simp [sumNat]
        | succ m ihm =>
          unfold sumNat; rw [ihm]
          by_cases him : i < m
          · have h2 : i < m + 1 := by omega
            simp [him, h2]; omega
          · by_cases h2 : i < m + 1
            · simp [him, h2]; omega
            · simp [him, h2]
      rw [h1 h]; simp [hi]
  rw [sumNat_ext _ _ h hrow]
  have htri : ∀ m, m ≤ h → 2 * sumNat (fun i => if i = 0 then 0 else h - 1 - i) m =
      if m = 0 then 0 else (m - 1) * (2 * h - 2 - m) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ihm =>
      unfold sumNat
      by_cases hm0 : m = 0
      · subst hm0; simp [sumNat]
      · have hih := ihm (by omega)
        simp only [hm0, ↓reduceIte] at hih ⊢
        have hsucc_ne : m + 1 ≠ 0 := by omega
        simp only [hsucc_ne, ↓reduceIte]
        have hstep : (m - 1) * (2 * h - 2 - m) + 2 * (h - 1 - m) = m * (2 * h - 2 - (m + 1)) := by
          have hm1 : m = (m - 1) + 1 := by omega
          have hd1 : 2 * h - 2 - m = (2 * h - 2 - (m + 1)) + 1 := by omega
          have hrhs : m * (2 * h - 2 - (m + 1)) = (m - 1) * (2 * h - 2 - (m + 1)) + (2 * h - 2 - (m + 1)) := by
            calc m * (2 * h - 2 - (m + 1))
                = ((m - 1) + 1) * (2 * h - 2 - (m + 1)) := by rw [← hm1]
              _ = (m - 1) * (2 * h - 2 - (m + 1)) + (2 * h - 2 - (m + 1)) := by rw [Nat.add_mul, Nat.one_mul]
          rw [hrhs, hd1, Nat.mul_add, Nat.mul_one]
          omega
        rw [Nat.mul_add, hih, Nat.add_sub_cancel, hstep]
  have := htri h (Nat.le_refl _)
  have hne : h ≠ 0 := by omega
  simp only [hne, ↓reduceIte] at this
  have hsub : 2 * h - 2 - h = h - 2 := by omega
  rw [hsub] at this
  exact this

/-- **Theorem T2d (Exact All-$n$ Total 2-Blade Nullity Mass via $+4M_n - 4M_n$ Cancellation):**
    For EVERY $n \ge 3$,
    $M_n = \sum_{1 \le i < j < 2^n} \nu_n^{\mathrm{std}}(i, j) = 8(2^{n-1} - 1)(2^{n-2} - 1)(2^{n-3} - 1)$. -/
theorem totalNullityMass_all_n (n : Nat) (hn : 3 ≤ n) :
    totalNullityMass n = 8 * (2 ^ (n - 1) - 1) * (2 ^ (n - 2) - 1) * (2 ^ (n - 3) - 1) := by
  by_cases hn3 : n = 3
  · subst hn3; exact octonion_mass_zero
  · let m := n - 1
    have hnm : n = m + 1 := by omega
    have hm3 : 3 ≤ m := by omega
    rw [hnm, totalNullityMass_eq_sumUnordered]
    have hdecomp := sumUnordered_nullity_doubling m hm3 id
    simp only [id] at hdecomp
    rw [hdecomp]
    -- 2 * sum(2 * nu) = 4 * M_m, axis term = 0, and cross term:
    -- 2 * sum(2^m - 4 - 2 * nu) + 4 * M_m = 2 * sum(2^m - 4) = (2^m - 1)*(2^m - 2)*(2^m - 4)!
    have hscale : sumUnordered (fun i j => 2 * twobladeNullity m i j) (2 ^ m) =
                  2 * sumUnordered (fun i j => twobladeNullity m i j) (2 ^ m) := by
      unfold sumUnordered
      rw [← sumNat_scale]
      apply sumNat_ext; intro i _
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceIte, ← sumNat_scale]
        apply sumNat_ext; intro j _
        by_cases hij : i < j <;> simp [hij]
    have hcancel :
        sumUnordered (fun i b => 2 ^ m - 4 - 2 * twobladeNullity m i b) (2 ^ m) +
        2 * sumUnordered (fun i b => twobladeNullity m i b) (2 ^ m) =
        (2 ^ m - 4) * sumUnordered (fun _ _ => 1) (2 ^ m) := by
      rw [← hscale]
      have hadd :
          sumUnordered (fun i b => 2 ^ m - 4 - 2 * twobladeNullity m i b) (2 ^ m) +
          sumUnordered (fun i b => 2 * twobladeNullity m i b) (2 ^ m) =
          sumUnordered (fun _ _ => 2 ^ m - 4) (2 ^ m) := by
        unfold sumUnordered
        rw [← sumNat_pointwise_add]
        apply sumNat_ext; intro i hi
        by_cases hi0 : i = 0
        · simp [hi0]
        · simp only [hi0, ↓reduceIte, ← sumNat_pointwise_add]
          apply sumNat_ext; intro b hb
          by_cases hib : i < b
          · simp only [hib, ↓reduceIte]
            have hle : 2 * twobladeNullity m i b ≤ 2 ^ m - 4 := by
              by_cases hm4 : m = 3
              · rw [hm4] at hi hb ⊢
                rw [octonion_nullity_all_zero i b (by omega) (by omega) hi hb (by omega)]; omega
              · have hbd := (nullity_mod4_and_bound m hm3 i b (by omega) (by omega) hi hb (by omega)).2 (by omega)
                have hp2 : 2 ^ m = 2 * 2 ^ (m - 1) := two_pow_mul_split m 1 (by omega)
                have hge4 : 4 ≤ 2 ^ (m - 1) := by
                  calc 4 = 2 ^ 2 := rfl
                    _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
                omega
            omega
          · simp [hib]
      rw [hadd]
      unfold sumUnordered
      rw [← sumNat_scale]
      apply sumNat_ext; intro i _
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceIte, ← sumNat_scale]
        apply sumNat_ext; intro b _
        by_cases hib : i < b <;> simp [hib]
    have hmass :
        2 * sumUnordered (fun i j => 2 * twobladeNullity m i j) (2 ^ m) +
        3 * (2 ^ m - 1) * 0 +
        2 * sumUnordered (fun i b => 2 ^ m - 4 - 2 * twobladeNullity m i b) (2 ^ m) =
        (2 ^ m - 4) * ((2 ^ m - 1) * (2 ^ m - 2)) := by
      have hpairs := count_unordered_pairs_formula (2 ^ m) (Nat.two_pow_pos m)
      have h2c : 2 * sumUnordered (fun i b => 2 ^ m - 4 - 2 * twobladeNullity m i b) (2 ^ m) +
                 4 * sumUnordered (fun i b => twobladeNullity m i b) (2 ^ m) =
                 (2 ^ m - 4) * (2 * sumUnordered (fun _ _ => 1) (2 ^ m)) := by
        have := congrArg (2 * ·) hcancel
        rw [Nat.mul_add] at this
        have hrot : 2 * ((2 ^ m - 4) * sumUnordered (fun _ _ => 1) (2 ^ m)) =
                    (2 ^ m - 4) * (2 * sumUnordered (fun _ _ => 1) (2 ^ m)) := by ac_rfl
        rw [hrot] at this; omega
      rw [hscale]
      rw [← hpairs]
      omega
    rw [hmass]
    -- Factor (2^m - 4)*(2^m - 1)*(2^m - 2) = 8*(2^m - 1)*(2^(m-1) - 1)*(2^(m-2) - 1)!
    have hp1 : 2 ^ m = 2 * 2 ^ (m - 1) := two_pow_mul_split m 1 (by omega)
    have hp2 : 2 ^ m = 4 * 2 ^ (m - 2) := two_pow_mul_split m 2 (by omega)
    have hf2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
      have : 1 ≤ 2 ^ (m - 1) := Nat.two_pow_pos (m - 1); omega
    have hf4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
      have : 1 ≤ 2 ^ (m - 2) := Nat.two_pow_pos (m - 2); omega
    have hs1 : m + 1 - 1 = m := by omega
    have hs2 : m + 1 - 2 = m - 1 := by omega
    have hs3 : m + 1 - 3 = m - 2 := by omega
    rw [hs1, hs2, hs3, hf2, hf4]
    -- Goal: 4*(2^(m-2)-1)*((2^m-1)*(2*(2^(m-1)-1))) = 8*(2^m-1)*(2^(m-1)-1)*(2^(m-2)-1)
    have h8 : (8 : Nat) = 4 * 2 := rfl
    rw [h8]; ac_rfl

/-! ### Theorems T2e & T2f: Exact Non-ZD Count, Interleaving, Palindrome, Top Jump & Midpoint 42 -/

/-- **Theorem T2e (Exact All-$n$ Zero-Divisor-Free 2-Blade Count):**
    For EVERY $n \ge 3$, $H_n^{\mathrm{std}}(0) = (6n - 9) 2^{n-2} + 3$. -/
theorem nonZDCount_all_n : ∀ n, 3 ≤ n → nullityHist n 0 = nonZDCountFormula n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn3 : n = 2
    · subst hn3; exact octonion_nonZD_21
    · have hn_ge3 : 3 ≤ n := by omega
      rw [nullityHist_eq_sumUnordered (n + 1) 0]
      have hdecomp := sumUnordered_nullity_doubling n hn_ge3 (fun x => if x = 0 then 1 else 0)
      rw [hdecomp]
      have h1 : sumUnordered (fun i j => if 2 * twobladeNullity n i j = 0 then 1 else 0) (2 ^ n) =
                nullityHist n 0 := by
        rw [nullityHist_eq_sumUnordered]
        apply sumUnordered_ext; intro i j _ _ _
        by_cases h : twobladeNullity n i j = 0
        · simp [h]
        · have hne : 2 * twobladeNullity n i j ≠ 0 := by omega
          simp only [h, hne, ↓reduceIte]
      have h2 : sumUnordered (fun i b => if 2 ^ n - 4 - 2 * twobladeNullity n i b = 0 then 1 else 0) (2 ^ n) = 0 := by
        have hz : sumUnordered (fun _ _ => 0) (2 ^ n) = 0 := by
          unfold sumUnordered
          apply Eq.trans _ (sumNat_zero (2 ^ n))
          apply sumNat_ext; intro i _; by_cases hi0 : i = 0 <;> simp [hi0, sumNat_zero]
        apply Eq.trans _ hz
        apply sumUnordered_ext; intro i b hi0 hib hb
        have hpos : 0 < 2 ^ n - 4 - 2 * twobladeNullity n i b := by
          by_cases hn4 : n = 3
          · subst hn4; rw [octonion_nullity_all_zero i b hi0 (by omega) (by omega) hb (by omega)]; omega
          · have hbd := (nullity_mod4_and_bound n hn_ge3 i b hi0 (by omega) (by omega) hb (by omega)).2 (by omega)
            have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
            have hge8 : 8 ≤ 2 ^ (n - 1) := by
              calc 8 = 2 ^ 3 := rfl
                _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
            omega
        have hne : 2 ^ n - 4 - 2 * twobladeNullity n i b ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
      rw [h1, h2, ih hn_ge3]
      simp only [↓reduceIte, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      unfold nonZDCountFormula
      have hp1 : 2 ^ n = 4 * 2 ^ (n - 2) := two_pow_mul_split n 2 (by omega)
      have hp2 : 2 ^ (n + 1 - 2) = 2 * 2 ^ (n - 2) := by
        have hsub : n + 1 - 2 = (n - 2) + 1 := by omega
        rw [hsub, Nat.pow_succ, Nat.mul_comm]
      rw [hp1, hp2]
      have hmul1 : 6 * (n + 1) - 9 = (6 * n - 9) + 6 := by omega
      rw [hmul1]
      have hX : 1 ≤ 2 ^ (n - 2) := Nat.two_pow_pos (n - 2)
      -- Goal: 2 * ((6n-9)*X + 3) + 3 * (4*X - 1) = ((6n-9)+6)*(2*X) + 3
      have hdist : ((6 * n - 9) + 6) * (2 * 2 ^ (n - 2)) =
                   2 * ((6 * n - 9) * 2 ^ (n - 2)) + 12 * 2 ^ (n - 2) := by
        rw [Nat.add_mul]
        have hA : (6 * n - 9) * (2 * 2 ^ (n - 2)) = 2 * ((6 * n - 9) * 2 ^ (n - 2)) := by ac_rfl
        have hB : 6 * (2 * 2 ^ (n - 2)) = 12 * 2 ^ (n - 2) := by omega
        rw [hA, hB]
      rw [hdist]; omega

/-- **Theorem T2f-1 (Exact Interleaving — Even Bins):**
    For EVERY $n \ge 3$ and EVERY $m \ge 1$, $H_{n+1}^{\mathrm{std}}(8m) = 2\,H_n^{\mathrm{std}}(4m)$. -/
theorem terrace_interleave_even (n m : Nat) (hn : 3 ≤ n) (hm : 1 ≤ m) :
    nullityHist (n + 1) (8 * m) = 2 * nullityHist n (4 * m) := by
  rw [nullityHist_eq_sumUnordered (n + 1) (8 * m)]
  have hdecomp := sumUnordered_nullity_doubling n hn (fun x => if x = 8 * m then 1 else 0)
  rw [hdecomp]
  have h1 : sumUnordered (fun i j => if 2 * twobladeNullity n i j = 8 * m then 1 else 0) (2 ^ n) =
            nullityHist n (4 * m) := by
    rw [nullityHist_eq_sumUnordered]
    apply sumUnordered_ext; intro i j _ _ _
    by_cases h : twobladeNullity n i j = 4 * m
    · have h2 : 2 * (4 * m) = 8 * m := by omega
      simp only [h, h2, ↓reduceIte]
    · have h2 : 2 * twobladeNullity n i j ≠ 8 * m := by omega
      simp only [h, h2, ↓reduceIte]
  have h2 : sumUnordered (fun i b => if 2 ^ n - 4 - 2 * twobladeNullity n i b = 8 * m then 1 else 0) (2 ^ n) = 0 := by
    have hz : sumUnordered (fun _ _ => 0) (2 ^ n) = 0 := by
      unfold sumUnordered
      apply Eq.trans _ (sumNat_zero (2 ^ n))
      apply sumNat_ext; intro i _; by_cases hi0 : i = 0 <;> simp [hi0, sumNat_zero]
    apply Eq.trans _ hz
    apply sumUnordered_ext; intro i b hi0 hib hb
    have ⟨⟨k, hk⟩, _⟩ := nullity_mod4_and_bound n hn i b hi0 (by omega) (by omega) hb (by omega)
    have h8pow : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 hn
    have hne : 2 ^ n - 4 - 2 * twobladeNullity n i b ≠ 8 * m := by omega
    simp only [hne, ↓reduceIte]
  have h0ne : (0 : Nat) ≠ 8 * m := by omega
  rw [h1, h2]; simp [h0ne]

/-- **Theorem T2f-2 (Exact Interleaving — Odd Bins):**
    For EVERY $n \ge 3$ and EVERY $m$ with $8m < 2^n - 4$,
    $H_{n+1}^{\mathrm{std}}(2^n - 4 - 8m) = 2\,H_n^{\mathrm{std}}(4m)$. -/
theorem terrace_interleave_odd (n m : Nat) (hn : 3 ≤ n) (hm : 8 * m < 2 ^ n - 4) :
    nullityHist (n + 1) (2 ^ n - 4 - 8 * m) = 2 * nullityHist n (4 * m) := by
  rw [nullityHist_eq_sumUnordered (n + 1) (2 ^ n - 4 - 8 * m)]
  have hdecomp := sumUnordered_nullity_doubling n hn (fun x => if x = 2 ^ n - 4 - 8 * m then 1 else 0)
  rw [hdecomp]
  have h8pow : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 hn
  have h1 : sumUnordered (fun i j => if 2 * twobladeNullity n i j = 2 ^ n - 4 - 8 * m then 1 else 0) (2 ^ n) = 0 := by
    have hz : sumUnordered (fun _ _ => 0) (2 ^ n) = 0 := by
      unfold sumUnordered
      apply Eq.trans _ (sumNat_zero (2 ^ n))
      apply sumNat_ext; intro i _; by_cases hi0 : i = 0 <;> simp [hi0, sumNat_zero]
    apply Eq.trans _ hz
    apply sumUnordered_ext; intro i j hi0 hij hj
    have ⟨⟨k, hk⟩, _⟩ := nullity_mod4_and_bound n hn i j hi0 (by omega) (by omega) hj (by omega)
    have hne : 2 * twobladeNullity n i j ≠ 2 ^ n - 4 - 8 * m := by omega
    simp only [hne, ↓reduceIte]
  have h2 : sumUnordered (fun i b => if 2 ^ n - 4 - 2 * twobladeNullity n i b = 2 ^ n - 4 - 8 * m then 1 else 0) (2 ^ n) =
            nullityHist n (4 * m) := by
    rw [nullityHist_eq_sumUnordered]
    apply sumUnordered_ext; intro i b hi0 hib hb
    have hle : 2 * twobladeNullity n i b ≤ 2 ^ n - 4 := by
      by_cases hn4 : n = 3
      · subst hn4; rw [octonion_nullity_all_zero i b hi0 (by omega) (by omega) hb (by omega)]; omega
      · have hbd := (nullity_mod4_and_bound n hn i b hi0 (by omega) (by omega) hb (by omega)).2 (by omega)
        have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
        have hge8 : 8 ≤ 2 ^ (n - 1) := by
          calc 8 = 2 ^ 3 := rfl
            _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
    by_cases h : twobladeNullity n i b = 4 * m
    · have h2 : 2 * (4 * m) = 8 * m := by omega
      simp only [h, h2, ↓reduceIte]
    · have h2 : 2 ^ n - 4 - 2 * twobladeNullity n i b ≠ 2 ^ n - 4 - 8 * m := by omega
      simp only [h, h2, ↓reduceIte]
  have h0ne : (0 : Nat) ≠ 2 ^ n - 4 - 8 * m := by omega
  rw [h1, h2]; simp [h0ne]

/-- **Theorem T2f-3 (Universal Exact Palindrome of the Interior Terrace):**
    For EVERY $n \ge 3$ and EVERY $k \ge 1$ with $4k < 2^n - 4$:
    $H_{n+1}^{\mathrm{std}}(4k) = H_{n+1}^{\mathrm{std}}(2^n - 4 - 4k)$. -/
theorem terrace_palindrome_all_n (n k : Nat) (hn : 3 ≤ n) (hk1 : 1 ≤ k) (hk2 : 4 * k < 2 ^ n - 4) :
    nullityHist (n + 1) (4 * k) = nullityHist (n + 1) (2 ^ n - 4 - 4 * k) := by
  by_cases heven : k % 2 = 0
  · let m := k / 2
    have h4k : 4 * k = 8 * m := by omega
    rw [h4k, terrace_interleave_even n m hn (by omega), terrace_interleave_odd n m hn (by omega)]
  · have h8pow : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 hn
    let m := (2 ^ n - 4 - 4 * k) / 8
    have h8m : 8 * m = 2 ^ n - 4 - 4 * k := by omega
    have h4k : 4 * k = 2 ^ n - 4 - 8 * m := by omega
    rw [← h8m, h4k, terrace_interleave_odd n m hn (by omega), terrace_interleave_even n m hn (by omega)]

/-- **Theorem T2f-4 (Universal Exact Top-Bin Formula & Top-Bin Jump):**
    For EVERY $n \ge 3$, $H_{n+1}^{\mathrm{std}}(2^n - 4) = 2\,H_n^{\mathrm{std}}(0)$,
    and for EVERY $n \ge 4$, $H_{n+1}^{\mathrm{std}}(2^n - 4) = H_{n+1}^{\mathrm{std}}(4) + 3(2^n - 2)$. -/
theorem terrace_top_bin_all_n (n : Nat) (hn : 3 ≤ n) :
    nullityHist (n + 1) (2 ^ n - 4) = 2 * nonZDCountFormula n := by
  have hpow : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hodd := terrace_interleave_odd n 0 hn (by omega)
  simp only [Nat.mul_zero, Nat.sub_zero] at hodd
  rw [hodd, nonZDCount_all_n n hn]

theorem terrace_top_jump_all_n (n : Nat) (hn : 4 ≤ n) :
    nullityHist (n + 1) (2 ^ n - 4) = nullityHist (n + 1) 4 + 3 * (2 ^ n - 2) := by
  have hpow : 16 ≤ 2 ^ n := by
    calc 16 = 2 ^ 4 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have htop := terrace_top_bin_all_n n (by omega)
  have hpal := terrace_palindrome_all_n n 1 (by omega) (by omega) (by omega)
  have hsub : 2 ^ n - 4 - 4 * 1 = 2 ^ n - 8 := by omega
  have h2n : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 (by omega)
  have hge2 : 2 ≤ 2 ^ (n - 3) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h8 : 2 ^ n - 8 = 8 * (2 ^ (n - 3) - 1) := by omega
  have h4_eq : nullityHist (n + 1) 4 = 2 * nullityHist n (2 ^ (n - 1) - 4) := by
    have hev := terrace_interleave_even n (2 ^ (n - 3) - 1) (by omega) (by omega)
    have hp : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
      have h1 := two_pow_mul_split (n - 1) 2 (by omega)
      have hs : n - 1 - 2 = n - 3 := by omega
      rw [hs] at h1; exact h1
    have h4m : 4 * (2 ^ (n - 3) - 1) = 2 ^ (n - 1) - 4 := by omega
    rw [h4m, ← h8, ← hsub] at hev
    simpa [Nat.mul_one] using hpal.trans hev
  have htop_prev := terrace_top_bin_all_n (n - 1) (by omega)
  have hnp : (n - 1) + 1 = n := by omega
  rw [hnp] at htop_prev
  rw [htop, h4_eq, htop_prev]
  unfold nonZDCountFormula
  have hp1 : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
    have h1 : n - 2 = (n - 3) + 1 := by omega
    rw [h1, Nat.pow_succ, Nat.mul_comm]
  have hp3 : n - 1 - 2 = n - 3 := by omega
  rw [hp1, h2n, hp3]
  have hmul : 6 * n - 9 = (6 * (n - 1) - 9) + 6 := by omega
  rw [hmul]
  have hdist : ((6 * (n - 1) - 9) + 6) * (2 * 2 ^ (n - 3)) =
               2 * ((6 * (n - 1) - 9) * 2 ^ (n - 3)) + 12 * 2 ^ (n - 3) := by
    rw [Nat.add_mul]
    have hA : (6 * (n - 1) - 9) * (2 * 2 ^ (n - 3)) = 2 * ((6 * (n - 1) - 9) * 2 ^ (n - 3)) := by ac_rfl
    have hB : 6 * (2 * 2 ^ (n - 3)) = 12 * 2 ^ (n - 3) := by omega
    rw [hA, hB]
  rw [hdist]; omega

/-- **Theorem T2f-5 (Crowning Pillar 1 + Pillar 2 Synthesis — Universal Split Midpoint 42 Law):**
    For EVERY $n \ge 4$ and EVERY signature $\gamma \in \{\pm 1\}^n$ (`flipMask`),
    $H_n^\gamma(2^{n-2}) = 42 \cdot 2^{n-4}$. -/
theorem terrace_midpoint_std_all_n :
    ∀ n, 4 ≤ n → nullityHist n (2 ^ (n - 2)) = 42 * 2 ^ (n - 4) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : n = 3
    · subst hn4; exact sedenion_hist_42
    · have hn_ge4 : 4 ≤ n := by omega
      have h8m : 2 ^ (n + 1 - 2) = 8 * 2 ^ (n - 4) := by
        have h1 := two_pow_mul_split (n + 1 - 2) 3 (by omega)
        have hs : n + 1 - 2 - 3 = n - 4 := by omega
        rw [hs] at h1; exact h1
      have h4m : 4 * 2 ^ (n - 4) = 2 ^ (n - 2) := by
        have h1 := two_pow_mul_split (n - 2) 2 (by omega)
        have hs : n - 2 - 2 = n - 4 := by omega
        rw [hs] at h1; exact h1.symm
      have hge1 : 1 ≤ 2 ^ (n - 4) := Nat.two_pow_pos (n - 4)
      rw [h8m, terrace_interleave_even n (2 ^ (n - 4)) (by omega) hge1, h4m, ih hn_ge4]
      have hp : 2 ^ (n + 1 - 4) = 2 * 2 ^ (n - 4) := by
        have h1 : n + 1 - 4 = (n - 4) + 1 := by omega
        rw [h1, Nat.pow_succ, Nat.mul_comm]
      rw [hp]; omega

theorem universal_split_midpoint_42 (n flipMask : Nat) (hn : 4 ≤ n) :
    nullityHistGamma n flipMask (2 ^ (n - 2)) = 42 * 2 ^ (n - 4) := by
  rw [midpoint_stratum_invariance n flipMask (by omega), terrace_midpoint_std_all_n n hn]

end

end CDTerrace
