module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import CDTerrace.Basic
public import CDTerrace.MirrorConservation
public import CDTerrace.TerraceLaw
public import CDTerrace.FiniteCertificates

/-!
# CDTerrace.SpectralGaps — Universal All-$n$ Gray-Code Bit-Locking & Spectral Band-Gap Classification

Proves three universal all-$n$ theorems extending Pillars I–II to the complete spectral-gap
structure of all $2^n$ generalized Cayley-Dickson signatures $\mathrm{CD}_n(\gamma)$:

- **T5a (`gray_code_bit_locking_all_n`):** For EVERY $n \ge 4$, EVERY $1 \le i < j < 2^n$ with
  Euclidean 2-blade nullity $v = \nu_n^{\mathrm{std}}(i, j) = 4m$, and EVERY depth
  $d \in \{0, \dots, n - 4\}$, bit $n - 1 - d$ of $i \oplus j$ is locked deterministically to the
  Binary Reflected Gray Code of $m = v / 4$ across the window $[2^{d+1},\; 2^{n-1} - 2^{d+1} - 4]$
  (and $[4, 2^{n-1} - 4]$ for $d = 0$).
- **T5b (`exponential_spectral_band_gap_all_n`):** Telescoping the Gray-code XOR sum proves the
  Dyadic-Quarter Parity Locking Law and yields an EXPONENTIALLY WIDE continuous interior spectral
  band gap at `flipMask = 2^n - 8` for EVERY $n \ge 6$:
  $H_n^{2^n - 8}(v) = 0$ for all $2^{n-2} < v < 3 \cdot 2^{n-3}$ (width $2^{n-3} - 1$ consecutive
  multiples of $4$), flanked by strictly populated edges
  $H_n^{2^n - 8}(2^{n-2}) = 42 \cdot 2^{n-4}$ and $H_n^{2^n - 8}(3 \cdot 2^{n-3}) > 0$.
- **T5c (`complete_spectral_gap_dichotomy_all_n`):** Complete all-$n$, all-signature if-and-only-if
  classification for EVERY $n \ge 6$ and EVERY $f < 2^n$:
  $\mathrm{CD}_n(f)$ exhibits an interior mod-4 spectral gap in $(0, 2^{n-1} - 4)$ IF AND ONLY IF
  $8 \mid f$ and $f \notin \{0, 8, 2^{n-1}, 2^{n-1} + 8\}$ — comprising exactly $2^{n-3} - 4$ out of
  all $2^n$ signatures.
-/

namespace CDTerrace

public section

/-! ### Core Definitions for Spectral-Gap Classification -/

/-- Existence of an interior multiple-of-4 spectral gap strictly inside $(0, 2^{n-1} - 4)$. -/
@[expose] def hasInteriorMod4Gap (n f : Nat) : Prop :=
  ∃ v, 4 ∣ v ∧ 0 < v ∧ v < 2 ^ (n - 1) - 4 ∧ nullityHistGamma n f v = 0

/-- Exact decidable classifier for gapped signatures at level $n \ge 6$:
    $8 \mid f$ and $f \notin \{0, 8, 2^{n-1}, 2^{n-1} + 8\}$ (at least one middle bit $4 \le b \le n - 2$ set). -/
@[expose] def isGappedMask (n f : Nat) : Bool :=
  (f % 8 == 0) && (f != 0) && (f != 8) && (f != 2 ^ (n - 1)) && (f != 2 ^ (n - 1) + 8)

/-- Gray-code bit function for depth $d$ applied to $m = v / 4$. -/
@[expose] def grayLockBit (d m : Nat) : Bool :=
  if d = 0 then m.testBit 0 else xor (m.testBit (d - 1)) (m.testBit d)

/-! ### Histogram Positivity & Vanishing Characterizations -/

theorem nullityHistRow_pos_iff (n f v i : Nat) :
    ∀ lim, 0 < nullityHistRow n f v i lim ↔
      ∃ j, i < j ∧ j < lim ∧ twobladeNullityGamma n f i j = v := by
  intro lim
  induction lim with
  | zero =>
    simp [nullityHistRow]
  | succ j ih =>
    unfold nullityHistRow
    constructor
    · intro hpos
      by_cases hcur : i < j ∧ twobladeNullityGamma n f i j = v
      · exact ⟨j, hcur.1, by omega, hcur.2⟩
      · have hcond : (i < j && twobladeNullityGamma n f i j == v) = false := by
          cases h1 : decide (i < j) <;> cases h2 : (twobladeNullityGamma n f i j == v) <;> simp_all
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hpos
        rcases ih.mp hpos with ⟨j', h1, h2, h3⟩
        exact ⟨j', h1, by omega, h3⟩
    · rintro ⟨j', h1, h2, h3⟩
      by_cases hjeq : j' = j
      · subst hjeq
        simp only [h1, h3, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        omega
      · have hprev : 0 < nullityHistRow n f v i j := ih.mpr ⟨j', h1, by omega, h3⟩
        split <;> omega

theorem nullityHistRange_pos_iff (n f v limJ : Nat) :
    ∀ limI, 0 < nullityHistRange n f v limI limJ ↔
      ∃ i j, 0 < i ∧ i < limI ∧ i < j ∧ j < limJ ∧ twobladeNullityGamma n f i j = v := by
  intro limI
  induction limI with
  | zero =>
    simp [nullityHistRange]
  | succ i ih =>
    unfold nullityHistRange
    constructor
    · intro hpos
      by_cases hi0 : i = 0
      · subst hi0
        simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero] at hpos
        rcases ih.mp hpos with ⟨i', j', h1, h2, h3, h4, h5⟩
        exact ⟨i', j', h1, by omega, h3, h4, h5⟩
      · have hib : (i == 0) = false := beq_false_of_ne hi0
        simp only [hib, Bool.false_eq_true, ↓reduceIte] at hpos
        by_cases hrow : 0 < nullityHistRow n f v i limJ
        · rcases (nullityHistRow_pos_iff n f v i limJ).mp hrow with ⟨j, h1, h2, h3⟩
          exact ⟨i, j, by omega, by omega, h1, h2, h3⟩
        · have hprev : 0 < nullityHistRange n f v i limJ := by omega
          rcases ih.mp hprev with ⟨i', j', h1, h2, h3, h4, h5⟩
          exact ⟨i', j', h1, by omega, h3, h4, h5⟩
    · rintro ⟨i', j', h1, h2, h3, h4, h5⟩
      by_cases hieq : i' = i
      · subst hieq
        have hib : (i' == 0) = false := beq_false_of_ne (by omega)
        simp only [hib, Bool.false_eq_true, ↓reduceIte]
        have hrow : 0 < nullityHistRow n f v i' limJ :=
          (nullityHistRow_pos_iff n f v i' limJ).mpr ⟨j', h3, h4, h5⟩
        omega
      · have hprev : 0 < nullityHistRange n f v i limJ :=
          ih.mpr ⟨i', j', h1, by omega, h3, h4, h5⟩
        split <;> omega

theorem nullityHistGamma_pos_iff (n f v : Nat) :
    0 < nullityHistGamma n f v ↔
      ∃ i j, 0 < i ∧ i < j ∧ j < 2 ^ n ∧ twobladeNullityGamma n f i j = v := by
  unfold nullityHistGamma
  rw [nullityHistRange_pos_iff]
  constructor
  · rintro ⟨i, j, h1, _, h3, h4, h5⟩; exact ⟨i, j, h1, h3, h4, h5⟩
  · rintro ⟨i, j, h1, h3, h4, h5⟩; exact ⟨i, j, h1, by omega, h3, h4, h5⟩

theorem nullityHistGamma_eq_zero_iff (n f v : Nat) :
    nullityHistGamma n f v = 0 ↔
      ∀ i j, 0 < i → i < j → j < 2 ^ n → twobladeNullityGamma n f i j ≠ v := by
  constructor
  · intro hz i j h1 h2 h3 heq
    have hpos : 0 < nullityHistGamma n f v :=
      (nullityHistGamma_pos_iff n f v).mpr ⟨i, j, h1, h2, h3, heq⟩
    omega
  · intro hall
    by_cases hz : nullityHistGamma n f v = 0
    · exact hz
    · rcases (nullityHistGamma_pos_iff n f v).mp (by omega) with ⟨i, j, h1, h2, h3, heq⟩
      exact absurd heq (hall i j h1 h2 h3)

/-! ### Bitwise & Parity Decomposition Helpers -/

theorem testBit_two_pow_sub_one_sub :
    ∀ k x j, x < 2 ^ k → j < k →
      (2 ^ k - 1 - x).testBit j = !(x.testBit j) := by
  intro k
  induction k with
  | zero => intro _ j _ hj; omega
  | succ k ih =>
    intro x j hx hj
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmod_eq : (2 ^ (k + 1) - 1 - x) % 2 = 1 - x % 2 := by omega
    have hdiv_eq : (2 ^ (k + 1) - 1 - x) / 2 = 2 ^ k - 1 - x / 2 := by omega
    cases j with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero, hmod_eq]
      cases Nat.mod_two_eq_zero_or_one x with
      | inl h0 => simp [h0]
      | inr h1 => simp [h1]
    | succ j' =>
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv_eq]
      exact ih (x / 2) j' (by omega) (by omega)

theorem testBit_mul_two (m k : Nat) :
    (2 * m).testBit (k + 1) = m.testBit k := by
  rw [Nat.testBit_succ]
  have h : (2 * m) / 2 = m := by omega
  rw [h]

theorem testBit_mul_two_zero (m : Nat) :
    (2 * m).testBit 0 = false := by
  simp [Nat.testBit_zero]

theorem testBit_zero_false_of_mod8 (f r : Nat) (hf8 : f % 8 = 0) (hr : r < 3) :
    f.testBit r = false := by
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [Nat.testBit_zero]; simp [show f % 2 = 0 by omega]
  · rw [Nat.testBit_succ, Nat.testBit_zero]; simp [show (f / 2) % 2 = 0 by omega]
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_zero]; simp [show (f / 2 / 2) % 2 = 0 by omega]

theorem parityBits_mod_two_pow :
    ∀ k m, parityBits k (m % 2 ^ k) = parityBits k m := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro m
    unfold parityBits
    have h2 : 2 ∣ 2 ^ (k + 1) := ⟨2 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have hm2 : (m % 2 ^ (k + 1)) % 2 = m % 2 := Nat.mod_mod_of_dvd m h2
    have hmd : (m % 2 ^ (k + 1)) / 2 = (m / 2) % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.mod_mul_right_div_self m 2 (2 ^ k)
    rw [hm2, hmd, ih (m / 2)]

theorem parityBits_succ_high (k m : Nat) :
    parityBits (k + 1) m = xor (parityBits k m) (m.testBit k) := by
  rw [parityBits_split, parityBits_mod_two_pow]
  have hbit : ((m / 2 ^ k) % 2 == 1) = m.testBit k := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
    cases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) <;> simp [*]
  rw [hbit]

theorem parityBits_congr_bits :
    ∀ k a b, (∀ j, j < k → a.testBit j = b.testBit j) →
      parityBits k a = parityBits k b := by
  intro k
  induction k with
  | zero => intro _ _ _; rfl
  | succ k ih =>
    intro a b h
    rw [parityBits_succ_high, parityBits_succ_high,
        ih a b (fun j hj => h j (by omega)), h k (by omega)]

theorem parityBits_and_mask_eq_xor (k x f1 f2 : Nat) :
    parityBits k (x &&& (f1 ^^^ f2)) = xor (parityBits k (x &&& f1)) (parityBits k (x &&& f2)) := by
  have hdist : x &&& (f1 ^^^ f2) = (x &&& f1) ^^^ (x &&& f2) := by
    apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases x.testBit j <;> cases f1.testBit j <;> cases f2.testBit j <;> rfl
  rw [hdist, parityBits_xor]

theorem testBit_two_pow_sub_eight (n k : Nat) (hn : 3 ≤ n) (hk : k < n) :
    (2 ^ n - 8).testBit k = decide (3 ≤ k) := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have heq : 2 ^ n - 8 = 2 ^ n - 1 - 7 := by omega
  rw [heq, testBit_two_pow_sub_one_sub n 7 k (by omega) hk]
  by_cases h3 : k < 3
  · have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · have hlt : 7 < 2 ^ k := by
      calc 7 < 8 := by omega
        _ = 2 ^ 3 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow hlt]
    have hge : 3 ≤ k := by omega
    simp [hge]

/-! ### Theorem T5a: Universal Binary Reflected Gray-Code Bit-Locking Law -/

theorem sedenion_nullity4_cross_bit3 (i j : Nat)
    (hi0 : 0 < i) (hij : i < j) (hj : j < 16)
    (hnu : twobladeNullity 4 i j = 4) :
    (i ^^^ j).testBit 3 = true := by
  by_cases hih : i < 8
  · by_cases hjh : j < 8
    · have h0 := nullity_doubling_lower 3 i j hi0 (by omega) hih hjh (by omega)
      have hoct := octonion_nullity_all_zero i j hi0 (by omega) hih hjh (by omega)
      rw [hoct] at h0
      rw [h0] at hnu
      omega
    · let b := j - 8
      have hjb : j = b + 2 ^ 3 := by omega
      have hblt : b < 2 ^ 3 := by omega
      have hih3 : i < 2 ^ 3 := hih
      rw [hjb, xor_add_right hih3 hblt, testBit_add_pow2_lt 3 (i ^^^ b) 3 (Nat.xor_lt_two_pow hih3 hblt)]
      simp
  · let a := i - 8
    let b := j - 8
    have hia : i = a + 8 := by omega
    have hjb : j = b + 8 := by omega
    have halt : a < 8 := by omega
    have hblt : b < 8 := by omega
    by_cases ha0 : a = 0
    · have hi8 : i = 8 := by omega
      rw [hi8, hjb] at hnu
      have hax := (nullity_doubling_axis 3 b (by omega) hblt).1
      rw [hax] at hnu
      omega
    · rw [hia, hjb] at hnu
      have hup := nullity_doubling_upper 3 a b (by omega) (by omega) halt hblt (by omega)
      have hoct := octonion_nullity_all_zero a b (by omega) (by omega) halt hblt (by omega)
      rw [hoct] at hup
      rw [hup] at hnu
      omega

/-- **Theorem T5a (Universal Binary Reflected Gray-Code Bit-Locking Law):**
    For EVERY $n \ge 4$, EVERY $1 \le i < j < 2^n$ with Euclidean 2-blade nullity
    $v = \nu_n^{\mathrm{std}}(i, j) = 4m$, and EVERY depth $d \in \{0, \dots, n - 4\}$:
    - At $d = 0$ ($4 \le v \le 2^{n-1} - 4$): $\mathrm{bit}_{n-1}(i \oplus j) = \mathrm{bit}_0(m)$.
    - At $1 \le d \le n - 4$ ($2^{d+1} \le v \le 2^{n-1} - 2^{d+1} - 4$):
      $\mathrm{bit}_{n-1-d}(i \oplus j) = \mathrm{bit}_{d-1}(m) \oplus \mathrm{bit}_d(m)$
      (bit $d - 1$ of the Binary Reflected Gray Code of $m = v / 4$). -/
theorem gray_code_bit_locking_all_n :
    ∀ n, 4 ≤ n → ∀ i j, 0 < i → i < j → j < 2 ^ n →
      let v := twobladeNullity n i j
      let m := v / 4
      ((4 ≤ v → v ≤ 2 ^ (n - 1) - 4 →
          (i ^^^ j).testBit (n - 1) = m.testBit 0) ∧
       (∀ d, 1 ≤ d → d ≤ n - 4 →
          2 ^ (d + 1) ≤ v → v ≤ 2 ^ (n - 1) - 2 ^ (d + 1) - 4 →
          (i ^^^ j).testBit (n - 1 - d) = xor (m.testBit (d - 1)) (m.testBit d))) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : n = 3
    · subst hn4
      intro i j hi0 hij hj
      refine ⟨?_, ?_⟩
      · intro hvlo hvhi
        have hvlo4 : 4 ≤ twobladeNullity 4 i j := hvlo
        have hvhi4 : twobladeNullity 4 i j ≤ 4 := hvhi
        have hv4 : twobladeNullity 4 i j = 4 := by omega
        have hm1 : twobladeNullity 4 i j / 4 = 1 := by omega
        rw [hm1]
        exact sedenion_nullity4_cross_bit3 i j hi0 hij hj hv4
      · intro d hd1 hd0; omega
    · have hn_ge4 : 4 ≤ n := by omega
      have hih := ih hn_ge4
      have h2n_ge16 : 16 ≤ 2 ^ n := by
        calc 16 = 2 ^ 4 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_ge4
      have h2n1 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
      have h2n2 : 2 ^ n = 4 * 2 ^ (n - 2) := two_pow_mul_split n 2 (by omega)
      have h2n3 : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 (by omega)
      have hsame : ∀ a b, 0 < a → a < b → b < 2 ^ n →
          let v := 2 * twobladeNullity n a b
          let m := v / 4
          ((4 ≤ v → v ≤ 2 ^ n - 4 → (a ^^^ b).testBit n = m.testBit 0) ∧
           (∀ d, 1 ≤ d → d ≤ n - 3 →
              2 ^ (d + 1) ≤ v → v ≤ 2 ^ n - 2 ^ (d + 1) - 4 →
              (a ^^^ b).testBit (n - d) = xor (m.testBit (d - 1)) (m.testBit d))) := by
        intro a b ha0 hab hb
        have ⟨⟨mp, hmp⟩, hbd⟩ := nullity_mod4_and_bound n (by omega) a b ha0 (by omega) (by omega) hb (by omega)
        have hbdn := hbd hn_ge4
        have hm_eq : (2 * twobladeNullity n a b) / 4 = 2 * mp := by omega
        have hmp_eq : twobladeNullity n a b / 4 = mp := by omega
        refine ⟨?_, ?_⟩
        · intro _ _
          rw [hm_eq, testBit_mul_two_zero, Nat.testBit_lt_two_pow (Nat.xor_lt_two_pow (by omega) hb)]
        · intro d hd1 hdn hvlo hvhi
          rw [hm_eq]
          by_cases hd_eq1 : d = 1
          · subst hd_eq1
            rw [testBit_mul_two_zero, testBit_mul_two mp 0, Bool.false_xor]
            have hstep := (hih a b ha0 hab hb).1 (by omega) hbdn
            simpa [hmp_eq] using hstep
          · have hd2 : 2 ≤ d := by omega
            have htb1 : (2 * mp).testBit (d - 1) = mp.testBit (d - 2) :=
              (congrArg ((2 * mp).testBit) (by omega : d - 1 = (d - 2) + 1)).trans (testBit_mul_two mp (d - 2))
            have htb2 : (2 * mp).testBit d = mp.testBit (d - 1) :=
              (congrArg ((2 * mp).testBit) (by omega : d = (d - 1) + 1)).trans (testBit_mul_two mp (d - 1))
            rw [htb1, htb2]
            have hpowd : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
            have h4dvd_d : 4 ∣ 2 ^ d := ⟨2 ^ (d - 2), two_pow_mul_split d 2 hd2⟩
            have h4dvd_n1 : 4 ∣ 2 ^ (n - 1) := ⟨2 ^ (n - 3), by
              have h := two_pow_mul_split (n - 1) 2 (by omega)
              have hs : n - 1 - 2 = n - 3 := by omega
              rw [hs] at h; exact h⟩
            rcases h4dvd_d with ⟨qd, hqd⟩
            rcases h4dvd_n1 with ⟨qn, hqn⟩
            have hvlo_prev : 2 ^ d ≤ twobladeNullity n a b := by omega
            have hvhi_prev : twobladeNullity n a b ≤ 2 ^ (n - 1) - 2 ^ d - 4 := by omega
            have hstep := (hih a b ha0 hab hb).2 (d - 1) (by omega) (by omega)
              (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hvlo_prev)
              (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hvhi_prev)
            have hidx : n - d = n - 1 - (d - 1) := by omega
            have hidx2 : d - 1 - 1 = d - 2 := by omega
            rw [hidx, ← hmp_eq]
            simpa [hidx2] using hstep
      intro i j hi0 hij hj
      have h2np1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      by_cases hih_lt : i < 2 ^ n
      · by_cases hjh_lt : j < 2 ^ n
        · have hnu := nullity_doubling_lower n i j hi0 (by omega) hih_lt hjh_lt (by omega)
          simpa [hnu] using hsame i j hi0 hij hjh_lt
        · let b := j - 2 ^ n
          have hjb : j = b + 2 ^ n := by omega
          have hblt : b < 2 ^ n := by omega
          by_cases hb0 : b = 0
          · have hjpow : j = 2 ^ n := by omega
            have hax := (nullity_doubling_axis n i hi0 hih_lt).2.1
            rw [hjpow, hax]
            refine ⟨fun h => by omega, fun d hd1 _ h => ?_⟩
            have : 4 ≤ 2 ^ (d + 1) := by
              calc 4 = 2 ^ 2 := rfl
                _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
            omega
          · by_cases hbi : b = i
            · have hji : j = i + 2 ^ n := by omega
              have hax := (nullity_doubling_axis n i hi0 hih_lt).2.2
              rw [hji, hax]
              refine ⟨fun h => by omega, fun d hd1 _ h => ?_⟩
              have : 4 ≤ 2 ^ (d + 1) := by
                calc 4 = 2 ^ 2 := rfl
                  _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
              omega
            · have hnu : twobladeNullity (n + 1) i j = 2 ^ n - 4 - 2 * twobladeNullity n i b := by
                rw [hjb]; exact nullity_doubling_cross n i b (by omega) hi0 (by omega) hih_lt hblt (by omega)
              have hxor : i ^^^ j = (i ^^^ b) + 2 ^ n := by rw [hjb, xor_add_right hih_lt hblt]
              have hxlt : i ^^^ b < 2 ^ n := Nat.xor_lt_two_pow hih_lt hblt
              have ⟨⟨mp, hmp⟩, hbd⟩ := nullity_mod4_and_bound n (by omega) i b hi0 (by omega) hih_lt hblt (by omega)
              have hbdn := hbd hn_ge4
              have h2mp_lt : 2 * mp < 2 ^ (n - 2) := by omega
              have hm_eq : twobladeNullity (n + 1) i j / 4 = 2 ^ (n - 2) - 1 - 2 * mp := by omega
              have hmp_eq : twobladeNullity n i b / 4 = mp := by omega
              have hih_sym :
                  ((4 ≤ twobladeNullity n i b → twobladeNullity n i b ≤ 2 ^ (n - 1) - 4 →
                      (i ^^^ b).testBit (n - 1) = mp.testBit 0) ∧
                   (∀ d, 1 ≤ d → d ≤ n - 4 →
                      2 ^ (d + 1) ≤ twobladeNullity n i b →
                      twobladeNullity n i b ≤ 2 ^ (n - 1) - 2 ^ (d + 1) - 4 →
                      (i ^^^ b).testBit (n - 1 - d) = xor (mp.testBit (d - 1)) (mp.testBit d))) := by
                by_cases hib_lt : i < b
                · simpa [hmp_eq] using hih i b hi0 hib_lt hblt
                · have hbi_lt : b < i := by omega
                  have hsym_nu := twobladeNullity_symm n b i
                  have hsym_xor : b ^^^ i = i ^^^ b := Nat.xor_comm b i
                  simpa [hsym_nu, hsym_xor, hmp_eq] using hih b i (by omega) hbi_lt hih_lt
              refine ⟨?_, ?_⟩
              · intro _ _
                have hn1 : n + 1 - 1 = n := by omega
                rw [hn1, hxor, testBit_add_pow2_lt n (i ^^^ b) n hxlt]
                simp only [↓reduceIte]
                rw [hm_eq, testBit_two_pow_sub_one_sub (n - 2) (2 * mp) 0 h2mp_lt (by omega),
                    testBit_mul_two_zero]
                rfl
              · intro d hd1 hdn hvlo hvhi
                have hnp1 : 2 ^ (n + 1 - 1) = 2 ^ n := rfl
                rw [hnp1] at hvhi
                have hn1d : n + 1 - 1 - d = n - d := by omega
                have hnd_lt : n - d ≠ n := by omega
                rw [hn1d, hxor, testBit_add_pow2_lt n (i ^^^ b) (n - d) hxlt]
                simp only [hnd_lt, ↓reduceIte, hm_eq]
                have hd_lt : d < n - 2 := by omega
                rw [testBit_two_pow_sub_one_sub (n - 2) (2 * mp) (d - 1) h2mp_lt (by omega),
                    testBit_two_pow_sub_one_sub (n - 2) (2 * mp) d h2mp_lt hd_lt]
                have hnot_xor : ∀ x y : Bool, xor (!x) (!y) = xor x y := by
                  intro x y; cases x <;> cases y <;> rfl
                rw [hnot_xor]
                by_cases hd_eq1 : d = 1
                · subst hd_eq1
                  rw [testBit_mul_two_zero, testBit_mul_two mp 0, Bool.false_xor]
                  exact hih_sym.1 (by omega) hbdn
                · have hd2 : 2 ≤ d := by omega
                  have htb1 : (2 * mp).testBit (d - 1) = mp.testBit (d - 2) :=
                    (congrArg ((2 * mp).testBit) (by omega : d - 1 = (d - 2) + 1)).trans (testBit_mul_two mp (d - 2))
                  have htb2 : (2 * mp).testBit d = mp.testBit (d - 1) :=
                    (congrArg ((2 * mp).testBit) (by omega : d = (d - 1) + 1)).trans (testBit_mul_two mp (d - 1))
                  rw [htb1, htb2]
                  have hpowd : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
                  have h4dvd_d : 4 ∣ 2 ^ d := ⟨2 ^ (d - 2), two_pow_mul_split d 2 hd2⟩
                  have h4dvd_n1 : 4 ∣ 2 ^ (n - 1) := ⟨2 ^ (n - 3), by
                    have h := two_pow_mul_split (n - 1) 2 (by omega)
                    have hs : n - 1 - 2 = n - 3 := by omega
                    rw [hs] at h; exact h⟩
                  rcases h4dvd_d with ⟨qd, hqd⟩
                  rcases h4dvd_n1 with ⟨qn, hqn⟩
                  have hvlo_prev : 2 ^ d ≤ twobladeNullity n i b := by omega
                  have hvhi_prev : twobladeNullity n i b ≤ 2 ^ (n - 1) - 2 ^ d - 4 := by omega
                  have hstep := hih_sym.2 (d - 1) (by omega) (by omega)
                    (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hvlo_prev)
                    (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hvhi_prev)
                  have hidx : n - d = n - 1 - (d - 1) := by omega
                  have hidx2 : d - 1 - 1 = d - 2 := by omega
                  rw [hidx]
                  simpa [hidx2] using hstep
      · let a := i - 2 ^ n
        let b := j - 2 ^ n
        have hia : i = a + 2 ^ n := by omega
        have hjb : j = b + 2 ^ n := by omega
        have halt : a < 2 ^ n := by omega
        have hblt : b < 2 ^ n := by omega
        by_cases ha0 : a = 0
        · have hipow : i = 2 ^ n := by omega
          have hax := (nullity_doubling_axis n b (by omega) hblt).1
          rw [hipow, hjb, hax]
          refine ⟨fun h => by omega, fun d hd1 _ h => ?_⟩
          have : 4 ≤ 2 ^ (d + 1) := by
            calc 4 = 2 ^ 2 := rfl
              _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        · have hnu : twobladeNullity (n + 1) i j = 2 * twobladeNullity n a b := by
            rw [hia, hjb]; exact nullity_doubling_upper n a b (by omega) (by omega) halt hblt (by omega)
          have hxor : i ^^^ j = a ^^^ b := by rw [hia, hjb, xor_add_both halt hblt]
          rw [hnu, hxor]
          exact hsame a b (by omega) (by omega) hblt

/-! ### Theorem T5b: Telescoping Quarter Parity & Exponential Continuous Band Gap -/

theorem testBit_two_pow_sub_two_pow (n t j : Nat) (ht : t ≤ n) :
    (2 ^ n - 2 ^ t).testBit j = decide (t ≤ j ∧ j < n) := by
  have hpos_t : 0 < 2 ^ t := Nat.two_pow_pos t
  by_cases hjn : j < n
  · have h2t : 2 ^ t ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) ht
    have h1 : 2 ^ n - 2 ^ t = 2 ^ n - 1 - (2 ^ t - 1) := by omega
    rw [h1, testBit_two_pow_sub_one_sub n (2 ^ t - 1) j (by omega) hjn]
    by_cases hjt : j < t
    · have hones : (2 ^ t - 1).testBit j = true := by
        have := testBit_two_pow_sub_one_sub t 0 j hpos_t hjt
        simpa using this
      rw [hones]
      have hnt : ¬(t ≤ j ∧ j < n) := by omega
      simp [hnt]
    · have hlt : 2 ^ t - 1 < 2 ^ j := by
        have hle : 2 ^ t ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      rw [Nat.testBit_lt_two_pow hlt]
      have hok : t ≤ j ∧ j < n := by omega
      simp [hok]
  · have hlt : 2 ^ n - 2 ^ t < 2 ^ j := by
      have hpos_j : 0 < 2 ^ j := Nat.two_pow_pos j
      have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.testBit_lt_two_pow hlt]
    have hnt : ¬(t ≤ j ∧ j < n) := by omega
    simp [hnt]

theorem parityBits_single_pow2 (n b x : Nat) (hb : b < n) :
    parityBits n (x &&& 2 ^ b) = x.testBit b := by
  have htb : ∀ j, (x &&& 2 ^ b).testBit j = if j = b then x.testBit b else false := by
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hje : j = b
    · subst hje; simp
    · have hne : ¬(b = j) := Ne.symm hje
      simp [hje, hne]
  have hgen : ∀ r, r ≤ n → parityBits r (x &&& 2 ^ b) = if b < r then x.testBit b else false := by
    intro r hr
    induction r with
    | zero => simp [parityBits]
    | succ r ihr =>
      rw [parityBits_succ_high, ihr (by omega), htb r]
      by_cases hrb : r = b
      · subst hrb
        have hlt1 : ¬(r < r) := by omega
        have hlt2 : r < r + 1 := by omega
        simp [hlt1, hlt2]
      · by_cases hlt : b < r
        · have hlt2 : b < r + 1 := by omega
          simp [hrb, hlt, hlt2]
        · have hlt2 : ¬(b < r + 1) := by omega
          simp [hrb, hlt, hlt2]
  simpa [hb] using hgen n (Nat.le_refl n)

theorem gray_xor_telescope (n m : Nat) (hn : 4 ≤ n) (x : Nat)
    (h0 : x.testBit (n - 1) = m.testBit 0)
    (hstep : ∀ d, 1 ≤ d → d ≤ n - 4 →
      x.testBit (n - 1 - d) = xor (m.testBit (d - 1)) (m.testBit d)) :
    ∀ k, 1 ≤ k → k ≤ n - 3 →
      parityBits n (x &&& (2 ^ n - 2 ^ (n - k))) = m.testBit (k - 1) := by
  intro k hk1 hkn
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      have hmask : 2 ^ n - 2 ^ (n - 1) = 2 ^ (n - 1) := by
        have h2 := two_pow_mul_split n 1 (by omega)
        omega
      rw [hmask, parityBits_single_pow2 n (n - 1) x (by omega), h0]
    · have hk1' : 1 ≤ k := by omega
      have hprev := ih hk1' (by omega)
      have hmask_xor : 2 ^ n - 2 ^ (n - (k + 1)) =
          (2 ^ n - 2 ^ (n - k)) ^^^ (2 ^ (n - (k + 1))) := by
        apply Nat.eq_of_testBit_eq; intro j
        rw [Nat.testBit_xor, Nat.testBit_two_pow,
            testBit_two_pow_sub_two_pow n (n - (k + 1)) j (by omega),
            testBit_two_pow_sub_two_pow n (n - k) j (by omega)]
        by_cases hje : j = n - (k + 1)
        · subst hje
          have h1 : decide (n - (k + 1) ≤ n - (k + 1) ∧ n - (k + 1) < n) = true := decide_eq_true (by omega)
          have h2 : decide (n - k ≤ n - (k + 1) ∧ n - (k + 1) < n) = false := decide_eq_false (by omega)
          have h3 : decide (n - (k + 1) = n - (k + 1)) = true := decide_eq_true rfl
          rw [h1, h2, h3]; rfl
        · have h3 : decide (n - (k + 1) = j) = false := decide_eq_false (Ne.symm hje)
          rw [h3, Bool.xor_false]
          by_cases hcond : n - k ≤ j ∧ j < n
          · rw [decide_eq_true hcond, decide_eq_true (by omega : n - (k + 1) ≤ j ∧ j < n)]
          · rw [decide_eq_false hcond, decide_eq_false (by omega : ¬(n - (k + 1) ≤ j ∧ j < n))]
      rw [hmask_xor, parityBits_and_mask_eq_xor, hprev,
          parityBits_single_pow2 n (n - (k + 1)) x (by omega)]
      have hstep_k := hstep k hk1' (by omega)
      have hidx : n - (k + 1) = n - 1 - k := by omega
      have hidx2 : k + 1 - 1 = k := by omega
      rw [hidx, hidx2, hstep_k]
      cases m.testBit (k - 1) <;> cases m.testBit k <;> rfl

/-- **Quarter Parity Locking Corollary:** For $n \ge 4$ and $1 \le i < j < 2^n$ with
    $v = \nu_n^{\mathrm{std}}(i, j)$, at `flipMask = 2^n - 8`:
    - $2^{n-3} \le v < 2^{n-2} \implies \mathrm{parity}_n((i \oplus j) \,\&\, (2^n - 8)) = \mathrm{false}$,
    - $2^{n-2} \le v < 3 \cdot 2^{n-3} \implies \mathrm{parity}_n((i \oplus j) \,\&\, (2^n - 8)) = \mathrm{true}$. -/
theorem quarter_parity_locking_all_n (n i j : Nat) (hn : 4 ≤ n)
    (hi0 : 0 < i) (hij : i < j) (hj : j < 2 ^ n) :
    let v := twobladeNullity n i j
    (2 ^ (n - 3) ≤ v → v < 2 ^ (n - 2) →
      parityBits n ((i ^^^ j) &&& (2 ^ n - 8)) = false) ∧
    (2 ^ (n - 2) ≤ v → v < 3 * 2 ^ (n - 3) →
      parityBits n ((i ^^^ j) &&& (2 ^ n - 8)) = true) := by
  have ⟨h0, hstep⟩ := gray_code_bit_locking_all_n n hn i j hi0 hij hj
  have ⟨⟨m, hm⟩, hbd⟩ := nullity_mod4_and_bound n (by omega) i j hi0 (by omega) (by omega) hj (by omega)
  have hbdn := hbd hn
  have hm_eq : twobladeNullity n i j / 4 = m := by omega
  have hpow3 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 1) 2 (by omega)
    have hs : n - 1 - 2 = n - 3 := by omega
    rw [hs] at h; exact h
  have hpow2 : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 2) 1 (by omega)
    have hs : n - 2 - 1 = n - 3 := by omega
    rw [hs] at h; exact h
  have htel : 2 ^ (n - 3) ≤ twobladeNullity n i j →
      twobladeNullity n i j ≤ 3 * 2 ^ (n - 3) - 4 →
      parityBits n ((i ^^^ j) &&& (2 ^ n - 8)) = m.testBit (n - 4) := by
    intro hvlo hvhi
    have hlo4 : 4 ≤ twobladeNullity n i j := by
      have : 2 ≤ 2 ^ (n - 3) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h0' : (i ^^^ j).testBit (n - 1) = m.testBit 0 := by
      rw [← hm_eq]; exact h0 hlo4 hbdn
    have hstep' : ∀ d, 1 ≤ d → d ≤ n - 4 →
        (i ^^^ j).testBit (n - 1 - d) = xor (m.testBit (d - 1)) (m.testBit d) := by
      intro d hd1 hdn
      have hpowd : 2 ^ (d + 1) ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [← hm_eq]
      exact hstep d hd1 hdn (by omega) (by omega)
    have h := gray_xor_telescope n m hn (i ^^^ j) h0' hstep' (n - 3) (by omega) (Nat.le_refl _)
    have hsub1 : n - (n - 3) = 3 := by omega
    have hsub2 : n - 3 - 1 = n - 4 := by omega
    rw [hsub1, hsub2] at h
    exact h
  have h2n4 : 2 ^ (n - 3) = 2 * 2 ^ (n - 4) := by
    have h := two_pow_mul_split (n - 3) 1 (by omega)
    have hs : n - 3 - 1 = n - 4 := by omega
    rw [hs] at h; exact h
  have hpos : 0 < 2 ^ (n - 4) := Nat.two_pow_pos (n - 4)
  refine ⟨?_, ?_⟩
  · intro hvlo hvhi
    have hhi : twobladeNullity n i j ≤ 3 * 2 ^ (n - 3) - 4 := by omega
    rw [htel hvlo hhi]
    have hm_lt : m < 2 ^ (n - 4) := by omega
    exact Nat.testBit_lt_two_pow hm_lt
  · intro hvlo hvhi
    by_cases hn4 : n = 4
    · subst hn4
      have hv4 : twobladeNullity 4 i j = 4 := by omega
      have hb3 := sedenion_nullity4_cross_bit3 i j hi0 hij hj hv4
      rw [show (2 ^ 4 - 8 : Nat) = 2 ^ 3 from rfl, parityBits_single_pow2 4 3 _ (by omega), hb3]
    · have hhi : twobladeNullity n i j ≤ 3 * 2 ^ (n - 3) - 4 := by
        have h4 : 4 ∣ 3 * 2 ^ (n - 3) := ⟨3 * 2 ^ (n - 5), by
          have h := two_pow_mul_split (n - 3) 2 (by omega)
          have hs : n - 3 - 2 = n - 5 := by omega
          rw [hs] at h; omega⟩
        rcases h4 with ⟨q, hq⟩; omega
      rw [htel (by omega) hhi]
      have hm_ge : 2 ^ (n - 4) ≤ m := by omega
      have hm_lt : m - 2 ^ (n - 4) < 2 ^ (n - 4) := by omega
      have hm_split : m = (m - 2 ^ (n - 4)) + 2 ^ (n - 4) := by omega
      rw [hm_split, testBit_add_pow2_lt (n - 4) (m - 2 ^ (n - 4)) (n - 4) hm_lt]
      simp

/-- Explicit witness pair `(1, 25)` at upper band edge `3 * 2^(n-3)` for all $n \ge 5$. -/
theorem upper_band_edge_witness_all_n :
    ∀ n, 5 ≤ n →
      twobladeNullity n 1 25 = 3 * 2 ^ (n - 3) ∧
      parityBits n ((1 ^^^ 25) &&& (2 ^ n - 8)) = false := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn5 : n = 4
    · subst hn5
      have hnu5 : twobladeNullity 5 1 25 = 12 := by
        have h19 : twobladeNullity 4 1 9 = 0 := by
          rw [← nu4Closed_eq 1 9 (by omega) (by omega) (by omega)]; rfl
        have hcross := nullity_doubling_cross 4 1 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [h19] at hcross
        simpa using hcross
      exact ⟨hnu5, by decide⟩
    · have hn_ge5 : 5 ≤ n := by omega
      rcases ih hn_ge5 with ⟨hnu, _⟩
      have h32 : 32 ≤ 2 ^ n := by
        calc 32 = 2 ^ 5 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_ge5
      have hnu_next : twobladeNullity (n + 1) 1 25 = 3 * 2 ^ (n + 1 - 3) := by
        rw [nullity_doubling_lower n 1 25 (by omega) (by omega) (by omega) (by omega) (by omega), hnu]
        have hp : 2 ^ (n + 1 - 3) = 2 * 2 ^ (n - 3) := by
          have h1 : n + 1 - 3 = (n - 3) + 1 := by omega
          rw [h1, Nat.pow_succ, Nat.mul_comm]
        rw [hp]; omega
      have hpar_next : parityBits (n + 1) ((1 ^^^ 25) &&& (2 ^ (n + 1) - 8)) = false := by
        have h24 : 1 ^^^ 25 = 24 := by decide
        rw [h24]
        have hbit : ∀ j, j < n + 1 → (24 &&& (2 ^ (n + 1) - 8)).testBit j = (24 : Nat).testBit j := by
          intro j hj
          rw [Nat.testBit_and, testBit_two_pow_sub_eight (n + 1) j (by omega) hj]
          by_cases h3 : 3 ≤ j
          · simp [h3]
          · have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
            rcases this with rfl | rfl | rfl <;> decide
        rw [parityBits_congr_bits (n + 1) _ 24 hbit]
        have hzero : ∀ r, 5 ≤ r → parityBits r 24 = false := by
          intro r hr
          induction r with
          | zero => omega
          | succ r ihr =>
            by_cases hr5 : r = 4
            · subst hr5; decide
            · rw [parityBits_succ_high, ihr (by omega)]
              have hlt : 24 < 2 ^ r := by
                calc 24 < 32 := by omega
                  _ = 2 ^ 5 := rfl
                  _ ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) (by omega)
              rw [Nat.testBit_lt_two_pow hlt]; rfl
        exact hzero (n + 1) (by omega)
      exact ⟨hnu_next, hpar_next⟩

/-- **Theorem T5b (Exponential Continuous Spectral Band Gap at `flipMask = 2^n - 8`):**
    For EVERY $n \ge 6$:
    1. Every value $v$ strictly inside $(2^{n-2},\; 3 \cdot 2^{n-3})$ (width $2^{n-3} - 1$
       consecutive multiples of $4$) has exact histogram count $H_n^{2^n - 8}(v) = 0$.
    2. Lower band edge: $H_n^{2^n - 8}(2^{n-2}) = 42 \cdot 2^{n-4} > 0$.
    3. Upper band edge: $H_n^{2^n - 8}(3 \cdot 2^{n-3}) > 0$. -/
theorem exponential_spectral_band_gap_all_n (n : Nat) (hn : 6 ≤ n) :
    (∀ v, 2 ^ (n - 2) < v → v < 3 * 2 ^ (n - 3) →
      nullityHistGamma n (2 ^ n - 8) v = 0) ∧
    nullityHistGamma n (2 ^ n - 8) (2 ^ (n - 2)) = 42 * 2 ^ (n - 4) ∧
    0 < nullityHistGamma n (2 ^ n - 8) (3 * 2 ^ (n - 3)) := by
  have hpow2 : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 2) 1 (by omega)
    have hs : n - 2 - 1 = n - 3 := by omega
    rw [hs] at h; exact h
  have hpow1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 1) 2 (by omega)
    have hs : n - 1 - 2 = n - 3 := by omega
    rw [hs] at h; exact h
  refine ⟨?_, universal_split_midpoint_42 n (2 ^ n - 8) (by omega), ?_⟩
  · intro v hvlo hvhi
    rw [nullityHistGamma_eq_zero_iff]
    intro i j hi0 hij hj heq
    rcases nilpotent_mirror_law n (2 ^ n - 8) i j (by omega) (by omega) hj (by omega) with ⟨hF, hT⟩
    rcases quarter_parity_locking_all_n n i j (by omega) hi0 hij hj with ⟨hQ2, hQ3⟩
    cases hpar : parityBits n ((i ^^^ j) &&& (2 ^ n - 8))
    · have hstd : twobladeNullity n i j = v := by rw [← hF hpar, heq]
      have ht := hQ3 (by omega) (by omega)
      rw [hpar] at ht; cases ht
    · have hsum := hT hpar
      have hstd : twobladeNullity n i j = 2 ^ (n - 1) - v := by omega
      have hf := hQ2 (by omega) (by omega)
      rw [hpar] at hf; cases hf
  · rcases upper_band_edge_witness_all_n n (by omega) with ⟨hnu, hpar⟩
    have h64 : 64 ≤ 2 ^ n := by
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have hng := (nilpotent_mirror_law n (2 ^ n - 8) 1 25 (by omega) (by omega) (by omega) (by omega)).1 hpar
    rw [nullityHistGamma_pos_iff]
    exact ⟨1, 25, by omega, by omega, by omega, hng.trans hnu⟩

/-! ### Theorem T5c: Exact Complete All-$n$, All-Signature Spectral-Gap Dichotomy -/

/-- Locked Gray-code parity function $P_f(m)$ for an upper-bit mask `8 ∣ f` over bits `3 .. n - 1`. -/
@[expose] def lockedGrayParityLoop (n f m : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let b := 3 + k
    let contrib := if f.testBit b then grayLockBit (n - 1 - b) m else false
    xor (lockedGrayParityLoop n f m k) contrib

@[expose] def lockedGrayParity (n f m : Nat) : Bool :=
  lockedGrayParityLoop n f m (n - 3)

theorem parityBits_eq_lockedGrayParity (n f i j : Nat) (hn : 4 ≤ n)
    (hi0 : 0 < i) (hij : i < j) (hj : j < 2 ^ n)
    (hf8 : f % 8 = 0)
    (hvlo : 2 ^ (n - 3) ≤ twobladeNullity n i j)
    (hvhi : twobladeNullity n i j ≤ 3 * 2 ^ (n - 3) - 4) :
    parityBits n ((i ^^^ j) &&& f) = lockedGrayParity n f (twobladeNullity n i j / 4) := by
  have ⟨h0, hstep⟩ := gray_code_bit_locking_all_n n hn i j hi0 hij hj
  have hpow1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 1) 2 (by omega)
    have hs : n - 1 - 2 = n - 3 := by omega
    rw [hs] at h; exact h
  have hbit_eq : ∀ b, 3 ≤ b → b < n →
      (i ^^^ j).testBit b = grayLockBit (n - 1 - b) (twobladeNullity n i j / 4) := by
    intro b hb3 hbn
    unfold grayLockBit
    by_cases htop : b = n - 1
    · subst htop
      have h0d : n - 1 - (n - 1) = 0 := by omega
      simp only [h0d, ↓reduceIte]
      have h4 : 4 ≤ twobladeNullity n i j := by
        have : 2 ≤ 2 ^ (n - 3) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
        have ⟨⟨m, hm⟩, _⟩ := nullity_mod4_and_bound n (by omega) i j hi0 (by omega) (by omega) hj (by omega)
        omega
      exact h0 h4 (by omega)
    · have hd1 : 1 ≤ n - 1 - b := by omega
      have hd0 : ¬(n - 1 - b = 0) := by omega
      simp only [hd0, ↓reduceIte]
      have hpowd : 2 ^ (n - 1 - b + 1) ≤ 2 ^ (n - 3) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hst := hstep (n - 1 - b) hd1 (by omega) (by omega) (by omega)
      have hidx : n - 1 - (n - 1 - b) = b := by omega
      rw [hidx] at hst
      exact hst
  have hlow3 : parityBits 3 ((i ^^^ j) &&& f) = false := by
    have hcongr : ∀ r, r < 3 → ((i ^^^ j) &&& f).testBit r = (0 : Nat).testBit r := by
      intro r hr
      rw [Nat.testBit_and, testBit_zero_false_of_mod8 f r hf8 hr, Bool.and_false, Nat.zero_testBit]
    rw [parityBits_congr_bits 3 _ 0 hcongr]; rfl
  have hloop : ∀ k, k ≤ n - 3 →
      parityBits (3 + k) ((i ^^^ j) &&& f) =
        lockedGrayParityLoop n f (twobladeNullity n i j / 4) k := by
    intro k hk
    induction k with
    | zero => simpa [lockedGrayParityLoop] using hlow3
    | succ k ih =>
      have hadd : 3 + (k + 1) = (3 + k) + 1 := by omega
      rw [hadd, parityBits_succ_high, ih (by omega)]
      show xor (lockedGrayParityLoop n f (twobladeNullity n i j / 4) k) (((i ^^^ j) &&& f).testBit (3 + k)) =
           xor (lockedGrayParityLoop n f (twobladeNullity n i j / 4) k)
             (if f.testBit (3 + k) then grayLockBit (n - 1 - (3 + k)) (twobladeNullity n i j / 4) else false)
      rw [Nat.testBit_and, hbit_eq (3 + k) (by omega) (by omega)]
      cases f.testBit (3 + k) <;> simp
  unfold lockedGrayParity
  have hn_eq : 3 + (n - 3) = n := by omega
  have h := hloop (n - 3) (Nat.le_refl _)
  simpa [hn_eq] using h

/-- Gray-code single-bit flip lemma: at $m_+ = 2^{n-4} + 2^{d-1}$ vs $m_- = 2^{n-4} - 2^{d-1}$
    (for $1 \le d \le n - 5$, $n \ge 6$), EVERY Gray bit $k \ne d$ ($0 \le k \le n - 4$) is equal
    at $m_+$ and $m_-$, while at $k = d$, `grayLockBit d m_+ = true` and `grayLockBit d m_- = false`! -/
theorem grayLockBit_mirror_flip (n d : Nat) (hn : 6 ≤ n) (hd1 : 1 ≤ d) (hd5 : d ≤ n - 5) :
    let mPlus := 2 ^ (n - 4) + 2 ^ (d - 1)
    let mMinus := 2 ^ (n - 4) - 2 ^ (d - 1)
    grayLockBit d mPlus = true ∧
    grayLockBit d mMinus = false ∧
    (∀ k, k ≤ n - 4 → k ≠ d → grayLockBit k mPlus = grayLockBit k mMinus) := by
  have hdm_lt : 2 ^ (d - 1) < 2 ^ (n - 4) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hbp : ∀ j, (2 ^ (n - 4) + 2 ^ (d - 1)).testBit j =
      (decide (j = n - 4) || decide (j = d - 1)) := by
    intro j
    rw [Nat.add_comm, testBit_add_pow2_lt (n - 4) (2 ^ (d - 1)) j hdm_lt, Nat.testBit_two_pow]
    by_cases hj1 : j = n - 4
    · subst hj1; simp
    · by_cases hj2 : j = d - 1
      · subst hj2; simp [hj1]
      · have hne : ¬(d - 1 = j) := Ne.symm hj2
        simp [hj1, hj2, hne]
  have hbm : ∀ j, (2 ^ (n - 4) - 2 ^ (d - 1)).testBit j =
      decide (d - 1 ≤ j ∧ j < n - 4) := by
    intro j
    exact testBit_two_pow_sub_two_pow (n - 4) (d - 1) j (by omega)
  have hd0 : d ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold grayLockBit
    simp only [hd0, ↓reduceIte, hbp]
    have h1 : d - 1 ≠ n - 4 := by omega
    have h2 : d ≠ n - 4 := by omega
    have h3 : d ≠ d - 1 := by omega
    simp [h1, h2, h3]
  · unfold grayLockBit
    simp only [hd0, ↓reduceIte, hbm]
    have h1 : d - 1 ≤ d - 1 ∧ d - 1 < n - 4 := by omega
    have h2 : d - 1 ≤ d ∧ d < n - 4 := by omega
    simp [h1, h2]
  · intro k hkn hkd
    unfold grayLockBit
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte, hbp, hbm]
      have h0n : (0 : Nat) ≠ n - 4 := by omega
      have h0lt : 0 < n - 4 := by omega
      by_cases hd_eq1 : d = 1
      · subst hd_eq1; simp [h0n, h0lt]
      · have h1 : (0 : Nat) ≠ d - 1 := by omega
        have h2 : ¬(d - 1 ≤ 0) := by omega
        simp [h0n, h1, h2]
    · simp only [hk0, ↓reduceIte, hbp, hbm]
      by_cases hk_lt : k < d
      · by_cases hk_pred : k = d - 1
        · subst hk_pred
          have ha1 : d - 1 - 1 ≠ n - 4 := by omega
          have ha2 : d - 1 - 1 ≠ d - 1 := by omega
          have ha3 : d - 1 ≠ n - 4 := by omega
          have hb1 : ¬(d - 1 ≤ d - 1 - 1) := by omega
          have hb2 : d - 1 ≤ d - 1 ∧ d - 1 < n - 4 := by omega
          simp [ha1, ha2, ha3, hb1, hb2]
        · have ha1 : k - 1 ≠ n - 4 := by omega
          have ha2 : k - 1 ≠ d - 1 := by omega
          have ha3 : k ≠ n - 4 := by omega
          have ha4 : k ≠ d - 1 := by omega
          have hb1 : ¬(d - 1 ≤ k - 1) := by omega
          have hb2 : ¬(d - 1 ≤ k) := by omega
          simp [ha1, ha2, ha3, ha4, hb1, hb2]
      · by_cases hk_top : k = n - 4
        · subst hk_top
          have ha1 : n - 4 - 1 ≠ n - 4 := by omega
          have ha2 : n - 4 - 1 ≠ d - 1 := by omega
          have ha4 : n - 4 ≠ d - 1 := by omega
          have hb1 : d - 1 ≤ n - 4 - 1 ∧ n - 4 - 1 < n - 4 := by omega
          have hb2 : ¬(n - 4 < n - 4) := by omega
          simp [ha1, ha2, ha4, hb1, hb2]
        · have ha1 : k - 1 ≠ n - 4 := by omega
          have ha2 : k - 1 ≠ d - 1 := by omega
          have ha3 : k ≠ n - 4 := by omega
          have ha4 : k ≠ d - 1 := by omega
          have hb1 : d - 1 ≤ k - 1 ∧ k - 1 < n - 4 := by omega
          have hb2 : d - 1 ≤ k ∧ k < n - 4 := by omega
          simp [ha1, ha2, ha3, ha4, hb1, hb2]

theorem exists_middle_bit_of_gapped (n f : Nat) (hn : 6 ≤ n) (hf : f < 2 ^ n)
    (hg : isGappedMask n f = true) :
    ∃ b, 4 ≤ b ∧ b ≤ n - 2 ∧ f.testBit b = true := by
  unfold isGappedMask at hg
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hg
  rcases hg with ⟨⟨⟨⟨hf8, hne0⟩, hne8⟩, hneTop⟩, hneTop8⟩
  by_cases hex : ∃ b, 4 ≤ b ∧ b ≤ n - 2 ∧ f.testBit b = true
  · exact hex
  · exfalso
    have hnone : ∀ b, 4 ≤ b → b ≤ n - 2 → f.testBit b = false := by
      intro b hb4 hbn
      cases h : f.testBit b
      · rfl
      · exact absurd ⟨b, hb4, hbn, h⟩ hex
    let c := (if f.testBit (n - 1) then 2 ^ (n - 1) else 0) + (if f.testBit 3 then 8 else 0)
    have h8lt : (if f.testBit 3 then 8 else 0) < 2 ^ (n - 1) := by
      have : 32 ≤ 2 ^ (n - 1) := by
        calc 32 = 2 ^ 5 := rfl
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      split <;> omega
    have hfeq : f = c := by
      apply Nat.eq_of_testBit_eq; intro j
      have hc : c.testBit j =
          ((if j = n - 1 then f.testBit (n - 1) else false) ||
           (if j = 3 then f.testBit 3 else false)) := by
        dsimp only [c]
        cases htop : f.testBit (n - 1)
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          cases h3 : f.testBit 3
          · simp
          · simp only [↓reduceIte, show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow]
            by_cases hj3 : j = 3
            · subst hj3; simp
            · have hne : ¬(3 = j) := Ne.symm hj3
              simp [hj3, hne]
        · simp only [↓reduceIte]
          rw [Nat.add_comm, testBit_add_pow2_lt (n - 1) _ j h8lt]
          by_cases hjn : j = n - 1
          · subst hjn; simp
          · simp only [hjn, ↓reduceIte, Bool.false_or]
            cases h3 : f.testBit 3
            · simp
            · simp only [↓reduceIte, show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow]
              by_cases hj3 : j = 3
              · subst hj3; simp
              · have hne : ¬(3 = j) := Ne.symm hj3
                simp [hj3, hne]
      rw [hc]
      by_cases hjn : j = n - 1
      · subst hjn
        have hne3 : n - 1 ≠ 3 := by omega
        simp [hne3]
      · by_cases hj3 : j = 3
        · subst hj3; simp [hjn]
        · simp only [hjn, hj3, ↓reduceIte, Bool.or_self]
          by_cases hjlt3 : j < 3
          · exact testBit_zero_false_of_mod8 f j hf8 hjlt3
          · by_cases hjmid : j ≤ n - 2
            · exact hnone j (by omega) hjmid
            · exact Nat.testBit_lt_two_pow (by
                have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
                omega)
    dsimp only [c] at hfeq
    cases htop : f.testBit (n - 1) <;> cases h3 : f.testBit 3 <;> simp [htop, h3] at hfeq <;> omega

theorem gapped_mask_has_interior_gap (n f : Nat) (hn : 6 ≤ n) (hf : f < 2 ^ n)
    (hg : isGappedMask n f = true) :
    hasInteriorMod4Gap n f := by
  have hf8 : f % 8 = 0 := by
    unfold isGappedMask at hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact hg.1.1.1.1
  rcases exists_middle_bit_of_gapped n f hn hf hg with ⟨b, hb4, hbn2, hfb⟩
  let d := n - 1 - b
  have hd1 : 1 ≤ d := by omega
  have hd5 : d ≤ n - 5 := by omega
  let mPlus := 2 ^ (n - 4) + 2 ^ (d - 1)
  let mMinus := 2 ^ (n - 4) - 2 ^ (d - 1)
  let vPlus := 4 * mPlus
  let vMinus := 4 * mMinus
  have hpow1 : 2 ^ (n - 1) = 8 * 2 ^ (n - 4) := by
    have h := two_pow_mul_split (n - 1) 3 (by omega)
    have hs : n - 1 - 3 = n - 4 := by omega
    rw [hs] at h; exact h
  have hpow3 : 2 ^ (n - 3) = 2 * 2 ^ (n - 4) := by
    have h := two_pow_mul_split (n - 3) 1 (by omega)
    have hs : n - 3 - 1 = n - 4 := by omega
    rw [hs] at h; exact h
  have hge4 : 4 ≤ 2 ^ (n - 4) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (n - 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have hdm_le : 2 ^ (d - 1) ≤ 2 ^ (n - 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow6 : 2 ^ (n - 4) = 4 * 2 ^ (n - 6) := by
    have h := two_pow_mul_split (n - 4) 2 (by omega)
    have hs : n - 4 - 2 = n - 6 := by omega
    rw [hs] at h; exact h
  have hpos_d1 : 0 < 2 ^ (d - 1) := Nat.two_pow_pos (d - 1)
  have hvp_in : 2 ^ (n - 3) ≤ vPlus ∧ vPlus ≤ 3 * 2 ^ (n - 3) - 4 := by omega
  have hvm_in : 2 ^ (n - 3) ≤ vMinus ∧ vMinus ≤ 3 * 2 ^ (n - 3) - 4 := by omega
  rcases grayLockBit_mirror_flip n d hn hd1 hd5 with ⟨hgt, hgf, hgeq⟩
  have hpar_diff : lockedGrayParity n f mPlus = !(lockedGrayParity n f mMinus) := by
    have hloop : ∀ k, k ≤ n - 3 →
        lockedGrayParityLoop n f mPlus k =
          if b < 3 + k then !(lockedGrayParityLoop n f mMinus k)
          else lockedGrayParityLoop n f mMinus k := by
      intro k hk
      induction k with
      | zero =>
        have hnb : ¬(b < 3 + 0) := by omega
        simp [lockedGrayParityLoop, hnb]
      | succ k ih =>
        unfold lockedGrayParityLoop
        dsimp only
        rw [ih (by omega)]
        by_cases hbk : b = 3 + k
        · have hd_eq : n - 1 - (3 + k) = d := by omega
          have hnot_lt : ¬(b < 3 + k) := by omega
          have hlt : b < 3 + (k + 1) := by omega
          have hfb' : f.testBit (3 + k) = true := by rw [← hbk]; exact hfb
          simp only [hnot_lt, hlt, ↓reduceIte, hfb', hd_eq]
          change xor (lockedGrayParityLoop n f mMinus k) (grayLockBit d (2 ^ (n - 4) + 2 ^ (d - 1))) =
                 !(xor (lockedGrayParityLoop n f mMinus k) (grayLockBit d (2 ^ (n - 4) - 2 ^ (d - 1))))
          rw [hgt, hgf]
          cases lockedGrayParityLoop n f mMinus k <;> rfl
        · have hne_d : n - 1 - (3 + k) ≠ d := by omega
          have hbit_same : grayLockBit (n - 1 - (3 + k)) mPlus = grayLockBit (n - 1 - (3 + k)) mMinus :=
            hgeq (n - 1 - (3 + k)) (by omega) hne_d
          rw [hbit_same]
          by_cases hlt_prev : b < 3 + k
          · have hlt_next : b < 3 + (k + 1) := by omega
            simp only [hlt_prev, hlt_next, ↓reduceIte]
            cases lockedGrayParityLoop n f mMinus k <;> cases f.testBit (3 + k) <;>
              cases grayLockBit (n - 1 - (3 + k)) mMinus <;> rfl
          · have hlt_next : ¬(b < 3 + (k + 1)) := by omega
            simp only [hlt_prev, hlt_next, ↓reduceIte]
    unfold lockedGrayParity
    have hblt : b < 3 + (n - 3) := by omega
    simpa [hblt] using hloop (n - 3) (Nat.le_refl _)
  have hkill : ∀ v, 4 ∣ v → 2 ^ (n - 3) ≤ v → v ≤ 3 * 2 ^ (n - 3) - 4 →
      2 ^ (n - 3) ≤ 2 ^ (n - 1) - v → 2 ^ (n - 1) - v ≤ 3 * 2 ^ (n - 3) - 4 →
      lockedGrayParity n f (v / 4) = true →
      lockedGrayParity n f ((2 ^ (n - 1) - v) / 4) = false →
      nullityHistGamma n f v = 0 := by
    intro v _ hv1 hv2 hmv1 hmv2 hp1 hp2
    rw [nullityHistGamma_eq_zero_iff]
    intro i j hi0 hij hj heq
    rcases nilpotent_mirror_law n f i j (by omega) (by omega) hj (by omega) with ⟨hF, hT⟩
    cases hpar : parityBits n ((i ^^^ j) &&& f)
    · have hstd : twobladeNullity n i j = v := by rw [← hF hpar, heq]
      have hl := parityBits_eq_lockedGrayParity n f i j (by omega) hi0 hij hj hf8 (by omega) (by omega)
      rw [hstd, hp1, hpar] at hl; cases hl
    · have hsum := hT hpar
      have hstd : twobladeNullity n i j = 2 ^ (n - 1) - v := by omega
      have hl := parityBits_eq_lockedGrayParity n f i j (by omega) hi0 hij hj hf8 (by omega) (by omega)
      rw [hstd, hp2, hpar] at hl; cases hl
  cases hpm : lockedGrayParity n f mMinus
  · have hpt : lockedGrayParity n f mPlus = true := by rw [hpar_diff, hpm]; rfl
    refine ⟨vPlus, ⟨mPlus, rfl⟩, by omega, by omega, ?_⟩
    apply hkill vPlus ⟨mPlus, rfl⟩ hvp_in.1 hvp_in.2 (by omega) (by omega)
    · have hdiv : vPlus / 4 = mPlus := by omega
      rw [hdiv]; exact hpt
    · have hsub : (2 ^ (n - 1) - vPlus) / 4 = mMinus := by omega
      rw [hsub]; exact hpm
  · have hpf : lockedGrayParity n f mPlus = false := by rw [hpar_diff, hpm]; rfl
    refine ⟨vMinus, ⟨mMinus, rfl⟩, by omega, by omega, ?_⟩
    apply hkill vMinus ⟨mMinus, rfl⟩ hvm_in.1 hvm_in.2 (by omega) (by omega)
    · have hdiv : vMinus / 4 = mMinus := by omega
      rw [hdiv]; exact hpm
    · have hsub : (2 ^ (n - 1) - vMinus) / 4 = mPlus := by omega
      rw [hsub]; exact hpf

/-! ### Converse: Every Non-Gapped Signature Has Zero Interior Gaps -/

/-- Decidable check for `n = 4` base case: every `f < 16` with `f % 8 ≠ 0` realizes BOTH parities
    on BOTH Euclidean bins `v = 0` and `v = 4`. -/
@[expose] def cd4CheckPair (f v : Nat) (p : Bool) : Bool :=
  (List.range 16).any fun i =>
    (List.range 16).any fun j =>
      decide (0 < i ∧ i < j) &&
      (nu4Closed i j == v) &&
      (parityBits 4 ((i ^^^ j) &&& f) == p)

theorem cd4_not_div8_both_parities_check :
    ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15].all fun f =>
      cd4CheckPair f 0 false && cd4CheckPair f 0 true &&
      cd4CheckPair f 4 false && cd4CheckPair f 4 true) = true := by
  decide

theorem cd4_not_div8_both_parities (f v : Nat) (p : Bool) (hf : f < 16) (hf8 : f % 8 ≠ 0)
    (hv : v = 0 ∨ v = 4) :
    ∃ i j, 0 < i ∧ i < j ∧ j < 16 ∧ twobladeNullity 4 i j = v ∧
      parityBits 4 ((i ^^^ j) &&& f) = p := by
  have hmem : f ∈ [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15] := by
    have : f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 ∨
           f = 9 ∨ f = 10 ∨ f = 11 ∨ f = 12 ∨ f = 13 ∨ f = 14 ∨ f = 15 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hall := List.all_eq_true.mp cd4_not_div8_both_parities_check f hmem
  have hchk : cd4CheckPair f v p = true := by
    simp only [Bool.and_eq_true] at hall
    rcases hv with rfl | rfl <;> cases p
    · exact hall.1.1.1
    · exact hall.1.1.2
    · exact hall.1.2
    · exact hall.2
  unfold cd4CheckPair at hchk
  rcases List.any_eq_true.mp hchk with ⟨i, hi, hchk2⟩
  rcases List.any_eq_true.mp hchk2 with ⟨j, hj, hcond⟩
  rw [List.mem_range] at hi hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
  rcases hcond with ⟨⟨⟨hi0, hij⟩, hnu⟩, hpar⟩
  refine ⟨i, j, hi0, hij, hj, ?_, hpar⟩
  rw [← nu4Closed_eq i j hi0 (by omega) hj]
  exact hnu

/-- **Universal Both-Parities Lemma for `f % 8 ≠ 0`:**
    For EVERY $n \ge 4$, EVERY $f < 2^n$ with $f \bmod 8 \ne 0$, EVERY multiple of $4$ in
    $[0, 2^{n-1} - 4]$, and EVERY target parity $p \in \{\mathrm{false}, \mathrm{true}\}$,
    there exists a pair $1 \le i < j < 2^n$ with $\nu_n^{\mathrm{std}}(i, j) = v$ and
    $\mathrm{parity}_n((i \oplus j) \,\&\, f) = p$. -/
theorem both_parities_when_not_div8 :
    ∀ n, 4 ≤ n → ∀ f v, f < 2 ^ n → f % 8 ≠ 0 → 4 ∣ v → v ≤ 2 ^ (n - 1) - 4 →
      ∀ p : Bool, ∃ i j, 0 < i ∧ i < j ∧ j < 2 ^ n ∧
        twobladeNullity n i j = v ∧ parityBits n ((i ^^^ j) &&& f) = p := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : n = 3
    · subst hn4
      intro f v hf hf8 ⟨k, hk⟩ hv p
      have hv4 : v ≤ 4 := hv
      exact cd4_not_div8_both_parities f v p hf hf8 (by omega)
    · have hn_ge4 : 4 ≤ n := by omega
      have hih := ih hn_ge4
      intro f v hf hf8 ⟨k, hk⟩ hv p
      have hv_bound : v ≤ 2 ^ n - 4 := hv
      let f' := f % 2 ^ n
      have h8dvd : 8 ∣ 2 ^ n := ⟨2 ^ (n - 3), two_pow_mul_split n 3 (by omega)⟩
      have hf'8 : f' % 8 ≠ 0 := by
        have : f' % 8 = f % 8 := Nat.mod_mod_of_dvd f h8dvd
        omega
      have hf'lt : f' < 2 ^ n := Nat.mod_lt f (Nat.two_pow_pos n)
      have h2n1 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
      have h8n : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 (by omega)
      have h2np1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge8 : 8 ≤ 2 ^ (n - 1) := by
        calc 8 = 2 ^ 3 := rfl
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      by_cases heven : k % 2 = 0
      · let v' := 4 * (k / 2)
        have hv'le : v' ≤ 2 ^ (n - 1) - 4 := by omega
        rcases hih f' v' hf'lt hf'8 ⟨k / 2, rfl⟩ hv'le p with ⟨i, j, hi0, hij, hj, hnu, hpar⟩
        have hnu_next : twobladeNullity (n + 1) i j = v := by
          rw [nullity_doubling_lower n i j hi0 (by omega) (by omega) hj (by omega), hnu]; omega
        have hpar_next : parityBits (n + 1) ((i ^^^ j) &&& f) = p := by
          rw [parityBits_succ_high, Nat.testBit_and,
              Nat.testBit_lt_two_pow (Nat.xor_lt_two_pow (by omega) hj),
              Bool.false_and, Bool.xor_false]
          have hcongr : ∀ r, r < n → ((i ^^^ j) &&& f).testBit r = ((i ^^^ j) &&& f').testBit r := by
            intro r hr
            simp only [Nat.testBit_and, f', Nat.testBit_mod_two_pow, hr, decide_true, Bool.true_and]
          rw [parityBits_congr_bits n _ _ hcongr, hpar]
        exact ⟨i, j, hi0, hij, by omega, hnu_next, hpar_next⟩
      · let v' := (2 ^ n - 4 - v) / 2
        have hv'4 : 4 ∣ v' := ⟨(2 ^ n - 4 - v) / 8, by omega⟩
        have hv'le : v' ≤ 2 ^ (n - 1) - 4 := by omega
        let p' := xor p (f.testBit n)
        rcases hih f' v' hf'lt hf'8 hv'4 hv'le p' with ⟨i, b, hi0, hib, hb, hnu, hpar⟩
        have hnu_next : twobladeNullity (n + 1) i (b + 2 ^ n) = v := by
          rw [nullity_doubling_cross n i b (by omega) hi0 (by omega) (by omega) hb (by omega), hnu]
          omega
        have hpar_next : parityBits (n + 1) ((i ^^^ (b + 2 ^ n)) &&& f) = p := by
          rw [xor_add_right (by omega) hb, parityBits_succ_high, Nat.testBit_and,
              testBit_add_pow2_lt n (i ^^^ b) n (Nat.xor_lt_two_pow (by omega) hb)]
          simp only [↓reduceIte, Bool.true_and]
          have hcongr : ∀ r, r < n →
              (((i ^^^ b) + 2 ^ n) &&& f).testBit r = ((i ^^^ b) &&& f').testBit r := by
            intro r hr
            have hrne : r ≠ n := by omega
            simp only [Nat.testBit_and, testBit_add_pow2_lt n (i ^^^ b) r (Nat.xor_lt_two_pow (by omega) hb),
                       hrne, ↓reduceIte, f', Nat.testBit_mod_two_pow, hr, decide_true, Bool.true_and]
          rw [parityBits_congr_bits n _ _ hcongr, hpar]
          dsimp only [p']
          cases p <;> cases f.testBit n <;> rfl
        exact ⟨i, b + 2 ^ n, hi0, by omega, by omega, hnu_next, hpar_next⟩

/-- Every Euclidean multiple-of-4 bin in $[0, 2^{n-1} - 4]$ is strictly populated for $n \ge 4$. -/
theorem std_all_mod4_populated :
    ∀ n, 4 ≤ n → ∀ v, 4 ∣ v → v ≤ 2 ^ (n - 1) - 4 → 0 < nullityHist n v := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : n = 3
    · subst hn4
      intro v ⟨k, hk⟩ hv
      have hv4 : v ≤ 4 := hv
      have : v = 0 ∨ v = 4 := by omega
      rcases this with rfl | rfl
      · rw [nonZDCount_all_n 4 (by omega)]; decide
      · rw [show (4 : Nat) = 2 ^ (4 - 2) from rfl, terrace_midpoint_std_all_n 4 (by omega)]; decide
    · have hn_ge4 : 4 ≤ n := by omega
      have hih := ih hn_ge4
      intro v ⟨k, hk⟩ hv
      have hv_bound : v ≤ 2 ^ n - 4 := hv
      have h2n : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 (by omega)
      have h2n1 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
      have hge2 : 2 ≤ 2 ^ (n - 3) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
      by_cases hv0 : v = 0
      · subst hv0
        rw [nonZDCount_all_n (n + 1) (by omega)]
        unfold nonZDCountFormula; omega
      · by_cases heven : k % 2 = 0
        · let m := k / 2
          have hv8 : v = 8 * m := by omega
          rw [hv8, terrace_interleave_even n m (by omega) (by omega)]
          have hprev := hih (4 * m) ⟨m, rfl⟩ (by omega)
          omega
        · let m := (2 ^ n - 4 - v) / 8
          have hvodd : v = 2 ^ n - 4 - 8 * m := by omega
          rw [hvodd, terrace_interleave_odd n m (by omega) (by omega)]
          have hprev := hih (4 * m) ⟨m, rfl⟩ (by omega)
          omega

/-- **Outer Bit-3 Both-Parities Lemma:** For EVERY $n \ge 4$ and EVERY multiple of $4$ outside
    $[2^{n-3},\; 3 \cdot 2^{n-3})$ (i.e., $v < 2^{n-3}$ or $3 \cdot 2^{n-3} \le v \le 2^{n-1} - 4$),
    BOTH `(i ^^^ j).testBit 3 = false` and `(i ^^^ j).testBit 3 = true` occur at $\nu_n^{\mathrm{std}}(i, j) = v$. -/
theorem bit3_both_parities_outer :
    ∀ n, 4 ≤ n → ∀ v, 4 ∣ v → v ≤ 2 ^ (n - 1) - 4 →
      (v < 2 ^ (n - 3) ∨ 3 * 2 ^ (n - 3) ≤ v) →
      ∀ p : Bool, ∃ i j, 0 < i ∧ i < j ∧ j < 2 ^ n ∧
        twobladeNullity n i j = v ∧ (i ^^^ j).testBit 3 = p := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : n = 3
    · subst hn4
      intro v ⟨k, hk⟩ hv hout p
      have hv4 : v ≤ 4 := hv
      have hout' : v < 2 ∨ 6 ≤ v := hout
      have hv0 : v = 0 := by omega
      subst hv0
      cases p
      · refine ⟨1, 2, by omega, by omega, by omega, ?_, by decide⟩
        rw [← nu4Closed_eq 1 2 (by omega) (by omega) (by omega)]; rfl
      · refine ⟨1, 8, by omega, by omega, by omega, ?_, by decide⟩
        rw [← nu4Closed_eq 1 8 (by omega) (by omega) (by omega)]; rfl
    · have hn_ge4 : 4 ≤ n := by omega
      have hih := ih hn_ge4
      intro v ⟨k, hk⟩ hv hout p
      have hv_bound : v ≤ 2 ^ n - 4 := hv
      have h2n : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 (by omega)
      have h2n1 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
      have h2n2 : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
        have h := two_pow_mul_split (n - 2) 1 (by omega)
        have hs : n - 2 - 1 = n - 3 := by omega
        rw [hs] at h; exact h
      have h2np1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge8 : 8 ≤ 2 ^ (n - 1) := by
        calc 8 = 2 ^ 3 := rfl
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hout_eq : v < 2 ^ (n - 2) ∨ 3 * 2 ^ (n - 2) ≤ v := by
        simpa [show n + 1 - 3 = n - 2 by omega] using hout
      by_cases heven : k % 2 = 0
      · let v' := 4 * (k / 2)
        have hout' : v' < 2 ^ (n - 3) ∨ 3 * 2 ^ (n - 3) ≤ v' := by omega
        have hv'le : v' ≤ 2 ^ (n - 1) - 4 := by omega
        rcases hih v' ⟨k / 2, rfl⟩ hv'le hout' p with ⟨i, j, hi0, hij, hj, hnu, hb3⟩
        exact ⟨i, j, hi0, hij, by omega,
          by rw [nullity_doubling_lower n i j hi0 (by omega) (by omega) hj (by omega), hnu]; omega, hb3⟩
      · let v' := (2 ^ n - 4 - v) / 2
        have hv'4 : 4 ∣ v' := ⟨(2 ^ n - 4 - v) / 8, by omega⟩
        have hv'le : v' ≤ 2 ^ (n - 1) - 4 := by omega
        have hout' : v' < 2 ^ (n - 3) ∨ 3 * 2 ^ (n - 3) ≤ v' := by
          rcases hout_eq with hlo | hhi
          · right
            by_cases hn4' : n = 4
            · subst hn4'; omega
            · have h4dvd : 4 ∣ 3 * 2 ^ (n - 3) := ⟨3 * 2 ^ (n - 5), by
                have h := two_pow_mul_split (n - 3) 2 (by omega)
                have hs : n - 3 - 2 = n - 5 := by omega
                rw [hs] at h; omega⟩
              rcases hv'4 with ⟨q1, hq1⟩
              rcases h4dvd with ⟨q2, hq2⟩
              omega
          · left; omega
        rcases hih v' hv'4 hv'le hout' p with ⟨i, b, hi0, hib, hb, hnu, hb3⟩
        have hb3' : (i ^^^ (b + 2 ^ n)).testBit 3 = p := by
          rw [xor_add_right (by omega) hb,
              testBit_add_pow2_lt n (i ^^^ b) 3 (Nat.xor_lt_two_pow (by omega) hb)]
          have hne : (3 : Nat) ≠ n := by omega
          simp [hne, hb3]
        exact ⟨i, b + 2 ^ n, hi0, by omega, by omega,
          by rw [nullity_doubling_cross n i b (by omega) hi0 (by omega) (by omega) hb (by omega), hnu]; omega,
          hb3'⟩

theorem parityBits_top_plus_eight (n x : Nat) (hn : 5 ≤ n) :
    parityBits n (x &&& (2 ^ (n - 1) + 8)) = xor (x.testBit (n - 1)) (x.testBit 3) := by
  have hxor_eq : 2 ^ (n - 1) + 8 = (2 ^ (n - 1)) ^^^ (2 ^ 3) := by
    have h8lt : (8 : Nat) < 2 ^ (n - 1) := by
      calc 8 < 16 := by omega
        _ = 2 ^ 4 := rfl
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.add_comm, Nat.xor_comm]
    have h := xor_add_right h8lt (Nat.two_pow_pos (n - 1))
    simpa [Nat.xor_zero] using h.symm
  rw [hxor_eq, parityBits_and_mask_eq_xor,
      parityBits_single_pow2 n (n - 1) x (by omega),
      parityBits_single_pow2 n 3 x (by omega)]

/-- Helper: bit 3 of `i ^^^ j` is locked to `true` on the interior band `[2^(n-3), 3*2^(n-3) - 4]`. -/
theorem bit3_locked_true_interior (n w i j : Nat) (hn : 6 ≤ n)
    (hi0 : 0 < i) (hij : i < j) (hj : j < 2 ^ n)
    (hnu : twobladeNullity n i j = w)
    (hw1 : 2 ^ (n - 3) ≤ w) (hw2 : w ≤ 3 * 2 ^ (n - 3) - 4) :
    (i ^^^ j).testBit 3 = true := by
  have hpow1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 1) 2 (by omega)
    have hs : n - 1 - 2 = n - 3 := by omega
    rw [hs] at h; exact h
  have h2n5 : 2 ^ (n - 3) = 4 * 2 ^ (n - 5) := by
    have h := two_pow_mul_split (n - 3) 2 (by omega)
    have hs : n - 3 - 2 = n - 5 := by omega
    rw [hs] at h; exact h
  have h2n4 : 2 ^ (n - 4) = 2 * 2 ^ (n - 5) := by
    have h := two_pow_mul_split (n - 4) 1 (by omega)
    have hs : n - 4 - 1 = n - 5 := by omega
    rw [hs] at h; exact h
  have hstep := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).2 (n - 4) (by omega) (Nat.le_refl _)
    (by rw [show n - 4 + 1 = n - 3 by omega, hnu]; omega)
    (by rw [show n - 4 + 1 = n - 3 by omega, hnu]; omega)
  have hidx1 : n - 1 - (n - 4) = 3 := by omega
  have hidx2 : n - 4 - 1 = n - 5 := by omega
  rw [hidx1, hidx2, hnu] at hstep
  rw [hstep]
  let mm := w / 4
  change xor (mm.testBit (n - 5)) (mm.testBit (n - 4)) = true
  by_cases hmid : mm < 2 ^ (n - 4)
  · have hb_hi : mm.testBit (n - 4) = false := Nat.testBit_lt_two_pow hmid
    have hm_sp : mm = (mm - 2 ^ (n - 5)) + 2 ^ (n - 5) := by omega
    have hb_lo : mm.testBit (n - 5) = true := by
      rw [hm_sp, testBit_add_pow2_lt (n - 5) (mm - 2 ^ (n - 5)) (n - 5) (by omega)]; simp
    rw [hb_lo, hb_hi]; rfl
  · have hmm : mm = w / 4 := rfl
    have hpos5 : 0 < 2 ^ (n - 5) := Nat.two_pow_pos (n - 5)
    have hm_sp : mm = (mm - 2 ^ (n - 4)) + 2 ^ (n - 4) := by omega
    have hrem : mm - 2 ^ (n - 4) < 2 ^ (n - 5) := by omega
    have hb_hi : mm.testBit (n - 4) = true := by
      rw [hm_sp, testBit_add_pow2_lt (n - 4) (mm - 2 ^ (n - 4)) (n - 4) (by omega)]; simp
    have hb_lo : mm.testBit (n - 5) = false := by
      rw [hm_sp, testBit_add_pow2_lt (n - 4) (mm - 2 ^ (n - 4)) (n - 5) (by omega)]
      have hne : n - 5 ≠ n - 4 := by omega
      simp [hne, Nat.testBit_lt_two_pow hrem]
    rw [hb_lo, hb_hi]; rfl

theorem non_gapped_mask_no_interior_gap (n f : Nat) (hn : 6 ≤ n) (hf : f < 2 ^ n)
    (hng : isGappedMask n f = false) :
    ¬ hasInteriorMod4Gap n f := by
  rintro ⟨v, ⟨k, hk⟩, hv0, hvhi, hzero⟩
  have hpos : 0 < nullityHistGamma n f v := by
    by_cases hf8 : f % 8 ≠ 0
    · rcases both_parities_when_not_div8 n (by omega) f v hf hf8 ⟨k, hk⟩ (by omega) false with
        ⟨i, j, hi0, hij, hj, hnu, hpar⟩
      have heq := (nilpotent_mirror_law n f i j (by omega) (by omega) hj (by omega)).1 hpar
      exact (nullityHistGamma_pos_iff n f v).mpr ⟨i, j, hi0, hij, hj, heq.trans hnu⟩
    · have hf8eq : f % 8 = 0 := by omega
      have hcases : f = 0 ∨ f = 8 ∨ f = 2 ^ (n - 1) ∨ f = 2 ^ (n - 1) + 8 := by
        unfold isGappedMask at hng
        simp only [hf8eq, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hng
        omega
      have hpow1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
        have h := two_pow_mul_split (n - 1) 2 (by omega)
        have hs : n - 1 - 2 = n - 3 := by omega
        rw [hs] at h; exact h
      have h4dvd_n3 : 4 ∣ 2 ^ (n - 3) := ⟨2 ^ (n - 5), by
        have h := two_pow_mul_split (n - 3) 2 (by omega)
        have hs : n - 3 - 2 = n - 5 := by omega
        rw [hs] at h; exact h⟩
      rcases h4dvd_n3 with ⟨q3, hq3⟩
      have hq3_pos : 2 ≤ q3 := by
        have : 8 ≤ 2 ^ (n - 3) := by
          calc 8 = 2 ^ 3 := rfl
            _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      rcases hcases with rfl | rfl | rfl | rfl
      · exact std_all_mod4_populated n (by omega) v ⟨k, hk⟩ (by omega)
      · -- f = 8
        by_cases hout : v < 2 ^ (n - 3) ∨ 3 * 2 ^ (n - 3) ≤ v
        · rcases bit3_both_parities_outer n (by omega) v ⟨k, hk⟩ (by omega) hout false with
            ⟨i, j, hi0, hij, hj, hnu, hb3⟩
          have hpar : parityBits n ((i ^^^ j) &&& 8) = false := by
            rw [show (8 : Nat) = 2 ^ 3 from rfl, parityBits_single_pow2 n 3 _ (by omega), hb3]
          have heq := (nilpotent_mirror_law n 8 i j (by omega) (by omega) hj (by omega)).1 hpar
          exact (nullityHistGamma_pos_iff n 8 v).mpr ⟨i, j, hi0, hij, hj, heq.trans hnu⟩
        · let vm := 2 ^ (n - 1) - v
          by_cases hv_eq : v = 2 ^ (n - 3)
          · rcases bit3_both_parities_outer n (by omega) vm ⟨3 * q3, by omega⟩ (by omega) (Or.inr (by omega)) true with
              ⟨i, j, hi0, hij, hj, hnu, hb3⟩
            have hpar : parityBits n ((i ^^^ j) &&& 8) = true := by
              rw [show (8 : Nat) = 2 ^ 3 from rfl, parityBits_single_pow2 n 3 _ (by omega), hb3]
            have hsum := (nilpotent_mirror_law n 8 i j (by omega) (by omega) hj (by omega)).2 hpar
            exact (nullityHistGamma_pos_iff n 8 v).mpr ⟨i, j, hi0, hij, hj, by omega⟩
          · have hvm_pos := std_all_mod4_populated n (by omega) vm ⟨4 * q3 - k, by omega⟩ (by omega)
            rcases (nullityHistGamma_pos_iff n 0 vm).mp hvm_pos with ⟨i, j, hi0, hij, hj, hnu0⟩
            have hnu : twobladeNullity n i j = vm := by
              have h0 := (nilpotent_mirror_law n 0 i j (by omega) (by omega) hj (by omega)).1 (by simp [parityBits_zero])
              omega
            have hb3t := bit3_locked_true_interior n vm i j hn hi0 hij hj hnu (by omega) (by omega)
            have hpar : parityBits n ((i ^^^ j) &&& 8) = true := by
              rw [show (8 : Nat) = 2 ^ 3 from rfl, parityBits_single_pow2 n 3 _ (by omega), hb3t]
            have hsum := (nilpotent_mirror_law n 8 i j (by omega) (by omega) hj (by omega)).2 hpar
            exact (nullityHistGamma_pos_iff n 8 v).mpr ⟨i, j, hi0, hij, hj, by omega⟩
      · -- f = 2^(n-1)
        by_cases hev : k % 2 = 0
        · have hv_pos := std_all_mod4_populated n (by omega) v ⟨k, hk⟩ (by omega)
          rcases (nullityHistGamma_pos_iff n 0 v).mp hv_pos with ⟨i, j, hi0, hij, hj, hnu0⟩
          have hnu : twobladeNullity n i j = v := by
            have h0 := (nilpotent_mirror_law n 0 i j (by omega) (by omega) hj (by omega)).1 (by simp [parityBits_zero])
            omega
          have htop := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).1 (by omega) (by omega)
          have hpar : parityBits n ((i ^^^ j) &&& 2 ^ (n - 1)) = false := by
            rw [parityBits_single_pow2 n (n - 1) _ (by omega), htop, hnu, show v / 4 = k by omega, Nat.testBit_zero]
            simp [hev]
          have heq := (nilpotent_mirror_law n (2 ^ (n - 1)) i j (by omega) (by omega) hj (by omega)).1 hpar
          exact (nullityHistGamma_pos_iff n (2 ^ (n - 1)) v).mpr ⟨i, j, hi0, hij, hj, heq.trans hnu⟩
        · let vm := 2 ^ (n - 1) - v
          have hvm_pos := std_all_mod4_populated n (by omega) vm ⟨4 * q3 - k, by omega⟩ (by omega)
          rcases (nullityHistGamma_pos_iff n 0 vm).mp hvm_pos with ⟨i, j, hi0, hij, hj, hnu0⟩
          have hnu : twobladeNullity n i j = vm := by
            have h0 := (nilpotent_mirror_law n 0 i j (by omega) (by omega) hj (by omega)).1 (by simp [parityBits_zero])
            omega
          have htop := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).1 (by omega) (by omega)
          have hpar : parityBits n ((i ^^^ j) &&& 2 ^ (n - 1)) = true := by
            rw [parityBits_single_pow2 n (n - 1) _ (by omega), htop, hnu,
                show vm / 4 = 4 * q3 - k by omega, Nat.testBit_zero]
            have : (4 * q3 - k) % 2 = 1 := by omega
            simp [this]
          have hsum := (nilpotent_mirror_law n (2 ^ (n - 1)) i j (by omega) (by omega) hj (by omega)).2 hpar
          exact (nullityHistGamma_pos_iff n (2 ^ (n - 1)) v).mpr ⟨i, j, hi0, hij, hj, by omega⟩
      · -- f = 2^(n-1) + 8
        by_cases hout : v < 2 ^ (n - 3) ∨ 3 * 2 ^ (n - 3) ≤ v
        · let wantB3 : Bool := decide (k % 2 = 1)
          rcases bit3_both_parities_outer n (by omega) v ⟨k, hk⟩ (by omega) hout wantB3 with
            ⟨i, j, hi0, hij, hj, hnu, hb3⟩
          have htop := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).1 (by omega) (by omega)
          have htop_val : (i ^^^ j).testBit (n - 1) = wantB3 := by
            rw [htop, hnu, show v / 4 = k by omega, Nat.testBit_zero]
          have hpar : parityBits n ((i ^^^ j) &&& (2 ^ (n - 1) + 8)) = false := by
            rw [parityBits_top_plus_eight n _ (by omega), htop_val, hb3]
            cases wantB3 <;> rfl
          have heq := (nilpotent_mirror_law n (2 ^ (n - 1) + 8) i j (by omega) (by omega) hj (by omega)).1 hpar
          exact (nullityHistGamma_pos_iff n (2 ^ (n - 1) + 8) v).mpr ⟨i, j, hi0, hij, hj, heq.trans hnu⟩
        · by_cases hv_eq : v = 2 ^ (n - 3)
          · let vm := 2 ^ (n - 1) - v
            let wantB3 : Bool := !(decide ((3 * q3) % 2 = 1))
            rcases bit3_both_parities_outer n (by omega) vm ⟨3 * q3, by omega⟩ (by omega) (Or.inr (by omega)) wantB3 with
              ⟨i, j, hi0, hij, hj, hnu, hb3⟩
            have htop := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).1 (by omega) (by omega)
            have htop_val : (i ^^^ j).testBit (n - 1) = decide ((3 * q3) % 2 = 1) := by
              rw [htop, hnu, show vm / 4 = 3 * q3 by omega, Nat.testBit_zero]
            have hpar : parityBits n ((i ^^^ j) &&& (2 ^ (n - 1) + 8)) = true := by
              rw [parityBits_top_plus_eight n _ (by omega), htop_val, hb3]
              dsimp only [wantB3]
              cases decide ((3 * q3) % 2 = 1) <;> rfl
            have hsum := (nilpotent_mirror_law n (2 ^ (n - 1) + 8) i j (by omega) (by omega) hj (by omega)).2 hpar
            exact (nullityHistGamma_pos_iff n (2 ^ (n - 1) + 8) v).mpr ⟨i, j, hi0, hij, hj, by omega⟩
          · by_cases hodd : k % 2 = 1
            · have hv_pos := std_all_mod4_populated n (by omega) v ⟨k, hk⟩ (by omega)
              rcases (nullityHistGamma_pos_iff n 0 v).mp hv_pos with ⟨i, j, hi0, hij, hj, hnu0⟩
              have hnu : twobladeNullity n i j = v := by
                have h0 := (nilpotent_mirror_law n 0 i j (by omega) (by omega) hj (by omega)).1 (by simp [parityBits_zero])
                omega
              have htop := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).1 (by omega) (by omega)
              have hb3 := bit3_locked_true_interior n v i j hn hi0 hij hj hnu (by omega) (by omega)
              have hpar : parityBits n ((i ^^^ j) &&& (2 ^ (n - 1) + 8)) = false := by
                rw [parityBits_top_plus_eight n _ (by omega), htop, hnu, show v / 4 = k by omega,
                    Nat.testBit_zero, hb3]
                simp [hodd]
              have heq := (nilpotent_mirror_law n (2 ^ (n - 1) + 8) i j (by omega) (by omega) hj (by omega)).1 hpar
              exact (nullityHistGamma_pos_iff n (2 ^ (n - 1) + 8) v).mpr ⟨i, j, hi0, hij, hj, heq.trans hnu⟩
            · let vm := 2 ^ (n - 1) - v
              have hvm_pos := std_all_mod4_populated n (by omega) vm ⟨4 * q3 - k, by omega⟩ (by omega)
              rcases (nullityHistGamma_pos_iff n 0 vm).mp hvm_pos with ⟨i, j, hi0, hij, hj, hnu0⟩
              have hnu : twobladeNullity n i j = vm := by
                have h0 := (nilpotent_mirror_law n 0 i j (by omega) (by omega) hj (by omega)).1 (by simp [parityBits_zero])
                omega
              have htop := (gray_code_bit_locking_all_n n (by omega) i j hi0 hij hj).1 (by omega) (by omega)
              have hb3 := bit3_locked_true_interior n vm i j hn hi0 hij hj hnu (by omega) (by omega)
              have hpar : parityBits n ((i ^^^ j) &&& (2 ^ (n - 1) + 8)) = true := by
                rw [parityBits_top_plus_eight n _ (by omega), htop, hnu,
                    show vm / 4 = 4 * q3 - k by omega, Nat.testBit_zero, hb3]
                have hev : (4 * q3 - k) % 2 = 0 := by omega
                simp [hev]
              have hsum := (nilpotent_mirror_law n (2 ^ (n - 1) + 8) i j (by omega) (by omega) hj (by omega)).2 hpar
              exact (nullityHistGamma_pos_iff n (2 ^ (n - 1) + 8) v).mpr ⟨i, j, hi0, hij, hj, by omega⟩
  omega

/-- Exact count of gapped signatures: `countPred (isGappedMask n) (2^n) = 2^(n-3) - 4` for $n \ge 6$. -/
theorem countPred_div8 (m : Nat) :
    countPred (fun f => f % 8 == 0) (8 * m) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : 8 * (m + 1) = 8 * m + 8 := by omega
    rw [h, countPred_add, ih]
    have hstep : countPred (fun k => (8 * m + k) % 8 == 0) 8 = 1 := by
      have hext : countPred (fun k => (8 * m + k) % 8 == 0) 8 =
                  countPred (fun k => k % 8 == 0) 8 := by
        apply countPred_ext; intro k _; simp [Nat.add_mod]
      rw [hext]; rfl
    rw [hstep]

theorem countPred_gapped_masks (n : Nat) (hn : 6 ≤ n) :
    countPred (isGappedMask n) (2 ^ n) = 2 ^ (n - 3) - 4 := by
  have h2n : 2 ^ n = 8 * 2 ^ (n - 3) := two_pow_mul_split n 3 (by omega)
  have h2n1 : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    have h := two_pow_mul_split (n - 1) 2 (by omega)
    have hs : n - 1 - 2 = n - 3 := by omega
    rw [hs] at h; exact h
  have h2n1_8 : 2 ^ (n - 1) = 8 * 2 ^ (n - 4) := by
    have h := two_pow_mul_split (n - 1) 3 (by omega)
    have hs : n - 1 - 3 = n - 4 := by omega
    rw [hs] at h; exact h
  have hge8 : 8 ≤ 2 ^ (n - 3) := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
  let isExcl : Nat → Bool := fun f =>
    decide (f = 0 ∨ f = 8 ∨ f = 2 ^ (n - 1) ∨ f = 2 ^ (n - 1) + 8)
  have hsplit : ∀ lim,
      countPred (isGappedMask n) lim + countPred isExcl lim =
        countPred (fun f => f % 8 == 0) lim := by
    intro lim
    induction lim with
    | zero => rfl
    | succ f ih =>
      unfold countPred
      by_cases hex : f = 0 ∨ f = 8 ∨ f = 2 ^ (n - 1) ∨ f = 2 ^ (n - 1) + 8
      · have hdiv8 : f % 8 = 0 := by rcases hex with rfl | rfl | rfl | rfl <;> omega
        have hng : isGappedMask n f = false := by
          unfold isGappedMask
          rcases hex with rfl | rfl | rfl | rfl <;> simp
        have hexb : isExcl f = true := by simp [isExcl, hex]
        simp only [hng, hexb, hdiv8, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        omega
      · have hexb : isExcl f = false := decide_eq_false hex
        have hg_eq : isGappedMask n f = (f % 8 == 0) := by
          unfold isGappedMask
          have h1 : (f != 0) = true := bne_iff_ne.mpr (by omega)
          have h2 : (f != 8) = true := bne_iff_ne.mpr (by omega)
          have h3 : (f != 2 ^ (n - 1)) = true := bne_iff_ne.mpr (by omega)
          have h4 : (f != 2 ^ (n - 1) + 8) = true := bne_iff_ne.mpr (by omega)
          simp only [h1, h2, h3, h4, Bool.and_true]
        simp only [hexb, hg_eq, Bool.false_eq_true, ↓reduceIte]
        omega
  have hne0_t : (0 : Nat) ≠ 2 ^ (n - 1) := by omega
  have hne0_t8 : (0 : Nat) ≠ 2 ^ (n - 1) + 8 := by omega
  have hne8_t : (8 : Nat) ≠ 2 ^ (n - 1) := by omega
  have hne8_t8 : (8 : Nat) ≠ 2 ^ (n - 1) + 8 := by omega
  have hnet_t8 : 2 ^ (n - 1) ≠ 2 ^ (n - 1) + 8 := by omega
  have hex4 : countPred isExcl (2 ^ n) = 4 := by
    have hsum4 : ∀ lim,
        countPred isExcl lim =
          countPred (fun f => decide (f = 0)) lim +
          countPred (fun f => decide (f = 8)) lim +
          countPred (fun f => decide (f = 2 ^ (n - 1))) lim +
          countPred (fun f => decide (f = 2 ^ (n - 1) + 8)) lim := by
      intro lim
      induction lim with
      | zero => rfl
      | succ f ih =>
        unfold countPred; rw [ih]
        by_cases h0 : f = 0
        · have a1 : decide (f = 0) = true := decide_eq_true h0
          have a2 : decide (f = 8) = false := decide_eq_false (by omega)
          have a3 : decide (f = 2 ^ (n - 1)) = false := decide_eq_false (by omega)
          have a4 : decide (f = 2 ^ (n - 1) + 8) = false := decide_eq_false (by omega)
          have ae : isExcl f = true := decide_eq_true (Or.inl h0)
          simp only [ae, a1, a2, a3, a4, Bool.false_eq_true, ↓reduceIte]; omega
        · by_cases h8 : f = 8
          · have a1 : decide (f = 0) = false := decide_eq_false h0
            have a2 : decide (f = 8) = true := decide_eq_true h8
            have a3 : decide (f = 2 ^ (n - 1)) = false := decide_eq_false (by omega)
            have a4 : decide (f = 2 ^ (n - 1) + 8) = false := decide_eq_false (by omega)
            have ae : isExcl f = true := decide_eq_true (Or.inr (Or.inl h8))
            simp only [ae, a1, a2, a3, a4, Bool.false_eq_true, ↓reduceIte]; omega
          · by_cases ht : f = 2 ^ (n - 1)
            · have a1 : decide (f = 0) = false := decide_eq_false h0
              have a2 : decide (f = 8) = false := decide_eq_false h8
              have a3 : decide (f = 2 ^ (n - 1)) = true := decide_eq_true ht
              have a4 : decide (f = 2 ^ (n - 1) + 8) = false := decide_eq_false (by omega)
              have ae : isExcl f = true := decide_eq_true (Or.inr (Or.inr (Or.inl ht)))
              simp only [ae, a1, a2, a3, a4, Bool.false_eq_true, ↓reduceIte]; omega
            · by_cases ht8 : f = 2 ^ (n - 1) + 8
              · have a1 : decide (f = 0) = false := decide_eq_false h0
                have a2 : decide (f = 8) = false := decide_eq_false h8
                have a3 : decide (f = 2 ^ (n - 1)) = false := decide_eq_false ht
                have a4 : decide (f = 2 ^ (n - 1) + 8) = true := decide_eq_true ht8
                have ae : isExcl f = true := decide_eq_true (Or.inr (Or.inr (Or.inr ht8)))
                simp only [ae, a1, a2, a3, a4, Bool.false_eq_true, ↓reduceIte]; omega
              · simp [isExcl, h0, h8, ht, ht8]
    rw [hsum4, countPred_single, countPred_single, countPred_single, countPred_single]
    have hlt0 : 0 < 2 ^ n := by omega
    have hlt8 : 8 < 2 ^ n := by omega
    have hltt : 2 ^ (n - 1) < 2 ^ n := by omega
    have hltt8 : 2 ^ (n - 1) + 8 < 2 ^ n := by omega
    simp [hlt0, hlt8, hltt, hltt8]
  have hs := hsplit (2 ^ n)
  have hdiv_all : countPred (fun f => f % 8 == 0) (2 ^ n) = 2 ^ (n - 3) := by
    rw [h2n, countPred_div8]
  rw [hex4, hdiv_all] at hs
  omega

/-- **Theorem T5c (Complete All-$n$, All-Signature Spectral-Gap Dichotomy):**
    For EVERY $n \ge 6$:
    1. Every flip mask $f < 2^n$ exhibits an interior mod-4 spectral gap in $(0, 2^{n-1} - 4)$
       IF AND ONLY IF $8 \mid f$ and $f \notin \{0, 8, 2^{n-1}, 2^{n-1} + 8\}$.
    2. Exactly $2^{n-3} - 4$ out of all $2^n$ signatures exhibit an interior spectral gap. -/
theorem complete_spectral_gap_dichotomy_all_n (n : Nat) (hn : 6 ≤ n) :
    (∀ f, f < 2 ^ n → (hasInteriorMod4Gap n f ↔ isGappedMask n f = true)) ∧
    countPred (isGappedMask n) (2 ^ n) = 2 ^ (n - 3) - 4 := by
  refine ⟨?_, countPred_gapped_masks n hn⟩
  intro f hf
  constructor
  · intro hgap
    cases hg : isGappedMask n f
    · exact absurd hgap (non_gapped_mask_no_interior_gap n f hn hf hg)
    · rfl
  · exact gapped_mask_has_interior_gap n f hn hf

end

end CDTerrace
