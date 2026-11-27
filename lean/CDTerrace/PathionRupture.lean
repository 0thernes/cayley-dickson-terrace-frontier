module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue
public import CDTerrace.Basic
public import CDTerrace.MirrorConservation
public import CDTerrace.TerraceLaw
public import CDTerrace.HurwitzRupture
public import CDTerrace.FiniteCertificates

/-!
# CDTerrace.PathionRupture — Exact Pathion Ceiling $r_{\max}(\mathrm{CD}_5) = 14$ ($7+7$ Rigidity) & Dimension-64 Split Spectral Gap

Proves in zero-Mathlib, strictly constructive Lean 4.35.0 (`0` `sorry`, `0` `native_decide`,
`0` custom axioms, zero `maxRecDepth`/`maxHeartbeats` overrides, zero MILP solvers in the trust base):
- **Universal Half-Swap Symmetry (`cdSign_halfSwap`, `pairingCancels_halfSwap`):**
  For EVERY $n \ge 1$, the half-swap involution $x \mapsto x \oplus 2^n$ preserves bilinear
  norm cancellation `pairingCancels (n + 1)` across every affine 2-plane in $\mathrm{CD}_{n+1}$.
- **Theorem T4e (`pathion_exact_ceiling_14_and_7_7_rigidity`):**
  Pure-kernel proof over ALL $2^{32} = 4{,}294{,}967{,}296$ coordinate subsets of the 32-dimensional
  Pathions $\mathrm{CD}_5$ (and over ALL duplicate-free lists `S : List Nat` satisfying
  `isNormMultPair 5 S S`) using a fixed-descending (`15..0`) greedy clique-cover certificate on
  the 2,995 valid lower halves with $|S_{\mathrm{lo}}| \ge 8$:
  1. Every norm-multiplicative coordinate subset of $\mathrm{CD}_5$ satisfies $|S| \le 14$
     (establishing $r_{\max}(\mathrm{CD}_5) = 14$ together with `pathionWitness14`, retiring HiGHS
     MILP completely from the proof trust base!).
  2. **Strict $7 + 7$ Half-Balance Rigidity:** Every 14-dimensional norm-multiplicative coordinate
     subset of $\mathrm{CD}_5$ splits strictly evenly with $7$ elements in $\{0..15\}$ and
     $7$ elements in $\{16..31\}$ (no unbalanced $8 + 6$, $9 + 5$, or $10 + 4$ 14D subset exists!).
- **Theorem T4f (`cd6_split56_interior_spectral_gap`):**
  Complete pure-kernel 9-bin 2-blade nullity histogram certification for the dimension-64 split
  Chingon algebra $\mathrm{CD}_6(\gamma)$ at `flipMask = 56`, proving the emergence of an
  interior spectral gap at dimension 64:
  $H_6^{56}(16) = 168$, **$H_6^{56}(20) = 0$**, $H_6^{56}(24) = 56$.
-/

namespace CDTerrace

public section

/-! ### Part 1: Universal All-$n$ Half-Swap Invariance of Bilinear Norm Cancellation -/

/-- Exact sign factor relating $\sigma_{n+1}(x \oplus 2^n, y \oplus 2^n)$ to $\sigma_{n+1}(x, y)$
    for all distinct $x, y < 2^{n+1}$. -/
@[expose] def halfSwapSign (n x y : Nat) : Int :=
  (if decide (x < 2 ^ n) == decide (y < 2 ^ n) then -1 else 1) *
  (if x == 0 || x == 2 ^ n then -1 else 1) *
  (if (x ^^^ y) == 2 ^ n then -1 else 1)

theorem xor_half_eq {n x : Nat} (hx : x < 2 ^ (n + 1)) :
    x ^^^ 2 ^ n = if x < 2 ^ n then x + 2 ^ n else x - 2 ^ n := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hlt : x < 2 ^ n
  · simp only [hlt, ↓reduceIte]
    have h := xor_add_right hlt (Nat.two_pow_pos n)
    simpa using h
  · simp only [hlt, ↓reduceIte]
    let a := x - 2 ^ n
    have hxa : x = a + 2 ^ n := by omega
    have halt : a < 2 ^ n := by omega
    rw [hxa]
    have h := xor_add_both halt (Nat.two_pow_pos n)
    simpa using h

/-- **Universal All-$n$ Half-Swap Sign Formula:**
    For every $n \ge 1$ and all distinct $x, y < 2^{n+1}$,
    $\sigma_{n+1}(x \oplus 2^n, y \oplus 2^n) = \sigma_{n+1}(x, y) \cdot \mathrm{halfSwapSign}(n, x, y)$. -/
theorem cdSign_halfSwap (n x y : Nat) (hx : x < 2 ^ (n + 1)) (hy : y < 2 ^ (n + 1)) (hne : x ≠ y) :
    cdSign (n + 1) (x ^^^ 2 ^ n) (y ^^^ 2 ^ n) =
      cdSign (n + 1) x y * halfSwapSign n x y := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [xor_half_eq hx, xor_half_eq hy]
  unfold halfSwapSign
  by_cases hxh : x < 2 ^ n <;> by_cases hyh : y < 2 ^ n
  · simp only [hxh, hyh, decide_true, beq_self_eq_true, ↓reduceIte]
    have hne_h : (x ^^^ y == 2 ^ n) = false := by
      apply beq_false_of_ne
      have hlt : x ^^^ y < 2 ^ n := Nat.xor_lt_two_pow hxh hyh
      omega
    have hxne_h : (x == 2 ^ n) = false := beq_false_of_ne (by omega)
    rw [cdSign_succ_ll n x y hxh hyh, cdSign_succ_hh n x y]
    simp only [hxne_h, hne_h, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
    by_cases hx0 : x = 0
    · subst hx0
      have hy0 : y ≠ 0 := Ne.symm hne
      simp only [hy0, beq_self_eq_true, ↓reduceIte, cdSign_zero_left n y hyh, cdSign_zero_right n y hyh]
      rfl
    · have hx0b : (x == 0) = false := beq_false_of_ne hx0
      simp only [hx0b, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
      by_cases hy0 : y = 0
      · subst hy0
        simp only [↓reduceIte, cdSign_zero_right n x hxh, cdSign_zero_left n x hxh]; rfl
      · simp only [hy0, ↓reduceIte]
        rw [cdSign_anticomm n y x (by omega) (by omega) hyh hxh (Ne.symm hne)]
        omega
  · obtain ⟨b, hblt, hyb⟩ : ∃ b, b < 2 ^ n ∧ y = b + 2 ^ n := ⟨y - 2 ^ n, by omega, by omega⟩
    have hx_sub : y - 2 ^ n = b := by omega
    simp only [hxh, hyh, decide_true, decide_false, ↓reduceIte, hx_sub]
    have htf : (true == false) = false := rfl
    have hxne_h : (x == 2 ^ n) = false := beq_false_of_ne (by omega)
    rw [hyb, cdSign_succ_lh n x b hxh, cdSign_succ_hl n x b hblt]
    simp only [htf, hxne_h, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
    have hxor_xb : x ^^^ (b + 2 ^ n) = (x ^^^ b) + 2 ^ n := xor_add_right hxh hblt
    rw [hxor_xb]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [beq_self_eq_true, Nat.zero_xor, ↓reduceIte, cdSign_zero_right n b hblt, cdSign_zero_left n b hblt]
      by_cases hb0 : b = 0
      · subst hb0; simp [cdSign_zero_left n 0 hpow]
      · have hne1 : (b + 2 ^ n == 2 ^ n) = false := beq_false_of_ne (by omega)
        simp [hb0, hne1]
    · have hx0b : (x == 0) = false := beq_false_of_ne hx0
      simp only [hx0b, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
      by_cases hb0 : b = 0
      · subst hb0
        have hne1 : ((x ^^^ 0) + 2 ^ n == 2 ^ n) = false := beq_false_of_ne (by rw [Nat.xor_zero]; omega)
        simp only [hne1, Bool.false_eq_true, ↓reduceIte, cdSign_zero_left n x hxh, cdSign_zero_right n x hxh]
        rfl
      · simp only [hb0, ↓reduceIte]
        by_cases hxb : x = b
        · subst hxb
          simp only [Nat.xor_self, Nat.zero_add, beq_self_eq_true, ↓reduceIte, cdSign_diag n x (by omega) hxh]
          rfl
        · have hne1 : ((x ^^^ b) + 2 ^ n == 2 ^ n) = false := by
            apply beq_false_of_ne
            have hnz : x ^^^ b ≠ 0 := fun h => hxb (eq_of_xor_eq_zero h)
            omega
          simp only [hne1, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
          rw [cdSign_anticomm n b x (by omega) (by omega) hblt hxh (Ne.symm hxb)]
  · obtain ⟨a, halt, hxa⟩ : ∃ a, a < 2 ^ n ∧ x = a + 2 ^ n := ⟨x - 2 ^ n, by omega, by omega⟩
    have ha_sub : x - 2 ^ n = a := by omega
    simp only [hxh, hyh, decide_true, decide_false, ↓reduceIte, ha_sub]
    have hft : (false == true) = false := rfl
    have hane_0 : (a + 2 ^ n == 0) = false := beq_false_of_ne (by omega)
    rw [hxa, cdSign_succ_hl n a y hyh, cdSign_succ_lh n a y halt]
    simp only [hft, hane_0, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
    have hxor_ay : (a + 2 ^ n) ^^^ y = (a ^^^ y) + 2 ^ n := xor_add_left halt hyh
    rw [hxor_ay]
    by_cases ha0 : a = 0
    · subst ha0
      simp only [Nat.zero_add, beq_self_eq_true, Nat.zero_xor, ↓reduceIte,
                 cdSign_zero_left n y hyh, cdSign_zero_right n y hyh]
      by_cases hy0 : y = 0
      · subst hy0; simp [cdSign_zero_left n 0 hpow]
      · have hne1 : (y + 2 ^ n == 2 ^ n) = false := beq_false_of_ne (by omega)
        simp [hy0, hne1]
    · have hne_h : (a + 2 ^ n == 2 ^ n) = false := beq_false_of_ne (by omega)
      simp only [hne_h, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
      by_cases hy0 : y = 0
      · subst hy0
        have hne1 : ((a ^^^ 0) + 2 ^ n == 2 ^ n) = false := beq_false_of_ne (by rw [Nat.xor_zero]; omega)
        simp only [hne1, Bool.false_eq_true, ↓reduceIte, cdSign_zero_right n a halt, cdSign_zero_left n a halt]
        rfl
      · simp only [hy0, ↓reduceIte]
        by_cases hay : a = y
        · subst hay
          simp only [Nat.xor_self, Nat.zero_add, beq_self_eq_true, ↓reduceIte, cdSign_diag n a (by omega) halt]
          rfl
        · have hne1 : ((a ^^^ y) + 2 ^ n == 2 ^ n) = false := by
            apply beq_false_of_ne
            have hnz : a ^^^ y ≠ 0 := fun h => hay (eq_of_xor_eq_zero h)
            omega
          simp only [hne1, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
          rw [cdSign_anticomm n y a (by omega) (by omega) hyh halt (Ne.symm hay)]
  · obtain ⟨a, halt, hxa⟩ : ∃ a, a < 2 ^ n ∧ x = a + 2 ^ n := ⟨x - 2 ^ n, by omega, by omega⟩
    obtain ⟨b, hblt, hyb⟩ : ∃ b, b < 2 ^ n ∧ y = b + 2 ^ n := ⟨y - 2 ^ n, by omega, by omega⟩
    have ha_sub : x - 2 ^ n = a := by omega
    have hb_sub : y - 2 ^ n = b := by omega
    have hab_ne : a ≠ b := by omega
    simp only [hxh, hyh, decide_false, beq_self_eq_true, ↓reduceIte, ha_sub, hb_sub]
    have hane_0 : (a + 2 ^ n == 0) = false := beq_false_of_ne (by omega)
    have hxor_ab : (a + 2 ^ n) ^^^ (b + 2 ^ n) = a ^^^ b := xor_add_both halt hblt
    have hne_h : (a ^^^ b == 2 ^ n) = false := by
      apply beq_false_of_ne
      have hlt : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow halt hblt
      omega
    rw [hxa, hyb, hxor_ab, cdSign_succ_ll n a b halt hblt, cdSign_succ_hh n a b]
    simp only [hane_0, Bool.false_or, hne_h, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b ≠ 0 := Ne.symm hab_ne
      simp only [Nat.zero_add, beq_self_eq_true, hb0, ↓reduceIte,
                 cdSign_zero_left n b hblt, cdSign_zero_right n b hblt]
      rfl
    · have hne_ah : (a + 2 ^ n == 2 ^ n) = false := beq_false_of_ne (by omega)
      simp only [hne_ah, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
      by_cases hb0 : b = 0
      · subst hb0
        simp only [↓reduceIte, cdSign_zero_right n a halt, cdSign_zero_left n a halt]; rfl
      · simp only [hb0, ↓reduceIte]
        rw [cdSign_anticomm n b a (by omega) (by omega) hblt halt (Ne.symm hab_ne)]
        omega

/-- **Universal All-$n$ Half-Swap Invariance of `pairingCancels`:**
    For EVERY $n \ge 1$ and all distinct $a, b, c, d < 2^{n+1}$ with $a \oplus b = c \oplus d$,
    `pairingCancels (n + 1)` is invariant under swapping all 4 indices by $\oplus 2^n$. -/
theorem pairingCancels_halfSwap (n a b c d : Nat)
    (ha : a < 2 ^ (n + 1)) (hb : b < 2 ^ (n + 1)) (hc : c < 2 ^ (n + 1)) (hd : d < 2 ^ (n + 1))
    (hac : a ≠ c) (hbd : b ≠ d) (had : a ≠ d) (hbc : b ≠ c) (hxor : a ^^^ b = c ^^^ d) :
    pairingCancels (n + 1) (a ^^^ 2 ^ n) (b ^^^ 2 ^ n) (c ^^^ 2 ^ n) (d ^^^ 2 ^ n) =
      pairingCancels (n + 1) a b c d := by
  unfold pairingCancels
  rw [cdSign_halfSwap n a c ha hc hac, cdSign_halfSwap n b d hb hd hbd,
      cdSign_halfSwap n a d ha hd had, cdSign_halfSwap n b c hb hc hbc]
  have heq_ac_bd : a ^^^ c = b ^^^ d := by
    have h1 := congrArg (fun z => z ^^^ b ^^^ c) hxor
    have hL : (a ^^^ b) ^^^ b ^^^ c = a ^^^ c := by rw [xor_sub_self_cancel]
    have hR : (c ^^^ d) ^^^ b ^^^ c = b ^^^ d := by
      apply Nat.eq_of_testBit_eq; intro m
      simp only [Nat.testBit_xor]
      cases c.testBit m <;> cases d.testBit m <;> cases b.testBit m <;> rfl
    rw [hL, hR] at h1; exact h1
  have heq_ad_bc : a ^^^ d = b ^^^ c := by
    have h1 := congrArg (fun z => z ^^^ b ^^^ d) hxor
    have hL : (a ^^^ b) ^^^ b ^^^ d = a ^^^ d := by rw [xor_sub_self_cancel]
    have hR : (c ^^^ d) ^^^ b ^^^ d = b ^^^ c := by
      apply Nat.eq_of_testBit_eq; intro m
      simp only [Nat.testBit_xor]
      cases c.testBit m <;> cases d.testBit m <;> cases b.testBit m <;> rfl
    rw [hL, hR] at h1; exact h1
  have hprod_eq : halfSwapSign n a c * halfSwapSign n b d =
                  halfSwapSign n a d * halfSwapSign n b c := by
    unfold halfSwapSign
    rw [heq_ac_bd, heq_ad_bc]
    cases decide (a < 2 ^ n) <;> cases decide (b < 2 ^ n) <;>
    cases decide (c < 2 ^ n) <;> cases decide (d < 2 ^ n) <;>
    cases (a == 0 || a == 2 ^ n) <;> cases (b == 0 || b == 2 ^ n) <;>
    cases ((b ^^^ d) == 2 ^ n) <;> cases ((b ^^^ c) == 2 ^ n) <;> rfl
  have hhs_pm1 : ∀ x y, halfSwapSign n x y = 1 ∨ halfSwapSign n x y = -1 := by
    intro x y; unfold halfSwapSign
    cases (decide (x < 2 ^ n) == decide (y < 2 ^ n)) <;>
    cases (x == 0 || x == 2 ^ n) <;>
    cases ((x ^^^ y) == 2 ^ n) <;> decide
  have hrearr1 :
      (cdSign (n + 1) a c * halfSwapSign n a c) * (cdSign (n + 1) b d * halfSwapSign n b d) =
      (cdSign (n + 1) a c * cdSign (n + 1) b d) * (halfSwapSign n a c * halfSwapSign n b d) := by
    ac_rfl
  have hrearr2 :
      (cdSign (n + 1) a d * halfSwapSign n a d) * (cdSign (n + 1) b c * halfSwapSign n b c) =
      (cdSign (n + 1) a d * cdSign (n + 1) b c) * (halfSwapSign n a d * halfSwapSign n b c) := by
    ac_rfl
  rw [hrearr1, hrearr2, hprod_eq]
  rcases hhs_pm1 a d with h1 | h1 <;> rcases hhs_pm1 b c with h2 | h2 <;>
  rcases cdSign_val_pm1 (n + 1) a c with s1 | s1 <;>
  rcases cdSign_val_pm1 (n + 1) b d with s2 | s2 <;>
  rcases cdSign_val_pm1 (n + 1) a d with s3 | s3 <;>
  rcases cdSign_val_pm1 (n + 1) b c with s4 | s4 <;>
  simp [h1, h2, s1, s2, s3, s4]

/-- 32-bit population count using C-primitive `popcount16`. -/
@[expose] def popcount32 (m : Nat) : Nat :=
  popcount16 (m % 65536) + popcount16 (m / 65536)

theorem testBit_lo_hi16 (lo hi k : Nat) (hlo : lo < 65536) :
    (lo + 65536 * hi).testBit k =
      if k < 16 then lo.testBit k else hi.testBit (k - 16) := by
  have h65 : (65536 : Nat) = 2 ^ 16 := rfl
  rw [h65]
  by_cases hk : k < 16
  · simp only [hk, ↓reduceIte]
    have hmod : (lo + 2 ^ 16 * hi) % 2 ^ 16 = lo := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    have htb : ((lo + 2 ^ 16 * hi) % 2 ^ 16).testBit k = (lo + 2 ^ 16 * hi).testBit k := by
      rw [Nat.testBit_mod_two_pow]; simp [hk]
    rw [← htb, hmod]
  · simp only [hk, ↓reduceIte]
    have hdiv : (lo + 2 ^ 16 * hi) / 2 ^ 16 = hi := by
      rw [Nat.add_mul_div_left lo hi (Nat.two_pow_pos 16), Nat.div_eq_of_lt hlo, Nat.zero_add]
    have hsub : k = (k - 16) + 16 := by omega
    conv => lhs; rw [hsub]
    rw [← Nat.testBit_div_two_pow, hdiv]

theorem isNormMultMask5_swap16 (lo hi : Nat) (hlo : lo < 65536) (hhi : hi < 65536)
    (hnm : isNormMultMask 5 (lo + 65536 * hi) = true) :
    isNormMultMask 5 (hi + 65536 * lo) = true := by
  have hbit_swap : ∀ x, x < 32 →
      (hi + 65536 * lo).testBit x = (lo + 65536 * hi).testBit (x ^^^ 16) := by
    intro x hx
    rw [testBit_lo_hi16 hi lo x hhi, testBit_lo_hi16 lo hi (x ^^^ 16) hlo,
        show (16 : Nat) = 2 ^ 4 from rfl, xor_half_eq (n := 4) hx]
    by_cases hx16 : x < 16
    · have hge : ¬(x + 16 < 16) := by omega
      have hsub : x + 16 - 16 = x := by omega
      simp [hx16, hge, hsub]
    · have hlt : x - 16 < 16 := by omega
      simp [hx16, hlt]
  have hpair_true : ∀ a b c, a < 32 → b < 32 → c < 32 → a ≠ b → c ≠ a → c ≠ b →
      (lo + 65536 * hi).testBit a = true → (lo + 65536 * hi).testBit b = true →
      (lo + 65536 * hi).testBit c = true → (lo + 65536 * hi).testBit (a ^^^ b ^^^ c) = true →
      pairingCancels 5 a b c (a ^^^ b ^^^ c) = true := by
    intro a b c ha hb hc hab hca hcb hta htb htc htd
    have hpc_symm_ab : ∀ x y z w, pairingCancels 5 y x z w = pairingCancels 5 x y z w := by
      intro x y z w; unfold pairingCancels; rw [Int.add_comm, Int.mul_comm (cdSign 5 y z), Int.mul_comm (cdSign 5 y w)]
    have hpc_symm_cd : ∀ x y z w, pairingCancels 5 x y w z = pairingCancels 5 x y z w := by
      intro x y z w; unfold pairingCancels; rw [Int.add_comm]
    have hfrom : ∀ x y z, x < y → y < 32 → z < 32 → z ≠ x → z ≠ y → z < (x ^^^ y ^^^ z) →
        (lo + 65536 * hi).testBit x = true → (lo + 65536 * hi).testBit y = true →
        (lo + 65536 * hi).testBit z = true → (lo + 65536 * hi).testBit (x ^^^ y ^^^ z) = true →
        pairingCancels 5 x y z (x ^^^ y ^^^ z) = true := by
      intro x y z hxy hy hz hzx hzy hzd htx hty htz htw
      unfold isNormMultMask at hnm
      have h1 := (allNat_eq_true _ 32).mp hnm x (by omega)
      simp only [htx, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
      have h2 := (allNat_eq_true _ 32).mp h1 y hy
      simp only [hxy, hty, decide_true, Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2
      have h3 := (allNat_eq_true _ 32).mp h2 z hz
      have hne1 : (z != x) = true := bne_iff_ne.mpr hzx
      have hne2 : (z != y) = true := bne_iff_ne.mpr hzy
      have hdw : (x ^^^ y ^^^ z) < 32 := Nat.xor_lt_two_pow (n := 5) (Nat.xor_lt_two_pow (n := 5) (by omega) hy) hz
      simp only [htz, hne1, hne2, hzd, hdw, htw, decide_true, Bool.and_true, Bool.not_true,
                 Bool.false_eq_true, ↓reduceIte] at h3
      exact h3
    let d := a ^^^ b ^^^ c
    have hdlt : d < 32 := Nat.xor_lt_two_pow (n := 5) (Nat.xor_lt_two_pow (n := 5) ha hb) hc
    have hcd_ne : c ≠ d := by
      intro h; apply hab
      have : a ^^^ b = 0 := by
        have h1 := congrArg (· ^^^ c) h
        rw [Nat.xor_self, xor_sub_self_cancel] at h1; exact h1.symm
      exact eq_of_xor_eq_zero this
    have hda : d ≠ a := by
      intro h; apply hcb
      have : b ^^^ c = 0 := by
        have h1 := congrArg (· ^^^ a) h
        have hL : (a ^^^ b ^^^ c) ^^^ a = b ^^^ c := by
          apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
          cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> rfl
        rw [hL, Nat.xor_self] at h1; exact h1
      exact (eq_of_xor_eq_zero this).symm
    have hdb : d ≠ b := by
      intro h; apply hca
      have : a ^^^ c = 0 := by
        have h1 := congrArg (· ^^^ b) h
        have hL : (a ^^^ b ^^^ c) ^^^ b = a ^^^ c := by
          apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
          cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> rfl
        rw [hL, Nat.xor_self] at h1; exact h1
      exact (eq_of_xor_eq_zero this).symm
    have hdxor : a ^^^ b ^^^ d = c := by
      show a ^^^ b ^^^ (a ^^^ b ^^^ c) = c
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    have hbxor : b ^^^ a ^^^ c = d := by rw [Nat.xor_comm b a]
    have hbdxor : b ^^^ a ^^^ d = c := by rw [Nat.xor_comm b a]; exact hdxor
    change pairingCancels 5 a b c d = true
    by_cases hlt_ab : a < b <;> by_cases hlt_cd : c < d
    · exact hfrom a b c hlt_ab hb hc hca hcb hlt_cd hta htb htc htd
    · have hdc : d < c := by omega
      rw [← hpc_symm_cd a b c d, ← hdxor]
      exact hfrom a b d hlt_ab hb hdlt hda hdb (by rw [hdxor]; exact hdc) hta htb htd (by rw [hdxor]; exact htc)
    · have hba : b < a := by omega
      rw [← hpc_symm_ab a b c d, ← hbxor]
      exact hfrom b a c hba ha hc hcb hca (by rw [hbxor]; exact hlt_cd) htb hta htc (by rw [hbxor]; exact htd)
    · have hba : b < a := by omega
      have hdc : d < c := by omega
      rw [← hpc_symm_ab a b c d, ← hpc_symm_cd b a c d, ← hbdxor]
      exact hfrom b a d hba ha hdlt hdb hda (by rw [hbdxor]; exact hdc) htb hta htd (by rw [hbdxor]; exact htc)
  unfold isNormMultMask
  rw [allNat_eq_true]; intro a ha
  by_cases hta : (hi + 65536 * lo).testBit a = true
  · simp only [hta, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [allNat_eq_true]; intro b hb
    by_cases hcond_b : (a < b && (hi + 65536 * lo).testBit b) = true
    · simp only [hcond_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond_b
      rw [allNat_eq_true]; intro c hc
      by_cases hcond_c : ((hi + 65536 * lo).testBit c && c != a && c != b) = true
      · simp only [hcond_c, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.and_eq_true, bne_iff_ne] at hcond_c
        let d := a ^^^ b ^^^ c
        change (if !(decide (c < d) && decide (d < 2 ^ 5) && (hi + 65536 * lo).testBit d) then true
                else pairingCancels 5 a b c d) = true
        by_cases hcond_d : (decide (c < d) && decide (d < 2 ^ 5) && (hi + 65536 * lo).testBit d) = true
        · simp only [hcond_d, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond_d
          have hd_xor : a ^^^ b = c ^^^ d := by
            show a ^^^ b = c ^^^ (a ^^^ b ^^^ c)
            apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
            cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> rfl
          have hd_ne_a : a ≠ d := by
            intro h
            have : b ^^^ c = 0 := by
              have h1 := congrArg (· ^^^ a) h.symm
              have hL : (a ^^^ b ^^^ c) ^^^ a = b ^^^ c := by
                apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
                cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> rfl
              rw [hL, Nat.xor_self] at h1; exact h1
            exact hcond_c.2 (eq_of_xor_eq_zero this).symm
          have hd_ne_b : b ≠ d := by
            intro h
            have : a ^^^ c = 0 := by
              have h1 := congrArg (· ^^^ b) h.symm
              have hL : (a ^^^ b ^^^ c) ^^^ b = a ^^^ c := by
                apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
                cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> rfl
              rw [hL, Nat.xor_self] at h1; exact h1
            exact hcond_c.1.2 (eq_of_xor_eq_zero this).symm
          rw [← pairingCancels_halfSwap 4 a b c d ha hb hc hcond_d.1.2
              (Ne.symm hcond_c.1.2) hd_ne_b hd_ne_a (Ne.symm hcond_c.2) hd_xor]
          have hd16 : d ^^^ 16 = (a ^^^ 16) ^^^ (b ^^^ 16) ^^^ (c ^^^ 16) := by
            show (a ^^^ b ^^^ c) ^^^ 16 = (a ^^^ 16) ^^^ (b ^^^ 16) ^^^ (c ^^^ 16)
            apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
            cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> cases (16 : Nat).testBit m <;> rfl
          have h16lt : ∀ z, z < 32 → z ^^^ 16 < 32 := fun z hz => Nat.xor_lt_two_pow (n := 5) hz (by decide)
          have hne_sw : ∀ x y, x ≠ y → x ^^^ 16 ≠ y ^^^ 16 := by
            intro x y hxy heq
            have := congrArg (· ^^^ 16) heq
            rw [xor_sub_self_cancel, xor_sub_self_cancel] at this; exact hxy this
          rw [show (2 ^ 4 : Nat) = 16 from rfl, hd16]
          exact hpair_true (a ^^^ 16) (b ^^^ 16) (c ^^^ 16)
            (h16lt a ha) (h16lt b hb) (h16lt c hc)
            (hne_sw a b (by omega)) (hne_sw c a hcond_c.1.2) (hne_sw c b hcond_c.2)
            (by rw [← hbit_swap a ha]; exact hta)
            (by rw [← hbit_swap b hb]; exact hcond_b.2)
            (by rw [← hbit_swap c hc]; exact hcond_c.1.1)
            (by rw [← hd16, ← hbit_swap d hcond_d.1.2]; exact hcond_d.2)
        · simp only [Bool.eq_false_iff.mpr hcond_d, Bool.not_false, ↓reduceIte]
      · simp [Bool.eq_false_iff.mpr hcond_c]
    · simp [Bool.eq_false_iff.mpr hcond_b]
  · simp [Bool.eq_false_iff.mpr hta]

/-! ### Part 2: Exact Cross-Half Bad-Plane Table & Greedy Clique-Cover Certificate for $\mathrm{CD}_5$ -/

/-- Exact table of cross-half bad pairs `(a, b)` ($a < b < 16$, $a \oplus b = u \oplus v$)
    causing `pairingCancels 5 a (v + 16) b (u + 16) = false` for $1 \le v < u < 16$. -/
@[expose] def crossBadPairs : Nat → Nat → List (Nat × Nat)
  | 2, 1 => [(4, 7), (5, 6), (8, 11), (9, 10)]
  | 3, 1 => [(4, 6), (5, 7), (8, 10), (9, 11)]
  | 3, 2 => [(4, 5), (6, 7), (8, 9), (10, 11)]
  | 4, 1 => [(2, 7), (3, 6), (8, 13), (9, 12)]
  | 4, 2 => [(1, 7), (3, 5), (8, 14), (10, 12)]
  | 4, 3 => [(1, 6), (2, 5), (8, 15), (11, 12)]
  | 5, 1 => [(2, 6), (3, 7), (8, 12), (9, 13)]
  | 5, 2 => [(1, 6), (3, 4), (8, 15), (10, 13)]
  | 5, 3 => [(1, 7), (2, 4), (8, 14), (11, 13)]
  | 5, 4 => [(2, 3), (6, 7), (8, 9), (12, 13)]
  | 6, 1 => [(2, 5), (3, 4), (8, 15), (9, 14)]
  | 6, 2 => [(1, 5), (3, 7), (8, 12), (10, 14)]
  | 6, 3 => [(1, 4), (2, 7), (8, 13), (11, 14)]
  | 6, 4 => [(1, 3), (5, 7), (8, 10), (12, 14)]
  | 6, 5 => [(1, 2), (4, 7), (8, 11), (13, 14)]
  | 7, 1 => [(2, 4), (3, 5), (8, 14), (9, 15)]
  | 7, 2 => [(1, 4), (3, 6), (8, 13), (10, 15)]
  | 7, 3 => [(1, 5), (2, 6), (8, 12), (11, 15)]
  | 7, 4 => [(1, 2), (5, 6), (8, 11), (12, 15)]
  | 7, 5 => [(1, 3), (4, 6), (8, 10), (13, 15)]
  | 7, 6 => [(2, 3), (4, 5), (8, 9), (14, 15)]
  | 8, 1 => [(2, 11), (3, 10), (4, 13), (5, 12), (6, 15), (7, 14)]
  | 8, 2 => [(1, 11), (3, 9), (4, 14), (5, 15), (6, 12), (7, 13)]
  | 8, 3 => [(1, 10), (2, 9), (4, 15), (5, 14), (6, 13), (7, 12)]
  | 8, 4 => [(1, 13), (2, 14), (3, 15), (5, 9), (6, 10), (7, 11)]
  | 8, 5 => [(1, 12), (2, 15), (3, 14), (4, 9), (6, 11), (7, 10)]
  | 8, 6 => [(1, 15), (2, 12), (3, 13), (4, 10), (5, 11), (7, 9)]
  | 8, 7 => [(1, 14), (2, 13), (3, 12), (4, 11), (5, 10), (6, 9)]
  | 9, 1 => [(2, 10), (3, 11), (4, 12), (5, 13), (6, 14), (7, 15)]
  | 9, 2 => [(1, 10), (3, 8), (4, 15), (5, 14), (6, 13), (7, 12)]
  | 9, 3 => [(1, 11), (2, 8), (4, 14), (5, 15), (6, 12), (7, 13)]
  | 9, 4 => [(1, 12), (2, 15), (3, 14), (5, 8), (6, 11), (7, 10)]
  | 9, 5 => [(1, 13), (2, 14), (3, 15), (4, 8), (6, 10), (7, 11)]
  | 9, 6 => [(1, 14), (2, 13), (3, 12), (4, 11), (5, 10), (7, 8)]
  | 9, 7 => [(1, 15), (2, 12), (3, 13), (4, 10), (5, 11), (6, 8)]
  | 9, 8 => [(2, 3), (4, 5), (6, 7), (10, 11), (12, 13), (14, 15)]
  | 10, 1 => [(2, 9), (3, 8), (4, 15), (5, 14), (6, 13), (7, 12)]
  | 10, 2 => [(1, 9), (3, 11), (4, 12), (5, 13), (6, 14), (7, 15)]
  | 10, 3 => [(1, 8), (2, 11), (4, 13), (5, 12), (6, 15), (7, 14)]
  | 10, 4 => [(1, 15), (2, 12), (3, 13), (5, 11), (6, 8), (7, 9)]
  | 10, 5 => [(1, 14), (2, 13), (3, 12), (4, 11), (6, 9), (7, 8)]
  | 10, 6 => [(1, 13), (2, 14), (3, 15), (4, 8), (5, 9), (7, 11)]
  | 10, 7 => [(1, 12), (2, 15), (3, 14), (4, 9), (5, 8), (6, 11)]
  | 10, 8 => [(1, 3), (4, 6), (5, 7), (9, 11), (12, 14), (13, 15)]
  | 10, 9 => [(1, 2), (8, 11), (12, 15), (13, 14)]
  | 11, 1 => [(2, 8), (3, 9), (4, 14), (5, 15), (6, 12), (7, 13)]
  | 11, 2 => [(1, 8), (3, 10), (4, 13), (5, 12), (6, 15), (7, 14)]
  | 11, 3 => [(1, 9), (2, 10), (4, 12), (5, 13), (6, 14), (7, 15)]
  | 11, 4 => [(1, 14), (2, 13), (3, 12), (5, 10), (6, 9), (7, 8)]
  | 11, 5 => [(1, 15), (2, 12), (3, 13), (4, 10), (6, 8), (7, 9)]
  | 11, 6 => [(1, 12), (2, 15), (3, 14), (4, 9), (5, 8), (7, 10)]
  | 11, 7 => [(1, 13), (2, 14), (3, 15), (4, 8), (5, 9), (6, 10)]
  | 11, 8 => [(1, 2), (4, 7), (5, 6), (9, 10), (12, 15), (13, 14)]
  | 11, 9 => [(1, 3), (8, 10), (12, 14), (13, 15)]
  | 11, 10 => [(2, 3), (8, 9), (12, 13), (14, 15)]
  | 12, 1 => [(2, 15), (3, 14), (4, 9), (5, 8), (6, 11), (7, 10)]
  | 12, 2 => [(1, 15), (3, 13), (4, 10), (5, 11), (6, 8), (7, 9)]
  | 12, 3 => [(1, 14), (2, 13), (4, 11), (5, 10), (6, 9), (7, 8)]
  | 12, 4 => [(1, 9), (2, 10), (3, 11), (5, 13), (6, 14), (7, 15)]
  | 12, 5 => [(1, 8), (2, 11), (3, 10), (4, 13), (6, 15), (7, 14)]
  | 12, 6 => [(1, 11), (2, 8), (3, 9), (4, 14), (5, 15), (7, 13)]
  | 12, 7 => [(1, 10), (2, 9), (3, 8), (4, 15), (5, 14), (6, 13)]
  | 12, 8 => [(1, 5), (2, 6), (3, 7), (9, 13), (10, 14), (11, 15)]
  | 12, 9 => [(1, 4), (8, 13), (10, 15), (11, 14)]
  | 12, 10 => [(2, 4), (8, 14), (9, 15), (11, 13)]
  | 12, 11 => [(3, 4), (8, 15), (9, 14), (10, 13)]
  | 13, 1 => [(2, 14), (3, 15), (4, 8), (5, 9), (6, 10), (7, 11)]
  | 13, 2 => [(1, 14), (3, 12), (4, 11), (5, 10), (6, 9), (7, 8)]
  | 13, 3 => [(1, 15), (2, 12), (4, 10), (5, 11), (6, 8), (7, 9)]
  | 13, 4 => [(1, 8), (2, 11), (3, 10), (5, 12), (6, 15), (7, 14)]
  | 13, 5 => [(1, 9), (2, 10), (3, 11), (4, 12), (6, 14), (7, 15)]
  | 13, 6 => [(1, 10), (2, 9), (3, 8), (4, 15), (5, 14), (7, 12)]
  | 13, 7 => [(1, 11), (2, 8), (3, 9), (4, 14), (5, 15), (6, 12)]
  | 13, 8 => [(1, 4), (2, 7), (3, 6), (9, 12), (10, 15), (11, 14)]
  | 13, 9 => [(1, 5), (8, 12), (10, 14), (11, 15)]
  | 13, 10 => [(2, 5), (8, 15), (9, 14), (11, 12)]
  | 13, 11 => [(3, 5), (8, 14), (9, 15), (10, 12)]
  | 13, 12 => [(4, 5), (8, 9), (10, 11), (14, 15)]
  | 14, 1 => [(2, 13), (3, 12), (4, 11), (5, 10), (6, 9), (7, 8)]
  | 14, 2 => [(1, 13), (3, 15), (4, 8), (5, 9), (6, 10), (7, 11)]
  | 14, 3 => [(1, 12), (2, 15), (4, 9), (5, 8), (6, 11), (7, 10)]
  | 14, 4 => [(1, 11), (2, 8), (3, 9), (5, 15), (6, 12), (7, 13)]
  | 14, 5 => [(1, 10), (2, 9), (3, 8), (4, 15), (6, 13), (7, 12)]
  | 14, 6 => [(1, 9), (2, 10), (3, 11), (4, 12), (5, 13), (7, 15)]
  | 14, 7 => [(1, 8), (2, 11), (3, 10), (4, 13), (5, 12), (6, 15)]
  | 14, 8 => [(1, 7), (2, 4), (3, 5), (9, 15), (10, 12), (11, 13)]
  | 14, 9 => [(1, 6), (8, 15), (10, 13), (11, 12)]
  | 14, 10 => [(2, 6), (8, 12), (9, 13), (11, 15)]
  | 14, 11 => [(3, 6), (8, 13), (9, 12), (10, 15)]
  | 14, 12 => [(4, 6), (8, 10), (9, 11), (13, 15)]
  | 14, 13 => [(5, 6), (8, 11), (9, 10), (12, 15)]
  | 15, 1 => [(2, 12), (3, 13), (4, 10), (5, 11), (6, 8), (7, 9)]
  | 15, 2 => [(1, 12), (3, 14), (4, 9), (5, 8), (6, 11), (7, 10)]
  | 15, 3 => [(1, 13), (2, 14), (4, 8), (5, 9), (6, 10), (7, 11)]
  | 15, 4 => [(1, 10), (2, 9), (3, 8), (5, 14), (6, 13), (7, 12)]
  | 15, 5 => [(1, 11), (2, 8), (3, 9), (4, 14), (6, 12), (7, 13)]
  | 15, 6 => [(1, 8), (2, 11), (3, 10), (4, 13), (5, 12), (7, 14)]
  | 15, 7 => [(1, 9), (2, 10), (3, 11), (4, 12), (5, 13), (6, 14)]
  | 15, 8 => [(1, 6), (2, 5), (3, 4), (9, 14), (10, 13), (11, 12)]
  | 15, 9 => [(1, 7), (8, 14), (10, 12), (11, 13)]
  | 15, 10 => [(2, 7), (8, 13), (9, 12), (11, 14)]
  | 15, 11 => [(3, 7), (8, 12), (9, 13), (10, 14)]
  | 15, 12 => [(4, 7), (8, 11), (9, 10), (13, 14)]
  | 15, 13 => [(5, 7), (8, 10), (9, 11), (12, 14)]
  | 15, 14 => [(6, 7), (8, 9), (10, 11), (12, 13)]
  | _, _ => []

/-- Soundness of `crossBadPairs`: every entry `(a, b) ∈ crossBadPairs u v` ($v < u < 16$)
    is a verified norm-multiplicativity failure `pairingCancels 5 a (v + 16) b (u + 16) = false`! -/
theorem crossBadPairs_sound :
    ∀ u, u < 16 → ∀ v, v < u → ∀ p ∈ crossBadPairs u v,
      p.1 < p.2 ∧ p.2 < 16 ∧ (p.1 ^^^ p.2 = u ^^^ v) ∧
      pairingCancels 5 p.1 (v + 16) p.2 (u + 16) = false := by
  have hcheck :
      allNat (fun u =>
        allNat (fun v =>
          if !(v < u) then true
          else (crossBadPairs u v).all (fun p =>
            decide (p.1 < p.2) && decide (p.2 < 16) &&
            (p.1 ^^^ p.2 == u ^^^ v) && !pairingCancels 5 p.1 (v + 16) p.2 (u + 16))) 16) 16 = true := by
    decide
  intro u hu v hvu p hp
  have h1 := (allNat_eq_true _ 16).mp hcheck u hu
  have h2 := (allNat_eq_true _ 16).mp h1 v (by omega)
  simp only [hvu, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2
  have h3 := List.all_eq_true.mp h2 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h3
  exact ⟨h3.1.1.1, h3.1.1.2, h3.1.2, h3.2⟩

/-- Flat 16-bit record avoiding arithmetic inside the inner greedy clique-cover loop. -/
structure Bits16 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  b10 : Bool
  b11 : Bool
  b12 : Bool
  b13 : Bool
  b14 : Bool
  b15 : Bool

@[expose] def Bits16.get (b : Bits16) : Nat → Bool
  | 0 => b.b0 | 1 => b.b1 | 2 => b.b2 | 3 => b.b3
  | 4 => b.b4 | 5 => b.b5 | 6 => b.b6 | 7 => b.b7
  | 8 => b.b8 | 9 => b.b9 | 10 => b.b10 | 11 => b.b11
  | 12 => b.b12 | 13 => b.b13 | 14 => b.b14 | 15 => b.b15
  | _ => false

@[expose] def mkBits16 (lo8 hi8 : Nat) : Bits16 :=
  { b0  := lo8 % 2 == 1,         b1  := (lo8 / 2) % 2 == 1,
    b2  := (lo8 / 4) % 2 == 1,   b3  := (lo8 / 8) % 2 == 1,
    b4  := (lo8 / 16) % 2 == 1,  b5  := (lo8 / 32) % 2 == 1,
    b6  := (lo8 / 64) % 2 == 1,  b7  := (lo8 / 128) % 2 == 1,
    b8  := hi8 % 2 == 1,         b9  := (hi8 / 2) % 2 == 1,
    b10 := (hi8 / 4) % 2 == 1,   b11 := (hi8 / 8) % 2 == 1,
    b12 := (hi8 / 16) % 2 == 1,  b13 := (hi8 / 32) % 2 == 1,
    b14 := (hi8 / 64) % 2 == 1,  b15 := (hi8 / 128) % 2 == 1 }

theorem mkBits16_get (lo8 hi8 k : Nat) (hlo : lo8 < 256) (hk : k < 16) :
    (mkBits16 lo8 hi8).get k = (lo8 + 256 * hi8).testBit k := by
  have h8 : ∀ x j, ((x / 2 ^ j) % 2 == 1) = x.testBit j := bitAt_eq_testBit
  have hlo_tb : ∀ j, j < 8 → (lo8 + 256 * hi8).testBit j = lo8.testBit j := by
    intro j hj
    have hmod : (lo8 + 2 ^ 8 * hi8) % 2 ^ 8 = lo8 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    have h1 : ((lo8 + 2 ^ 8 * hi8) % 2 ^ 8).testBit j = (lo8 + 2 ^ 8 * hi8).testBit j := by
      rw [Nat.testBit_mod_two_pow]; simp [hj]
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← h1, hmod]
  have hhi_tb : ∀ j, (lo8 + 256 * hi8).testBit (8 + j) = hi8.testBit j := by
    intro j
    have hdiv : (lo8 + 2 ^ 8 * hi8) / 2 ^ 8 = hi8 := by
      rw [Nat.add_mul_div_left lo8 hi8 (Nat.two_pow_pos 8), Nat.div_eq_of_lt hlo, Nat.zero_add]
    rw [show (256 : Nat) = 2 ^ 8 from rfl, show 8 + j = j + 8 from Nat.add_comm 8 j,
        ← Nat.testBit_div_two_pow, hdiv]
  match k with
  | 0 => rw [hlo_tb 0 (by omega)]; unfold mkBits16 Bits16.get; simpa using h8 lo8 0
  | 1 => rw [hlo_tb 1 (by omega)]; exact h8 lo8 1
  | 2 => rw [hlo_tb 2 (by omega)]; exact h8 lo8 2
  | 3 => rw [hlo_tb 3 (by omega)]; exact h8 lo8 3
  | 4 => rw [hlo_tb 4 (by omega)]; exact h8 lo8 4
  | 5 => rw [hlo_tb 5 (by omega)]; exact h8 lo8 5
  | 6 => rw [hlo_tb 6 (by omega)]; exact h8 lo8 6
  | 7 => rw [hlo_tb 7 (by omega)]; exact h8 lo8 7
  | 8 => rw [show (8 : Nat) = 8 + 0 from rfl, hhi_tb 0]; unfold mkBits16 Bits16.get; simpa using h8 hi8 0
  | 9 => rw [show (9 : Nat) = 8 + 1 from rfl, hhi_tb 1]; exact h8 hi8 1
  | 10 => rw [show (10 : Nat) = 8 + 2 from rfl, hhi_tb 2]; exact h8 hi8 2
  | 11 => rw [show (11 : Nat) = 8 + 3 from rfl, hhi_tb 3]; exact h8 hi8 3
  | 12 => rw [show (12 : Nat) = 8 + 4 from rfl, hhi_tb 4]; exact h8 hi8 4
  | 13 => rw [show (13 : Nat) = 8 + 5 from rfl, hhi_tb 5]; exact h8 hi8 5
  | 14 => rw [show (14 : Nat) = 8 + 6 from rfl, hhi_tb 6]; exact h8 hi8 6
  | 15 => rw [show (15 : Nat) = 8 + 7 from rfl, hhi_tb 7]; exact h8 hi8 7
  | k + 16 => omega

@[expose] def hasCrossEdge (bits : Bits16) (v u : Nat) : Bool :=
  (crossBadPairs v u).any (fun p => bits.get p.1 && bits.get p.2)

/-- Static 15-vertex enum for O(1) constructor-match clique checks (zero Nat comparison in kernel). -/
inductive Vtx where
  | v1 | v2 | v3 | v4 | v5 | v6 | v7 | v8 | v9 | v10 | v11 | v12 | v13 | v14 | v15
  deriving DecidableEq

@[expose] def Vtx.toNat : Vtx → Nat
  | .v1 => 1 | .v2 => 2 | .v3 => 3 | .v4 => 4 | .v5 => 5
  | .v6 => 6 | .v7 => 7 | .v8 => 8 | .v9 => 9 | .v10 => 10
  | .v11 => 11 | .v12 => 12 | .v13 => 13 | .v14 => 14 | .v15 => 15

@[expose] def hasCrossEdgeVtx (b : Bits16) : Vtx → Vtx → Bool
  | .v2, u => match u with
    | .v1 => (b.b4 && b.b7) || ((b.b5 && b.b6) || ((b.b8 && b.b11) || ((b.b9 && b.b10))))
    | _ => false
  | .v3, u => match u with
    | .v1 => (b.b4 && b.b6) || ((b.b5 && b.b7) || ((b.b8 && b.b10) || ((b.b9 && b.b11))))
    | .v2 => (b.b4 && b.b5) || ((b.b6 && b.b7) || ((b.b8 && b.b9) || ((b.b10 && b.b11))))
    | _ => false
  | .v4, u => match u with
    | .v1 => (b.b2 && b.b7) || ((b.b3 && b.b6) || ((b.b8 && b.b13) || ((b.b9 && b.b12))))
    | .v2 => (b.b1 && b.b7) || ((b.b3 && b.b5) || ((b.b8 && b.b14) || ((b.b10 && b.b12))))
    | .v3 => (b.b1 && b.b6) || ((b.b2 && b.b5) || ((b.b8 && b.b15) || ((b.b11 && b.b12))))
    | _ => false
  | .v5, u => match u with
    | .v1 => (b.b2 && b.b6) || ((b.b3 && b.b7) || ((b.b8 && b.b12) || ((b.b9 && b.b13))))
    | .v2 => (b.b1 && b.b6) || ((b.b3 && b.b4) || ((b.b8 && b.b15) || ((b.b10 && b.b13))))
    | .v3 => (b.b1 && b.b7) || ((b.b2 && b.b4) || ((b.b8 && b.b14) || ((b.b11 && b.b13))))
    | .v4 => (b.b2 && b.b3) || ((b.b6 && b.b7) || ((b.b8 && b.b9) || ((b.b12 && b.b13))))
    | _ => false
  | .v6, u => match u with
    | .v1 => (b.b2 && b.b5) || ((b.b3 && b.b4) || ((b.b8 && b.b15) || ((b.b9 && b.b14))))
    | .v2 => (b.b1 && b.b5) || ((b.b3 && b.b7) || ((b.b8 && b.b12) || ((b.b10 && b.b14))))
    | .v3 => (b.b1 && b.b4) || ((b.b2 && b.b7) || ((b.b8 && b.b13) || ((b.b11 && b.b14))))
    | .v4 => (b.b1 && b.b3) || ((b.b5 && b.b7) || ((b.b8 && b.b10) || ((b.b12 && b.b14))))
    | .v5 => (b.b1 && b.b2) || ((b.b4 && b.b7) || ((b.b8 && b.b11) || ((b.b13 && b.b14))))
    | _ => false
  | .v7, u => match u with
    | .v1 => (b.b2 && b.b4) || ((b.b3 && b.b5) || ((b.b8 && b.b14) || ((b.b9 && b.b15))))
    | .v2 => (b.b1 && b.b4) || ((b.b3 && b.b6) || ((b.b8 && b.b13) || ((b.b10 && b.b15))))
    | .v3 => (b.b1 && b.b5) || ((b.b2 && b.b6) || ((b.b8 && b.b12) || ((b.b11 && b.b15))))
    | .v4 => (b.b1 && b.b2) || ((b.b5 && b.b6) || ((b.b8 && b.b11) || ((b.b12 && b.b15))))
    | .v5 => (b.b1 && b.b3) || ((b.b4 && b.b6) || ((b.b8 && b.b10) || ((b.b13 && b.b15))))
    | .v6 => (b.b2 && b.b3) || ((b.b4 && b.b5) || ((b.b8 && b.b9) || ((b.b14 && b.b15))))
    | _ => false
  | .v8, u => match u with
    | .v1 => (b.b2 && b.b11) || ((b.b3 && b.b10) || ((b.b4 && b.b13) || ((b.b5 && b.b12) || ((b.b6 && b.b15) || ((b.b7 && b.b14))))))
    | .v2 => (b.b1 && b.b11) || ((b.b3 && b.b9) || ((b.b4 && b.b14) || ((b.b5 && b.b15) || ((b.b6 && b.b12) || ((b.b7 && b.b13))))))
    | .v3 => (b.b1 && b.b10) || ((b.b2 && b.b9) || ((b.b4 && b.b15) || ((b.b5 && b.b14) || ((b.b6 && b.b13) || ((b.b7 && b.b12))))))
    | .v4 => (b.b1 && b.b13) || ((b.b2 && b.b14) || ((b.b3 && b.b15) || ((b.b5 && b.b9) || ((b.b6 && b.b10) || ((b.b7 && b.b11))))))
    | .v5 => (b.b1 && b.b12) || ((b.b2 && b.b15) || ((b.b3 && b.b14) || ((b.b4 && b.b9) || ((b.b6 && b.b11) || ((b.b7 && b.b10))))))
    | .v6 => (b.b1 && b.b15) || ((b.b2 && b.b12) || ((b.b3 && b.b13) || ((b.b4 && b.b10) || ((b.b5 && b.b11) || ((b.b7 && b.b9))))))
    | .v7 => (b.b1 && b.b14) || ((b.b2 && b.b13) || ((b.b3 && b.b12) || ((b.b4 && b.b11) || ((b.b5 && b.b10) || ((b.b6 && b.b9))))))
    | _ => false
  | .v9, u => match u with
    | .v1 => (b.b2 && b.b10) || ((b.b3 && b.b11) || ((b.b4 && b.b12) || ((b.b5 && b.b13) || ((b.b6 && b.b14) || ((b.b7 && b.b15))))))
    | .v2 => (b.b1 && b.b10) || ((b.b3 && b.b8) || ((b.b4 && b.b15) || ((b.b5 && b.b14) || ((b.b6 && b.b13) || ((b.b7 && b.b12))))))
    | .v3 => (b.b1 && b.b11) || ((b.b2 && b.b8) || ((b.b4 && b.b14) || ((b.b5 && b.b15) || ((b.b6 && b.b12) || ((b.b7 && b.b13))))))
    | .v4 => (b.b1 && b.b12) || ((b.b2 && b.b15) || ((b.b3 && b.b14) || ((b.b5 && b.b8) || ((b.b6 && b.b11) || ((b.b7 && b.b10))))))
    | .v5 => (b.b1 && b.b13) || ((b.b2 && b.b14) || ((b.b3 && b.b15) || ((b.b4 && b.b8) || ((b.b6 && b.b10) || ((b.b7 && b.b11))))))
    | .v6 => (b.b1 && b.b14) || ((b.b2 && b.b13) || ((b.b3 && b.b12) || ((b.b4 && b.b11) || ((b.b5 && b.b10) || ((b.b7 && b.b8))))))
    | .v7 => (b.b1 && b.b15) || ((b.b2 && b.b12) || ((b.b3 && b.b13) || ((b.b4 && b.b10) || ((b.b5 && b.b11) || ((b.b6 && b.b8))))))
    | .v8 => (b.b2 && b.b3) || ((b.b4 && b.b5) || ((b.b6 && b.b7) || ((b.b10 && b.b11) || ((b.b12 && b.b13) || ((b.b14 && b.b15))))))
    | _ => false
  | .v10, u => match u with
    | .v1 => (b.b2 && b.b9) || ((b.b3 && b.b8) || ((b.b4 && b.b15) || ((b.b5 && b.b14) || ((b.b6 && b.b13) || ((b.b7 && b.b12))))))
    | .v2 => (b.b1 && b.b9) || ((b.b3 && b.b11) || ((b.b4 && b.b12) || ((b.b5 && b.b13) || ((b.b6 && b.b14) || ((b.b7 && b.b15))))))
    | .v3 => (b.b1 && b.b8) || ((b.b2 && b.b11) || ((b.b4 && b.b13) || ((b.b5 && b.b12) || ((b.b6 && b.b15) || ((b.b7 && b.b14))))))
    | .v4 => (b.b1 && b.b15) || ((b.b2 && b.b12) || ((b.b3 && b.b13) || ((b.b5 && b.b11) || ((b.b6 && b.b8) || ((b.b7 && b.b9))))))
    | .v5 => (b.b1 && b.b14) || ((b.b2 && b.b13) || ((b.b3 && b.b12) || ((b.b4 && b.b11) || ((b.b6 && b.b9) || ((b.b7 && b.b8))))))
    | .v6 => (b.b1 && b.b13) || ((b.b2 && b.b14) || ((b.b3 && b.b15) || ((b.b4 && b.b8) || ((b.b5 && b.b9) || ((b.b7 && b.b11))))))
    | .v7 => (b.b1 && b.b12) || ((b.b2 && b.b15) || ((b.b3 && b.b14) || ((b.b4 && b.b9) || ((b.b5 && b.b8) || ((b.b6 && b.b11))))))
    | .v8 => (b.b1 && b.b3) || ((b.b4 && b.b6) || ((b.b5 && b.b7) || ((b.b9 && b.b11) || ((b.b12 && b.b14) || ((b.b13 && b.b15))))))
    | .v9 => (b.b1 && b.b2) || ((b.b8 && b.b11) || ((b.b12 && b.b15) || ((b.b13 && b.b14))))
    | _ => false
  | .v11, u => match u with
    | .v1 => (b.b2 && b.b8) || ((b.b3 && b.b9) || ((b.b4 && b.b14) || ((b.b5 && b.b15) || ((b.b6 && b.b12) || ((b.b7 && b.b13))))))
    | .v2 => (b.b1 && b.b8) || ((b.b3 && b.b10) || ((b.b4 && b.b13) || ((b.b5 && b.b12) || ((b.b6 && b.b15) || ((b.b7 && b.b14))))))
    | .v3 => (b.b1 && b.b9) || ((b.b2 && b.b10) || ((b.b4 && b.b12) || ((b.b5 && b.b13) || ((b.b6 && b.b14) || ((b.b7 && b.b15))))))
    | .v4 => (b.b1 && b.b14) || ((b.b2 && b.b13) || ((b.b3 && b.b12) || ((b.b5 && b.b10) || ((b.b6 && b.b9) || ((b.b7 && b.b8))))))
    | .v5 => (b.b1 && b.b15) || ((b.b2 && b.b12) || ((b.b3 && b.b13) || ((b.b4 && b.b10) || ((b.b6 && b.b8) || ((b.b7 && b.b9))))))
    | .v6 => (b.b1 && b.b12) || ((b.b2 && b.b15) || ((b.b3 && b.b14) || ((b.b4 && b.b9) || ((b.b5 && b.b8) || ((b.b7 && b.b10))))))
    | .v7 => (b.b1 && b.b13) || ((b.b2 && b.b14) || ((b.b3 && b.b15) || ((b.b4 && b.b8) || ((b.b5 && b.b9) || ((b.b6 && b.b10))))))
    | .v8 => (b.b1 && b.b2) || ((b.b4 && b.b7) || ((b.b5 && b.b6) || ((b.b9 && b.b10) || ((b.b12 && b.b15) || ((b.b13 && b.b14))))))
    | .v9 => (b.b1 && b.b3) || ((b.b8 && b.b10) || ((b.b12 && b.b14) || ((b.b13 && b.b15))))
    | .v10 => (b.b2 && b.b3) || ((b.b8 && b.b9) || ((b.b12 && b.b13) || ((b.b14 && b.b15))))
    | _ => false
  | .v12, u => match u with
    | .v1 => (b.b2 && b.b15) || ((b.b3 && b.b14) || ((b.b4 && b.b9) || ((b.b5 && b.b8) || ((b.b6 && b.b11) || ((b.b7 && b.b10))))))
    | .v2 => (b.b1 && b.b15) || ((b.b3 && b.b13) || ((b.b4 && b.b10) || ((b.b5 && b.b11) || ((b.b6 && b.b8) || ((b.b7 && b.b9))))))
    | .v3 => (b.b1 && b.b14) || ((b.b2 && b.b13) || ((b.b4 && b.b11) || ((b.b5 && b.b10) || ((b.b6 && b.b9) || ((b.b7 && b.b8))))))
    | .v4 => (b.b1 && b.b9) || ((b.b2 && b.b10) || ((b.b3 && b.b11) || ((b.b5 && b.b13) || ((b.b6 && b.b14) || ((b.b7 && b.b15))))))
    | .v5 => (b.b1 && b.b8) || ((b.b2 && b.b11) || ((b.b3 && b.b10) || ((b.b4 && b.b13) || ((b.b6 && b.b15) || ((b.b7 && b.b14))))))
    | .v6 => (b.b1 && b.b11) || ((b.b2 && b.b8) || ((b.b3 && b.b9) || ((b.b4 && b.b14) || ((b.b5 && b.b15) || ((b.b7 && b.b13))))))
    | .v7 => (b.b1 && b.b10) || ((b.b2 && b.b9) || ((b.b3 && b.b8) || ((b.b4 && b.b15) || ((b.b5 && b.b14) || ((b.b6 && b.b13))))))
    | .v8 => (b.b1 && b.b5) || ((b.b2 && b.b6) || ((b.b3 && b.b7) || ((b.b9 && b.b13) || ((b.b10 && b.b14) || ((b.b11 && b.b15))))))
    | .v9 => (b.b1 && b.b4) || ((b.b8 && b.b13) || ((b.b10 && b.b15) || ((b.b11 && b.b14))))
    | .v10 => (b.b2 && b.b4) || ((b.b8 && b.b14) || ((b.b9 && b.b15) || ((b.b11 && b.b13))))
    | .v11 => (b.b3 && b.b4) || ((b.b8 && b.b15) || ((b.b9 && b.b14) || ((b.b10 && b.b13))))
    | _ => false
  | .v13, u => match u with
    | .v1 => (b.b2 && b.b14) || ((b.b3 && b.b15) || ((b.b4 && b.b8) || ((b.b5 && b.b9) || ((b.b6 && b.b10) || ((b.b7 && b.b11))))))
    | .v2 => (b.b1 && b.b14) || ((b.b3 && b.b12) || ((b.b4 && b.b11) || ((b.b5 && b.b10) || ((b.b6 && b.b9) || ((b.b7 && b.b8))))))
    | .v3 => (b.b1 && b.b15) || ((b.b2 && b.b12) || ((b.b4 && b.b10) || ((b.b5 && b.b11) || ((b.b6 && b.b8) || ((b.b7 && b.b9))))))
    | .v4 => (b.b1 && b.b8) || ((b.b2 && b.b11) || ((b.b3 && b.b10) || ((b.b5 && b.b12) || ((b.b6 && b.b15) || ((b.b7 && b.b14))))))
    | .v5 => (b.b1 && b.b9) || ((b.b2 && b.b10) || ((b.b3 && b.b11) || ((b.b4 && b.b12) || ((b.b6 && b.b14) || ((b.b7 && b.b15))))))
    | .v6 => (b.b1 && b.b10) || ((b.b2 && b.b9) || ((b.b3 && b.b8) || ((b.b4 && b.b15) || ((b.b5 && b.b14) || ((b.b7 && b.b12))))))
    | .v7 => (b.b1 && b.b11) || ((b.b2 && b.b8) || ((b.b3 && b.b9) || ((b.b4 && b.b14) || ((b.b5 && b.b15) || ((b.b6 && b.b12))))))
    | .v8 => (b.b1 && b.b4) || ((b.b2 && b.b7) || ((b.b3 && b.b6) || ((b.b9 && b.b12) || ((b.b10 && b.b15) || ((b.b11 && b.b14))))))
    | .v9 => (b.b1 && b.b5) || ((b.b8 && b.b12) || ((b.b10 && b.b14) || ((b.b11 && b.b15))))
    | .v10 => (b.b2 && b.b5) || ((b.b8 && b.b15) || ((b.b9 && b.b14) || ((b.b11 && b.b12))))
    | .v11 => (b.b3 && b.b5) || ((b.b8 && b.b14) || ((b.b9 && b.b15) || ((b.b10 && b.b12))))
    | .v12 => (b.b4 && b.b5) || ((b.b8 && b.b9) || ((b.b10 && b.b11) || ((b.b14 && b.b15))))
    | _ => false
  | .v14, u => match u with
    | .v1 => (b.b2 && b.b13) || ((b.b3 && b.b12) || ((b.b4 && b.b11) || ((b.b5 && b.b10) || ((b.b6 && b.b9) || ((b.b7 && b.b8))))))
    | .v2 => (b.b1 && b.b13) || ((b.b3 && b.b15) || ((b.b4 && b.b8) || ((b.b5 && b.b9) || ((b.b6 && b.b10) || ((b.b7 && b.b11))))))
    | .v3 => (b.b1 && b.b12) || ((b.b2 && b.b15) || ((b.b4 && b.b9) || ((b.b5 && b.b8) || ((b.b6 && b.b11) || ((b.b7 && b.b10))))))
    | .v4 => (b.b1 && b.b11) || ((b.b2 && b.b8) || ((b.b3 && b.b9) || ((b.b5 && b.b15) || ((b.b6 && b.b12) || ((b.b7 && b.b13))))))
    | .v5 => (b.b1 && b.b10) || ((b.b2 && b.b9) || ((b.b3 && b.b8) || ((b.b4 && b.b15) || ((b.b6 && b.b13) || ((b.b7 && b.b12))))))
    | .v6 => (b.b1 && b.b9) || ((b.b2 && b.b10) || ((b.b3 && b.b11) || ((b.b4 && b.b12) || ((b.b5 && b.b13) || ((b.b7 && b.b15))))))
    | .v7 => (b.b1 && b.b8) || ((b.b2 && b.b11) || ((b.b3 && b.b10) || ((b.b4 && b.b13) || ((b.b5 && b.b12) || ((b.b6 && b.b15))))))
    | .v8 => (b.b1 && b.b7) || ((b.b2 && b.b4) || ((b.b3 && b.b5) || ((b.b9 && b.b15) || ((b.b10 && b.b12) || ((b.b11 && b.b13))))))
    | .v9 => (b.b1 && b.b6) || ((b.b8 && b.b15) || ((b.b10 && b.b13) || ((b.b11 && b.b12))))
    | .v10 => (b.b2 && b.b6) || ((b.b8 && b.b12) || ((b.b9 && b.b13) || ((b.b11 && b.b15))))
    | .v11 => (b.b3 && b.b6) || ((b.b8 && b.b13) || ((b.b9 && b.b12) || ((b.b10 && b.b15))))
    | .v12 => (b.b4 && b.b6) || ((b.b8 && b.b10) || ((b.b9 && b.b11) || ((b.b13 && b.b15))))
    | .v13 => (b.b5 && b.b6) || ((b.b8 && b.b11) || ((b.b9 && b.b10) || ((b.b12 && b.b15))))
    | _ => false
  | .v15, u => match u with
    | .v1 => (b.b2 && b.b12) || ((b.b3 && b.b13) || ((b.b4 && b.b10) || ((b.b5 && b.b11) || ((b.b6 && b.b8) || ((b.b7 && b.b9))))))
    | .v2 => (b.b1 && b.b12) || ((b.b3 && b.b14) || ((b.b4 && b.b9) || ((b.b5 && b.b8) || ((b.b6 && b.b11) || ((b.b7 && b.b10))))))
    | .v3 => (b.b1 && b.b13) || ((b.b2 && b.b14) || ((b.b4 && b.b8) || ((b.b5 && b.b9) || ((b.b6 && b.b10) || ((b.b7 && b.b11))))))
    | .v4 => (b.b1 && b.b10) || ((b.b2 && b.b9) || ((b.b3 && b.b8) || ((b.b5 && b.b14) || ((b.b6 && b.b13) || ((b.b7 && b.b12))))))
    | .v5 => (b.b1 && b.b11) || ((b.b2 && b.b8) || ((b.b3 && b.b9) || ((b.b4 && b.b14) || ((b.b6 && b.b12) || ((b.b7 && b.b13))))))
    | .v6 => (b.b1 && b.b8) || ((b.b2 && b.b11) || ((b.b3 && b.b10) || ((b.b4 && b.b13) || ((b.b5 && b.b12) || ((b.b7 && b.b14))))))
    | .v7 => (b.b1 && b.b9) || ((b.b2 && b.b10) || ((b.b3 && b.b11) || ((b.b4 && b.b12) || ((b.b5 && b.b13) || ((b.b6 && b.b14))))))
    | .v8 => (b.b1 && b.b6) || ((b.b2 && b.b5) || ((b.b3 && b.b4) || ((b.b9 && b.b14) || ((b.b10 && b.b13) || ((b.b11 && b.b12))))))
    | .v9 => (b.b1 && b.b7) || ((b.b8 && b.b14) || ((b.b10 && b.b12) || ((b.b11 && b.b13))))
    | .v10 => (b.b2 && b.b7) || ((b.b8 && b.b13) || ((b.b9 && b.b12) || ((b.b11 && b.b14))))
    | .v11 => (b.b3 && b.b7) || ((b.b8 && b.b12) || ((b.b9 && b.b13) || ((b.b10 && b.b14))))
    | .v12 => (b.b4 && b.b7) || ((b.b8 && b.b11) || ((b.b9 && b.b10) || ((b.b13 && b.b14))))
    | .v13 => (b.b5 && b.b7) || ((b.b8 && b.b10) || ((b.b9 && b.b11) || ((b.b12 && b.b14))))
    | .v14 => (b.b6 && b.b7) || ((b.b8 && b.b9) || ((b.b10 && b.b11) || ((b.b12 && b.b13))))
    | _ => false
  | _, _ => false

@[expose] def anyPairs (b : Bits16) : List (Nat × Nat) → Bool
  | [] => false
  | [(x, y)] => b.get x && b.get y
  | (x, y) :: ps => (b.get x && b.get y) || anyPairs b ps

theorem anyPairs_eq_any (b : Bits16) (ps : List (Nat × Nat)) :
    anyPairs b ps = ps.any (fun p => b.get p.1 && b.get p.2) := by
  induction ps with
  | nil => rfl
  | cons p tl ih =>
    rcases p with ⟨x, y⟩
    cases tl with
    | nil => simp [anyPairs]
    | cons q tl' =>
      change ((b.get x && b.get y) || anyPairs b (q :: tl')) = _
      rw [ih]; rfl

theorem hasCrossEdgeVtx_eq (b : Bits16) (v u : Vtx) (h : u.toNat < v.toNat) :
    hasCrossEdgeVtx b v u = hasCrossEdge b v.toNat u.toNat := by
  unfold hasCrossEdge
  rw [← anyPairs_eq_any]
  cases v <;> cases u <;> first | (exfalso; revert h; decide) | rfl

@[expose] def greedyInsertVtx (bits : Bits16) (u : Vtx) : List (List Vtx) → List (List Vtx)
  | [] => [[u]]
  | c :: cs =>
    if c.all (fun v => hasCrossEdgeVtx bits v u) then (u :: c) :: cs
    else c :: greedyInsertVtx bits u cs

@[expose] def greedyCliquesVtx (bits : Bits16) : List (List Vtx) :=
  let cs := greedyInsertVtx bits .v15 []
  let cs := greedyInsertVtx bits .v14 cs
  let cs := greedyInsertVtx bits .v13 cs
  let cs := greedyInsertVtx bits .v12 cs
  let cs := greedyInsertVtx bits .v11 cs
  let cs := greedyInsertVtx bits .v10 cs
  let cs := greedyInsertVtx bits .v9 cs
  let cs := greedyInsertVtx bits .v8 cs
  let cs := greedyInsertVtx bits .v7 cs
  let cs := greedyInsertVtx bits .v6 cs
  let cs := greedyInsertVtx bits .v5 cs
  let cs := greedyInsertVtx bits .v4 cs
  let cs := greedyInsertVtx bits .v3 cs
  let cs := greedyInsertVtx bits .v2 cs
  greedyInsertVtx bits .v1 cs

@[expose] def greedyCliques (bits : Bits16) : List (List Nat) :=
  [0] :: (greedyCliquesVtx bits).map (fun c => c.map Vtx.toNat)

theorem greedyCliques_length (bits : Bits16) :
    (greedyCliques bits).length = (greedyCliquesVtx bits).length + 1 := by
  simp [greedyCliques]

/-- Precomputed forbidden-mask cache for a fixed lower byte lo8 (computed once per lo8). -/
structure Forb8 where
  f0 : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
  f5 : Nat
  f6 : Nat
  f7 : Nat

@[expose] def Forb8.get (f : Forb8) : Nat → Nat
  | 0 => f.f0 | 1 => f.f1 | 2 => f.f2 | 3 => f.f3
  | 4 => f.f4 | 5 => f.f5 | 6 => f.f6 | 7 => f.f7
  | _ => 0

@[expose] def mkForb8 (lo8 : Nat) : Forb8 :=
  { f0 := forbMask4Direct lo8 0, f1 := forbMask4Direct lo8 1,
    f2 := forbMask4Direct lo8 2, f3 := forbMask4Direct lo8 3,
    f4 := forbMask4Direct lo8 4, f5 := forbMask4Direct lo8 5,
    f6 := forbMask4Direct lo8 6, f7 := forbMask4Direct lo8 7 }

theorem mkForb8_get (lo8 u : Nat) (hu : u < 8) :
    (mkForb8 lo8).get u = forbMask4Direct lo8 u := by
  match u with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | u + 8 => omega

/-- Pure C-primitive depth-d binary-tree ll over [start, start + 2^d). -/
@[expose] def allTree (P : Nat → Bool) : Nat → Nat → Bool
  | start, 0 => P start
  | start, d + 1 => allTree P start d && allTree P (start + 2 ^ d) d

theorem allTree_eq_true (P : Nat → Bool) :
    ∀ d s, allTree P s d = true ↔ ∀ k, k < 2 ^ d → P (s + k) = true := by
  intro d
  induction d with
  | zero =>
    intro s
    unfold allTree
    constructor
    · intro h k hk
      have hk0 : k = 0 := by omega
      subst hk0; simpa using h
    · intro h; simpa using h 0 (by omega)
  | succ d ih =>
    intro s
    unfold allTree
    rw [Bool.and_eq_true, ih s, ih (s + 2 ^ d)]
    have h2d : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    constructor
    · rintro ⟨h1, h2⟩ k hk
      by_cases hlt : k < 2 ^ d
      · exact h1 k hlt
      · have hsub : k - 2 ^ d < 2 ^ d := by omega
        have heq : s + 2 ^ d + (k - 2 ^ d) = s + k := by omega
        rw [← heq]; exact h2 (k - 2 ^ d) hsub
    · intro hall
      refine ⟨fun k hk => hall k (by omega), fun k hk => ?_⟩
      rw [Nat.add_assoc]; exact hall (2 ^ d + k) (by omega)

/-- Pruned branch-and-bound verifier across all independent sedenion upper bytes hi8
    for fixed lower byte lo8: visits ONLY valid sedenion lower halves with |S_lo| ≥ 8
    (exactly 2,995 leaves across all 256 values of lo8) and verifies |S_lo| + greedyCliques ≤ 13. -/
@[expose] def checkIndepHi (lo8 : Nat) (forb : Forb8) : Nat → Nat → Nat → Bool
  | 0, chosen, cnt =>
    if cnt < 8 then true
    else
      let bits := mkBits16 lo8 chosen
      cnt + (greedyCliquesVtx bits).length ≤ 12
  | rem + 1, chosen, cnt =>
    if cnt + (rem + 1) < 8 then true
    else
      let u := 7 - rem
      checkIndepHi lo8 forb rem chosen cnt &&
        (if disjointBelow chosen (forb.get u) u then
           checkIndepHi lo8 forb rem (chosen + 2 ^ u) (cnt + 1)
         else true)

/-- Odd-byte symmetry: only the 128 odd lo8 = 2*k + 1 ( \in S_{\mathrm{lo}}$) need to be
    checked because adding $ preserves orbMask4Direct and all cross-edges (1..b15) while
    strictly increasing popcount8 by 1. -/
@[expose] def checkPathionOddChunk (start : Nat) : Bool :=
  allTree (fun k => let lo8 := 2 * k + 1; checkIndepHi lo8 (mkForb8 lo8) 8 0 (popcount8 lo8)) start 3

theorem checkPathionOddChunk_0  : checkPathionOddChunk 0   = true := rfl
theorem checkPathionOddChunk_1  : checkPathionOddChunk 8   = true := rfl
theorem checkPathionOddChunk_2  : checkPathionOddChunk 16  = true := rfl
theorem checkPathionOddChunk_3  : checkPathionOddChunk 24  = true := rfl
theorem checkPathionOddChunk_4  : checkPathionOddChunk 32  = true := rfl
theorem checkPathionOddChunk_5  : checkPathionOddChunk 40  = true := rfl
theorem checkPathionOddChunk_6  : checkPathionOddChunk 48  = true := rfl
theorem checkPathionOddChunk_7  : checkPathionOddChunk 56  = true := rfl
theorem checkPathionOddChunk_8  : checkPathionOddChunk 64  = true := rfl
theorem checkPathionOddChunk_9  : checkPathionOddChunk 72  = true := rfl
theorem checkPathionOddChunk_10 : checkPathionOddChunk 80  = true := rfl
theorem checkPathionOddChunk_11 : checkPathionOddChunk 88  = true := rfl
theorem checkPathionOddChunk_12 : checkPathionOddChunk 96  = true := rfl
theorem checkPathionOddChunk_13 : checkPathionOddChunk 104 = true := rfl
theorem checkPathionOddChunk_14 : checkPathionOddChunk 112 = true := rfl
theorem checkPathionOddChunk_15 : checkPathionOddChunk 120 = true := rfl

theorem checkPathionOdd_all (k : Nat) (hk : k < 128) :
    checkIndepHi (2 * k + 1) (mkForb8 (2 * k + 1)) 8 0 (popcount8 (2 * k + 1)) = true := by
  have hdispatch : ∀ s, checkPathionOddChunk s = true → s ≤ k → k < s + 8 →
      checkIndepHi (2 * k + 1) (mkForb8 (2 * k + 1)) 8 0 (popcount8 (2 * k + 1)) = true := by
    intro s hchk hge hlt
    have h := (allTree_eq_true _ 3 s).mp hchk (k - s) (by omega)
    have heq : s + (k - s) = k := by omega
    rw [heq] at h; exact h
  by_cases h0 : k < 8
  · exact hdispatch 0 checkPathionOddChunk_0 (by omega) (by omega)
  · by_cases h1 : k < 16
    · exact hdispatch 8 checkPathionOddChunk_1 (by omega) (by omega)
    · by_cases h2 : k < 24
      · exact hdispatch 16 checkPathionOddChunk_2 (by omega) (by omega)
      · by_cases h3 : k < 32
        · exact hdispatch 24 checkPathionOddChunk_3 (by omega) (by omega)
        · by_cases h4 : k < 40
          · exact hdispatch 32 checkPathionOddChunk_4 (by omega) (by omega)
          · by_cases h5 : k < 48
            · exact hdispatch 40 checkPathionOddChunk_5 (by omega) (by omega)
            · by_cases h6 : k < 56
              · exact hdispatch 48 checkPathionOddChunk_6 (by omega) (by omega)
              · by_cases h7 : k < 64
                · exact hdispatch 56 checkPathionOddChunk_7 (by omega) (by omega)
                · by_cases h8 : k < 72
                  · exact hdispatch 64 checkPathionOddChunk_8 (by omega) (by omega)
                  · by_cases h9 : k < 80
                    · exact hdispatch 72 checkPathionOddChunk_9 (by omega) (by omega)
                    · by_cases h10 : k < 88
                      · exact hdispatch 80 checkPathionOddChunk_10 (by omega) (by omega)
                      · by_cases h11 : k < 96
                        · exact hdispatch 88 checkPathionOddChunk_11 (by omega) (by omega)
                        · by_cases h12 : k < 104
                          · exact hdispatch 96 checkPathionOddChunk_12 (by omega) (by omega)
                          · by_cases h13 : k < 112
                            · exact hdispatch 104 checkPathionOddChunk_13 (by omega) (by omega)
                            · by_cases h14 : k < 120
                              · exact hdispatch 112 checkPathionOddChunk_14 (by omega) (by omega)
                              · exact hdispatch 120 checkPathionOddChunk_15 (by omega) (by omega)

theorem hasCrossEdgeVtx_ignore_b0 (b1 b2 : Bits16)
    (h1 : b1.b1 = b2.b1) (h2 : b1.b2 = b2.b2) (h3 : b1.b3 = b2.b3) (h4 : b1.b4 = b2.b4)
    (h5 : b1.b5 = b2.b5) (h6 : b1.b6 = b2.b6) (h7 : b1.b7 = b2.b7) (h8 : b1.b8 = b2.b8)
    (h9 : b1.b9 = b2.b9) (h10 : b1.b10 = b2.b10) (h11 : b1.b11 = b2.b11) (h12 : b1.b12 = b2.b12)
    (h13 : b1.b13 = b2.b13) (h14 : b1.b14 = b2.b14) (h15 : b1.b15 = b2.b15)
    (v u : Vtx) :
    hasCrossEdgeVtx b1 v u = hasCrossEdgeVtx b2 v u := by
  cases v <;> cases u <;> simp [hasCrossEdgeVtx, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

theorem greedyCliquesVtx_ignore_b0 (b1 b2 : Bits16)
    (h1 : b1.b1 = b2.b1) (h2 : b1.b2 = b2.b2) (h3 : b1.b3 = b2.b3) (h4 : b1.b4 = b2.b4)
    (h5 : b1.b5 = b2.b5) (h6 : b1.b6 = b2.b6) (h7 : b1.b7 = b2.b7) (h8 : b1.b8 = b2.b8)
    (h9 : b1.b9 = b2.b9) (h10 : b1.b10 = b2.b10) (h11 : b1.b11 = b2.b11) (h12 : b1.b12 = b2.b12)
    (h13 : b1.b13 = b2.b13) (h14 : b1.b14 = b2.b14) (h15 : b1.b15 = b2.b15) :
    greedyCliquesVtx b1 = greedyCliquesVtx b2 := by
  have hedge : ∀ v u, hasCrossEdgeVtx b1 v u = hasCrossEdgeVtx b2 v u :=
    hasCrossEdgeVtx_ignore_b0 b1 b2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  have hins : ∀ u cs, greedyInsertVtx b1 u cs = greedyInsertVtx b2 u cs := by
    intro u cs
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      unfold greedyInsertVtx
      have hall : c.all (fun v => hasCrossEdgeVtx b1 v u) = c.all (fun v => hasCrossEdgeVtx b2 v u) := by
        congr 1; funext v; exact hedge v u
      rw [hall, ih]
  unfold greedyCliquesVtx
  simp only [hins]

theorem forbMask4_ignore_bit0 (lo8 : Nat) (_hlo8 : lo8 < 256) (u : Nat) (hu : u < 8) :
    forbMask4 (2 * (lo8 / 2) + 1) u = forbMask4 lo8 u := by
  rw [← forbMask4Direct_eq_forbMask4 _ u hu, ← forbMask4Direct_eq_forbMask4 lo8 u hu]
  have hd : ∀ m, 1 ≤ m → (2 * (lo8 / 2) + 1) / (2 ^ m) = lo8 / (2 ^ m) := by
    intro m hm
    have hm' : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : m = (m - 1) + 1 := by omega
      conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
    rw [hm', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have : (2 * (lo8 / 2) + 1) / 2 = lo8 / 2 := by omega
    rw [this]
  have hpf : ∀ a1 b1 a2 b2 bit, 1 ≤ a1 → 1 ≤ b1 → 1 ≤ a2 → 1 ≤ b2 →
      forbPairFast (2 * (lo8 / 2) + 1) a1 b1 a2 b2 bit = forbPairFast lo8 a1 b1 a2 b2 bit := by
    intro a1 b1 a2 b2 bit ha1 hb1 ha2 hb2
    unfold forbPairFast bitAt
    rw [hd a1 ha1, hd b1 hb1, hd a2 ha2, hd b2 hb2]
  match u with
  | 0 => rfl
  | 1 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | 2 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | 3 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | 4 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | 5 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | 6 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | 7 => unfold forbMask4Direct; repeat rw [hpf _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
  | u + 8 => omega

theorem popcount8_le_odd (lo8 : Nat) : popcount8 lo8 ≤ popcount8 (2 * (lo8 / 2) + 1) := by
  have hd : ∀ m, 1 ≤ m → (2 * (lo8 / 2) + 1) / (2 ^ m) = lo8 / (2 ^ m) := by
    intro m hm
    have hm' : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : m = (m - 1) + 1 := by omega
      conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
    rw [hm', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have : (2 * (lo8 / 2) + 1) / 2 = lo8 / 2 := by omega
    rw [this]
  have h1 : (2 * (lo8 / 2) + 1) / 2 = lo8 / 2 := hd 1 (by omega)
  have h2 : (2 * (lo8 / 2) + 1) / 4 = lo8 / 4 := hd 2 (by omega)
  have h3 : (2 * (lo8 / 2) + 1) / 8 = lo8 / 8 := hd 3 (by omega)
  have h4 : (2 * (lo8 / 2) + 1) / 16 = lo8 / 16 := hd 4 (by omega)
  have h5 : (2 * (lo8 / 2) + 1) / 32 = lo8 / 32 := hd 5 (by omega)
  have h6 : (2 * (lo8 / 2) + 1) / 64 = lo8 / 64 := hd 6 (by omega)
  have h7 : (2 * (lo8 / 2) + 1) / 128 = lo8 / 128 := hd 7 (by omega)
  unfold popcount8
  rw [h1, h2, h3, h4, h5, h6, h7]
  omega

theorem checkIndepHi_sound (lo8 hi8 : Nat) (hhi8 : hi8 < 256)
    (hind : isIndepForb (forbMask4 lo8) hi8 = true)
    (h8 : 8 ≤ popcount8 lo8 + popcount8 hi8) :
    ∀ rem chosen cnt, rem ≤ 8 → chosen = hi8 % (2 ^ (8 - rem)) →
      cnt = popcount8 lo8 + popcount8 chosen →
      checkIndepHi lo8 (mkForb8 lo8) rem chosen cnt = true →
      popcount8 lo8 + popcount8 hi8 + (greedyCliques (mkBits16 lo8 hi8)).length ≤ 13 := by
  intro rem
  induction rem with
  | zero =>
    intro chosen cnt _ hch hcnt hchk
    have hmod : hi8 % 2 ^ (8 - 0) = hi8 := Nat.mod_eq_of_lt hhi8
    rw [hmod] at hch
    subst hch
    unfold checkIndepHi at hchk
    have hnot : ¬(cnt < 8) := by omega
    simp only [hnot, ↓reduceIte, decide_eq_true_eq] at hchk
    rw [greedyCliques_length]
    omega
  | succ rem ih =>
    intro chosen cnt hrem hch hcnt hchk
    let u := 7 - rem
    have hu_eq : 8 - (rem + 1) = u := by omega
    have hu1_eq : 8 - rem = u + 1 := by omega
    have hu8 : u < 8 := by omega
    have hch_lt : chosen < 2 ^ u := by rw [hch, hu_eq]; exact Nat.mod_lt hi8 (Nat.two_pow_pos u)
    have hpop_le : popcount8 hi8 ≤ popcount8 chosen + (rem + 1) := by
      rw [popcount8_eq_countPred, popcount8_eq_countPred]
      have hstep : ∀ k, k ≤ 8 →
          countPred (fun j => hi8.testBit j) k ≤
          countPred (fun j => chosen.testBit j) k + (if u < k then k - u else 0) := by
        intro k hk
        induction k with
        | zero => simp [countPred]
        | succ k ihk =>
          unfold countPred
          have hihk := ihk (by omega)
          by_cases hku : k < u
          · have htb : chosen.testBit k = hi8.testBit k := by
              rw [hch, hu_eq, Nat.testBit_mod_two_pow]; simp [hku]
            rw [htb]
            have hnot1 : ¬(u < k) := by omega
            have hnot2 : ¬(u < k + 1) := by omega
            simp only [hnot1, hnot2, ↓reduceIte] at hihk ⊢; omega
          · have hpos2 : u < k + 1 := by omega
            by_cases hku2 : u < k
            · simp only [hku2, hpos2, ↓reduceIte] at hihk ⊢
              cases hi8.testBit k <;> cases chosen.testBit k <;> simp <;> omega
            · simp only [hku2, hpos2, ↓reduceIte] at hihk ⊢
              cases hi8.testBit k <;> cases chosen.testBit k <;> simp <;> omega
      have := hstep 8 (Nat.le_refl _)
      simp only [hu8, ↓reduceIte] at this; omega
    unfold checkIndepHi at hchk
    have hnot : ¬(cnt + (rem + 1) < 8) := by omega
    simp only [hnot, ↓reduceIte, Bool.and_eq_true] at hchk
    have hdivmod : hi8 % 2 ^ (u + 1) = chosen + 2 ^ u * ((hi8 / 2 ^ u) % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul, ← hu_eq, ← hch]
    rcases Nat.mod_two_eq_zero_or_one (hi8 / 2 ^ u) with h0 | h1
    · have hch0 : chosen = hi8 % 2 ^ (8 - rem) := by
        rw [hu1_eq, hdivmod, h0, Nat.mul_zero, Nat.add_zero]
      exact ih chosen cnt (by omega) hch0 hcnt hchk.1
    · have hch1 : chosen + 2 ^ u = hi8 % 2 ^ (8 - rem) := by
        rw [hu1_eq, hdivmod, h1, Nat.mul_one]
      have hbit_u : hi8.testBit u = true := by
        have hm := mod2_eq_ite_testBit hi8 u
        rw [h1] at hm
        cases htb : hi8.testBit u
        · rw [htb] at hm; simp at hm
        · rfl
      have hdisj : disjointBelow chosen ((mkForb8 lo8).get u) u = true := by
        rw [mkForb8_get lo8 u hu8, forbMask4Direct_eq_forbMask4 lo8 u hu8, disjointBelow_eq_land_zero chosen _ u hch_lt, beq_iff_eq]
        have hind_u := (allNat_eq_true _ 8).mp hind u hu8
        simp only [hbit_u, Bool.not_true, Bool.false_or, beq_iff_eq] at hind_u
        apply Nat.eq_of_testBit_eq; intro k
        rw [Nat.testBit_and, Nat.zero_testBit]
        by_cases hku : k < u
        · have hck : chosen.testBit k = hi8.testBit k := by
            rw [hch, hu_eq, Nat.testBit_mod_two_pow]; simp [hku]
          rw [hck]
          have h0k := congrArg (fun z => z.testBit k) hind_u
          rw [Nat.testBit_and, Nat.zero_testBit] at h0k
          exact h0k
        · have hlt_k : chosen < 2 ^ k := by
            calc chosen < 2 ^ u := hch_lt
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          simp [Nat.testBit_lt_two_pow hlt_k]
      have hR := hchk.2
      change (if disjointBelow chosen ((mkForb8 lo8).get u) u = true then _ else true) = true at hR
      rw [hdisj] at hR
      simp only [↓reduceIte] at hR
      have hpop1 : popcount8 (chosen + 2 ^ u) = popcount8 chosen + 1 := by
        rw [popcount8_eq_countPred, popcount8_eq_countPred]
        have htb_add : ∀ k, (chosen + 2 ^ u).testBit k = if k = u then true else chosen.testBit k := by
          intro k
          by_cases hku : k < u
          · have hne : k ≠ u := by omega
            simp only [hne, ↓reduceIte]
            simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
            have hsp : 2 ^ u = 2 ^ (u - k) * 2 ^ k := by
              have : (u - k) + k = u := by omega
              rw [← Nat.pow_add, this]
            have hdiv : (chosen + 2 ^ u) / 2 ^ k = chosen / 2 ^ k + 2 ^ (u - k) := by
              rw [hsp, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k)]
            have h2 : 2 ^ (u - k) = 2 * 2 ^ (u - k - 1) := by
              have ht : u - k = (u - k - 1) + 1 := by omega
              conv => lhs; rw [ht, Nat.pow_succ, Nat.mul_comm]
            rw [hdiv, h2]
            have hmod : (chosen / 2 ^ k + 2 * 2 ^ (u - k - 1)) % 2 = (chosen / 2 ^ k) % 2 := by omega
            simp [hmod]
          · by_cases hkeq : k = u
            · subst hkeq; simp only [↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
              have hd : (chosen + 2 ^ u) / 2 ^ u = 1 := by
                rw [Nat.add_div_right chosen (Nat.two_pow_pos u), Nat.div_eq_of_lt hch_lt, Nat.zero_add]
              rw [hd]; rfl
            · have hne : k ≠ u := hkeq
              simp only [hne, ↓reduceIte]
              have hlt1 : chosen < 2 ^ k := Nat.lt_of_lt_of_le hch_lt (Nat.pow_le_pow_right (by omega) (by omega))
              have hlt2 : chosen + 2 ^ u < 2 ^ k := by
                have h2u : 2 ^ (u + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
                rw [Nat.pow_succ] at h2u; omega
              rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]
        have hch_u0 : chosen.testBit u = false := Nat.testBit_lt_two_pow hch_lt
        have hdiff : ∀ k, k ≤ 8 →
            countPred (fun j => (chosen + 2 ^ u).testBit j) k =
            countPred (fun j => chosen.testBit j) k + (if u < k then 1 else 0) := by
          intro k hk
          induction k with
          | zero => simp [countPred]
          | succ k ihk =>
            unfold countPred; rw [ihk (by omega), htb_add k]
            by_cases hku : k = u
            · subst hku; simp [hch_u0]
            · have hlt_iff : (u < k + 1) ↔ (u < k) := by omega
              simp [hku, hlt_iff]; omega
        have := hdiff 8 (Nat.le_refl _)
        simp only [hu8, ↓reduceIte] at this; omega
      exact ih (chosen + 2 ^ u) (cnt + 1) (by omega) hch1 (by omega) hR

/-! ### Part 3: Clique-Cover Soundness & Exact Pigeonhole Upper Bound -/

/-- Strictly ascending clique in `hasCrossEdge bits` with all elements in `[lb, 16)`. -/
def IsValidClique (bits : Bits16) (lb : Nat) : List Nat → Prop
  | [] => True
  | x :: xs =>
    lb ≤ x ∧ x < 16 ∧
    (∀ y ∈ xs, x < y ∧ hasCrossEdge bits y x = true) ∧
    IsValidClique bits (x + 1) xs

theorem isValidClique_mono {bits : Bits16} {lb1 lb2 : Nat} {c : List Nat}
    (hle : lb1 ≤ lb2) (h : IsValidClique bits lb2 c) : IsValidClique bits lb1 c := by
  cases c with
  | nil => trivial
  | cons x xs => exact ⟨Nat.le_trans hle h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem isValidClique_lb {bits : Bits16} {lb : Nat} {c : List Nat}
    (h : IsValidClique bits lb c) : ∀ y ∈ c, lb ≤ y := by
  induction c generalizing lb with
  | nil => intro _ hy; cases hy
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact h.1
    · have h1 : lb ≤ x := h.1
      have h2 := ih h.2.2.2 y hmem
      omega

theorem isValidClique_pair {bits : Bits16} {lb : Nat} {c : List Nat}
    (h : IsValidClique bits lb c) :
    ∀ u ∈ c, ∀ v ∈ c, u < v → hasCrossEdge bits v u = true := by
  induction c generalizing lb with
  | nil => intro _ hu; cases hu
  | cons x xs ih =>
    intro u hu v hv huv
    rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hv with rfl | hv'
    · omega
    · exact (h.2.2.1 v hv').2
    · have hxu := (h.2.2.1 u hu').1; omega
    · exact ih h.2.2.2 u hu' v hv' huv

theorem isValidClique_ub {bits : Bits16} {lb : Nat} {c : List Nat}
    (h : IsValidClique bits lb c) : ∀ y ∈ c, y < 16 := by
  induction c generalizing lb with
  | nil => intro _ hy; cases hy
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact h.2.1
    · exact ih h.2.2.2 y hmem

theorem greedyInsertVtx_valid (bits : Bits16) (u : Vtx) (cs : List (List Vtx))
    (hcs : ∀ c ∈ cs, IsValidClique bits (u.toNat + 1) (c.map Vtx.toNat)) :
    ∀ c ∈ greedyInsertVtx bits u cs, IsValidClique bits u.toNat (c.map Vtx.toNat) := by
  have hu16 : u.toNat < 16 := by cases u <;> decide
  induction cs with
  | nil =>
    intro c hc
    simp only [greedyInsertVtx, List.mem_singleton] at hc
    subst hc
    exact ⟨Nat.le_refl _, hu16, (fun _ h => nomatch h), trivial⟩
  | cons c0 rest ih =>
    unfold greedyInsertVtx
    have hc0 := hcs c0 (List.mem_cons_self ..)
    have hrest : ∀ c ∈ rest, IsValidClique bits (u.toNat + 1) (c.map Vtx.toNat) :=
      fun c hc => hcs c (List.mem_cons_of_mem c0 hc)
    by_cases hall : c0.all (fun v => hasCrossEdgeVtx bits v u) = true
    · simp only [hall, ↓reduceIte]
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · refine ⟨Nat.le_refl _, hu16, ?_, hc0⟩
        intro y hy
        rcases List.mem_map.mp hy with ⟨v, hv, rfl⟩
        have hlb := isValidClique_lb hc0 v.toNat (List.mem_map_of_mem hv)
        have hf := List.all_eq_true.mp hall v hv
        rw [hasCrossEdgeVtx_eq bits v u (by omega)] at hf
        exact ⟨hlb, hf⟩
      · exact isValidClique_mono (by omega) (hrest c hmem)
    · simp only [Bool.eq_false_iff.mpr hall, Bool.false_eq_true, ↓reduceIte]
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact isValidClique_mono (by omega) hc0
      · exact ih hrest c hmem

theorem greedyInsertVtx_covers (bits : Bits16) (u : Vtx) (cs : List (List Vtx)) :
    (∃ c ∈ greedyInsertVtx bits u cs, u.toNat ∈ c.map Vtx.toNat) ∧
    (∀ x, (∃ c ∈ cs, x ∈ c.map Vtx.toNat) → ∃ c ∈ greedyInsertVtx bits u cs, x ∈ c.map Vtx.toNat) := by
  induction cs with
  | nil =>
    exact ⟨⟨[u], List.mem_cons_self .., List.mem_cons_self ..⟩, fun _ ⟨_, hc, _⟩ => nomatch hc⟩
  | cons c0 rest ih =>
    unfold greedyInsertVtx
    by_cases hall : c0.all (fun v => hasCrossEdgeVtx bits v u) = true
    · simp only [hall, ↓reduceIte]
      refine ⟨⟨u :: c0, List.mem_cons_self .., List.mem_cons_self ..⟩, ?_⟩
      rintro x ⟨c, hc, hx⟩
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact ⟨u :: c, List.mem_cons_self .., List.mem_cons_of_mem u.toNat hx⟩
      · exact ⟨c, List.mem_cons_of_mem _ hmem, hx⟩
    · simp only [Bool.eq_false_iff.mpr hall, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rcases ih.1 with ⟨c, hc, hu⟩
        exact ⟨c, List.mem_cons_of_mem c0 hc, hu⟩
      · rintro x ⟨c, hc, hx⟩
        rcases List.mem_cons.mp hc with rfl | hmem
        · exact ⟨c, List.mem_cons_self .., hx⟩
        · rcases ih.2 x ⟨c, hmem, hx⟩ with ⟨c', hc', hx'⟩
          exact ⟨c', List.mem_cons_of_mem c0 hc', hx'⟩

theorem greedyCliquesVtx_step (bits : Bits16) (u : Vtx) (cs : List (List Vtx))
    (h : (∀ c ∈ cs, IsValidClique bits (u.toNat + 1) (c.map Vtx.toNat)) ∧
         (∀ x, u.toNat < x → x < 16 → ∃ c ∈ cs, x ∈ c.map Vtx.toNat)) :
    (∀ c ∈ greedyInsertVtx bits u cs, IsValidClique bits u.toNat (c.map Vtx.toNat)) ∧
    (∀ x, u.toNat ≤ x → x < 16 → ∃ c ∈ greedyInsertVtx bits u cs, x ∈ c.map Vtx.toNat) := by
  refine ⟨greedyInsertVtx_valid bits u cs h.1, fun x hge hlt => ?_⟩
  by_cases heq : x = u.toNat
  · subst heq; exact (greedyInsertVtx_covers bits u cs).1
  · exact (greedyInsertVtx_covers bits u cs).2 x (h.2 x (by omega) hlt)

theorem greedyCliques_spec (bits : Bits16) :
    (∀ c ∈ greedyCliques bits, IsValidClique bits 0 c) ∧
    (∀ x, x < 16 → ∃ c ∈ greedyCliques bits, x ∈ c) := by
  have h15 : (∀ c ∈ ([] : List (List Vtx)), IsValidClique bits (Vtx.v15.toNat + 1) (c.map Vtx.toNat)) ∧
             (∀ x, Vtx.v15.toNat < x → x < 16 → ∃ c ∈ ([] : List (List Vtx)), x ∈ c.map Vtx.toNat) :=
    ⟨(fun _ h => nomatch h), fun _ h1 h2 => (by simp [Vtx.toNat] at h1; omega)⟩
  have h14 := greedyCliquesVtx_step bits .v15 _ h15
  have h13 := greedyCliquesVtx_step bits .v14 _ ⟨h14.1, fun x hx1 hx2 => h14.2 x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h12 := greedyCliquesVtx_step bits .v13 _ ⟨h13.1, fun x hx1 hx2 => h13.2 x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h11 := greedyCliquesVtx_step bits .v12 _ ⟨h12.1, fun x hx1 hx2 => h12.2 x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h10 := greedyCliquesVtx_step bits .v11 _ ⟨h11.1, fun x hx1 hx2 => h11.2 x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h9  := greedyCliquesVtx_step bits .v10 _ ⟨h10.1, fun x hx1 hx2 => h10.2 x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h8  := greedyCliquesVtx_step bits .v9  _ ⟨h9.1,  fun x hx1 hx2 => h9.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h7  := greedyCliquesVtx_step bits .v8  _ ⟨h8.1,  fun x hx1 hx2 => h8.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h6  := greedyCliquesVtx_step bits .v7  _ ⟨h7.1,  fun x hx1 hx2 => h7.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h5  := greedyCliquesVtx_step bits .v6  _ ⟨h6.1,  fun x hx1 hx2 => h6.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h4  := greedyCliquesVtx_step bits .v5  _ ⟨h5.1,  fun x hx1 hx2 => h5.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h3  := greedyCliquesVtx_step bits .v4  _ ⟨h4.1,  fun x hx1 hx2 => h4.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h2  := greedyCliquesVtx_step bits .v3  _ ⟨h3.1,  fun x hx1 hx2 => h3.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h1  := greedyCliquesVtx_step bits .v2  _ ⟨h2.1,  fun x hx1 hx2 => h2.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  have h0  := greedyCliquesVtx_step bits .v1  _ ⟨h1.1,  fun x hx1 hx2 => h1.2  x (by simp [Vtx.toNat] at hx1 ⊢; omega) hx2⟩
  unfold greedyCliques greedyCliquesVtx
  refine ⟨?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · exact ⟨Nat.le_refl 0, by omega, (fun _ h => nomatch h), trivial⟩
    · rcases List.mem_map.mp hmem with ⟨cv, hcv, rfl⟩
      exact isValidClique_mono (by omega) (h0.1 cv hcv)
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact ⟨[0], List.mem_cons_self .., List.mem_cons_self ..⟩
    · rcases h0.2 x (by simp [Vtx.toNat]; omega) hx with ⟨cv, hcv, hxc⟩
      exact ⟨cv.map Vtx.toNat, List.mem_cons_of_mem [0] (List.mem_map_of_mem hcv), hxc⟩

theorem countPred_or_le (P Q : Nat → Bool) (m : Nat) :
    countPred (fun x => P x || Q x) m ≤ countPred P m + countPred Q m := by
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold countPred
    cases P m <;> cases Q m <;> simp <;> omega

theorem countPred_le_one_of_unique (P : Nat → Bool) (m : Nat)
    (huniq : ∀ u v, u < v → v < m → P u = true → P v = true → False) :
    countPred P m ≤ 1 := by
  induction m with
  | zero => exact Nat.zero_le 1
  | succ m ih =>
    unfold countPred
    by_cases hm : P m = true
    · have hz : countPred P m = 0 := by
        have h0 : ∀ k, k ≤ m → countPred P k = 0 := by
          intro k hk
          induction k with
          | zero => rfl
          | succ k ihk =>
            unfold countPred
            have hPk : P k = false := Bool.eq_false_iff.mpr (fun h => huniq k m (by omega) (by omega) h hm)
            simp [ihk (by omega), hPk]
        exact h0 m (Nat.le_refl m)
      simp [hm, hz]
    · simp only [Bool.eq_false_iff.mpr hm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih (fun u v huv hv => huniq u v huv (by omega))

theorem popcount16_le_clique_cover (bits : Bits16) (hi : Nat) (cs : List (List Nat))
    (hvalid : ∀ c ∈ cs, IsValidClique bits 0 c)
    (hcov : ∀ x, x < 16 → ∃ c ∈ cs, x ∈ c)
    (hind : ∀ u v, u < v → v < 16 → hi.testBit u = true → hi.testBit v = true →
              hasCrossEdge bits v u = false) :
    popcount16 hi ≤ cs.length := by
  rw [popcount16_eq_countPred]
  have heq : countPred (fun x => hi.testBit x) 16 =
             countPred (fun x => hi.testBit x && cs.any (fun c => c.contains x)) 16 := by
    apply countPred_ext; intro x hx
    rcases hcov x hx with ⟨c, hc, hxc⟩
    have hany : cs.any (fun c => c.contains x) = true :=
      List.any_eq_true.mpr ⟨c, hc, List.contains_iff_mem.mpr hxc⟩
    rw [hany, Bool.and_true]
  rw [heq]
  have hsum : ∀ (L : List (List Nat)), (∀ c ∈ L, IsValidClique bits 0 c) →
      countPred (fun x => hi.testBit x && L.any (fun c => c.contains x)) 16 ≤ L.length := by
    intro L
    induction L with
    | nil =>
      intro _
      have : countPred (fun x => hi.testBit x && false) 16 = 0 := by
        exact (countPred_ext _ (fun _ => false) 16 (fun _ _ => by simp)).trans (countPred_false 16)
      simpa using this
    | cons c rest ih =>
      intro hL
      have hsplit :
          countPred (fun x => hi.testBit x && (c :: rest).any (fun c' => c'.contains x)) 16 =
          countPred (fun x => (hi.testBit x && c.contains x) ||
                              (hi.testBit x && rest.any (fun c' => c'.contains x))) 16 := by
        apply countPred_ext; intro x _
        simp only [List.any_cons]
        cases hi.testBit x <;> cases c.contains x <;> cases rest.any (fun c' => c'.contains x) <;> rfl
      rw [hsplit]
      have hle := countPred_or_le
        (fun x => hi.testBit x && c.contains x)
        (fun x => hi.testBit x && rest.any (fun c' => c'.contains x)) 16
      have hc1 : countPred (fun x => hi.testBit x && c.contains x) 16 ≤ 1 := by
        apply countPred_le_one_of_unique
        intro u v huv hv hu hv'
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hu hv'
        have hedge := isValidClique_pair (hL c (List.mem_cons_self ..)) u hu.2 v hv'.2 huv
        have hno := hind u v huv hv hu.1 hv'.1
        rw [hedge] at hno; cases hno
      have hrest := ih (fun c' hc' => hL c' (List.mem_cons_of_mem c hc'))
      simp only [List.length_cons]
      omega
  exact hsum cs hvalid

/-- Lower restriction: if `m = lo + 65536 * hi` is norm-multiplicative in $\mathrm{CD}_5$,
    then its lower 16 bits `lo` are norm-multiplicative in $\mathrm{CD}_4$ and its upper
    16 bits `hi` form an independent set in `hasCrossEdge (mkBits16 (lo % 256) (lo / 256))`. -/
theorem pathion_lo_valid_and_hi_indep (lo hi : Nat) (hlo : lo < 65536) (_hhi : hi < 65536)
    (hnm : isNormMultMask 5 (lo + 65536 * hi) = true) :
    isNormMultMask 4 lo = true ∧
    (∀ u v, u < v → v < 16 → hi.testBit u = true → hi.testBit v = true →
      hasCrossEdge (mkBits16 (lo % 256) (lo / 256)) v u = false) := by
  refine ⟨?_, ?_⟩
  · unfold isNormMultMask at hnm ⊢
    rw [allNat_eq_true]; intro a ha
    have hta : (lo + 65536 * hi).testBit a = lo.testBit a := by
      rw [testBit_lo_hi16 lo hi a hlo]; simp [ha]
    by_cases hba : lo.testBit a = true
    · simp only [hba, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have h1 := (allNat_eq_true _ 32).mp hnm a (by omega)
      simp only [hta, hba, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
      rw [allNat_eq_true]; intro b hb
      have htb : (lo + 65536 * hi).testBit b = lo.testBit b := by
        rw [testBit_lo_hi16 lo hi b hlo]; simp [hb]
      by_cases hcb : (a < b && lo.testBit b) = true
      · simp only [hcb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have h2 := (allNat_eq_true _ 32).mp h1 b (by omega)
        simp only [htb, hcb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2
        rw [allNat_eq_true]; intro c hc
        have htc : (lo + 65536 * hi).testBit c = lo.testBit c := by
          rw [testBit_lo_hi16 lo hi c hlo]; simp [hc]
        by_cases hcc : (lo.testBit c && c != a && c != b) = true
        · simp only [hcc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have h3 := (allNat_eq_true _ 32).mp h2 c (by omega)
          simp only [htc, hcc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h3
          let d := a ^^^ b ^^^ c
          have hd16 : d < 16 := Nat.xor_lt_two_pow (n := 4) (Nat.xor_lt_two_pow (n := 4) ha hb) hc
          have htd : (lo + 65536 * hi).testBit d = lo.testBit d := by
            rw [testBit_lo_hi16 lo hi d hlo]; simp [hd16]
          change (if !(decide (c < d) && decide (d < 2 ^ 4) && lo.testBit d) then true
                  else pairingCancels 4 a b c d) = true
          by_cases hcd : (decide (c < d) && decide (d < 2 ^ 4) && lo.testBit d) = true
          · simp only [hcd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcd
            have hd32 : d < 2 ^ 5 := by omega
            change (if !(decide (c < d) && decide (d < 2 ^ 5) && (lo + 65536 * hi).testBit d) then true
                    else pairingCancels 5 a b c d) = true at h3
            simp only [hcd.1.1, hd32, htd, hcd.2, decide_true, Bool.and_true, Bool.not_true,
                       Bool.false_eq_true, ↓reduceIte] at h3
            unfold pairingCancels at h3 ⊢
            rw [cdSign_succ_ll 4 a c ha hc, cdSign_succ_ll 4 b d hb hd16,
                cdSign_succ_ll 4 a d ha hd16, cdSign_succ_ll 4 b c hb hc] at h3
            exact h3
          · simp only [Bool.eq_false_iff.mpr hcd, Bool.not_false, ↓reduceIte]
        · simp [Bool.eq_false_iff.mpr hcc]
      · simp [Bool.eq_false_iff.mpr hcb]
    · simp [Bool.eq_false_iff.mpr hba]
  · intro u v huv hv hbu hbv
    apply Bool.eq_false_iff.mpr; intro hedge
    unfold hasCrossEdge at hedge
    rcases List.any_eq_true.mp hedge with ⟨⟨a, b⟩, hmem, hbits⟩
    simp only [Bool.and_eq_true] at hbits
    rcases crossBadPairs_sound v hv u huv (a, b) hmem with ⟨hab, hb16, hxor, hbad⟩
    have hlo_eq : lo % 256 + 256 * (lo / 256) = lo := by omega
    have hta : (lo + 65536 * hi).testBit a = true := by
      have ha1 : lo.testBit a = true := by
        rw [← hlo_eq, ← mkBits16_get (lo % 256) (lo / 256) a (Nat.mod_lt _ (by omega)) (by omega)]
        exact hbits.1
      rw [testBit_lo_hi16 lo hi a hlo]; simp [(by omega : a < 16), ha1]
    have htb : (lo + 65536 * hi).testBit b = true := by
      have hb1 : lo.testBit b = true := by
        rw [← hlo_eq, ← mkBits16_get (lo % 256) (lo / 256) b (Nat.mod_lt _ (by omega)) hb16]
        exact hbits.2
      rw [testBit_lo_hi16 lo hi b hlo]; simp [hb16, hb1]
    have htu : (lo + 65536 * hi).testBit (u + 16) = true := by
      rw [testBit_lo_hi16 lo hi (u + 16) hlo]
      have hge : ¬(u + 16 < 16) := by omega
      have hsub : u + 16 - 16 = u := by omega
      simp [hge, hsub, hbu]
    have htv : (lo + 65536 * hi).testBit (v + 16) = true := by
      rw [testBit_lo_hi16 lo hi (v + 16) hlo]
      have hge : ¬(v + 16 < 16) := by omega
      have hsub : v + 16 - 16 = v := by omega
      simp [hge, hsub, hbv]
    unfold isNormMultMask at hnm
    have h1 := (allNat_eq_true _ 32).mp hnm a (by omega)
    simp only [hta, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
    have h2 := (allNat_eq_true _ 32).mp h1 (u + 16) (by omega)
    have hau : a < u + 16 := by omega
    simp only [hau, htu, decide_true, Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2
    have h3 := (allNat_eq_true _ 32).mp h2 b (by omega)
    have hba : (b != a) = true := bne_iff_ne.mpr (by omega)
    have hbu2 : (b != u + 16) = true := bne_iff_ne.mpr (by omega)
    have hdv : a ^^^ (u + 16) ^^^ b = v + 16 := by
      have h1 : a ^^^ (u + 16) = (a ^^^ u) + 16 := xor_add_right (n := 4) (by omega) (by omega)
      have h2 : ((a ^^^ u) + 16) ^^^ b = ((a ^^^ u) ^^^ b) + 16 :=
        xor_add_left (n := 4) (Nat.xor_lt_two_pow (n := 4) (by omega) (by omega)) hb16
      have h3 : (a ^^^ u) ^^^ b = v := by
        have h4 : (a ^^^ u) ^^^ b = (a ^^^ b) ^^^ u := by
          apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
          cases a.testBit m <;> cases u.testBit m <;> cases b.testBit m <;> rfl
        rw [h4, hxor, xor_sub_self_cancel]
      rw [h1, h2, h3]
    simp only [htb, hba, hbu2, Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h3
    rw [hdv] at h3
    have hbv_lt : b < v + 16 := by omega
    have hv32 : v + 16 < 2 ^ 5 := by omega
    simp only [hbv_lt, hv32, htv, decide_true, Bool.and_true, Bool.not_true,
               Bool.false_eq_true, ↓reduceIte, hbad] at h3

/-- Core asymmetric half-ceiling: whenever `|S_lo| ≥ 8` in a norm-multiplicative subset of $\mathrm{CD}_5$,
    the total dimension is strictly bounded by `13` (`|S_lo| + |S_hi| ≤ 13`). -/
theorem pathion_lo_ge8_total_le_13 (lo hi : Nat) (hlo : lo < 65536) (hhi : hi < 65536)
    (hnm : isNormMultMask 5 (lo + 65536 * hi) = true) (h8 : 8 ≤ popcount16 lo) :
    popcount16 lo + popcount16 hi ≤ 13 := by
  rcases pathion_lo_valid_and_hi_indep lo hi hlo hhi hnm with ⟨hlo_nm, hhi_ind⟩
  let lo8 := lo % 256
  let hi8 := lo / 256
  have hlo8 : lo8 < 256 := Nat.mod_lt lo (by omega)
  have hhi8 : hi8 < 256 := by omega
  have hlo_eq : lo8 + 256 * hi8 = lo := by omega
  have hpop_lo : popcount16 lo = popcount8 lo8 + popcount8 hi8 := rfl
  have hind_lo : isIndepForb (forbMask4 lo8) hi8 = true := by
    rw [← hiAvoidsBad_eq_isIndepForb lo8 hi8 hhi8, ← isNormMultMask4_eq_hiAvoidsBad lo8 hi8 hlo8, hlo_eq]
    exact hlo_nm
  let lo8' := 2 * (lo8 / 2) + 1
  have hpop_le : popcount8 lo8 ≤ popcount8 lo8' := popcount8_le_odd lo8
  have hind_lo' : isIndepForb (forbMask4 lo8') hi8 = true := by
    unfold isIndepForb at hind_lo ⊢
    rw [allNat_eq_true] at hind_lo ⊢
    intro u hu
    rw [forbMask4_ignore_bit0 lo8 hlo8 u hu]
    exact hind_lo u hu
  have hchk2 := checkIndepHi_sound lo8' hi8 hhi8 hind_lo' (by omega) 8 0 (popcount8 lo8')
    (Nat.le_refl 8) (by omega) (by simp [popcount8]) (checkPathionOdd_all (lo8 / 2) (by omega))
  have hdiv : ∀ m, 1 ≤ m → lo8' / (2 ^ m) = lo8 / (2 ^ m) := by
    intro m hm
    have hm' : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : m = (m - 1) + 1 := by omega
      conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
    rw [hm', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have : lo8' / 2 = lo8 / 2 := by omega
    rw [this]
  have h1 : lo8' / 2 = lo8 / 2 := hdiv 1 (by omega)
  have h2 : lo8' / 4 = lo8 / 4 := hdiv 2 (by omega)
  have h3 : lo8' / 8 = lo8 / 8 := hdiv 3 (by omega)
  have h4 : lo8' / 16 = lo8 / 16 := hdiv 4 (by omega)
  have h5 : lo8' / 32 = lo8 / 32 := hdiv 5 (by omega)
  have h6 : lo8' / 64 = lo8 / 64 := hdiv 6 (by omega)
  have h7 : lo8' / 128 = lo8 / 128 := hdiv 7 (by omega)
  have hcl_vtx : greedyCliquesVtx (mkBits16 lo8' hi8) = greedyCliquesVtx (mkBits16 lo8 hi8) :=
    greedyCliquesVtx_ignore_b0 (mkBits16 lo8' hi8) (mkBits16 lo8 hi8)
      (by simp only [mkBits16, h1])
      (by simp only [mkBits16, h2])
      (by simp only [mkBits16, h3])
      (by simp only [mkBits16, h4])
      (by simp only [mkBits16, h5])
      (by simp only [mkBits16, h6])
      (by simp only [mkBits16, h7])
      rfl rfl rfl rfl rfl rfl rfl rfl
  have hcl_eq : (greedyCliques (mkBits16 lo8' hi8)).length = (greedyCliques (mkBits16 lo8 hi8)).length := by
    rw [greedyCliques_length, greedyCliques_length, hcl_vtx]
  rw [hcl_eq] at hchk2
  have hspec := greedyCliques_spec (mkBits16 lo8 hi8)
  have hhi_le := popcount16_le_clique_cover (mkBits16 lo8 hi8) hi
    (greedyCliques (mkBits16 lo8 hi8)) hspec.1 hspec.2 hhi_ind
  omega

/-! ### Part 4: Lift from Bitmask to Arbitrary Duplicate-Free Lists (`isNormMultPair 5 S S`) -/

@[expose] def listToMask : List Nat → Nat
  | [] => 0
  | x :: xs => (1 <<< x) ||| listToMask xs

theorem testBit_listToMask (S : List Nat) (k : Nat) :
    (listToMask S).testBit k = decide (k ∈ S) := by
  induction S with
  | nil => simp [listToMask]
  | cons a tl ih =>
    unfold listToMask
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    by_cases hka : k = a
    · subst hka; simp
    · have h1 : (decide (a ≤ k) && Nat.testBit 1 (k - a)) = false := by
        by_cases hle : a ≤ k
        · simp [hle, testBit_one_of_ne_zero (by omega : k - a ≠ 0)]
        · simp [hle]
      simp [h1, hka]

theorem listToMask_lt_two_pow (n : Nat) (S : List Nat) (hbound : ∀ x ∈ S, x < n) :
    listToMask S < 2 ^ n := by
  induction S with
  | nil => exact Nat.two_pow_pos n
  | cons a tl ih =>
    unfold listToMask
    have ha : a < n := hbound a (List.mem_cons_self ..)
    have hsh : 1 <<< a < 2 ^ n := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.pow_lt_pow_right (by omega) ha
    exact Nat.or_lt_two_pow hsh (ih (fun x hx => hbound x (List.mem_cons_of_mem a hx)))

theorem countPred_mem_nodup :
    ∀ (m : Nat) (S : List Nat), S.Nodup → (∀ x ∈ S, x < m) →
      countPred (fun k => decide (k ∈ S)) m = S.length := by
  intro m
  induction m with
  | zero =>
    intro S _ hlt
    cases S with
    | nil => rfl
    | cons a _ => have := hlt a (List.mem_cons_self ..); omega
  | succ m ih =>
    intro S hnd hlt
    unfold countPred
    let S' := S.filter (fun x => x != m)
    have hnd' : S'.Nodup := list_nodup_filter _ hnd
    have hlt' : ∀ x ∈ S', x < m := by
      intro x hx
      have hm := List.mem_filter.mp hx
      have hxlt := hlt x hm.1
      have hxne : x ≠ m := bne_iff_ne.mp hm.2
      omega
    have hext : countPred (fun k => decide (k ∈ S)) m = countPred (fun k => decide (k ∈ S')) m := by
      apply countPred_ext; intro k hk
      have hkne : (k != m) = true := bne_iff_ne.mpr (by omega)
      simp [S', List.mem_filter, hkne]
    rw [hext, ih S' hnd' hlt']
    have hpart := list_length_filter_partition (fun x => x != m) S
    let Sm := S.filter (fun x => !(x != m))
    have hSm_len : Sm.length = if m ∈ S then 1 else 0 := by
      have hSm_nd : Sm.Nodup := list_nodup_filter _ hnd
      have hSm_eq : ∀ x ∈ Sm, x = m := by
        intro x hx
        have h1 := (List.mem_filter.mp hx).2
        simp only [Bool.not_eq_true', bne_eq_false_iff_eq] at h1
        exact h1
      by_cases hm : m ∈ S
      · simp only [hm, ↓reduceIte]
        have hm_in : m ∈ Sm := List.mem_filter.mpr ⟨hm, by simp⟩
        cases hSm : Sm with
        | nil => rw [hSm] at hm_in; cases hm_in
        | cons a tl =>
          rw [hSm] at hSm_nd
          rw [List.nodup_cons] at hSm_nd
          have ha : a = m := hSm_eq a (by rw [hSm]; exact List.mem_cons_self ..)
          cases tl with
          | nil => rfl
          | cons b _ =>
            have hb : b = m := hSm_eq b (by rw [hSm]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
            rw [ha, ← hb] at hSm_nd
            exact absurd (List.mem_cons_self ..) hSm_nd.1
      · simp only [hm, ↓reduceIte]
        cases hSm : Sm with
        | nil => rfl
        | cons a _ =>
          have ha_in : a ∈ Sm := by rw [hSm]; exact List.mem_cons_self ..
          have ha_eq : a = m := hSm_eq a ha_in
          exact absurd (ha_eq ▸ (List.mem_filter.mp ha_in).1) hm
    change S'.length + Sm.length = S.length at hpart
    rw [hSm_len] at hpart
    by_cases hm : m ∈ S <;> simp [hm] at hpart ⊢ <;> omega

theorem popcount_listToMask_splits (S : List Nat) (hnd : S.Nodup) (hbound : ∀ x ∈ S, x < 32) :
    popcount16 (listToMask S % 65536) = (S.filter (fun x => decide (x < 16))).length ∧
    popcount16 (listToMask S / 65536) = (S.filter (fun x => decide (16 ≤ x))).length ∧
    popcount32 (listToMask S) = S.length := by
  have hlo : popcount16 (listToMask S % 65536) = (S.filter (fun x => decide (x < 16))).length := by
    rw [popcount16_eq_countPred]
    have hext : countPred (fun k => (listToMask S % 65536).testBit k) 16 =
                countPred (fun k => decide (k ∈ S.filter (fun x => decide (x < 16)))) 16 := by
      apply countPred_ext; intro k hk
      rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
      simp [hk, testBit_listToMask, List.mem_filter]
    rw [hext]
    exact countPred_mem_nodup 16 _ (list_nodup_filter _ hnd)
      (fun x hx => decide_eq_true_eq.mp (List.mem_filter.mp hx).2)
  have hhi : popcount16 (listToMask S / 65536) = (S.filter (fun x => decide (16 ≤ x))).length := by
    rw [popcount16_eq_countPred]
    let Shi := (S.filter (fun x => decide (16 ≤ x))).map (· - 16)
    have hnd_hi : Shi.Nodup :=
      list_nodup_map_sub 16 (list_nodup_filter _ hnd)
        (fun x hx => decide_eq_true_eq.mp (List.mem_filter.mp hx).2)
    have hlt_hi : ∀ x ∈ Shi, x < 16 := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
      have h1 := hbound u (List.mem_filter.mp hu).1
      have h2 := decide_eq_true_eq.mp (List.mem_filter.mp hu).2
      omega
    have hext : countPred (fun k => (listToMask S / 65536).testBit k) 16 =
                countPred (fun k => decide (k ∈ Shi)) 16 := by
      apply countPred_ext; intro k hk
      rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_div_two_pow, testBit_listToMask]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Shi, List.mem_map, List.mem_filter]
      constructor
      · intro hmem
        exact ⟨k + 16, ⟨hmem, by omega⟩, by omega⟩
      · rintro ⟨u, ⟨hu, h16⟩, hsub⟩
        have : u = k + 16 := by omega
        rw [← this]; exact hu
    rw [hext, countPred_mem_nodup 16 Shi hnd_hi hlt_hi, List.length_map]
  have hpart := list_length_filter_partition (fun x => decide (x < 16)) S
  have hfeq : S.filter (fun x => !(decide (x < 16))) = S.filter (fun x => decide (16 ≤ x)) := by
    congr 1; funext x
    by_cases h : x < 16
    · have h2 : ¬(16 ≤ x) := by omega
      simp [h, h2]
    · have h2 : 16 ≤ x := by omega
      simp [h, h2]
  rw [hfeq] at hpart
  unfold popcount32
  exact ⟨hlo, hhi, by omega⟩

theorem isNormMultPair_implies_mask5 (S : List Nat) (hnm : isNormMultPair 5 S S) :
    isNormMultMask 5 (listToMask S) = true := by
  unfold isNormMultMask
  rw [allNat_eq_true]; intro a ha
  by_cases hta : (listToMask S).testBit a = true
  · simp only [hta, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have haS : a ∈ S := by rw [testBit_listToMask] at hta; exact decide_eq_true_eq.mp hta
    rw [allNat_eq_true]; intro b hb
    by_cases hcb : (a < b && (listToMask S).testBit b) = true
    · simp only [hcb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq, testBit_listToMask] at hcb
      rw [allNat_eq_true]; intro c hc
      by_cases hcc : ((listToMask S).testBit c && c != a && c != b) = true
      · simp only [hcc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.and_eq_true, testBit_listToMask, decide_eq_true_eq, bne_iff_ne] at hcc
        let d := a ^^^ b ^^^ c
        change (if !(decide (c < d) && decide (d < 2 ^ 5) && (listToMask S).testBit d) then true
                else pairingCancels 5 a b c d) = true
        by_cases hcd : (decide (c < d) && decide (d < 2 ^ 5) && (listToMask S).testBit d) = true
        · simp only [hcd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq, testBit_listToMask] at hcd
          have hxor : a ^^^ b = c ^^^ d := by
            show a ^^^ b = c ^^^ (a ^^^ b ^^^ c)
            apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor]
            cases a.testBit m <;> cases b.testBit m <;> cases c.testBit m <;> rfl
          unfold pairingCancels
          exact beq_iff_eq.mpr (hnm.2.2 a haS b hcb.2 c hcc.1.1 d hcd.2 (by omega) (by omega) hxor)
        · simp only [Bool.eq_false_iff.mpr hcd, Bool.not_false, ↓reduceIte]
      · simp [Bool.eq_false_iff.mpr hcc]
    · simp [Bool.eq_false_iff.mpr hcb]
  · simp [Bool.eq_false_iff.mpr hta]

/-- **Theorem T4e (Exact Pathion Symmetric Coordinate Ceiling $r_{\max}(\mathrm{CD}_5) = 14$ & Strict $7+7$ Half-Balance Rigidity):**
    Pure-kernel proof over ALL $2^{32} = 4{,}294{,}967{,}296$ coordinate subsets of $\mathrm{CD}_5$
    (zero HiGHS MILP, zero DFS, zero backtracking, zero `native_decide`):
    1. Every norm-multiplicative bitmask $m < 2^{32}$ has $\mathrm{popcount}_{32}(m) \le 14$.
    2. Every 14-dimensional norm-multiplicative bitmask splits strictly $7 + 7$ across
       $\{0..15\}$ and $\{16..31\}$.
    3. Equivalently, every duplicate-free list $S$ satisfying `isNormMultPair 5 S S` has
       $|S| \le 14$, and $|S| = 14 \implies |S \cap \{0..15\}| = 7 \land |S \cap \{16..31\}| = 7$. -/
theorem pathion_exact_ceiling_14_and_7_7_rigidity :
    (∀ m, m < 2 ^ 32 → isNormMultMask 5 m = true → popcount32 m ≤ 14) ∧
    (∀ m, m < 2 ^ 32 → isNormMultMask 5 m = true → popcount32 m = 14 →
      popcount16 (m % 65536) = 7 ∧ popcount16 (m / 65536) = 7) ∧
    (∀ S : List Nat, S.Nodup → isNormMultPair 5 S S →
      S.length ≤ 14 ∧
      (S.length = 14 →
        (S.filter (fun x => decide (x < 16))).length = 7 ∧
        (S.filter (fun x => decide (16 ≤ x))).length = 7)) := by
  have hmain : ∀ m, m < 2 ^ 32 → isNormMultMask 5 m = true →
      popcount32 m ≤ 14 ∧
      (popcount32 m = 14 → popcount16 (m % 65536) = 7 ∧ popcount16 (m / 65536) = 7) := by
    intro m hm hnm
    let lo := m % 65536
    let hi := m / 65536
    have hlo : lo < 65536 := Nat.mod_lt m (by omega)
    have hhi : hi < 65536 := by
      have h232 : 2 ^ 32 = 65536 * 65536 := rfl
      omega
    have hm_eq : lo + 65536 * hi = m := by omega
    have hpop_m : popcount32 m = popcount16 lo + popcount16 hi := rfl
    have hlo_def : popcount16 (m % 65536) = popcount16 lo := rfl
    have hhi_def : popcount16 (m / 65536) = popcount16 hi := rfl
    rw [← hm_eq] at hnm
    by_cases h8lo : 8 ≤ popcount16 lo
    · have h13 := pathion_lo_ge8_total_le_13 lo hi hlo hhi hnm h8lo
      exact ⟨by omega, fun h14 => by omega⟩
    · by_cases h8hi : 8 ≤ popcount16 hi
      · have hsw := isNormMultMask5_swap16 lo hi hlo hhi hnm
        have h13 := pathion_lo_ge8_total_le_13 hi lo hhi hlo hsw h8hi
        exact ⟨by omega, fun h14 => by omega⟩
      · exact ⟨by omega, fun h14 => ⟨by omega, by omega⟩⟩
  refine ⟨fun m hm hnm => (hmain m hm hnm).1, fun m hm hnm => (hmain m hm hnm).2, ?_⟩
  intro S hnd hnm
  have hlt : listToMask S < 2 ^ 32 := listToMask_lt_two_pow 32 S hnm.1
  have hmask : isNormMultMask 5 (listToMask S) = true := isNormMultPair_implies_mask5 S hnm
  rcases hmain (listToMask S) hlt hmask with ⟨hle, h77⟩
  rcases popcount_listToMask_splits S hnd hnm.1 with ⟨hlo, hhi, htot⟩
  rw [htot] at hle h77
  refine ⟨hle, fun h14 => ?_⟩
  rcases h77 h14 with ⟨h1, h2⟩
  exact ⟨hlo.symm.trans h1, hhi.symm.trans h2⟩

/-! ### Part 5: Theorem T4f — Dimension-64 Split-Signature Interior Spectral Gap Phase Transition -/

/-- Exact $O(1)$ closed-form standard nullity of $\mathrm{CD}_6$ ($1 \le i < j < 64$),
    proved directly from `TerraceLaw` (`nullity_doubling_*` + `nu5Closed_eq`). -/
@[expose] def nu6Closed (i j : Nat) : Nat :=
  if i < 32 then
    if j < 32 then 2 * nu5Closed i j
    else if j == 32 then 0
    else if j == i + 32 then 0
    else 28 - 2 * (if i < j - 32 then nu5Closed i (j - 32) else nu5Closed (j - 32) i)
  else if i == 32 then 0
  else 2 * nu5Closed (i - 32) (j - 32)

theorem nu6Closed_eq (i j : Nat) (hi0 : 0 < i) (hij : i < j) (hj : j < 64) :
    nu6Closed i j = twobladeNullity 6 i j := by
  unfold nu6Closed
  by_cases hi32 : i < 32
  · simp only [hi32, ↓reduceIte]
    by_cases hj32 : j < 32
    · simp only [hj32, ↓reduceIte]
      rw [nu5Closed_eq i j hi0 hij hj32,
          nullity_doubling_lower 5 i j hi0 (by omega) hi32 hj32 (by omega)]
    · simp only [hj32, ↓reduceIte]
      by_cases hj_eq : j = 32
      · subst hj_eq
        simp only [beq_self_eq_true, ↓reduceIte]
        exact (nullity_doubling_axis 5 i hi0 hi32).2.1.symm
      · have hjb : (j == 32) = false := beq_false_of_ne hj_eq
        simp only [hjb, Bool.false_eq_true, ↓reduceIte]
        by_cases hjd : j = i + 32
        · subst hjd
          simp only [beq_self_eq_true, ↓reduceIte]
          exact (nullity_doubling_axis 5 i hi0 hi32).2.2.symm
        · have hjdb : (j == i + 32) = false := beq_false_of_ne hjd
          simp only [hjdb, Bool.false_eq_true, ↓reduceIte]
          let b := j - 32
          have hjb_eq : j = b + 32 := by omega
          have hblt : b < 32 := by omega
          have hb0 : 0 < b := by omega
          have hib_ne : i ≠ b := by omega
          have hcr := nullity_doubling_cross 5 i b (by omega) hi0 hb0 hi32 hblt hib_ne
          rw [hjb_eq, hcr]
          have h28 : 2 ^ 5 - 4 = 28 := rfl
          have hsub : b + 32 - 32 = b := by omega
          rw [h28, hsub]
          by_cases hib : i < b
          · simp only [hib, ↓reduceIte, nu5Closed_eq i b hi0 hib hblt]
          · simp only [hib, ↓reduceIte, nu5Closed_eq b i hb0 (by omega) hi32, twobladeNullity_symm 5 b i]
  · simp only [hi32, ↓reduceIte]
    by_cases hi_eq : i = 32
    · subst hi_eq
      simp only [beq_self_eq_true, ↓reduceIte]
      let b := j - 32
      have hjb_eq : j = b + 32 := by omega
      rw [hjb_eq]; exact (nullity_doubling_axis 5 b (by omega) (by omega)).1.symm
    · have hib : (i == 32) = false := beq_false_of_ne hi_eq
      simp only [hib, Bool.false_eq_true, ↓reduceIte]
      let a := i - 32
      let b := j - 32
      have ha_eq : i = a + 32 := by omega
      have hb_eq : j = b + 32 := by omega
      rw [ha_eq, hb_eq, nullity_doubling_upper 5 a b (by omega) (by omega) (by omega) (by omega) (by omega)]
      have hsa : a + 32 - 32 = a := by omega
      have hsb : b + 32 - 32 = b := by omega
      rw [hsa, hsb, nu5Closed_eq a b (by omega) (by omega) (by omega)]

/-- Pure C-primitive 3-bit parity (`x % 2 + (x/2)%2 + (x/4)%2` mod 2), zero `Nat.bitwise`. -/
@[expose] def parity3 (x : Nat) : Bool :=
  (x % 2 + (x / 2) % 2 + (x / 4) % 2) % 2 == 1

theorem parityBits6_flip56 (i j : Nat) :
    parityBits 6 ((i ^^^ j) &&& 56) = xor (parity3 (i / 8)) (parity3 (j / 8)) := by
  have hbit : ∀ (z k : Nat), ((z / 2 ^ k) % 2 == 1) = z.testBit k := bitAt_eq_testBit
  have hp6 : ∀ z, parityBits 6 z =
      xor (z.testBit 0) (xor (z.testBit 1) (xor (z.testBit 2)
        (xor (z.testBit 3) (xor (z.testBit 4) (z.testBit 5))))) := by
    intro z
    unfold parityBits parityBits parityBits parityBits parityBits parityBits parityBits
    simp only [Bool.xor_false]
    have h0 : (z % 2 == 1) = z.testBit 0 := by simpa using hbit z 0
    have h1 : (z / 2 % 2 == 1) = z.testBit 1 := hbit z 1
    have h2 : (z / 2 / 2 % 2 == 1) = z.testBit 2 := by rw [Nat.div_div_eq_div_mul]; exact hbit z 2
    have h3 : (z / 2 / 2 / 2 % 2 == 1) = z.testBit 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact hbit z 3
    have h4 : (z / 2 / 2 / 2 / 2 % 2 == 1) = z.testBit 4 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact hbit z 4
    have h5 : (z / 2 / 2 / 2 / 2 / 2 % 2 == 1) = z.testBit 5 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      exact hbit z 5
    rw [h0, h1, h2, h3, h4, h5]
  have hp3 : ∀ x, parity3 (x / 8) = xor (x.testBit 3) (xor (x.testBit 4) (x.testBit 5)) := by
    intro x
    unfold parity3
    have b0 : (x / 8) % 2 = if x.testBit 3 then 1 else 0 := by
      have h := mod2_eq_ite_testBit x 3; simpa using h
    have b1 : (x / 8 / 2) % 2 = if x.testBit 4 then 1 else 0 := by
      rw [Nat.div_div_eq_div_mul]; exact mod2_eq_ite_testBit x 4
    have b2 : (x / 8 / 4) % 2 = if x.testBit 5 then 1 else 0 := by
      rw [Nat.div_div_eq_div_mul]; exact mod2_eq_ite_testBit x 5
    rw [b0, b1, b2]
    cases x.testBit 3 <;> cases x.testBit 4 <;> cases x.testBit 5 <;> rfl
  rw [hp6, hp3 i, hp3 j]
  simp only [Nat.testBit_and, Nat.testBit_xor]
  have t56 : (56 : Nat).testBit 0 = false ∧ (56 : Nat).testBit 1 = false ∧
             (56 : Nat).testBit 2 = false ∧ (56 : Nat).testBit 3 = true ∧
             (56 : Nat).testBit 4 = true ∧ (56 : Nat).testBit 5 = true := by decide
  rw [t56.1, t56.2.1, t56.2.2.1, t56.2.2.2.1, t56.2.2.2.2.1, t56.2.2.2.2.2]
  simp only [Bool.and_false, Bool.and_true, Bool.false_xor]
  cases i.testBit 3 <;> cases i.testBit 4 <;> cases i.testBit 5 <;>
  cases j.testBit 3 <;> cases j.testBit 4 <;> cases j.testBit 5 <;> rfl

/-- Balanced binary-tree 4-bin accumulator (depth 6 + 6 = 12, zero `Nat.bitwise`) for `CD_6(56)`. -/
@[expose] def quadAdd (a b : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

@[expose] def sumQuadTree (f : Nat → Nat × Nat × Nat × Nat) : Nat → Nat → Nat × Nat × Nat × Nat
  | s, 0 => f s
  | s, d + 1 => quadAdd (sumQuadTree f s d) (sumQuadTree f (s + 2 ^ d) d)

@[expose] def cd6Cell56 (i j : Nat) : Nat × Nat × Nat × Nat :=
  if i == 0 then (0, 0, 0, 0)
  else if i < j then
    let nu := if xor (parity3 (i / 8)) (parity3 (j / 8)) then 32 - nu6Closed i j else nu6Closed i j
    if nu == 0 then (1, 0, 0, 0)
    else if nu == 4 then (0, 1, 0, 0)
    else if nu == 8 then (0, 0, 1, 0)
    else if nu == 12 then (0, 0, 0, 1)
    else (0, 0, 0, 0)
  else (0, 0, 0, 0)

@[expose] def cd6QuadTree56 : Nat × Nat × Nat × Nat :=
  sumQuadTree (fun i => sumQuadTree (fun j => cd6Cell56 i j) 0 6) 0 6

theorem sumNat_add_split (g : Nat → Nat) (a b : Nat) :
    sumNat g (a + b) = sumNat g a + sumNat (fun k => g (a + k)) b := by
  induction b with
  | zero => simp [sumNat]
  | succ b ih =>
    rw [Nat.add_succ]
    show sumNat g (a + b) + g (a + b) = sumNat g a + (sumNat (fun k => g (a + k)) b + g (a + b))
    rw [ih]; omega

theorem sumQuadTree_eq_sumNat (f : Nat → Nat × Nat × Nat × Nat) :
    ∀ d s,
      (sumQuadTree f s d).1 = sumNat (fun k => (f (s + k)).1) (2 ^ d) ∧
      (sumQuadTree f s d).2.1 = sumNat (fun k => (f (s + k)).2.1) (2 ^ d) ∧
      (sumQuadTree f s d).2.2.1 = sumNat (fun k => (f (s + k)).2.2.1) (2 ^ d) ∧
      (sumQuadTree f s d).2.2.2 = sumNat (fun k => (f (s + k)).2.2.2) (2 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro s
    simp [sumQuadTree, sumNat]
  | succ d ih =>
    intro s
    unfold sumQuadTree quadAdd
    rcases ih s with ⟨h1L, h2L, h3L, h4L⟩
    rcases ih (s + 2 ^ d) with ⟨h1R, h2R, h3R, h4R⟩
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow, sumNat_add_split, sumNat_add_split, sumNat_add_split, sumNat_add_split]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · dsimp only
      first | rw [h1L, h1R] | rw [h2L, h2R] | rw [h3L, h3R] | rw [h4L, h4R]
      congr 1; apply sumNat_ext; intro k _; rw [Nat.add_assoc]

theorem cd6QuadTree56_eq :
    cd6QuadTree56 =
      (nullityHistGamma 6 56 0, nullityHistGamma 6 56 4,
       nullityHistGamma 6 56 8, nullityHistGamma 6 56 12) := by
  have hcell : ∀ i j,
      (cd6Cell56 i j).1 = (if i = 0 then 0 else if i < j then
        if (if parityBits 6 ((i ^^^ j) &&& 56) then 32 - nu6Closed i j else nu6Closed i j) == 0
        then 1 else 0 else 0) ∧
      (cd6Cell56 i j).2.1 = (if i = 0 then 0 else if i < j then
        if (if parityBits 6 ((i ^^^ j) &&& 56) then 32 - nu6Closed i j else nu6Closed i j) == 4
        then 1 else 0 else 0) ∧
      (cd6Cell56 i j).2.2.1 = (if i = 0 then 0 else if i < j then
        if (if parityBits 6 ((i ^^^ j) &&& 56) then 32 - nu6Closed i j else nu6Closed i j) == 8
        then 1 else 0 else 0) ∧
      (cd6Cell56 i j).2.2.2 = (if i = 0 then 0 else if i < j then
        if (if parityBits 6 ((i ^^^ j) &&& 56) then 32 - nu6Closed i j else nu6Closed i j) == 12
        then 1 else 0 else 0) := by
    intro i j
    unfold cd6Cell56
    rw [parityBits6_flip56 i j]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have hib : (i == 0) = false := beq_false_of_ne hi0
      simp only [hi0, hib, Bool.false_eq_true, ↓reduceIte]
      by_cases hij : i < j
      · simp only [hij, ↓reduceIte]
        let nu := if xor (parity3 (i / 8)) (parity3 (j / 8)) then 32 - nu6Closed i j else nu6Closed i j
        by_cases h0 : nu = 0
        · have h0b : (nu == 0) = true := beq_iff_eq.mpr h0
          have h4b : (nu == 4) = false := beq_false_of_ne (by omega)
          have h8b : (nu == 8) = false := beq_false_of_ne (by omega)
          have h12b : (nu == 12) = false := beq_false_of_ne (by omega)
          simp only [nu, h0b, h4b, h8b, h12b, Bool.false_eq_true, ↓reduceIte]
          exact ⟨trivial, trivial, trivial, trivial⟩
        · have h0b : (nu == 0) = false := beq_false_of_ne h0
          by_cases h4 : nu = 4
          · have h4b : (nu == 4) = true := beq_iff_eq.mpr h4
            have h8b : (nu == 8) = false := beq_false_of_ne (by omega)
            have h12b : (nu == 12) = false := beq_false_of_ne (by omega)
            simp only [nu, h0b, h4b, h8b, h12b, Bool.false_eq_true, ↓reduceIte]
            exact ⟨trivial, trivial, trivial, trivial⟩
          · have h4b : (nu == 4) = false := beq_false_of_ne h4
            by_cases h8 : nu = 8
            · have h8b : (nu == 8) = true := beq_iff_eq.mpr h8
              have h12b : (nu == 12) = false := beq_false_of_ne (by omega)
              simp only [nu, h0b, h4b, h8b, h12b, Bool.false_eq_true, ↓reduceIte]
              exact ⟨trivial, trivial, trivial, trivial⟩
            · have h8b : (nu == 8) = false := beq_false_of_ne h8
              by_cases h12 : nu = 12
              · have h12b : (nu == 12) = true := beq_iff_eq.mpr h12
                simp only [nu, h0b, h4b, h8b, h12b, Bool.false_eq_true, ↓reduceIte]
                exact ⟨trivial, trivial, trivial, trivial⟩
              · have h12b : (nu == 12) = false := beq_false_of_ne h12
                simp only [nu, h0b, h4b, h8b, h12b, Bool.false_eq_true, ↓reduceIte]
                exact ⟨trivial, trivial, trivial, trivial⟩
      · simp [hij]
  have hout := sumQuadTree_eq_sumNat (fun i => sumQuadTree (fun j => cd6Cell56 i j) 0 6) 6 0
  have h0 := nullityHistGamma_eq_fast 6 56 0 (by omega) nu6Closed nu6Closed_eq
  have h4 := nullityHistGamma_eq_fast 6 56 4 (by omega) nu6Closed nu6Closed_eq
  have h8 := nullityHistGamma_eq_fast 6 56 8 (by omega) nu6Closed nu6Closed_eq
  have h12 := nullityHistGamma_eq_fast 6 56 12 (by omega) nu6Closed nu6Closed_eq
  have hzero_sum : ∀ (P : Nat → Nat), (∀ j, j < 64 → P j = 0) → sumNat P 64 = 0 := by
    intro P hP
    have h : ∀ m, m ≤ 64 → sumNat P m = 0 := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ihm => unfold sumNat; rw [ihm (by omega), hP m (by omega)]
    exact h 64 (Nat.le_refl _)
  have h1 : cd6QuadTree56.1 = nullityHistGamma 6 56 0 := by
    rw [cd6QuadTree56, hout.1, h0]
    apply sumNat_ext; intro i _
    rw [Nat.zero_add, (sumQuadTree_eq_sumNat (fun j => cd6Cell56 i j) 6 0).1]
    by_cases hi0 : i = 0
    · subst hi0; simp only [↓reduceIte]
      exact hzero_sum _ (fun j _ => by rw [Nat.zero_add, (hcell 0 j).1]; rfl)
    · simp only [hi0, ↓reduceIte]
      apply sumNat_ext; intro j _
      rw [Nat.zero_add, (hcell i j).1]; simp [hi0]
  have h2 : cd6QuadTree56.2.1 = nullityHistGamma 6 56 4 := by
    rw [cd6QuadTree56, hout.2.1, h4]
    apply sumNat_ext; intro i _
    rw [Nat.zero_add, (sumQuadTree_eq_sumNat (fun j => cd6Cell56 i j) 6 0).2.1]
    by_cases hi0 : i = 0
    · subst hi0; simp only [↓reduceIte]
      exact hzero_sum _ (fun j _ => by rw [Nat.zero_add, (hcell 0 j).2.1]; rfl)
    · simp only [hi0, ↓reduceIte]
      apply sumNat_ext; intro j _
      rw [Nat.zero_add, (hcell i j).2.1]; simp [hi0]
  have h3 : cd6QuadTree56.2.2.1 = nullityHistGamma 6 56 8 := by
    rw [cd6QuadTree56, hout.2.2.1, h8]
    apply sumNat_ext; intro i _
    rw [Nat.zero_add, (sumQuadTree_eq_sumNat (fun j => cd6Cell56 i j) 6 0).2.2.1]
    by_cases hi0 : i = 0
    · subst hi0; simp only [↓reduceIte]
      exact hzero_sum _ (fun j _ => by rw [Nat.zero_add, (hcell 0 j).2.2.1]; rfl)
    · simp only [hi0, ↓reduceIte]
      apply sumNat_ext; intro j _
      rw [Nat.zero_add, (hcell i j).2.2.1]; simp [hi0]
  have h4eq : cd6QuadTree56.2.2.2 = nullityHistGamma 6 56 12 := by
    rw [cd6QuadTree56, hout.2.2.2, h12]
    apply sumNat_ext; intro i _
    rw [Nat.zero_add, (sumQuadTree_eq_sumNat (fun j => cd6Cell56 i j) 6 0).2.2.2]
    by_cases hi0 : i = 0
    · subst hi0; simp only [↓reduceIte]
      exact hzero_sum _ (fun j _ => by rw [Nat.zero_add, (hcell 0 j).2.2.2]; rfl)
    · simp only [hi0, ↓reduceIte]
      apply sumNat_ext; intro j _
      rw [Nat.zero_add, (hcell i j).2.2.2]; simp [hi0]
  cases h : cd6QuadTree56 with
  | mk a b =>
    cases b with
    | mk b c =>
      cases c with
      | mk c d =>
        rw [h] at h1 h2 h3 h4eq
        dsimp only at h1 h2 h3 h4eq
        rw [h1, h2, h3, h4eq]

theorem cd6_std_mirror_sums :
    nullityHist 6 0 + nullityHist 6 32 = 435 ∧
    nullityHist 6 4 + nullityHist 6 28 = 594 ∧
    nullityHist 6 8 + nullityHist 6 24 = 420 ∧
    nullityHist 6 12 + nullityHist 6 20 = 336 := by
  have h0 : nullityHist 6 0 = 435 := by
    have h := nonZDCount_all_n 6 (by omega)
    rw [show nonZDCountFormula 6 = 435 from rfl] at h
    exact h
  have h32 : nullityHist 6 32 = 0 := by
    unfold nullityHist
    rw [nullityHistGamma_eq_fast 6 0 32 (by omega) nu6Closed nu6Closed_eq]
    have hzero : ∀ (P : Nat → Nat) (m : Nat), (∀ k, k < m → P k = 0) → sumNat P m = 0 := by
      intro P m hP
      induction m with
      | zero => rfl
      | succ m ihm => unfold sumNat; rw [ihm (fun k hk => hP k (by omega)), hP m (by omega)]
    apply hzero; intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · simp only [hi0, ↓reduceIte]
      apply hzero; intro j hj
      by_cases hij : i < j
      · simp only [hij, ↓reduceIte]
        have hpar : parityBits 6 0 = false := rfl
        have hle := (nullity_mod4_and_bound 6 (by omega) i j (by omega) (by omega) hi hj (by omega)).2 (by omega)
        rw [Nat.and_zero, hpar, nu6Closed_eq i j (by omega) hij hj]
        have hne : (twobladeNullity 6 i j == 32) = false := beq_false_of_ne (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte, hne]
      · simp [hij]
  have h28 : nullityHist 6 28 = 342 := by
    have h := terrace_top_bin_all_n 5 (by omega)
    rw [show 5 + 1 = 6 from rfl, show 2 ^ 5 - 4 = 28 from rfl,
        show 2 * nonZDCountFormula 5 = 342 from rfl] at h
    exact h
  have h4 : nullityHist 6 4 = 252 := by
    have htop := terrace_top_jump_all_n 5 (by omega)
    rw [show 5 + 1 = 6 from rfl, show 2 ^ 5 - 4 = 28 from rfl, show 3 * (2 ^ 5 - 2) = 90 from rfl] at htop
    omega
  have h54 : nullityHist 5 4 = 84 := by
    have h12 : nullityHist 5 12 = 126 := by
      have h := terrace_top_bin_all_n 4 (by omega)
      rw [show 4 + 1 = 5 from rfl, show 2 ^ 4 - 4 = 12 from rfl,
          show 2 * nonZDCountFormula 4 = 126 from rfl] at h
      exact h
    have htop := terrace_top_jump_all_n 4 (by omega)
    rw [show 4 + 1 = 5 from rfl, show 2 ^ 4 - 4 = 12 from rfl, show 3 * (2 ^ 4 - 2) = 42 from rfl] at htop
    omega
  have h8 : nullityHist 6 8 = 168 := by
    have he := terrace_interleave_even 5 1 (by omega) (by omega)
    rw [show 5 + 1 = 6 from rfl, show 8 * 1 = 8 from rfl, show 4 * 1 = 4 from rfl] at he
    omega
  have h24 : nullityHist 6 24 = 252 := by
    have hp := terrace_palindrome_all_n 5 1 (by omega) (by omega) (by omega)
    rw [show 5 + 1 = 6 from rfl, show 4 * 1 = 4 from rfl, show 2 ^ 5 - 4 - 4 = 24 from rfl] at hp
    omega
  have h12 : nullityHist 6 12 = 168 := by
    have ho := terrace_interleave_odd 5 2 (by omega) (by omega)
    have h58 : nullityHist 5 8 = 84 := by
      have h := terrace_midpoint_std_all_n 5 (by omega)
      rw [show 2 ^ (5 - 2) = 8 from rfl, show 42 * 2 ^ (5 - 4) = 84 from rfl] at h
      exact h
    rw [show 5 + 1 = 6 from rfl, show 2 ^ 5 - 4 - 8 * 2 = 12 from rfl, show 4 * 2 = 8 from rfl] at ho
    omega
  have h20 : nullityHist 6 20 = 168 := by
    have hp := terrace_palindrome_all_n 5 2 (by omega) (by omega) (by omega)
    rw [show 5 + 1 = 6 from rfl, show 4 * 2 = 8 from rfl, show 2 ^ 5 - 4 - 8 = 20 from rfl] at hp
    omega
  omega

/-- **Theorem T4f (Dimension-64 Split-Signature Interior Spectral Gap Phase Transition):**
    At dimension 64 in $\mathrm{CD}_6(\gamma)$ with `flipMask = 56` ($\gamma = (-1,-1,-1,+1,+1,+1)$),
    the complete 9-bin 2-blade nullity histogram is
    `{0: 257, 4: 422, 8: 364, 12: 336, 16: 168, 20: 0, 24: 56, 28: 172, 32: 178}`,
    exhibiting the first interior spectral gap $H_6^{56}(16) = 168$, **$H_6^{56}(20) = 0$**,
    $H_6^{56}(24) = 56$. -/
theorem cd6_split56_interior_spectral_gap :
    nullityHistGamma 6 56 0 = 257 ∧
    nullityHistGamma 6 56 4 = 422 ∧
    nullityHistGamma 6 56 8 = 364 ∧
    nullityHistGamma 6 56 12 = 336 ∧
    nullityHistGamma 6 56 16 = 168 ∧
    nullityHistGamma 6 56 20 = 0 ∧
    nullityHistGamma 6 56 24 = 56 ∧
    nullityHistGamma 6 56 28 = 172 ∧
    nullityHistGamma 6 56 32 = 178 := by
  have hquad : cd6QuadTree56 = (257, 422, 364, 336) := rfl
  rw [cd6QuadTree56_eq] at hquad
  injection hquad with h0 hrest1
  injection hrest1 with h4 hrest2
  injection hrest2 with h8 h12
  have h16 : nullityHistGamma 6 56 16 = 168 := by
    have h := universal_split_midpoint_42 6 56 (by omega)
    rw [show 2 ^ (6 - 2) = 16 from rfl, show 42 * 2 ^ (6 - 4) = 168 from rfl] at h
    exact h
  have hm0 : nullityHistGamma 6 56 0 + nullityHistGamma 6 56 32 = 435 := by
    have h := mirror_sum_conservation 6 56 0 (by omega) (by omega)
    rw [show 2 ^ (6 - 1) - 0 = 32 from rfl] at h
    exact h.trans cd6_std_mirror_sums.1
  have hm4 : nullityHistGamma 6 56 4 + nullityHistGamma 6 56 28 = 594 := by
    have h := mirror_sum_conservation 6 56 4 (by omega) (by omega)
    rw [show 2 ^ (6 - 1) - 4 = 28 from rfl] at h
    exact h.trans cd6_std_mirror_sums.2.1
  have hm8 : nullityHistGamma 6 56 8 + nullityHistGamma 6 56 24 = 420 := by
    have h := mirror_sum_conservation 6 56 8 (by omega) (by omega)
    rw [show 2 ^ (6 - 1) - 8 = 24 from rfl] at h
    exact h.trans cd6_std_mirror_sums.2.2.1
  have hm12 : nullityHistGamma 6 56 12 + nullityHistGamma 6 56 20 = 336 := by
    have h := mirror_sum_conservation 6 56 12 (by omega) (by omega)
    rw [show 2 ^ (6 - 1) - 12 = 20 from rfl] at h
    exact h.trans cd6_std_mirror_sums.2.2.2
  refine ⟨h0, h4, h8, h12, h16, by omega, by omega, by omega, by omega⟩

end

end CDTerrace
