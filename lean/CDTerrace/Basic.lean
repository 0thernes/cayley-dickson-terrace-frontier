module
-- SPDX-License-Identifier: Apache-2.0
/-!
# CDTerrace.Basic — Generalized Cayley-Dickson Sign Cocycle & Core Definitions

Zero-Mathlib, strictly constructive Lean 4.35.0 foundations for the $2^n$-dimensional
generalized Cayley-Dickson tower $\mathrm{CD}_n(\gamma)$ ($\gamma \in \{\pm 1\}^n$),
its 2-blade left-multiplication block determinants, nullity histograms, right-multiplier
compatibility graphs, Hurwitz-Radon function $\rho(2^n)$, and exact dyadic terrace formulas.
-/

namespace CDTerrace

public section

/-- Parity of the popcount of `m` (`true` iff odd). Uses structural recursion on fuel `n`. -/
@[expose] def parityBits : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, m => xor (m % 2 == 1) (parityBits n (m / 2))

/-- Sign $(-1)^{\mathrm{popcount}(m \bmod 2^n)} \in \{+1, -1\}$. -/
@[expose] def paritySign (n m : Nat) : Int :=
  if parityBits n m then -1 else 1

/-- Standard Euclidean Cayley-Dickson basis multiplication sign $\sigma_n^{\mathrm{std}}(i, j) \in \{\pm 1\}$
    for $e_i \cdot e_j = \sigma_n(i, j)\, e_{i \oplus j}$ in $\mathrm{CD}_n$ ($\dim = 2^n$).
    Doubling rule: $(a, b)(c, d) = (ac - \bar{d}b,\; da + b\bar{c})$ with $\overline{e_0}=e_0$,
    $\overline{e_k}=-e_k$ ($k \ge 1$). -/
@[expose] def cdSign : Nat → Nat → Nat → Int
  | 0, _, _ => 1
  | n + 1, i, j =>
    let h := 2 ^ n
    if i < h then
      if j < h then cdSign n i j
      else cdSign n (j - h) i
    else
      if j < h then
        if j == 0 then cdSign n (i - h) 0 else -(cdSign n (i - h) j)
      else
        if j - h == 0 then -(cdSign n 0 (i - h)) else cdSign n (j - h) (i - h)

/-- Generalized Cayley-Dickson basis multiplication sign $\sigma_n^\gamma(i, j) \in \{\pm 1\}$
    parameterized by a bitmask `flipMask : Nat` where bit `m` is `1` iff doubling parameter
    $\gamma_{m+1} = +1$ (split) and `0` iff $\gamma_{m+1} = -1$ (Euclidean).
    Doubling rule at step $n+1$: $(0, b)(0, d) = (\gamma_{n+1}\bar{d}b, 0)$. -/
@[expose] def cdSignGamma : Nat → Nat → Nat → Nat → Int
  | 0, _, _, _ => 1
  | n + 1, flipMask, i, j =>
    let h := 2 ^ n
    let gBit := (flipMask / h) % 2 == 1
    let lowFlip := flipMask % h
    if i < h then
      if j < h then cdSignGamma n lowFlip i j
      else cdSignGamma n lowFlip (j - h) i
    else
      if j < h then
        if j == 0 then cdSignGamma n lowFlip (i - h) 0
        else -(cdSignGamma n lowFlip (i - h) j)
      else
        let base :=
          if j - h == 0 then -(cdSignGamma n lowFlip 0 (i - h))
          else cdSignGamma n lowFlip (j - h) (i - h)
        if gBit then -base else base

/-- 2-blade $2 \times 2$ block determinant sign product
    $\delta_n^\gamma(i, j, k) = \sigma_n^\gamma(i, k)\,\sigma_n^\gamma(i, k')\,\sigma_n^\gamma(j, k)\,\sigma_n^\gamma(j, k')$
    where $k' = k \oplus i \oplus j$. The block $\{k, k'\}$ is singular iff $\delta = +1$. -/
@[expose] def blockDeltaGamma (n flipMask i j k : Nat) : Int :=
  let kp := k ^^^ (i ^^^ j)
  cdSignGamma n flipMask i k * cdSignGamma n flipMask i kp *
  cdSignGamma n flipMask j k * cdSignGamma n flipMask j kp

/-- Standard Euclidean 2-blade block determinant sign product $\delta_n^{\mathrm{std}}(i, j, k)$. -/
@[expose] def blockDelta (n i j k : Nat) : Int :=
  let kp := k ^^^ (i ^^^ j)
  cdSign n i k * cdSign n i kp * cdSign n j k * cdSign n j kp

/-- Count of indices $k \in \{0, \dots, m - 1\}$ with $\delta_n^\gamma(i, j, k) = +1$.
    Since $k$ and $k \oplus i \oplus j$ have identical $\delta$, for $m = 2^n$ this equals $2\,\nu_n^\gamma(i, j)$. -/
@[expose] def countSingularIdxGamma (n flipMask i j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    countSingularIdxGamma n flipMask i j m +
      (if blockDeltaGamma n flipMask i j m == 1 then 1 else 0)

/-- Standard Euclidean singular index count over $\{0, \dots, m - 1\}$. -/
@[expose] def countSingularIdx (n i j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    countSingularIdx n i j m +
      (if blockDelta n i j m == 1 then 1 else 0)

/-- Exact 2-blade left-annihilator nullity $\nu_n^\gamma(i, j) = \frac{1}{2}\#\{k < 2^n : \delta_n^\gamma(i, j, k) = +1\}$. -/
@[expose] def twobladeNullityGamma (n flipMask i j : Nat) : Nat :=
  countSingularIdxGamma n flipMask i j (2 ^ n) / 2

/-- Standard Euclidean 2-blade left-annihilator nullity $\nu_n^{\mathrm{std}}(i, j)$. -/
@[expose] def twobladeNullity (n i j : Nat) : Nat :=
  countSingularIdx n i j (2 ^ n) / 2

/-- Row helper for 2-blade nullity histogram over $j < \mathrm{lim}$. -/
@[expose] def nullityHistRow (n flipMask v i : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
    nullityHistRow n flipMask v i j +
      (if i < j && twobladeNullityGamma n flipMask i j == v then 1 else 0)

/-- Exact 2-blade nullity histogram $H_n^\gamma(v)$ over $1 \le i < \mathrm{lim}_i$, $j < \mathrm{lim}_j$. -/
@[expose] def nullityHistRange (n flipMask v : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, lim =>
    nullityHistRange n flipMask v i lim +
      (if i == 0 then 0 else nullityHistRow n flipMask v i lim)

/-- Histogram count $H_n^\gamma(v)$ over all $1 \le i < j < 2^n$. -/
@[expose] def nullityHistGamma (n flipMask v : Nat) : Nat :=
  nullityHistRange n flipMask v (2 ^ n) (2 ^ n)

/-- Standard Euclidean histogram count $H_n^{\mathrm{std}}(v)$. -/
@[expose] def nullityHist (n v : Nat) : Nat :=
  nullityHistGamma n 0 v

/-- Row helper for total 2-blade nullity mass. -/
@[expose] def totalNullityMassRow (n i : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
    totalNullityMassRow n i j + (if i < j then twobladeNullity n i j else 0)

/-- Total 2-blade nullity mass $M_n$ over $1 \le i < \mathrm{lim}_i$, $j < \mathrm{lim}_j$. -/
@[expose] def totalNullityMassRange (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, lim =>
    totalNullityMassRange n i lim +
      (if i == 0 then 0 else totalNullityMassRow n i lim)

/-- Total 2-blade nullity mass $M_n$ over all $1 \le i < j < 2^n$. -/
@[expose] def totalNullityMass (n : Nat) : Nat :=
  totalNullityMassRange n (2 ^ n) (2 ^ n)

/-- Right-multiplier norm-multiplicativity compatibility predicate for `[2^n, s, 2^n]`:
    $j$ and $x$ are compatible iff $\forall i < 2^n,\; \sigma_n(i, j)\sigma_n(i \oplus j \oplus x, x) +
    \sigma_n(i, x)\sigma_n(i \oplus j \oplus x, j) = 0$. -/
@[expose] def rightCompatCheck (n j x : Nat) : Nat → Bool
  | 0 => true
  | i + 1 =>
    let k := i ^^^ (j ^^^ x)
    (cdSign n i j * cdSign n k x + cdSign n i x * cdSign n k j == 0) &&
    rightCompatCheck n j x i

/-- Right-multiplier compatibility edge in $G_n^{\mathrm{comp}}$ for distinct $j, x < 2^n$. -/
@[expose] def rightCompat (n j x : Nat) : Bool :=
  (j != x) && rightCompatCheck n j x (2 ^ n)

/-- Classical Hurwitz-Radon function $\rho(2^n) = 8\lfloor n/4 \rfloor + 2^{n \bmod 4}$. -/
@[expose] def hurwitzRadon (n : Nat) : Nat :=
  8 * (n / 4) + (2 ^ (n % 4))

/-- Exact closed-form count of zero-divisor-free 2-blades $H_n^{\mathrm{std}}(0)$ for $n \ge 3$. -/
@[expose] def nonZDCountFormula (n : Nat) : Nat :=
  (6 * n - 9) * (2 ^ (n - 2)) + 3

/-- Exact closed-form count of 2-blade zero divisors $\#\mathrm{ZD}_2(\mathrm{CD}_n)$ for $n \ge 3$. -/
@[expose] def zdCountFormula (n : Nat) : Nat :=
  ((2 ^ n - 1) * (2 ^ n - 2)) / 2 - nonZDCountFormula n

/-- Exact Biss-Dugger-Isaksen maximum annihilator dimension $2^n - 4n + 4$ for $n \ge 4$. -/
@[expose] def bdiMaxAnnihilator (n : Nat) : Nat :=
  2 ^ n - 4 * n + 4

/-- Exact 2-blade maximum nullity ceiling $2^{n-1} - 4$ for $n \ge 4$. -/
@[expose] def twobladeMaxNullity (n : Nat) : Nat :=
  2 ^ (n - 1) - 4

/-! ### Foundational All-$n$ Algebraic Properties of `cdSign` -/

theorem cdSign_val_pm1 : ∀ n i j, cdSign n i j = 1 ∨ cdSign n i j = -1 := by
  intro n
  induction n with
  | zero => intro _ _; exact Or.inl rfl
  | succ n ih =>
    intro i j
    unfold cdSign
    dsimp only
    split
    · split
      · exact ih _ _
      · exact ih _ _
    · split
      · split
        · exact ih _ _
        · rcases ih (i - 2 ^ n) j with h | h <;> simp [h]
      · split
        · rcases ih 0 (i - 2 ^ n) with h | h <;> simp [h]
        · exact ih _ _

theorem cdSign_sq_one (n i j : Nat) : cdSign n i j * cdSign n i j = 1 := by
  rcases cdSign_val_pm1 n i j with h | h <;> simp [h]

theorem cdSignGamma_val_pm1 : ∀ n f i j, cdSignGamma n f i j = 1 ∨ cdSignGamma n f i j = -1 := by
  intro n
  induction n with
  | zero => intro _ _ _; exact Or.inl rfl
  | succ n ih =>
    intro f i j
    unfold cdSignGamma
    dsimp only
    split
    · split
      · exact ih _ _ _
      · exact ih _ _ _
    · split
      · split
        · exact ih _ _ _
        · rcases ih (f % 2 ^ n) (i - 2 ^ n) j with h | h <;> simp [h]
      · split
        · split
          · rcases ih (f % 2 ^ n) 0 (i - 2 ^ n) with h | h <;> simp [h]
          · rcases ih (f % 2 ^ n) (j - 2 ^ n) (i - 2 ^ n) with h | h <;> simp [h]
        · split
          · rcases ih (f % 2 ^ n) 0 (i - 2 ^ n) with h | h <;> simp [h]
          · exact ih _ _ _

theorem cdSignGamma_sq_one (n f i j : Nat) :
    cdSignGamma n f i j * cdSignGamma n f i j = 1 := by
  rcases cdSignGamma_val_pm1 n f i j with h | h <;> simp [h]

theorem cdSignGamma_zero_eq_cdSign : ∀ n i j, cdSignGamma n 0 i j = cdSign n i j := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro i j
    unfold cdSignGamma cdSign
    have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
    have hdiv : 0 / 2 ^ n = 0 := Nat.zero_div _
    have hmod : 0 % 2 ^ n = 0 := Nat.zero_mod _
    simp only [hdiv, hmod, Nat.zero_mod, beq_iff_eq, Nat.zero_ne_one, ↓reduceIte]
    split
    · split
      · exact ih _ _
      · exact ih _ _
    · split
      · split
        · exact ih _ _
        · rw [ih]
      · split
        · rw [ih]
        · exact ih _ _

theorem cdSign_zero_both :
    ∀ n, (∀ j, j < 2 ^ n → cdSign n 0 j = 1) ∧ (∀ i, i < 2 ^ n → cdSign n i 0 = 1) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    rcases ih with ⟨ihL, ihR⟩
    have h0 : (0 : Nat) < 2 ^ n := Nat.two_pow_pos n
    refine ⟨?_, ?_⟩
    · intro j hj
      unfold cdSign
      simp only [h0, ↓reduceIte]
      split
      · exact ihL j ‹_›
      · exact ihR (j - 2 ^ n) (by omega)
    · intro i hi
      unfold cdSign
      simp only [h0, ↓reduceIte]
      split
      · exact ihR i ‹_›
      · simp only [beq_self_eq_true, ↓reduceIte]
        exact ihR (i - 2 ^ n) (by omega)

theorem cdSign_zero_left (n j : Nat) (hj : j < 2 ^ n) : cdSign n 0 j = 1 :=
  (cdSign_zero_both n).1 j hj

theorem cdSign_zero_right (n i : Nat) (hi : i < 2 ^ n) : cdSign n i 0 = 1 :=
  (cdSign_zero_both n).2 i hi

theorem cdSign_diag : ∀ n i, 0 < i → i < 2 ^ n → cdSign n i i = -1 := by
  intro n
  induction n with
  | zero => intro i h0 h1; omega
  | succ n ih =>
    intro i h0 h1
    unfold cdSign
    by_cases hih : i < 2 ^ n
    · simp only [hih, ↓reduceIte]
      exact ih i h0 hih
    · simp only [hih, ↓reduceIte]
      by_cases hsub : i - 2 ^ n = 0
      · simp only [hsub, beq_self_eq_true, ↓reduceIte]
        rw [cdSign_zero_left n 0 (Nat.two_pow_pos n)]
      · have hne : (i - 2 ^ n == 0) = false := beq_false_of_ne hsub
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        have hlt : i - 2 ^ n < 2 ^ n := by rw [Nat.pow_succ] at h1; omega
        exact ih (i - 2 ^ n) (by omega) hlt

theorem cdSign_anticomm :
    ∀ n i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
      cdSign n i j = -(cdSign n j i) := by
  intro n
  induction n with
  | zero => intro i j hi _ hi2 _ _; omega
  | succ n ih =>
    intro i j hi hj hi2 hj2 hne
    unfold cdSign
    by_cases hih : i < 2 ^ n <;> by_cases hjh : j < 2 ^ n
    · simp only [hih, hjh, ↓reduceIte]
      exact ih i j hi hj hih hjh hne
    · have hi0 : (i == 0) = false := beq_false_of_ne (by omega)
      simp only [hih, hjh, hi0, ↓reduceIte, Bool.false_eq_true]
      omega
    · have hj0 : (j == 0) = false := beq_false_of_ne (by omega)
      simp only [hih, hjh, hj0, ↓reduceIte, Bool.false_eq_true]
    · simp only [hih, hjh, ↓reduceIte]
      have hilt : i - 2 ^ n < 2 ^ n := by rw [Nat.pow_succ] at hi2; omega
      have hjlt : j - 2 ^ n < 2 ^ n := by rw [Nat.pow_succ] at hj2; omega
      by_cases his : i - 2 ^ n = 0
      · have hjs : j - 2 ^ n ≠ 0 := by omega
        have hjsb : (j - 2 ^ n == 0) = false := beq_false_of_ne hjs
        simp only [his, hjsb, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        rw [cdSign_zero_right n (j - 2 ^ n) hjlt, cdSign_zero_left n (j - 2 ^ n) hjlt]
        rfl
      · by_cases hjs : j - 2 ^ n = 0
        · have hisb : (i - 2 ^ n == 0) = false := beq_false_of_ne his
          simp only [hjs, hisb, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
          rw [cdSign_zero_left n (i - 2 ^ n) hilt, cdSign_zero_right n (i - 2 ^ n) hilt]
        · have hisb : (i - 2 ^ n == 0) = false := beq_false_of_ne his
          have hjsb : (j - 2 ^ n == 0) = false := beq_false_of_ne hjs
          simp only [hisb, hjsb, Bool.false_eq_true, ↓reduceIte]
          exact ih (j - 2 ^ n) (i - 2 ^ n) (by omega) (by omega) hjlt hilt (by omega)

/-! ### Bitwise Helper Lemmas for XOR on $[0, 2^n)$ -/

theorem testBit_add_pow2_lt (n a k : Nat) (ha : a < 2 ^ n) :
    (a + 2 ^ n).testBit k = (if k = n then true else a.testBit k) := by
  by_cases hkn : k = n
  · subst hkn
    simp only [↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdiv : (a + 2 ^ k) / 2 ^ k = a / 2 ^ k + 1 := Nat.add_div_right a hpos
    have h0 : a / 2 ^ k = 0 := Nat.div_eq_of_lt ha
    rw [hdiv, h0]; decide
  · simp only [hkn, ↓reduceIte]
    by_cases hlt : k < n
    · simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      have hpow : 2 ^ n = 2 ^ (n - k) * 2 ^ k := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have hdiv : (a + 2 ^ n) / 2 ^ k = a / 2 ^ k + 2 ^ (n - k) := by
        rw [hpow, Nat.add_mul_div_right _ _ hpos]
      have heven : 2 ^ (n - k) % 2 = 0 := by
        have hge : 1 ≤ n - k := by omega
        have hsplit : 2 ^ (n - k) = 2 ^ (n - k - 1) * 2 := by
          rw [← Nat.pow_succ]
          exact congrArg (2 ^ ·) (by omega)
        rw [hsplit]; omega
      rw [hdiv]
      have hmod : (a / 2 ^ k + 2 ^ (n - k)) % 2 = (a / 2 ^ k) % 2 := by omega
      have hb1 : (1 &&& (a / 2 ^ k + 2 ^ (n - k))) = (a / 2 ^ k + 2 ^ (n - k)) % 2 := by
        rw [Nat.and_comm, Nat.and_one_is_mod]
      have hb2 : (1 &&& (a / 2 ^ k)) = (a / 2 ^ k) % 2 := by
        rw [Nat.and_comm, Nat.and_one_is_mod]
      rw [hb1, hb2, hmod]
    · have hgt : n + 1 ≤ k := by omega
      have hle : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hgt
      have h1 : a + 2 ^ n < 2 ^ k := by rw [Nat.pow_succ] at hle; omega
      have h2 : a < 2 ^ k := by omega
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem xor_lt_two_pow' {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ b < 2 ^ n :=
  Nat.xor_lt_two_pow ha hb

theorem xor_add_left {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (a + 2 ^ n) ^^^ b = (a ^^^ b) + 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, testBit_add_pow2_lt n a k ha,
      testBit_add_pow2_lt n (a ^^^ b) k (Nat.xor_lt_two_pow ha hb), Nat.testBit_xor]
  by_cases hkn : k = n
  · subst hkn
    have hbf : b.testBit k = false := Nat.testBit_lt_two_pow hb
    simp [hbf]
  · simp [hkn]

theorem xor_add_right {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ (b + 2 ^ n) = (a ^^^ b) + 2 ^ n := by
  rw [Nat.xor_comm, xor_add_left hb ha, Nat.xor_comm]

theorem xor_add_both {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (a + 2 ^ n) ^^^ (b + 2 ^ n) = a ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, testBit_add_pow2_lt n a k ha,
      testBit_add_pow2_lt n b k hb, Nat.testBit_xor]
  by_cases hkn : k = n
  · subst hkn
    have haf : a.testBit k = false := Nat.testBit_lt_two_pow ha
    have hbf : b.testBit k = false := Nat.testBit_lt_two_pow hb
    simp [haf, hbf]
  · simp [hkn]

theorem xor_sub_self_cancel (a b : Nat) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have h1 := congrArg (· ^^^ b) h
  rw [xor_sub_self_cancel, Nat.zero_xor] at h1
  exact h1

theorem cdSign_left_alt_basis :
    ∀ n i k, 0 < i → i < 2 ^ n → k < 2 ^ n →
      cdSign n i k * cdSign n i (i ^^^ k) = -1 := by
  intro n
  induction n with
  | zero => intro i _ hi hi2 _; omega
  | succ n ih =>
    intro i k hi hi2 hk2
    have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
    have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hih : i < 2 ^ n <;> by_cases hkh : k < 2 ^ n
    · have hxk : i ^^^ k < 2 ^ n := Nat.xor_lt_two_pow hih hkh
      unfold cdSign
      simp only [hih, hkh, hxk, ↓reduceIte]
      exact ih i k hi hih hkh
    · let b := k - 2 ^ n
      have hbk : k = b + 2 ^ n := by omega
      have hblt : b < 2 ^ n := by omega
      have hxk : i ^^^ k = (i ^^^ b) + 2 ^ n := by rw [hbk, xor_add_right hih hblt]
      have hxlt : i ^^^ b < 2 ^ n := Nat.xor_lt_two_pow hih hblt
      have hxk_ge : ¬(i ^^^ k < 2 ^ n) := by omega
      unfold cdSign
      simp only [hih, hkh, hxk_ge, ↓reduceIte]
      have hs1 : k - 2 ^ n = b := rfl
      have hs2 : (i ^^^ k) - 2 ^ n = i ^^^ b := by omega
      rw [hs1, hs2]
      by_cases hb0 : b = 0
      · rw [hb0, Nat.xor_zero, cdSign_zero_left n i hih, cdSign_diag n i hi hih]; rfl
      · by_cases hbi : b = i
        · rw [hbi, Nat.xor_self, cdSign_diag n i hi hih, cdSign_zero_left n i hih]; rfl
        · have hxne0 : i ^^^ b ≠ 0 := fun hz => hbi (Eq.symm (eq_of_xor_eq_zero hz))
          have hxpos : 0 < i ^^^ b := by omega
          have hxne : i ^^^ b ≠ i := by
            intro heq
            have : (i ^^^ b) ^^^ i = 0 := by rw [heq, Nat.xor_self]
            rw [Nat.xor_comm i b, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
            exact hb0 this
          rw [cdSign_anticomm n b i (by omega) hi hblt hih hbi,
              cdSign_anticomm n (i ^^^ b) i hxpos hi hxlt hih hxne,
              Int.neg_mul_neg]
          exact ih i b hi hih hblt
    · let a := i - 2 ^ n
      have hai : i = a + 2 ^ n := by omega
      have halt : a < 2 ^ n := by omega
      have hxk : i ^^^ k = (a ^^^ k) + 2 ^ n := by rw [hai, xor_add_left halt hkh]
      have hxlt : a ^^^ k < 2 ^ n := Nat.xor_lt_two_pow halt hkh
      have hxk_ge : ¬(i ^^^ k < 2 ^ n) := by omega
      unfold cdSign
      simp only [hih, hkh, hxk_ge, ↓reduceIte]
      have hs1 : i - 2 ^ n = a := rfl
      have hs2 : (i ^^^ k) - 2 ^ n = a ^^^ k := by omega
      rw [hs1, hs2]
      by_cases hk0 : k = 0
      · subst hk0
        rw [Nat.xor_zero]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [cdSign_zero_right n a halt]
        by_cases ha0 : a = 0
        · rw [ha0]; simp only [beq_self_eq_true, ↓reduceIte]; rw [cdSign_zero_left n 0 hpow]; rfl
        · have hab : (a == 0) = false := beq_false_of_ne ha0
          simp only [hab, Bool.false_eq_true, ↓reduceIte]
          rw [cdSign_diag n a (by omega) halt]; rfl
      · have hkb : (k == 0) = false := beq_false_of_ne hk0
        simp only [hkb, Bool.false_eq_true, ↓reduceIte]
        by_cases hax0 : a ^^^ k = 0
        · have hak : a = k := eq_of_xor_eq_zero hax0
          simp only [hax0, beq_self_eq_true, ↓reduceIte]
          rw [hak, cdSign_diag n k (by omega) hkh, cdSign_zero_left n k hkh]; rfl
        · have haxb : (a ^^^ k == 0) = false := beq_false_of_ne hax0
          simp only [haxb, Bool.false_eq_true, ↓reduceIte]
          by_cases ha0 : a = 0
          · rw [ha0, Nat.zero_xor, cdSign_zero_left n k hkh, cdSign_zero_right n k hkh]; rfl
          · have hne : a ^^^ k ≠ a := by
              intro heq
              have : (a ^^^ k) ^^^ a = 0 := by rw [heq, Nat.xor_self]
              rw [Nat.xor_comm a k, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
              exact hk0 this
            rw [cdSign_anticomm n (a ^^^ k) a (by omega) (by omega) hxlt halt hne,
                Int.neg_mul_neg]
            exact ih a k (by omega) halt hkh
    · let a := i - 2 ^ n
      let b := k - 2 ^ n
      have hai : i = a + 2 ^ n := by omega
      have hbk : k = b + 2 ^ n := by omega
      have halt : a < 2 ^ n := by omega
      have hblt : b < 2 ^ n := by omega
      have hxk : i ^^^ k = a ^^^ b := by rw [hai, hbk, xor_add_both halt hblt]
      have hxlt : i ^^^ k < 2 ^ n := by rw [hxk]; exact Nat.xor_lt_two_pow halt hblt
      unfold cdSign
      simp only [hih, hkh, hxlt, ↓reduceIte]
      have hs1 : i - 2 ^ n = a := rfl
      have hs2 : k - 2 ^ n = b := rfl
      rw [hs1, hs2, hxk]
      by_cases hb0 : b = 0
      · rw [hb0, Nat.xor_zero]
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [cdSign_zero_left n a halt]
        by_cases ha0 : a = 0
        · rw [ha0]; simp only [beq_self_eq_true, ↓reduceIte]; rw [cdSign_zero_left n 0 hpow]; rfl
        · have hab : (a == 0) = false := beq_false_of_ne ha0
          simp only [hab, Bool.false_eq_true, ↓reduceIte]
          rw [cdSign_diag n a (by omega) halt]; rfl
      · have hbb : (b == 0) = false := beq_false_of_ne hb0
        simp only [hbb, Bool.false_eq_true, ↓reduceIte]
        by_cases hab : a ^^^ b = 0
        · have heq : a = b := eq_of_xor_eq_zero hab
          simp only [hab, beq_self_eq_true, ↓reduceIte]
          rw [heq, cdSign_diag n b (by omega) hblt, cdSign_zero_right n b hblt]; rfl
        · have habb : (a ^^^ b == 0) = false := beq_false_of_ne hab
          simp only [habb, Bool.false_eq_true, ↓reduceIte]
          by_cases ha0 : a = 0
          · rw [ha0, Nat.zero_xor, cdSign_zero_right n b hblt, cdSign_zero_left n b hblt]; rfl
          · have hba : b ≠ a := fun h => hab (by rw [h, Nat.xor_self])
            rw [cdSign_anticomm n b a (by omega) (by omega) hblt halt hba,
                Int.neg_mul_neg]
            exact ih a b (by omega) halt hblt

end

end CDTerrace
