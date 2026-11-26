module
-- SPDX-License-Identifier: Apache-2.0
public import CDTerrace.Basic

/-!
# CDTerrace.MirrorConservation — Universal All-$n$ Sign Factorization & Nilpotent Mirror Conservation

Proves universally for every $n \in \mathbb{N}$ and every doubling signature $\gamma \in \{\pm 1\}^n$
(encoded by `flipMask : Nat`):
- **T1a (`cdSignGamma_factorization`):** $\sigma_n^\gamma(i, j) = \sigma_n^{\mathrm{std}}(i, j) \cdot (-1)^{\mathrm{popcount}(i \,\&\, j \,\&\, \mathrm{flip}(\gamma))}$.
- **T1b (`blockDeltaGamma_eq`):** $\delta_n^\gamma(i, j, k) = (-1)^{\mathrm{popcount}((i \oplus j) \,\&\, \mathrm{flip}(\gamma))} \cdot \delta_n^{\mathrm{std}}(i, j, k)$ (independent of $k$!).
- **T1c (`twoblade_nilpotent_iff`):** For $1 \le i < j < 2^n$, $(e_i + e_j)^2 = 0 \iff \mathrm{parityBits}\; n\; ((i \oplus j) \,\&\, \mathrm{flip}(\gamma)) = \mathrm{true}$.
- **T1d (`nilpotent_mirror_law`):** Non-nilpotent 2-blades keep exact Euclidean nullity $\nu_n^\gamma(i, j) = \nu_n^{\mathrm{std}}(i, j)$;
  nilpotent 2-blades invert to $\nu_n^\gamma(i, j) + \nu_n^{\mathrm{std}}(i, j) = 2^{n-1}$.
- **T1e (`mirror_sum_conservation` & `midpoint_stratum_invariance`):**
  For ALL $n \ge 1$ and ALL signatures $\gamma \in \{\pm 1\}^n$, every mirror pair sum
  $H_n^\gamma(v) + H_n^\gamma(2^{n-1} - v)$ is completely independent of $\gamma$, and the exact
  midpoint stratum $H_n^\gamma(2^{n-2})$ is completely signature-invariant.
-/

namespace CDTerrace

public section

/-- Reusable predicate-counter over $[0, m)$. -/
@[expose] def countPred (Q : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => countPred Q m + (if Q m then 1 else 0)

theorem countPred_add (Q : Nat → Bool) (a b : Nat) :
    countPred Q (a + b) = countPred Q a + countPred (fun k => Q (a + k)) b := by
  induction b with
  | zero => simp [countPred]
  | succ b ih =>
    rw [Nat.add_succ]
    show countPred Q (a + b) + (if Q (a + b) then 1 else 0) =
         countPred Q a + (countPred (fun k => Q (a + k)) b + if Q (a + b) then 1 else 0)
    rw [ih]
    omega

theorem countPred_ext (Q1 Q2 : Nat → Bool) (lim : Nat)
    (hext : ∀ k, k < lim → Q1 k = Q2 k) :
    countPred Q1 lim = countPred Q2 lim := by
  induction lim with
  | zero => rfl
  | succ lim ih =>
    simp only [countPred]
    rw [ih (fun k hk => hext k (by omega)), hext lim (by omega)]

theorem countPred_xor_bijection :
    ∀ (m : Nat) (Q : Nat → Bool) (mask : Nat),
      mask < 2 ^ m →
      countPred Q (2 ^ m) = countPred (fun k => Q (k ^^^ mask)) (2 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro Q mask hm
    have hm0 : mask = 0 := by omega
    subst hm0
    simp [countPred]
  | succ m ihm =>
    intro Q mask hm
    have h2m : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
    rw [h2m, countPred_add, countPred_add]
    by_cases hmlt : mask < 2 ^ m
    · have h1 := ihm Q mask hmlt
      have h2 := ihm (fun k => Q (2 ^ m + k)) mask hmlt
      have heq2 : countPred (fun k => Q ((2 ^ m + k) ^^^ mask)) (2 ^ m) =
                  countPred (fun k => Q (2 ^ m + (k ^^^ mask))) (2 ^ m) := by
        apply countPred_ext
        intro k hk
        rw [Nat.add_comm (2 ^ m) k, xor_add_left hk hmlt, Nat.add_comm (k ^^^ mask) (2 ^ m)]
      rw [heq2, ← h1, ← h2]
    · let lo := mask - 2 ^ m
      have hlo : lo < 2 ^ m := by omega
      have hmask_eq : mask = lo + 2 ^ m := by omega
      have h1 := ihm (fun k => Q (2 ^ m + k)) lo hlo
      have h2 := ihm Q lo hlo
      have heqA : countPred (fun k => Q (k ^^^ mask)) (2 ^ m) =
                  countPred (fun k => Q (2 ^ m + (k ^^^ lo))) (2 ^ m) := by
        apply countPred_ext
        intro k hk
        rw [hmask_eq, xor_add_right hk hlo, Nat.add_comm (k ^^^ lo) (2 ^ m)]
      have heqB : countPred (fun k => Q ((2 ^ m + k) ^^^ mask)) (2 ^ m) =
                  countPred (fun k => Q (k ^^^ lo)) (2 ^ m) := by
        apply countPred_ext
        intro k hk
        rw [hmask_eq, Nat.add_comm (2 ^ m) k, xor_add_both hk hlo]
      rw [heqA, heqB, ← h1, ← h2, Nat.add_comm]

/-! ### Bitwise Parity Homomorphism Lemmas -/

theorem parityBits_zero (n : Nat) : parityBits n 0 = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [parityBits, ih]

theorem parityBits_xor : ∀ n a b, parityBits n (a ^^^ b) = xor (parityBits n a) (parityBits n b) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro a b
    unfold parityBits
    have hmod : ((a ^^^ b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
      have ha : (a % 2 == 1) = a.testBit 0 := by
        rw [Nat.testBit_zero]; cases Nat.mod_two_eq_zero_or_one a <;> simp [*]
      have hb : (b % 2 == 1) = b.testBit 0 := by
        rw [Nat.testBit_zero]; cases Nat.mod_two_eq_zero_or_one b <;> simp [*]
      have hab : ((a ^^^ b) % 2 == 1) = (a ^^^ b).testBit 0 := by
        rw [Nat.testBit_zero]; cases Nat.mod_two_eq_zero_or_one (a ^^^ b) <;> simp [*]
      rw [ha, hb, hab, Nat.testBit_xor]
    have hdiv : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor]
    rw [hmod, hdiv, ih (a / 2) (b / 2)]
    cases (a % 2 == 1) <;> cases (b % 2 == 1) <;> cases parityBits n (a / 2) <;> cases parityBits n (b / 2) <;> rfl

theorem parityBits_split :
    ∀ n m, parityBits (n + 1) m = xor (parityBits n (m % 2 ^ n)) ((m / 2 ^ n) % 2 == 1) := by
  intro n
  induction n with
  | zero =>
    intro m
    simp [parityBits]
  | succ n ih =>
    intro m
    unfold parityBits
    have hdiv2 : (m / 2) / 2 ^ n = m / 2 ^ (n + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have hmod2 : (m % 2 ^ (n + 1)) % 2 = m % 2 := by
      have h2 : 2 ∣ 2 ^ (n + 1) := ⟨2 ^ n, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      exact Nat.mod_mod_of_dvd m h2
    have hmoddiv : (m % 2 ^ (n + 1)) / 2 = (m / 2) % 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.mod_mul_right_div_self m 2 (2 ^ n)
    rw [ih (m / 2), hdiv2, hmod2, hmoddiv]
    cases (m % 2 == 1) <;> cases parityBits n ((m / 2) % 2 ^ n) <;> cases ((m / 2 ^ (n + 1)) % 2 == 1) <;> rfl

theorem paritySign_val (n m : Nat) : paritySign n m = 1 ∨ paritySign n m = -1 := by
  unfold paritySign
  cases parityBits n m <;> simp

theorem paritySign_xor (n a b : Nat) :
    paritySign n (a ^^^ b) = paritySign n a * paritySign n b := by
  unfold paritySign
  rw [parityBits_xor]
  cases parityBits n a <;> cases parityBits n b <;> decide

theorem paritySign_split (n m : Nat) :
    paritySign (n + 1) m =
      (if (m / 2 ^ n) % 2 == 1 then -(paritySign n (m % 2 ^ n)) else paritySign n (m % 2 ^ n)) := by
  unfold paritySign
  rw [parityBits_split]
  cases parityBits n (m % 2 ^ n) <;> cases ((m / 2 ^ n) % 2 == 1) <;> decide

theorem and_mod_pow2 (n a b : Nat) : (a &&& b) % 2 ^ n = (a % 2 ^ n) &&& (b % 2 ^ n) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hk : k < n <;> simp [hk]

theorem and_div_pow2 (n a b : Nat) : (a &&& b) / 2 ^ n = (a / 2 ^ n) &&& (b / 2 ^ n) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two_pow, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]

theorem div_pow2_lt_zero {n a : Nat} (ha : a < 2 ^ n) : a / 2 ^ n = 0 :=
  Nat.div_eq_of_lt ha

theorem div_pow2_ge_one {n a : Nat} (hge : ¬(a < 2 ^ n)) (hlt : a < 2 ^ (n + 1)) :
    a / 2 ^ n = 1 := by
  have h1 : 2 ^ n ≤ a := by omega
  have h2 : a < 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm] at hlt; exact hlt
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem mod_pow2_sub {n a : Nat} (hge : ¬(a < 2 ^ n)) (hlt : a < 2 ^ (n + 1)) :
    a % 2 ^ n = a - 2 ^ n := by
  have hdiv : a / 2 ^ n = 1 := div_pow2_ge_one hge hlt
  have hdm := Nat.div_add_mod a (2 ^ n)
  rw [hdiv] at hdm
  omega

theorem one_and_mod_two (m : Nat) : (1 &&& m) % 2 = m % 2 := by
  rw [Nat.and_comm, Nat.and_one_is_mod, Nat.mod_mod]

/-! ### Theorem T1a: Universal All-$n$ Sign-Cocycle Factorization -/

/-- **Theorem T1a:** For EVERY $n \in \mathbb{N}$, EVERY signature mask `flipMask`, and all
    basis indices $i, j < 2^n$, the generalized Cayley-Dickson multiplication sign factors
    multiplicatively as
    $\sigma_n^\gamma(i, j) = \sigma_n^{\mathrm{std}}(i, j) \cdot (-1)^{\mathrm{popcount}(i \,\&\, j \,\&\, \mathrm{flip}(\gamma))}$. -/
theorem cdSignGamma_factorization :
    ∀ n flipMask i j, i < 2 ^ n → j < 2 ^ n →
      cdSignGamma n flipMask i j =
        cdSign n i j * paritySign n (i &&& j &&& flipMask) := by
  intro n
  induction n with
  | zero =>
    intro flipMask i j hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    rfl
  | succ n ih =>
    intro flipMask i j hi hj
    unfold cdSignGamma cdSign
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hih : i < 2 ^ n <;> by_cases hjh : j < 2 ^ n
    · simp only [hih, hjh, ↓reduceIte]
      rw [ih (flipMask % 2 ^ n) i j hih hjh]
      rw [paritySign_split n (i &&& j &&& flipMask)]
      have hdi : i / 2 ^ n = 0 := div_pow2_lt_zero hih
      have hd : (i &&& j &&& flipMask) / 2 ^ n = 0 := by
        rw [and_div_pow2, and_div_pow2, hdi]; simp
      have hm : (i &&& j &&& flipMask) % 2 ^ n = i &&& j &&& (flipMask % 2 ^ n) := by
        rw [and_mod_pow2, and_mod_pow2, Nat.mod_eq_of_lt hih, Nat.mod_eq_of_lt hjh]
      simp [hd, hm]
    · simp only [hih, hjh, ↓reduceIte]
      have hj_sub : j - 2 ^ n < 2 ^ n := by omega
      rw [ih (flipMask % 2 ^ n) (j - 2 ^ n) i hj_sub hih]
      rw [paritySign_split n (i &&& j &&& flipMask)]
      have hdi : i / 2 ^ n = 0 := div_pow2_lt_zero hih
      have hd : (i &&& j &&& flipMask) / 2 ^ n = 0 := by
        rw [and_div_pow2, and_div_pow2, hdi]; simp
      have hjm : j % 2 ^ n = j - 2 ^ n := mod_pow2_sub hjh hj
      have hm : (i &&& j &&& flipMask) % 2 ^ n = (j - 2 ^ n) &&& i &&& (flipMask % 2 ^ n) := by
        rw [and_mod_pow2, and_mod_pow2, Nat.mod_eq_of_lt hih, hjm, Nat.and_comm i (j - 2 ^ n)]
      simp [hd, hm]
    · simp only [hih, hjh, ↓reduceIte]
      have hi_sub : i - 2 ^ n < 2 ^ n := by omega
      have hdj : j / 2 ^ n = 0 := div_pow2_lt_zero hjh
      have hd : (i &&& j &&& flipMask) / 2 ^ n = 0 := by
        rw [and_div_pow2, and_div_pow2, hdj]; simp
      have him : i % 2 ^ n = i - 2 ^ n := mod_pow2_sub hih hi
      have hm : (i &&& j &&& flipMask) % 2 ^ n = (i - 2 ^ n) &&& j &&& (flipMask % 2 ^ n) := by
        rw [and_mod_pow2, and_mod_pow2, him, Nat.mod_eq_of_lt hjh]
      rw [paritySign_split n (i &&& j &&& flipMask)]
      simp only [hd, Nat.zero_mod, beq_iff_eq, Nat.zero_ne_one, ↓reduceIte, hm]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [↓reduceIte]
        rw [ih (flipMask % 2 ^ n) (i - 2 ^ n) 0 hi_sub (Nat.two_pow_pos n)]
      · simp only [hj0, ↓reduceIte]
        rw [ih (flipMask % 2 ^ n) (i - 2 ^ n) j hi_sub hjh, Int.neg_mul]
    · simp only [hih, hjh, ↓reduceIte]
      have hi_sub : i - 2 ^ n < 2 ^ n := by omega
      have hj_sub : j - 2 ^ n < 2 ^ n := by omega
      have hdi : i / 2 ^ n = 1 := div_pow2_ge_one hih hi
      have hdj : j / 2 ^ n = 1 := div_pow2_ge_one hjh hj
      have him : i % 2 ^ n = i - 2 ^ n := mod_pow2_sub hih hi
      have hjm : j % 2 ^ n = j - 2 ^ n := mod_pow2_sub hjh hj
      have hdmod : ((i &&& j &&& flipMask) / 2 ^ n) % 2 = (flipMask / 2 ^ n) % 2 := by
        rw [and_div_pow2, and_div_pow2, hdi, hdj]
        have : (1 &&& 1) = 1 := rfl
        rw [this, one_and_mod_two]
      have hm : (i &&& j &&& flipMask) % 2 ^ n = (j - 2 ^ n) &&& (i - 2 ^ n) &&& (flipMask % 2 ^ n) := by
        rw [and_mod_pow2, and_mod_pow2, him, hjm, Nat.and_comm (i - 2 ^ n) (j - 2 ^ n)]
      rw [paritySign_split n (i &&& j &&& flipMask), hdmod, hm]
      by_cases hj0 : j - 2 ^ n = 0
      · simp only [hj0]
        rw [ih (flipMask % 2 ^ n) 0 (i - 2 ^ n) (Nat.two_pow_pos n) hi_sub]
        have hz : (0 &&& (i - 2 ^ n) &&& (flipMask % 2 ^ n)) = 0 := by simp
        rw [hz]
        have hp0 : paritySign n 0 = 1 := by simp [paritySign, parityBits_zero]
        rw [hp0]
        cases ((flipMask / 2 ^ n) % 2 == 1) <;> simp [Int.neg_neg, Int.mul_one]
      · have hjb : (j - 2 ^ n == 0) = false := beq_false_of_ne hj0
        simp only [hjb, Bool.false_eq_true, ↓reduceIte]
        rw [ih (flipMask % 2 ^ n) (j - 2 ^ n) (i - 2 ^ n) hj_sub hi_sub]
        cases ((flipMask / 2 ^ n) % 2 == 1) <;> simp [Int.mul_neg]

/-! ### Theorem T1b: Universal $k$-Independent Block-Sign Flip Law -/

theorem bitwise_block_exponent (i j k flipMask : Nat) :
    let d := i ^^^ j
    let kp := k ^^^ d
    ((i &&& k &&& flipMask) ^^^ (i &&& kp &&& flipMask)) ^^^
    ((j &&& k &&& flipMask) ^^^ (j &&& kp &&& flipMask)) = d &&& flipMask := by
  dsimp only
  apply Nat.eq_of_testBit_eq
  intro m
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases i.testBit m <;> cases j.testBit m <;> cases k.testBit m <;> cases flipMask.testBit m <;> rfl

/-- **Theorem T1b:** For EVERY $n \in \mathbb{N}$, EVERY signature mask `flipMask`, and all
    $i, j, k < 2^n$, the $2 \times 2$ zero-divisor block determinant sign satisfies
    $\delta_n^\gamma(i, j, k) = (-1)^{\mathrm{popcount}((i \oplus j) \,\&\, \mathrm{flip}(\gamma))} \cdot \delta_n^{\mathrm{std}}(i, j, k)$,
    completely independent of the block index $k$. -/
theorem blockDeltaGamma_eq (n flipMask i j k : Nat)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hk : k < 2 ^ n) :
    blockDeltaGamma n flipMask i j k =
      paritySign n ((i ^^^ j) &&& flipMask) * blockDelta n i j k := by
  unfold blockDeltaGamma blockDelta
  dsimp only
  have hkp : k ^^^ (i ^^^ j) < 2 ^ n := Nat.xor_lt_two_pow hk (Nat.xor_lt_two_pow hi hj)
  rw [cdSignGamma_factorization n flipMask i k hi hk,
      cdSignGamma_factorization n flipMask i (k ^^^ (i ^^^ j)) hi hkp,
      cdSignGamma_factorization n flipMask j k hj hk,
      cdSignGamma_factorization n flipMask j (k ^^^ (i ^^^ j)) hj hkp]
  have hexp := bitwise_block_exponent i j k flipMask
  dsimp only at hexp
  have hps : paritySign n (i &&& k &&& flipMask) * paritySign n (i &&& (k ^^^ (i ^^^ j)) &&& flipMask) *
      (paritySign n (j &&& k &&& flipMask) * paritySign n (j &&& (k ^^^ (i ^^^ j)) &&& flipMask)) =
      paritySign n ((i ^^^ j) &&& flipMask) := by
    rw [← paritySign_xor, ← paritySign_xor, ← paritySign_xor, hexp]
  have hrearr :
      (cdSign n i k * paritySign n (i &&& k &&& flipMask)) *
      (cdSign n i (k ^^^ (i ^^^ j)) * paritySign n (i &&& (k ^^^ (i ^^^ j)) &&& flipMask)) *
      (cdSign n j k * paritySign n (j &&& k &&& flipMask)) *
      (cdSign n j (k ^^^ (i ^^^ j)) * paritySign n (j &&& (k ^^^ (i ^^^ j)) &&& flipMask)) =
      (paritySign n (i &&& k &&& flipMask) * paritySign n (i &&& (k ^^^ (i ^^^ j)) &&& flipMask) *
        (paritySign n (j &&& k &&& flipMask) * paritySign n (j &&& (k ^^^ (i ^^^ j)) &&& flipMask))) *
      (cdSign n i k * cdSign n i (k ^^^ (i ^^^ j)) * cdSign n j k * cdSign n j (k ^^^ (i ^^^ j))) := by
    ac_rfl
  rw [hrearr, hps]

/-! ### Theorem T1c: Exact 2-Blade Nilpotency Criterion -/

/-- **Theorem T1c:** For $1 \le i < j < 2^n$ and any signature mask `flipMask`, the 2-blade
    square coefficient $e_i^2 + e_j^2 = \sigma_n^\gamma(i, i) + \sigma_n^\gamma(j, j)$ vanishes
    (making $e_i + e_j$ a nilpotent with $(e_i + e_j)^2 = 0$) IF AND ONLY IF
    `parityBits n ((i ^^^ j) &&& flipMask) = true`. -/
theorem twoblade_nilpotent_iff (n flipMask i j : Nat)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    (cdSignGamma n flipMask i i + cdSignGamma n flipMask j j = 0) ↔
      parityBits n ((i ^^^ j) &&& flipMask) = true := by
  rw [cdSignGamma_factorization n flipMask i i hi hi,
      cdSignGamma_factorization n flipMask j j hj hj,
      cdSign_diag n i hi0 hi, cdSign_diag n j hj0 hj]
  have hii : i &&& i &&& flipMask = i &&& flipMask := by
    apply Nat.eq_of_testBit_eq; intro m; simp [Nat.testBit_and]
  have hjj : j &&& j &&& flipMask = j &&& flipMask := by
    apply Nat.eq_of_testBit_eq; intro m; simp [Nat.testBit_and]
  have hij : (i ^^^ j) &&& flipMask = (i &&& flipMask) ^^^ (j &&& flipMask) := by
    apply Nat.eq_of_testBit_eq; intro m
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases i.testBit m <;> cases j.testBit m <;> cases flipMask.testBit m <;> rfl
  rw [hii, hjj, hij, parityBits_xor]
  unfold paritySign
  cases parityBits n (i &&& flipMask) <;> cases parityBits n (j &&& flipMask) <;> decide

/-! ### Theorem T1d: Universal All-$n$ Nilpotent Mirror-Inversion Law -/

theorem blockDelta_val_pm1 (n i j k : Nat) :
    blockDelta n i j k = 1 ∨ blockDelta n i j k = -1 := by
  unfold blockDelta
  rcases cdSign_val_pm1 n i k with h1 | h1 <;>
  rcases cdSign_val_pm1 n i (k ^^^ (i ^^^ j)) with h2 | h2 <;>
  rcases cdSign_val_pm1 n j k with h3 | h3 <;>
  rcases cdSign_val_pm1 n j (k ^^^ (i ^^^ j)) with h4 | h4 <;>
  simp [h1, h2, h3, h4]

theorem blockDelta_pair_symm (n i j k : Nat) :
    blockDelta n i j (k ^^^ (i ^^^ j)) = blockDelta n i j k := by
  unfold blockDelta
  dsimp only
  rw [xor_sub_self_cancel]
  ac_rfl

theorem countSingularIdxGamma_eq_std (n flipMask i j : Nat)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hpar : parityBits n ((i ^^^ j) &&& flipMask) = false) :
    ∀ m, m ≤ 2 ^ n →
      countSingularIdxGamma n flipMask i j m = countSingularIdx n i j m := by
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold countSingularIdxGamma countSingularIdx
    rw [ih (by omega), blockDeltaGamma_eq n flipMask i j m hi hj (by omega)]
    have hps : paritySign n ((i ^^^ j) &&& flipMask) = 1 := by
      unfold paritySign; rw [hpar]; rfl
    rw [hps, Int.one_mul]

theorem countSingularIdxGamma_add_std (n flipMask i j : Nat)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hpar : parityBits n ((i ^^^ j) &&& flipMask) = true) :
    ∀ m, m ≤ 2 ^ n →
      countSingularIdxGamma n flipMask i j m + countSingularIdx n i j m = m := by
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold countSingularIdxGamma countSingularIdx
    rw [blockDeltaGamma_eq n flipMask i j m hi hj (by omega)]
    have hps : paritySign n ((i ^^^ j) &&& flipMask) = -1 := by
      unfold paritySign; rw [hpar]; rfl
    rw [hps]
    have hih := ih (by omega)
    rcases blockDelta_val_pm1 n i j m with hd | hd <;> simp [hd] <;> omega

theorem countSingularIdx_eq_countPred (n i j m : Nat) :
    countSingularIdx n i j m = countPred (fun k => blockDelta n i j k == 1) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold countSingularIdx countPred
    rw [ih]

/-- Parity of `countSingularIdx n i j (2 ^ n)`: since $k \mapsto k \oplus (i \oplus j)$ is a
    fixed-point-free involution on $[0, 2^n)$ preserving `blockDelta` when $i \neq j$, the
    singular index count is ALWAYS even! -/
theorem countSingularIdx_even_aux (n i j : Nat) (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j) :
    ∃ c, countSingularIdx n i j (2 ^ n) = 2 * c := by
  rw [countSingularIdx_eq_countPred]
  let d := i ^^^ j
  have hd0 : d ≠ 0 := fun h => hne (eq_of_xor_eq_zero h)
  let P : Nat → Bool := fun k => blockDelta n i j k == 1
  let f : Nat → Nat := fun k => k ^^^ d
  have hP_inv : ∀ k, P (f k) = P k := fun k => by
    show (blockDelta n i j (k ^^^ d) == 1) = (blockDelta n i j k == 1)
    rw [blockDelta_pair_symm]
  have hf_inv : ∀ k, f (f k) = k := fun k => xor_sub_self_cancel k d
  have hf_ne : ∀ k, f k ≠ k := by
    intro k h
    have hk1 : k ^^^ d = k := h
    have h2 : (k ^^^ d) ^^^ k = 0 := by rw [hk1, Nat.xor_self]
    rw [Nat.xor_comm k d, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h2
    exact hd0 h2
  have hsplit : ∀ m, countPred P m =
      countPred (fun k => decide (k < f k) && P k) m +
      countPred (fun k => decide (f k < k) && P k) m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [countPred]
      rw [ih]
      have hne_m := hf_ne m
      by_cases hPm : P m = true <;> by_cases hlt : m < f m
      · have hgt : ¬(f m < m) := by omega
        simp [hPm, hlt, hgt]; omega
      · have hgt : f m < m := by omega
        simp [hPm, hlt, hgt]; omega
      · have hgt : ¬(f m < m) := by omega
        have hPf : P m = false := by cases h : P m <;> simp_all
        simp [hPf, hlt, hgt]
      · have hgt : f m < m := by omega
        have hPf : P m = false := by cases h : P m <;> simp_all
        simp [hPf, hlt, hgt]
  have hd_lt : d < 2 ^ n := Nat.xor_lt_two_pow hi hj
  have heq_counts :
      countPred (fun k => decide (k < f k) && P k) (2 ^ n) =
      countPred (fun k => decide (f k < k) && P k) (2 ^ n) := by
    rw [countPred_xor_bijection n (fun k => decide (k < f k) && P k) d hd_lt]
    apply countPred_ext
    intro k _
    change (decide (f k < f (f k)) && P (f k)) = (decide (f k < k) && P k)
    rw [hf_inv k, hP_inv k]
  refine ⟨countPred (fun k => decide (k < f k) && P k) (2 ^ n), ?_⟩
  rw [hsplit (2 ^ n), ← heq_counts]
  omega

/-- **Theorem T1d (Universal Nilpotent Mirror-Inversion Law):**
    For EVERY $n \ge 1$, EVERY signature mask `flipMask`, and EVERY 2-blade $e_i + e_j$ ($i < j < 2^n$):
    - If $(e_i + e_j)^2 \neq 0$ (`parityBits n ((i ^^^ j) &&& flipMask) = false`), then
      $\nu_n^\gamma(i, j) = \nu_n^{\mathrm{std}}(i, j)$.
    - If $(e_i + e_j)^2 = 0$ (`parityBits n ((i ^^^ j) &&& flipMask) = true`), then
      $\nu_n^\gamma(i, j) + \nu_n^{\mathrm{std}}(i, j) = 2^{n-1}$. -/
theorem nilpotent_mirror_law (n flipMask i j : Nat) (hn : 1 ≤ n)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hne : i ≠ j) :
    (parityBits n ((i ^^^ j) &&& flipMask) = false →
      twobladeNullityGamma n flipMask i j = twobladeNullity n i j) ∧
    (parityBits n ((i ^^^ j) &&& flipMask) = true →
      twobladeNullityGamma n flipMask i j + twobladeNullity n i j = 2 ^ (n - 1)) := by
  refine ⟨?_, ?_⟩
  · intro hpar
    unfold twobladeNullityGamma twobladeNullity
    rw [countSingularIdxGamma_eq_std n flipMask i j hi hj hpar (2 ^ n) (Nat.le_refl _)]
  · intro hpar
    unfold twobladeNullityGamma twobladeNullity
    have hsum := countSingularIdxGamma_add_std n flipMask i j hi hj hpar (2 ^ n) (Nat.le_refl _)
    rcases countSingularIdx_even_aux n i j hi hj hne with ⟨c, hc⟩
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ m => simp [Nat.pow_succ, Nat.mul_comm]
    have hcg : countSingularIdxGamma n flipMask i j (2 ^ n) = 2 * (2 ^ (n - 1) - c) := by omega
    rw [hc, hcg]
    omega

/-! ### Theorem T1e: Universal All-$n$ Mirror-Pair Conservation & Midpoint Stratum Invariance -/

theorem nullityHistRow_mirror_sum (n flipMask v i : Nat) (hn : 1 ≤ n)
    (hv : v ≤ 2 ^ (n - 1)) (hi : i < 2 ^ n) :
    ∀ lim, lim ≤ 2 ^ n →
      nullityHistRow n flipMask v i lim +
        nullityHistRow n flipMask (2 ^ (n - 1) - v) i lim =
      nullityHistRow n 0 v i lim +
        nullityHistRow n 0 (2 ^ (n - 1) - v) i lim := by
  intro lim hlim
  induction lim with
  | zero => rfl
  | succ j ih =>
    unfold nullityHistRow
    have hih := ih (by omega)
    by_cases hij : i < j
    · have hne : i ≠ j := by omega
      have hstd0 : twobladeNullityGamma n 0 i j = twobladeNullity n i j := by
        unfold twobladeNullityGamma twobladeNullity
        have hp : parityBits n ((i ^^^ j) &&& 0) = false := by simp [parityBits_zero]
        exact congrArg (· / 2) (countSingularIdxGamma_eq_std n 0 i j hi (by omega) hp (2 ^ n) (Nat.le_refl _))
      have hbound : twobladeNullity n i j ≤ 2 ^ (n - 1) := by
        unfold twobladeNullity
        have hle : ∀ m, countSingularIdx n i j m ≤ m := by
          intro m; induction m with
          | zero => exact Nat.le_refl 0
          | succ m ihm => unfold countSingularIdx; split <;> omega
        have h2 := hle (2 ^ n)
        have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
          cases n with | zero => omega | succ m => simp [Nat.pow_succ, Nat.mul_comm]
        omega
      rcases nilpotent_mirror_law n flipMask i j hn hi (by omega) hne with ⟨hF, hT⟩
      cases hpar : parityBits n ((i ^^^ j) &&& flipMask)
      · have heq := hF hpar
        simp only [hij, decide_true, Bool.true_and, heq, hstd0]
        omega
      · have hsum := hT hpar
        have heq1 : (twobladeNullityGamma n flipMask i j == v) =
                    (twobladeNullity n i j == 2 ^ (n - 1) - v) := by
          by_cases h1 : twobladeNullityGamma n flipMask i j = v
          · have h2 : twobladeNullity n i j = 2 ^ (n - 1) - v := by omega
            simp [h1, h2]
          · have h2 : twobladeNullity n i j ≠ 2 ^ (n - 1) - v := by omega
            simp [beq_false_of_ne h1, beq_false_of_ne h2]
        have heq2 : (twobladeNullityGamma n flipMask i j == 2 ^ (n - 1) - v) =
                    (twobladeNullity n i j == v) := by
          by_cases h1 : twobladeNullityGamma n flipMask i j = 2 ^ (n - 1) - v
          · have h2 : twobladeNullity n i j = v := by omega
            simp [h1, h2]
          · have h2 : twobladeNullity n i j ≠ v := by omega
            simp [beq_false_of_ne h1, beq_false_of_ne h2]
        simp only [hij, decide_true, Bool.true_and, hstd0, heq1, heq2]
        omega
    · simp only [hij, decide_false, Bool.false_and]
      omega

theorem nullityHistRange_mirror_sum (n flipMask v : Nat) (hn : 1 ≤ n)
    (hv : v ≤ 2 ^ (n - 1)) :
    ∀ limI limJ, limI ≤ 2 ^ n → limJ ≤ 2 ^ n →
      nullityHistRange n flipMask v limI limJ +
        nullityHistRange n flipMask (2 ^ (n - 1) - v) limI limJ =
      nullityHistRange n 0 v limI limJ +
        nullityHistRange n 0 (2 ^ (n - 1) - v) limI limJ := by
  intro limI limJ hI hJ
  induction limI with
  | zero => rfl
  | succ i ih =>
    unfold nullityHistRange
    have hih := ih (by omega)
    by_cases hi0 : i = 0
    · subst hi0
      simp only [beq_self_eq_true, ↓reduceIte]
      omega
    · have hib : (i == 0) = false := beq_false_of_ne hi0
      simp only [hib, Bool.false_eq_true, ↓reduceIte]
      have hrow := nullityHistRow_mirror_sum n flipMask v i hn hv (by omega) limJ hJ
      omega

/-- **Theorem T1e (Universal All-$n$ Mirror-Pair Spectral Conservation):**
    For EVERY $n \ge 1$, EVERY signature $\gamma \in \{\pm 1\}^n$ (`flipMask`), and EVERY
    $0 \le v \le 2^{n-1}$, the mirror-pair 2-blade nullity histogram sum
    $H_n^\gamma(v) + H_n^\gamma(2^{n-1} - v)$ is completely independent of $\gamma$. -/
theorem mirror_sum_conservation (n flipMask v : Nat) (hn : 1 ≤ n) (hv : v ≤ 2 ^ (n - 1)) :
    nullityHistGamma n flipMask v + nullityHistGamma n flipMask (2 ^ (n - 1) - v) =
      nullityHist n v + nullityHist n (2 ^ (n - 1) - v) :=
  nullityHistRange_mirror_sum n flipMask v hn hv (2 ^ n) (2 ^ n) (Nat.le_refl _) (Nat.le_refl _)

/-- **Corollary T1e' (Universal All-$n$ Midpoint Stratum Invariance):**
    For EVERY $n \ge 2$ and EVERY signature $\gamma \in \{\pm 1\}^n$, the exact midpoint
    2-blade nullity stratum $H_n^\gamma(2^{n-2})$ is completely signature-invariant:
    $H_n^\gamma(2^{n-2}) = H_n^{\mathrm{std}}(2^{n-2})$. -/
theorem midpoint_stratum_invariance (n flipMask : Nat) (hn : 2 ≤ n) :
    nullityHistGamma n flipMask (2 ^ (n - 2)) = nullityHist n (2 ^ (n - 2)) := by
  have hpow : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have h1 : n - 1 = (n - 2) + 1 := by omega
    rw [h1, Nat.pow_succ, Nat.mul_comm]
  have hv : 2 ^ (n - 2) ≤ 2 ^ (n - 1) := by omega
  have hsub : 2 ^ (n - 1) - 2 ^ (n - 2) = 2 ^ (n - 2) := by omega
  have hcons := mirror_sum_conservation n flipMask (2 ^ (n - 2)) (by omega) hv
  rw [hsub] at hcons
  omega

end

end CDTerrace
