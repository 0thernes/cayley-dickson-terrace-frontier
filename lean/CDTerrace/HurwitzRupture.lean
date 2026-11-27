module
-- SPDX-License-Identifier: Apache-2.0
public import CDTerrace.Basic
public import CDTerrace.MirrorConservation
public import CDTerrace.TerraceLaw

/-!
# CDTerrace.HurwitzRupture — Euclidean Coordinate Right-Multiplier Rupture & Asymmetric Doubling Tower

Proves universally for every $n \ge 3$ in zero-Mathlib, strictly constructive Lean 4.35.0
for standard Euclidean Cayley-Dickson coordinate subspaces $\mathrm{CD}_n$:
- **T3a (`rightCompat_iff_nullity_zero`, `rightCompat_doubling_*`, `universal_right_multipliers_all_n`):**
  On imaginary basis indices $1 \le j < x < 2^n$, the $[2^n, s, 2^n]$ Euclidean right-multiplier
  compatibility graph $G_n^{\mathrm{comp}}$ is identical to the 2-blade non-zero-divisor graph
  $\{\{j, x\} : \nu_n^{\mathrm{std}}(j, x) = 0\}$, obeys an exact doubling law, and for every
  $n \ge 4$ its universal right-multipliers are exactly $\{e_0, e_{2^{n-1}}\}$.
- **T3b (`compat_clique_le_all_n`, `cdMaxClique_valid`):** Exact clique number
  $\omega(G_n^{\mathrm{comp}}) = n + 5$ for ALL $n \ge 3$ (both universal upper bound on every
  Euclidean coordinate right-multiplier clique and constructive $(n+5)$-clique witness
  $\{0, \dots, 7\} \cup \{2^3, \dots, 2^{n-1}\}$).
- **T3c (`hurwitz_radon_saturation_345`, `hurwitz_radon_rupture_all_ge6`):**
  Exact arithmetic comparison of the Euclidean coordinate ceiling $n + 5$ against the classical
  Hurwitz-Radon function $\rho(2^n) = 8\lfloor n/4 \rfloor + 2^{n \bmod 4}$ (whose optimality over
  general real bilinear forms is cited from Hurwitz/Radon/Adams, not formalized here):
  saturation $n + 5 = \rho(2^n)$ for $n \in \{3, 4, 5\}$ ($8, 9, 10$), followed by permanent strict
  rupture $n + 5 < \rho(2^n)$ for ALL $n \ge 6$ with permanent deficit $\rho(2^n) - (n + 5) \ge n - 5$.
- **T3d (`compatClique_implies_full_normMult`, `asymmetric_doubling_tower_all_n`):**
  Constructive full-left $[2^n, n+5, 2^n]$ pairs and the universal Euclidean coordinate
  asymmetric composition tower $[2^{n-1}, 2(n+4), 2^n]$ directly embedded in $\mathrm{CD}_n$
  for ALL $n \ge 4$ ($[8, 16, 16]$, $[16, 18, 32]$, $[32, 20, 64]$, $[64, 22, 128]$, ...).
-/

namespace CDTerrace

public section

/-! ### Helper Predicates for Cliques and Bilinear Norm-Multiplicativity -/

/-- Exact bilinear sum-of-squares composition condition for coordinate subspaces
    $S_L, S_R \subseteq \{0, \dots, 2^n - 1\}$ in $\mathrm{CD}_n$:
    $\|x y\|^2 = \|x\|^2 \|y\|^2$ identically on $\mathrm{span}(S_L) \times \mathrm{span}(S_R)$. -/
@[expose] def isNormMultPair (n : Nat) (SL SR : List Nat) : Prop :=
  (∀ i ∈ SL, i < 2 ^ n) ∧
  (∀ j ∈ SR, j < 2 ^ n) ∧
  (∀ i ∈ SL, ∀ k ∈ SL, ∀ j ∈ SR, ∀ l ∈ SR,
    i ≠ k → j ≠ l → (i ^^^ k) = (j ^^^ l) →
    cdSign n i j * cdSign n k l + cdSign n i l * cdSign n k j = 0)

/-- Clique in the $[2^n, s, 2^n]$ right-multiplier compatibility graph $G_n^{\mathrm{comp}}$. -/
@[expose] def isCompatClique (n : Nat) (S : List Nat) : Prop :=
  S.Nodup ∧ (∀ x ∈ S, x < 2 ^ n) ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → rightCompat n x y = true)

/-- Canonical $(n + 5)$-element right-multiplier clique witness
    $\{0, 1, \dots, 7\} \cup \{2^3, 2^4, \dots, 2^{n-1}\}$ for $n \ge 3$. -/
@[expose] def cdMaxClique : Nat → List Nat
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 2, 3]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7]
  | n + 4 => (2 ^ (n + 3)) :: cdMaxClique (n + 3)

/-- Doubled right-multiplier subspace of size $2(n + 4)$ inside $\mathrm{CD}_n$ ($n \ge 4$)
    for the $[2^{n-1}, 2(n+4), 2^n]$ asymmetric composition tower. -/
@[expose] def doubledRightWitness (n : Nat) : List Nat :=
  cdMaxClique (n - 1) ++ (cdMaxClique (n - 1)).map (· + 2 ^ (n - 1))

/-! ### Theorem T3a: Exact Equivalence Between $G_n^{\mathrm{comp}}$ and $\nu_n^{\mathrm{std}} = 0$ -/

theorem rightCompatCheck_iff (n j x : Nat) :
    ∀ lim, rightCompatCheck n j x lim = true ↔
      ∀ i, i < lim → cdSign n i j * cdSign n (i ^^^ (j ^^^ x)) x +
                     cdSign n i x * cdSign n (i ^^^ (j ^^^ x)) j = 0 := by
  intro lim
  induction lim with
  | zero =>
    constructor
    · intro _ i hi; omega
    · intro _; rfl
  | succ m ih =>
    unfold rightCompatCheck
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hm, hrest⟩ i hi
      by_cases him : i = m
      · subst him; exact hm
      · exact ih.mp hrest i (by omega)
    · intro hall
      exact ⟨hall m (by omega), ih.mpr (fun i hi => hall i (by omega))⟩

theorem rightCompat_iff (n j x : Nat) :
    rightCompat n j x = true ↔
      j ≠ x ∧ ∀ i, i < 2 ^ n →
        cdSign n i j * cdSign n (i ^^^ (j ^^^ x)) x +
        cdSign n i x * cdSign n (i ^^^ (j ^^^ x)) j = 0 := by
  unfold rightCompat
  simp only [Bool.and_eq_true, bne_iff_ne, rightCompatCheck_iff]

theorem rightCompat_symm (n j x : Nat) :
    rightCompat n j x = rightCompat n x j := by
  cases h : rightCompat n j x
  · cases h2 : rightCompat n x j
    · rfl
    · exfalso
      rw [rightCompat_iff] at h2
      have h1 : rightCompat n j x = true := by
        rw [rightCompat_iff]
        refine ⟨Ne.symm h2.1, fun i hi => ?_⟩
        rw [Nat.xor_comm j x, Int.add_comm]
        exact h2.2 i hi
      rw [h] at h1; cases h1
  · symm
    rw [rightCompat_iff] at h ⊢
    refine ⟨Ne.symm h.1, fun i hi => ?_⟩
    rw [Nat.xor_comm x j, Int.add_comm]
    exact h.2 i hi

theorem rightCompat_zero_universal (n x : Nat) (hx0 : 0 < x) (hx : x < 2 ^ n) :
    rightCompat n 0 x = true := by
  rw [rightCompat_iff]
  refine ⟨by omega, fun i hi => ?_⟩
  rw [Nat.zero_xor, cdSign_zero_right n i hi, cdSign_zero_right n (i ^^^ x) (Nat.xor_lt_two_pow hi hx),
      Int.one_mul, Int.mul_one]
  by_cases hi0 : i = 0
  · subst hi0; rw [Nat.zero_xor, cdSign_diag n x hx0 hx, cdSign_zero_left n x hx]; rfl
  · by_cases hix : i = x
    · subst hix; rw [Nat.xor_self, cdSign_zero_left n i hx, cdSign_diag n i hx0 hx]; rfl
    · have hne0 : i ^^^ x ≠ 0 := fun hz => hix (eq_of_xor_eq_zero hz)
      have hnex : i ^^^ x ≠ x := by
        intro heq
        have : (i ^^^ x) ^^^ x = 0 := by rw [heq, Nat.xor_self]
        rw [xor_sub_self_cancel] at this; exact hi0 this
      have hlt : i ^^^ x < 2 ^ n := Nat.xor_lt_two_pow hi hx
      have h1 := cdSign_right_alt_basis n x i hx0 hx hi
      rw [Nat.xor_comm x i] at h1
      -- Since cdSign n i x and cdSign n (i^x) x are in {±1} and their product is -1, their sum is 0!
      rcases cdSign_val_pm1 n i x with ha | ha <;> rcases cdSign_val_pm1 n (i ^^^ x) x with hb | hb <;>
        simp_all

/-- Pointwise equivalence between right-multiplier orthogonality at $i$ and
    block nonsingularity $\delta_n(j, x, i) = -1$ for $1 \le j \neq x < 2^n$. -/
theorem rightCompat_pointwise_iff_delta (n j x i : Nat)
    (hj0 : 0 < j) (hx0 : 0 < x) (hj : j < 2 ^ n) (hx : x < 2 ^ n) (hne : j ≠ x) (hi : i < 2 ^ n) :
    (cdSign n i j * cdSign n (i ^^^ (j ^^^ x)) x +
     cdSign n i x * cdSign n (i ^^^ (j ^^^ x)) j = 0) ↔
    blockDelta n j x i = -1 := by
  have hdlt : j ^^^ x < 2 ^ n := Nat.xor_lt_two_pow hj hx
  have hkp : i ^^^ (j ^^^ x) < 2 ^ n := Nat.xor_lt_two_pow hi hdlt
  by_cases hspec : i = 0 ∨ i = j ∨ i = x ∨ i = j ^^^ x
  · have hdel := blockDelta_special_nonsing n j x i hj0 hx0 hj hx hne hspec
    rw [hdel]
    constructor
    · intro _; rfl
    · intro _
      rcases hspec with hi0 | hij | hix | hid
      · rw [hi0, Nat.zero_xor, cdSign_zero_left n j hj, cdSign_zero_left n x hx, Int.one_mul, Int.one_mul]
        have hd0 : j ^^^ x ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
        have hxj : (j ^^^ x) ^^^ x = j := xor_sub_self_cancel j x
        have h1 := cdSign_left_alt_basis n (j ^^^ x) x (by omega) hdlt hx
        rw [hxj] at h1
        rcases cdSign_val_pm1 n (j ^^^ x) x with ha | ha <;>
        rcases cdSign_val_pm1 n (j ^^^ x) j with hb | hb <;> simp_all
      · rw [hij]
        have h1 : j ^^^ (j ^^^ x) = x := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [h1, cdSign_diag n j hj0 hj, cdSign_diag n x hx0 hx,
            cdSign_anticomm n j x hj0 hx0 hj hx hne]
        rcases cdSign_val_pm1 n x j with ha | ha <;> simp [ha]
      · rw [hix]
        have h1 : x ^^^ (j ^^^ x) = j := by rw [Nat.xor_comm j x, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [h1, cdSign_diag n j hj0 hj, cdSign_diag n x hx0 hx,
            cdSign_anticomm n j x hj0 hx0 hj hx hne]
        rcases cdSign_val_pm1 n x j with ha | ha <;> simp [ha]
      · rw [hid, Nat.xor_self, cdSign_zero_left n j hj, cdSign_zero_left n x hx, Int.mul_one, Int.mul_one]
        have hd0 : j ^^^ x ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
        have hxj : (j ^^^ x) ^^^ x = j := xor_sub_self_cancel j x
        have h1 := cdSign_left_alt_basis n (j ^^^ x) x (by omega) hdlt hx
        rw [hxj] at h1
        rcases cdSign_val_pm1 n (j ^^^ x) x with ha | ha <;>
        rcases cdSign_val_pm1 n (j ^^^ x) j with hb | hb <;> simp_all
  · have hi0 : i ≠ 0 := fun h => hspec (Or.inl h)
    have hij : i ≠ j := fun h => hspec (Or.inr (Or.inl h))
    have hix : i ≠ x := fun h => hspec (Or.inr (Or.inr (Or.inl h)))
    have hid : i ≠ j ^^^ x := fun h => hspec (Or.inr (Or.inr (Or.inr h)))
    have hkp0 : i ^^^ (j ^^^ x) ≠ 0 := fun hz => hid (eq_of_xor_eq_zero hz)
    have hkpj : i ^^^ (j ^^^ x) ≠ j := by
      intro heq
      have : (i ^^^ (j ^^^ x)) ^^^ (j ^^^ x) = j ^^^ (j ^^^ x) := congrArg (· ^^^ (j ^^^ x)) heq
      rw [xor_sub_self_cancel, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; exact hix this
    have hkpx : i ^^^ (j ^^^ x) ≠ x := by
      intro heq
      have : (i ^^^ (j ^^^ x)) ^^^ (j ^^^ x) = x ^^^ (j ^^^ x) := congrArg (· ^^^ (j ^^^ x)) heq
      rw [xor_sub_self_cancel, Nat.xor_comm j x, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; exact hij this
    rw [cdSign_anticomm n i j (by omega) hj0 hi hj hij,
        cdSign_anticomm n (i ^^^ (j ^^^ x)) x (by omega) hx0 hkp hx hkpx,
        cdSign_anticomm n i x (by omega) hx0 hi hx hix,
        cdSign_anticomm n (i ^^^ (j ^^^ x)) j (by omega) hj0 hkp hj hkpj]
    unfold blockDelta; dsimp only
    rcases cdSign_val_pm1 n j i with h1 | h1 <;>
    rcases cdSign_val_pm1 n j (i ^^^ (j ^^^ x)) with h2 | h2 <;>
    rcases cdSign_val_pm1 n x i with h3 | h3 <;>
    rcases cdSign_val_pm1 n x (i ^^^ (j ^^^ x)) with h4 | h4 <;>
    simp [h1, h2, h3, h4]

/-- **Theorem T3a (Exact Graph-Nullity Unification):**
    For EVERY $n \ge 1$ and all distinct imaginary basis indices $1 \le j \neq x < 2^n$,
    $j$ and $x$ are adjacent in the $[2^n, s, 2^n]$ right-multiplier compatibility graph
    $G_n^{\mathrm{comp}}$ IF AND ONLY IF $\nu_n^{\mathrm{std}}(j, x) = 0$. -/
theorem rightCompat_iff_nullity_zero (n j x : Nat)
    (hj0 : 0 < j) (hx0 : 0 < x) (hj : j < 2 ^ n) (hx : x < 2 ^ n) (hne : j ≠ x) :
    rightCompat n j x = true ↔ twobladeNullity n j x = 0 := by
  rw [rightCompat_iff]
  have hall_iff : (∀ i, i < 2 ^ n → blockDelta n j x i = -1) ↔ twobladeNullity n j x = 0 := by
    unfold twobladeNullity
    rcases countSingularIdx_even_aux n j x hj hx hne with ⟨c, hc⟩
    have hc0 : countSingularIdx n j x (2 ^ n) / 2 = 0 ↔ countSingularIdx n j x (2 ^ n) = 0 := by
      rw [hc]; omega
    rw [hc0]
    suffices ∀ m, m ≤ 2 ^ n →
        ((∀ i, i < m → blockDelta n j x i = -1) ↔ countSingularIdx n j x m = 0) by
      exact this (2 ^ n) (Nat.le_refl _)
    intro m hm
    induction m with
    | zero =>
      constructor
      · intro _; rfl
      · intro _ i hi; omega
    | succ m ih =>
      unfold countSingularIdx
      have hih := ih (by omega)
      constructor
      · intro hall
        rw [hih.mp (fun i hi => hall i (by omega)), hall m (by omega)]; rfl
      · intro hsum i hi
        have h1 : countSingularIdx n j x m = 0 := by omega
        have h2 : (if blockDelta n j x m == 1 then 1 else 0) = 0 := by omega
        by_cases him : i = m
        · subst him
          rcases blockDelta_val_pm1 n j x i with hd | hd
          · simp [hd] at h2
          · exact hd
        · exact hih.mpr h1 i (by omega)
  constructor
  · rintro ⟨_, h⟩
    exact hall_iff.mp (fun i hi => (rightCompat_pointwise_iff_delta n j x i hj0 hx0 hj hx hne hi).mp (h i hi))
  · intro hnu
    refine ⟨hne, fun i hi => ?_⟩
    exact (rightCompat_pointwise_iff_delta n j x i hj0 hx0 hj hx hne hi).mpr (hall_iff.mpr hnu i hi)

/-! ### Theorem T3b: Universal Doubling Law for $G_n^{\mathrm{comp}}$ & Exact Universal Multipliers -/

theorem rightCompat_doubling_lower (n a b : Nat) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    rightCompat (n + 1) a b = rightCompat n a b := by
  by_cases hab : a = b
  · subst hab; simp [rightCompat]
  · by_cases ha0 : a = 0
    · subst ha0
      have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [rightCompat_zero_universal (n + 1) b (by omega) (by omega),
          rightCompat_zero_universal n b (by omega) hb]
    · by_cases hb0 : b = 0
      · subst hb0
        have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [rightCompat_symm (n + 1), rightCompat_symm n,
            rightCompat_zero_universal (n + 1) a (by omega) (by omega),
            rightCompat_zero_universal n a (by omega) ha]
      · have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        have h1 := rightCompat_iff_nullity_zero (n + 1) a b (by omega) (by omega) (by omega) (by omega) hab
        have h2 := rightCompat_iff_nullity_zero n a b (by omega) (by omega) ha hb hab
        have hdbl := nullity_doubling_lower n a b (by omega) (by omega) ha hb hab
        cases hL : rightCompat (n + 1) a b <;> cases hR : rightCompat n a b
        · rfl
        · exfalso
          have hnu := h2.mp hR
          have hnu1 : twobladeNullity (n + 1) a b = 0 := by rw [hdbl, hnu]
          have := h1.mpr hnu1; rw [hL] at this; cases this
        · exfalso
          have hnu1 := h1.mp hL
          have hnu : twobladeNullity n a b = 0 := by omega
          have := h2.mpr hnu; rw [hR] at this; cases this
        · rfl

theorem rightCompat_doubling_upper (n a b : Nat) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    rightCompat (n + 1) (a + 2 ^ n) (b + 2 ^ n) = rightCompat n a b := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hab : a = b
  · subst hab; simp [rightCompat]
  · by_cases ha0 : a = 0
    · subst ha0
      have hax := (nullity_doubling_axis n b (by omega) hb).1
      have h1 := (rightCompat_iff_nullity_zero (n + 1) (2 ^ n) (b + 2 ^ n)
        (Nat.two_pow_pos n) (by omega) (by omega) (by omega) (by omega)).mpr hax
      simp only [Nat.zero_add]
      rw [h1, rightCompat_zero_universal n b (by omega) hb]
    · by_cases hb0 : b = 0
      · subst hb0
        have hax := (nullity_doubling_axis n a (by omega) ha).1
        have h1 := (rightCompat_iff_nullity_zero (n + 1) (2 ^ n) (a + 2 ^ n)
          (Nat.two_pow_pos n) (by omega) (by omega) (by omega) (by omega)).mpr hax
        simp only [Nat.zero_add]
        rw [rightCompat_symm (n + 1), rightCompat_symm n, h1,
            rightCompat_zero_universal n a (by omega) ha]
      · have h1 := rightCompat_iff_nullity_zero (n + 1) (a + 2 ^ n) (b + 2 ^ n)
          (by omega) (by omega) (by omega) (by omega) (by omega)
        have h2 := rightCompat_iff_nullity_zero n a b (by omega) (by omega) ha hb hab
        have hdbl := nullity_doubling_upper n a b (by omega) (by omega) ha hb hab
        cases hL : rightCompat (n + 1) (a + 2 ^ n) (b + 2 ^ n) <;> cases hR : rightCompat n a b
        · rfl
        · exfalso
          have hnu1 : twobladeNullity (n + 1) (a + 2 ^ n) (b + 2 ^ n) = 0 := by rw [hdbl, h2.mp hR]
          have := h1.mpr hnu1; rw [hL] at this; cases this
        · exfalso
          have hnu1 := h1.mp hL
          have hnu : twobladeNullity n a b = 0 := by omega
          have := h2.mpr hnu; rw [hR] at this; cases this
        · rfl

theorem rightCompat_doubling_cross (n a b : Nat) (hn : 3 ≤ n) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    rightCompat (n + 1) a (b + 2 ^ n) = decide (a = 0 ∨ b = 0 ∨ a = b) := by
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases ha0 : a = 0
  · subst ha0
    simp only [true_or, decide_true]
    exact rightCompat_zero_universal (n + 1) (b + 2 ^ n) (by omega) (by omega)
  · by_cases hb0 : b = 0
    · subst hb0
      simp only [Nat.zero_add, true_or, or_true, decide_true]
      exact (rightCompat_iff_nullity_zero (n + 1) a (2 ^ n)
        (by omega) (Nat.two_pow_pos n) (by omega) (by omega) (by omega)).mpr
        (nullity_doubling_axis n a (by omega) ha).2.1
    · by_cases hab : a = b
      · subst hab
        simp only [or_true, decide_true]
        exact (rightCompat_iff_nullity_zero (n + 1) a (a + 2 ^ n)
          (by omega) (by omega) (by omega) (by omega) (by omega)).mpr
          (nullity_doubling_axis n a (by omega) ha).2.2
      · simp only [ha0, hb0, hab, or_self, decide_false]
        have hcr := nullity_doubling_cross n a b (by omega) (by omega) (by omega) ha hb hab
        have hpos : 0 < twobladeNullity (n + 1) a (b + 2 ^ n) := by
          rw [hcr]
          by_cases hn3 : n = 3
          · subst hn3
            rw [octonion_nullity_all_zero a b (by omega) (by omega) ha hb hab]; omega
          · have hbd := (nullity_mod4_and_bound n hn a b (by omega) (by omega) ha hb hab).2 (by omega)
            have hp2 : 2 ^ n = 2 * 2 ^ (n - 1) := two_pow_mul_split n 1 (by omega)
            have hge8 : 8 ≤ 2 ^ (n - 1) := by
              calc 8 = 2 ^ 3 := rfl
                _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
            omega
        cases hrc : rightCompat (n + 1) a (b + 2 ^ n)
        · rfl
        · exfalso
          have h0 := (rightCompat_iff_nullity_zero (n + 1) a (b + 2 ^ n)
            (by omega) (by omega) (by omega) (by omega) (by omega)).mp hrc
          omega

/-- **Theorem T3b (Exact Universal Right-Multipliers of $\mathrm{CD}_n$ for ALL $n \ge 4$):**
    A basis index $j < 2^n$ is right-compatible with EVERY other basis element of $\mathrm{CD}_n$
    IF AND ONLY IF $j = 0$ or $j = 2^{n-1}$. -/
theorem universal_right_multipliers_all_n (n j : Nat) (hn : 4 ≤ n) (hj : j < 2 ^ n) :
    (∀ x, x < 2 ^ n → x ≠ j → rightCompat n j x = true) ↔ (j = 0 ∨ j = 2 ^ (n - 1)) := by
  let m := n - 1
  have hnm : n = m + 1 := by omega
  have hm3 : 3 ≤ m := by omega
  have hpow8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm3
  rw [hnm] at hj ⊢
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub]
  have h2m : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
  constructor
  · intro hall
    by_cases hjm : j < 2 ^ m
    · by_cases hj0 : j = 0
      · exact Or.inl hj0
      · exfalso
        -- Pick b ∈ {1, 2} distinct from j, and test x = b + 2^m!
        let b := if j = 1 then 2 else 1
        have hb0 : 0 < b := by dsimp [b]; split <;> omega
        have hblt : b < 2 ^ m := by dsimp [b]; split <;> omega
        have hjb : j ≠ b := by dsimp [b]; split <;> omega
        have hok := hall (b + 2 ^ m) (by omega) (by omega)
        rw [rightCompat_doubling_cross m j b hm3 hjm hblt] at hok
        simp [hj0, hjb] at hok; omega
    · let a := j - 2 ^ m
      have haj : j = a + 2 ^ m := by omega
      have halt : a < 2 ^ m := by omega
      by_cases ha0 : a = 0
      · exact Or.inr (by omega)
      · exfalso
        let b := if a = 1 then 2 else 1
        have hb0 : 0 < b := by dsimp [b]; split <;> omega
        have hblt : b < 2 ^ m := by dsimp [b]; split <;> omega
        have hba : b ≠ a := by dsimp [b]; split <;> omega
        have hok := hall b (by omega) (by omega)
        rw [rightCompat_symm, haj, rightCompat_doubling_cross m b a hm3 hblt halt] at hok
        simp [ha0, hba] at hok; omega
  · intro hor x hx hne
    rcases hor with rfl | rfl
    · exact rightCompat_zero_universal (m + 1) x (by omega) hx
    · by_cases hxm : x < 2 ^ m
      · rw [rightCompat_symm]
        have h0eq : (2 ^ m : Nat) = 0 + 2 ^ m := by omega
        rw [h0eq, rightCompat_doubling_cross m x 0 hm3 hxm (Nat.two_pow_pos m)]
        simp
      · let b := x - 2 ^ m
        have hbx : x = b + 2 ^ m := by omega
        have hblt : b < 2 ^ m := by omega
        have h0eq : (2 ^ m : Nat) = 0 + 2 ^ m := by omega
        rw [h0eq, hbx, rightCompat_doubling_upper m 0 b (Nat.two_pow_pos m) hblt]
        exact rightCompat_zero_universal m b (by omega) hblt

/-! ### Theorem T3c: Exact Clique Number $\omega(G_n^{\mathrm{comp}}) = n + 5$ for ALL $n \ge 3$ -/

theorem list_length_filter_partition {α : Type} (p : α → Bool) (L : List α) :
    (L.filter p).length + (L.filter (fun x => !(p x))).length = L.length := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.filter, List.length]
    cases p a <;> simp <;> omega

theorem list_nodup_filter {α : Type} (p : α → Bool) {L : List α} (h : L.Nodup) :
    (L.filter p).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    rw [List.nodup_cons] at h
    simp only [List.filter]
    cases p a
    · exact ih h.2
    · rw [List.nodup_cons]
      refine ⟨fun hmem => h.1 (List.mem_filter.mp hmem).1, ih h.2⟩

theorem list_nodup_map_sub (c : Nat) {L : List Nat} (h : L.Nodup)
    (hge : ∀ x ∈ L, c ≤ x) :
    (L.map (· - c)).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2 (fun x hx => hge x (List.mem_cons_of_mem a hx))⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, hba⟩
    have ha : c ≤ a := hge a (List.mem_cons_self ..)
    have hbc : c ≤ b := hge b (List.mem_cons_of_mem a hb)
    have heq : b = a := by omega
    subst heq
    exact h.1 hb

theorem list_nodup_subset_two_le {L : List Nat} (h : L.Nodup) (c : Nat)
    (hsub : ∀ x ∈ L, x = 0 ∨ x = c) : L.length ≤ 2 := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at h
    rcases hsub a (List.mem_cons_self ..) with rfl | rfl
    · have htl : ∀ x ∈ tl, x = c := by
        intro x hx
        rcases hsub x (List.mem_cons_of_mem _ hx) with rfl | hxc
        · exact absurd hx h.1
        · exact hxc
      cases tl with
      | nil => simp
      | cons b tl2 =>
        rw [List.nodup_cons] at h
        have hb : b = c := htl b (List.mem_cons_self ..)
        subst hb
        cases tl2 with
        | nil => simp
        | cons d _ =>
          have hd : d = b := htl d (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          subst hd
          exact absurd (List.mem_cons_self ..) h.2.1
    · have htl : ∀ x ∈ tl, x = 0 := by
        intro x hx
        rcases hsub x (List.mem_cons_of_mem _ hx) with hx0 | hxc
        · exact hx0
        · rw [hxc] at hx; exact absurd hx h.1
      cases tl with
      | nil => simp
      | cons b tl2 =>
        rw [List.nodup_cons] at h
        have hb : b = 0 := htl b (List.mem_cons_self ..)
        subst hb
        cases tl2 with
        | nil => simp
        | cons d _ =>
          have hd : d = 0 := htl d (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          subst hd
          exact absurd (List.mem_cons_self ..) h.2.1

theorem list_nodup_all_zero_le_one {L : List Nat} (h : L.Nodup)
    (hsub : ∀ x ∈ L, x = 0) : L.length ≤ 1 := by
  cases L with
  | nil => simp
  | cons a tl =>
    rw [List.nodup_cons] at h
    have ha : a = 0 := hsub a (List.mem_cons_self ..)
    subst ha
    cases tl with
    | nil => simp
    | cons b _ =>
      have hb : b = 0 := hsub b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      subst hb
      exact absurd (List.mem_cons_self ..) h.1

theorem list_nodup_lt_bound : ∀ (m : Nat) (L : List Nat), L.Nodup → (∀ x ∈ L, x < m) → L.length ≤ m := by
  intro m
  induction m with
  | zero =>
    intro L _ hlt
    cases L with
    | nil => simp
    | cons a _ => have := hlt a (List.mem_cons_self ..); omega
  | succ m ih =>
    intro L hnd hlt
    let L1 := L.filter (fun x => decide (x < m))
    let L2 := L.filter (fun x => !(decide (x < m)))
    have hpart := list_length_filter_partition (fun x => decide (x < m)) L
    have hle1 : L1.length ≤ m := ih L1 (list_nodup_filter _ hnd) (fun x hx => by
      have := (List.mem_filter.mp hx).2; simpa using this)
    have hle2 : L2.length ≤ 1 := by
      have hnd2 : L2.Nodup := list_nodup_filter (fun x => !(decide (x < m))) hnd
      cases hL2 : L2 with
      | nil => simp
      | cons a tl =>
        rw [hL2, List.nodup_cons] at hnd2
        have ha_mem : a ∈ L2 := by rw [hL2]; exact List.mem_cons_self ..
        have ha_eq : a = m := by
          have h1 := hlt a (List.mem_filter.mp ha_mem).1
          have h2 := (List.mem_filter.mp ha_mem).2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
          omega
        cases tl with
        | nil => simp
        | cons b _ =>
          have hb_mem : b ∈ L2 := by rw [hL2]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          have hb_eq : b = m := by
            have h1 := hlt b (List.mem_filter.mp hb_mem).1
            have h2 := (List.mem_filter.mp hb_mem).2
            simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
            omega
          rw [ha_eq, ← hb_eq] at hnd2
          exact absurd (List.mem_cons_self ..) hnd2.1
    change L1.length + L2.length = L.length at hpart
    omega

/-- **Theorem T3c-1 (Universal Upper Bound $\omega(G_n^{\mathrm{comp}}) \le n + 5$ for ALL $n \ge 3$):** -/
theorem compat_clique_le_all_n :
    ∀ n, 3 ≤ n → ∀ S, isCompatClique n S → S.length ≤ n + 5 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn3 : n = 2
    · subst hn3
      intro S ⟨hnd, hlt, _⟩
      exact list_nodup_lt_bound 8 S hnd hlt
    · have hn_ge3 : 3 ≤ n := by omega
      intro S ⟨hnd, hlt, hadj⟩
      have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      let S0 := S.filter (fun x => decide (x < 2 ^ n))
      let S1raw := S.filter (fun x => !(decide (x < 2 ^ n)))
      let S1 := S1raw.map (· - 2 ^ n)
      have hpart := list_length_filter_partition (fun x => decide (x < 2 ^ n)) S
      have hS1_len : S1.length = S1raw.length := List.length_map ..
      have hS0_clique : isCompatClique n S0 := by
        refine ⟨list_nodup_filter _ hnd, fun x hx => ?_, fun x hx y hy hne => ?_⟩
        · simpa using (List.mem_filter.mp hx).2
        · have hxlt : x < 2 ^ n := by simpa using (List.mem_filter.mp hx).2
          have hylt : y < 2 ^ n := by simpa using (List.mem_filter.mp hy).2
          have h := hadj x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hne
          rw [rightCompat_doubling_lower n x y hxlt hylt] at h
          exact h
      have hS1_clique : isCompatClique n S1 := by
        have hge : ∀ x ∈ S1raw, 2 ^ n ≤ x := by
          intro x hx
          have := (List.mem_filter.mp hx).2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
          omega
        refine ⟨list_nodup_map_sub (2 ^ n) (list_nodup_filter _ hnd) hge, fun x hx => ?_, fun x hx y hy hne => ?_⟩
        · rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
          have hult := hlt u (List.mem_filter.mp hu).1
          have huge := hge u hu
          omega
        · rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
          rcases List.mem_map.mp hy with ⟨v, hv, rfl⟩
          have hult := hlt u (List.mem_filter.mp hu).1
          have hvlt := hlt v (List.mem_filter.mp hv).1
          have huge := hge u hu
          have hvge := hge v hv
          have huv : u ≠ v := by omega
          have h := hadj u (List.mem_filter.mp hu).1 v (List.mem_filter.mp hv).1 huv
          have hu_eq : u = (u - 2 ^ n) + 2 ^ n := by omega
          have hv_eq : v = (v - 2 ^ n) + 2 ^ n := by omega
          rw [hu_eq, hv_eq, rightCompat_doubling_upper n (u - 2 ^ n) (v - 2 ^ n) (by omega) (by omega)] at h
          exact h
      have hle0 := ih hn_ge3 S0 hS0_clique
      have hle1 := ih hn_ge3 S1 hS1_clique
      -- Case split on whether S0 contains a nonzero element and whether S1 contains a nonzero element!
      by_cases h0_all : ∀ x ∈ S0, x = 0
      · have h0len : S0.length ≤ 1 := list_nodup_all_zero_le_one hS0_clique.1 h0_all
        change S0.length + S1raw.length = S.length at hpart
        omega
      · by_cases h1_all : ∀ y ∈ S1, y = 0
        · have h1len : S1.length ≤ 1 := list_nodup_all_zero_le_one hS1_clique.1 h1_all
          change S0.length + S1raw.length = S.length at hpart
          omega
        · -- Both S0 and S1 have a nonzero element! Constructively locate them via List.any!
          have hex0 : ∃ a ∈ S0, a ≠ 0 := by
            cases hfind : S0.find? (fun x => x != 0) with
            | none =>
              exfalso; apply h0_all; intro x hx
              have := List.find?_eq_none.mp hfind x hx
              simpa using this
            | some a =>
              exact ⟨a, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind⟩
          have hex1 : ∃ b ∈ S1, b ≠ 0 := by
            cases hfind : S1.find? (fun x => x != 0) with
            | none =>
              exfalso; apply h1_all; intro x hx
              have := List.find?_eq_none.mp hfind x hx
              simpa using this
            | some b =>
              exact ⟨b, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind⟩
          rcases hex0 with ⟨a, ha0, hane0⟩
          rcases hex1 with ⟨b, hb1, hbne0⟩
          -- Every nonzero x ∈ S0 must equal b, and every nonzero y ∈ S1 must equal a!
          have hcross : ∀ x ∈ S0, ∀ y ∈ S1, x = 0 ∨ y = 0 ∨ x = y := by
            intro x hx y hy
            rcases List.mem_map.mp hy with ⟨v, hv, rfl⟩
            have hxlt : x < 2 ^ n := by simpa using (List.mem_filter.mp hx).2
            have hvge : 2 ^ n ≤ v := by
              have := (List.mem_filter.mp hv).2
              simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this; omega
            have hvlt : v < 2 ^ (n + 1) := hlt v (List.mem_filter.mp hv).1
            have hne_xv : x ≠ v := by omega
            have h := hadj x (List.mem_filter.mp hx).1 v (List.mem_filter.mp hv).1 hne_xv
            have hv_eq : v = (v - 2 ^ n) + 2 ^ n := by omega
            rw [hv_eq, rightCompat_doubling_cross n x (v - 2 ^ n) hn_ge3 hxlt (by omega)] at h
            simpa using h
          have hS0_sub : ∀ x ∈ S0, x = 0 ∨ x = b := by
            intro x hx
            rcases hcross x hx b hb1 with rfl | hb0 | rfl
            · exact Or.inl rfl
            · exact absurd hb0 hbne0
            · exact Or.inr rfl
          have hS1_sub : ∀ y ∈ S1, y = 0 ∨ y = a := by
            intro y hy
            rcases hcross a ha0 y hy with ha_z | rfl | hay
            · exact absurd ha_z hane0
            · exact Or.inl rfl
            · exact Or.inr hay.symm
          have hlen0 := list_nodup_subset_two_le hS0_clique.1 b hS0_sub
          have hlen1 := list_nodup_subset_two_le hS1_clique.1 a hS1_sub
          change S0.length + S1raw.length = S.length at hpart
          omega

/-- **Theorem T3c-2 (Constructive $(n + 5)$-Clique Witness for ALL $n \ge 3$):** -/
theorem cdMaxClique_valid :
    ∀ n, 3 ≤ n → isCompatClique n (cdMaxClique n) ∧ (cdMaxClique n).length = n + 5 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn3 : n = 2
    · subst hn3
      refine ⟨⟨by decide, fun x hx => ?_, fun x hx y hy hne => ?_⟩, rfl⟩
      · simp [cdMaxClique] at hx; omega
      · -- In CD_3 (octonions), every distinct pair in {0..7} is right-compatible!
        have h : (List.range 8).all (fun a => (List.range 8).all (fun b =>
            a == b || rightCompat 3 a b)) = true := by decide
        have hxlt : x < 8 := by simp [cdMaxClique] at hx; omega
        have hylt : y < 8 := by simp [cdMaxClique] at hy; omega
        have h1 := List.all_eq_true.mp h x (List.mem_range.mpr hxlt)
        have h2 := List.all_eq_true.mp h1 y (List.mem_range.mpr hylt)
        simp only [Bool.or_eq_true, beq_iff_eq] at h2
        rcases h2 with heq | hok
        · exact absurd heq hne
        · exact hok
    · have hn_ge3 : 3 ≤ n := by omega
      rcases ih hn_ge3 with ⟨⟨hnd, hlt, hadj⟩, hlen⟩
      have hcd_eq : cdMaxClique (n + 1) = (2 ^ n) :: cdMaxClique n := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
        rfl
      have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hcd_eq]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨fun hmem => ?_, hnd⟩
        have := hlt (2 ^ n) hmem; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · have : 0 < 2 ^ n := Nat.two_pow_pos n; omega
        · have := hlt x hmem; omega
      · intro x hx y hy hne
        rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd rfl hne
        · rw [rightCompat_symm]
          have h0eq : (2 ^ n : Nat) = 0 + 2 ^ n := by omega
          rw [h0eq, rightCompat_doubling_cross n y 0 hn_ge3 (hlt y hy') (Nat.two_pow_pos n)]
          simp
        · have h0eq : (2 ^ n : Nat) = 0 + 2 ^ n := by omega
          rw [h0eq, rightCompat_doubling_cross n x 0 hn_ge3 (hlt x hx') (Nat.two_pow_pos n)]
          simp
        · rw [rightCompat_doubling_lower n x y (hlt x hx') (hlt y hy')]
          exact hadj x hx' y hy' hne
      · simp [hlen]

/-! ### Theorem T3d: Exact Saturation for $n \in \{3, 4, 5\}$ & Permanent Bott Rupture for ALL $n \ge 6$ -/

theorem hurwitz_radon_saturation_345 :
    (3 + 5 = hurwitzRadon 3) ∧ (4 + 5 = hurwitzRadon 4) ∧ (5 + 5 = hurwitzRadon 5) := by
  decide

/-- **Theorem T3d (Dimension-64 Hurwitz-Radon Bott-Periodicity Rupture):**
    For EVERY $n \ge 6$ ($\dim = 2^n \ge 64$), the Cayley-Dickson maximum right-composition
    dimension $n + 5$ is STRICTLY LESS than the classical Hurwitz-Radon ceiling $\rho(2^n)$,
    with permanent linear gap $\rho(2^n) - (n + 5) \ge n - 5$ (attaining $11 < 12$ at dim 64,
    $12 < 16$ at dim 128, $13 < 17$ at dim 256, ...). -/
theorem hurwitz_radon_rupture_all_ge6 (n : Nat) (hn : 6 ≤ n) :
    n + 5 < hurwitzRadon n ∧ n - 5 ≤ hurwitzRadon n - (n + 5) := by
  unfold hurwitzRadon
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hdm : n = 4 * (n / 4) + n % 4 := by omega
  rcases hmod with h | h | h | h <;> rw [h] <;> omega

/-! ### Theorem T3e: Universal All-$n$ Asymmetric Composition Tower $[2^{n-1}, 2(n+4), 2^n]$ -/

theorem compatClique_implies_full_normMult (n : Nat) (SR : List Nat)
    (hcliq : isCompatClique n SR) :
    isNormMultPair n (List.range (2 ^ n)) SR := by
  refine ⟨fun i hi => List.mem_range.mp hi, hcliq.2.1, ?_⟩
  intro i hi k hk j hj l hl hik hjl hxor
  have hilt : i < 2 ^ n := List.mem_range.mp hi
  have hrc := hcliq.2.2 j hj l hl hjl
  rw [rightCompat_iff] at hrc
  have hkeq : k = i ^^^ (j ^^^ l) := by
    rw [← hxor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hkeq]
  exact hrc.2 i hilt

/-- **Theorem T3e (Universal All-$n$ Asymmetric Doubling Tower $[2^{n-1}, 2(n+4), 2^n]$):**
    For EVERY $n \ge 4$, the half-algebra $\mathrm{CD}_{n-1}$ ($\dim = 2^{n-1}$) and the doubled
    right-multiplier subspace `doubledRightWitness n` ($\dim = 2(n + 4)$) form an EXACT integer
    sum-of-squares composition of type $[2^{n-1}, 2(n+4), 2^n]$ inside $\mathrm{CD}_n$!
    Instances: $[8, 16, 16]$ ($n=4$), $[16, 18, 32]$ ($n=5$), $[32, 20, 64]$ ($n=6$),
    $[64, 22, 128]$ ($n=7$), ... -/
theorem asymmetric_doubling_tower_all_n (n : Nat) (hn : 4 ≤ n) :
    isNormMultPair n (List.range (2 ^ (n - 1))) (doubledRightWitness n) ∧
    (doubledRightWitness n).Nodup ∧
    (doubledRightWitness n).length = 2 * (n + 4) := by
  let m := n - 1
  have hnm : n = m + 1 := by omega
  have hm3 : 3 ≤ m := by omega
  have h2m : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
  rcases cdMaxClique_valid m hm3 with ⟨hcliq, hlen⟩
  have hnm_pair := compatClique_implies_full_normMult m (cdMaxClique m) hcliq
  have hsub : n - 1 = m := rfl
  rw [hnm]
  unfold doubledRightWitness
  have hsub2 : m + 1 - 1 = m := by omega
  rw [hsub2]
  have hdisj : ∀ x ∈ cdMaxClique m, ∀ y ∈ (cdMaxClique m).map (· + 2 ^ m), x ≠ y := by
    intro x hx y hy
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    have hxlt := hcliq.2.1 x hx
    omega
  have hmap_nd : ((cdMaxClique m).map (· + 2 ^ m)).Nodup := by
    have hrec : ∀ L : List Nat, L.Nodup → (L.map (· + 2 ^ m)).Nodup := by
      intro L hnd
      induction L with
      | nil => exact List.nodup_nil
      | cons a tl ih =>
        rw [List.nodup_cons] at hnd
        rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, ih hnd.2⟩
        rcases List.mem_map.mp hmem with ⟨b, hb, hba⟩
        have : b = a := by omega
        subst this; exact hnd.1 hb
    exact hrec _ hcliq.1
  have hnodup : (cdMaxClique m ++ (cdMaxClique m).map (· + 2 ^ m)).Nodup := by
    rw [List.nodup_append]
    exact ⟨hcliq.1, hmap_nd, fun x hx y hy => hdisj x hx y hy⟩
  have hlength : (cdMaxClique m ++ (cdMaxClique m).map (· + 2 ^ m)).length = 2 * (m + 1 + 4) := by
    rw [List.length_append, List.length_map, hlen]; omega
  refine ⟨⟨?_, ?_, ?_⟩, hnodup, hlength⟩
  · intro i hi
    have hilt := List.mem_range.mp hi; omega
  · intro j hj
    rcases List.mem_append.mp hj with hj1 | hj2
    · have := hcliq.2.1 j hj1; omega
    · rcases List.mem_map.mp hj2 with ⟨z, hz, rfl⟩
      have := hcliq.2.1 z hz; omega
  · intro i hi k hk j hj l hl hik hjl hxor
    have hilt : i < 2 ^ m := List.mem_range.mp hi
    have hklt : k < 2 ^ m := List.mem_range.mp hk
    have hdlt : i ^^^ k < 2 ^ m := Nat.xor_lt_two_pow hilt hklt
    rcases List.mem_append.mp hj with hj1 | hj2 <;> rcases List.mem_append.mp hl with hl1 | hl2
    · -- Both j, l in lower half (cdMaxClique m): reduces directly to CD_m!
      have hjlt := hcliq.2.1 j hj1
      have hllt := hcliq.2.1 l hl1
      rw [cdSign_succ_ll m i j hilt hjlt, cdSign_succ_ll m k l hklt hllt,
          cdSign_succ_ll m i l hilt hllt, cdSign_succ_ll m k j hklt hjlt]
      exact hnm_pair.2.2 i (List.mem_range.mpr hilt) k (List.mem_range.mpr hklt) j hj1 l hl1 hik hjl hxor
    · -- j < 2^m, l = b + 2^m: IMPOSSIBLE because i^k < 2^m while j^l ≥ 2^m!
      rcases List.mem_map.mp hl2 with ⟨b, hb, rfl⟩
      have hjlt := hcliq.2.1 j hj1
      have hblt := hcliq.2.1 b hb
      have hge : j ^^^ (b + 2 ^ m) = (j ^^^ b) + 2 ^ m := xor_add_right hjlt hblt
      omega
    · -- j = a + 2^m, l < 2^m: IMPOSSIBLE because i^k < 2^m while j^l ≥ 2^m!
      rcases List.mem_map.mp hj2 with ⟨a, ha, rfl⟩
      have halt := hcliq.2.1 a ha
      have hllt := hcliq.2.1 l hl1
      have hge : (a + 2 ^ m) ^^^ l = (a ^^^ l) + 2 ^ m := xor_add_left halt hllt
      omega
    · -- Both j = a + 2^m, l = b + 2^m in upper half!
      rcases List.mem_map.mp hj2 with ⟨a, ha, rfl⟩
      rcases List.mem_map.mp hl2 with ⟨b, hb, rfl⟩
      have halt := hcliq.2.1 a ha
      have hblt := hcliq.2.1 b hb
      have hab : a ≠ b := by omega
      have hxor_ab : i ^^^ k = a ^^^ b := by rw [hxor, xor_add_both halt hblt]
      -- Goal: cdSign m a i * cdSign m b k + cdSign m b i * cdSign m a k = 0!
      rw [cdSign_succ_lh m i a hilt, cdSign_succ_lh m k b hklt,
          cdSign_succ_lh m i b hilt, cdSign_succ_lh m k a hklt]
      -- Use left-vs-right symmetry! By hnm_pair on (i, k) and (a, b):
      -- cdSign m i a * cdSign m k b + cdSign m i b * cdSign m k a = 0!
      have hbase := hnm_pair.2.2 i (List.mem_range.mpr hilt) k (List.mem_range.mpr hklt) a ha b hb hik hab hxor_ab
      -- Compare (cdSign m a i * cdSign m b k + cdSign m b i * cdSign m a k) with hbase!
      -- Notice: if i, k, a, b are all > 0 and pairwise distinct (except possibly i=a, k=b or i=b, k=a):
      -- Even simpler: prove for ALL u, v < 2^m with u ≠ v, cdSign m u v = -cdSign m v u when u>0,v>0, else +cdSign m v u!
      have hswap : ∀ u v, u < 2 ^ m → v < 2 ^ m →
          cdSign m v u = (if u = 0 ∨ v = 0 ∨ u = v then 1 else -1) * cdSign m u v := by
        intro u v hu hv
        by_cases hu0 : u = 0
        · subst hu0; simp [cdSign_zero_left m v hv, cdSign_zero_right m v hv]
        · by_cases hv0 : v = 0
          · subst hv0; simp [cdSign_zero_left m u hu, cdSign_zero_right m u hu]
          · by_cases huv : u = v
            · subst huv; simp
            · simp only [hu0, hv0, huv, or_self, ↓reduceIte]
              rw [cdSign_anticomm m v u (by omega) (by omega) hv hu (Ne.symm huv)]
              simp
      -- Check if {i, k} intersects {0, a, b} or is disjoint!
      by_cases hi0 : i = 0
      · subst hi0; rw [Nat.zero_xor] at hxor_ab
        rw [cdSign_zero_right m a halt, cdSign_zero_right m b hblt, Int.one_mul, Int.one_mul]
        rw [cdSign_zero_left m a halt, cdSign_zero_left m b hblt, Int.one_mul, Int.one_mul] at hbase
        by_cases ha0 : a = 0
        · subst ha0; rw [Nat.zero_xor] at hxor_ab; subst hxor_ab
          rw [cdSign_zero_left m k hklt, cdSign_diag m k (by omega) hklt]; rfl
        · by_cases hb0 : b = 0
          · subst hb0; rw [Nat.xor_zero] at hxor_ab; subst hxor_ab
            rw [cdSign_zero_left m k hklt, cdSign_diag m k (by omega) hklt]; rfl
          · have hka : k ≠ a := by
              intro h; rw [h] at hxor_ab; have : a ^^^ a = (a ^^^ b) ^^^ a := congrArg (· ^^^ a) hxor_ab
              rw [Nat.xor_self, Nat.xor_comm a b, xor_sub_self_cancel] at this; exact hb0 this.symm
            have hkb : k ≠ b := by
              intro h; rw [h] at hxor_ab; have : b ^^^ b = (a ^^^ b) ^^^ b := congrArg (· ^^^ b) hxor_ab
              rw [Nat.xor_self, xor_sub_self_cancel] at this; exact ha0 this.symm
            rw [cdSign_anticomm m b k (by omega) (by omega) hblt hklt (Ne.symm hkb),
                cdSign_anticomm m a k (by omega) (by omega) halt hklt (Ne.symm hka)]
            omega
      · by_cases hk0 : k = 0
        · subst hk0; rw [Nat.xor_zero] at hxor_ab
          rw [cdSign_zero_right m b hblt, cdSign_zero_right m a halt, Int.mul_one, Int.mul_one]
          rw [cdSign_zero_left m b hblt, cdSign_zero_left m a halt, Int.mul_one, Int.mul_one] at hbase
          by_cases ha0 : a = 0
          · subst ha0; rw [Nat.zero_xor] at hxor_ab; subst hxor_ab
            rw [cdSign_zero_left m i hilt, cdSign_diag m i (by omega) hilt]; rfl
          · by_cases hb0 : b = 0
            · subst hb0; rw [Nat.xor_zero] at hxor_ab; subst hxor_ab
              rw [cdSign_zero_left m i hilt, cdSign_diag m i (by omega) hilt]; rfl
            · have hia : i ≠ a := by
                intro h; rw [h] at hxor_ab; have : a ^^^ a = (a ^^^ b) ^^^ a := congrArg (· ^^^ a) hxor_ab
                rw [Nat.xor_self, Nat.xor_comm a b, xor_sub_self_cancel] at this; exact hb0 this.symm
              have hib : i ≠ b := by
                intro h; rw [h] at hxor_ab; have : b ^^^ b = (a ^^^ b) ^^^ b := congrArg (· ^^^ b) hxor_ab
                rw [Nat.xor_self, xor_sub_self_cancel] at this; exact ha0 this.symm
              rw [cdSign_anticomm m a i (by omega) (by omega) halt hilt (Ne.symm hia),
                  cdSign_anticomm m b i (by omega) (by omega) hblt hilt (Ne.symm hib)]
              omega
        · by_cases ha0 : a = 0
          · subst ha0; rw [Nat.zero_xor] at hxor_ab
            rw [cdSign_zero_left m i hilt, cdSign_zero_left m k hklt, Int.one_mul, Int.mul_one]
            rw [cdSign_zero_right m i hilt, cdSign_zero_right m k hklt, Int.one_mul, Int.mul_one] at hbase
            have hib : i ≠ b := by
              intro h; rw [h] at hxor_ab; have : b ^^^ k = b := hxor_ab
              have : (b ^^^ k) ^^^ b = b ^^^ b := congrArg (· ^^^ b) this
              rw [Nat.xor_comm b k, xor_sub_self_cancel, Nat.xor_self] at this; exact hk0 this
            have hkb : k ≠ b := by
              intro h; rw [h] at hxor_ab; have : (i ^^^ b) ^^^ b = b ^^^ b := congrArg (· ^^^ b) hxor_ab
              rw [xor_sub_self_cancel, Nat.xor_self] at this; exact hi0 this
            rw [cdSign_anticomm m b k (by omega) (by omega) hblt hklt (Ne.symm hkb),
                cdSign_anticomm m b i (by omega) (by omega) hblt hilt (Ne.symm hib)]
            omega
          · by_cases hb0 : b = 0
            · subst hb0; rw [Nat.xor_zero] at hxor_ab
              rw [cdSign_zero_left m k hklt, cdSign_zero_left m i hilt, Int.mul_one, Int.one_mul]
              rw [cdSign_zero_right m k hklt, cdSign_zero_right m i hilt, Int.mul_one, Int.one_mul] at hbase
              have hia : i ≠ a := by
                intro h; rw [h] at hxor_ab; have : (a ^^^ k) ^^^ a = a ^^^ a := congrArg (· ^^^ a) hxor_ab
                rw [Nat.xor_comm a k, xor_sub_self_cancel, Nat.xor_self] at this; exact hk0 this
              have hka : k ≠ a := by
                intro h; rw [h] at hxor_ab; have : (i ^^^ a) ^^^ a = a ^^^ a := congrArg (· ^^^ a) hxor_ab
                rw [xor_sub_self_cancel, Nat.xor_self] at this; exact hi0 this
              rw [cdSign_anticomm m a i (by omega) (by omega) halt hilt (Ne.symm hia),
                  cdSign_anticomm m a k (by omega) (by omega) halt hklt (Ne.symm hka)]
              omega
            · by_cases hia : i = a
              · subst hia
                have hkb : k = b := by
                  have : (i ^^^ k) ^^^ i = (i ^^^ b) ^^^ i := congrArg (· ^^^ i) hxor_ab
                  rw [Nat.xor_comm i k, Nat.xor_comm i b, xor_sub_self_cancel, xor_sub_self_cancel] at this
                  exact this
                subst hkb
                rw [cdSign_diag m i (by omega) hilt, cdSign_diag m k (by omega) hklt,
                    cdSign_anticomm m k i (by omega) (by omega) hklt hilt (Ne.symm hik)]
                rcases cdSign_val_pm1 m i k with h | h <;> simp [h]
              · by_cases hib : i = b
                · subst hib
                  have hka : k = a := by
                    have : (i ^^^ k) ^^^ i = (a ^^^ i) ^^^ i := congrArg (· ^^^ i) hxor_ab
                    rw [Nat.xor_comm i k, xor_sub_self_cancel, xor_sub_self_cancel] at this
                    exact this
                  subst hka
                  rw [cdSign_diag m i (by omega) hilt, cdSign_diag m k (by omega) hklt,
                      cdSign_anticomm m k i (by omega) (by omega) hklt hilt (Ne.symm hik)]
                  rcases cdSign_val_pm1 m i k with h | h <;> simp [h]
                · have hka : k ≠ a := by
                    intro h; rw [h] at hxor_ab
                    have : (i ^^^ a) ^^^ a = (a ^^^ b) ^^^ a := congrArg (· ^^^ a) hxor_ab
                    rw [xor_sub_self_cancel, Nat.xor_comm a b, xor_sub_self_cancel] at this; exact hib this
                  have hkb : k ≠ b := by
                    intro h; rw [h] at hxor_ab
                    have : (i ^^^ b) ^^^ b = (a ^^^ b) ^^^ b := congrArg (· ^^^ b) hxor_ab
                    rw [xor_sub_self_cancel, xor_sub_self_cancel] at this; exact hia this
                  rw [cdSign_anticomm m a i (by omega) (by omega) halt hilt (Ne.symm hia),
                      cdSign_anticomm m b k (by omega) (by omega) hblt hklt (Ne.symm hkb),
                      cdSign_anticomm m b i (by omega) (by omega) hblt hilt (Ne.symm hib),
                      cdSign_anticomm m a k (by omega) (by omega) halt hklt (Ne.symm hka),
                      Int.neg_mul_neg, Int.neg_mul_neg]
                  exact hbase

end

end CDTerrace
