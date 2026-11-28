module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import CDTerrace.Basic
public import CDTerrace.MirrorConservation

/-!
# CDTerrace.OddBladeExclusion — Universal Odd-Parity Zero-Divisor Exclusion & Odd-Pivot Matrix Inversion

Proves universally for EVERY dimension $2^n$ ($n \in \mathbb{N}$), EVERY signature
$\gamma \in \{\pm 1\}^n$ (and more generally EVERY $\mathbb{Z}_2^n$-twisted group algebra with
arbitrary $\{\pm 1\}$ cocycle $\sigma$):

- **T6a (`twisted_frobenius_mod2_involution`):** In any $\mathbb{Z}_2^n$-twisted group algebra with
  arbitrary sign function $\sigma(a, b) \in \{\pm 1\}$, any integer element $x \in \mathbb{Z}^{2^n}$
  with odd coordinate sum $\sum_{a < 2^n} x_a \equiv 1 \pmod 2$ acts as an exact modulo-2 involution
  on both left and right: $x \cdot (x \cdot y) \equiv y \pmod 2$ and $(y \cdot x) \cdot x \equiv y \pmod 2$.
- **T6b (`odd_parity_zero_divisor_exclusion_all_n`):** Using a self-contained zero-Mathlib
  fraction-free odd-pivot Gauss-Jordan inversion theorem (`odd_mod2_inv_matrix_integral_inv`),
  ANY $x \in \mathbb{Z}^{2^n}$ with odd coordinate sum admits exact odd-scalar integral inverses
  $B_L L_x = \Delta_L I$ ($\Delta_L \equiv 1 \pmod 2$) and $B_R R_x = \Delta_R I$
  ($\Delta_R \equiv 1 \pmod 2$). Consequently, $x$ is invertible over $\mathbb{Q}$, $\mathbb{R}$,
  $\mathbb{C}$, and every $\mathbb{F}_p$ ($p \nmid \Delta$), and is NEVER a left or right zero
  divisor over $\mathbb{Z}$ (or any characteristic-0 extension) in any $\mathrm{CD}_n(\gamma)$.
- **T6c (`odd_support_unit_blades_non_zd_all_n`):** Every signed odd-support unit $k$-blade
  $x = \sum_{a \in S} \varepsilon(a)\, e_a$ ($|S|$ odd, $\varepsilon(a) \in \{\pm 1\}$ — including
  ALL 3-blades $e_i \pm e_j \pm e_k$, 5-blades, 7-blades, ...) has odd coordinate sum and is
  therefore universally non-zero-divisor (left and right) across all dimensions $2^n$ and all $2^n$
  signatures. Contrapositively, EVERY integer zero divisor $x \in \mathrm{CD}_n(\gamma)$ must have
  EVEN coordinate sum $\sum_a x_a \equiv 0 \pmod 2$.
-/

namespace CDTerrace

public section

/-! ### Core Definitions for Twisted Multiplication, Matrix Algebra & Signed Blades -/

/-- Bilinear product in an arbitrary $\mathbb{Z}_2^n$-twisted group algebra with sign cocycle $\sigma$. -/
@[expose] def twistedMul (n : Nat) (σ : Nat → Nat → Int) (u v : Nat → Int) (t : Nat) : Int :=
  sumInt (fun a => σ a (a ^^^ t) * u a * v (a ^^^ t)) (2 ^ n)

/-- Odd coordinate-sum predicate $\sum_{a=0}^{2^n - 1} x_a \equiv 1 \pmod 2$. -/
@[expose] def oddCoordSum (n : Nat) (x : Nat → Int) : Prop :=
  sumInt x (2 ^ n) % 2 = 1

/-- $N \times N$ integer matrix multiplication $(A B)_{i, j} = \sum_{k=0}^{N-1} A_{i, k} B_{k, j}$. -/
@[expose] def matMulInt (N : Nat) (A B : Nat → Nat → Int) (i j : Nat) : Int :=
  sumInt (fun k => A i k * B k j) N

/-- $N \times N$ integer identity matrix. -/
@[expose] def idMatInt (i j : Nat) : Int :=
  if i == j then 1 else 0

/-- Left-multiplication matrix $(L_x)_{t, j} = \sigma_n^\gamma(t \oplus j, j)\, x_{t \oplus j}$
    for $x \in \mathrm{CD}_n(\gamma)$. -/
@[expose] def leftMulMat (n flipMask : Nat) (x : Nat → Int) (t j : Nat) : Int :=
  cdSignGamma n flipMask (t ^^^ j) j * x (t ^^^ j)

/-- Right-multiplication matrix $(R_x)_{t, j} = \sigma_n^\gamma(j, t \oplus j)\, x_{t \oplus j}$
    for $x \in \mathrm{CD}_n(\gamma)$. -/
@[expose] def rightMulMat (n flipMask : Nat) (x : Nat → Int) (t j : Nat) : Int :=
  cdSignGamma n flipMask j (t ^^^ j) * x (t ^^^ j)

/-- Coordinate vector of a signed unit blade $\sum_{a \in S} \varepsilon(a)\, e_a$. -/
@[expose] def signedBladeSum : List Nat → (Nat → Int) → Nat → Int
  | [], _, _ => 0
  | a :: rest, ε, t => (if t == a then ε a else 0) + signedBladeSum rest ε t

/-! ### Elementary `sumInt` Algebra & XOR-Bijection Lemmas -/

theorem sumInt_add_fn (f g : Nat → Int) (m : Nat) :
    sumInt (fun k => f k + g k) m = sumInt f m + sumInt g m := by
  induction m with
  | zero => rfl
  | succ m ih => unfold sumInt; rw [ih]; omega

theorem sumInt_sub_fn (f g : Nat → Int) (m : Nat) :
    sumInt (fun k => f k - g k) m = sumInt f m - sumInt g m := by
  induction m with
  | zero => rfl
  | succ m ih => unfold sumInt; rw [ih]; omega

theorem sumInt_mul_left (c : Int) (f : Nat → Int) (m : Nat) :
    sumInt (fun k => c * f k) m = c * sumInt f m := by
  induction m with
  | zero => simp [sumInt]
  | succ m ih => unfold sumInt; rw [ih, Int.mul_add]

theorem sumInt_mul_right (f : Nat → Int) (c : Int) (m : Nat) :
    sumInt (fun k => f k * c) m = sumInt f m * c := by
  induction m with
  | zero => simp [sumInt]
  | succ m ih => unfold sumInt; rw [ih, Int.add_mul]

theorem sumInt_split (f : Nat → Int) (a b : Nat) :
    sumInt f (a + b) = sumInt f a + sumInt (fun k => f (a + k)) b := by
  induction b with
  | zero => simp [sumInt]
  | succ b ih =>
    rw [Nat.add_succ]
    show sumInt f (a + b) + f (a + b) = sumInt f a + (sumInt (fun k => f (a + k)) b + f (a + b))
    rw [ih]; omega

theorem sumInt_swap (g : Nat → Nat → Int) (M N : Nat) :
    sumInt (fun a => sumInt (fun b => g a b) M) N =
      sumInt (fun b => sumInt (fun a => g a b) N) M := by
  induction N with
  | zero =>
    show (0 : Int) = sumInt (fun _ => 0) M
    rw [sumInt_zero]
  | succ N ih =>
    show sumInt (fun a => sumInt (fun b => g a b) M) N + sumInt (fun b => g N b) M =
         sumInt (fun b => sumInt (fun a => g a b) N + g N b) M
    rw [ih, ← sumInt_add_fn]

theorem sumInt_ite_eq (a : Nat) (val : Int) :
    ∀ m, sumInt (fun k => if k == a then val else 0) m = if a < m then val else 0 := by
  intro m
  induction m with
  | zero => simp [sumInt]
  | succ m ih =>
    unfold sumInt; rw [ih]
    by_cases h : m = a
    · subst h; simp
    · have hne : (m == a) = false := beq_false_of_ne h
      by_cases hlt : a < m
      · have hlt2 : a < m + 1 := by omega
        simp [hne, hlt, hlt2]
      · have hlt2 : ¬(a < m + 1) := by omega
        simp [hne, hlt, hlt2]

theorem sumInt_ite_eq_symm (a : Nat) (val : Int) (m : Nat) :
    sumInt (fun k => if a == k then val else 0) m = if a < m then val else 0 := by
  rw [← sumInt_ite_eq a val m]
  apply sumInt_ext; intro k _
  by_cases h : a = k
  · subst h; simp
  · simp [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]

theorem sumInt_xor_bijection :
    ∀ (m : Nat) (f : Nat → Int) (mask : Nat),
      mask < 2 ^ m →
      sumInt f (2 ^ m) = sumInt (fun k => f (k ^^^ mask)) (2 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro f mask hm
    have hm0 : mask = 0 := by omega
    subst hm0; simp [sumInt]
  | succ m ihm =>
    intro f mask hm
    have h2m : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
    rw [h2m, sumInt_split, sumInt_split]
    by_cases hmlt : mask < 2 ^ m
    · have h1 := ihm f mask hmlt
      have h2 := ihm (fun k => f (2 ^ m + k)) mask hmlt
      have heq2 : sumInt (fun k => f ((2 ^ m + k) ^^^ mask)) (2 ^ m) =
                  sumInt (fun k => f (2 ^ m + (k ^^^ mask))) (2 ^ m) := by
        apply sumInt_ext; intro k hk
        rw [Nat.add_comm (2 ^ m) k, xor_add_left hk hmlt, Nat.add_comm (k ^^^ mask) (2 ^ m)]
      rw [heq2, ← h1, ← h2]
    · let lo := mask - 2 ^ m
      have hlo : lo < 2 ^ m := by omega
      have hmask_eq : mask = lo + 2 ^ m := by omega
      have h1 := ihm (fun k => f (2 ^ m + k)) lo hlo
      have h2 := ihm f lo hlo
      have heqA : sumInt (fun k => f (k ^^^ mask)) (2 ^ m) =
                  sumInt (fun k => f (2 ^ m + (k ^^^ lo))) (2 ^ m) := by
        apply sumInt_ext; intro k hk
        rw [hmask_eq, xor_add_right hk hlo, Nat.add_comm (k ^^^ lo) (2 ^ m)]
      have heqB : sumInt (fun k => f ((2 ^ m + k) ^^^ mask)) (2 ^ m) =
                  sumInt (fun k => f (k ^^^ lo)) (2 ^ m) := by
        apply sumInt_ext; intro k hk
        rw [hmask_eq, Nat.add_comm (2 ^ m) k, xor_add_both hk hlo]
      rw [heqA, heqB, ← h1, ← h2, Int.add_comm]

theorem sumInt_emod2_congr (f g : Nat → Int) (m : Nat)
    (h : ∀ k, k < m → f k % 2 = g k % 2) :
    sumInt f m % 2 = sumInt g m % 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold sumInt
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h m (by omega)
    omega

theorem int_mul_emod2_even (a b : Int) (ha : a % 2 = 0) : (a * b) % 2 = 0 := by
  have hq : a = 2 * (a / 2) := by omega
  have hm : a * b = 2 * ((a / 2) * b) := by
    calc a * b = (2 * (a / 2)) * b := congrArg (· * b) hq
      _ = 2 * ((a / 2) * b) := Int.mul_assoc 2 (a / 2) b
  omega

theorem int_mul_emod2_odd_odd (a b : Int) (ha : a % 2 = 1) (hb : b % 2 = 1) : (a * b) % 2 = 1 := by
  have hqa : a = 2 * (a / 2) + 1 := by omega
  have hqb : b = 2 * (b / 2) + 1 := by omega
  have hm : a * b = 2 * (2 * (a / 2) * (b / 2) + (a / 2) + (b / 2)) + 1 := by
    calc a * b = (2 * (a / 2) + 1) * (2 * (b / 2) + 1) := by rw [← hqa, ← hqb]
      _ = 2 * (a / 2) * (2 * (b / 2)) + 2 * (a / 2) * 1 + 1 * (2 * (b / 2)) + 1 * 1 := by
            rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
      _ = 2 * (2 * (a / 2) * (b / 2) + (a / 2) + (b / 2)) + 1 := by
            have h1 : 2 * (a / 2) * (2 * (b / 2)) = 2 * (2 * (a / 2) * (b / 2)) := by ac_rfl
            rw [h1, Int.mul_one, Int.one_mul, Int.mul_add, Int.mul_add]
            rfl
  omega

theorem int_mul_emod2_odd_left (a b : Int) (ha : a % 2 = 1) : (a * b) % 2 = b % 2 := by
  have hqa : a = 2 * (a / 2) + 1 := by omega
  have hm : a * b = 2 * ((a / 2) * b) + b := by
    calc a * b = (2 * (a / 2) + 1) * b := congrArg (· * b) hqa
      _ = 2 * (a / 2) * b + 1 * b := Int.add_mul _ _ _
      _ = 2 * ((a / 2) * b) + b := by rw [Int.mul_assoc, Int.one_mul]
  omega

theorem int_sq_emod2 (z : Int) : (z * z) % 2 = z % 2 := by
  have h : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases h with h0 | h1
  · rw [int_mul_emod2_even z z h0, h0]
  · rw [int_mul_emod2_odd_odd z z h1 h1, h1]

theorem pm1_mul_emod2 (s z : Int) (hs : s = 1 ∨ s = -1) : (s * z) % 2 = z % 2 := by
  rcases hs with rfl | rfl <;> omega

theorem sumInt_self_xor_even :
    ∀ n (x : Nat → Int) (u : Nat), 0 < u → u < 2 ^ n →
      sumInt (fun a => x a * x (a ^^^ u)) (2 ^ n) % 2 = 0 := by
  intro n
  induction n with
  | zero => intro _ u hu0 hu1; omega
  | succ n ih =>
    intro x u hu0 hu1
    have h2n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [h2n, sumInt_split]
    by_cases hult : u < 2 ^ n
    · have h1 := ih x u hu0 hult
      have h2 := ih (fun a => x (2 ^ n + a)) u hu0 hult
      have hhi : sumInt (fun a => x (2 ^ n + a) * x ((2 ^ n + a) ^^^ u)) (2 ^ n) =
                 sumInt (fun a => x (2 ^ n + a) * x (2 ^ n + (a ^^^ u))) (2 ^ n) := by
        apply sumInt_ext; intro a ha
        rw [Nat.add_comm (2 ^ n) a, xor_add_left ha hult, Nat.add_comm (a ^^^ u) (2 ^ n)]
      rw [hhi]; omega
    · let lo := u - 2 ^ n
      have hlo : lo < 2 ^ n := by omega
      have hu_eq : u = lo + 2 ^ n := by omega
      have hhi : sumInt (fun a => x (2 ^ n + a) * x ((2 ^ n + a) ^^^ u)) (2 ^ n) =
                 sumInt (fun a => x a * x (a ^^^ u)) (2 ^ n) := by
        have hstep1 : sumInt (fun a => x (2 ^ n + a) * x ((2 ^ n + a) ^^^ u)) (2 ^ n) =
                      sumInt (fun a => x (2 ^ n + a) * x (a ^^^ lo)) (2 ^ n) := by
          apply sumInt_ext; intro a ha
          rw [hu_eq, Nat.add_comm (2 ^ n) a, xor_add_both ha hlo]
        rw [hstep1, sumInt_xor_bijection n (fun a => x (2 ^ n + a) * x (a ^^^ lo)) lo hlo]
        apply sumInt_ext; intro a ha
        rw [xor_sub_self_cancel, hu_eq, xor_add_right ha hlo,
            Nat.add_comm (2 ^ n) (a ^^^ lo), Int.mul_comm]
      rw [hhi]; omega

/-! ### Theorem T6a: Mod-2 Twisted-Group-Algebra Frobenius Involution -/

/-- **Theorem T6a (Universal Mod-2 Twisted-Group-Algebra Frobenius Involution):**
    For EVERY $n \in \mathbb{N}$, EVERY arbitrary $\{\pm 1\}$ sign cocycle $\sigma$, and EVERY
    $x \in \mathbb{Z}^{2^n}$ with odd coordinate sum (`oddCoordSum n x`), both left and right
    twisted multiplications by $x$ are exact involutions modulo 2, and `twistedMul` coincides
    definitionally with `cdMulCoordGamma` for `σ = cdSignGamma n f`. -/
theorem twisted_frobenius_mod2_involution (n : Nat) (σ : Nat → Nat → Int)
    (hσ : ∀ a b, σ a b = 1 ∨ σ a b = -1) (x : Nat → Int) (hx : oddCoordSum n x) :
    (∀ y t, t < 2 ^ n → (twistedMul n σ x (twistedMul n σ x y) t - y t) % 2 = 0) ∧
    (∀ y t, t < 2 ^ n → (twistedMul n σ (twistedMul n σ y x) x t - y t) % 2 = 0) ∧
    (∀ f u v t, twistedMul n (cdSignGamma n f) u v t = cdMulCoordGamma n f u v t) := by
  -- Core XOR-convolution involution lemma mod 2
  have hconv : ∀ (y : Nat → Int) (t : Nat), t < 2 ^ n →
      sumInt (fun a => x a * sumInt (fun b => x b * y (b ^^^ (a ^^^ t))) (2 ^ n)) (2 ^ n) % 2 =
        y t % 2 := by
    intro y t ht
    have hstep1 :
        sumInt (fun a => x a * sumInt (fun b => x b * y (b ^^^ (a ^^^ t))) (2 ^ n)) (2 ^ n) =
        sumInt (fun a => sumInt (fun b => (x a * x b) * y (b ^^^ (a ^^^ t))) (2 ^ n)) (2 ^ n) := by
      apply sumInt_ext; intro a _
      rw [← sumInt_mul_left]
      apply sumInt_ext; intro b _
      rw [Int.mul_assoc]
    have hstep2 :
        sumInt (fun a => sumInt (fun b => (x a * x b) * y (b ^^^ (a ^^^ t))) (2 ^ n)) (2 ^ n) =
        sumInt (fun a => sumInt (fun u => (x a * x (u ^^^ a)) * y (u ^^^ t)) (2 ^ n)) (2 ^ n) := by
      apply sumInt_ext; intro a ha
      rw [sumInt_xor_bijection n (fun b => (x a * x b) * y (b ^^^ (a ^^^ t))) a ha]
      apply sumInt_ext; intro u _
      have hxa : (u ^^^ a) ^^^ (a ^^^ t) = u ^^^ t := by
        rw [← Nat.xor_assoc, Nat.xor_assoc u a a, Nat.xor_self, Nat.xor_zero]
      rw [hxa]
    rw [hstep1, hstep2, sumInt_swap]
    have hstep3 :
        sumInt (fun u => sumInt (fun a => (x a * x (u ^^^ a)) * y (u ^^^ t)) (2 ^ n)) (2 ^ n) % 2 =
        sumInt (fun u => if u == 0 then y t else 0) (2 ^ n) % 2 := by
      apply sumInt_emod2_congr; intro u hu
      rw [sumInt_mul_right]
      by_cases hu0 : u = 0
      · subst hu0
        simp only [Nat.zero_xor, beq_self_eq_true, ↓reduceIte]
        have hsq : sumInt (fun a => x a * x a) (2 ^ n) % 2 = 1 := by
          have h1 := sumInt_emod2_congr (fun a => x a * x a) x (2 ^ n) (fun a _ => int_sq_emod2 (x a))
          rw [h1]; exact hx
        exact int_mul_emod2_odd_left _ (y t) hsq
      · have hne : (u == 0) = false := beq_false_of_ne hu0
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        have hev : sumInt (fun a => x a * x (u ^^^ a)) (2 ^ n) % 2 = 0 := by
          have hcomm : sumInt (fun a => x a * x (u ^^^ a)) (2 ^ n) =
                       sumInt (fun a => x a * x (a ^^^ u)) (2 ^ n) := by
            apply sumInt_ext; intro a _; rw [Nat.xor_comm u a]
          rw [hcomm]
          exact sumInt_self_xor_even n x u (by omega) hu
        exact int_mul_emod2_even _ (y (u ^^^ t)) hev
    rw [hstep3, sumInt_ite_eq 0 (y t) (2 ^ n)]
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    simp [hpos]
  -- Drop ±1 signs mod 2 for twistedMul
  have htw_mod : ∀ u v t,
      twistedMul n σ u v t % 2 = sumInt (fun a => u a * v (a ^^^ t)) (2 ^ n) % 2 := by
    intro u v t
    unfold twistedMul
    apply sumInt_emod2_congr; intro a _
    rw [Int.mul_assoc]
    exact pm1_mul_emod2 (σ a (a ^^^ t)) (u a * v (a ^^^ t)) (hσ a (a ^^^ t))
  refine ⟨?_, ?_, fun _ _ _ _ => rfl⟩
  · intro y t ht
    have h1 : twistedMul n σ x (twistedMul n σ x y) t % 2 =
              sumInt (fun a => x a * sumInt (fun b => x b * y (b ^^^ (a ^^^ t))) (2 ^ n)) (2 ^ n) % 2 := by
      rw [htw_mod]
      apply sumInt_emod2_congr; intro a _
      have hinner := htw_mod x y (a ^^^ t)
      have hdiff : (x a * twistedMul n σ x y (a ^^^ t) -
                    x a * sumInt (fun b => x b * y (b ^^^ (a ^^^ t))) (2 ^ n)) % 2 = 0 := by
        rw [← Int.mul_sub, Int.mul_comm]
        exact int_mul_emod2_even _ (x a) (by omega)
      omega
    rw [hconv y t ht] at h1
    omega
  · intro y t ht
    have hr_comm : ∀ u v s, s < 2 ^ n →
        twistedMul n σ u v s % 2 = sumInt (fun a => v a * u (a ^^^ s)) (2 ^ n) % 2 := by
      intro u v s hs
      rw [htw_mod, sumInt_xor_bijection n (fun a => u a * v (a ^^^ s)) s hs]
      apply sumInt_emod2_congr; intro a _
      rw [xor_sub_self_cancel, Int.mul_comm]
    have h1 : twistedMul n σ (twistedMul n σ y x) x t % 2 =
              sumInt (fun a => x a * sumInt (fun b => x b * y (b ^^^ (a ^^^ t))) (2 ^ n)) (2 ^ n) % 2 := by
      rw [hr_comm _ x t ht]
      apply sumInt_emod2_congr; intro a ha
      have hinner := hr_comm y x (a ^^^ t) (Nat.xor_lt_two_pow ha ht)
      have hdiff : (x a * twistedMul n σ y x (a ^^^ t) -
                    x a * sumInt (fun b => x b * y (b ^^^ (a ^^^ t))) (2 ^ n)) % 2 = 0 := by
        rw [← Int.mul_sub, Int.mul_comm]
        exact int_mul_emod2_even _ (x a) (by omega)
      omega
    rw [hconv y t ht] at h1
    omega

/-! ### Self-Contained Zero-Mathlib Fraction-Free Odd-Pivot Matrix Inversion -/

theorem matMulInt_assoc (N : Nat) (A B C : Nat → Nat → Int) (i j : Nat) :
    matMulInt N (matMulInt N A B) C i j = matMulInt N A (matMulInt N B C) i j := by
  unfold matMulInt
  have h1 : sumInt (fun k => sumInt (fun m => A i m * B m k) N * C k j) N =
            sumInt (fun k => sumInt (fun m => A i m * (B m k * C k j)) N) N := by
    apply sumInt_ext; intro k _
    rw [← sumInt_mul_right]
    apply sumInt_ext; intro m _; rw [Int.mul_assoc]
  have h2 : sumInt (fun m => A i m * sumInt (fun k => B m k * C k j) N) N =
            sumInt (fun m => sumInt (fun k => A i m * (B m k * C k j)) N) N := by
    apply sumInt_ext; intro m _
    rw [← sumInt_mul_left]
  rw [h1, h2, sumInt_swap]

theorem matMulInt_id_left (N : Nat) (A : Nat → Nat → Int) (i j : Nat) (hi : i < N) :
    matMulInt N idMatInt A i j = A i j := by
  unfold matMulInt idMatInt
  have h : sumInt (fun k => (if i == k then (1 : Int) else 0) * A k j) N =
           sumInt (fun k => if i == k then A i j else 0) N := by
    apply sumInt_ext; intro k _
    by_cases hik : i = k
    · subst hik; simp
    · simp [beq_false_of_ne hik]
  rw [h, sumInt_ite_eq_symm i (A i j) N]
  simp [hi]

/-- Swap two indices `k` and `r`. -/
@[expose] def swapIdx (k r i : Nat) : Nat :=
  if i == k then r else if i == r then k else i

theorem swapIdx_invol (k r i : Nat) : swapIdx k r (swapIdx k r i) = i := by
  unfold swapIdx
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : i = r
    · subst h2; simp
    · simp [beq_false_of_ne (Ne.symm h2)]
  · by_cases h2 : i = r
    · subst h2; simp [beq_false_of_ne h1]
    · simp [beq_false_of_ne h1, beq_false_of_ne h2]

theorem swapIdx_lt {N k r i : Nat} (hk : k < N) (hr : r < N) (hi : i < N) :
    swapIdx k r i < N := by
  unfold swapIdx; split
  · exact hr
  · split
    · exact hk
    · exact hi

theorem sumInt_swapIdx (N k r : Nat) (hk : k < N) (hr : r < N) (f : Nat → Int) :
    sumInt (fun m => f (swapIdx k r m)) N = sumInt f N := by
  by_cases hkr : k = r
  · subst hkr
    apply sumInt_ext; intro m _
    unfold swapIdx; split <;> simp_all
  · have hdiff : sumInt (fun m => f (swapIdx k r m) - f m) N = 0 := by
      have hrewrite :
          sumInt (fun m => f (swapIdx k r m) - f m) N =
          sumInt (fun m => (if m == k then f r - f k else 0) +
                           (if m == r then f k - f r else 0)) N := by
        apply sumInt_ext; intro m _
        unfold swapIdx
        by_cases h1 : m = k
        · subst h1; simp [beq_false_of_ne hkr]
        · by_cases h2 : m = r
          · subst h2; simp [beq_false_of_ne h1]
          · simp [beq_false_of_ne h1, beq_false_of_ne h2]
      rw [hrewrite, sumInt_add_fn, sumInt_ite_eq k (f r - f k) N, sumInt_ite_eq r (f k - f r) N]
      simp [hk, hr]; omega
    rw [sumInt_sub_fn] at hdiff
    omega

/-- Product of `f 0 * f 1 * ... * f (m - 1)` in `Int`. -/
@[expose] def prodInt (f : Nat → Int) : Nat → Int
  | 0 => 1
  | m + 1 => prodInt f m * f m

theorem prodInt_odd (f : Nat → Int) (m : Nat) (h : ∀ j, j < m → f j % 2 = 1) :
    prodInt f m % 2 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold prodInt
    exact int_mul_emod2_odd_odd _ _ (ih (fun j hj => h j (by omega))) (h m (by omega))

/-- Product of `f j` over `j < m` skipping index `skip`. -/
@[expose] def prodIntSkip (f : Nat → Int) (skip : Nat) : Nat → Int
  | 0 => 1
  | m + 1 => prodIntSkip f skip m * (if m == skip then 1 else f m)

theorem prodIntSkip_eq_prodInt (f : Nat → Int) (skip : Nat) :
    ∀ r, r ≤ skip → prodIntSkip f skip r = prodInt f r := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ihr =>
    unfold prodIntSkip prodInt
    have hne : (r == skip) = false := beq_false_of_ne (by omega)
    rw [ihr (by omega), hne]; rfl

theorem prodIntSkip_mul (f : Nat → Int) (skip : Nat) :
    ∀ m, skip < m → prodIntSkip f skip m * f skip = prodInt f m := by
  intro m hlt
  induction m with
  | zero => omega
  | succ m ih =>
    unfold prodIntSkip prodInt
    by_cases hms : m = skip
    · subst hms
      simp only [beq_self_eq_true, ↓reduceIte, Int.mul_one]
      rw [prodIntSkip_eq_prodInt f m m (Nat.le_refl m)]
    · have hne : (m == skip) = false := beq_false_of_ne hms
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hprev := ih (by omega)
      calc prodIntSkip f skip m * f m * f skip
          = (prodIntSkip f skip m * f skip) * f m := by ac_rfl
        _ = prodInt f m * f m := by rw [hprev]

/-- **Odd-Pivot Integral Matrix Inversion Lemma (Zero Mathlib):**
    Any $N \times N$ integer matrix $A$ that is invertible modulo 2 (admitting $U$ with
    $U A \equiv I \pmod 2$) admits an exact integer matrix $B$ and an ODD integer scalar $\Delta$
    ($\Delta \equiv 1 \pmod 2$, hence $\Delta \ne 0$) satisfying $B A = \Delta I$ over $\mathbb{Z}$! -/
theorem odd_mod2_inv_matrix_integral_inv (N : Nat) (A U0 : Nat → Nat → Int)
    (hU0 : ∀ i, i < N → ∀ j, j < N → (matMulInt N U0 A i j - idMatInt i j) % 2 = 0) :
    ∃ (B : Nat → Nat → Int) (Δ : Int), Δ % 2 = 1 ∧
      ∀ i, i < N → ∀ j, j < N → matMulInt N B A i j = if i == j then Δ else 0 := by
  have hdiag : ∀ k, k ≤ N →
      ∃ (L R U : Nat → Nat → Int),
        (∀ i, i < N → ∀ j, j < N → matMulInt N R A i j = L i j) ∧
        (∀ c, c < k → L c c % 2 = 1 ∧ ∀ r, r < N → r ≠ c → L r c = 0) ∧
        (∀ i, i < N → ∀ j, j < N → (matMulInt N U L i j - idMatInt i j) % 2 = 0) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨A, idMatInt, U0, ?_, ?_, hU0⟩
      · intro i hi j _; exact matMulInt_id_left N A i j hi
      · intro c hc; omega
    | succ k ih =>
      rcases ih (by omega) with ⟨L, R, U, hRA, hCol, hUL⟩
      have hpiv_exists : ∃ r, k ≤ r ∧ r < N ∧ L r k % 2 = 1 := by
        by_cases hex : ∃ r, k ≤ r ∧ r < N ∧ L r k % 2 = 1
        · exact hex
        · exfalso
          have heven_lo : ∀ r, k ≤ r → r < N → L r k % 2 = 0 := by
            intro r hrk hrN
            have h : L r k % 2 = 0 ∨ L r k % 2 = 1 := by omega
            rcases h with h0 | h1
            · exact h0
            · exact absurd ⟨r, hrk, hrN, h1⟩ hex
          let v : Nat → Int := fun c => if c < k then L c k else if c == k then 1 else 0
          have hLv_even : ∀ r, r < N → sumInt (fun c => L r c * v c) N % 2 = 0 := by
            intro r hrN
            by_cases hrk : r < k
            · have hsum : sumInt (fun c => L r c * v c) N =
                          sumInt (fun c => (if c == r then L r r * L r k else 0) +
                                           (if c == k then L r k else 0)) N := by
                apply sumInt_ext; intro c hc
                dsimp only [v]
                by_cases hcr : c = r
                · rw [hcr]
                  have hne : (r == k) = false := beq_false_of_ne (by omega)
                  simp [hrk, hne]
                · by_cases hck : c = k
                  · rw [hck]
                    have hlt : ¬(k < k) := by omega
                    have hner : (k == r) = false := beq_false_of_ne (by omega)
                    simp [hlt, hner]
                  · by_cases hclt : c < k
                    · have hz := (hCol c hclt).2 r hrN (by omega)
                      simp [hclt, hz, beq_false_of_ne hcr, beq_false_of_ne hck]
                    · simp [hclt, beq_false_of_ne hcr, beq_false_of_ne hck]
              rw [hsum, sumInt_add_fn, sumInt_ite_eq r _ N, sumInt_ite_eq k _ N]
              simp only [hrN, show k < N by omega, ↓reduceIte]
              have hm := int_mul_emod2_odd_left (L r r) (L r k) (hCol r hrk).1
              omega
            · have hsum : sumInt (fun c => L r c * v c) N =
                          sumInt (fun c => if c == k then L r k else 0) N := by
                apply sumInt_ext; intro c hc
                dsimp only [v]
                by_cases hclt : c < k
                · have hz := (hCol c hclt).2 r hrN (by omega)
                  simp [hclt, hz, beq_false_of_ne (by omega : c ≠ k)]
                · by_cases hck : c = k
                  · rw [hck]; simp
                  · simp [hclt, beq_false_of_ne hck]
              rw [hsum, sumInt_ite_eq k (L r k) N]
              simp only [show k < N by omega, ↓reduceIte]
              exact heven_lo r (by omega) hrN
          have h0 : sumInt (fun r => U k r * sumInt (fun c => L r c * v c) N) N % 2 = 0 := by
            have hzero := sumInt_emod2_congr
              (fun r => U k r * sumInt (fun c => L r c * v c) N)
              (fun _ => 0) N (fun r hr => by
                rw [Int.mul_comm]
                exact int_mul_emod2_even _ (U k r) (hLv_even r hr))
            rw [hzero, sumInt_zero]; rfl
          have h1 : sumInt (fun r => U k r * sumInt (fun c => L r c * v c) N) N % 2 = 1 := by
            have hrearr :
                sumInt (fun r => U k r * sumInt (fun c => L r c * v c) N) N =
                sumInt (fun c => matMulInt N U L k c * v c) N := by
              have ha : sumInt (fun r => U k r * sumInt (fun c => L r c * v c) N) N =
                        sumInt (fun r => sumInt (fun c => U k r * L r c * v c) N) N := by
                apply sumInt_ext; intro r _
                rw [← sumInt_mul_left]
                apply sumInt_ext; intro c _; rw [Int.mul_assoc]
              rw [ha, sumInt_swap]
              apply sumInt_ext; intro c _
              unfold matMulInt; rw [← sumInt_mul_right]
            rw [hrearr]
            have hcongr :
                sumInt (fun c => matMulInt N U L k c * v c) N % 2 =
                sumInt (fun c => idMatInt k c * v c) N % 2 := by
              apply sumInt_emod2_congr; intro c hc
              have hd := hUL k (by omega) c hc
              have hdiff : (matMulInt N U L k c * v c - idMatInt k c * v c) % 2 = 0 := by
                rw [← Int.sub_mul]
                exact int_mul_emod2_even _ (v c) hd
              omega
            rw [hcongr]
            have hvk : sumInt (fun c => idMatInt k c * v c) N = v k := by
              unfold idMatInt
              have he : sumInt (fun c => (if k == c then (1 : Int) else 0) * v c) N =
                        sumInt (fun c => if k == c then v k else 0) N := by
                apply sumInt_ext; intro c _
                by_cases hkc : k = c
                · rw [hkc]; simp
                · simp [beq_false_of_ne hkc]
              rw [he, sumInt_ite_eq_symm k (v k) N]
              simp [show k < N by omega]
            rw [hvk]
            have hlt : ¬(k < k) := by omega
            simp [v, hlt]
          omega
      rcases hpiv_exists with ⟨r, hrk, hrN, hrOdd⟩
      let L1 : Nat → Nat → Int := fun i j => L (swapIdx k r i) j
      let R1 : Nat → Nat → Int := fun i j => R (swapIdx k r i) j
      let U1 : Nat → Nat → Int := fun i j => U i (swapIdx k r j)
      have hRA1 : ∀ i, i < N → ∀ j, j < N → matMulInt N R1 A i j = L1 i j := by
        intro i hi j hj
        exact hRA (swapIdx k r i) (swapIdx_lt (by omega) hrN hi) j hj
      have hUL1 : ∀ i, i < N → ∀ j, j < N → (matMulInt N U1 L1 i j - idMatInt i j) % 2 = 0 := by
        intro i hi j hj
        have hmul : matMulInt N U1 L1 i j = matMulInt N U L i j := by
          unfold matMulInt
          exact sumInt_swapIdx N k r (by omega) hrN (fun m => U i m * L m j)
        rw [hmul]; exact hUL i hi j hj
      have hpOdd : L1 k k % 2 = 1 := by
        dsimp only [L1, swapIdx]; simp [hrOdd]
      have hCol1 : ∀ c, c < k → L1 c c % 2 = 1 ∧ ∀ i, i < N → i ≠ c → L1 i c = 0 := by
        intro c hc
        have hsc : swapIdx k r c = c := by
          unfold swapIdx; simp [beq_false_of_ne (by omega : c ≠ k), beq_false_of_ne (by omega : c ≠ r)]
        refine ⟨by dsimp only [L1]; rw [hsc]; exact (hCol c hc).1, ?_⟩
        intro i hi hic
        dsimp only [L1]
        have hsne : swapIdx k r i ≠ c := by
          intro heq
          have h1 := congrArg (swapIdx k r) heq
          rw [swapIdx_invol, hsc] at h1
          exact hic h1
        exact (hCol c hc).2 (swapIdx k r i) (swapIdx_lt (by omega) hrN hi) hsne
      let p := L1 k k
      let L2 : Nat → Nat → Int := fun i j =>
        if i == k then L1 k j else p * L1 i j - L1 i k * L1 k j
      let R2 : Nat → Nat → Int := fun i j =>
        if i == k then R1 k j else p * R1 i j - L1 i k * R1 k j
      let U2 : Nat → Nat → Int := fun i j =>
        if j == k then sumInt (fun m => if m == k then U1 i k else U1 i m * L1 m k) N
        else U1 i j
      refine ⟨L2, R2, U2, ?_, ?_, ?_⟩
      · intro i hi j hj
        unfold matMulInt
        dsimp only [L2, R2]
        by_cases hik : i = k
        · rw [hik]
          simp only [beq_self_eq_true, ↓reduceIte]
          exact hRA1 k (by omega) j hj
        · have hne : (i == k) = false := beq_false_of_ne hik
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          have hlin : sumInt (fun m => (p * R1 i m - L1 i k * R1 k m) * A m j) N =
                      p * matMulInt N R1 A i j - L1 i k * matMulInt N R1 A k j := by
            unfold matMulInt
            rw [← sumInt_mul_left, ← sumInt_mul_left, ← sumInt_sub_fn]
            apply sumInt_ext; intro m _
            rw [Int.sub_mul, Int.mul_assoc, Int.mul_assoc]
          rw [hlin, hRA1 i hi j hj, hRA1 k (by omega) j hj]
      · intro c hc
        by_cases hck : c = k
        · rw [hck]
          refine ⟨by dsimp only [L2]; simp [hpOdd], ?_⟩
          intro i _ hik
          dsimp only [L2, p]
          simp only [beq_false_of_ne hik, Bool.false_eq_true, ↓reduceIte]
          rw [Int.mul_comm (L1 k k) (L1 i k)]; omega
        · have hclt : c < k := by omega
          rcases hCol1 c hclt with ⟨hodd_c, hzero_c⟩
          have hne_ck : (c == k) = false := beq_false_of_ne hck
          have hlkc : L1 k c = 0 := hzero_c k (by omega) (by omega)
          refine ⟨?_, ?_⟩
          · dsimp only [L2, p]
            simp only [hne_ck, Bool.false_eq_true, ↓reduceIte, hlkc, Int.mul_zero, Int.sub_zero]
            exact int_mul_emod2_odd_odd (L1 k k) (L1 c c) hpOdd hodd_c
          · intro i hi hic
            dsimp only [L2]
            by_cases hik : i = k
            · rw [hik]; simp [hlkc]
            · simp only [beq_false_of_ne hik, Bool.false_eq_true, ↓reduceIte, hlkc,
                         hzero_c i hi hic, Int.mul_zero, Int.sub_zero]
      · intro i hi j hj
        have hstep : (matMulInt N U2 L2 i j - matMulInt N U1 L1 i j) % 2 = 0 := by
          unfold matMulInt
          have hexp :
              sumInt (fun m => U2 i m * L2 m j) N =
              sumInt (fun m => if m == k then U1 i k * L1 k j
                               else U1 i m * (L1 m k * L1 k j) + U1 i m * (p * L1 m j - L1 m k * L1 k j)) N := by
            have hsplit_u2 :
                sumInt (fun m => U2 i m * L2 m j) N =
                U2 i k * L1 k j + sumInt (fun m => if m == k then 0 else U1 i m * (p * L1 m j - L1 m k * L1 k j)) N := by
              have ha :
                  sumInt (fun m => U2 i m * L2 m j) N =
                  sumInt (fun m => (if m == k then U2 i k * L1 k j else 0) +
                                   (if m == k then 0 else U1 i m * (p * L1 m j - L1 m k * L1 k j))) N := by
                apply sumInt_ext; intro m _
                dsimp only [U2, L2]
                by_cases hmk : m = k
                · rw [hmk]; simp
                · simp [beq_false_of_ne hmk]
              rw [ha, sumInt_add_fn, sumInt_ite_eq k (U2 i k * L1 k j) N]
              simp [show k < N by omega]
            rw [hsplit_u2]
            have hu2k : U2 i k * L1 k j =
                sumInt (fun m => if m == k then U1 i k * L1 k j else U1 i m * (L1 m k * L1 k j)) N := by
              dsimp only [U2]
              simp only [beq_self_eq_true, ↓reduceIte]
              rw [← sumInt_mul_right]
              apply sumInt_ext; intro m _
              split
              · rfl
              · rw [Int.mul_assoc]
            rw [hu2k, ← sumInt_add_fn]
            apply sumInt_ext; intro m _
            split <;> omega
          rw [hexp, ← sumInt_sub_fn]
          have hmod0 := sumInt_emod2_congr
            (fun m => (if m == k then U1 i k * L1 k j
                       else U1 i m * (L1 m k * L1 k j) + U1 i m * (p * L1 m j - L1 m k * L1 k j)) -
                      U1 i m * L1 m j)
            (fun _ => 0) N (fun m _ => by
              by_cases hmk : m = k
              · rw [hmk]; simp
              · simp only [beq_false_of_ne hmk, Bool.false_eq_true, ↓reduceIte]
                have hsimp :
                    U1 i m * (L1 m k * L1 k j) + U1 i m * (p * L1 m j - L1 m k * L1 k j) - U1 i m * L1 m j =
                    (p - 1) * (U1 i m * L1 m j) := by
                  rw [← Int.mul_add]
                  have hc : L1 m k * L1 k j + (p * L1 m j - L1 m k * L1 k j) = p * L1 m j := by omega
                  rw [hc, show U1 i m * (p * L1 m j) = p * (U1 i m * L1 m j) by ac_rfl,
                      Int.sub_mul, Int.one_mul]
                rw [hsimp]
                exact int_mul_emod2_even (p - 1) (U1 i m * L1 m j) (by dsimp only [p]; omega))
          rw [hmod0, sumInt_zero]; rfl
        have hbase := hUL1 i hi j hj
        omega
  rcases hdiag N (Nat.le_refl N) with ⟨L, R, _, hRA, hCol, _⟩
  let d : Nat → Int := fun i => L i i
  let Δ : Int := prodInt d N
  let B : Nat → Nat → Int := fun i m => prodIntSkip d i N * R i m
  refine ⟨B, Δ, prodInt_odd d N (fun j hj => (hCol j hj).1), ?_⟩
  intro i hi j hj
  unfold matMulInt
  dsimp only [B]
  have hpull : sumInt (fun m => (prodIntSkip d i N * R i m) * A m j) N =
               prodIntSkip d i N * matMulInt N R A i j := by
    unfold matMulInt
    rw [← sumInt_mul_left]
    apply sumInt_ext; intro m _; rw [Int.mul_assoc]
  rw [hpull, hRA i hi j hj]
  by_cases hij : i = j
  · subst hij
    simp only [beq_self_eq_true, ↓reduceIte]
    exact prodIntSkip_mul d i N hi
  · simp only [beq_false_of_ne hij, Bool.false_eq_true, ↓reduceIte]
    rw [(hCol j hj).2 i hi hij, Int.mul_zero]

/-! ### Linking `cdMulCoordGamma` to `leftMulMat` and `rightMulMat` -/

theorem leftMulMat_apply (n flipMask : Nat) (x y : Nat → Int) (t : Nat) (ht : t < 2 ^ n) :
    sumInt (fun j => leftMulMat n flipMask x t j * y j) (2 ^ n) =
      cdMulCoordGamma n flipMask x y t := by
  unfold leftMulMat cdMulCoordGamma
  rw [sumInt_xor_bijection n (fun j => cdSignGamma n flipMask (t ^^^ j) j * x (t ^^^ j) * y j) t ht]
  apply sumInt_ext; intro a _
  have h1 : t ^^^ (a ^^^ t) = a := by
    rw [Nat.xor_comm t (a ^^^ t), xor_sub_self_cancel]
  rw [h1]

theorem rightMulMat_apply (n flipMask : Nat) (x y : Nat → Int) (t : Nat) :
    sumInt (fun j => rightMulMat n flipMask x t j * y j) (2 ^ n) =
      cdMulCoordGamma n flipMask y x t := by
  unfold rightMulMat cdMulCoordGamma
  apply sumInt_ext; intro j _
  rw [Nat.xor_comm t j]
  ac_rfl

theorem leftMulMat_sq_mod2 (n flipMask : Nat) (x : Nat → Int) (hx : oddCoordSum n x)
    (i j : Nat) (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    (matMulInt (2 ^ n) (leftMulMat n flipMask x) (leftMulMat n flipMask x) i j -
      idMatInt i j) % 2 = 0 := by
  have hinv := (twisted_frobenius_mod2_involution n (cdSignGamma n flipMask)
    (fun a b => cdSignGamma_val_pm1 n flipMask a b) x hx).1 (basisVec j) i hi
  have hmul : matMulInt (2 ^ n) (leftMulMat n flipMask x) (leftMulMat n flipMask x) i j =
              cdMulCoordGamma n flipMask x (cdMulCoordGamma n flipMask x (basisVec j)) i := by
    rw [← leftMulMat_apply n flipMask x _ i hi]
    unfold matMulInt
    apply sumInt_ext; intro k hk
    congr 1
    rw [← leftMulMat_apply n flipMask x (basisVec j) k hk]
    unfold basisVec
    have hsingle : sumInt (fun m => leftMulMat n flipMask x k m * (if m == j then 1 else 0)) (2 ^ n) =
                   sumInt (fun m => if m == j then leftMulMat n flipMask x k j else 0) (2 ^ n) := by
      apply sumInt_ext; intro m _
      by_cases hmj : m = j
      · subst hmj; simp
      · simp [beq_false_of_ne hmj]
    rw [hsingle, sumInt_ite_eq j _ (2 ^ n)]
    simp [hj]
  have hid : idMatInt i j = basisVec j i := rfl
  rw [hmul, hid]
  exact hinv

theorem rightMulMat_sq_mod2 (n flipMask : Nat) (x : Nat → Int) (hx : oddCoordSum n x)
    (i j : Nat) (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    (matMulInt (2 ^ n) (rightMulMat n flipMask x) (rightMulMat n flipMask x) i j -
      idMatInt i j) % 2 = 0 := by
  have hinv := (twisted_frobenius_mod2_involution n (cdSignGamma n flipMask)
    (fun a b => cdSignGamma_val_pm1 n flipMask a b) x hx).2.1 (basisVec j) i hi
  have hmul : matMulInt (2 ^ n) (rightMulMat n flipMask x) (rightMulMat n flipMask x) i j =
              cdMulCoordGamma n flipMask (cdMulCoordGamma n flipMask (basisVec j) x) x i := by
    rw [← rightMulMat_apply n flipMask x _ i]
    unfold matMulInt
    apply sumInt_ext; intro k _
    congr 1
    rw [← rightMulMat_apply n flipMask x (basisVec j) k]
    unfold basisVec
    have hsingle : sumInt (fun m => rightMulMat n flipMask x k m * (if m == j then 1 else 0)) (2 ^ n) =
                   sumInt (fun m => if m == j then rightMulMat n flipMask x k j else 0) (2 ^ n) := by
      apply sumInt_ext; intro m _
      by_cases hmj : m = j
      · subst hmj; simp
      · simp [beq_false_of_ne hmj]
    rw [hsingle, sumInt_ite_eq j _ (2 ^ n)]
    simp [hj]
  have hid : idMatInt i j = basisVec j i := rfl
  rw [hmul, hid]
  exact hinv

/-- **Theorem T6b (Universal All-$n$, All-Signature Odd-Parity Zero-Divisor Exclusion):**
    For EVERY $n \in \mathbb{N}$, EVERY signature `flipMask`, and EVERY $x \in \mathbb{Z}^{2^n}$
    with odd coordinate sum $\sum_{a < 2^n} x_a \equiv 1 \pmod 2$:
    1. $L_x$ admits an exact integral left-inverse $B_L L_x = \Delta_L I$ with $\Delta_L$ odd
       (hence invertible over $\mathbb{Q}$, $\mathbb{R}$, $\mathbb{C}$).
    2. $R_x$ admits an exact integral left-inverse $B_R R_x = \Delta_R I$ with $\Delta_R$ odd.
    3. $x$ has trivial left and right annihilators over $\mathbb{Z}$ (and every $\mathbb{Q}$-extension). -/
theorem odd_parity_zero_divisor_exclusion_all_n (n flipMask : Nat) (x : Nat → Int)
    (hx : oddCoordSum n x) :
    (∃ (B : Nat → Nat → Int) (Δ : Int), Δ % 2 = 1 ∧
      ∀ i, i < 2 ^ n → ∀ j, j < 2 ^ n →
        matMulInt (2 ^ n) B (leftMulMat n flipMask x) i j = if i == j then Δ else 0) ∧
    (∃ (B : Nat → Nat → Int) (Δ : Int), Δ % 2 = 1 ∧
      ∀ i, i < 2 ^ n → ∀ j, j < 2 ^ n →
        matMulInt (2 ^ n) B (rightMulMat n flipMask x) i j = if i == j then Δ else 0) ∧
    (∀ y, (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask x y t = 0) →
      ∀ t, t < 2 ^ n → y t = 0) ∧
    (∀ y, (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask y x t = 0) →
      ∀ t, t < 2 ^ n → y t = 0) := by
  have hL := odd_mod2_inv_matrix_integral_inv (2 ^ n)
    (leftMulMat n flipMask x) (leftMulMat n flipMask x)
    (fun i hi j hj => leftMulMat_sq_mod2 n flipMask x hx i j hi hj)
  have hR := odd_mod2_inv_matrix_integral_inv (2 ^ n)
    (rightMulMat n flipMask x) (rightMulMat n flipMask x)
    (fun i hi j hj => rightMulMat_sq_mod2 n flipMask x hx i j hi hj)
  have hker_from_inv : ∀ (A : Nat → Nat → Int),
      (∃ (B : Nat → Nat → Int) (Δ : Int), Δ % 2 = 1 ∧
        ∀ i, i < 2 ^ n → ∀ j, j < 2 ^ n → matMulInt (2 ^ n) B A i j = if i == j then Δ else 0) →
      ∀ (y : Nat → Int), (∀ t, t < 2 ^ n → sumInt (fun j => A t j * y j) (2 ^ n) = 0) →
        ∀ t, t < 2 ^ n → y t = 0 := by
    intro A ⟨B, Δ, hΔodd, hBA⟩ y hzero t ht
    have hΔne : Δ ≠ 0 := by omega
    have hmul0 : sumInt (fun k => B t k * sumInt (fun j => A k j * y j) (2 ^ n)) (2 ^ n) = 0 := by
      have h := sumInt_ext
        (fun k => B t k * sumInt (fun j => A k j * y j) (2 ^ n))
        (fun _ => 0) (2 ^ n) (fun k hk => by rw [hzero k hk, Int.mul_zero])
      rw [h, sumInt_zero]
    have hrearr :
        sumInt (fun k => B t k * sumInt (fun j => A k j * y j) (2 ^ n)) (2 ^ n) =
        Δ * y t := by
      have ha : sumInt (fun k => B t k * sumInt (fun j => A k j * y j) (2 ^ n)) (2 ^ n) =
                sumInt (fun k => sumInt (fun j => B t k * A k j * y j) (2 ^ n)) (2 ^ n) := by
        apply sumInt_ext; intro k _
        rw [← sumInt_mul_left]
        apply sumInt_ext; intro j _; rw [Int.mul_assoc]
      rw [ha, sumInt_swap]
      have hb : sumInt (fun j => sumInt (fun k => B t k * A k j * y j) (2 ^ n)) (2 ^ n) =
                sumInt (fun j => if t == j then Δ * y t else 0) (2 ^ n) := by
        apply sumInt_ext; intro j hj
        rw [sumInt_mul_right]
        change matMulInt (2 ^ n) B A t j * y j = _
        rw [hBA t ht j hj]
        by_cases htj : t = j
        · subst htj; simp
        · simp [beq_false_of_ne htj]
      rw [hb, sumInt_ite_eq_symm t (Δ * y t) (2 ^ n)]
      simp [ht]
    rw [hrearr] at hmul0
    rcases Int.mul_eq_zero.mp hmul0 with h1 | h2
    · exact absurd h1 hΔne
    · exact h2
  refine ⟨hL, hR, ?_, ?_⟩
  · intro y hy
    exact hker_from_inv (leftMulMat n flipMask x) hL y
      (fun t ht => (leftMulMat_apply n flipMask x y t ht).trans (hy t ht))
  · intro y hy
    exact hker_from_inv (rightMulMat n flipMask x) hR y
      (fun t ht => (rightMulMat_apply n flipMask x y t).trans (hy t ht))

/-! ### Theorem T6c: Universal Odd-Support Unit-Blade Non-Singularity & Parity Conservation -/

theorem sumInt_signedBladeSum_mod2 (n : Nat) (ε : Nat → Int) :
    ∀ S : List Nat, (∀ a ∈ S, a < 2 ^ n) → (∀ a ∈ S, ε a = 1 ∨ ε a = -1) →
      sumInt (signedBladeSum S ε) (2 ^ n) % 2 = (S.length % 2 : Nat) := by
  intro S
  induction S with
  | nil =>
    intro _ _
    simp [signedBladeSum, sumInt_zero]
  | cons a rest ih =>
    intro hlt hpm
    have ha_lt : a < 2 ^ n := hlt a (by simp)
    have ha_pm : ε a = 1 ∨ ε a = -1 := hpm a (by simp)
    have hrest := ih (fun b hb => hlt b (by simp [hb])) (fun b hb => hpm b (by simp [hb]))
    have hsplit : sumInt (signedBladeSum (a :: rest) ε) (2 ^ n) =
                  sumInt (fun t => if t == a then ε a else 0) (2 ^ n) +
                  sumInt (signedBladeSum rest ε) (2 ^ n) := by
      show sumInt (fun t => (if t == a then ε a else 0) + signedBladeSum rest ε t) (2 ^ n) = _
      exact sumInt_add_fn (fun t => if t == a then ε a else 0) (signedBladeSum rest ε) (2 ^ n)
    rw [hsplit, sumInt_ite_eq a (ε a) (2 ^ n)]
    simp only [ha_lt, ↓reduceIte, List.length_cons]
    rcases ha_pm with h1 | h1 <;> rw [h1] <;> omega

/-- **Theorem T6c (Universal Odd-Support Unit-Blade Non-Singularity & Zero-Divisor Parity Conservation):**
    1. For EVERY $n \in \mathbb{N}$, EVERY signature `flipMask`, EVERY odd-length list $S$ of basis
       indices in $[0, 2^n)$, and EVERY sign assignment $\varepsilon : \mathbb{N} \to \{\pm 1\}$
       (including EVERY unit 3-blade $e_i \pm e_j \pm e_k$, 5-blade, 7-blade, ...):
       $x = \sum_{a \in S} \varepsilon(a)\, e_a$ has odd coordinate sum and is strictly
       non-zero-divisor on BOTH left and right in $\mathrm{CD}_n(\gamma)$ (with odd-scalar integral
       inverses $B_L L_x = \Delta_L I$ and $B_R R_x = \Delta_R I$).
    2. Contrapositively (Zero-Divisor Parity Conservation): EVERY integer left or right zero
       divisor $x \in \mathrm{CD}_n(\gamma)$ MUST have EVEN coordinate sum
       $\sum_{a=0}^{2^n-1} x_a \equiv 0 \pmod 2$. -/
theorem odd_support_unit_blades_non_zd_all_n (n flipMask : Nat) :
    (∀ (S : List Nat) (ε : Nat → Int),
      S.length % 2 = 1 →
      (∀ a ∈ S, a < 2 ^ n) →
      (∀ a ∈ S, ε a = 1 ∨ ε a = -1) →
      oddCoordSum n (signedBladeSum S ε) ∧
      (∀ y, (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask (signedBladeSum S ε) y t = 0) →
        ∀ t, t < 2 ^ n → y t = 0) ∧
      (∀ y, (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask y (signedBladeSum S ε) t = 0) →
        ∀ t, t < 2 ^ n → y t = 0)) ∧
    (∀ (x y : Nat → Int),
      (∃ t, t < 2 ^ n ∧ y t ≠ 0) →
      ((∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask x y t = 0) ∨
       (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask y x t = 0)) →
      sumInt x (2 ^ n) % 2 = 0) := by
  refine ⟨?_, ?_⟩
  · intro S ε hodd hlt hpm
    have hx : oddCoordSum n (signedBladeSum S ε) := by
      unfold oddCoordSum
      rw [sumInt_signedBladeSum_mod2 n ε S hlt hpm, hodd]; rfl
    rcases odd_parity_zero_divisor_exclusion_all_n n flipMask (signedBladeSum S ε) hx with
      ⟨_, _, hL, hR⟩
    exact ⟨hx, hL, hR⟩
  · intro x y ⟨t0, ht0, hy0⟩ hzd
    have hcases : sumInt x (2 ^ n) % 2 = 0 ∨ sumInt x (2 ^ n) % 2 = 1 := by omega
    rcases hcases with hev | hodd
    · exact hev
    · exfalso
      rcases odd_parity_zero_divisor_exclusion_all_n n flipMask x hodd with ⟨_, _, hL, hR⟩
      rcases hzd with hleft | hright
      · exact hy0 (hL y hleft t0 ht0)
      · exact hy0 (hR y hright t0 ht0)

end

end CDTerrace
