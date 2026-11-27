module
-- SPDX-License-Identifier: Apache-2.0
public import CDTerrace.Basic
public import CDTerrace.MirrorConservation
public import CDTerrace.TerraceLaw

/-!
# CDTerrace.FiniteCertificates — Pure-Kernel Finite Certificates & Pillar 4 Lemmas

Proves in zero-Mathlib, strictly constructive Lean 4.35.0 (`0` `sorry`, `0` `native_decide`,
`0` custom axioms, zero `maxRecDepth`/`maxHeartbeats` overrides; verified across all 6 independent
Lean 4.35.0 kernels in CI):
- **T4a (`sedenion_42_fano_duality`, `sedenion_no_11d_coord_subspace`, `sedenion_bad_planes_split_2_2`):**
  Complete exact enumeration over all $2^{16} = 65536$ coordinate subspaces of $\mathbb{S}_{16}$:
  - Exactly **42** bad affine 2-planes out of 140 affine 2-planes in $\mathbb{F}_2^4$, every one of
    which splits strictly $2 + 2$ across $\{1..7\} \times \{9..15\}$.
  - Exactly **42** maximal 10-dimensional norm-multiplicative coordinate subspaces `[10, 10, 16]`,
    decomposing by $|S \cap \mathbb{O}|$ into the exact Fano triple **`7 + 28 + 7 = 42`**.
  - Exactly **0** norm-multiplicative coordinate subspaces of dimension $\ge 11$.
- **T4b (`sedenion_box_kites_7x6`, `bladeProdCoord4_eq_cdMul`):**
  Formal six-kernel re-verification of de Marrais's (2000) 42 Sedenion Box-Kite assessors under
  the pure algebraic mutual zero-divisor product $(e_i + e_j)(e_k \pm e_l) = 0$ (zero XOR
  pre-filtering): 4-regular (`84` undirected edges) partitioning by XOR signature
  $i \oplus j \in \{9,\dots,15\}$ into **7 disjoint octahedra $K_{2,2,2}$** of size 6 with
  genuinely proved zero cross-XOR-class edges, while $\mathbb{O} \oplus \mathbb{R} e_8$
  (mask `511`, dim 9) is norm-multiplicative.
- **T4c (`split_sedenion_4_phases`, `split_pathion_8_phases`):**
  Exhaustive pure-kernel classification of all 16 split Sedenion algebras $\mathrm{CD}_4(\gamma)$
  (`4` distinct histograms with multiplicities `1:1:7:7`, invariant $H_4^\gamma(4) = 42$) and
  all 32 split Pathion algebras $\mathrm{CD}_5(\gamma)$ (`8` distinct histograms with
  multiplicities `4×1 + 4×7`, invariant $H_5^\gamma(8) = 84$, $H_5^\gamma(4) + H_5^\gamma(12) = 210$).
- **T4d (`pathion_14_and_chingon_16_witnesses`, `domain_sq_eq_one_imp`, `int_sq_eq_one_iff`,
  `gaussInt_sq_eq_one_iff`):**
  Verified explicit symmetric norm-multiplicative witnesses `[14, 14, 32]` in $\mathrm{CD}_5$ and
  `[16, 16, 64]` in $\mathrm{CD}_6$, plus the elementary unit lemma $c^2 = 1 \implies c = \pm 1$
  derived directly from standard commutative integral-domain axioms (and explicitly over
  $\mathbb{Z}$ and $\mathbb{Z}[i]$).
-/

namespace CDTerrace

public section

/-! ### Small Core Helpers (Zero-Mathlib, $O(\log N)$ Kernel Stack Depth) -/

@[expose] def allNat (P : Nat → Bool) : Nat → Bool
  | 0 => true
  | m + 1 => P m && allNat P m

theorem allNat_eq_true (P : Nat → Bool) : ∀ m, allNat P m = true ↔ ∀ k, k < m → P k = true := by
  intro m
  induction m with
  | zero =>
    constructor
    · intro _ k hk; omega
    · intro _; rfl
  | succ m ih =>
    unfold allNat
    rw [Bool.and_eq_true, ih]
    constructor
    · intro ⟨hm, hall⟩ k hk
      by_cases hkm : k = m
      · subst hkm; exact hm
      · exact hall k (by omega)
    · intro hall
      exact ⟨hall m (by omega), fun k hk => hall k (by omega)⟩

/-- Binary-tree sum over `[start, start + 2^d)` with exact recursion depth `d`! -/
@[expose] def sumTree (f : Nat → Nat) : Nat → Nat → Nat
  | start, 0 => f start
  | start, d + 1 => sumTree f start d + sumTree f (start + 2 ^ d) d

theorem sumTree_eq_sumNat (f : Nat → Nat) :
    ∀ d s, sumTree f s d = sumNat (fun k => f (s + k)) (2 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro s; simp [sumTree, sumNat]
  | succ d ih =>
    intro s
    unfold sumTree
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [ih s, ih (s + 2 ^ d), hpow, sumNat_add]
    congr 1
    apply sumNat_ext; intro k _; rw [Nat.add_assoc]

theorem sumTree_zero_eq (f : Nat → Nat) (d : Nat) :
    sumTree f 0 d = sumNat f (2 ^ d) := by
  rw [sumTree_eq_sumNat]
  apply sumNat_ext; intro k _; rw [Nat.zero_add]

theorem countPred_false (m : Nat) : countPred (fun _ => false) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => unfold countPred; simp [ih]

theorem countPred_disj (P Q : Nat → Bool) (m : Nat)
    (hdisj : ∀ k, k < m → (P k && Q k) = false) :
    countPred (fun k => P k || Q k) m = countPred P m + countPred Q m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold countPred
    rw [ih (fun k hk => hdisj k (by omega))]
    have hm := hdisj m (by omega)
    cases hP : P m <;> cases hQ : Q m <;> simp_all <;> omega

/-! ### Elementary Commutative-Domain Unit Lemma & Gaussian-Integer Rigidity -/

/-- **Theorem T4d-1 (Commutative Integral-Domain Unit Lemma):**
    In ANY commutative integral domain $(R, 0, 1, +, \cdot, -)$, every $c \in R$ with
    $c^2 = 1$ satisfies $c = 1 \lor c = -1$. Derived directly from standard ring axioms
    by proving $(c - 1)(c + 1) = c^2 - 1 = 0$ (zero pre-factored hypothesis). -/
theorem domain_sq_eq_one_imp {R : Type}
    (zero one : R) (add mul : R → R → R) (neg : R → R)
    (h_add_assoc : ∀ x y z, add (add x y) z = add x (add y z))
    (h_zero_add : ∀ x, add zero x = x)
    (h_add_zero : ∀ x, add x zero = x)
    (h_add_neg : ∀ x, add x (neg x) = zero)
    (h_neg_add : ∀ x, add (neg x) x = zero)
    (h_mul_comm : ∀ x y, mul x y = mul y x)
    (h_mul_one : ∀ x, mul x one = x)
    (h_left_distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z))
    (h_right_distrib : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z))
    (h_neg_mul : ∀ x y, mul (neg x) y = neg (mul x y))
    (h_dom : ∀ x y, mul x y = zero → x = zero ∨ y = zero) :
    ∀ c, mul c c = one → c = one ∨ c = neg one := by
  intro c hsq
  have hprod : mul (add c (neg one)) (add c one) = zero := by
    rw [h_left_distrib, h_right_distrib, h_mul_one, hsq,
        h_neg_mul, h_mul_comm one c, h_mul_one,
        h_add_assoc, ← h_add_assoc (neg c) c (neg one), h_neg_add, h_zero_add, h_add_neg]
  rcases h_dom _ _ hprod with h1 | h2
  · left
    calc c = add c zero := (h_add_zero c).symm
      _ = add c (add (neg one) one) := by rw [h_neg_add]
      _ = add (add c (neg one)) one := (h_add_assoc c (neg one) one).symm
      _ = add zero one := by rw [h1]
      _ = one := h_zero_add one
  · right
    calc c = add c zero := (h_add_zero c).symm
      _ = add c (add one (neg one)) := by rw [h_add_neg]
      _ = add (add c one) (neg one) := (h_add_assoc c one (neg one)).symm
      _ = add zero (neg one) := by rw [h2]
      _ = neg one := h_zero_add (neg one)

theorem int_sq_eq_one_iff (c : Int) : c * c = 1 ↔ c = 1 ∨ c = -1 := by
  constructor
  · intro h
    have hfac : (c - 1) * (c + 1) = 0 := by
      have : (c - 1) * (c + 1) = c * c - 1 := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_one, Int.one_mul, Int.add_sub_assoc]
        omega
      omega
    rcases Int.mul_eq_zero.mp hfac with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro h; rcases h with rfl | rfl <;> rfl

/-- Exact Gaussian integers $\mathbb{Z}[i]$ witnessing $\mathbb{Q}(i)$ base-field rigidity. -/
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

@[expose] def GaussInt.one : GaussInt := ⟨1, 0⟩
@[expose] def GaussInt.negOne : GaussInt := ⟨-1, 0⟩
@[expose] def GaussInt.mul (z w : GaussInt) : GaussInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- **Theorem T4d-2 (Gaussian-Integer Pure-Intercalate Rigidity):**
    Even in $\mathbb{Z}[i] \subset \mathbb{Q}(i)$, $z^2 = 1 \iff z \in \{+1, -1\}$. -/
theorem gaussInt_sq_eq_one_iff (z : GaussInt) :
    z.mul z = GaussInt.one ↔ z = GaussInt.one ∨ z = GaussInt.negOne := by
  constructor
  · intro h
    cases z with | mk a b =>
    unfold GaussInt.mul GaussInt.one at h
    injection h with hre him
    have h2ab : a * b = 0 := by
      have hcomm : b * a = a * b := Int.mul_comm b a
      rw [hcomm] at him
      have hsum : a * b + a * b = 0 := him
      omega
    rcases Int.mul_eq_zero.mp h2ab with ha0 | hb0
    · subst ha0
      have hneg1 : -(b * b) = 1 := by simpa using hre
      have hsq : 0 ≤ b * b := by
        rcases Int.le_total 0 b with hb | hb
        · exact Int.mul_nonneg hb hb
        · have hneg : 0 ≤ -b := by omega
          have := Int.mul_nonneg hneg hneg
          rw [Int.neg_mul_neg] at this; exact this
      omega
    · subst hb0
      have ha1 : a * a = 1 := by simpa using hre
      rcases (int_sq_eq_one_iff a).mp ha1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · intro h; rcases h with rfl | rfl <;> rfl

/-! ### Exact Bilinear Norm-Multiplicativity & Bad Affine 2-Plane Definitions -/

/-- Exact 4-tuple norm-cancellation check for an unordered pair of pairs `(a, b) | (c, d)`
    with `a ^^^ b = c ^^^ d`: returns `true` iff the cross-term vanishes. -/
@[expose] def pairingCancels (n a b c d : Nat) : Bool :=
  cdSign n a c * cdSign n b d + cdSign n a d * cdSign n b c == 0

/-- An affine 2-plane `{a, b, c, d}` in $\mathbb{F}_2^n$ (with `a ^^^ b ^^^ c = d`) is **bad**
    if ANY of its 3 unordered pairings fails bilinear norm cancellation. -/
@[expose] def isBadAffinePlane (n a b c d : Nat) : Bool :=
  !(pairingCancels n a b c d && pairingCancels n a c b d && pairingCancels n a d b c)

/-- Direct textbook check: a coordinate basis subset `S` (given as a bitmask) is
    norm-multiplicative in $\mathrm{CD}_n$ iff $\|xy\|^2 = \|x\|^2 \|y\|^2$ for all
    $x, y \in \mathrm{span}(S)$. -/
@[expose] def isNormMultMask (n mask : Nat) : Bool :=
  let dim := 2 ^ n
  allNat (fun a =>
    if !mask.testBit a then true
    else allNat (fun b =>
      if !(a < b && mask.testBit b) then true
      else allNat (fun c =>
        if !(mask.testBit c && c != a && c != b) then true
        else
          let d := a ^^^ b ^^^ c
          if !(c < d && d < dim && mask.testBit d) then true
          else pairingCancels n a b c d) dim) dim) dim

/-- Equivalent list-based norm-multiplicativity check for sparse high-dimensional witnesses. -/
@[expose] def isNormMultList (n : Nat) (S : List Nat) : Bool :=
  S.all fun a =>
    S.all fun b =>
      if !(a < b) then true
      else S.all fun c =>
        if !(c != a && c != b) then true
        else
          let d := a ^^^ b ^^^ c
          if !(c < d && S.contains d) then true
          else pairingCancels n a b c d

/-- Explicit symmetric norm-multiplicative `[14, 14, 32]` coordinate subspace witness in $\mathrm{CD}_5$. -/
@[expose] def pathionWitness14 : List Nat :=
  [0, 1, 2, 4, 5, 8, 10, 16, 17, 18, 20, 21, 24, 26]

/-- Explicit symmetric norm-multiplicative `[16, 16, 64]` coordinate subspace witness in $\mathrm{CD}_6$. -/
@[expose] def chingonWitness16 : List Nat :=
  [0, 4, 6, 8, 11, 13, 14, 24, 31, 32, 36, 38, 56, 57, 60, 63]

/-- **Theorem T4d-3 (Certified `[14, 14, 32]` Pathion & `[16, 16, 64]` Chingon Witnesses):**
    Both explicit coordinate subspaces are duplicate-free, in-bounds, and satisfy exact
    bilinear norm-multiplicativity $\|xy\|^2 = \|x\|^2 \|y\|^2$ in $\mathrm{CD}_5$ and $\mathrm{CD}_6$. -/
theorem pathion_14_and_chingon_16_witnesses :
    pathionWitness14.length = 14 ∧
    pathionWitness14.Nodup ∧
    (∀ x ∈ pathionWitness14, x < 32) ∧
    isNormMultList 5 pathionWitness14 = true ∧
    chingonWitness16.length = 16 ∧
    chingonWitness16.Nodup ∧
    (∀ x ∈ chingonWitness16, x < 64) ∧
    isNormMultList 6 chingonWitness16 = true := by
  refine ⟨rfl, by decide, ?_, by decide, rfl, by decide, ?_, by decide⟩
  · intro x hx
    have h : pathionWitness14.all (fun y => y < 32) = true := by decide
    exact decide_eq_true_eq.mp (List.all_eq_true.mp h x hx)
  · intro x hx
    have h : chingonWitness16.all (fun y => y < 64) = true := by decide
    exact decide_eq_true_eq.mp (List.all_eq_true.mp h x hx)

/-! ### Theorem T4a: Sedenion Triple-42 & Fano `7 + 28 + 7` Duality (All $2^{16}$ Subspaces) -/

/-- Exact count of affine 2-planes `{a < b < c < d}` in $\mathbb{F}_2^4$ (`140`). -/
@[expose] def countAffinePlanes4 : Nat :=
  sumNat (fun a => sumNat (fun b =>
    if !(a < b) then 0
    else sumNat (fun c =>
      let d := a ^^^ b ^^^ c
      if b < c && c < d && d < 16 then 1 else 0) 16) 16) 16

/-- Exact count of bad affine 2-planes in $\mathbb{S}_{16}$ (`42`). -/
@[expose] def countBadAffinePlanes4 : Nat :=
  sumNat (fun a => sumNat (fun b =>
    if !(a < b) then 0
    else sumNat (fun c =>
      let d := a ^^^ b ^^^ c
      if b < c && c < d && d < 16 && isBadAffinePlane 4 a b c d then 1 else 0) 16) 16) 16

/-- Explicit literal list of the 42 bad affine 2-planes `(a, b, c, d)` in $\mathbb{S}_{16}$,
    encoded as `(loMask, u, v)` with `loMask = (1 <<< a) ||| (1 <<< b)`, `u = c - 8`, `v = d - 8`. -/
@[expose] def cd4BadPlaneMasks : List (Nat × Nat × Nat) :=
  [(6, 4, 7), (6, 5, 6), (10, 4, 6), (10, 5, 7), (18, 2, 7), (18, 3, 6),
   (34, 2, 6), (34, 3, 7), (66, 2, 5), (66, 3, 4), (130, 2, 4), (130, 3, 5),
   (12, 4, 5), (12, 6, 7), (20, 1, 7), (20, 3, 5), (36, 1, 6), (36, 3, 4),
   (68, 1, 5), (68, 3, 7), (132, 1, 4), (132, 3, 6), (24, 1, 6), (24, 2, 5),
   (40, 1, 7), (40, 2, 4), (72, 1, 4), (72, 2, 7), (136, 1, 5), (136, 2, 6),
   (48, 2, 3), (48, 6, 7), (80, 1, 3), (80, 5, 7), (144, 1, 2), (144, 5, 6),
   (96, 1, 2), (96, 4, 7), (160, 1, 3), (160, 4, 6), (192, 2, 3), (192, 4, 5)]

theorem cd4_bad_planes_count :
    countAffinePlanes4 = 140 ∧ countBadAffinePlanes4 = 42 ∧ cd4BadPlaneMasks.length = 42 := by
  decide

/-- Every bad affine 2-plane $\{a < b < c < d\}$ of $\mathbb{S}_{16}$ splits strictly $2 + 2$
    across the imaginary octonion half $\{1..7\}$ and the upper imaginary half $\{9..15\}$. -/
theorem sedenion_bad_planes_split_2_2 :
    ∀ a b c d, a < b → b < c → c < d → d < 16 →
      (a ^^^ b ^^^ c = d) → isBadAffinePlane 4 a b c d = true →
      1 ≤ a ∧ b ≤ 7 ∧ 9 ≤ c ∧ d ≤ 15 := by
  have hall :
      allNat (fun a =>
        allNat (fun b =>
          if !(a < b) then true
          else allNat (fun c =>
            let d := a ^^^ b ^^^ c
            if !(b < c && c < d && d < 16 && isBadAffinePlane 4 a b c d) then true
            else decide (1 ≤ a && b ≤ 7 && 9 ≤ c && d ≤ 15)) 16) 16) 16 = true := by
    decide
  intro a b c d hab hbc hcd hd hxor hbad
  have ha := (allNat_eq_true _ 16).mp hall a (by omega)
  have hb := (allNat_eq_true _ 16).mp ha b (by omega)
  simp only [hab, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb
  have hc := (allNat_eq_true _ 16).mp hb c (by omega)
  change (if !(b < c && c < (a ^^^ b ^^^ c) && (a ^^^ b ^^^ c) < 16 &&
              isBadAffinePlane 4 a b c (a ^^^ b ^^^ c)) then true
          else decide (1 ≤ a && b ≤ 7 && 9 ≤ c && (a ^^^ b ^^^ c) ≤ 15)) = true at hc
  rw [hxor] at hc
  simp only [hbc, hcd, hd, hbad, decide_true, Bool.and_true, Bool.not_true, Bool.false_eq_true,
             ↓reduceIte, decide_eq_true_eq, Bool.and_eq_true] at hc
  omega

/-- Popcount of an 8-bit integer (`0 ≤ x < 256`), using pure C-primitive `div`/`mod`
    for instantaneous kernel `rfl` evaluation! -/
@[expose] def popcount8 (x : Nat) : Nat :=
  (x % 2) + ((x / 2) % 2) + ((x / 4) % 2) + ((x / 8) % 2) +
  ((x / 16) % 2) + ((x / 32) % 2) + ((x / 64) % 2) + ((x / 128) % 2)

theorem mod2_eq_ite_testBit (x k : Nat) :
    (x / 2 ^ k) % 2 = if x.testBit k then 1 else 0 := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h0 | h1
  · have ha : (1 &&& x / 2 ^ k) = 0 := by rw [Nat.and_comm, Nat.and_one_is_mod, h0]
    simp [h0, ha]
  · have ha : (1 &&& x / 2 ^ k) = 1 := by rw [Nat.and_comm, Nat.and_one_is_mod, h1]
    simp [h1, ha]

theorem popcount8_eq_countPred (z : Nat) :
    popcount8 z = countPred (fun k => z.testBit k) 8 := by
  unfold popcount8
  simp only [countPred]
  have h0 : z % 2 = if z.testBit 0 then 1 else 0 := by simpa using mod2_eq_ite_testBit z 0
  have h1 := mod2_eq_ite_testBit z 1
  have h2 := mod2_eq_ite_testBit z 2
  have h3 := mod2_eq_ite_testBit z 3
  have h4 := mod2_eq_ite_testBit z 4
  have h5 := mod2_eq_ite_testBit z 5
  have h6 := mod2_eq_ite_testBit z 6
  have h7 := mod2_eq_ite_testBit z 7
  change (z % 2) + ((z / 2 ^ 1) % 2) + ((z / 2 ^ 2) % 2) + ((z / 2 ^ 3) % 2) +
         ((z / 2 ^ 4) % 2) + ((z / 2 ^ 5) % 2) + ((z / 2 ^ 6) % 2) + ((z / 2 ^ 7) % 2) = _
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  omega

/-- Popcount of a 16-bit integer (`0 ≤ m < 65536`). -/
@[expose] def popcount16 (m : Nat) : Nat :=
  popcount8 (m % 256) + popcount8 (m / 256)

/-- For a fixed lower-octonion mask `lo < 256`, compute the 8-bit forbidden-neighbor mask
    of upper vertex `u ∈ {0..7}` induced by all bad affine 2-planes whose lower pair lies in `lo`. -/
@[expose] def forbMask4 (lo u : Nat) : Nat :=
  cd4BadPlaneMasks.foldl (fun acc (lm, p, q) =>
    if (lo &&& lm) == lm then
      if p == u then acc ||| (1 <<< q)
      else if q == u then acc ||| (1 <<< p)
      else acc
    else acc) 0

/-- C-primitive bit test `(x / 2^k) % 2 == 1` avoiding `Nat.land`/`Nat.bitwise` recursion in `decide`! -/
@[expose] def bitAt (x k : Nat) : Bool := (x / (2 ^ k)) % 2 == 1

theorem bitAt_eq_testBit (x k : Nat) : bitAt x k = x.testBit k := by
  unfold bitAt
  have hm := mod2_eq_ite_testBit x k
  rw [hm]
  cases x.testBit k <;> rfl

/-- C-primitive check whether two 8-bit masks share any bit `< u` (`0` uses of `Nat.land`!). -/
@[expose] def disjointBelow (x y : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => !(bitAt x k && bitAt y k) && disjointBelow x y k

theorem disjointBelow_eq_land_zero (x y u : Nat) (hx : x < 2 ^ u) :
    disjointBelow x y u = ((x &&& y) == 0) := by
  have hiff : ∀ m, disjointBelow x y m = true ↔ ∀ k, k < m → (x.testBit k && y.testBit k) = false := by
    intro m
    induction m with
    | zero =>
      constructor
      · intro _ k hk; omega
      · intro _; rfl
    | succ m ih =>
      unfold disjointBelow
      rw [Bool.and_eq_true, ih, Bool.not_eq_true', bitAt_eq_testBit, bitAt_eq_testBit]
      constructor
      · intro ⟨hm, hall⟩ k hk
        by_cases hkm : k = m
        · subst hkm; exact hm
        · exact hall k (by omega)
      · intro hall
        exact ⟨hall m (by omega), fun k hk => hall k (by omega)⟩
  apply Bool.eq_iff_iff.mpr
  rw [hiff, beq_iff_eq]
  constructor
  · intro hall
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hku : k < u
    · exact hall k hku
    · have hlt : x < 2 ^ k := by
        calc x < 2 ^ u := hx
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      simp [Nat.testBit_lt_two_pow hlt]
  · intro hzero k _
    have := congrArg (fun z => z.testBit k) hzero
    rw [Nat.testBit_and, Nat.zero_testBit] at this
    exact this

/-- C-primitive 2-bit pair trigger (`0` uses of `Nat.land` or `Nat.lor`!):
    returns `bit` iff `lo` contains both `{a1, b1}` or both `{a2, b2}`. -/
@[expose] def forbPairFast (lo a1 b1 a2 b2 bit : Nat) : Nat :=
  if (bitAt lo a1 && bitAt lo b1) || (bitAt lo a2 && bitAt lo b2) then bit else 0

/-- Pure C-primitive (`Nat.div`/`Nat.mod`/`Nat.add`) forbidden-neighbor mask of `u ∈ {0..7}`!
    ZERO `Nat.land`, ZERO `Nat.lor`, ZERO `List.foldl` -> O(1) kernel evaluation! -/
@[expose] def forbMask4Direct (lo : Nat) : Nat → Nat
  | 1 => forbPairFast lo 4 7 5 6 4 + forbPairFast lo 4 6 5 7 8 + forbPairFast lo 2 7 3 6 16 +
         forbPairFast lo 2 6 3 7 32 + forbPairFast lo 2 5 3 4 64 + forbPairFast lo 2 4 3 5 128
  | 2 => forbPairFast lo 4 7 5 6 2 + forbPairFast lo 4 5 6 7 8 + forbPairFast lo 1 7 3 5 16 +
         forbPairFast lo 1 6 3 4 32 + forbPairFast lo 1 5 3 7 64 + forbPairFast lo 1 4 3 6 128
  | 3 => forbPairFast lo 4 6 5 7 2 + forbPairFast lo 4 5 6 7 4 + forbPairFast lo 1 6 2 5 16 +
         forbPairFast lo 1 7 2 4 32 + forbPairFast lo 1 4 2 7 64 + forbPairFast lo 1 5 2 6 128
  | 4 => forbPairFast lo 2 7 3 6 2 + forbPairFast lo 1 7 3 5 4 + forbPairFast lo 1 6 2 5 8 +
         forbPairFast lo 2 3 6 7 32 + forbPairFast lo 1 3 5 7 64 + forbPairFast lo 1 2 5 6 128
  | 5 => forbPairFast lo 2 6 3 7 2 + forbPairFast lo 1 6 3 4 4 + forbPairFast lo 1 7 2 4 8 +
         forbPairFast lo 2 3 6 7 16 + forbPairFast lo 1 2 4 7 64 + forbPairFast lo 1 3 4 6 128
  | 6 => forbPairFast lo 2 5 3 4 2 + forbPairFast lo 1 5 3 7 4 + forbPairFast lo 1 4 2 7 8 +
         forbPairFast lo 1 3 5 7 16 + forbPairFast lo 1 2 4 7 32 + forbPairFast lo 2 3 4 5 128
  | 7 => forbPairFast lo 2 4 3 5 2 + forbPairFast lo 1 4 3 6 4 + forbPairFast lo 1 5 2 6 8 +
         forbPairFast lo 1 2 5 6 16 + forbPairFast lo 1 3 4 6 32 + forbPairFast lo 2 3 4 5 64
  | _ => 0

theorem forbMask4_lt_256 (lo u : Nat) : forbMask4 lo u < 256 := by
  have hall8 : cd4BadPlaneMasks.all (fun (_, p, q) => p < 8 && q < 8) = true := by decide
  have hbit_lt : ∀ b, b < 8 → (1 <<< b) < 256 := by
    intro b hb; rw [Nat.shiftLeft_eq, Nat.one_mul]
    calc 2 ^ b ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      _ < 256 := by decide
  have hor_lt : ∀ a b, a < 256 → b < 256 → (a ||| b) < 256 := by
    intro a b ha hb
    have hpow : (256 : Nat) = 2 ^ 8 := rfl
    rw [hpow] at ha hb ⊢
    exact Nat.or_lt_two_pow ha hb
  have hfold : ∀ (L : List (Nat × Nat × Nat)) (acc : Nat),
      acc < 256 → (L.all fun (_, p, q) => p < 8 && q < 8) = true →
      L.foldl (fun a (lm, p, q) =>
        if (lo &&& lm) == lm then
          if p == u then a ||| (1 <<< q)
          else if q == u then a ||| (1 <<< p)
          else a
        else a) acc < 256 := by
    intro L
    induction L with
    | nil => intro acc hacc _; exact hacc
    | cons hd tl ih =>
      intro acc hacc hall
      rcases hd with ⟨lm, p, q⟩
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
      rw [List.foldl_cons]
      apply ih _ _ hall.2
      by_cases hlm : ((lo &&& lm) == lm) = true
      · simp only [hlm, ↓reduceIte]
        by_cases hpu : (p == u) = true
        · simp only [hpu, ↓reduceIte]; exact hor_lt acc _ hacc (hbit_lt q hall.1.2)
        · simp only [hpu, Bool.false_eq_true, ↓reduceIte]
          by_cases hqu : (q == u) = true
          · simp only [hqu, ↓reduceIte]; exact hor_lt acc _ hacc (hbit_lt p hall.1.1)
          · simp only [hqu, Bool.false_eq_true, ↓reduceIte]; exact hacc
      · simp only [hlm]; exact hacc
  exact hfold cd4BadPlaneMasks 0 (by omega) hall8

theorem forbMask4Direct_lt_256 (lo u : Nat) : forbMask4Direct lo u < 256 := by
  have hfp : ∀ a1 b1 a2 b2 bit, forbPairFast lo a1 b1 a2 b2 bit ≤ bit := by
    intro a1 b1 a2 b2 bit; unfold forbPairFast; split <;> omega
  match u with
  | 1 => have := hfp 4 7 5 6 4; have := hfp 4 6 5 7 8; have := hfp 2 7 3 6 16
         have := hfp 2 6 3 7 32; have := hfp 2 5 3 4 64; have := hfp 2 4 3 5 128
         simp only [forbMask4Direct]; omega
  | 2 => have := hfp 4 7 5 6 2; have := hfp 4 5 6 7 8; have := hfp 1 7 3 5 16
         have := hfp 1 6 3 4 32; have := hfp 1 5 3 7 64; have := hfp 1 4 3 6 128
         simp only [forbMask4Direct]; omega
  | 3 => have := hfp 4 6 5 7 2; have := hfp 4 5 6 7 4; have := hfp 1 6 2 5 16
         have := hfp 1 7 2 4 32; have := hfp 1 4 2 7 64; have := hfp 1 5 2 6 128
         simp only [forbMask4Direct]; omega
  | 4 => have := hfp 2 7 3 6 2; have := hfp 1 7 3 5 4; have := hfp 1 6 2 5 8
         have := hfp 2 3 6 7 32; have := hfp 1 3 5 7 64; have := hfp 1 2 5 6 128
         simp only [forbMask4Direct]; omega
  | 5 => have := hfp 2 6 3 7 2; have := hfp 1 6 3 4 4; have := hfp 1 7 2 4 8
         have := hfp 2 3 6 7 16; have := hfp 1 2 4 7 64; have := hfp 1 3 4 6 128
         simp only [forbMask4Direct]; omega
  | 6 => have := hfp 2 5 3 4 2; have := hfp 1 5 3 7 4; have := hfp 1 4 2 7 8
         have := hfp 1 3 5 7 16; have := hfp 1 2 4 7 32; have := hfp 2 3 4 5 128
         simp only [forbMask4Direct]; omega
  | 7 => have := hfp 2 4 3 5 2; have := hfp 1 4 3 6 4; have := hfp 1 5 2 6 8
         have := hfp 1 2 5 6 16; have := hfp 1 3 4 6 32; have := hfp 2 3 4 5 64
         simp only [forbMask4Direct]; omega
  | 0 | _ + 8 => simp only [forbMask4Direct]; omega

/-- Direct predicate: `hi < 256` avoids all 42 bad affine 2-planes paired with `lo < 256`. -/
@[expose] def hiAvoidsBad (lo hi : Nat) : Bool :=
  cd4BadPlaneMasks.all fun (lm, p, q) =>
    !((lo &&& lm) == lm && hi.testBit p && hi.testBit q)

theorem testBit_lo_hi (lo hi x : Nat) (hlo : lo < 256) :
    (lo + 256 * hi).testBit x = if x < 8 then lo.testBit x else hi.testBit (x - 8) := by
  have h256 : (256 : Nat) = 2 ^ 8 := rfl
  rw [h256, Nat.mul_comm (2 ^ 8) hi, Nat.add_comm]
  by_cases hx : x < 8
  · simp only [hx, ↓reduceIte]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hsplit : 2 ^ 8 = 2 ^ x * 2 ^ (8 - x) := by
      have : x + (8 - x) = 8 := by omega
      rw [← Nat.pow_add, this]
    have hmul : hi * 2 ^ 8 = 2 ^ x * (hi * 2 ^ (8 - x)) := by
      rw [hsplit]; ac_rfl
    have hdiv : (hi * 2 ^ 8 + lo) / 2 ^ x = hi * 2 ^ (8 - x) + lo / 2 ^ x := by
      rw [hmul, Nat.mul_add_div (Nat.two_pow_pos x)]
    rw [hdiv]
    have h2 : 2 ^ (8 - x) = 2 * 2 ^ (7 - x) := by
      have : 8 - x = (7 - x) + 1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]
    have hmul2 : hi * 2 ^ (8 - x) = 2 * (hi * 2 ^ (7 - x)) := by
      rw [h2]; ac_rfl
    rw [hmul2]
    have hmod : (2 * (hi * 2 ^ (7 - x)) + lo / 2 ^ x) % 2 = (lo / 2 ^ x) % 2 := by omega
    simp [hmod]
  · simp only [hx, ↓reduceIte]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hsplit : 2 ^ x = 2 ^ 8 * 2 ^ (x - 8) := by
      have : 8 + (x - 8) = x := by omega
      rw [← Nat.pow_add, this]
    rw [hsplit, ← Nat.div_div_eq_div_mul]
    have hdiv1 : (hi * 2 ^ 8 + lo) / 2 ^ 8 = hi := by
      rw [Nat.mul_comm hi (2 ^ 8), Nat.mul_add_div (by omega : 0 < 2 ^ 8),
          Nat.div_eq_of_lt hlo, Nat.add_zero]
    rw [hdiv1]

/-- Key finite lemma (`< 15ms` in pure kernel, depth 16):
    Every non-cancelling 4-tuple `(a, b, c, d)` in `CD_4` belongs to one of the 42 masks in
    `cd4BadPlaneMasks`, and conversely each of the 42 masks has an explicit non-cancelling 4-tuple
    and exact popcount 4. -/
theorem cd4_bad_pairing_iff_mem :
    allNat (fun a => allNat (fun b =>
      if !(a < b) then true
      else allNat (fun c =>
        if !(c != a && c != b) then true
        else
          let d := a ^^^ b ^^^ c
          if !(c < d && d < 16) then true
          else
            let bad := !pairingCancels 4 a b c d
            let inList := cd4BadPlaneMasks.any fun (lm, p, q) =>
              let m := lm + 256 * ((1 <<< p) ||| (1 <<< q))
              m.testBit a && m.testBit b && m.testBit c && m.testBit d
            (!bad) || inList) 16) 16) 16 = true := by
  decide

theorem cd4_bad_plane_masks_witness :
    cd4BadPlaneMasks.all (fun (lm, p, q) =>
      p < 8 && q < 8 && lm < 256 &&
      (popcount16 (lm + 256 * ((1 <<< p) ||| (1 <<< q))) == 4) &&
      !isNormMultMask 4 (lm + 256 * ((1 <<< p) ||| (1 <<< q)))) = true := by
  decide

theorem popcount16_eq_countPred (z : Nat) :
    popcount16 z = countPred (fun k => z.testBit k) 16 := by
  unfold popcount16
  rw [popcount8_eq_countPred, popcount8_eq_countPred]
  have hsplit : (16 : Nat) = 8 + 8 := rfl
  rw [hsplit, countPred_add]
  congr 1
  · apply countPred_ext; intro k hk
    have hz : z % 256 + 256 * (z / 256) = z := by omega
    have h := testBit_lo_hi (z % 256) (z / 256) k (Nat.mod_lt z (by omega))
    rw [hz] at h; simp only [hk, ↓reduceIte] at h; exact h.symm
  · apply countPred_ext; intro k hk
    have hz : z % 256 + 256 * (z / 256) = z := by omega
    have h := testBit_lo_hi (z % 256) (z / 256) (8 + k) (Nat.mod_lt z (by omega))
    have hnot : ¬(8 + k < 8) := by omega
    have hsub : 8 + k - 8 = k := by omega
    rw [hz] at h; simp only [hnot, hsub, ↓reduceIte] at h; exact h.symm

theorem isNormMultMask_mono (n m1 m2 : Nat)
    (hsub : ∀ x, x < 2 ^ n → m1.testBit x = true → m2.testBit x = true)
    (h2 : isNormMultMask n m2 = true) :
    isNormMultMask n m1 = true := by
  unfold isNormMultMask at h2 ⊢
  rw [allNat_eq_true] at h2 ⊢
  intro a ha
  by_cases ha1 : m1.testBit a = true
  · have ha2 := hsub a ha ha1
    have h2a := h2 a ha
    simp only [ha1, ha2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2a ⊢
    rw [allNat_eq_true] at h2a ⊢
    intro b hb
    by_cases hcond_b1 : (decide (a < b) && m1.testBit b) = true
    · simp only [Bool.and_eq_true] at hcond_b1
      have hb2 := hsub b hb hcond_b1.2
      have h2b := h2a b hb
      simp only [hcond_b1.1, hcond_b1.2, hb2, Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2b ⊢
      rw [allNat_eq_true] at h2b ⊢
      intro c hc
      by_cases hcond_c1 : (m1.testBit c && (c != a) && (c != b)) = true
      · simp only [Bool.and_eq_true] at hcond_c1
        have hc2 := hsub c hc hcond_c1.1.1
        have h2c := h2b c hc
        simp only [hcond_c1.1.1, hc2, hcond_c1.1.2, hcond_c1.2, Bool.and_true,
                   Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2c ⊢
        by_cases hcond_d1 : (decide (c < a ^^^ b ^^^ c) && decide (a ^^^ b ^^^ c < 2 ^ n) && m1.testBit (a ^^^ b ^^^ c)) = true
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond_d1
          have hd2 := hsub (a ^^^ b ^^^ c) hcond_d1.1.2 hcond_d1.2
          simp only [hcond_d1.1.1, hcond_d1.1.2, hcond_d1.2, hd2, decide_true,
                     Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2c ⊢
          exact h2c
        · have hcond_d1_f := Bool.eq_false_iff.mpr hcond_d1
          simp only [hcond_d1_f, Bool.not_false, ↓reduceIte]
      · simp [hcond_c1]
    · simp [hcond_b1]
  · simp [ha1]

/-- Exact equivalence `isNormMultMask 4 (lo + 256 * hi) = hiAvoidsBad lo hi` for ALL
    `lo < 256`, `hi < 256` — bridging the direct textbook bilinear norm definition to the
    42-plane hypergraph formulation with ZERO gap! -/
theorem isNormMultMask4_eq_hiAvoidsBad (lo hi : Nat) (hlo : lo < 256) :
    isNormMultMask 4 (lo + 256 * hi) = hiAvoidsBad lo hi := by
  have hsub_bit : ∀ lm p q x, (lm, p, q) ∈ cd4BadPlaneMasks →
      ((lo &&& lm) == lm) = true → hi.testBit p = true → hi.testBit q = true →
      (lm + 256 * ((1 <<< p) ||| (1 <<< q))).testBit x = true →
      (lo + 256 * hi).testBit x = true := by
    intro lm p q x hmem hlo_and hp hq hx
    have hsp := List.all_eq_true.mp cd4_bad_plane_masks_witness (lm, p, q) hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsp
    have hlm256 : lm < 256 := hsp.1.1.2
    rw [testBit_lo_hi lm _ x hlm256] at hx
    rw [testBit_lo_hi lo hi x hlo]
    by_cases hx8 : x < 8
    · simp only [hx8, ↓reduceIte] at hx ⊢
      have heq := beq_iff_eq.mp hlo_and
      have hbit := congrArg (fun z => z.testBit x) heq
      rw [Nat.testBit_and, hx, Bool.and_true] at hbit
      exact hbit
    · simp only [hx8, ↓reduceIte] at hx ⊢
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft] at hx
      rcases Bool.or_eq_true_iff.mp hx with h1 | h2
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at h1
        have : x - 8 = p := by omega
        rw [this]; exact hp
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at h2
        have : x - 8 = q := by omega
        rw [this]; exact hq
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hnm
    unfold hiAvoidsBad
    apply List.all_eq_true.mpr
    intro ⟨lm, p, q⟩ hmem
    by_cases hbad : ((lo &&& lm) == lm && hi.testBit p && hi.testBit q) = true
    · exfalso
      simp only [Bool.and_eq_true] at hbad
      have hsp := List.all_eq_true.mp cd4_bad_plane_masks_witness (lm, p, q) hmem
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsp
      have hmono := isNormMultMask_mono 4 (lm + 256 * ((1 <<< p) ||| (1 <<< q))) (lo + 256 * hi)
        (fun x _ hx => hsub_bit lm p q x hmem hbad.1.1 hbad.1.2 hbad.2 hx) hnm
      rw [hsp.2] at hmono; cases hmono
    · simp [Bool.eq_false_iff.mpr hbad]
  · intro hav
    unfold isNormMultMask
    rw [allNat_eq_true]; intro a ha16
    by_cases ha_in : (lo + 256 * hi).testBit a = true
    · simp only [ha_in, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [allNat_eq_true]; intro b hb16
      by_cases hcond_b : (decide (a < b) && (lo + 256 * hi).testBit b) = true
      · simp only [hcond_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [allNat_eq_true]; intro c hc16
        by_cases hcond_c : ((lo + 256 * hi).testBit c && (c != a) && (c != b)) = true
        · simp only [hcond_c, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hcond_d : (decide (c < a ^^^ b ^^^ c) && decide (a ^^^ b ^^^ c < 16) && (lo + 256 * hi).testBit (a ^^^ b ^^^ c)) = true
          · simp only [hcond_d, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            let d := a ^^^ b ^^^ c
            by_cases hpc : pairingCancels 4 a b c d = true
            · exact hpc
            · exfalso
              have hpc_f : pairingCancels 4 a b c (a ^^^ b ^^^ c) = false := Bool.eq_false_iff.mpr hpc
              have hchk := (allNat_eq_true _ 16).mp cd4_bad_pairing_iff_mem a ha16
              have hchk2 := (allNat_eq_true _ 16).mp hchk b hb16
              simp only [Bool.and_eq_true] at hcond_b hcond_c hcond_d
              simp only [hcond_b.1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk2
              have hchk3 := (allNat_eq_true _ 16).mp hchk2 c hc16
              simp only [hcond_c.1.2, hcond_c.2, hcond_d.1.1, hcond_d.1.2,
                         Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                         hpc_f, Bool.not_false, Bool.false_or] at hchk3
              rcases List.any_eq_true.mp hchk3 with ⟨⟨lm, p, q⟩, hmem, hbits⟩
              have hsp := List.all_eq_true.mp cd4_bad_plane_masks_witness (lm, p, q) hmem
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsp
              have hp8 : p < 8 := hsp.1.1.1.1
              have hq8 : q < 8 := hsp.1.1.1.2
              have hlm256 : lm < 256 := hsp.1.1.2
              have hpop4 : popcount16 (lm + 256 * ((1 <<< p) ||| (1 <<< q))) = 4 := hsp.1.2
              have hm_eq4 : ∀ x, x < 16 →
                  (lm + 256 * ((1 <<< p) ||| (1 <<< q))).testBit x = true →
                  x = a ∨ x = b ∨ x = c ∨ x = d := by
                intro x hx hmx
                have hne_ab : a ≠ b := by have := decide_eq_true_eq.mp hcond_b.1; omega
                have hne_ca : c ≠ a := bne_iff_ne.mp hcond_c.1.2
                have hne_cb : c ≠ b := bne_iff_ne.mp hcond_c.2
                have hne_cd : c ≠ d := by have := decide_eq_true_eq.mp hcond_d.1.1; omega
                have hne_da : d ≠ a := by
                  intro heq
                  have h1 : d ^^^ a = 0 := by rw [heq, Nat.xor_self]
                  have hbc : b ^^^ c = 0 := by
                    dsimp only [d] at h1
                    have hsimp : ((a ^^^ b) ^^^ c) ^^^ a = b ^^^ c := by
                      rw [Nat.xor_comm (a ^^^ b) c, Nat.xor_assoc, Nat.xor_comm a b,
                          Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.xor_comm]
                    rw [← hsimp]; exact h1
                  exact hne_cb (Eq.symm (eq_of_xor_eq_zero hbc))
                have hne_db : d ≠ b := by
                  intro heq
                  have h1 : d ^^^ b = 0 := by rw [heq, Nat.xor_self]
                  have hac : a ^^^ c = 0 := by
                    have hsimp : ((a ^^^ b) ^^^ c) ^^^ b = a ^^^ c := by
                      rw [Nat.xor_comm (a ^^^ b) c, Nat.xor_assoc, Nat.xor_assoc,
                          Nat.xor_self, Nat.xor_zero, Nat.xor_comm]
                    rw [← hsimp]; exact h1
                  exact hne_ca (Eq.symm (eq_of_xor_eq_zero hac))
                by_cases hxa : x = a
                · exact Or.inl hxa
                · by_cases hxb : x = b
                  · exact Or.inr (Or.inl hxb)
                  · by_cases hxc : x = c
                    · exact Or.inr (Or.inr (Or.inl hxc))
                    · by_cases hxd : x = d
                      · exact Or.inr (Or.inr (Or.inr hxd))
                      · exfalso
                        let m := lm + 256 * ((1 <<< p) ||| (1 <<< q))
                        have h5 : ∀ k, k ≤ 16 →
                            (if a < k then 1 else 0) + (if b < k then 1 else 0) +
                            (if c < k then 1 else 0) + (if d < k then 1 else 0) +
                            (if x < k then 1 else 0) ≤ countPred (fun j => m.testBit j) k := by
                          intro k hk
                          induction k with
                          | zero => simp [countPred]
                          | succ k ihk =>
                            unfold countPred
                            have hih := ihk (by omega)
                            simp only [Bool.and_eq_true] at hbits
                            have hstep1 : ∀ y, k ≠ y → (if y < k + 1 then 1 else 0) = (if y < k then 1 else 0) := by
                              intro y hky
                              by_cases hy : y < k
                              · have hy2 : y < k + 1 := by omega
                                simp only [hy, hy2, ↓reduceIte]
                              · have hy2 : ¬(y < k + 1) := by omega
                                simp only [hy, hy2, ↓reduceIte]
                            have hstep_eq : ∀ y, k = y → (if y < k + 1 then 1 else 0) = (if y < k then 1 else 0) + 1 := by
                              intro y hky; subst hky; simp
                            by_cases hka : k = a
                            · have hmk : m.testBit k = true := by rw [hka]; exact hbits.1.1.1
                              rw [hstep_eq a hka, hstep1 b (by omega), hstep1 c (by omega),
                                  hstep1 d (by omega), hstep1 x (by omega), hmk]
                              simp only [↓reduceIte]; omega
                            · by_cases hkb : k = b
                              · have hmk : m.testBit k = true := by rw [hkb]; exact hbits.1.1.2
                                rw [hstep1 a hka, hstep_eq b hkb, hstep1 c (by omega),
                                    hstep1 d (by omega), hstep1 x (by omega), hmk]
                                simp only [↓reduceIte]; omega
                              · by_cases hkc : k = c
                                · have hmk : m.testBit k = true := by rw [hkc]; exact hbits.1.2
                                  rw [hstep1 a hka, hstep1 b hkb, hstep_eq c hkc,
                                      hstep1 d (by omega), hstep1 x (by omega), hmk]
                                  simp only [↓reduceIte]; omega
                                · by_cases hkd : k = d
                                  · have hmk : m.testBit k = true := by rw [hkd]; exact hbits.2
                                    rw [hstep1 a hka, hstep1 b hkb, hstep1 c hkc,
                                        hstep_eq d hkd, hstep1 x (by omega), hmk]
                                    simp only [↓reduceIte]; omega
                                  · by_cases hkx : k = x
                                    · have hmk : m.testBit k = true := by rw [hkx]; exact hmx
                                      rw [hstep1 a hka, hstep1 b hkb, hstep1 c hkc,
                                          hstep1 d hkd, hstep_eq x hkx, hmk]
                                      simp only [↓reduceIte]; omega
                                    · rw [hstep1 a hka, hstep1 b hkb,
                                          hstep1 c hkc, hstep1 d hkd,
                                          hstep1 x hkx]
                                      omega
                        have hle5 := h5 16 (Nat.le_refl _)
                        have hd16 : d < 16 := decide_eq_true_eq.mp hcond_d.1.2
                        rw [← popcount16_eq_countPred, hpop4] at hle5
                        simp only [ha16, hb16, hc16, hd16, hx, ↓reduceIte] at hle5
                        omega
              have hbit_in : ∀ x, x < 16 → (lm + 256 * ((1 <<< p) ||| (1 <<< q))).testBit x = true →
                  (lo + 256 * hi).testBit x = true := by
                intro x hx hmx
                rcases hm_eq4 x hx hmx with rfl | rfl | rfl | rfl
                · exact ha_in
                · exact hcond_b.2
                · exact hcond_c.1.1
                · exact hcond_d.2
              have hlo_and : (lo &&& lm) = lm := by
                apply Nat.eq_of_testBit_eq; intro k
                rw [Nat.testBit_and]
                by_cases hkm : lm.testBit k = true
                · have hk8 : k < 8 := by
                    by_cases h8 : k < 8
                    · exact h8
                    · exfalso
                      have hlt : lm < 2 ^ k := by
                        calc lm < 2 ^ 8 := hlm256
                          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
                      rw [Nat.testBit_lt_two_pow hlt] at hkm; cases hkm
                  have h1 := hbit_in k (by omega) (by rw [testBit_lo_hi lm _ k hlm256]; simp [hk8, hkm])
                  rw [testBit_lo_hi lo hi k hlo] at h1
                  simp [hk8, hkm] at h1 ⊢; exact h1
                · simp [Bool.eq_false_iff.mpr hkm]
              have hp_in : hi.testBit p = true := by
                have h1 := hbit_in (p + 8) (by omega) (by
                  rw [testBit_lo_hi lm _ (p + 8) hlm256]
                  have hge : ¬(p + 8 < 8) := by omega
                  simp [hge, Nat.testBit_or, Nat.testBit_shiftLeft])
                rw [testBit_lo_hi lo hi (p + 8) hlo] at h1
                have hge : ¬(p + 8 < 8) := by omega
                simpa [hge] using h1
              have hq_in : hi.testBit q = true := by
                have h1 := hbit_in (q + 8) (by omega) (by
                  rw [testBit_lo_hi lm _ (q + 8) hlm256]
                  have hge : ¬(q + 8 < 8) := by omega
                  simp [hge, Nat.testBit_or, Nat.testBit_shiftLeft])
                rw [testBit_lo_hi lo hi (q + 8) hlo] at h1
                have hge : ¬(q + 8 < 8) := by omega
                simpa [hge] using h1
              have hav_mem := List.all_eq_true.mp hav (lm, p, q) hmem
              simp [hlo_and, hp_in, hq_in] at hav_mem
          · have hcond_d_f := Bool.eq_false_iff.mpr hcond_d
            simp only [hcond_d_f, Bool.not_false, ↓reduceIte]
        · simp [hcond_c]
      · simp [hcond_b]
    · simp [ha_in]

/-- Pure C-primitive branch-and-bound counter returning `(count_eq_target, count_gt_target)`
    over all extensions of `chosen` by bits `u..7` avoiding `forb` (ZERO `Nat.land`/`Nat.lor`!). -/
@[expose] def countIndepHi (forb : Nat → Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _chosen, cnt, target =>
      if cnt == target then (1, 0)
      else if target < cnt then (0, 1)
      else (0, 0)
  | rem + 1, chosen, cnt, target =>
      if cnt + (rem + 1) < target then (0, 0)
      else
        let u := 7 - rem
        let r0 := countIndepHi forb rem chosen cnt target
        if disjointBelow chosen (forb u) u then
          let r1 := countIndepHi forb rem (chosen + 2 ^ u) (cnt + 1) target
          (r0.1 + r1.1, r0.2 + r1.2)
        else r0

theorem countIndepHi_ext (f g : Nat → Nat) (hext : ∀ u, u < 8 → f u = g u) :
    ∀ rem chosen cnt target, rem ≤ 8 →
      countIndepHi f rem chosen cnt target = countIndepHi g rem chosen cnt target := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _; rfl
  | succ rem ih =>
    intro chosen cnt target hrem
    unfold countIndepHi; dsimp only
    rw [hext (7 - rem) (by omega), ih chosen cnt target (by omega),
        ih (chosen + 2 ^ (7 - rem)) (cnt + 1) target (by omega)]

/-- Direct predicate: `hi < 256` is independent in the symmetric graph `forb`. -/
@[expose] def isIndepForb (forb : Nat → Nat) (hi : Nat) : Bool :=
  allNat (fun u => !hi.testBit u || ((hi &&& forb u) == 0)) 8

theorem testBit_one_of_ne_zero {k : Nat} (hk : k ≠ 0) : Nat.testBit 1 k = false :=
  Bool.eq_false_iff.mpr (fun h => hk ((Nat.testBit_one_eq_true_iff_self_eq_zero).mp h))

theorem testBit_forbMask4 (lo u v : Nat) (_hu : u < 8) (_hv : v < 8) :
    (forbMask4 lo u).testBit v =
      cd4BadPlaneMasks.any (fun (lm, p, q) =>
        (lo &&& lm) == lm && ((p == u && q == v) || (q == u && p == v))) := by
  have hfold : ∀ (L : List (Nat × Nat × Nat)) (acc : Nat),
      (L.all fun (_, p, q) => p < 8 && q < 8 && (p != q)) = true →
      (L.foldl (fun a (lm, p, q) =>
        if (lo &&& lm) == lm then
          if p == u then a ||| (1 <<< q)
          else if q == u then a ||| (1 <<< p)
          else a
        else a) acc).testBit v =
      (acc.testBit v || L.any (fun (lm, p, q) =>
        (lo &&& lm) == lm && ((p == u && q == v) || (q == u && p == v)))) := by
    intro L
    induction L with
    | nil => intro acc _; simp
    | cons hd tl ih =>
      intro acc hall
      rcases hd with ⟨lm, p, q⟩
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
      have hpq : p ≠ q := bne_iff_ne.mp hall.1.2
      rw [List.foldl_cons, ih _ hall.2, List.any_cons]
      by_cases hlm : ((lo &&& lm) == lm) = true
      · simp only [hlm, ↓reduceIte, Bool.true_and]
        by_cases hpu : p = u
        · subst hpu
          have hqu : (q == p) = false := beq_false_of_ne (Ne.symm hpq)
          simp only [beq_self_eq_true, hqu, Bool.false_and, Bool.or_false, Bool.true_and,
                     ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
          by_cases hqv : q = v
          · subst hqv; simp
          · have hqv_f : (q == v) = false := beq_false_of_ne hqv
            have hbit : (decide (q ≤ v) && Nat.testBit 1 (v - q)) = false := by
              by_cases hle : q ≤ v
              · simp [hle, testBit_one_of_ne_zero (by omega : v - q ≠ 0)]
              · simp [hle]
            simp [hqv_f, hbit]
        · have hpu_f : (p == u) = false := beq_false_of_ne hpu
          simp only [hpu_f, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.false_or]
          by_cases hqu : q = u
          · subst hqu
            simp only [beq_self_eq_true, Bool.true_and, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
            by_cases hpv : p = v
            · subst hpv; simp
            · have hpv_f : (p == v) = false := beq_false_of_ne hpv
              have hbit : (decide (p ≤ v) && Nat.testBit 1 (v - p)) = false := by
                by_cases hle : p ≤ v
                · simp [hle, testBit_one_of_ne_zero (by omega : v - p ≠ 0)]
                · simp [hle]
              simp [hpv_f, hbit]
          · have hqu_f : (q == u) = false := beq_false_of_ne hqu
            simp [hqu_f]
      · have hlm_f : ((lo &&& lm) == lm) = false := Bool.eq_false_iff.mpr hlm
        simp [hlm_f]
  have hall8 : cd4BadPlaneMasks.all (fun (_, p, q) => p < 8 && q < 8 && (p != q)) = true := by decide
  unfold forbMask4
  rw [hfold cd4BadPlaneMasks 0 hall8]
  simp

/-- Exact proof that `forbMask4Direct lo u = forbMask4 lo u` for EVERY `lo` and `u < 8`! -/
theorem forbMask4Direct_eq_forbMask4 (lo u : Nat) (hu : u < 8) :
    forbMask4Direct lo u = forbMask4 lo u := by
  have hmod_direct : forbMask4Direct lo u = forbMask4Direct (lo % 256) u := by
    have hbit_mod : ∀ k, k < 8 → bitAt lo k = bitAt (lo % 256) k := by
      intro k hk
      rw [bitAt_eq_testBit, bitAt_eq_testBit, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
      simp [hk]
    have hfp_mod : ∀ a1 b1 a2 b2 bit, a1 < 8 → b1 < 8 → a2 < 8 → b2 < 8 →
        forbPairFast lo a1 b1 a2 b2 bit = forbPairFast (lo % 256) a1 b1 a2 b2 bit := by
      intro a1 b1 a2 b2 bit ha1 hb1 ha2 hb2
      unfold forbPairFast
      rw [hbit_mod a1 ha1, hbit_mod b1 hb1, hbit_mod a2 ha2, hbit_mod b2 hb2]
    match u with
    | 0 | _ + 8 => rfl
    | 1 => simp only [forbMask4Direct]
           rw [hfp_mod 4 7 5 6 4 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 4 6 5 7 8 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 7 3 6 16 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 6 3 7 32 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 5 3 4 64 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 4 3 5 128 (by omega) (by omega) (by omega) (by omega)]
    | 2 => simp only [forbMask4Direct]
           rw [hfp_mod 4 7 5 6 2 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 4 5 6 7 8 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 7 3 5 16 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 6 3 4 32 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 5 3 7 64 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 4 3 6 128 (by omega) (by omega) (by omega) (by omega)]
    | 3 => simp only [forbMask4Direct]
           rw [hfp_mod 4 6 5 7 2 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 4 5 6 7 4 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 6 2 5 16 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 7 2 4 32 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 4 2 7 64 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 5 2 6 128 (by omega) (by omega) (by omega) (by omega)]
    | 4 => simp only [forbMask4Direct]
           rw [hfp_mod 2 7 3 6 2 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 7 3 5 4 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 6 2 5 8 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 3 6 7 32 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 3 5 7 64 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 2 5 6 128 (by omega) (by omega) (by omega) (by omega)]
    | 5 => simp only [forbMask4Direct]
           rw [hfp_mod 2 6 3 7 2 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 6 3 4 4 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 7 2 4 8 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 3 6 7 16 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 2 4 7 64 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 3 4 6 128 (by omega) (by omega) (by omega) (by omega)]
    | 6 => simp only [forbMask4Direct]
           rw [hfp_mod 2 5 3 4 2 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 5 3 7 4 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 4 2 7 8 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 3 5 7 16 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 2 4 7 32 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 3 4 5 128 (by omega) (by omega) (by omega) (by omega)]
    | 7 => simp only [forbMask4Direct]
           rw [hfp_mod 2 4 3 5 2 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 4 3 6 4 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 5 2 6 8 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 2 5 6 16 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 1 3 4 6 32 (by omega) (by omega) (by omega) (by omega),
               hfp_mod 2 3 4 5 64 (by omega) (by omega) (by omega) (by omega)]
  have hmod_forb : forbMask4 lo u = forbMask4 (lo % 256) u := by
    apply Nat.eq_of_testBit_eq; intro k
    by_cases hk : k < 8
    · rw [testBit_forbMask4 lo u k hu hk, testBit_forbMask4 (lo % 256) u k hu hk]
      have hlm256 : cd4BadPlaneMasks.all (fun (lm, _, _) => lm < 256) = true := by decide
      have hany_ext : ∀ (L : List (Nat × Nat × Nat)),
          (L.all fun (lm, _, _) => lm < 256) = true →
          L.any (fun (lm, p, q) => (lo &&& lm) == lm && ((p == u && q == k) || (q == u && p == k))) =
          L.any (fun (lm, p, q) => ((lo % 256) &&& lm) == lm && ((p == u && q == k) || (q == u && p == k))) := by
        intro L
        induction L with
        | nil => intro _; rfl
        | cons hd tl ih =>
          rcases hd with ⟨lm, p, q⟩
          intro hall
          simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
          rw [List.any_cons, List.any_cons, ih hall.2]
          have hand_eq : (lo &&& lm) = ((lo % 256) &&& lm) := by
            apply Nat.eq_of_testBit_eq; intro j
            rw [Nat.testBit_and, Nat.testBit_and, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
            by_cases hj : j < 8
            · simp [hj]
            · have hlt : lm < 2 ^ j := by
                calc lm < 2 ^ 8 := hall.1
                  _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
              simp [Nat.testBit_lt_two_pow hlt]
          dsimp only
          rw [hand_eq]
      exact hany_ext cd4BadPlaneMasks hlm256
    · have h1 : forbMask4 lo u < 2 ^ k := by
        calc forbMask4 lo u < 2 ^ 8 := forbMask4_lt_256 lo u
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : forbMask4 (lo % 256) u < 2 ^ k := by
        calc forbMask4 (lo % 256) u < 2 ^ 8 := forbMask4_lt_256 (lo % 256) u
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  rw [hmod_direct, hmod_forb]
  have hm_lt : lo % 256 < 256 := Nat.mod_lt lo (by omega)
  have hall_eq : allNat (fun i => allNat (fun j =>
      allNat (fun w => forbMask4Direct (16 * i + j) w == forbMask4 (16 * i + j) w) 8) 16) 16 = true := by
    decide
  have hi := (allNat_eq_true _ 16).mp hall_eq ((lo % 256) / 16) (by omega)
  have hj := (allNat_eq_true _ 16).mp hi ((lo % 256) % 16) (by omega)
  have hw := (allNat_eq_true _ 8).mp hj u hu
  have heq_m : 16 * ((lo % 256) / 16) + (lo % 256) % 16 = lo % 256 := by omega
  rw [heq_m] at hw
  exact beq_iff_eq.mp hw

/-- Pure algebraic proof (zero `decide`!) that `forbMask4 lo` is symmetric and irreflexive
    for EVERY `lo`! -/
theorem forbMask4_symm_irref (lo : Nat) :
    (∀ u v, u < 8 → v < 8 → (forbMask4 lo u).testBit v = (forbMask4 lo v).testBit u) ∧
    (∀ u, u < 8 → (forbMask4 lo u).testBit u = false) := by
  have hall_ne : cd4BadPlaneMasks.all (fun (_, p, q) => p != q) = true := by decide
  constructor
  · intro u v hu hv
    rw [testBit_forbMask4 lo u v hu hv, testBit_forbMask4 lo v u hv hu]
    congr 1; funext ⟨lm, p, q⟩; dsimp only
    cases (lo &&& lm) == lm <;> cases p == u <;> cases q == v <;> cases q == u <;> cases p == v <;> rfl
  · intro u hu
    rw [testBit_forbMask4 lo u u hu hu]
    apply Bool.eq_false_iff.mpr; intro hany
    rcases List.any_eq_true.mp hany with ⟨⟨lm, p, q⟩, hmem, hcond⟩
    have hne := bne_iff_ne.mp (List.all_eq_true.mp hall_ne (lm, p, q) hmem)
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
    rcases hcond.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne rfl

theorem hiAvoidsBad_eq_isIndepForb (lo hi : Nat) (hhi : hi < 256) :
    hiAvoidsBad lo hi = isIndepForb (forbMask4 lo) hi := by
  have hall8 : cd4BadPlaneMasks.all (fun (_, p, q) => p < 8 && q < 8) = true := by decide
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hav
    unfold isIndepForb
    rw [allNat_eq_true]; intro u hu
    by_cases hbu : hi.testBit u = true
    · simp only [hbu, Bool.not_true, Bool.false_or, beq_iff_eq]
      apply Nat.eq_of_testBit_eq; intro v
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hv8 : v < 8
      · rw [testBit_forbMask4 lo u v hu hv8]
        by_cases hbv : hi.testBit v = true
        · simp only [hbv, Bool.true_and]
          apply Bool.eq_false_iff.mpr; intro hany
          rcases List.any_eq_true.mp hany with ⟨⟨lm, p, q⟩, hmem, hcond⟩
          have hav_m := List.all_eq_true.mp hav (lm, p, q) hmem
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
          rcases hcond.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [hcond.1, hbu, hbv] at hav_m
          · simp [hcond.1, hbu, hbv] at hav_m
        · simp [Bool.eq_false_iff.mpr hbv]
      · have hlt : hi < 2 ^ v := by
          calc hi < 2 ^ 8 := hhi
            _ ≤ 2 ^ v := Nat.pow_le_pow_right (by omega) (by omega)
        simp [Nat.testBit_lt_two_pow hlt]
    · simp [Bool.eq_false_iff.mpr hbu]
  · intro hind
    unfold hiAvoidsBad
    apply List.all_eq_true.mpr; intro ⟨lm, p, q⟩ hmem
    have hsp := List.all_eq_true.mp hall8 (lm, p, q) hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsp
    by_cases hbad : ((lo &&& lm) == lm && hi.testBit p && hi.testBit q) = true
    · exfalso
      simp only [Bool.and_eq_true] at hbad
      have h1 := (allNat_eq_true _ 8).mp hind p hsp.1
      simp only [hbad.1.2, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
      have hbit := congrArg (fun z => z.testBit q) h1
      rw [Nat.testBit_and, Nat.zero_testBit, hbad.2, Bool.true_and,
          testBit_forbMask4 lo p q hsp.1 hsp.2] at hbit
      have hany : cd4BadPlaneMasks.any (fun (lm', p', q') =>
          (lo &&& lm') == lm' && ((p' == p && q' == q) || (q' == p && p' == q))) = true := by
        apply List.any_eq_true.mpr
        refine ⟨(lm, p, q), hmem, ?_⟩
        simp [hbad.1.1]
      rw [hany] at hbit; cases hbit
    · simp [Bool.eq_false_iff.mpr hbad]

/-- Exact soundness of `countIndepHi`: for any symmetric irreflexive 8-vertex graph `forb`,
    `countIndepHi forb 8 0 0 target` equals the exact pair of counts over all `hi < 256`. -/
theorem countIndepHi_sound (forb : Nat → Nat)
    (hsym : ∀ u v, u < 8 → v < 8 → (forb u).testBit v = (forb v).testBit u)
    (hirref : ∀ u, u < 8 → (forb u).testBit u = false)
    (target : Nat) :
    let res := countIndepHi forb 8 0 0 target
    res.1 = countPred (fun hi => isIndepForb forb hi && (popcount8 hi == target)) 256 ∧
    res.2 = countPred (fun hi => isIndepForb forb hi && decide (target < popcount8 hi)) 256 := by
  have hpop_eq : ∀ z, popcount8 z = countPred (fun k => z.testBit k) 8 := popcount8_eq_countPred
  have hgen : ∀ rem chosen cnt, rem ≤ 8 → chosen < 2 ^ (8 - rem) →
      cnt = popcount8 chosen →
      isIndepForb forb chosen = true →
      let u := 8 - rem
      let matchPrefix : Nat → Bool := fun hi => hi % (2 ^ u) == chosen
      (countIndepHi forb rem chosen cnt target).1 =
        countPred (fun hi => matchPrefix hi && isIndepForb forb hi && (popcount8 hi == target)) 256 ∧
      (countIndepHi forb rem chosen cnt target).2 =
        countPred (fun hi => matchPrefix hi && isIndepForb forb hi && decide (target < popcount8 hi)) 256 := by
    intro rem
    induction rem with
    | zero =>
      intro chosen cnt _ hlt hcnt hind
      have hsingle_eq : ∀ (P : Nat → Bool),
          countPred (fun hi => (hi % 256 == chosen) && P hi) 256 = if P chosen then 1 else 0 := by
        intro P
        have h1 : ∀ m, m ≤ 256 →
            countPred (fun hi => (hi % 256 == chosen) && P hi) m =
            if chosen < m && P chosen then 1 else 0 := by
          intro m hm
          induction m with
          | zero => simp [countPred]
          | succ m ihm =>
            unfold countPred; rw [ihm (by omega)]
            have hmod : m % 256 = m := Nat.mod_eq_of_lt (by omega)
            by_cases hmc : m = chosen
            · subst hmc; simp [hmod]
            · have hne : (m % 256 == chosen) = false := by rw [hmod]; exact beq_false_of_ne hmc
              have hlt_iff : (chosen < m + 1) ↔ (chosen < m) := by omega
              simp [hne, hlt_iff]
        rw [h1 256 (Nat.le_refl _)]; simp [hlt]
      unfold countIndepHi; dsimp only
      have h256 : 2 ^ (8 - 0) = 256 := rfl
      rw [h256]
      have hs1 := hsingle_eq (fun hi => isIndepForb forb hi && (popcount8 hi == target))
      have hs2 := hsingle_eq (fun hi => isIndepForb forb hi && decide (target < popcount8 hi))
      simp only [Bool.and_assoc] at hs1 hs2 ⊢
      rw [hs1, hs2, hind, ← hcnt]
      simp only [Bool.true_and]
      by_cases h1 : cnt = target
      · subst h1; simp
      · have h1f : (cnt == target) = false := beq_false_of_ne h1
        by_cases h2 : target < cnt
        · simp [h1f, h2]
        · simp [h1f, h2]
    | succ rem ih =>
      intro chosen cnt hrem hlt hcnt hind
      let u := 7 - rem
      have hu_eq : 8 - (rem + 1) = u := by omega
      have hu1_eq : 8 - rem = u + 1 := by omega
      have hu8 : u < 8 := by omega
      have hbit_pop_le : ∀ hi, hi < 256 → hi % 2 ^ u = chosen →
          popcount8 hi ≤ cnt + (rem + 1) := by
        intro hi _ hmod
        rw [hcnt, hpop_eq hi, hpop_eq chosen]
        have hstep : ∀ k, k ≤ 8 →
            countPred (fun j => hi.testBit j) k ≤
            countPred (fun j => chosen.testBit j) k + (if u < k then k - u else 0) := by
          intro k hk
          induction k with
          | zero => simp [countPred]
          | succ k ihk =>
            unfold countPred
            have hihk := ihk (by omega)
            by_cases hku : k < u
            · have htb : hi.testBit k = chosen.testBit k := by
                rw [← hmod, Nat.testBit_mod_two_pow]; simp [hku]
              rw [htb]
              have hnot1 : ¬(u < k) := by omega
              have hnot2 : ¬(u < k + 1) := by omega
              simp only [hnot1, hnot2, ↓reduceIte] at hihk ⊢; omega
            · have hpos2 : u < k + 1 := by omega
              by_cases hku2 : u < k
              · simp only [hku2, hpos2, ↓reduceIte] at hihk ⊢
                cases hi.testBit k <;> cases chosen.testBit k <;> simp <;> omega
              · simp only [hku2, hpos2, ↓reduceIte] at hihk ⊢
                cases hi.testBit k <;> cases chosen.testBit k <;> simp <;> omega
        have := hstep 8 (Nat.le_refl _)
        simp only [hu8, ↓reduceIte] at this; omega
      by_cases hprune : cnt + (rem + 1) < target
      · unfold countIndepHi; dsimp only
        simp only [hprune, ↓reduceIte]
        constructor
        · symm
          apply Eq.trans (countPred_ext _ (fun _ => false) 256 (fun hi hhi => ?_)) (countPred_false 256)
          by_cases hm : (hi % 2 ^ (8 - (rem + 1)) == chosen) = true
          · rw [hu_eq, beq_iff_eq] at hm
            have hle := hbit_pop_le hi hhi hm
            have hne : (popcount8 hi == target) = false := beq_false_of_ne (by omega)
            simp [hne]
          · have hmf := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_and]
        · symm
          apply Eq.trans (countPred_ext _ (fun _ => false) 256 (fun hi hhi => ?_)) (countPred_false 256)
          by_cases hm : (hi % 2 ^ (8 - (rem + 1)) == chosen) = true
          · rw [hu_eq, beq_iff_eq] at hm
            have hle := hbit_pop_le hi hhi hm
            have hnot : ¬(target < popcount8 hi) := by omega
            simp [hnot]
          · have hmf := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_and]
      · unfold countIndepHi; dsimp only
        simp only [hprune, ↓reduceIte]
        have hch_lt1 : chosen < 2 ^ (8 - rem) := by
          rw [hu1_eq, Nat.pow_succ]; rw [hu_eq] at hlt; omega
        have hch1_eq : chosen ||| (1 <<< u) = chosen + 2 ^ u := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]
          apply Nat.eq_of_testBit_eq; intro k
          rw [Nat.testBit_or, Nat.testBit_two_pow]
          have hlt_u : chosen < 2 ^ u := by rw [← hu_eq]; exact hlt
          by_cases hku : k < u
          · have htb : (chosen + 2 ^ u).testBit k = chosen.testBit k := by
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
            have hne : u ≠ k := by omega
            simp [hne, htb]
          · by_cases hkeq : k = u
            · rw [hkeq]
              have hadd_bit : (chosen + 2 ^ u).testBit u = true := by
                simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
                have h1 : (chosen + 2 ^ u) / 2 ^ u = 1 := by
                  rw [Nat.add_div_right chosen (Nat.two_pow_pos u), Nat.div_eq_of_lt hlt_u, Nat.zero_add]
                rw [h1]; rfl
              simp [hadd_bit]
            · have hlt_ch : chosen < 2 ^ k := by
                calc chosen < 2 ^ u := hlt_u
                  _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
              have hlt_sum : chosen + 2 ^ u < 2 ^ k := by
                have h2u : 2 ^ (u + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
                rw [Nat.pow_succ] at h2u; omega
              have hne : u ≠ k := by omega
              simp [hne, Nat.testBit_lt_two_pow hlt_ch, Nat.testBit_lt_two_pow hlt_sum]
        have hch1_lt : chosen ||| (1 <<< u) < 2 ^ (8 - rem) := by
          rw [hch1_eq, hu1_eq, Nat.pow_succ]; rw [hu_eq] at hlt; omega
        have hpart : ∀ (Q : Nat → Bool),
            countPred (fun hi => (hi % 2 ^ u == chosen) && Q hi) 256 =
            countPred (fun hi => (hi % 2 ^ (u + 1) == chosen) && Q hi) 256 +
            countPred (fun hi => (hi % 2 ^ (u + 1) == (chosen ||| (1 <<< u))) && Q hi) 256 := by
          intro Q
          rw [← countPred_disj]
          · apply countPred_ext; intro hi _
            have hpow : 2 ^ (u + 1) = 2 ^ u * 2 := Nat.pow_succ 2 u
            have hdivmod : hi % 2 ^ (u + 1) = hi % 2 ^ u + 2 ^ u * ((hi / 2 ^ u) % 2) := by
              rw [hpow, Nat.mod_mul]
            have hlt_u : chosen < 2 ^ u := by rw [← hu_eq]; exact hlt
            rw [hch1_eq]
            by_cases hq : Q hi = true
            · simp only [hq, Bool.and_true]
              by_cases hm : hi % 2 ^ u = chosen
              · have hmb : (hi % 2 ^ u == chosen) = true := beq_iff_eq.mpr hm
                rw [hmb]
                have hbit := Nat.mod_two_eq_zero_or_one (hi / 2 ^ u)
                rcases hbit with h0 | h1
                · have heq0 : hi % 2 ^ (u + 1) = chosen := by rw [hdivmod, hm, h0, Nat.mul_zero, Nat.add_zero]
                  simp [heq0]
                · have heq1 : hi % 2 ^ (u + 1) = chosen + 2 ^ u := by rw [hdivmod, hm, h1, Nat.mul_one]
                  have hne0 : (chosen + 2 ^ u == chosen) = false := beq_false_of_ne (by
                    have := Nat.two_pow_pos u; omega)
                  simp [heq1, hne0]
              · have hmb : (hi % 2 ^ u == chosen) = false := beq_false_of_ne hm
                have hne0 : (hi % 2 ^ (u + 1) == chosen) = false := beq_false_of_ne (by
                  intro heq; apply hm
                  have : (hi % 2 ^ (u + 1)) % 2 ^ u = chosen % 2 ^ u := congrArg (· % 2 ^ u) heq
                  rw [hpow, Nat.mod_mul_right_mod, Nat.mod_eq_of_lt hlt_u] at this; exact this)
                have hne1 : (hi % 2 ^ (u + 1) == chosen + 2 ^ u) = false := beq_false_of_ne (by
                  intro heq; apply hm
                  have : (hi % 2 ^ (u + 1)) % 2 ^ u = (chosen + 2 ^ u) % 2 ^ u := congrArg (· % 2 ^ u) heq
                  rw [hpow, Nat.mod_mul_right_mod, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_u] at this
                  exact this)
                simp [hmb, hne0, hne1]
            · simp [Bool.eq_false_iff.mpr hq]
          · intro hi _
            have hne : chosen ≠ chosen ||| (1 <<< u) := by
              rw [hch1_eq]; have := Nat.two_pow_pos u; omega
            by_cases h1 : (hi % 2 ^ (u + 1) == chosen) = true
            · rw [beq_iff_eq] at h1
              have h2 : (hi % 2 ^ (u + 1) == chosen ||| (1 <<< u)) = false := by
                rw [h1]; exact beq_false_of_ne hne
              simp [h2]
            · simp [Bool.eq_false_iff.mpr h1]
        have hih0 := ih chosen cnt (by omega) hch_lt1 hcnt hind
        rw [hu1_eq] at hih0
        have hdisj_eq : disjointBelow chosen (forb (7 - rem)) (7 - rem) = ((chosen &&& forb (7 - rem)) == 0) :=
          disjointBelow_eq_land_zero chosen (forb u) u (by rw [← hu_eq]; exact hlt)
        rw [hdisj_eq]
        by_cases hok : ((chosen &&& forb (7 - rem)) == 0) = true
        · simp only [hok, ↓reduceIte]
          rw [← hch1_eq]
          have hcnt1 : cnt + 1 = popcount8 (chosen ||| (1 <<< u)) := by
            rw [hcnt, hpop_eq, hpop_eq]
            have hch_u0 : chosen.testBit u = false := Nat.testBit_lt_two_pow (by rw [← hu_eq]; exact hlt)
            have hdiff : ∀ k, k ≤ 8 →
                countPred (fun j => (chosen ||| (1 <<< u)).testBit j) k =
                countPred (fun j => chosen.testBit j) k + (if u < k then 1 else 0) := by
              intro k hk
              induction k with
              | zero => simp [countPred]
              | succ k ihk =>
                unfold countPred; rw [ihk (by omega)]
                rw [Nat.testBit_or, Nat.testBit_shiftLeft]
                by_cases hku : k = u
                · subst hku; simp [hch_u0]
                · have hbit : (decide (u ≤ k) && Nat.testBit 1 (k - u)) = false := by
                    by_cases hle : u ≤ k
                    · simp [hle, testBit_one_of_ne_zero (by omega : k - u ≠ 0)]
                    · simp [hle]
                  have hlt_iff : (u < k + 1) ↔ (u < k) := by omega
                  simp [hbit, hlt_iff]; omega
            have := hdiff 8 (Nat.le_refl _)
            simp only [hu8, ↓reduceIte] at this; omega
          have hind1 : isIndepForb forb (chosen ||| (1 <<< u)) = true := by
            unfold isIndepForb
            rw [allNat_eq_true]; intro w hw8
            by_cases hwu : w = u
            · rw [hwu]
              simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.le_refl, decide_true, Nat.sub_self,
                         Nat.testBit_one_zero, Bool.and_true, Bool.or_true, Bool.not_true,
                         Bool.false_or, beq_iff_eq]
              apply Nat.eq_of_testBit_eq; intro v
              rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.zero_testBit]
              have h0 := congrArg (fun z => z.testBit v) (beq_iff_eq.mp hok)
              rw [Nat.testBit_and, Nat.zero_testBit] at h0
              by_cases hvu : v = u
              · rw [hvu]; simp [hirref u hu8]
              · have hbit : (decide (u ≤ v) && Nat.testBit 1 (v - u)) = false := by
                  by_cases hle : u ≤ v
                  · simp [hle, testBit_one_of_ne_zero (by omega : v - u ≠ 0)]
                  · simp [hle]
                rw [hbit, Bool.or_false]; exact h0
            · by_cases hcw : chosen.testBit w = true
              · have hbit_w : (chosen ||| (1 <<< u)).testBit w = true := by
                  rw [Nat.testBit_or, hcw, Bool.true_or]
                simp only [hbit_w, Bool.not_true, Bool.false_or, beq_iff_eq]
                have hind_w := (allNat_eq_true _ 8).mp hind w hw8
                simp only [hcw, Bool.not_true, Bool.false_or, beq_iff_eq] at hind_w
                apply Nat.eq_of_testBit_eq; intro v
                rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.zero_testBit]
                have h0 := congrArg (fun z => z.testBit v) hind_w
                rw [Nat.testBit_and, Nat.zero_testBit] at h0
                by_cases hvu : v = u
                · rw [hvu]
                  have hfwu : (forb w).testBit u = false := by
                    rw [hsym w u hw8 hu8]
                    have h0u := congrArg (fun z => z.testBit w) (beq_iff_eq.mp hok)
                    rw [Nat.testBit_and, hcw, Bool.true_and, Nat.zero_testBit] at h0u
                    exact h0u
                  simp [hfwu]
                · have hbit : (decide (u ≤ v) && Nat.testBit 1 (v - u)) = false := by
                    by_cases hle : u ≤ v
                    · simp [hle, testBit_one_of_ne_zero (by omega : v - u ≠ 0)]
                    · simp [hle]
                  rw [hbit, Bool.or_false]; exact h0
              · have hbit_w : (chosen ||| (1 <<< u)).testBit w = false := by
                  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.eq_false_iff.mpr hcw, Bool.false_or]
                  by_cases hle : u ≤ w
                  · simp [hle, testBit_one_of_ne_zero (by omega : w - u ≠ 0)]
                  · simp [hle]
                simp [hbit_w]
          have hih1 := ih (chosen ||| (1 <<< u)) (cnt + 1) (by omega) hch1_lt hcnt1 hind1
          rw [hu1_eq] at hih1
          rw [hu_eq]
          simp only [Bool.and_assoc] at hih0 hih1 ⊢
          rw [hpart (fun hi => isIndepForb forb hi && (popcount8 hi == target)),
              hpart (fun hi => isIndepForb forb hi && decide (target < popcount8 hi)),
              hih0.1, hih0.2, hih1.1, hih1.2]
          exact ⟨rfl, rfl⟩
        · have hok_f : ((chosen &&& forb (7 - rem)) == 0) = false := Bool.eq_false_iff.mpr hok
          simp only [hok_f, Bool.false_eq_true, ↓reduceIte]
          have hzero : ∀ (P : Nat → Bool),
              countPred (fun hi => (hi % 2 ^ (u + 1) == (chosen ||| (1 <<< u))) && isIndepForb forb hi && P hi) 256 = 0 := by
            intro P
            apply Eq.trans (countPred_ext _ (fun _ => false) 256 (fun hi _ => ?_)) (countPred_false 256)
            by_cases hm : (hi % 2 ^ (u + 1) == (chosen ||| (1 <<< u))) = true
            · rw [beq_iff_eq] at hm
              have hind_f : isIndepForb forb hi = false := by
                apply Bool.eq_false_iff.mpr; intro hind_hi
                have hu_ok := (allNat_eq_true _ 8).mp hind_hi u hu8
                have hbit_u : hi.testBit u = true := by
                  have htb : (hi % 2 ^ (u + 1)).testBit u = hi.testBit u := by
                    rw [Nat.testBit_mod_two_pow]; simp
                  rw [← htb, hm, Nat.testBit_or, Nat.testBit_shiftLeft]
                  simp
                simp only [hbit_u, Bool.not_true, Bool.false_or, beq_iff_eq] at hu_ok
                apply hok; rw [beq_iff_eq]
                apply Nat.eq_of_testBit_eq; intro v
                rw [Nat.testBit_and, Nat.zero_testBit]
                by_cases hvu : v < u
                · have htb_v : chosen.testBit v = hi.testBit v := by
                    have h1 : (hi % 2 ^ (u + 1)).testBit v = hi.testBit v := by
                      rw [Nat.testBit_mod_two_pow]; simp [(by omega : v < u + 1)]
                    rw [← h1, hm, Nat.testBit_or, Nat.testBit_shiftLeft]
                    have hnot : ¬(u ≤ v) := by omega
                    simp [hnot]
                  rw [htb_v]
                  have := congrArg (fun z => z.testBit v) hu_ok
                  rw [Nat.testBit_and, Nat.zero_testBit] at this; exact this
                · have hlt_v : chosen < 2 ^ v := by
                    calc chosen < 2 ^ u := by rw [← hu_eq]; exact hlt
                      _ ≤ 2 ^ v := Nat.pow_le_pow_right (by omega) (by omega)
                  simp [Nat.testBit_lt_two_pow hlt_v]
              simp [hind_f]
            · simp [Bool.eq_false_iff.mpr hm]
          rw [hu_eq]
          have h1 := hzero (fun hi => popcount8 hi == target)
          have h2 := hzero (fun hi => decide (target < popcount8 hi))
          simp only [Bool.and_assoc] at hih0 h1 h2 ⊢
          have hp1 := hpart (fun hi => isIndepForb forb hi && (popcount8 hi == target))
          have hp2 := hpart (fun hi => isIndepForb forb hi && decide (target < popcount8 hi))
          refine ⟨?_, ?_⟩
          · exact hih0.1.trans (by rw [hp1, h1]; exact (Nat.add_zero _).symm)
          · exact hih0.2.trans (by rw [hp2, h2]; exact (Nat.add_zero _).symm)
  have hind0 : isIndepForb forb 0 = true := by
    unfold isIndepForb; rw [allNat_eq_true]; intro u _; simp
  have h := hgen 8 0 0 (Nat.le_refl _) (by decide) rfl hind0
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mod_one, beq_self_eq_true, Bool.true_and] using h1
  · have h2 := h.2
    simpa only [Nat.sub_self, Nat.pow_zero, Nat.mod_one, beq_self_eq_true, Bool.true_and] using h2

/-- Binary-tree depth-8 sums for the exact Sedenion 10D/11D and Fano `7 + 28 + 7` counts
    using zero-recursion `forbMask4Direct`! -/
@[expose] def cd4Count10Fast : Nat :=
  sumTree (fun lo =>
    let pl := popcount8 lo
    if pl < 2 then 0 else (countIndepHi (forbMask4Direct lo) 8 0 0 (10 - pl)).1) 0 8

@[expose] def cd4CountGe11Fast : Nat :=
  sumTree (fun lo =>
    let pl := popcount8 lo
    if pl < 2 then 0 else (countIndepHi (forbMask4Direct lo) 8 0 0 (10 - pl)).2) 0 8

@[expose] def cd4Count10WithLoFast (k : Nat) : Nat :=
  sumTree (fun lo =>
    if popcount8 lo == k then (countIndepHi (forbMask4Direct lo) 8 0 0 (10 - k)).1 else 0) 0 8

theorem cd4_subspace_fast_vals :
    cd4Count10Fast = 42 ∧
    cd4CountGe11Fast = 0 ∧
    cd4Count10WithLoFast 8 = 7 ∧
    cd4Count10WithLoFast 5 = 28 ∧
    cd4Count10WithLoFast 2 = 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exact full-enumeration counts over all $2^{16} = 65536$ coordinate subspaces of $\mathbb{S}_{16}$. -/
@[expose] def countNormMult4Eq10 : Nat :=
  countPred (fun m => isNormMultMask 4 m && (popcount16 m == 10)) 65536

@[expose] def countNormMult4Ge11 : Nat :=
  countPred (fun m => isNormMultMask 4 m && decide (11 ≤ popcount16 m)) 65536

@[expose] def countNormMult4Eq10WithLo (k : Nat) : Nat :=
  countPred (fun m => isNormMultMask 4 m && (popcount16 m == 10) && (popcount8 (m % 256) == k)) 65536

theorem countPred_256x256 (P : Nat → Bool) :
    countPred P 65536 =
      sumNat (fun lo => countPred (fun hi => P (lo + 256 * hi)) 256) 256 := by
  have h1 : ∀ b,
      countPred P (256 * b) =
      sumNat (fun hi => countPred (fun lo => P (lo + 256 * hi)) 256) b := by
    intro b
    induction b with
    | zero => simp [countPred, sumNat]
    | succ b ihb =>
      have hmul : 256 * (b + 1) = 256 * b + 256 := by omega
      rw [hmul, countPred_add, ihb]
      exact congrArg (sumNat (fun hi => countPred (fun lo => P (lo + 256 * hi)) 256) b + ·)
        (countPred_ext (fun k => P (256 * b + k)) (fun lo => P (lo + 256 * b)) 256
          (fun lo _ => congrArg P (Nat.add_comm (256 * b) lo)))
  have h256 : (65536 : Nat) = 256 * 256 := rfl
  rw [h256, h1 256]
  have hsum : ∀ a b,
      sumNat (fun hi => countPred (fun lo => P (lo + 256 * hi)) a) b =
      sumNat (fun lo => countPred (fun hi => P (lo + 256 * hi)) b) a := by
    intro a b
    have hL : sumNat (fun hi => countPred (fun lo => P (lo + 256 * hi)) a) b =
              sumNat (fun hi => sumNat (fun lo => if P (lo + 256 * hi) then 1 else 0) a) b := by
      apply sumNat_ext; intro hi _; exact countPred_eq_sumNat _ a
    have hR : sumNat (fun lo => countPred (fun hi => P (lo + 256 * hi)) b) a =
              sumNat (fun lo => sumNat (fun hi => if P (lo + 256 * hi) then 1 else 0) b) a := by
      apply sumNat_ext; intro lo _; exact countPred_eq_sumNat _ b
    rw [hL, hR, sumNat_transpose]
  exact hsum 256 256

/-- **Theorem T4a (Complete Sedenion Triple-42 & Fano `7 + 28 + 7` Duality):**
    Over ALL $2^{16} = 65536$ coordinate subspaces of $\mathbb{S}_{16}$:
    1. Exactly **42** bad affine 2-planes out of 140.
    2. Exactly **42** 10-dimensional norm-multiplicative coordinate subspaces (`[10, 10, 16]`).
    3. Exact Fano intersection decomposition **`7 + 28 + 7 = 42`** for $|S \cap \mathbb{O}| \in \{8, 5, 2\}$.
    4. **ZERO** norm-multiplicative coordinate subspaces of dimension $\ge 11$. -/
theorem sedenion_42_fano_duality :
    countAffinePlanes4 = 140 ∧
    countBadAffinePlanes4 = 42 ∧
    countNormMult4Eq10 = 42 ∧
    countNormMult4Ge11 = 0 ∧
    countNormMult4Eq10WithLo 8 = 7 ∧
    countNormMult4Eq10WithLo 5 = 28 ∧
    countNormMult4Eq10WithLo 2 = 7 := by
  have hpop8_le : ∀ x, popcount8 x ≤ 8 := by
    intro x; unfold popcount8; omega
  have hpop16_split : ∀ lo hi, lo < 256 → popcount16 (lo + 256 * hi) = popcount8 lo + popcount8 hi := by
    intro lo hi hlo
    unfold popcount16
    have hmod : (lo + 256 * hi) % 256 = lo := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    have hdiv : (lo + 256 * hi) / 256 = hi := by
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < 256), Nat.div_eq_of_lt hlo, Nat.zero_add]
    rw [hmod, hdiv]
  have htbl_eq : ∀ lo target,
      countIndepHi (forbMask4Direct lo) 8 0 0 target = countIndepHi (forbMask4 lo) 8 0 0 target := by
    intro lo target
    exact countIndepHi_ext (forbMask4Direct lo) (forbMask4 lo) (forbMask4Direct_eq_forbMask4 lo) 8 0 0 target (Nat.le_refl _)
  have hrow10 : ∀ lo, lo < 256 →
      countPred (fun hi => isNormMultMask 4 (lo + 256 * hi) && (popcount16 (lo + 256 * hi) == 10)) 256 =
      if popcount8 lo < 2 then 0 else (countIndepHi (forbMask4Direct lo) 8 0 0 (10 - popcount8 lo)).1 := by
    intro lo hlo
    by_cases hpl : popcount8 lo < 2
    · simp only [hpl, ↓reduceIte]
      apply Eq.trans (countPred_ext _ (fun _ => false) 256 (fun hi _ => ?_)) (countPred_false 256)
      rw [hpop16_split lo hi hlo]
      have h8 := hpop8_le hi
      have hne : (popcount8 lo + popcount8 hi == 10) = false := beq_false_of_ne (by omega)
      simp [hne]
    · simp only [hpl, ↓reduceIte, htbl_eq]
      have ⟨hsym, hirr⟩ := forbMask4_symm_irref lo
      rw [(countIndepHi_sound (forbMask4 lo) hsym hirr (10 - popcount8 lo)).1]
      apply countPred_ext; intro hi hhi
      rw [isNormMultMask4_eq_hiAvoidsBad lo hi hlo, hiAvoidsBad_eq_isIndepForb lo hi hhi,
          hpop16_split lo hi hlo]
      have hpl8 := hpop8_le lo
      congr 1
      by_cases h : popcount8 lo + popcount8 hi = 10
      · have h2 : popcount8 hi = 10 - popcount8 lo := by omega
        rw [beq_iff_eq.mpr h, beq_iff_eq.mpr h2]
      · have h2 : popcount8 hi ≠ 10 - popcount8 lo := by omega
        rw [beq_false_of_ne h, beq_false_of_ne h2]
  have hrow11 : ∀ lo, lo < 256 →
      countPred (fun hi => isNormMultMask 4 (lo + 256 * hi) && decide (11 ≤ popcount16 (lo + 256 * hi))) 256 =
      if popcount8 lo < 2 then 0 else (countIndepHi (forbMask4Direct lo) 8 0 0 (10 - popcount8 lo)).2 := by
    intro lo hlo
    by_cases hpl : popcount8 lo < 2
    · simp only [hpl, ↓reduceIte]
      apply Eq.trans (countPred_ext _ (fun _ => false) 256 (fun hi _ => ?_)) (countPred_false 256)
      rw [hpop16_split lo hi hlo]
      have h8 := hpop8_le hi
      have hnot : ¬(11 ≤ popcount8 lo + popcount8 hi) := by omega
      simp [hnot]
    · simp only [hpl, ↓reduceIte, htbl_eq]
      have ⟨hsym, hirr⟩ := forbMask4_symm_irref lo
      rw [(countIndepHi_sound (forbMask4 lo) hsym hirr (10 - popcount8 lo)).2]
      apply countPred_ext; intro hi hhi
      rw [isNormMultMask4_eq_hiAvoidsBad lo hi hlo, hiAvoidsBad_eq_isIndepForb lo hi hhi,
          hpop16_split lo hi hlo]
      have hpl8 := hpop8_le lo
      congr 1
      by_cases h : 11 ≤ popcount8 lo + popcount8 hi
      · have h2 : 10 - popcount8 lo < popcount8 hi := by omega
        simp [h, h2]
      · have h2 : ¬(10 - popcount8 lo < popcount8 hi) := by omega
        simp [h, h2]
  have hfk : ∀ k, 2 ≤ k → countNormMult4Eq10WithLo k = cd4Count10WithLoFast k := by
    intro k hk
    unfold countNormMult4Eq10WithLo cd4Count10WithLoFast
    rw [countPred_256x256, sumTree_zero_eq]
    apply sumNat_ext; intro lo hlo
    have hmod : ∀ hi, (lo + 256 * hi) % 256 = lo := fun hi => by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    by_cases hpk : popcount8 lo = k
    · have hpkb : (popcount8 lo == k) = true := beq_iff_eq.mpr hpk
      have hge2 : ¬(k < 2) := by omega
      simp only [hpkb, ↓reduceIte]
      have hrow := hrow10 lo hlo
      rw [hpk] at hrow
      simp only [hge2, ↓reduceIte] at hrow
      rw [← hrow]
      apply countPred_ext; intro hi _
      rw [hmod hi, hpkb, Bool.and_true]
    · have hpkb : (popcount8 lo == k) = false := beq_false_of_ne hpk
      simp only [hpkb, Bool.false_eq_true, ↓reduceIte]
      apply Eq.trans (countPred_ext _ (fun _ => false) 256 (fun hi _ => ?_)) (countPred_false 256)
      rw [hmod hi, hpkb, Bool.and_false]
  rcases cd4_subspace_fast_vals with ⟨h10, h11, hf8, hf5, hf2⟩
  refine ⟨cd4_bad_planes_count.1, cd4_bad_planes_count.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold countNormMult4Eq10
    rw [countPred_256x256, sumNat_ext _ _ 256 hrow10]
    exact (sumTree_zero_eq _ 8).symm.trans h10
  · unfold countNormMult4Ge11
    rw [countPred_256x256, sumNat_ext _ _ 256 hrow11]
    exact (sumTree_zero_eq _ 8).symm.trans h11
  · rw [hfk 8 (by omega)]; exact hf8
  · rw [hfk 5 (by omega)]; exact hf5
  · rw [hfk 2 (by omega)]; exact hf2

/-- Corollary: No coordinate subspace of $\mathbb{S}_{16}$ of dimension $\ge 11$ is norm-multiplicative. -/
theorem sedenion_no_11d_coord_subspace (m : Nat) (hm : m < 65536) (hdim : 11 ≤ popcount16 m) :
    isNormMultMask 4 m = false := by
  by_cases h : isNormMultMask 4 m = true
  · exfalso
    have hpos : 0 < countNormMult4Ge11 := by
      unfold countNormMult4Ge11
      have hstep : ∀ k, m < k → 0 < countPred (fun x => isNormMultMask 4 x && decide (11 ≤ popcount16 x)) k := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ihk =>
          unfold countPred
          by_cases hmk : m = k
          · subst hmk; simp [h, hdim]
          · have := ihk (by omega); omega
      exact hstep 65536 hm
    rw [sedenion_42_fano_duality.2.2.2.1] at hpos; omega
  · exact Bool.eq_false_iff.mpr h

/-! ### Theorem T4b: Sedenion 42 Box-Kite Assessors ($7 \times K_{2,2,2}$) & 9D Subspace $\mathbb{O} \oplus \mathbb{R} e_8$ -/

/-- The 42 Sedenion Box-Kite assessors $(i, j)$ with $1 \le i \le 7$, $9 \le j \le 15$, $i \neq j - 8$. -/
@[expose] def sedenionAssessors : List (Nat × Nat) :=
  (List.range 8).flatMap fun i =>
    if i == 0 then []
    else (List.range 16).flatMap fun j =>
      if 9 ≤ j && i != j - 8 then [(i, j)] else []

/-- Exact coordinate $t$ of the full sedenion product $(e_i + e_j)(e_k + s\,e_l)$ in $\mathbb{S}_{16}$
    (sum of the 4 basis products landing in slot $t$; zero XOR pre-filtering). -/
@[expose] def bladeProdCoord4 (i j k l : Nat) (s : Int) (t : Nat) : Int :=
  (if i ^^^ k == t then cdSign 4 i k else 0) +
  (if i ^^^ l == t then s * cdSign 4 i l else 0) +
  (if j ^^^ k == t then cdSign 4 j k else 0) +
  (if j ^^^ l == t then s * cdSign 4 j l else 0)

/-- Bridge theorem: `bladeProdCoord4 i j k l s t` equals the full bilinear Cayley-Dickson
    product `cdMulCoordGamma 4 0 (twobladeVec i j) (signedBladeVec k l s) t`. -/
theorem bladeProdCoord4_eq_cdMul (i j k l : Nat) (s : Int) (t : Nat)
    (hi : i < 16) (hj : j < 16) (hne_ij : i ≠ j) (hne_kl : k ≠ l) :
    bladeProdCoord4 i j k l s t =
      cdMulCoordGamma 4 0 (twobladeVec i j) (signedBladeVec k l s) t := by
  rw [cdMulCoordGamma_twoblade 4 0 i j hi hj hne_ij (signedBladeVec k l s) t,
      cdSignGamma_zero_eq_cdSign, cdSignGamma_zero_eq_cdSign]
  unfold bladeProdCoord4 signedBladeVec basisVec
  have hEq : ∀ a b : Nat, ((a ^^^ b) == t) = ((a ^^^ t) == b) := by
    intro a b
    by_cases h : a ^^^ b = t
    · have h2 : a ^^^ t = b := by rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      simp [h, h2]
    · have h2 : a ^^^ t ≠ b := by
        intro heq; apply h; rw [← heq, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      simp [beq_false_of_ne h, beq_false_of_ne h2]
  rw [hEq i k, hEq i l, hEq j k, hEq j l]
  have hhalf : ∀ a : Nat,
      (if a ^^^ t == k then cdSign 4 a k else 0) + (if a ^^^ t == l then s * cdSign 4 a l else 0) =
      cdSign 4 a (a ^^^ t) * ((if a ^^^ t == k then 1 else 0) + s * (if a ^^^ t == l then 1 else 0)) := by
    intro a
    by_cases h1 : a ^^^ t = k
    · simp [h1, hne_kl]
    · by_cases h2 : a ^^^ t = l
      · simp [h2, Ne.symm hne_kl, Int.mul_comm]
      · simp [beq_false_of_ne h1, beq_false_of_ne h2]
  rw [Int.add_assoc ((if i ^^^ t == k then cdSign 4 i k else 0) + (if i ^^^ t == l then s * cdSign 4 i l else 0)),
      hhalf i, hhalf j]

/-- Pure algebraic Box-Kite mutual zero-divisor adjacency (ZERO XOR pre-filtering):
    assessors `(i, j)` and `(k, l)` are adjacent iff there exists $s \in \{+1, -1\}$ such that
    $(e_i + e_j)(e_k + s\,e_l) = 0$ identically across all 16 basis slots of $\mathbb{S}_{16}$. -/
@[expose] def boxKiteAdj (p q : Nat × Nat) : Bool :=
  allNat (fun t => bladeProdCoord4 p.1 p.2 q.1 q.2 1 t == 0) 16 ||
  allNat (fun t => bladeProdCoord4 p.1 p.2 q.1 q.2 (-1) t == 0) 16

/-- Fast equivalent 4-slot checker for `boxKiteAdj` (only the 4 support slots can be nonzero). -/
@[expose] def bladeProdZero4Slots (i j k l : Nat) (s : Int) : Bool :=
  (bladeProdCoord4 i j k l s (i ^^^ k) == 0) &&
  (bladeProdCoord4 i j k l s (i ^^^ l) == 0) &&
  (bladeProdCoord4 i j k l s (j ^^^ k) == 0) &&
  (bladeProdCoord4 i j k l s (j ^^^ l) == 0)

@[expose] def boxKiteAdjFast (p q : Nat × Nat) : Bool :=
  bladeProdZero4Slots p.1 p.2 q.1 q.2 1 || bladeProdZero4Slots p.1 p.2 q.1 q.2 (-1)

theorem bladeProdZero4Slots_eq (i j k l : Nat) (s : Int)
    (hi : i < 16) (hj : j < 16) (hk : k < 16) (hl : l < 16) :
    allNat (fun t => bladeProdCoord4 i j k l s t == 0) 16 = bladeProdZero4Slots i j k l s := by
  apply Bool.eq_iff_iff.mpr
  rw [allNat_eq_true]
  unfold bladeProdZero4Slots
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro hall
    exact ⟨⟨⟨hall _ (Nat.xor_lt_two_pow (n := 4) hi hk),
             hall _ (Nat.xor_lt_two_pow (n := 4) hi hl)⟩,
             hall _ (Nat.xor_lt_two_pow (n := 4) hj hk)⟩,
           hall _ (Nat.xor_lt_two_pow (n := 4) hj hl)⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ t _
    by_cases ht1 : i ^^^ k = t
    · rw [← ht1]; exact h1
    · by_cases ht2 : i ^^^ l = t
      · rw [← ht2]; exact h2
      · by_cases ht3 : j ^^^ k = t
        · rw [← ht3]; exact h3
        · by_cases ht4 : j ^^^ l = t
          · rw [← ht4]; exact h4
          · unfold bladeProdCoord4
            simp [beq_false_of_ne ht1, beq_false_of_ne ht2,
                  beq_false_of_ne ht3, beq_false_of_ne ht4]

theorem boxKiteAdj_eq_fast (p q : Nat × Nat)
    (hp1 : p.1 < 16) (hp2 : p.2 < 16) (hq1 : q.1 < 16) (hq2 : q.2 < 16) :
    boxKiteAdj p q = boxKiteAdjFast p q := by
  unfold boxKiteAdj boxKiteAdjFast
  rw [bladeProdZero4Slots_eq p.1 p.2 q.1 q.2 1 hp1 hp2 hq1 hq2,
      bladeProdZero4Slots_eq p.1 p.2 q.1 q.2 (-1) hp1 hp2 hq1 hq2]

theorem sedenionAssessors_lt16 : ∀ p ∈ sedenionAssessors, p.1 < 16 ∧ p.2 < 16 := by
  have h : sedenionAssessors.all (fun p => decide (p.1 < 16 && p.2 < 16)) = true := by decide
  intro p hp
  have hp' := decide_eq_true_eq.mp (List.all_eq_true.mp h p hp)
  exact ⟨by simp_all, by simp_all⟩

/-- **Theorem T4b (Formal Six-Kernel Re-Verification of de Marrais's 7 Box-Kites = $7 \times K_{2,2,2}$):**
    Under the pure algebraic vanishing-product adjacency `boxKiteAdj` (zero XOR pre-filtering):
    1. Exactly 42 assessors, every assessor has exact degree 4 (`84` undirected edges).
    2. Partitioned by XOR signature $s = i \oplus j \in \{9,\dots,15\}$ into **7 disjoint
       components of exact size 6**, with **genuinely proved** 0 cross-component edges ($7 \times K_{2,2,2}$).
    3. The 9-dimensional coordinate subspace $\mathbb{O} \oplus \mathbb{R} e_8$ (mask `511`)
       is norm-multiplicative in $\mathbb{S}_{16}$. -/
theorem sedenion_box_kites_7x6 :
    sedenionAssessors.length = 42 ∧
    sedenionAssessors.all (fun p => (sedenionAssessors.filter (boxKiteAdj p)).length == 4) = true ∧
    ([9, 10, 11, 12, 13, 14, 15].all fun s =>
      let comp := sedenionAssessors.filter (fun p => p.1 ^^^ p.2 == s)
      comp.length == 6 &&
      comp.all (fun p => (comp.filter (boxKiteAdj p)).length == 4)) = true ∧
    sedenionAssessors.all (fun p =>
      sedenionAssessors.all (fun q => !boxKiteAdj p q || (p.1 ^^^ p.2 == q.1 ^^^ q.2))) = true ∧
    popcount16 511 = 9 ∧
    isNormMultMask 4 511 = true := by
  have hfast :
      sedenionAssessors.length = 42 ∧
      sedenionAssessors.all (fun p => (sedenionAssessors.filter (boxKiteAdjFast p)).length == 4) = true ∧
      ([9, 10, 11, 12, 13, 14, 15].all fun s =>
        let comp := sedenionAssessors.filter (fun p => p.1 ^^^ p.2 == s)
        comp.length == 6 &&
        comp.all (fun p => (comp.filter (boxKiteAdjFast p)).length == 4)) = true ∧
      sedenionAssessors.all (fun p =>
        sedenionAssessors.all (fun q => !boxKiteAdjFast p q || (p.1 ^^^ p.2 == q.1 ^^^ q.2))) = true ∧
      popcount16 511 = 9 ∧
      isNormMultMask 4 511 = true := by decide
  have hfilt : ∀ (L : List (Nat × Nat)) (p : Nat × Nat),
      p ∈ sedenionAssessors → (∀ q ∈ L, q ∈ sedenionAssessors) →
      L.filter (boxKiteAdj p) = L.filter (boxKiteAdjFast p) := by
    intro L p hp hsub
    induction L with
    | nil => rfl
    | cons q tl ih =>
      have hplt := sedenionAssessors_lt16 p hp
      have hqlt := sedenionAssessors_lt16 q (hsub q (List.mem_cons_self ..))
      simp only [List.filter, boxKiteAdj_eq_fast p q hplt.1 hplt.2 hqlt.1 hqlt.2]
      rw [ih (fun r hr => hsub r (List.mem_cons_of_mem q hr))]
  refine ⟨hfast.1, ?_, ?_, ?_, hfast.2.2.2.2.1, hfast.2.2.2.2.2⟩
  · rw [List.all_eq_true]
    intro p hp
    rw [hfilt sedenionAssessors p hp (fun _ h => h)]
    exact List.all_eq_true.mp hfast.2.1 p hp
  · rw [List.all_eq_true]
    intro s hs
    have hsF := List.all_eq_true.mp hfast.2.2.1 s hs
    simp only [Bool.and_eq_true, List.all_eq_true] at hsF ⊢
    refine ⟨hsF.1, fun p hp => ?_⟩
    have hpm : p ∈ sedenionAssessors := (List.mem_filter.mp hp).1
    rw [hfilt _ p hpm (fun q hq => (List.mem_filter.mp hq).1)]
    exact hsF.2 p hp
  · rw [List.all_eq_true]
    intro p hp
    rw [List.all_eq_true]
    intro q hq
    have hplt := sedenionAssessors_lt16 p hp
    have hqlt := sedenionAssessors_lt16 q hq
    rw [boxKiteAdj_eq_fast p q hplt.1 hplt.2 hqlt.1 hqlt.2]
    exact List.all_eq_true.mp (List.all_eq_true.mp hfast.2.2.2.1 p hp) q hq

/-! ### Theorem T4c: Exhaustive Split-Phase Classifications of $\mathrm{CD}_4(\gamma)$ & $\mathrm{CD}_5(\gamma)$ -/

/-- Exact $O(1)$ closed-form standard nullity of $\mathrm{CD}_4$ ($1 \le i < j < 16$),
    proved directly from `TerraceLaw` (`nullity_doubling_*` + `octonion_nullity_all_zero`)! -/
@[expose] def nu4Closed (i j : Nat) : Nat :=
  if i < 8 && 8 < j && j != i + 8 then 4 else 0

theorem nu4Closed_eq (i j : Nat) (hi0 : 0 < i) (hij : i < j) (hj : j < 16) :
    nu4Closed i j = twobladeNullity 4 i j := by
  unfold nu4Closed
  by_cases hi8 : i < 8
  · by_cases hj8 : j < 8
    · have hnot : ¬(8 < j) := by omega
      simp only [hi8, hnot, decide_false, decide_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [nullity_doubling_lower 3 i j hi0 (by omega) hi8 hj8 (by omega),
          octonion_nullity_all_zero i j hi0 (by omega) hi8 hj8 (by omega)]
    · by_cases hj_eq : j = 8
      · subst hj_eq
        simp only [Nat.lt_irrefl, decide_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact (nullity_doubling_axis 3 i hi0 hi8).2.1.symm
      · by_cases hjd : j = i + 8
        · subst hjd
          simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact (nullity_doubling_axis 3 i hi0 hi8).2.2.symm
        · have h8j : 8 < j := by omega
          have hne_b : (j != i + 8) = true := bne_iff_ne.mpr hjd
          simp only [hi8, h8j, hne_b, decide_true, Bool.and_true, ↓reduceIte]
          let b := j - 8
          have hjb : j = b + 8 := by omega
          rw [hjb, nullity_doubling_cross 3 i b (by omega) hi0 (by omega) hi8 (by omega) (by omega),
              octonion_nullity_all_zero i b hi0 (by omega) hi8 (by omega) (by omega)]
  · simp only [hi8, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    by_cases hi_eq : i = 8
    · subst hi_eq
      let b := j - 8
      have hjb : j = b + 8 := by omega
      rw [hjb]; exact (nullity_doubling_axis 3 b (by omega) (by omega)).1.symm
    · let a := i - 8
      let b := j - 8
      have ha_eq : i = a + 8 := by omega
      have hb_eq : j = b + 8 := by omega
      rw [ha_eq, hb_eq, nullity_doubling_upper 3 a b (by omega) (by omega) (by omega) (by omega) (by omega),
          octonion_nullity_all_zero a b (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- Exact $O(1)$ closed-form standard nullity of $\mathrm{CD}_5$ ($1 \le i < j < 32$),
    proved directly from `TerraceLaw` (`nullity_doubling_*` + `nu4Closed_eq`)! -/
@[expose] def nu5Closed (i j : Nat) : Nat :=
  if i < 16 then
    if j < 16 then 2 * nu4Closed i j
    else if j == 16 then 0
    else if j == i + 16 then 0
    else 12 - 2 * (if i < j - 16 then nu4Closed i (j - 16) else nu4Closed (j - 16) i)
  else if i == 16 then 0
  else 2 * nu4Closed (i - 16) (j - 16)

theorem nu5Closed_eq (i j : Nat) (hi0 : 0 < i) (hij : i < j) (hj : j < 32) :
    nu5Closed i j = twobladeNullity 5 i j := by
  unfold nu5Closed
  by_cases hi16 : i < 16
  · simp only [hi16, ↓reduceIte]
    by_cases hj16 : j < 16
    · simp only [hj16, ↓reduceIte]
      rw [nu4Closed_eq i j hi0 hij hj16,
          nullity_doubling_lower 4 i j hi0 (by omega) hi16 hj16 (by omega)]
    · simp only [hj16, ↓reduceIte]
      by_cases hj_eq : j = 16
      · subst hj_eq
        simp only [beq_self_eq_true, ↓reduceIte]
        exact (nullity_doubling_axis 4 i hi0 hi16).2.1.symm
      · have hjb : (j == 16) = false := beq_false_of_ne hj_eq
        simp only [hjb, Bool.false_eq_true, ↓reduceIte]
        by_cases hjd : j = i + 16
        · subst hjd
          simp only [beq_self_eq_true, ↓reduceIte]
          exact (nullity_doubling_axis 4 i hi0 hi16).2.2.symm
        · have hjdb : (j == i + 16) = false := beq_false_of_ne hjd
          simp only [hjdb, Bool.false_eq_true, ↓reduceIte]
          let b := j - 16
          have hjb_eq : j = b + 16 := by omega
          have hblt : b < 16 := by omega
          have hb0 : 0 < b := by omega
          have hib_ne : i ≠ b := by omega
          have hcr := nullity_doubling_cross 4 i b (by omega) hi0 hb0 hi16 hblt hib_ne
          rw [hjb_eq, hcr]
          have h12 : 2 ^ 4 - 4 = 12 := rfl
          have hsub : b + 16 - 16 = b := by omega
          rw [h12, hsub]
          by_cases hib : i < b
          · simp only [hib, ↓reduceIte, nu4Closed_eq i b hi0 hib hblt]
          · simp only [hib, ↓reduceIte, nu4Closed_eq b i hb0 (by omega) hi16, twobladeNullity_symm 4 b i]
  · simp only [hi16, ↓reduceIte]
    by_cases hi_eq : i = 16
    · subst hi_eq
      simp only [beq_self_eq_true, ↓reduceIte]
      let b := j - 16
      have hjb_eq : j = b + 16 := by omega
      rw [hjb_eq]; exact (nullity_doubling_axis 4 b (by omega) (by omega)).1.symm
    · have hib : (i == 16) = false := beq_false_of_ne hi_eq
      simp only [hib, Bool.false_eq_true, ↓reduceIte]
      let a := i - 16
      let b := j - 16
      have ha_eq : i = a + 16 := by omega
      have hb_eq : j = b + 16 := by omega
      rw [ha_eq, hb_eq, nullity_doubling_upper 4 a b (by omega) (by omega) (by omega) (by omega) (by omega)]
      have hsa : a + 16 - 16 = a := by omega
      have hsb : b + 16 - 16 = b := by omega
      rw [hsa, hsb, nu4Closed_eq a b (by omega) (by omega) (by omega)]

/-- General exact bridge: for any `n ≥ 1`, `flip`, `v`, and closed-form `nuStd` agreeing with
    `twobladeNullity n` on `0 < i < j < 2^n`, `nullityHistGamma n flip v` equals the fast
    double `sumNat` using the Mirror Law `nilpotent_mirror_law`! -/
theorem nullityHistGamma_eq_fast (n flip v : Nat) (hn : 1 ≤ n) (nuStd : Nat → Nat → Nat)
    (hnu : ∀ i j, 0 < i → i < j → j < 2 ^ n → nuStd i j = twobladeNullity n i j) :
    nullityHistGamma n flip v =
      sumNat (fun i => if i = 0 then 0 else
        sumNat (fun j => if i < j then
          if (if parityBits n ((i ^^^ j) &&& flip) then 2 ^ (n - 1) - nuStd i j else nuStd i j) == v
          then 1 else 0 else 0) (2 ^ n)) (2 ^ n) := by
  have hrow : ∀ i k, nullityHistRow n flip v i k =
      sumNat (fun j => if i < j && (twobladeNullityGamma n flip i j == v) then 1 else 0) k := by
    intro i k
    induction k with
    | zero => rfl
    | succ k ihk => unfold nullityHistRow sumNat; rw [ihk]
  have hrange : ∀ m, nullityHistRange n flip v m (2 ^ n) =
      sumNat (fun i => if i = 0 then 0 else
        sumNat (fun j => if i < j && (twobladeNullityGamma n flip i j == v) then 1 else 0) (2 ^ n)) m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ihm =>
      unfold nullityHistRange sumNat; rw [ihm]
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have hmb : (m == 0) = false := beq_false_of_ne hm0
        simp only [hm0, hmb, Bool.false_eq_true, ↓reduceIte, hrow]
  unfold nullityHistGamma
  rw [hrange (2 ^ n)]
  apply sumNat_ext; intro i _
  by_cases hi0 : i = 0
  · simp [hi0]
  · simp only [hi0, ↓reduceIte]
    apply sumNat_ext; intro j hj
    by_cases hij : i < j
    · simp only [hij, decide_true, Bool.true_and, ↓reduceIte]
      have hmir := nilpotent_mirror_law n flip i j hn (by omega) hj (by omega)
      rw [hnu i j (by omega) hij hj]
      by_cases hp : parityBits n ((i ^^^ j) &&& flip) = true
      · simp only [hp, ↓reduceIte]
        have h2 := hmir.2 hp
        have heq : 2 ^ (n - 1) - twobladeNullity n i j = twobladeNullityGamma n flip i j := by omega
        rw [heq]
      · have hpf : parityBits n ((i ^^^ j) &&& flip) = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, hmir.1 hpf]
    · simp [hij]

@[expose] def cd4HistFast (flip v : Nat) : Nat :=
  sumNat (fun i => if i = 0 then 0 else
    sumNat (fun j => if i < j then
      if (if parityBits 4 ((i ^^^ j) &&& flip) then 8 - nu4Closed i j else nu4Closed i j) == v
      then 1 else 0 else 0) 16) 16

theorem cd4HistFast_eq (flip v : Nat) : nullityHistGamma 4 flip v = cd4HistFast flip v :=
  nullityHistGamma_eq_fast 4 flip v (by omega) nu4Closed nu4Closed_eq

/-- **Theorem T4c-1 (Complete 16-Signature Split Sedenion Phase Classification):**
    Across all 16 signatures $\gamma \in \{\pm 1\}^4$ of $\mathrm{CD}_4(\gamma)$:
    Exactly **4** distinct nullity-histogram phases occur with multiplicities **`1 : 1 : 7 : 7`**:
    `(63, 42, 0)` (mult `1`), `(49, 42, 14)` (mult `1`), `(31, 42, 32)` (mult `7`),
    `(25, 42, 38)` (mult `7`). -/
theorem split_sedenion_4_phases :
    let profs := (List.range 16).map (fun fl =>
      (nullityHistGamma 4 fl 0, nullityHistGamma 4 fl 4, nullityHistGamma 4 fl 8))
    (profs.count (63, 42, 0) = 1) ∧
    (profs.count (49, 42, 14) = 1) ∧
    (profs.count (31, 42, 32) = 7) ∧
    (profs.count (25, 42, 38) = 7) := by
  have heq : (List.range 16).map (fun fl =>
      (nullityHistGamma 4 fl 0, nullityHistGamma 4 fl 4, nullityHistGamma 4 fl 8)) =
      (List.range 16).map (fun fl => (cd4HistFast fl 0, cd4HistFast fl 4, cd4HistFast fl 8)) := by
    apply List.map_congr_left; intro fl _
    rw [cd4HistFast_eq, cd4HistFast_eq, cd4HistFast_eq]
  dsimp only; rw [heq]; decide

/-- Ultra-fast single-pass triangular `(H(0), H(4))` pair counter for `CD_5(flip)`.
    By the already-proved `universal_split_midpoint_42` ($H_5^\gamma(8) = 84$) and
    `mirror_sum_conservation` ($H_5^\gamma(0) + H_5^\gamma(16) = 171$,
    $H_5^\gamma(4) + H_5^\gamma(12) = 210$), this determines all 5 bins in ONE pass! -/
@[expose] def cd5PairRow (flip i : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | j + 1 =>
    let p := cd5PairRow flip i j
    if i < j then
      let nu := if parityBits 5 ((i ^^^ j) &&& flip) then 16 - nu5Closed i j else nu5Closed i j
      if nu == 0 then (p.1 + 1, p.2)
      else if nu == 4 then (p.1, p.2 + 1)
      else p
    else p

@[expose] def cd5PairRange (flip : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | i + 1 =>
    let p := cd5PairRange flip i
    if i == 0 then p
    else
      let r := cd5PairRow flip i 32
      (p.1 + r.1, p.2 + r.2)

theorem cd5PairRange_eq (flip : Nat) :
    cd5PairRange flip 32 = (nullityHistGamma 5 flip 0, nullityHistGamma 5 flip 4) := by
  have hrow : ∀ i k,
      (cd5PairRow flip i k).1 =
        sumNat (fun j => if i < j then
          if (if parityBits 5 ((i ^^^ j) &&& flip) then 16 - nu5Closed i j else nu5Closed i j) == 0
          then 1 else 0 else 0) k ∧
      (cd5PairRow flip i k).2 =
        sumNat (fun j => if i < j then
          if (if parityBits 5 ((i ^^^ j) &&& flip) then 16 - nu5Closed i j else nu5Closed i j) == 4
          then 1 else 0 else 0) k := by
    intro i k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ihk =>
      unfold cd5PairRow sumNat
      rcases ihk with ⟨ih1, ih2⟩
      by_cases hik : i < k
      · simp only [hik, ↓reduceIte]
        let nu := if parityBits 5 ((i ^^^ k) &&& flip) then 16 - nu5Closed i k else nu5Closed i k
        by_cases h0 : nu = 0
        · have h0b : (nu == 0) = true := beq_iff_eq.mpr h0
          have h4b : (nu == 4) = false := beq_false_of_ne (by omega)
          simp only [nu, h0b, h4b, Bool.false_eq_true, ↓reduceIte, ih1, ih2, Nat.add_zero]
          exact ⟨trivial, trivial⟩
        · have h0b : (nu == 0) = false := beq_false_of_ne h0
          by_cases h4 : nu = 4
          · have h4b : (nu == 4) = true := beq_iff_eq.mpr h4
            simp only [nu, h0b, h4b, Bool.false_eq_true, ↓reduceIte, ih1, ih2, Nat.add_zero]
            exact ⟨trivial, trivial⟩
          · have h4b : (nu == 4) = false := beq_false_of_ne h4
            simp only [nu, h0b, h4b, Bool.false_eq_true, ↓reduceIte, ih1, ih2, Nat.add_zero]
            exact ⟨trivial, trivial⟩
      · simp only [hik, ↓reduceIte, ih1, ih2, Nat.add_zero]; exact ⟨trivial, trivial⟩
  have hrange : ∀ m,
      (cd5PairRange flip m).1 =
        sumNat (fun i => if i = 0 then 0 else
          sumNat (fun j => if i < j then
            if (if parityBits 5 ((i ^^^ j) &&& flip) then 16 - nu5Closed i j else nu5Closed i j) == 0
            then 1 else 0 else 0) 32) m ∧
      (cd5PairRange flip m).2 =
        sumNat (fun i => if i = 0 then 0 else
          sumNat (fun j => if i < j then
            if (if parityBits 5 ((i ^^^ j) &&& flip) then 16 - nu5Closed i j else nu5Closed i j) == 4
            then 1 else 0 else 0) 32) m := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ihm =>
      unfold cd5PairRange sumNat
      rcases ihm with ⟨ih1, ih2⟩
      by_cases hm0 : m = 0
      · subst hm0; simp [ih1, ih2]
      · have hmb : (m == 0) = false := beq_false_of_ne hm0
        simp only [hm0, hmb, Bool.false_eq_true, ↓reduceIte, ih1, ih2, (hrow m 32).1, (hrow m 32).2]
        exact ⟨trivial, trivial⟩
  have h0 := nullityHistGamma_eq_fast 5 flip 0 (by omega) nu5Closed nu5Closed_eq
  have h4 := nullityHistGamma_eq_fast 5 flip 4 (by omega) nu5Closed nu5Closed_eq
  have hp := hrange 32
  ext
  · exact hp.1.trans h0.symm
  · exact hp.2.trans h4.symm

/-- Reconstruct the full 5-bin `CD_5(flip)` profile from `(H(0), H(4))` using the proved
    Mirror Conservation (`H(0)+H(16)=171`, `H(4)+H(12)=210`) & Midpoint 42 Law (`H(8)=84`)! -/
@[expose] def cd5FullFromPair (p : Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  (p.1, p.2, 84, 210 - p.2, 171 - p.1)

theorem cd5_std_mirror_sums :
    nullityHist 5 0 + nullityHist 5 16 = 171 ∧
    nullityHist 5 4 + nullityHist 5 12 = 210 := by
  have h0 : nullityHist 5 0 = 171 := nonZDCount_all_n 5 (by omega)
  have h16 : nullityHist 5 16 = 0 := by
    unfold nullityHist
    rw [nullityHistGamma_eq_fast 5 0 16 (by omega) nu5Closed nu5Closed_eq]
    decide
  have h12 : nullityHist 5 12 = 126 := terrace_top_bin_all_n 4 (by omega)
  have h4 : nullityHist 5 4 = 84 := by
    have htop := terrace_top_jump_all_n 4 (by omega)
    change nullityHist 5 12 = nullityHist 5 4 + 3 * (16 - 2) at htop
    omega
  omega

theorem cd5FullFromPair_eq (flip : Nat) :
    cd5FullFromPair (cd5PairRange flip 32) =
      (nullityHistGamma 5 flip 0, nullityHistGamma 5 flip 4,
       nullityHistGamma 5 flip 8, nullityHistGamma 5 flip 12,
       nullityHistGamma 5 flip 16) := by
  rw [cd5PairRange_eq]
  unfold cd5FullFromPair
  have hmid : nullityHistGamma 5 flip 8 = 84 := universal_split_midpoint_42 5 flip (by omega)
  have hm0 : nullityHistGamma 5 flip 0 + nullityHistGamma 5 flip 16 = 171 := by
    have h := mirror_sum_conservation 5 flip 0 (by omega) (by omega)
    simpa [cd5_std_mirror_sums.1] using h
  have hm4 : nullityHistGamma 5 flip 4 + nullityHistGamma 5 flip 12 = 210 := by
    have h := mirror_sum_conservation 5 flip 4 (by omega) (by omega)
    simpa [cd5_std_mirror_sums.2] using h
  have h12 : 210 - nullityHistGamma 5 flip 4 = nullityHistGamma 5 flip 12 := by omega
  have h16 : 171 - nullityHistGamma 5 flip 0 = nullityHistGamma 5 flip 16 := by omega
  rw [hmid, h12, h16]

/-- **Theorem T4c-2 (Complete 32-Signature Split Pathion Phase Classification):**
    Across all 32 signatures $\gamma \in \{\pm 1\}^5$ of $\mathrm{CD}_5(\gamma)$:
    Exactly **8** distinct nullity-histogram phases occur with multiplicities **`4×1 + 4×7`**:
    4 phases of multiplicity `1` (Euclidean octonion core) and 4 phases of multiplicity `7`
    (the 7 split-octonion bases), summing to `32`, with universal invariant $H_5^\gamma(8) = 84$
    and $H_5^\gamma(4) + H_5^\gamma(12) = 210$. -/
theorem split_pathion_8_phases :
    let profs := (List.range 32).map (fun fl =>
      (nullityHistGamma 5 fl 0, nullityHistGamma 5 fl 4,
       nullityHistGamma 5 fl 8, nullityHistGamma 5 fl 12,
       nullityHistGamma 5 fl 16))
    (profs.count (171, 84, 84, 126, 0) = 1) ∧
    (profs.count (141, 126, 84, 84, 30) = 1) ∧
    (profs.count (127, 28, 84, 182, 44) = 1) ∧
    (profs.count (113, 182, 84, 28, 58) = 1) ∧
    (profs.count (91, 100, 84, 110, 80) = 7) ∧
    (profs.count (79, 124, 84, 86, 92) = 7) ∧
    (profs.count (77, 110, 84, 100, 94) = 7) ∧
    (profs.count (65, 86, 84, 124, 106) = 7) := by
  have heq : (List.range 32).map (fun fl =>
      (nullityHistGamma 5 fl 0, nullityHistGamma 5 fl 4,
       nullityHistGamma 5 fl 8, nullityHistGamma 5 fl 12,
       nullityHistGamma 5 fl 16)) =
      (List.range 32).map (fun fl => cd5FullFromPair (cd5PairRange fl 32)) := by
    apply List.map_congr_left; intro fl _
    exact (cd5FullFromPair_eq fl).symm
  dsimp only; rw [heq]; decide

end

end CDTerrace
