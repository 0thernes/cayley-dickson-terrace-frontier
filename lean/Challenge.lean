module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import CDTerrace.Basic
public import CDTerrace.HurwitzRupture
public import CDTerrace.FiniteCertificates
public import CDTerrace.PathionRupture
public import CDTerrace.SpectralGaps
public import CDTerrace.OddBladeExclusion

/-!
# Statement-Only Challenge Definitions (`Challenge.lean`)

Defines all 28 headline theorem statement abbreviations (`T1aStmt`–`T6cStmt`) and their
master conjunction (`AllTerraceTheoremsStmt`) against the core mathematical definitions
in `CDTerrace.Basic`, `CDTerrace.HurwitzRupture`, `CDTerrace.FiniteCertificates`,
`CDTerrace.PathionRupture`, `CDTerrace.SpectralGaps`, and `CDTerrace.OddBladeExclusion`.
-/

namespace Challenge

open CDTerrace

@[expose] public section

/-- **T1a:** Universal all-$n$ multiplicative sign factorization across all $2^n$ signatures. -/
abbrev T1aStmt : Prop :=
  ∀ n flipMask i j, i < 2 ^ n → j < 2 ^ n →
    cdSignGamma n flipMask i j = cdSign n i j * paritySign n (i &&& j &&& flipMask)

/-- **T1b:** Universal $k$-independent $2 \times 2$ zero-divisor block-sign flip law. -/
abbrev T1bStmt : Prop :=
  ∀ n flipMask i j k, i < 2 ^ n → j < 2 ^ n → k < 2 ^ n →
    blockDeltaGamma n flipMask i j k = paritySign n ((i ^^^ j) &&& flipMask) * blockDelta n i j k

/-- **T1c:** Exact 2-blade cross-term anticommutativity and full bilinear nilpotency criterion
    $(e_i + e_j)^2 = 0$ across all dimensions and signatures. -/
abbrev T1cStmt : Prop :=
  ∀ n flipMask i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
    (cdSignGamma n flipMask i j + cdSignGamma n flipMask j i = 0) ∧
    ((∀ t, t < 2 ^ n →
        cdMulCoordGamma n flipMask (twobladeVec i j) (twobladeVec i j) t = 0) ↔
      parityBits n ((i ^^^ j) &&& flipMask) = true)

/-- **T1d:** Universal all-$n$ Nilpotent Mirror-Inversion Law. -/
abbrev T1dStmt : Prop :=
  ∀ n flipMask i j, 1 ≤ n → i < 2 ^ n → j < 2 ^ n → i ≠ j →
    (parityBits n ((i ^^^ j) &&& flipMask) = false →
      twobladeNullityGamma n flipMask i j = twobladeNullity n i j) ∧
    (parityBits n ((i ^^^ j) &&& flipMask) = true →
      twobladeNullityGamma n flipMask i j + twobladeNullity n i j = 2 ^ (n - 1))

/-- **T1e:** Universal all-$n$ Mirror-Pair Spectral Conservation & Midpoint Stratum Invariance. -/
abbrev T1eStmt : Prop :=
  (∀ n flipMask v, 1 ≤ n → v ≤ 2 ^ (n - 1) →
    nullityHistGamma n flipMask v + nullityHistGamma n flipMask (2 ^ (n - 1) - v) =
      nullityHist n v + nullityHist n (2 ^ (n - 1) - v)) ∧
  (∀ n flipMask, 2 ≤ n →
    nullityHistGamma n flipMask (2 ^ (n - 2)) = nullityHist n (2 ^ (n - 2)))

/-- **T1f:** Exact $2 \times 2$ Block Left-Annihilator Kernel-Basis Isomorphism proving
    `twobladeNullityGamma n flipMask i j` equals the exact cardinality of an explicit 2-sparse
    linearly independent spanning $\mathbb{Z}$-basis of $\ker L_{e_i + e_j}$. -/
abbrev T1fStmt : Prop :=
  ∀ n flipMask i j, i < 2 ^ n → j < 2 ^ n → i ≠ j →
    let reps := singularOrbitRepsGamma n flipMask i j
    reps.length = twobladeNullityGamma n flipMask i j ∧
    (∀ k ∈ reps, ∀ t, t < 2 ^ n →
      cdMulCoordGamma n flipMask (twobladeVec i j)
        (twobladeKernelBasisVec n flipMask i j k) t = 0) ∧
    (∀ v : Nat → Int,
      (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask (twobladeVec i j) v t = 0) ↔
      (∀ x, x < 2 ^ n → v x = linearCombKernelBasis n flipMask i j reps v x)) ∧
    (∀ c : Nat → Int,
      (∀ x, x < 2 ^ n → linearCombKernelBasis n flipMask i j reps c x = 0) →
      (∀ k ∈ reps, c k = 0))

/-- **T2a:** Exact four-branch 2-blade nullity doubling recurrence for all $n \ge 2$. -/
abbrev T2aStmt : Prop :=
  (∀ n i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
    twobladeNullity (n + 1) i j = 2 * twobladeNullity n i j) ∧
  (∀ n i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
    twobladeNullity (n + 1) (i + 2 ^ n) (j + 2 ^ n) = 2 * twobladeNullity n i j) ∧
  (∀ n a, 0 < a → a < 2 ^ n →
    twobladeNullity (n + 1) (2 ^ n) (a + 2 ^ n) = 0 ∧
    twobladeNullity (n + 1) a (2 ^ n) = 0 ∧
    twobladeNullity (n + 1) a (a + 2 ^ n) = 0) ∧
  (∀ n i b, 2 ≤ n → 0 < i → 0 < b → i < 2 ^ n → b < 2 ^ n → i ≠ b →
    twobladeNullity (n + 1) i (b + 2 ^ n) = 2 ^ n - 4 - 2 * twobladeNullity n i b)

/-- **T2b:** Universal divisibility by 4 (independent elementary 2-blade proof specializing
    Moreno's theorem), sharp attainable $2^{n-1} - 4$ ceiling, strict separation from the cited
    Biss–Dugger–Isaksen formula $2^n - 4n + 4$ for every $n \ge 5$, and unique equality at
    $n = 4$ among $n \ge 4$. -/
abbrev T2bStmt : Prop :=
  (∀ n, 3 ≤ n → ∀ i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
    4 ∣ twobladeNullity n i j ∧ (4 ≤ n → twobladeNullity n i j ≤ 2 ^ (n - 1) - 4)) ∧
  (∀ n, 4 ≤ n → ∃ i j, 0 < i ∧ i < j ∧ j < 2 ^ n ∧ twobladeNullity n i j = twobladeMaxNullity n) ∧
  (∀ n, 5 ≤ n → twobladeMaxNullity n < bdiMaxAnnihilator n) ∧
  (∀ n, 4 ≤ n → (twobladeMaxNullity n = bdiMaxAnnihilator n ↔ n = 4))

/-- **T2c:** Closed-form all-$n$ Total 2-Blade Nullity Mass and Non-Zero-Divisor Count. -/
abbrev T2cStmt : Prop :=
  (∀ n, 3 ≤ n → totalNullityMass n = 8 * (2 ^ (n - 1) - 1) * (2 ^ (n - 2) - 1) * (2 ^ (n - 3) - 1)) ∧
  (∀ n, 3 ≤ n → nullityHist n 0 = nonZDCountFormula n)

/-- **T2d:** The Dyadic-Palindromic Terrace Law: exact even/odd bin interleaving and universal
    interior palindrome for all $n \ge 3$. -/
abbrev T2dStmt : Prop :=
  (∀ n m, 3 ≤ n → 1 ≤ m → nullityHist (n + 1) (8 * m) = 2 * nullityHist n (4 * m)) ∧
  (∀ n m, 3 ≤ n → 8 * m < 2 ^ n - 4 → nullityHist (n + 1) (2 ^ n - 4 - 8 * m) = 2 * nullityHist n (4 * m)) ∧
  (∀ n k, 3 ≤ n → 1 ≤ k → 4 * k < 2 ^ n - 4 →
    nullityHist (n + 1) (4 * k) = nullityHist (n + 1) (2 ^ n - 4 - 4 * k))

/-- **T2e:** Universal exact top terrace bin $H_{n+1}(2^n - 4) = 2 H_n(0)$ and exact top jump
    $H_{n+1}(2^n - 4) = H_{n+1}(4) + 3(2^n - 2)$. -/
abbrev T2eStmt : Prop :=
  (∀ n, 3 ≤ n → nullityHist (n + 1) (2 ^ n - 4) = 2 * nonZDCountFormula n) ∧
  (∀ n, 4 ≤ n → nullityHist (n + 1) (2 ^ n - 4) = nullityHist (n + 1) 4 + 3 * (2 ^ n - 2))

/-- **T2f:** Universal All-Signature Midpoint 42 Law: $H_n^\gamma(2^{n-2}) = 42 \cdot 2^{n-4}$
    for every $n \ge 4$ and every signature $\gamma \in \{\pm 1\}^n$. -/
abbrev T2fStmt : Prop :=
  (∀ n, 4 ≤ n → nullityHist n (2 ^ (n - 2)) = 42 * 2 ^ (n - 4)) ∧
  (∀ n flipMask, 4 ≤ n → nullityHistGamma n flipMask (2 ^ (n - 2)) = 42 * 2 ^ (n - 4))

/-- **T3a:** Exact doubling law of the Euclidean coordinate right-compatibility graph
    $G_n^{\mathrm{comp}}$ and exact uniqueness of the two universal right-multipliers
    $\{e_0, e_{2^{n-1}}\}$ for all $n \ge 4$. -/
abbrev T3aStmt : Prop :=
  (∀ n a b, a < 2 ^ n → b < 2 ^ n → rightCompat (n + 1) a b = rightCompat n a b) ∧
  (∀ n a b, a < 2 ^ n → b < 2 ^ n → rightCompat (n + 1) (a + 2 ^ n) (b + 2 ^ n) = rightCompat n a b) ∧
  (∀ n a b, 3 ≤ n → a < 2 ^ n → b < 2 ^ n →
    rightCompat (n + 1) a (b + 2 ^ n) = decide (a = 0 ∨ b = 0 ∨ a = b)) ∧
  (∀ n j, 4 ≤ n → j < 2 ^ n →
    ((∀ x, x < 2 ^ n → x ≠ j → rightCompat n j x = true) ↔ (j = 0 ∨ j = 2 ^ (n - 1))))

/-- **T3b:** Exact Euclidean coordinate right-compatibility clique number
    $\omega(G_n^{\mathrm{comp}}) = n + 5$ for every $n \ge 3$. -/
abbrev T3bStmt : Prop :=
  (∀ n, 3 ≤ n → ∀ S, isCompatClique n S → S.length ≤ n + 5) ∧
  (∀ n, 3 ≤ n → isCompatClique n (cdMaxClique n) ∧ (cdMaxClique n).length = n + 5)

/-- **T3c:** Exact arithmetic comparison of the Euclidean coordinate ceiling $n + 5$ against the
    classical Hurwitz–Radon function $\rho(2^n)$: saturation at $n \in \{3, 4, 5\}$ and permanent
    strict rupture $n + 5 < \rho(2^n)$ with linear deficit $\ge n - 5$ for all $n \ge 6$. -/
abbrev T3cStmt : Prop :=
  ((3 + 5 = hurwitzRadon 3) ∧ (4 + 5 = hurwitzRadon 4) ∧ (5 + 5 = hurwitzRadon 5)) ∧
  (∀ n, 6 ≤ n → n + 5 < hurwitzRadon n ∧ n - 5 ≤ hurwitzRadon n - (n + 5))

/-- **T3d:** Constructive full-left $[2^n, n + 5, 2^n]$ and asymmetric doubling tower
    $[2^{n-1}, 2(n + 4), 2^n]$ Euclidean norm-multiplicative coordinate pairs for all $n \ge 4$. -/
abbrev T3dStmt : Prop :=
  (∀ n SR, isCompatClique n SR → isNormMultPair n (List.range (2 ^ n)) SR) ∧
  (∀ n, 4 ≤ n →
    isNormMultPair n (List.range (2 ^ (n - 1))) (doubledRightWitness n) ∧
    (doubledRightWitness n).Nodup ∧
    (doubledRightWitness n).length = 2 * (n + 4))

/-- **T4a:** Exhaustive $2^{16}$ Sedenion Triple-42 & Fano $7 + 28 + 7 = 42$ Duality, exact
    non-existence of any 11D norm-multiplicative coordinate subspace in $\mathbb{S}_{16}$, and
    universal $2 + 2$ split of all 42 bad affine 2-planes across $\{1..7\} \times \{9..15\}$. -/
abbrev T4aStmt : Prop :=
  (countAffinePlanes4 = 140 ∧
   countBadAffinePlanes4 = 42 ∧
   countNormMult4Eq10 = 42 ∧
   countNormMult4Ge11 = 0 ∧
   countNormMult4Eq10WithLo 8 = 7 ∧
   countNormMult4Eq10WithLo 5 = 28 ∧
   countNormMult4Eq10WithLo 2 = 7) ∧
  (∀ m, m < 65536 → 11 ≤ popcount16 m → isNormMultMask 4 m = false) ∧
  (∀ a b c d, a < b → b < c → c < d → d < 16 →
    (a ^^^ b ^^^ c = d) → isBadAffinePlane 4 a b c d = true →
    1 ≤ a ∧ b ≤ 7 ∧ 9 ≤ c ∧ d ≤ 15)

/-- **T4b:** Formal six-kernel re-verification of de Marrais's 42 Sedenion Box-Kite assessors
    ($7 \times K_{2,2,2}$) under pure algebraic vanishing-product adjacency `boxKiteAdj` (zero XOR
    pre-filtering) plus bridge to `cdMulCoordGamma` and 9D norm-multiplicative $\mathbb{O} \oplus \mathbb{R}e_8$. -/
abbrev T4bStmt : Prop :=
  (∀ i j k l s t, i < 16 → j < 16 → i ≠ j → k ≠ l →
    bladeProdCoord4 i j k l s t =
      cdMulCoordGamma 4 0 (twobladeVec i j) (signedBladeVec k l s) t) ∧
  sedenionAssessors.length = 42 ∧
  sedenionAssessors.all (fun p => (sedenionAssessors.filter (boxKiteAdj p)).length == 4) = true ∧
  ([9, 10, 11, 12, 13, 14, 15].all fun s =>
    let comp := sedenionAssessors.filter (fun p => p.1 ^^^ p.2 == s)
    comp.length == 6 &&
    comp.all (fun p => (comp.filter (boxKiteAdj p)).length == 4)) = true ∧
  sedenionAssessors.all (fun p =>
    sedenionAssessors.all (fun q => !boxKiteAdj p q || (p.1 ^^^ p.2 == q.1 ^^^ q.2))) = true ∧
  popcount16 511 = 9 ∧
  isNormMultMask 4 511 = true

/-- **T4c:** Complete exhaustive Split-Signature Phase Classifications of $\mathrm{CD}_4(\gamma)$
    ($1 : 1 : 7 : 7$) and $\mathrm{CD}_5(\gamma)$ ($4 \times 1 + 4 \times 7$). -/
abbrev T4cStmt : Prop :=
  (let profs := (List.range 16).map (fun fl =>
     (nullityHistGamma 4 fl 0, nullityHistGamma 4 fl 4, nullityHistGamma 4 fl 8))
   (profs.count (63, 42, 0) = 1) ∧
   (profs.count (49, 42, 14) = 1) ∧
   (profs.count (31, 42, 32) = 7) ∧
   (profs.count (25, 42, 38) = 7)) ∧
  (let profs := (List.range 32).map (fun fl =>
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
   (profs.count (65, 86, 84, 124, 106) = 7))

/-- **T4d:** Certified $[14, 14, 32]$ Pathion and $[16, 16, 64]$ Chingon symmetric coordinate
    witnesses plus the elementary commutative-domain unit lemma ($c^2 = 1 \implies c = \pm 1$)
    derived directly from standard ring axioms, and explicit $\mathbb{Z}$ / $\mathbb{Z}[i]$ forms. -/
abbrev T4dStmt : Prop :=
  (pathionWitness14.length = 14 ∧
   pathionWitness14.Nodup ∧
   (∀ x ∈ pathionWitness14, x < 32) ∧
   isNormMultList 5 pathionWitness14 = true ∧
   chingonWitness16.length = 16 ∧
   chingonWitness16.Nodup ∧
   (∀ x ∈ chingonWitness16, x < 64) ∧
   isNormMultList 6 chingonWitness16 = true) ∧
  (∀ {R : Type} (zero one : R) (add mul : R → R → R) (neg : R → R),
    (∀ x y z, add (add x y) z = add x (add y z)) →
    (∀ x, add zero x = x) →
    (∀ x, add x zero = x) →
    (∀ x, add x (neg x) = zero) →
    (∀ x, add (neg x) x = zero) →
    (∀ x y, mul x y = mul y x) →
    (∀ x, mul x one = x) →
    (∀ x y z, mul x (add y z) = add (mul x y) (mul x z)) →
    (∀ x y z, mul (add x y) z = add (mul x z) (mul y z)) →
    (∀ x y, mul (neg x) y = neg (mul x y)) →
    (∀ x y, mul x y = zero → x = zero ∨ y = zero) →
    ∀ c, mul c c = one → c = one ∨ c = neg one) ∧
  (∀ c : Int, c * c = 1 ↔ c = 1 ∨ c = -1) ∧
  (∀ z : GaussInt, z.mul z = GaussInt.one ↔ z = GaussInt.one ∨ z = GaussInt.negOne)

/-- **T4e:** Pure-kernel proof over all $2^{32}$ coordinate subsets of $\mathrm{CD}_5$ (retiring
    HiGHS MILP from the proof trust base!) that $r_{\max}(\mathrm{CD}_5) \le 14$ (hence $= 14$
    with `T4d`) AND strict $7 + 7$ half-balance rigidity for every 14D norm-multiplicative
    coordinate subspace of $\mathrm{CD}_5$. -/
abbrev T4eStmt : Prop :=
  (∀ m, m < 2 ^ 32 → isNormMultMask 5 m = true → popcount32 m ≤ 14) ∧
  (∀ m, m < 2 ^ 32 → isNormMultMask 5 m = true → popcount32 m = 14 →
    popcount16 (m % 65536) = 7 ∧ popcount16 (m / 65536) = 7) ∧
  (∀ S : List Nat, S.Nodup → isNormMultPair 5 S S →
    S.length ≤ 14 ∧
    (S.length = 14 →
      (S.filter (fun x => decide (x < 16))).length = 7 ∧
      (S.filter (fun x => decide (16 ≤ x))).length = 7))

/-- **T4f:** Pure-kernel proof of the Dimension-64 split-signature interior spectral gap phase
    transition in $\mathrm{CD}_6(\gamma)$ at `flipMask = 56`: complete 9-bin histogram with
    $H_6^{56}(16) = 168$, $H_6^{56}(20) = 0$, $H_6^{56}(24) = 56$. -/
abbrev T4fStmt : Prop :=
  nullityHistGamma 6 56 0 = 257 ∧
  nullityHistGamma 6 56 4 = 422 ∧
  nullityHistGamma 6 56 8 = 364 ∧
  nullityHistGamma 6 56 12 = 336 ∧
  nullityHistGamma 6 56 16 = 168 ∧
  nullityHistGamma 6 56 20 = 0 ∧
  nullityHistGamma 6 56 24 = 56 ∧
  nullityHistGamma 6 56 28 = 172 ∧
  nullityHistGamma 6 56 32 = 178

/-- **T5a:** Universal all-$n$ Binary Reflected Gray-Code Bit-Locking Law ($n \ge 4$):
    bit $n - 1 - d$ of $i \oplus j$ is locked deterministically to the Binary Reflected Gray Code
    of $m = \nu_n^{\mathrm{std}}(i, j) / 4$ on $[2^{d+1},\; 2^{n-1} - 2^{d+1} - 4]$
    (and $[4,\; 2^{n-1} - 4]$ for $d = 0$). -/
abbrev T5aStmt : Prop :=
  ∀ n, 4 ≤ n → ∀ i j, 0 < i → i < j → j < 2 ^ n →
    let v := twobladeNullity n i j
    let m := v / 4
    ((4 ≤ v → v ≤ 2 ^ (n - 1) - 4 →
        (i ^^^ j).testBit (n - 1) = m.testBit 0) ∧
     (∀ d, 1 ≤ d → d ≤ n - 4 →
        2 ^ (d + 1) ≤ v → v ≤ 2 ^ (n - 1) - 2 ^ (d + 1) - 4 →
        (i ^^^ j).testBit (n - 1 - d) = xor (m.testBit (d - 1)) (m.testBit d)))

/-- **T5b:** Universal Exponential Continuous Spectral Band Gap at `flipMask = 2^n - 8` for all
    $n \ge 6$: every $v \in (2^{n-2},\; 3 \cdot 2^{n-3})$ (width $2^{n-3} - 1$ consecutive
    multiples of $4$) has $H_n^{2^n - 8}(v) = 0$, flanked by populated lower edge
    $H_n^{2^n - 8}(2^{n-2}) = 42 \cdot 2^{n-4}$ and upper edge $H_n^{2^n - 8}(3 \cdot 2^{n-3}) > 0$. -/
abbrev T5bStmt : Prop :=
  ∀ n, 6 ≤ n →
    (∀ v, 2 ^ (n - 2) < v → v < 3 * 2 ^ (n - 3) →
      nullityHistGamma n (2 ^ n - 8) v = 0) ∧
    nullityHistGamma n (2 ^ n - 8) (2 ^ (n - 2)) = 42 * 2 ^ (n - 4) ∧
    0 < nullityHistGamma n (2 ^ n - 8) (3 * 2 ^ (n - 3))

/-- **T5c:** Exact Complete All-$n$, All-Signature Spectral-Gap Dichotomy for all $n \ge 6$:
    $\mathrm{CD}_n(f)$ has an interior mod-4 spectral gap in $(0, 2^{n-1} - 4)$ IF AND ONLY IF
    $8 \mid f$ and $f \notin \{0, 8, 2^{n-1}, 2^{n-1} + 8\}$, comprising exactly $2^{n-3} - 4$
    out of all $2^n$ signatures. -/
abbrev T5cStmt : Prop :=
  ∀ n, 6 ≤ n →
    (∀ f, f < 2 ^ n → (hasInteriorMod4Gap n f ↔ isGappedMask n f = true)) ∧
    countPred (isGappedMask n) (2 ^ n) = 2 ^ (n - 3) - 4

/-- **T6a:** Universal Mod-2 Twisted-Group-Algebra Frobenius Involution for arbitrary $\{\pm 1\}$
    cocycles $\sigma$ and any $x \in \mathbb{Z}^{2^n}$ with odd coordinate sum. -/
abbrev T6aStmt : Prop :=
  ∀ n (σ : Nat → Nat → Int), (∀ a b, σ a b = 1 ∨ σ a b = -1) →
    ∀ x, oddCoordSum n x →
      (∀ y t, t < 2 ^ n → (twistedMul n σ x (twistedMul n σ x y) t - y t) % 2 = 0) ∧
      (∀ y t, t < 2 ^ n → (twistedMul n σ (twistedMul n σ y x) x t - y t) % 2 = 0) ∧
      (∀ f u v t, twistedMul n (cdSignGamma n f) u v t = cdMulCoordGamma n f u v t)

/-- **T6b:** Universal All-$n$, All-Signature Odd-Parity Zero-Divisor Exclusion via fraction-free
    odd-pivot integral matrix inversion ($B_L L_x = \Delta_L I$ and $B_R R_x = \Delta_R I$ with odd
    $\Delta_L, \Delta_R$, implying invertibility over $\mathbb{Q}, \mathbb{R}, \mathbb{C}$ and
    trivial left/right annihilators). -/
abbrev T6bStmt : Prop :=
  ∀ n flipMask x, oddCoordSum n x →
    (∃ (B : Nat → Nat → Int) (Δ : Int), Δ % 2 = 1 ∧
      ∀ i, i < 2 ^ n → ∀ j, j < 2 ^ n →
        matMulInt (2 ^ n) B (leftMulMat n flipMask x) i j = if i == j then Δ else 0) ∧
    (∃ (B : Nat → Nat → Int) (Δ : Int), Δ % 2 = 1 ∧
      ∀ i, i < 2 ^ n → ∀ j, j < 2 ^ n →
        matMulInt (2 ^ n) B (rightMulMat n flipMask x) i j = if i == j then Δ else 0) ∧
    (∀ y, (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask x y t = 0) →
      ∀ t, t < 2 ^ n → y t = 0) ∧
    (∀ y, (∀ t, t < 2 ^ n → cdMulCoordGamma n flipMask y x t = 0) →
      ∀ t, t < 2 ^ n → y t = 0)

/-- **T6c:** Universal Odd-Support Unit-Blade Non-Singularity (all signed 3-blades, 5-blades,
    ..., $(2m+1)$-blades across all $n$ and all $2^n$ signatures) & Zero-Divisor Parity
    Conservation ($\sum x_a \equiv 0 \pmod 2$ for every integer zero divisor). -/
abbrev T6cStmt : Prop :=
  ∀ n flipMask,
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
      sumInt x (2 ^ n) % 2 = 0)

/-- Master conjunction of all 28 headline theorems across all 6 pillars. -/
abbrev AllTerraceTheoremsStmt : Prop :=
  T1aStmt ∧ T1bStmt ∧ T1cStmt ∧ T1dStmt ∧ T1eStmt ∧ T1fStmt ∧
  T2aStmt ∧ T2bStmt ∧ T2cStmt ∧ T2dStmt ∧ T2eStmt ∧ T2fStmt ∧
  T3aStmt ∧ T3bStmt ∧ T3cStmt ∧ T3dStmt ∧
  T4aStmt ∧ T4bStmt ∧ T4cStmt ∧ T4dStmt ∧ T4eStmt ∧ T4fStmt ∧
  T5aStmt ∧ T5bStmt ∧ T5cStmt ∧
  T6aStmt ∧ T6bStmt ∧ T6cStmt

end
end Challenge
