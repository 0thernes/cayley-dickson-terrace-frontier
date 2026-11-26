module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import CDTerrace.Basic
public import CDTerrace.HurwitzRupture
public import CDTerrace.FiniteCertificates

/-!
# Statement-Only Challenge Definitions (`Challenge.lean`)

Defines the 19 headline theorem statement abbreviations (`T1aStmt`–`T4dStmt`) and their
master conjunction (`AllTerraceTheoremsStmt`) against the core mathematical definitions
in `CDTerrace.Basic`, `CDTerrace.HurwitzRupture`, and `CDTerrace.FiniteCertificates`.
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

/-- **T1c:** Exact 2-blade nilpotency criterion across all dimensions and signatures. -/
abbrev T1cStmt : Prop :=
  ∀ n flipMask i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n →
    ((cdSignGamma n flipMask i i + cdSignGamma n flipMask j j = 0) ↔
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

/-- **T2b:** Universal divisibility by 4, $2^{n-1} - 4$ ceiling, and strict separation from the
    Biss–Dugger–Isaksen annihilator ceiling $2^n - 4n + 4$ for every $n \ge 5$. -/
abbrev T2bStmt : Prop :=
  (∀ n, 3 ≤ n → ∀ i j, 0 < i → 0 < j → i < 2 ^ n → j < 2 ^ n → i ≠ j →
    4 ∣ twobladeNullity n i j ∧ (4 ≤ n → twobladeNullity n i j ≤ 2 ^ (n - 1) - 4)) ∧
  (∀ n, 5 ≤ n → twobladeMaxNullity n < bdiMaxAnnihilator n)

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

/-- **T3a:** Exact doubling law of the right-compatibility graph $G_n^{\mathrm{comp}}$ and exact
    uniqueness of the two universal right-multipliers $\{e_0, e_{2^{n-1}}\}$ for all $n \ge 4$. -/
abbrev T3aStmt : Prop :=
  (∀ n a b, a < 2 ^ n → b < 2 ^ n → rightCompat (n + 1) a b = rightCompat n a b) ∧
  (∀ n a b, a < 2 ^ n → b < 2 ^ n → rightCompat (n + 1) (a + 2 ^ n) (b + 2 ^ n) = rightCompat n a b) ∧
  (∀ n a b, 3 ≤ n → a < 2 ^ n → b < 2 ^ n →
    rightCompat (n + 1) a (b + 2 ^ n) = decide (a = 0 ∨ b = 0 ∨ a = b)) ∧
  (∀ n j, 4 ≤ n → j < 2 ^ n →
    ((∀ x, x < 2 ^ n → x ≠ j → rightCompat n j x = true) ↔ (j = 0 ∨ j = 2 ^ (n - 1))))

/-- **T3b:** Exact clique number $\omega(G_n^{\mathrm{comp}}) = n + 5$ for every $n \ge 3$. -/
abbrev T3bStmt : Prop :=
  (∀ n, 3 ≤ n → ∀ S, isCompatClique n S → S.length ≤ n + 5) ∧
  (∀ n, 3 ≤ n → isCompatClique n (cdMaxClique n) ∧ (cdMaxClique n).length = n + 5)

/-- **T3c:** Exact Hurwitz–Radon saturation at $n \in \{3, 4, 5\}$ and the Dimension-64
    Hurwitz–Radon Bott Rupture $n + 5 < \rho(2^n)$ with linear deficit $\ge n - 5$ for all $n \ge 6$. -/
abbrev T3cStmt : Prop :=
  ((3 + 5 = hurwitzRadon 3) ∧ (4 + 5 = hurwitzRadon 4) ∧ (5 + 5 = hurwitzRadon 5)) ∧
  (∀ n, 6 ≤ n → n + 5 < hurwitzRadon n ∧ n - 5 ≤ hurwitzRadon n - (n + 5))

/-- **T3d:** Constructive full-left $[2^n, n + 5, 2^n]$ and asymmetric doubling tower
    $[2^{n-1}, 2(n + 4), 2^n]$ norm-multiplicative coordinate pairs for all $n \ge 4$. -/
abbrev T3dStmt : Prop :=
  (∀ n SR, isCompatClique n SR → isNormMultPair n (List.range (2 ^ n)) SR) ∧
  (∀ n, 4 ≤ n →
    isNormMultPair n (List.range (2 ^ (n - 1))) (doubledRightWitness n) ∧
    (doubledRightWitness n).Nodup ∧
    (doubledRightWitness n).length = 2 * (n + 4))

/-- **T4a:** Exhaustive $2^{16}$ Sedenion Triple-42 & Fano $7 + 28 + 7 = 42$ Duality, plus
    exact non-existence of any 11D norm-multiplicative coordinate subspace in $\mathbb{S}_{16}$. -/
abbrev T4aStmt : Prop :=
  (countAffinePlanes4 = 140 ∧
   countBadAffinePlanes4 = 42 ∧
   countNormMult4Eq10 = 42 ∧
   countNormMult4Ge11 = 0 ∧
   countNormMult4Eq10WithLo 8 = 7 ∧
   countNormMult4Eq10WithLo 5 = 28 ∧
   countNormMult4Eq10WithLo 2 = 7) ∧
  (∀ m, m < 65536 → 11 ≤ popcount16 m → isNormMultMask 4 m = false)

/-- **T4b:** Complete Sedenion $7 \times K_{2,2,2}$ Box-Kite decomposition (42 assessors, 4-regular,
    7 XOR-partitioned octahedra) and 9D norm-multiplicative $\mathbb{O} \oplus \mathbb{R}e_8$. -/
abbrev T4bStmt : Prop :=
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
    witnesses plus abstract & Gaussian-integer pure-intercalate base-field rigidity. -/
abbrev T4dStmt : Prop :=
  (pathionWitness14.length = 14 ∧
   pathionWitness14.Nodup ∧
   (∀ x ∈ pathionWitness14, x < 32) ∧
   isNormMultList 5 pathionWitness14 = true ∧
   chingonWitness16.length = 16 ∧
   chingonWitness16.Nodup ∧
   (∀ x ∈ chingonWitness16, x < 64) ∧
   isNormMultList 6 chingonWitness16 = true) ∧
  (∀ {R : Type} (zero one negOne : R) (mul sub : R → R → R),
    (∀ c, mul c c = one → mul (sub c one) (sub c negOne) = zero) →
    (∀ x y, mul x y = zero → x = zero ∨ y = zero) →
    (∀ x y, sub x y = zero → x = y) →
    ∀ c, mul c c = one → c = one ∨ c = negOne) ∧
  (∀ c : Int, c * c = 1 ↔ c = 1 ∨ c = -1) ∧
  (∀ z : GaussInt, z.mul z = GaussInt.one ↔ z = GaussInt.one ∨ z = GaussInt.negOne)

/-- Master conjunction of all 19 headline theorems across all 4 pillars. -/
abbrev AllTerraceTheoremsStmt : Prop :=
  T1aStmt ∧ T1bStmt ∧ T1cStmt ∧ T1dStmt ∧ T1eStmt ∧
  T2aStmt ∧ T2bStmt ∧ T2cStmt ∧ T2dStmt ∧ T2eStmt ∧ T2fStmt ∧
  T3aStmt ∧ T3bStmt ∧ T3cStmt ∧ T3dStmt ∧
  T4aStmt ∧ T4bStmt ∧ T4cStmt ∧ T4dStmt

end
end Challenge
