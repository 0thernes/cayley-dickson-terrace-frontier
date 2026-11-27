// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue

#![forbid(unsafe_code)]

//! Exact zero-dependency verifier for generalized Cayley-Dickson algebras `CD_n(gamma)`:
//! - Pillar 1: Sign-cocycle factorization, nilpotent mirror-inversion law, mirror-pair
//!   conservation, and exhaustive split-phase classification up to `CD_8(gamma)` (256D, all 256 signatures).
//! - Pillar 2: Universal dyadic-palindromic terrace law, 4-case doubling recurrence, exact
//!   nullity mass `M_n`, exact non-ZD counts, palindrome, top-bin jump, and BDI ceiling separation.
//! - Pillar 3: Graph-nullity unification `G_n^comp`, shell degrees, universal multipliers,
//!   Euclidean coordinate right-multiplier rupture (`n + 5 < rho(2^n)` for `n >= 6`), and asymmetric
//!   doubling tower `[2^(n-1), 2(n+4), 2^n]`.
//! - Pillar 4: Sedenion Triple-42 (`42` bad 2+2 affine 2-planes, `42 = 7+28+7` maximal `[10,10,16]`
//!   subspaces, `0` of dim `>= 11`, `42` Box-Kite assessors forming `7 x K_{2,2,2}` under pure
//!   algebraic vanishing product with spectrum `{4^7, 0^21, (-2)^14}`), exact exhaustive Pathion
//!   `r_max(CD_5) = 14` with strict `7 + 7` balance and exact count `280` 14D subspaces,
//!   `CD_6(flip=56)` interior spectral gap `H_6^{56}(20) = 0`, and Chingon `[16, 16, 64]` witness.

use std::collections::{BTreeMap, BTreeSet};

/// Standard Euclidean Cayley-Dickson multiplication sign `sigma_n(i, j) in {-1, +1}`.
#[inline]
pub fn cd_sign(n: u32, i: usize, j: usize) -> i8 {
    if n == 0 {
        return 1;
    }
    let h = 1usize << (n - 1);
    if i < h {
        if j < h {
            cd_sign(n - 1, i, j)
        } else {
            cd_sign(n - 1, j - h, i)
        }
    } else {
        let a = i - h;
        if j < h {
            if j == 0 {
                cd_sign(n - 1, a, 0)
            } else {
                -cd_sign(n - 1, a, j)
            }
        } else {
            let b = j - h;
            if b == 0 {
                -cd_sign(n - 1, 0, a)
            } else {
                cd_sign(n - 1, b, a)
            }
        }
    }
}

/// Direct recursive generalized Cayley-Dickson multiplication sign `sigma_n^gamma(i, j)`
/// with `flip_mask` encoding which doubling stages use `gamma_k = +1` (bit `k = 1`) vs `-1` (`0`).
#[inline]
pub fn cd_sign_gamma_direct(n: u32, flip_mask: usize, i: usize, j: usize) -> i8 {
    if n == 0 {
        return 1;
    }
    let h = 1usize << (n - 1);
    let flipped = ((flip_mask >> (n - 1)) & 1) == 1;
    if i < h {
        if j < h {
            cd_sign_gamma_direct(n - 1, flip_mask, i, j)
        } else {
            cd_sign_gamma_direct(n - 1, flip_mask, j - h, i)
        }
    } else {
        let a = i - h;
        if j < h {
            if j == 0 {
                cd_sign_gamma_direct(n - 1, flip_mask, a, 0)
            } else {
                -cd_sign_gamma_direct(n - 1, flip_mask, a, j)
            }
        } else {
            let b = j - h;
            let raw = if b == 0 {
                -cd_sign_gamma_direct(n - 1, flip_mask, 0, a)
            } else {
                cd_sign_gamma_direct(n - 1, flip_mask, b, a)
            };
            if flipped { -raw } else { raw }
        }
    }
}

/// Pillar 1 closed-form sign-cocycle factorization:
/// `sigma_n^gamma(i, j) = sigma_n^std(i, j) * (-1)^popcount(i & j & flip_mask)`.
#[inline]
pub fn cd_sign_gamma_factored(n: u32, flip_mask: usize, i: usize, j: usize) -> i8 {
    let mask = if n >= usize::BITS { usize::MAX } else { (1usize << n) - 1 };
    let parity = ((i & j & flip_mask & mask).count_ones() & 1) == 1;
    let s = cd_sign(n, i, j);
    if parity { -s } else { s }
}

/// Exact 2x2 block determinant sign `delta_n^std(i, j, k) in {-1, +1}`.
#[inline]
pub fn block_delta(n: u32, i: usize, j: usize, k: usize) -> i8 {
    let d = i ^ j;
    let kp = k ^ d;
    cd_sign(n, i, k) * cd_sign(n, i, kp) * cd_sign(n, j, k) * cd_sign(n, j, kp)
}

/// Standard 2-blade nullity `nu_n^std(i, j)` computed directly from block signs.
pub fn twoblade_nullity_direct(n: u32, i: usize, j: usize) -> usize {
    let dim = 1usize << n;
    let mut sing = 0usize;
    for k in 0..dim {
        if block_delta(n, i, j, k) == 1 {
            sing += 1;
        }
    }
    sing / 2
}

/// Fast O(n) exact standard 2-blade nullity via the proved 4-case doubling recurrence (Pillar 2).
#[inline]
pub fn twoblade_nullity_fast(n: u32, i: usize, j: usize) -> usize {
    if n <= 3 {
        return 0;
    }
    let (a, b) = if i < j { (i, j) } else { (j, i) };
    if a == 0 || a == b {
        return 0;
    }
    let h = 1usize << (n - 1);
    if b < h {
        2 * twoblade_nullity_fast(n - 1, a, b)
    } else if a >= h {
        if a == h {
            0
        } else {
            2 * twoblade_nullity_fast(n - 1, a - h, b - h)
        }
    } else {
        let bh = b - h;
        if bh == 0 || bh == a {
            0
        } else {
            h - 4 - 2 * twoblade_nullity_fast(n - 1, a, bh)
        }
    }
}

/// Generalized 2-blade nullity `nu_n^gamma(i, j)` via the proved Nilpotent Mirror Law (Pillar 1).
#[inline]
pub fn twoblade_nullity_gamma(n: u32, flip_mask: usize, i: usize, j: usize) -> usize {
    if n == 0 {
        return 0;
    }
    let nu = twoblade_nullity_fast(n, i, j);
    let mask = if n >= usize::BITS { usize::MAX } else { (1usize << n) - 1 };
    let nilp = (((i ^ j) & flip_mask & mask).count_ones() & 1) == 1;
    if nilp {
        (1usize << (n - 1)) - nu
    } else {
        nu
    }
}

/// Hurwitz-Radon function `rho(2^n) = 8 * (n / 4) + 2^(n % 4)`.
#[inline]
pub const fn hurwitz_radon(n: u32) -> usize {
    8 * (n as usize / 4) + (1usize << (n % 4))
}

/// Exact non-ZD 2-blade count formula `(6n - 9) * 2^(n - 2) + 3` for `n >= 3`.
#[inline]
pub const fn non_zd_formula(n: u32) -> usize {
    assert!(n >= 3, "non_zd_formula requires n >= 3");
    (6 * n as usize - 9) * (1usize << (n - 2)) + 3
}

/// Exact total 2-blade nullity mass `8 * (2^(n-1)-1) * (2^(n-2)-1) * (2^(n-3)-1)` for `n >= 3`.
#[inline]
pub const fn total_mass_formula(n: u32) -> u128 {
    assert!(n >= 3, "total_mass_formula requires n >= 3");
    let a = (1u128 << (n - 1)) - 1;
    let b = (1u128 << (n - 2)) - 1;
    let c = (1u128 << (n - 3)) - 1;
    8 * a * b * c
}

/// Exact 2-blade histogram for `CD_n(flip_mask)`.
pub fn nullity_histogram_gamma(n: u32, flip_mask: usize) -> BTreeMap<usize, usize> {
    let dim = 1usize << n;
    let mut hist: BTreeMap<usize, usize> = BTreeMap::new();
    for i in 1..dim {
        for j in (i + 1)..dim {
            let nu = twoblade_nullity_gamma(n, flip_mask, i, j);
            *hist.entry(nu).or_insert(0) += 1;
        }
    }
    hist
}

/// Standard Euclidean histogram for `CD_n`.
pub fn nullity_histogram(n: u32) -> BTreeMap<usize, usize> {
    nullity_histogram_gamma(n, 0)
}

/// Check bilinear norm-multiplicativity `||x*y||^2 = ||x||^2 * ||y||^2` for coordinate subspaces `SL, SR` in `CD_n`.
pub fn is_norm_mult_pair(n: u32, sl: &[usize], sr: &[usize]) -> bool {
    let dim = 1usize << n;
    if sl.iter().any(|&x| x >= dim) || sr.iter().any(|&y| y >= dim) {
        return false;
    }
    let sl_set: BTreeSet<usize> = sl.iter().copied().collect();
    let sr_set: BTreeSet<usize> = sr.iter().copied().collect();
    if sl_set.len() != sl.len() || sr_set.len() != sr.len() {
        return false;
    }
    for (idx_i, &i) in sl.iter().enumerate() {
        for &k in &sl[idx_i + 1..] {
            let d = i ^ k;
            for &j in &sr_set {
                let l = j ^ d;
                if l > j && sr_set.contains(&l) {
                    let s = cd_sign(n, i, j) as i32 * cd_sign(n, k, l) as i32
                        + cd_sign(n, i, l) as i32 * cd_sign(n, k, j) as i32;
                    if s != 0 {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// Check right-multiplier compatibility `rightCompat n j x`.
pub fn right_compat(n: u32, j: usize, x: usize) -> bool {
    if j == x {
        return false;
    }
    let dim = 1usize << n;
    if j >= dim || x >= dim {
        return false;
    }
    let d = j ^ x;
    for i in 0..dim {
        let k = i ^ d;
        let s = cd_sign(n, i, j) as i32 * cd_sign(n, k, x) as i32
            + cd_sign(n, i, x) as i32 * cd_sign(n, k, j) as i32;
        if s != 0 {
            return false;
        }
    }
    true
}

/// Pure algebraic mutual zero-divisor check `(e_i + e_j) * (e_k + s * e_l) == 0` in `S_16`
/// (zero XOR pre-filtering).
pub fn sedenion_blade_annihilates(i: usize, j: usize, k: usize, l: usize) -> bool {
    for s in [1i32, -1i32] {
        let mut prod = [0i32; 16];
        prod[i ^ k] += cd_sign(4, i, k) as i32;
        prod[i ^ l] += s * cd_sign(4, i, l) as i32;
        prod[j ^ k] += cd_sign(4, j, k) as i32;
        prod[j ^ l] += s * cd_sign(4, j, l) as i32;
        if prod.iter().all(|&v| v == 0) {
            return true;
        }
    }
    false
}

/// Canonical maximum compatibility clique witness `cdMaxClique n` of size `n + 5` for `n >= 3`.
pub fn cd_max_clique(n: u32) -> Vec<usize> {
    assert!(n >= 3);
    let mut v: Vec<usize> = (0..8).collect();
    for k in 3..n {
        v.push(1usize << k);
    }
    v
}

/// Canonical asymmetric doubling right-multiplier witness of size `2(n + 4)` for `n >= 4`.
pub fn doubled_right_witness(n: u32) -> Vec<usize> {
    assert!(n >= 4);
    let h = 1usize << (n - 1);
    let base = cd_max_clique(n - 1);
    let mut out = base.clone();
    for x in base {
        out.push(x + h);
    }
    out
}

/// Exhaustive exact audit of `CD_5` symmetric coordinate subspaces:
/// 1. Confirms all 630 bad affine 2-planes (`42 lo + 42 hi + 546 cross`).
/// 2. Certifies via fixed-descending (`15..0`) greedy clique cover over all `2,995` valid
///    lower halves with `|S_lo| >= 8` that `|S_lo| + |S_hi| <= 13` (0 failures), hence
///    by half-swap symmetry `r_max(CD_5) = 14` and every 14D subspace splits strictly `7 + 7`.
/// 3. Exhaustively counts ALL 14-dimensional norm-multiplicative coordinate subspaces (`280`),
///    verifying 100% split `7 + 7` and 100% contain both universal multipliers `{e_0, e_16}`.
pub fn audit_pathion_exact() -> (usize, usize, usize, bool, bool) {
    let mut bad_lo: Vec<u16> = Vec::new();
    let mut cross_bad_for_uv: Vec<Vec<(u8, u8)>> = vec![Vec::new(); 256];
    let mut total_bad = 0usize;
    let mut cross_count = 0usize;

    for a in 0..32usize {
        for b in (a + 1)..32 {
            for c in (b + 1)..32 {
                let d = a ^ b ^ c;
                if d > c {
                    let p1 = cd_sign(5, a, c) as i32 * cd_sign(5, b, d) as i32
                        + cd_sign(5, a, d) as i32 * cd_sign(5, b, c) as i32;
                    let p2 = cd_sign(5, a, b) as i32 * cd_sign(5, c, d) as i32
                        + cd_sign(5, a, d) as i32 * cd_sign(5, c, b) as i32;
                    let p3 = cd_sign(5, a, b) as i32 * cd_sign(5, d, c) as i32
                        + cd_sign(5, a, c) as i32 * cd_sign(5, d, b) as i32;
                    if p1 != 0 || p2 != 0 || p3 != 0 {
                        total_bad += 1;
                        if d < 16 {
                            bad_lo.push((1u16 << a) | (1u16 << b) | (1u16 << c) | (1u16 << d));
                        } else if b < 16 && c >= 16 {
                            cross_count += 1;
                            let v = c - 16;
                            let u = d - 16;
                            cross_bad_for_uv[(u << 4) | v].push((a as u8, b as u8));
                        }
                    }
                }
            }
        }
    }
    assert_eq!(total_bad, 630);
    assert_eq!(bad_lo.len(), 42);
    assert_eq!(cross_count, 546);

    // 1. Greedy descending clique-cover certificate on all valid lo with pop >= 8
    let mut valid_ge8 = 0usize;
    let mut greedy_failures = 0usize;
    let mut valid_eq7: Vec<u16> = Vec::new();
    for lo in 0u32..65536 {
        let pop = lo.count_ones() as usize;
        if pop < 7 {
            continue;
        }
        let mu = lo as u16;
        if !bad_lo.iter().all(|&bm| (mu & bm) != bm) {
            continue;
        }
        if pop == 7 {
            valid_eq7.push(mu);
            continue;
        }
        valid_ge8 += 1;
        let mut cliques: Vec<Vec<usize>> = Vec::new();
        for u in (0..16usize).rev() {
            let mut placed = false;
            for c in &mut cliques {
                let mut ok = true;
                for &v in c.iter() {
                    let edge = cross_bad_for_uv[(v << 4) | u]
                        .iter()
                        .any(|&(a, b)| ((mu >> a) & 1) != 0 && ((mu >> b) & 1) != 0);
                    if !edge {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    c.push(u);
                    placed = true;
                    break;
                }
            }
            if !placed {
                cliques.push(vec![u]);
            }
        }
        if pop + cliques.len() > 13 {
            greedy_failures += 1;
        }
    }
    assert_eq!(valid_ge8, 2995);
    assert_eq!(greedy_failures, 0);

    // 2. Exhaustive count of ALL 14D norm-multiplicative coordinate subspaces (all must be 7 + 7!)
    // Precompute per-lo forbidden masks on hi (16 vertices) and find all 7-cliques of non-forbidden hi
    // that are also valid sedenion masks!
    let valid_eq7_set: BTreeSet<u16> = valid_eq7.iter().copied().collect();
    let mut count_14d = 0usize;
    let mut all_have_0_and_16 = true;
    for &lo in &valid_eq7 {
        let mut forb = [0u16; 16];
        for u in 1..16usize {
            for v in 1..u {
                let edge = cross_bad_for_uv[(u << 4) | v]
                    .iter()
                    .any(|&(a, b)| ((lo >> a) & 1) != 0 && ((lo >> b) & 1) != 0);
                if edge {
                    forb[u] |= 1u16 << v;
                    forb[v] |= 1u16 << u;
                }
            }
        }
        struct DfsCtx<'a> {
            forb: &'a [u16; 16],
            valid_eq7_set: &'a BTreeSet<u16>,
            lo: u16,
            count_14d: usize,
            all_have_0_and_16: bool,
        }
        fn dfs(u: usize, chosen: u16, cnt: usize, ctx: &mut DfsCtx<'_>) {
            if cnt == 7 {
                if ctx.valid_eq7_set.contains(&chosen) {
                    ctx.count_14d += 1;
                    if (ctx.lo & 1) == 0 || (chosen & 1) == 0 {
                        ctx.all_have_0_and_16 = false;
                    }
                }
                return;
            }
            if u == 16 || cnt + (16 - u) < 7 {
                return;
            }
            if (chosen & ctx.forb[u]) == 0 {
                dfs(u + 1, chosen | (1u16 << u), cnt + 1, ctx);
            }
            dfs(u + 1, chosen, cnt, ctx);
        }
        let mut ctx = DfsCtx {
            forb: &forb,
            valid_eq7_set: &valid_eq7_set,
            lo,
            count_14d: 0,
            all_have_0_and_16: true,
        };
        dfs(0, 0, 0, &mut ctx);
        count_14d += ctx.count_14d;
        all_have_0_and_16 &= ctx.all_have_0_and_16;
    }
    assert_eq!(count_14d, 280);
    assert!(all_have_0_and_16);
    (14, count_14d, greedy_failures, true, all_have_0_and_16)
}

/// Summary report of all verified claims across `CD_3..CD_8`.
#[derive(Debug, Clone)]
pub struct AuditSummary {
    pub cocycle_checked_dim5: usize,
    pub terrace_verified_up_to: u32,
    pub split_phase_counts: Vec<(u32, usize, Vec<usize>, usize, bool)>,
    pub hurwitz_table: Vec<(u32, usize, usize, usize, Vec<usize>)>,
    pub sedenion_bad_planes: usize,
    pub sedenion_10d_count: usize,
    pub sedenion_11d_count: usize,
    pub sedenion_fano_split: (usize, usize, usize),
    pub sedenion_box_kites_ok: bool,
    pub pathion_14_ok: bool,
    pub pathion_exact_max_dim: usize,
    pub pathion_14d_count: usize,
    pub pathion_greedy_ge8_failures: usize,
    pub pathion_all_14d_balanced_7_7: bool,
    pub pathion_all_14d_contain_0_16: bool,
    pub cd6_flip56_gap_bin20: usize,
    pub chingon_16_ok: bool,
}

/// Exhaustive Sedenion Triple-42 & Box-Kite audit (including pure algebraic adjacency and exact spectrum).
pub fn audit_sedenion_42() -> (usize, usize, usize, (usize, usize, usize), bool) {
    // 1. All 140 affine 2-planes & 42 bad planes (verifying strict 2+2 split across {1..7} x {9..15})
    let mut bad_masks: Vec<u16> = Vec::new();
    let mut total_planes = 0usize;
    for a in 0..16usize {
        for b in (a + 1)..16 {
            for c in (b + 1)..16 {
                let d = a ^ b ^ c;
                if d > c {
                    total_planes += 1;
                    let p1 = cd_sign(4, a, c) as i32 * cd_sign(4, b, d) as i32
                        + cd_sign(4, a, d) as i32 * cd_sign(4, b, c) as i32;
                    let p2 = cd_sign(4, a, b) as i32 * cd_sign(4, c, d) as i32
                        + cd_sign(4, a, d) as i32 * cd_sign(4, c, b) as i32;
                    let p3 = cd_sign(4, a, b) as i32 * cd_sign(4, d, c) as i32
                        + cd_sign(4, a, c) as i32 * cd_sign(4, d, b) as i32;
                    if p1 != 0 || p2 != 0 || p3 != 0 {
                        assert!((1..=7).contains(&a) && b <= 7 && (9..=15).contains(&c) && d <= 15);
                        bad_masks.push((1u16 << a) | (1u16 << b) | (1u16 << c) | (1u16 << d));
                    }
                }
            }
        }
    }
    assert_eq!(total_planes, 140);
    assert_eq!(bad_masks.len(), 42);

    // 2. All 65536 coordinate subspaces
    let mut c10 = 0usize;
    let mut c11 = 0usize;
    let mut f8 = 0usize;
    let mut f5 = 0usize;
    let mut f2 = 0usize;
    for m in 0u32..65536 {
        let pop = m.count_ones() as usize;
        if pop < 10 {
            continue;
        }
        let mu = m as u16;
        if bad_masks.iter().all(|&bm| (mu & bm) != bm) {
            if pop == 10 {
                c10 += 1;
                match (m & 0xff).count_ones() {
                    8 => f8 += 1,
                    5 => f5 += 1,
                    2 => f2 += 1,
                    other => panic!("unexpected Fano split {other}"),
                }
            } else {
                c11 += 1;
            }
        }
    }

    // 3. 42 Box-Kite assessors under pure algebraic vanishing product (NO XOR pre-filtering!)
    let mut assessors = Vec::new();
    for i in 1..8usize {
        for j in 9..16usize {
            if i != j - 8 {
                assessors.push((i, j));
            }
        }
    }
    assert_eq!(assessors.len(), 42);
    let mut adj = [[0i64; 42]; 42];
    let mut cross_xor_edges = 0usize;
    for u in 0..42 {
        let (i, j) = assessors[u];
        for v in 0..42 {
            let (k, l) = assessors[v];
            if sedenion_blade_annihilates(i, j, k, l) {
                adj[u][v] = 1;
                if (i ^ j) != (k ^ l) {
                    cross_xor_edges += 1;
                }
            }
        }
    }
    assert_eq!(cross_xor_edges, 0);
    let all_deg4 = (0..42).all(|u| adj[u].iter().sum::<i64>() == 4);
    let mut a2 = [[0i64; 42]; 42];
    let mut a3 = [[0i64; 42]; 42];
    for r in 0..42 {
        for c in 0..42 {
            let mut s = 0i64;
            for (k, adj_k) in adj.iter().enumerate() {
                s += adj[r][k] * adj_k[c];
            }
            a2[r][c] = s;
        }
    }
    for r in 0..42 {
        for c in 0..42 {
            let mut s = 0i64;
            for (k, adj_k) in adj.iter().enumerate() {
                s += a2[r][k] * adj_k[c];
            }
            a3[r][c] = s;
        }
    }
    let min_poly_ok = (0..42).all(|r| (0..42).all(|c| a3[r][c] - 2 * a2[r][c] - 8 * adj[r][c] == 0));
    let tr1: i64 = (0..42).map(|i| adj[i][i]).sum();
    let tr2: i64 = (0..42).map(|i| a2[i][i]).sum();
    let tr3: i64 = (0..42).map(|i| a3[i][i]).sum();
    let spectrum_ok = min_poly_ok && tr1 == 0 && tr2 == 168 && tr3 == 336;
    let bk_ok = all_deg4 && spectrum_ok && cross_xor_edges == 0;

    (bad_masks.len(), c10, c11, (f8, f5, f2), bk_ok)
}

/// Run the full multi-pillar verification suite up to `CD_8` (256D).
pub fn run_full_audit() -> AuditSummary {
    // 1. Cocycle factorization check on all 32x32x32 triples of CD_5(gamma)
    let mut cocycle_count = 0usize;
    for fl in 0..32usize {
        for i in 0..32usize {
            for j in 0..32usize {
                assert_eq!(
                    cd_sign_gamma_direct(5, fl, i, j),
                    cd_sign_gamma_factored(5, fl, i, j)
                );
                cocycle_count += 1;
            }
        }
    }

    // 2. Cross-check fast doubling nullity vs direct block-sign nullity for CD_3..CD_6
    for n in 3..=6u32 {
        let dim = 1usize << n;
        for i in 1..dim {
            for j in (i + 1)..dim {
                assert_eq!(twoblade_nullity_direct(n, i, j), twoblade_nullity_fast(n, i, j));
            }
        }
    }

    // 3. Terrace laws across CD_3..CD_8
    for n in 3..=8u32 {
        let h = nullity_histogram(n);
        assert_eq!(*h.get(&0).unwrap_or(&0), non_zd_formula(n));
        let mass: u128 = h.iter().map(|(&k, &v)| (k as u128) * (v as u128)).sum();
        assert_eq!(mass, total_mass_formula(n));
        if n >= 4 {
            let mid = 1usize << (n - 2);
            assert_eq!(*h.get(&mid).unwrap_or(&0), 42 * (1usize << (n - 4)));
            let top = (1usize << (n - 1)) - 4;
            assert_eq!(*h.get(&top).unwrap_or(&0), 2 * non_zd_formula(n - 1));
            let mut k = 1usize;
            while 4 * k < top {
                assert_eq!(
                    h.get(&(4 * k)).copied().unwrap_or(0),
                    h.get(&(top - 4 * k)).copied().unwrap_or(0)
                );
                k += 1;
            }
            if n >= 5 {
                let top_val = *h.get(&top).unwrap_or(&0);
                let low_val = *h.get(&4).unwrap_or(&0);
                assert_eq!(top_val - low_val, 3 * ((1usize << (n - 1)) - 2));
            }
        }
    }

    // 4. Exhaustive split-phase classification & mirror conservation across ALL 2^n signatures for CD_4..CD_8!
    let mut split_phase_counts = Vec::new();
    let mut cd6_flip56_gap_bin20 = usize::MAX;
    for n in 4..=8u32 {
        let num_sigs = 1usize << n;
        let std_h = nullity_histogram(n);
        let half = 1usize << (n - 1);
        let mid = 1usize << (n - 2);
        let mut class_mults: BTreeMap<Vec<(usize, usize)>, usize> = BTreeMap::new();
        let mut has_spectral_gap = false;

        let dim = 1usize << n;
        let mut pairs: Vec<(usize, usize)> = Vec::with_capacity((dim - 1) * (dim - 2) / 2);
        for i in 1..dim {
            for j in (i + 1)..dim {
                pairs.push((i ^ j, twoblade_nullity_fast(n, i, j)));
            }
        }

        for fl in 0..num_sigs {
            let mut counts = vec![0usize; half + 1];
            for &(d, nu_std) in &pairs {
                let nilp = ((d & fl).count_ones() & 1) == 1;
                let nu = if nilp { half - nu_std } else { nu_std };
                counts[nu] += 1;
            }
            if n == 6 && fl == 56 {
                assert_eq!(counts[0], 257);
                assert_eq!(counts[4], 422);
                assert_eq!(counts[8], 364);
                assert_eq!(counts[12], 336);
                assert_eq!(counts[16], 168);
                assert_eq!(counts[20], 0);
                assert_eq!(counts[24], 56);
                assert_eq!(counts[28], 172);
                assert_eq!(counts[32], 178);
                cd6_flip56_gap_bin20 = counts[20];
            }
            assert_eq!(counts[mid], 42 * (1usize << (n - 4)));
            for v in (0..=half).step_by(4) {
                let std_sum = std_h.get(&v).copied().unwrap_or(0)
                    + std_h.get(&(half - v)).copied().unwrap_or(0);
                assert_eq!(counts[v] + counts[half - v], std_sum);
            }
            let top = half - 4;
            for v in (4..=top).step_by(4) {
                if counts[v] == 0 {
                    has_spectral_gap = true;
                }
            }
            let key: Vec<(usize, usize)> = counts
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c > 0)
                .map(|(k, &c)| (k, c))
                .collect();
            *class_mults.entry(key).or_insert(0) += 1;
        }
        let mut mults: Vec<usize> = class_mults.values().copied().collect();
        mults.sort_unstable();
        let expected_classes = 1usize << (n - 2);
        assert_eq!(class_mults.len(), expected_classes);
        split_phase_counts.push((n, class_mults.len(), mults, 42 * (1usize << (n - 4)), has_spectral_gap));
    }
    assert_eq!(cd6_flip56_gap_bin20, 0);

    // 5. Pillar 3: G_n^comp, shell degrees, Hurwitz-Radon rupture & asymmetric doubling tower for n = 3..8
    let mut hurwitz_table = Vec::new();
    for n in 3..=8u32 {
        let dim = 1usize << n;
        let cliq = cd_max_clique(n);
        assert_eq!(cliq.len(), n as usize + 5);
        let mut deg_set = BTreeSet::new();
        if n <= 6 {
            let mut univ = Vec::new();
            for j in 0..dim {
                let mut deg = 0usize;
                for x in 0..dim {
                    if x == j {
                        continue;
                    }
                    let rc = right_compat(n, j, x);
                    if j > 0 && x > 0 {
                        assert_eq!(rc, twoblade_nullity_fast(n, j, x) == 0);
                    }
                    if rc {
                        deg += 1;
                    }
                }
                if deg == dim - 1 {
                    univ.push(j);
                }
                deg_set.insert(deg);
            }
            if n >= 4 {
                assert_eq!(univ, vec![0, 1usize << (n - 1)]);
            }
            assert!(is_norm_mult_pair(n, &(0..dim).collect::<Vec<_>>(), &cliq));
            if n >= 4 {
                let drw = doubled_right_witness(n);
                assert_eq!(drw.len(), 2 * (n as usize + 4));
                assert!(is_norm_mult_pair(n, &(0..(dim / 2)).collect::<Vec<_>>(), &drw));
            }
        } else {
            for j in 0..dim {
                let mut deg = 0usize;
                for x in 0..dim {
                    if x == j {
                        continue;
                    }
                    let rc = j == 0 || x == 0 || twoblade_nullity_fast(n, j, x) == 0;
                    if rc {
                        deg += 1;
                    }
                }
                deg_set.insert(deg);
            }
        }
        let expected_degs: Vec<usize> = (3..=n)
            .map(|k| (1usize << k) + 2 * ((n - k) as usize) - 1)
            .collect();
        let actual_degs: Vec<usize> = deg_set.into_iter().collect();
        assert_eq!(actual_degs, expected_degs);
        let asym_s = if n >= 4 { 2 * (n as usize + 4) } else { 8 };
        hurwitz_table.push((n, n as usize + 5, hurwitz_radon(n), asym_s, actual_degs));
    }

    // 6. Sedenion Triple-42, exact Pathion r_max=14 (280 7+7 subspaces) & Chingon witness
    let (bad4, c10, c11, fano, bk_ok) = audit_sedenion_42();
    assert_eq!(bad4, 42);
    assert_eq!(c10, 42);
    assert_eq!(c11, 0);
    assert_eq!(fano, (7, 28, 7));
    assert!(bk_ok);

    let (p_max, p_cnt, p_fail, p_bal, p_u016) = audit_pathion_exact();
    let w14 = [0, 1, 2, 4, 5, 8, 10, 16, 17, 18, 20, 21, 24, 26];
    let w16 = [0, 4, 6, 8, 11, 13, 14, 24, 31, 32, 36, 38, 56, 57, 60, 63];
    let pathion_14_ok = is_norm_mult_pair(5, &w14, &w14);
    let chingon_16_ok = is_norm_mult_pair(6, &w16, &w16);
    assert!(pathion_14_ok);
    assert!(chingon_16_ok);

    AuditSummary {
        cocycle_checked_dim5: cocycle_count,
        terrace_verified_up_to: 8,
        split_phase_counts,
        hurwitz_table,
        sedenion_bad_planes: bad4,
        sedenion_10d_count: c10,
        sedenion_11d_count: c11,
        sedenion_fano_split: fano,
        sedenion_box_kites_ok: bk_ok,
        pathion_14_ok,
        pathion_exact_max_dim: p_max,
        pathion_14d_count: p_cnt,
        pathion_greedy_ge8_failures: p_fail,
        pathion_all_14d_balanced_7_7: p_bal,
        pathion_all_14d_contain_0_16: p_u016,
        cd6_flip56_gap_bin20,
        chingon_16_ok,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_full_audit_passes() {
        let s = run_full_audit();
        assert_eq!(s.cocycle_checked_dim5, 32 * 32 * 32);
        assert_eq!(s.terrace_verified_up_to, 8);
        assert_eq!(s.sedenion_bad_planes, 42);
        assert_eq!(s.sedenion_10d_count, 42);
        assert_eq!(s.sedenion_11d_count, 0);
        assert_eq!(s.sedenion_fano_split, (7, 28, 7));
        assert!(s.sedenion_box_kites_ok);
        assert!(s.pathion_14_ok);
        assert_eq!(s.pathion_exact_max_dim, 14);
        assert_eq!(s.pathion_14d_count, 280);
        assert_eq!(s.pathion_greedy_ge8_failures, 0);
        assert!(s.pathion_all_14d_balanced_7_7);
        assert!(s.pathion_all_14d_contain_0_16);
        assert_eq!(s.cd6_flip56_gap_bin20, 0);
        assert!(s.chingon_16_ok);
    }

    #[test]
    fn test_negative_boundaries() {
        let bad11: Vec<usize> = (0..11).collect();
        assert!(!is_norm_mult_pair(4, &bad11, &bad11));
        assert!(!right_compat(4, 1, 10));
        assert!(!right_compat(4, 1, 16));
        assert_eq!(twoblade_nullity_gamma(0, 0, 0, 0), 0);
        assert_eq!(cd_max_clique(6).len(), 11);
        assert_eq!(hurwitz_radon(6), 12);
        assert!(cd_max_clique(6).len() < hurwitz_radon(6));
        let h_std = nullity_histogram_gamma(4, 0);
        let h_fl8 = nullity_histogram_gamma(4, 8);
        assert_ne!(h_std.get(&0), h_fl8.get(&0));
        assert_eq!(
            h_fl8.get(&0).copied().unwrap_or(0) + h_fl8.get(&8).copied().unwrap_or(0),
            63
        );
        assert_eq!(h_fl8.get(&4).copied().unwrap_or(0), 42);
    }

    #[test]
    fn test_exact_integer_multiplication_norm_in_witnesses() {
        let w14 = [0, 1, 2, 4, 5, 8, 10, 16, 17, 18, 20, 21, 24, 26];
        let mut x = [0i64; 32];
        let mut y = [0i64; 32];
        for (idx, &basis) in w14.iter().enumerate() {
            x[basis] = (idx as i64) * 3 - 17;
            y[basis] = (idx as i64) * 5 - 29;
        }
        let mut z = [0i64; 32];
        for i in 0..32 {
            if x[i] == 0 {
                continue;
            }
            for j in 0..32 {
                if y[j] == 0 {
                    continue;
                }
                z[i ^ j] += (cd_sign(5, i, j) as i64) * x[i] * y[j];
            }
        }
        let nx: i128 = x.iter().map(|&v| (v as i128) * (v as i128)).sum();
        let ny: i128 = y.iter().map(|&v| (v as i128) * (v as i128)).sum();
        let nz: i128 = z.iter().map(|&v| (v as i128) * (v as i128)).sum();
        assert_eq!(nz, nx * ny);
    }
}
