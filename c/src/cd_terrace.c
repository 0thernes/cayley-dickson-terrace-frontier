/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 */

#include "cd_terrace.h"
#include <stdio.h>
#include <string.h>

static inline uint32_t cd_popcount32(uint32_t x) {
    uint32_t c = 0u;
    while (x != 0u) {
        x &= (x - 1u);
        c++;
    }
    return c;
}

int8_t cd_sign(uint32_t n, uint32_t i, uint32_t j) {
    if (n > CD_MAX_N) {
        return 0;
    }
    if (n == 0u) {
        return 1;
    }
    uint32_t dim = 1u << n;
    if (i >= dim || j >= dim) {
        return 0;
    }
    uint32_t h = 1u << (n - 1u);
    if (i < h) {
        if (j < h) {
            return cd_sign(n - 1u, i, j);
        }
        return cd_sign(n - 1u, j - h, i);
    }
    uint32_t a = i - h;
    if (j < h) {
        if (j == 0u) {
            return cd_sign(n - 1u, a, 0u);
        }
        return (int8_t)(-cd_sign(n - 1u, a, j));
    }
    uint32_t b = j - h;
    if (b == 0u) {
        return (int8_t)(-cd_sign(n - 1u, 0u, a));
    }
    return cd_sign(n - 1u, b, a);
}

int8_t cd_sign_gamma_direct(uint32_t n, uint32_t flip_mask, uint32_t i, uint32_t j) {
    if (n > CD_MAX_N) {
        return 0;
    }
    if (n == 0u) {
        return 1;
    }
    uint32_t dim = 1u << n;
    if (i >= dim || j >= dim) {
        return 0;
    }
    uint32_t h = 1u << (n - 1u);
    bool flipped = ((flip_mask >> (n - 1u)) & 1u) != 0u;
    if (i < h) {
        if (j < h) {
            return cd_sign_gamma_direct(n - 1u, flip_mask, i, j);
        }
        return cd_sign_gamma_direct(n - 1u, flip_mask, j - h, i);
    }
    uint32_t a = i - h;
    if (j < h) {
        if (j == 0u) {
            return cd_sign_gamma_direct(n - 1u, flip_mask, a, 0u);
        }
        return (int8_t)(-cd_sign_gamma_direct(n - 1u, flip_mask, a, j));
    }
    uint32_t b = j - h;
    int8_t raw = (b == 0u)
        ? (int8_t)(-cd_sign_gamma_direct(n - 1u, flip_mask, 0u, a))
        : cd_sign_gamma_direct(n - 1u, flip_mask, b, a);
    return flipped ? (int8_t)(-raw) : raw;
}

int8_t cd_sign_gamma_factored(uint32_t n, uint32_t flip_mask, uint32_t i, uint32_t j) {
    if (n > CD_MAX_N) {
        return 0;
    }
    uint32_t mask = (1u << n) - 1u;
    uint32_t pc = cd_popcount32(i & j & flip_mask & mask);
    int8_t s = cd_sign(n, i, j);
    return ((pc & 1u) != 0u) ? (int8_t)(-s) : s;
}

int8_t cd_block_delta(uint32_t n, uint32_t i, uint32_t j, uint32_t k) {
    if (n > CD_MAX_N) {
        return 0;
    }
    uint32_t dim = 1u << n;
    if (i >= dim || j >= dim || k >= dim) {
        return 0;
    }
    uint32_t d = i ^ j;
    uint32_t kp = k ^ d;
    int32_t p = (int32_t)cd_sign(n, i, k) * (int32_t)cd_sign(n, i, kp)
              * (int32_t)cd_sign(n, j, k) * (int32_t)cd_sign(n, j, kp);
    return (int8_t)p;
}

uint32_t cd_twoblade_nullity_direct(uint32_t n, uint32_t i, uint32_t j) {
    if (n > CD_MAX_N) {
        return 0u;
    }
    uint32_t dim = 1u << n;
    if (i >= dim || j >= dim) {
        return 0u;
    }
    uint32_t sing = 0u;
    for (uint32_t k = 0u; k < dim; k++) {
        if (cd_block_delta(n, i, j, k) == 1) {
            sing++;
        }
    }
    return sing / 2u;
}

uint32_t cd_twoblade_nullity_fast(uint32_t n, uint32_t i, uint32_t j) {
    if (n <= 3u || n > CD_MAX_N) {
        return 0u;
    }
    uint32_t dim = 1u << n;
    if (i >= dim || j >= dim) {
        return 0u;
    }
    uint32_t a = (i < j) ? i : j;
    uint32_t b = (i < j) ? j : i;
    if (a == 0u || a == b) {
        return 0u;
    }
    uint32_t h = 1u << (n - 1u);
    if (b < h) {
        return 2u * cd_twoblade_nullity_fast(n - 1u, a, b);
    }
    if (a >= h) {
        if (a == h) {
            return 0u;
        }
        return 2u * cd_twoblade_nullity_fast(n - 1u, a - h, b - h);
    }
    uint32_t bh = b - h;
    if (bh == 0u || bh == a) {
        return 0u;
    }
    return h - 4u - 2u * cd_twoblade_nullity_fast(n - 1u, a, bh);
}

uint32_t cd_twoblade_nullity_gamma(uint32_t n, uint32_t flip_mask, uint32_t i, uint32_t j) {
    if (n == 0u || n > CD_MAX_N) {
        return 0u;
    }
    uint32_t dim = 1u << n;
    if (i >= dim || j >= dim) {
        return 0u;
    }
    uint32_t nu = cd_twoblade_nullity_fast(n, i, j);
    uint32_t mask = (1u << n) - 1u;
    bool nilp = ((cd_popcount32((i ^ j) & flip_mask & mask)) & 1u) != 0u;
    return nilp ? ((1u << (n - 1u)) - nu) : nu;
}

uint32_t cd_hurwitz_radon(uint32_t n) {
    return 8u * (n / 4u) + (1u << (n % 4u));
}

uint64_t cd_non_zd_formula(uint32_t n) {
    if (n < 3u || n > 60u) {
        return 0u;
    }
    return (uint64_t)(6u * n - 9u) * (1ULL << (n - 2u)) + 3ULL;
}

uint64_t cd_total_mass_formula(uint32_t n) {
    if (n < 3u || n > 20u) {
        return 0u;
    }
    uint64_t a = (1ULL << (n - 1u)) - 1ULL;
    uint64_t b = (1ULL << (n - 2u)) - 1ULL;
    uint64_t c = (1ULL << (n - 3u)) - 1ULL;
    return 8ULL * a * b * c;
}

bool cd_right_compat(uint32_t n, uint32_t j, uint32_t x) {
    if (j == x || n > CD_MAX_N) {
        return false;
    }
    uint32_t dim = 1u << n;
    if (j >= dim || x >= dim) {
        return false;
    }
    uint32_t d = j ^ x;
    for (uint32_t i = 0u; i < dim; i++) {
        uint32_t k = i ^ d;
        int32_t s = (int32_t)cd_sign(n, i, j) * (int32_t)cd_sign(n, k, x)
                  + (int32_t)cd_sign(n, i, x) * (int32_t)cd_sign(n, k, j);
        if (s != 0) {
            return false;
        }
    }
    return true;
}

bool cd_is_norm_mult_pair(uint32_t n, const uint32_t *sl, size_t len_l,
                          const uint32_t *sr, size_t len_r) {
    if (n > CD_MAX_N || sl == NULL || sr == NULL) {
        return false;
    }
    uint32_t dim = 1u << n;
    bool in_l[CD_MAX_DIM];
    bool in_r[CD_MAX_DIM];
    memset(in_l, 0, sizeof(in_l));
    memset(in_r, 0, sizeof(in_r));
    for (size_t idx = 0u; idx < len_l; idx++) {
        if (sl[idx] >= dim || in_l[sl[idx]]) {
            return false;
        }
        in_l[sl[idx]] = true;
    }
    for (size_t idx = 0u; idx < len_r; idx++) {
        if (sr[idx] >= dim || in_r[sr[idx]]) {
            return false;
        }
        in_r[sr[idx]] = true;
    }
    for (size_t a = 0u; a < len_l; a++) {
        for (size_t b = a + 1u; b < len_l; b++) {
            uint32_t i = sl[a];
            uint32_t k = sl[b];
            uint32_t d = i ^ k;
            for (size_t c = 0u; c < len_r; c++) {
                uint32_t j = sr[c];
                uint32_t l = j ^ d;
                if (l > j && l < dim && in_r[l]) {
                    int32_t s = (int32_t)cd_sign(n, i, j) * (int32_t)cd_sign(n, k, l)
                              + (int32_t)cd_sign(n, i, l) * (int32_t)cd_sign(n, k, j);
                    if (s != 0) {
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

/* Exact Pathion CD_5 greedy clique-cover audit proving r_max(CD_5) = 14 and strict 7+7 balance. */
static int cd_audit_pathion_exact(void) {
    uint16_t bad_lo[42];
    size_t n_bad_lo = 0u;
    uint8_t cross_a[256][8];
    uint8_t cross_b[256][8];
    uint8_t cross_len[256];
    memset(cross_len, 0, sizeof(cross_len));
    size_t total_bad = 0u;

    for (uint32_t a = 0u; a < 32u; a++) {
        for (uint32_t b = a + 1u; b < 32u; b++) {
            for (uint32_t c = b + 1u; c < 32u; c++) {
                uint32_t d = a ^ b ^ c;
                if (d > c) {
                    int32_t p1 = (int32_t)cd_sign(5u, a, c) * (int32_t)cd_sign(5u, b, d)
                               + (int32_t)cd_sign(5u, a, d) * (int32_t)cd_sign(5u, b, c);
                    int32_t p2 = (int32_t)cd_sign(5u, a, b) * (int32_t)cd_sign(5u, c, d)
                               + (int32_t)cd_sign(5u, a, d) * (int32_t)cd_sign(5u, c, b);
                    int32_t p3 = (int32_t)cd_sign(5u, a, b) * (int32_t)cd_sign(5u, d, c)
                               + (int32_t)cd_sign(5u, a, c) * (int32_t)cd_sign(5u, d, b);
                    if (p1 != 0 || p2 != 0 || p3 != 0) {
                        total_bad++;
                        if (d < 16u && n_bad_lo < 42u) {
                            bad_lo[n_bad_lo++] = (uint16_t)((1u << a) | (1u << b) | (1u << c) | (1u << d));
                        } else if (b < 16u && c >= 16u) {
                            uint32_t key = ((d - 16u) << 4) | (c - 16u);
                            uint8_t idx = cross_len[key];
                            if (idx < 8u) {
                                cross_a[key][idx] = (uint8_t)a;
                                cross_b[key][idx] = (uint8_t)b;
                                cross_len[key] = (uint8_t)(idx + 1u);
                            }
                        }
                    }
                }
            }
        }
    }
    if (total_bad != 630u || n_bad_lo != 42u) {
        return 14;
    }

    size_t valid_ge8 = 0u;
    for (uint32_t lo = 0u; lo < 65536u; lo++) {
        uint32_t pop = cd_popcount32(lo);
        if (pop < 8u) {
            continue;
        }
        uint16_t mu = (uint16_t)lo;
        bool ok_lo = true;
        for (size_t m = 0u; m < 42u; m++) {
            if ((mu & bad_lo[m]) == bad_lo[m]) {
                ok_lo = false;
                break;
            }
        }
        if (!ok_lo) {
            continue;
        }
        valid_ge8++;
        uint8_t cliques[16][16];
        uint8_t clen[16];
        size_t n_cliques = 0u;
        for (int ui = 15; ui >= 0; ui--) {
            uint32_t u = (uint32_t)ui;
            bool placed = false;
            for (size_t ci = 0u; ci < n_cliques; ci++) {
                bool can_add = true;
                for (uint8_t vi = 0u; vi < clen[ci]; vi++) {
                    uint32_t v = (uint32_t)cliques[ci][vi];
                    uint32_t key = (v << 4) | u;
                    bool edge = false;
                    for (uint8_t pi = 0u; pi < cross_len[key]; pi++) {
                        if (((mu >> cross_a[key][pi]) & 1u) != 0u &&
                            ((mu >> cross_b[key][pi]) & 1u) != 0u) {
                            edge = true;
                            break;
                        }
                    }
                    if (!edge) {
                        can_add = false;
                        break;
                    }
                }
                if (can_add) {
                    cliques[ci][clen[ci]++] = (uint8_t)u;
                    placed = true;
                    break;
                }
            }
            if (!placed) {
                cliques[n_cliques][0] = (uint8_t)u;
                clen[n_cliques] = 1u;
                n_cliques++;
            }
        }
        if (pop + (uint32_t)n_cliques > 13u) {
            return 15;
        }
    }
    if (valid_ge8 != 2995u) {
        return 16;
    }
    return 0;
}

int cd_run_full_audit(bool verbose) {
    /* 1. Cocycle factorization across all 32x32x32 triples of CD_5(gamma) */
    for (uint32_t fl = 0u; fl < 32u; fl++) {
        for (uint32_t i = 0u; i < 32u; i++) {
            for (uint32_t j = 0u; j < 32u; j++) {
                if (cd_sign_gamma_direct(5u, fl, i, j) != cd_sign_gamma_factored(5u, fl, i, j)) {
                    return 1;
                }
            }
        }
    }

    /* 2. Cross-check fast doubling nullity vs direct block-sign nullity for CD_3..CD_6 */
    for (uint32_t n = 3u; n <= 6u; n++) {
        uint32_t dim = 1u << n;
        for (uint32_t i = 1u; i < dim; i++) {
            for (uint32_t j = i + 1u; j < dim; j++) {
                if (cd_twoblade_nullity_direct(n, i, j) != cd_twoblade_nullity_fast(n, i, j)) {
                    return 2;
                }
            }
        }
    }

    /* 3. Terrace law & exhaustive split mirror conservation across ALL 496 algebras CD_4..CD_8 (ZERO striding!) */
    static uint16_t pair_d[32385];
    static uint8_t pair_nu[32385];
    for (uint32_t n = 4u; n <= 8u; n++) {
        uint32_t dim = 1u << n;
        uint32_t half = 1u << (n - 1u);
        uint32_t mid = 1u << (n - 2u);
        uint32_t std_hist[129];
        memset(std_hist, 0, sizeof(std_hist));
        uint64_t mass = 0ULL;
        size_t n_pairs = 0u;
        for (uint32_t i = 1u; i < dim; i++) {
            for (uint32_t j = i + 1u; j < dim; j++) {
                uint32_t nu = cd_twoblade_nullity_fast(n, i, j);
                std_hist[nu]++;
                mass += (uint64_t)nu;
                pair_d[n_pairs] = (uint16_t)(i ^ j);
                pair_nu[n_pairs] = (uint8_t)nu;
                n_pairs++;
            }
        }
        if ((uint64_t)std_hist[0] != cd_non_zd_formula(n)) {
            return 3;
        }
        if (mass != cd_total_mass_formula(n)) {
            return 4;
        }
        if (std_hist[mid] != 42u * (1u << (n - 4u))) {
            return 5;
        }
        uint32_t top = half - 4u;
        for (uint32_t v = 4u; v < top; v += 4u) {
            if (std_hist[v] != std_hist[top - v]) {
                return 6;
            }
        }
        /* Exhaustive across ALL 2^n signatures for EVERY level n = 4..8 (all 496 algebras!) */
        for (uint32_t fl = 0u; fl < dim; fl++) {
            uint32_t h[129];
            memset(h, 0, sizeof(h));
            for (size_t p = 0u; p < n_pairs; p++) {
                uint32_t nu_std = (uint32_t)pair_nu[p];
                bool nilp = (cd_popcount32((uint32_t)pair_d[p] & fl) & 1u) != 0u;
                uint32_t nu = nilp ? (half - nu_std) : nu_std;
                h[nu]++;
            }
            if (h[mid] != 42u * (1u << (n - 4u))) {
                return 7;
            }
            for (uint32_t v = 0u; v <= half; v += 4u) {
                if (h[v] + h[half - v] != std_hist[v] + std_hist[half - v]) {
                    return 8;
                }
            }
            if (n == 6u && fl == 56u) {
                if (h[16] != 168u || h[20] != 0u || h[24] != 56u) {
                    return 17;
                }
            }
        }
    }

    /* 4. Pillar 3 & Pillar 4 witnesses, negative checks, and exact Pathion r_max=14 audit */
    if (cd_hurwitz_radon(6u) != 12u || (6u + 5u) >= cd_hurwitz_radon(6u)) {
        return 9;
    }
    static const uint32_t w14[14] = {0, 1, 2, 4, 5, 8, 10, 16, 17, 18, 20, 21, 24, 26};
    static const uint32_t w16[16] = {0, 4, 6, 8, 11, 13, 14, 24, 31, 32, 36, 38, 56, 57, 60, 63};
    if (!cd_is_norm_mult_pair(5u, w14, 14u, w14, 14u)) {
        return 10;
    }
    if (!cd_is_norm_mult_pair(6u, w16, 16u, w16, 16u)) {
        return 11;
    }
    static const uint32_t bad11[11] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    if (cd_is_norm_mult_pair(4u, bad11, 11u, bad11, 11u)) {
        return 12;
    }
    if (cd_right_compat(4u, 1u, 10u)) {
        return 13;
    }
    int prc = cd_audit_pathion_exact();
    if (prc != 0) {
        return prc;
    }

    if (verbose) {
        printf("ISO C11 cd_terrace v%s full audit: ALL CHECKS PASSED (all 496 algebras CD_4..CD_8, CD_5 r_max=14, CD_6(56) gap).\n",
               CD_TERRACE_VERSION);
    }
    return 0;
}
