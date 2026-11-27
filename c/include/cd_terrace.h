/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Strict ISO C11 verifier for Generalized Cayley-Dickson Algebras CD_n(gamma):
 * Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation,
 * Euclidean Coordinate Right-Multiplier Rupture, and Pathion Exact Ceiling (r_max = 14).
 */

#ifndef CD_TERRACE_H
#define CD_TERRACE_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Maximum algebra level supported in fixed-stack buffers (CD_8 = 256D). */
#define CD_MAX_N 8u
#define CD_MAX_DIM (1u << CD_MAX_N)

/* Standard Euclidean Cayley-Dickson sign sigma_n(i, j) in {-1, +1}; returns 0 if n > CD_MAX_N. */
int8_t cd_sign(uint32_t n, uint32_t i, uint32_t j);

/* Direct recursive generalized Cayley-Dickson sign sigma_n^gamma(i, j); returns 0 if n > CD_MAX_N. */
int8_t cd_sign_gamma_direct(uint32_t n, uint32_t flip_mask, uint32_t i, uint32_t j);

/* Pillar 1 factored sign cocycle: sigma_n^std(i, j) * (-1)^popcount(i & j & flip_mask). */
int8_t cd_sign_gamma_factored(uint32_t n, uint32_t flip_mask, uint32_t i, uint32_t j);

/* Exact 2x2 block determinant sign delta_n^std(i, j, k) in {-1, +1}. */
int8_t cd_block_delta(uint32_t n, uint32_t i, uint32_t j, uint32_t k);

/* Direct 2-blade nullity nu_n^std(i, j) via block determinant sum. */
uint32_t cd_twoblade_nullity_direct(uint32_t n, uint32_t i, uint32_t j);

/* Fast O(n) exact 2-blade nullity via Pillar 2 4-case doubling recurrence. */
uint32_t cd_twoblade_nullity_fast(uint32_t n, uint32_t i, uint32_t j);

/* Generalized 2-blade nullity nu_n^gamma(i, j) via Pillar 1 Nilpotent Mirror Law. */
uint32_t cd_twoblade_nullity_gamma(uint32_t n, uint32_t flip_mask, uint32_t i, uint32_t j);

/* Classical Hurwitz-Radon function rho(2^n) = 8*(n/4) + 2^(n%4). */
uint32_t cd_hurwitz_radon(uint32_t n);

/* Exact zero-divisor-free 2-blade count formula (6n - 9) * 2^(n - 2) + 3 for n >= 3. */
uint64_t cd_non_zd_formula(uint32_t n);

/* Exact total 2-blade nullity mass 8*(2^(n-1)-1)*(2^(n-2)-1)*(2^(n-3)-1) for n >= 3. */
uint64_t cd_total_mass_formula(uint32_t n);

/* Right-multiplier compatibility edge in G_n^comp for distinct j, x < 2^n. */
bool cd_right_compat(uint32_t n, uint32_t j, uint32_t x);

/* Verify bilinear norm-multiplicativity ||x*y||^2 = ||x||^2 ||y||^2 on coordinate pair (sl, sr). */
bool cd_is_norm_mult_pair(uint32_t n, const uint32_t *sl, size_t len_l,
                          const uint32_t *sr, size_t len_r);

/* Run exhaustive C11 audit across all 496 algebras CD_4..CD_8 (zero striding), CD_5 r_max=14,
 * and CD_6(flip=56) interior spectral gap; returns 0 on PASS. */
int cd_run_full_audit(bool verbose);

#ifdef __cplusplus
}
#endif

#endif /* CD_TERRACE_H */
