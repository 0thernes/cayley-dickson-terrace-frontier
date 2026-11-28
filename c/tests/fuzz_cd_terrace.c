/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Deterministic high-throughput fuzzer verifying algebraic invariants across random
 * generalized Cayley-Dickson parameters (CD_1..CD_7) with zero UB/memory errors.
 */

#include "cd_terrace.h"
#include <stdio.h>
#include <stdlib.h>

static uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    uint64_t iters = (argc > 1) ? strtoull(argv[1], NULL, 10) : 100000ULL;
    uint64_t rng = 0x20260017cafe1234ULL;

    for (uint64_t step = 0ULL; step < iters; step++) {
        uint64_t r = splitmix64(&rng);
        uint32_t n = 1u + (uint32_t)(r % 7u); /* CD_1..CD_7 */
        uint32_t dim = 1u << n;
        uint32_t flip = (uint32_t)((r >> 8) & (dim - 1u));
        uint32_t i = (uint32_t)((r >> 20) & (dim - 1u));
        uint32_t j = (uint32_t)((r >> 32) & (dim - 1u));

        /* Cocycle factorization identity */
        if (cd_sign_gamma_direct(n, flip, i, j) != cd_sign_gamma_factored(n, flip, i, j)) {
            fprintf(stderr, "Fuzz failure: cocycle mismatch at n=%u flip=%u i=%u j=%u\n", n, flip, i, j);
            return 1;
        }
        /* Anti-commutativity for distinct nonzero basis indices */
        if (i > 0u && j > 0u && i != j) {
            if (cd_sign(n, i, j) != (int8_t)(-cd_sign(n, j, i))) {
                fprintf(stderr, "Fuzz failure: anticomm at n=%u i=%u j=%u\n", n, i, j);
                return 2;
            }
            /* Direct vs doubling nullity & right-compatibility unification */
            uint32_t nu_f = cd_twoblade_nullity_fast(n, i, j);
            uint32_t nu_d = cd_twoblade_nullity_direct(n, i, j);
            if (nu_f != nu_d) {
                fprintf(stderr, "Fuzz failure: nullity mismatch at n=%u i=%u j=%u\n", n, i, j);
                return 3;
            }
            if ((nu_f == 0u) != cd_right_compat(n, i, j)) {
                fprintf(stderr, "Fuzz failure: compat/nullity mismatch at n=%u i=%u j=%u\n", n, i, j);
                return 4;
            }
            /* Nilpotent Mirror Law check */
            uint32_t nu_g = cd_twoblade_nullity_gamma(n, flip, i, j);
            uint32_t half = 1u << (n - 1u);
            if (nu_g > half) {
                fprintf(stderr, "Fuzz failure: nullity range at n=%u\n", n);
                return 5;
            }
            /* Pillar 5 (T5a): Binary Reflected Gray-Code Bit-Locking */
            if (n >= 4u) {
                uint32_t d_xor = i ^ j;
                uint32_t m_bin = nu_f / 4u;
                if (nu_f >= 4u && nu_f <= half - 4u) {
                    if ((((d_xor >> (n - 1u)) & 1u) != 0u) != cd_gray_lock_bit(0u, m_bin)) {
                        fprintf(stderr, "Fuzz failure: Gray bit d=0 at n=%u i=%u j=%u\n", n, i, j);
                        return 6;
                    }
                }
                for (uint32_t depth = 1u; depth <= n - 4u; depth++) {
                    uint32_t lo_bnd = 1u << (depth + 1u);
                    if (nu_f >= lo_bnd && nu_f <= half - lo_bnd - 4u) {
                        if ((((d_xor >> (n - 1u - depth)) & 1u) != 0u) != cd_gray_lock_bit(depth, m_bin)) {
                            fprintf(stderr, "Fuzz failure: Gray bit d=%u at n=%u i=%u j=%u\n", depth, n, i, j);
                            return 7;
                        }
                    }
                }
            }
        }
        /* Pillar 6 (T6a): randomized odd-coordinate-sum Frobenius mod-2 involution on CD_1..CD_4 */
        if (n <= 4u && (step & 15ULL) == 0ULL) {
            int64_t x[16];
            int64_t y[16];
            int64_t tmp[16];
            int64_t res[16];
            int64_t sum_x = 0;
            for (uint32_t t = 0u; t < dim; t++) {
                uint64_t rt = splitmix64(&rng);
                x[t] = (int64_t)((int32_t)(rt & 7ULL) - 3);
                y[t] = (int64_t)((int32_t)((rt >> 8) & 7ULL) - 3);
                sum_x += x[t];
            }
            if ((sum_x & 1) == 0) {
                x[0] += 1;
            }
            if (!cd_mul_gamma_vec(n, flip, x, y, tmp) || !cd_mul_gamma_vec(n, flip, x, tmp, res)) {
                return 8;
            }
            for (uint32_t t = 0u; t < dim; t++) {
                if (((res[t] - y[t]) & 1) != 0) {
                    fprintf(stderr, "Fuzz failure: Pillar 6 left mod-2 involution at n=%u flip=%u\n", n, flip);
                    return 9;
                }
            }
        }
    }
    printf("Deterministic C11 fuzzer: %llu iterations PASSED.\n", (unsigned long long)iters);
    return 0;
}
