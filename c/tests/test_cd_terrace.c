/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Unit, negative, and CLI test suite for ISO C11 cd_terrace engine.
 */

#include "cd_terrace.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv) {
    bool verify_all = (argc > 1 && strcmp(argv[1], "--verify-all") == 0);
    int rc = cd_run_full_audit(true);
    if (rc != 0) {
        fprintf(stderr, "cd_run_full_audit FAILED with code %d\n", rc);
        return rc;
    }

    /* Additional explicit boundary & witness assertions */
    assert(cd_hurwitz_radon(3u) == 8u);
    assert(cd_hurwitz_radon(4u) == 9u);
    assert(cd_hurwitz_radon(5u) == 10u);
    assert(cd_hurwitz_radon(6u) == 12u);
    assert(cd_hurwitz_radon(7u) == 16u);
    assert(cd_non_zd_formula(4u) == 63ULL);
    assert(cd_non_zd_formula(5u) == 171ULL);
    assert(cd_non_zd_formula(6u) == 435ULL);
    assert(cd_total_mass_formula(4u) == 168ULL);
    assert(cd_total_mass_formula(5u) == 2520ULL);
    assert(cd_total_mass_formula(6u) == 26040ULL);

    /* Verify [32, 20, 64] asymmetric doubling tower witness in CD_6 */
    uint32_t left32[32];
    for (uint32_t i = 0u; i < 32u; i++) {
        left32[i] = i;
    }
    static const uint32_t right20[20] = {
        0, 1, 2, 3, 4, 5, 6, 7, 8, 16,
        32, 33, 34, 35, 36, 37, 38, 39, 40, 48
    };
    assert(cd_is_norm_mult_pair(6u, left32, 32u, right20, 20u));

    /* Negative: out-of-bounds or duplicate inputs must return false/0 cleanly (zero shift UB!) */
    static const uint32_t dup[2] = {1, 1};
    assert(!cd_is_norm_mult_pair(4u, dup, 2u, dup, 2u));
    assert(!cd_right_compat(4u, 3u, 3u));
    assert(!cd_right_compat(9u, 0u, 1u));
    assert(cd_sign(99u, 0u, 0u) == 0);
    assert(cd_sign_gamma_direct(99u, 0u, 0u, 0u) == 0);
    assert(cd_twoblade_nullity_fast(99u, 0u, 1u) == 0u);
    assert(cd_twoblade_nullity_gamma(99u, 0u, 0u, 1u) == 0u);

    if (verify_all) {
        printf("CLI --verify-all PASS.\n");
    } else {
        printf("C11 unit & negative tests: ALL PASSED.\n");
    }
    return 0;
}
