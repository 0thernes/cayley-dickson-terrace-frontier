/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * libFuzzer harness (Build Standard B15) for cd_terrace ISO C11 engine.
 * Build with: clang -std=c11 -O1 -g -fsanitize=fuzzer,address,undefined \
 *   -Iinclude src/cd_terrace.c tests/fuzz_libfuzzer.c -o build/fuzz_libfuzzer
 */

#include "cd_terrace.h"
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 4u) {
        return 0;
    }
    uint32_t n = 1u + (uint32_t)(data[0] % 6u);
    uint32_t dim = 1u << n;
    uint32_t flip = (uint32_t)data[1] & (dim - 1u);
    uint32_t i = (uint32_t)data[2] & (dim - 1u);
    uint32_t j = (uint32_t)data[3] & (dim - 1u);

    if (cd_sign_gamma_direct(n, flip, i, j) != cd_sign_gamma_factored(n, flip, i, j)) {
        abort();
    }
    if (i > 0u && j > 0u && i != j) {
        if (cd_twoblade_nullity_direct(n, i, j) != cd_twoblade_nullity_fast(n, i, j)) {
            abort();
        }
        if ((cd_twoblade_nullity_fast(n, i, j) == 0u) != cd_right_compat(n, i, j)) {
            abort();
        }
    }
    return 0;
}
