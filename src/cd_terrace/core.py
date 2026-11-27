# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Core exact-integer algorithms for Generalized Cayley-Dickson Algebras CD_n(gamma)."""

from __future__ import annotations

from collections import Counter
from collections.abc import Sequence
from functools import cache

PATHION_WITNESS_14: tuple[int, ...] = (0, 1, 2, 4, 5, 8, 10, 16, 17, 18, 20, 21, 24, 26)
CHINGON_WITNESS_16: tuple[int, ...] = (
    0,
    4,
    6,
    8,
    11,
    13,
    14,
    24,
    31,
    32,
    36,
    38,
    56,
    57,
    60,
    63,
)


def _validate_indices(n: int, *indices: int) -> None:
    if n < 0:
        raise ValueError(f"n must be non-negative, got {n}")
    dim = 1 << n
    for idx in indices:
        if idx < 0 or idx >= dim:
            raise ValueError(f"basis index {idx} out of range [0, {dim}) for CD_{n}")


@cache
def cd_sign(n: int, i: int, j: int) -> int:
    """Standard Euclidean Cayley-Dickson multiplication sign sigma_n(i, j) in {-1, +1}."""
    _validate_indices(n, i, j)
    if n == 0:
        return 1
    h = 1 << (n - 1)
    if i < h:
        if j < h:
            return cd_sign(n - 1, i, j)
        return cd_sign(n - 1, j - h, i)
    a = i - h
    if j < h:
        if j == 0:
            return cd_sign(n - 1, a, 0)
        return -cd_sign(n - 1, a, j)
    b = j - h
    if b == 0:
        return -cd_sign(n - 1, 0, a)
    return cd_sign(n - 1, b, a)


def cd_sign_gamma_direct(n: int, flip_mask: int, i: int, j: int) -> int:
    """Direct recursive generalized Cayley-Dickson sign sigma_n^gamma(i, j)."""
    _validate_indices(n, i, j)
    if n == 0:
        return 1
    h = 1 << (n - 1)
    flipped = ((flip_mask >> (n - 1)) & 1) == 1
    if i < h:
        if j < h:
            return cd_sign_gamma_direct(n - 1, flip_mask, i, j)
        return cd_sign_gamma_direct(n - 1, flip_mask, j - h, i)
    a = i - h
    if j < h:
        if j == 0:
            return cd_sign_gamma_direct(n - 1, flip_mask, a, 0)
        return -cd_sign_gamma_direct(n - 1, flip_mask, a, j)
    b = j - h
    raw = (
        -cd_sign_gamma_direct(n - 1, flip_mask, 0, a)
        if b == 0
        else cd_sign_gamma_direct(n - 1, flip_mask, b, a)
    )
    return -raw if flipped else raw


def cd_sign_gamma_factored(n: int, flip_mask: int, i: int, j: int) -> int:
    """Pillar 1 sign-cocycle factorization: sigma_n^std(i, j) * (-1)^popcount(i & j & flip)."""
    _validate_indices(n, i, j)
    mask = (1 << n) - 1
    parity = ((i & j & flip_mask & mask).bit_count() & 1) == 1
    s = cd_sign(n, i, j)
    return -s if parity else s


def block_delta(n: int, i: int, j: int, k: int) -> int:
    """Exact 2x2 block determinant sign delta_n^std(i, j, k) in {-1, +1}."""
    _validate_indices(n, i, j, k)
    d = i ^ j
    kp = k ^ d
    return cd_sign(n, i, k) * cd_sign(n, i, kp) * cd_sign(n, j, k) * cd_sign(n, j, kp)


def twoblade_nullity_direct(n: int, i: int, j: int) -> int:
    """Direct standard 2-blade nullity via counting singular 2x2 blocks."""
    _validate_indices(n, i, j)
    dim = 1 << n
    sing = sum(1 for k in range(dim) if block_delta(n, i, j, k) == 1)
    return sing // 2


def twoblade_nullity_fast(n: int, i: int, j: int) -> int:
    """O(n) exact standard 2-blade nullity via the proved 4-case doubling recurrence."""
    _validate_indices(n, i, j)
    if n <= 3:
        return 0
    a, b = (i, j) if i < j else (j, i)
    if a == 0 or a == b:
        return 0
    h = 1 << (n - 1)
    if b < h:
        return 2 * twoblade_nullity_fast(n - 1, a, b)
    if a >= h:
        if a == h:
            return 0
        return 2 * twoblade_nullity_fast(n - 1, a - h, b - h)
    bh = b - h
    if bh == 0 or bh == a:
        return 0
    return h - 4 - 2 * twoblade_nullity_fast(n - 1, a, bh)


def twoblade_nullity_gamma(n: int, flip_mask: int, i: int, j: int) -> int:
    """Generalized 2-blade nullity via the proved Nilpotent Mirror Law."""
    _validate_indices(n, i, j)
    if n == 0:
        return 0
    nu = twoblade_nullity_fast(n, i, j)
    mask = (1 << n) - 1
    nilp = (((i ^ j) & flip_mask & mask).bit_count() & 1) == 1
    return (1 << (n - 1)) - nu if nilp else nu


def hurwitz_radon(n: int) -> int:
    """Classical Hurwitz-Radon number rho(2^n) = 8 * (n // 4) + 2^(n % 4)."""
    return 8 * (n // 4) + (1 << (n % 4))


def non_zd_formula(n: int) -> int:
    """Exact zero-divisor-free 2-blade count (6n - 9) * 2^(n - 2) + 3 for n >= 3."""
    if n < 3:
        raise ValueError("Formula requires n >= 3")
    return (6 * n - 9) * (1 << (n - 2)) + 3


def total_mass_formula(n: int) -> int:
    """Exact total 2-blade nullity mass 8*(2^(n-1)-1)*(2^(n-2)-1)*(2^(n-3)-1) for n >= 3."""
    if n < 3:
        raise ValueError("Formula requires n >= 3")
    return 8 * ((1 << (n - 1)) - 1) * ((1 << (n - 2)) - 1) * ((1 << (n - 3)) - 1)


def nullity_histogram_gamma(n: int, flip_mask: int) -> dict[int, int]:
    """Exact 2-blade nullity histogram for CD_n(flip_mask)."""
    dim = 1 << n
    counts: Counter[int] = Counter()
    for i in range(1, dim):
        for j in range(i + 1, dim):
            counts[twoblade_nullity_gamma(n, flip_mask, i, j)] += 1
    return dict(sorted(counts.items()))


def nullity_histogram(n: int) -> dict[int, int]:
    """Exact Euclidean 2-blade nullity histogram for CD_n."""
    return nullity_histogram_gamma(n, 0)


def right_compat(n: int, j: int, x: int) -> bool:
    """Check right-multiplier compatibility edge in G_n^comp."""
    dim = 1 << n
    if j == x or j < 0 or x < 0 or j >= dim or x >= dim:
        return False
    d = j ^ x
    for i in range(dim):
        k = i ^ d
        if cd_sign(n, i, j) * cd_sign(n, k, x) + cd_sign(n, i, x) * cd_sign(n, k, j) != 0:
            return False
    return True


def is_norm_mult_pair(n: int, sl: Sequence[int], sr: Sequence[int]) -> bool:
    """Verify exact bilinear norm-multiplicativity ||xy||^2 = ||x||^2 ||y||^2 on (sl, sr)."""
    dim = 1 << n
    if any(x < 0 or x >= dim for x in sl) or any(y < 0 or y >= dim for y in sr):
        return False
    sl_set = set(sl)
    sr_set = set(sr)
    if len(sl_set) != len(sl) or len(sr_set) != len(sr):
        return False
    sl_sorted = sorted(sl_set)
    for idx, i in enumerate(sl_sorted):
        for k in sl_sorted[idx + 1 :]:
            d = i ^ k
            for j in sr_set:
                l_idx = j ^ d
                if l_idx > j and l_idx in sr_set and (
                    cd_sign(n, i, j) * cd_sign(n, k, l_idx)
                    + cd_sign(n, i, l_idx) * cd_sign(n, k, j)
                    != 0
                ):
                    return False
    return True


def cd_max_clique(n: int) -> list[int]:
    """Canonical maximum compatibility clique witness of size n + 5 for n >= 3."""
    if n < 3:
        raise ValueError("Requires n >= 3")
    return list(range(8)) + [1 << k for k in range(3, n)]


def doubled_right_witness(n: int) -> list[int]:
    """Canonical asymmetric doubling right-multiplier witness of size 2(n + 4) for n >= 4."""
    if n < 4:
        raise ValueError("Requires n >= 4")
    h = 1 << (n - 1)
    base = cd_max_clique(n - 1)
    return base + [x + h for x in base]
