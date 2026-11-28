# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Core exact-integer algorithms for Generalized Cayley-Dickson Algebras CD_n(gamma)."""

from __future__ import annotations

from collections import Counter
from collections.abc import Sequence
from functools import cache
from math import gcd

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


def gray_lock_bit(d: int, m: int) -> bool:
    """Pillar 5 Binary Reflected Gray-Code locking bit g(d, m):
    bit 0 of m for d = 0, and bit (d - 1) xor bit d of m for d >= 1."""
    if d < 0 or m < 0:
        raise ValueError(f"d and m must be non-negative, got d={d}, m={m}")
    if d == 0:
        return bool(m & 1)
    return bool(((m >> (d - 1)) ^ (m >> d)) & 1)


def is_gapped_mask(n: int, flip_mask: int) -> bool:
    """Pillar 5 exact all-n, all-signature spectral-gap criterion (T5c) for n >= 6:
    8 | flip_mask and flip_mask not in {0, 8, 2^(n-1), 2^(n-1) + 8}."""
    if n < 6:
        raise ValueError(f"Spectral-gap dichotomy requires n >= 6, got {n}")
    dim = 1 << n
    if flip_mask < 0 or flip_mask >= dim:
        raise ValueError(f"flip_mask {flip_mask} out of range [0, {dim}) for CD_{n}")
    half = 1 << (n - 1)
    return (flip_mask % 8 == 0) and flip_mask not in (0, 8, half, half + 8)


def cd_mul_gamma_vec(n: int, flip_mask: int, x: Sequence[int], y: Sequence[int]) -> list[int]:
    """Exact integer bilinear multiplication in CD_n(flip_mask)."""
    if n < 0:
        raise ValueError(f"n must be non-negative, got {n}")
    dim = 1 << n
    if len(x) != dim or len(y) != dim:
        raise ValueError(f"Vectors must have length {dim} for CD_{n}, got {len(x)} and {len(y)}")
    out = [0] * dim
    for a, xa in enumerate(x):
        if xa == 0:
            continue
        for b, yb in enumerate(y):
            if yb == 0:
                continue
            out[a ^ b] += cd_sign_gamma_factored(n, flip_mask, a, b) * xa * yb
    return out


def left_mul_matrix_gamma(n: int, flip_mask: int, x: Sequence[int]) -> list[list[int]]:
    """Exact 2^n x 2^n integer left-multiplication matrix L_x in CD_n(flip_mask)."""
    dim = 1 << n
    if len(x) != dim:
        raise ValueError(f"Vector must have length {dim} for CD_{n}")
    return [
        [cd_sign_gamma_factored(n, flip_mask, t ^ j, j) * x[t ^ j] for j in range(dim)]
        for t in range(dim)
    ]


def right_mul_matrix_gamma(n: int, flip_mask: int, x: Sequence[int]) -> list[list[int]]:
    """Exact 2^n x 2^n integer right-multiplication matrix R_x in CD_n(flip_mask)."""
    dim = 1 << n
    if len(x) != dim:
        raise ValueError(f"Vector must have length {dim} for CD_{n}")
    return [
        [cd_sign_gamma_factored(n, flip_mask, j, t ^ j) * x[t ^ j] for j in range(dim)]
        for t in range(dim)
    ]


def odd_pivot_integral_inv(mat: Sequence[Sequence[int]]) -> tuple[list[list[int]], int]:
    """Pillar 6 fraction-free odd-pivot Gauss-Jordan matrix inversion over Z (T6b):
    Given any N x N integer matrix invertible mod 2, returns (B, delta) with odd delta
    (delta % 2 == 1, hence delta != 0) satisfying B @ mat == delta * I over Z."""
    size = len(mat)
    if any(len(row) != size for row in mat):
        raise ValueError("Input matrix must be square")
    left = [list(row) for row in mat]
    right = [[1 if i == j else 0 for j in range(size)] for i in range(size)]
    for k in range(size):
        piv = next((r for r in range(k, size) if (left[r][k] & 1) == 1), None)
        if piv is None:
            raise ValueError(f"Matrix is not invertible modulo 2 (no odd pivot at column {k})")
        if piv != k:
            left[k], left[piv] = left[piv], left[k]
            right[k], right[piv] = right[piv], right[k]
        p = left[k][k]
        for i in range(size):
            if i == k:
                continue
            lik = left[i][k]
            row_l = [p * left[i][j] - lik * left[k][j] for j in range(size)]
            row_r = [p * right[i][j] - lik * right[k][j] for j in range(size)]
            g = gcd(*row_l, *row_r)
            if g > 1:
                row_l = [v // g for v in row_l]
                row_r = [v // g for v in row_r]
            left[i] = row_l
            right[i] = row_r
    delta = 1
    for i in range(size):
        delta = (delta * left[i][i]) // gcd(delta, left[i][i])
    inv = []
    for i in range(size):
        scale = delta // left[i][i]
        inv.append([scale * v for v in right[i]])
    if delta < 0:
        delta = -delta
        inv = [[-v for v in row] for row in inv]
    return inv, delta
