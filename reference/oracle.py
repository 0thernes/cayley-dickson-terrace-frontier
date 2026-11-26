# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Independent naive-algebra reference oracle for generalized Cayley-Dickson algebras.

This module intentionally implements generalized Cayley-Dickson multiplication DIRECTLY
via exact rational/integer recursive doubling (a, b)(c, d) = (ac + gamma * d_bar b, d a + b c_bar)
WITHOUT using any sign tables, cocycle factorizations, doubling recurrences, or mirror laws.
It computes exact nullspaces via exact Fraction Gaussian elimination over Q to serve as an
independent first-principles falsification oracle against `src/cd_terrace`, Rust, C11, and Lean 4.
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction


def cd_conj_vec(x: Sequence[int]) -> list[int]:
    """Cayley-Dickson involution: conj(x_0, x_1, ...) = (x_0, -x_1, ...)."""
    if not x:
        return []
    return [x[0]] + [-v for v in x[1:]]


def cd_mul_vec(x: Sequence[int], y: Sequence[int], gammas: Sequence[int]) -> list[int]:
    """Exact recursive generalized Cayley-Dickson product over Z.

    gammas = (gamma_0, ..., gamma_{n-1}) where gamma_k in {-1, +1}:
    - Standard Euclidean CD_n uses gammas = (-1, -1, ..., -1).
    - Flip mask `flip` has gamma_k = +1 iff bit k of `flip` is 1.
    Product rule: (a, b)(c, d) = (a*c + gamma_{n-1} * conj(d)*b, d*a + b*conj(c)).
    """
    n = len(gammas)
    if n == 0:
        return [x[0] * y[0]]
    h = 1 << (n - 1)
    a, b = x[:h], x[h:]
    c, d = y[:h], y[h:]
    g = gammas[-1]
    sub = gammas[:-1]
    ac = cd_mul_vec(a, c, sub)
    dbar_b = cd_mul_vec(cd_conj_vec(d), b, sub)
    da = cd_mul_vec(d, a, sub)
    b_cbar = cd_mul_vec(b, cd_conj_vec(c), sub)
    lo = [ac[i] + g * dbar_b[i] for i in range(h)]
    hi = [da[i] + b_cbar[i] for i in range(h)]
    return lo + hi


def flip_to_gammas(n: int, flip_mask: int) -> tuple[int, ...]:
    """Convert bitmask `flip_mask` to signature tuple gamma in {-1, +1}^n."""
    return tuple(1 if ((flip_mask >> k) & 1) else -1 for k in range(n))


def left_mult_matrix(x: Sequence[int], gammas: Sequence[int]) -> list[list[int]]:
    """Exact integer matrix of left multiplication L_x : y -> x * y."""
    dim = len(x)
    cols = []
    for j in range(dim):
        ej = [1 if k == j else 0 for k in range(dim)]
        cols.append(cd_mul_vec(x, ej, gammas))
    return [[cols[j][r] for j in range(dim)] for r in range(dim)]


def exact_nullity_q(mat: Sequence[Sequence[int]]) -> int:
    """Exact nullity of an integer matrix over Q via exact Fraction RREF."""
    rows = len(mat)
    cols = len(mat[0]) if rows else 0
    a = [[Fraction(v) for v in row] for row in mat]
    rank = 0
    for c in range(cols):
        pivot = None
        for r in range(rank, rows):
            if a[r][c] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        pv = a[rank][c]
        a[rank] = [v / pv for v in a[rank]]
        for r in range(rows):
            if r != rank and a[r][c] != 0:
                factor = a[r][c]
                a[r] = [a[r][k] - factor * a[rank][k] for k in range(cols)]
        rank += 1
    return cols - rank


def naive_twoblade_nullity(n: int, flip_mask: int, i: int, j: int) -> int:
    """First-principles nullity of L_{e_i + e_j} in CD_n(flip_mask) via exact Q Gaussian elimination."""
    dim = 1 << n
    x = [1 if k in (i, j) else 0 for k in range(dim)]
    mat = left_mult_matrix(x, flip_to_gammas(n, flip_mask))
    return exact_nullity_q(mat)


def norm_sq_vec(x: Sequence[int]) -> int:
    """Euclidean squared norm ||x||^2 = sum x_k^2."""
    return sum(v * v for v in x)
