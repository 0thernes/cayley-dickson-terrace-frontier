# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Quickstart demonstration of the 6 pillars of Cayley-Dickson Terrace Frontier."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from cd_terrace import (
    CHINGON_WITNESS_16,
    PATHION_WITNESS_14,
    cd_max_clique,
    cd_mul_gamma_vec,
    doubled_right_witness,
    hurwitz_radon,
    is_gapped_mask,
    is_norm_mult_pair,
    left_mul_matrix_gamma,
    non_zd_formula,
    nullity_histogram,
    nullity_histogram_gamma,
    odd_pivot_integral_inv,
    total_mass_formula,
)


def main() -> None:
    print("=== Cayley-Dickson Terrace Frontier — Quickstart Demo ===")
    for n in (4, 5, 6):
        h = nullity_histogram(n)
        print(
            f"CD_{n} (dim {1 << n:2d}): H(0)={h[0]} (formula {non_zd_formula(n)}), "
            f"midpoint H({1 << (n - 2)})={h[1 << (n - 2)]}, "
            f"mass={sum(k * v for k, v in h.items())} (formula {total_mass_formula(n)})"
        )
    print("\nPillar 1 — Split-Sedenion Nilpotent Mirror Conservation (CD_4, flip=8):")
    h_std = nullity_histogram_gamma(4, 0)
    h_fl8 = nullity_histogram_gamma(4, 8)
    print(f"  Standard (-,-,-,-): {h_std}")
    print(f"  Split    (-,-,-,+): {h_fl8}")
    print(
        f"  Conserved mirror sum H(0)+H(8): {h_std.get(0, 0) + h_std.get(8, 0)} == "
        f"{h_fl8.get(0, 0) + h_fl8.get(8, 0)}; invariant midpoint H(4) = {h_fl8[4]}"
    )

    print("\nPillar 3 — Dimension-64 Euclidean Coordinate Right-Multiplier Rupture vs. rho(2^n):")
    for n in range(3, 9):
        omega = len(cd_max_clique(n))
        rho = hurwitz_radon(n)
        status = "SATURATED" if omega == rho else f"RUPTURE (gap = {rho - omega})"
        print(f"  n={n} (dim {1 << n:3d}): omega(G_n^comp) = {omega:2d}, rho(2^n) = {rho:2d}  [{status}]")

    print("\nPillar 4 — Certified High-Dimensional Coordinate Composition Witnesses:")
    print(f"  Pathion [14, 14, 32] valid: {is_norm_mult_pair(5, PATHION_WITNESS_14, PATHION_WITNESS_14)}")
    print(f"  Chingon [16, 16, 64] valid: {is_norm_mult_pair(6, CHINGON_WITNESS_16, CHINGON_WITNESS_16)}")
    print(
        f"  Asymmetric [32, 20, 64] valid: "
        f"{is_norm_mult_pair(6, list(range(32)), doubled_right_witness(6))}"
    )

    print("\nPillar 5 — Gray-Code Bit-Locking & Exponential Spectral Band Gap (T5a-T5c):")
    for n in (6, 7):
        gapped = [f for f in range(1 << n) if is_gapped_mask(n, f)]
        h_gap = nullity_histogram_gamma(n, (1 << n) - 8)
        lo_e, hi_e = 1 << (n - 2), 3 * (1 << (n - 3))
        empty = [v for v in range(lo_e + 4, hi_e, 4) if h_gap.get(v, 0) == 0]
        print(
            f"  CD_{n} (flip={(1 << n) - 8}): gapped masks = {len(gapped)} (formula {(1 << (n - 3)) - 4}), "
            f"band gap = {empty} between H({lo_e})={h_gap[lo_e]} and H({hi_e})={h_gap[hi_e]}"
        )

    print("\nPillar 6 — Odd-Parity Zero-Divisor Exclusion & Sharp 4-Blade Witness (T6a-T6c):")
    x3 = [1 if t in (1, 2, 10) else 0 for t in range(16)]
    _, delta = odd_pivot_integral_inv(left_mul_matrix_gamma(4, 0, x3))
    print(f"  Unit 3-blade e_1 + e_2 + e_10 in CD_4(0): odd-pivot integral inverse delta mod 2 = {delta % 2} (invertible!)")
    x4 = [0] * 16
    x4[1], x4[2], x4[9], x4[10] = 1, 1, 1, -1
    y4 = [1 if t in (4, 15) else 0 for t in range(16)]
    print(
        f"  Even 4-blade (e_1 + e_2 + e_9 - e_10)*(e_4 + e_15) == 0: "
        f"{all(v == 0 for v in cd_mul_gamma_vec(4, 0, x4, y4))} (sum = {sum(x4)}, even!)"
    )


if __name__ == "__main__":
    main()
