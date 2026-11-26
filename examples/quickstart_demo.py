# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Quickstart demonstration of the 4 pillars of Cayley-Dickson Terrace Frontier."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from cd_terrace import (
    CHINGON_WITNESS_16,
    PATHION_WITNESS_14,
    cd_max_clique,
    doubled_right_witness,
    hurwitz_radon,
    is_norm_mult_pair,
    non_zd_formula,
    nullity_histogram,
    nullity_histogram_gamma,
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

    print("\nPillar 3 — Dimension-64 Hurwitz-Radon Bott Rupture:")
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


if __name__ == "__main__":
    main()
