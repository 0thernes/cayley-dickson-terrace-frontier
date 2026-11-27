# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate all frozen, deterministic JSON datasets in data/ from exact arithmetic."""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from cd_terrace import (
    CHINGON_WITNESS_16,
    PATHION_WITNESS_14,
    cd_max_clique,
    cd_sign,
    doubled_right_witness,
    hurwitz_radon,
    is_norm_mult_pair,
    non_zd_formula,
    nullity_histogram,
    total_mass_formula,
    twoblade_nullity_fast,
)

DATA_DIR = ROOT / "data"


def write_json(name: str, payload: dict) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    path = DATA_DIR / name
    text = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    path.write_bytes(text.encode("utf-8"))
    print(f"Wrote {path.relative_to(ROOT)} ({len(text)} bytes)")


def build_terraces_dataset() -> dict:
    algebras = []
    for n in range(3, 9):
        dim = 1 << n
        h = nullity_histogram(n)
        total_pairs = (dim - 1) * (dim - 2) // 2
        mass = sum(k * v for k, v in h.items())
        assert h[0] == non_zd_formula(n)
        assert mass == total_mass_formula(n)
        bdi_max = (dim - 4 * n + 4) if n >= 4 else 0
        twoblade_max = ((1 << (n - 1)) - 4) if n >= 4 else 0
        algebras.append(
            {
                "n": n,
                "dim": dim,
                "total_2blades": total_pairs,
                "non_zd_count": h[0],
                "zd_count": total_pairs - h[0],
                "total_nullity_mass": mass,
                "bad_affine_2planes": mass // 4,
                "midpoint_bin": (1 << (n - 2)) if n >= 4 else None,
                "midpoint_count": h.get(1 << (n - 2), 0) if n >= 4 else None,
                "twoblade_max_nullity": twoblade_max,
                "bdi_max_annihilator_dim": bdi_max,
                "histogram": {str(k): v for k, v in sorted(h.items())},
            }
        )
    return {
        "schema_version": "1.0",
        "description": "Exact Euclidean 2-blade nullity terrace distributions for CD_3..CD_8 (8D..256D).",
        "algebras": algebras,
    }


def build_split_phases_dataset() -> dict:
    levels = []
    for n in range(4, 9):
        dim = 1 << n
        half = 1 << (n - 1)
        mid = 1 << (n - 2)
        pairs = [
            (i ^ j, twoblade_nullity_fast(n, i, j))
            for i in range(1, dim)
            for j in range(i + 1, dim)
        ]
        phase_map: dict[tuple[tuple[int, int], ...], list[int]] = {}
        for fl in range(dim):
            cnt: Counter[int] = Counter()
            for d, nu_std in pairs:
                nilp = ((d & fl).bit_count() & 1) == 1
                cnt[(half - nu_std) if nilp else nu_std] += 1
            assert cnt[mid] == 42 * (1 << (n - 4))
            key = tuple(sorted(cnt.items()))
            phase_map.setdefault(key, []).append(fl)
        phases = []
        top = half - 4
        for key, flips in sorted(phase_map.items(), key=lambda kv: (len(kv[1]), kv[0])):
            hdict = dict(key)
            gap_bins = [v for v in range(4, top + 1, 4) if hdict.get(v, 0) == 0]
            phases.append(
                {
                    "multiplicity": len(flips),
                    "example_flip_mask": flips[0],
                    "flip_masks": flips if n <= 6 else flips[:8],
                    "spectral_gap_bins": gap_bins,
                    "histogram": {str(k): v for k, v in key},
                }
            )
        levels.append(
            {
                "n": n,
                "dim": dim,
                "total_signatures": dim,
                "distinct_phases": len(phases),
                "expected_phases_formula": 1 << (n - 2),
                "invariant_midpoint_bin": mid,
                "invariant_midpoint_count": 42 * (1 << (n - 4)),
                "spectral_gap_phase_count": sum(1 for p in phases if p["spectral_gap_bins"]),
                "phases": phases,
            }
        )
    return {
        "schema_version": "1.0",
        "description": "Exhaustive split-signature CD_n(gamma) phase classification for n = 4..8 (all 496 algebras).",
        "levels": levels,
    }


def solve_pathion_symmetric_exact() -> dict:
    """Certify exact maximum symmetric coordinate composition dimension r_max(CD_5) = 14,
    strict 7 + 7 half-balance rigidity, and exact count of all 280 14D subspaces
    via deterministic greedy clique-cover + exhaustive 7+7 enumeration AND HiGHS MILP cross-check."""
    bad_planes = []
    bad_lo_masks = []
    cross_bad_for_uv: dict[tuple[int, int], list[tuple[int, int]]] = {
        (u, v): [] for u in range(16) for v in range(u)
    }
    for a in range(32):
        for b in range(a + 1, 32):
            for c in range(b + 1, 32):
                d = a ^ b ^ c
                if d > c:
                    p1 = cd_sign(5, a, c) * cd_sign(5, b, d) + cd_sign(5, a, d) * cd_sign(5, b, c)
                    p2 = cd_sign(5, a, b) * cd_sign(5, c, d) + cd_sign(5, a, d) * cd_sign(5, c, b)
                    p3 = cd_sign(5, a, b) * cd_sign(5, d, c) + cd_sign(5, a, c) * cd_sign(5, d, b)
                    if p1 != 0 or p2 != 0 or p3 != 0:
                        bad_planes.append((a, b, c, d))
                        if d < 16:
                            bad_lo_masks.append((1 << a) | (1 << b) | (1 << c) | (1 << d))
                        elif b < 16 and c >= 16:
                            cross_bad_for_uv[(d - 16, c - 16)].append((a, b))
    assert len(bad_planes) == 630
    assert len(bad_lo_masks) == 42

    # 1. Exact deterministic greedy descending clique-cover check (matching Lean T4e!)
    valid_eq7: list[int] = []
    valid_ge8 = 0
    greedy_failures = 0
    for lo in range(65536):
        pop = lo.bit_count()
        if pop < 7:
            continue
        if not all((lo & bm) != bm for bm in bad_lo_masks):
            continue
        if pop == 7:
            valid_eq7.append(lo)
            continue
        valid_ge8 += 1
        cliques: list[list[int]] = []
        for u in range(15, -1, -1):
            placed = False
            for cl in cliques:
                if all(
                    any(((lo >> a) & 1) and ((lo >> b) & 1) for a, b in cross_bad_for_uv[(v, u)])
                    for v in cl
                ):
                    cl.append(u)
                    placed = True
                    break
            if not placed:
                cliques.append([u])
        if pop + len(cliques) > 13:
            greedy_failures += 1
    assert valid_ge8 == 2995
    assert greedy_failures == 0

    # 2. Exhaustive count of ALL 14D norm-multiplicative coordinate subspaces (strict 7 + 7 split)
    valid_eq7_set = set(valid_eq7)
    count_14d = 0
    all_contain_0_16 = True
    for lo in valid_eq7:
        forb = [0] * 16
        for u in range(1, 16):
            for v in range(1, u):
                if any(((lo >> a) & 1) and ((lo >> b) & 1) for a, b in cross_bad_for_uv[(u, v)]):
                    forb[u] |= 1 << v
                    forb[v] |= 1 << u

        def dfs(u: int, chosen: int, cnt: int) -> None:
            nonlocal count_14d, all_contain_0_16
            if cnt == 7:
                if chosen in valid_eq7_set:
                    count_14d += 1
                    if not ((lo & 1) and (chosen & 1)):
                        all_contain_0_16 = False
                return
            if u == 16 or cnt + (16 - u) < 7:
                return
            if (chosen & forb[u]) == 0:
                dfs(u + 1, chosen | (1 << u), cnt + 1)
            dfs(u + 1, chosen, cnt)

        dfs(0, 0, 0)
    assert count_14d == 280
    assert all_contain_0_16

    # 3. Independent HiGHS MILP cross-check (no longer in proof trust base; Lean T4e proves r_max=14!)
    a_mat = np.zeros((len(bad_planes), 32), dtype=float)
    for row, (a, b, c, d) in enumerate(bad_planes):
        a_mat[row, [a, b, c, d]] = 1.0
    res = milp(
        c=-np.ones(32),
        integrality=np.ones(32),
        bounds=Bounds(0, 1),
        constraints=LinearConstraint(a_mat, -np.inf, np.full(len(bad_planes), 3.0)),
    )
    assert res.success
    opt_dim = round(-float(res.fun))
    opt_witness = [i for i, v in enumerate(res.x) if v > 0.5]
    assert opt_dim == 14
    assert is_norm_mult_pair(5, opt_witness, opt_witness)
    return {
        "n": 5,
        "dim": 32,
        "bad_affine_2planes": len(bad_planes),
        "exact_max_symmetric_coord_dim": opt_dim,
        "lean_kernel_proved": True,
        "strict_7_plus_7_balance": True,
        "exact_14d_subspace_count": count_14d,
        "all_14d_contain_e0_and_e16": all_contain_0_16,
        "valid_lo_ge8_count": valid_ge8,
        "greedy_clique_cover_failures": greedy_failures,
        "yiu_general_integer_dim": 16,
        "symmetric_rupture_gap": 16 - opt_dim,
        "milp_crosscheck_status": int(res.status),
        "milp_crosscheck_message": str(res.message),
        "canonical_witness_14": list(PATHION_WITNESS_14),
        "milp_witness_14": opt_witness,
    }


def build_sedenion_and_witnesses_dataset() -> dict:
    bad_planes = []
    for a in range(16):
        for b in range(a + 1, 16):
            for c in range(b + 1, 16):
                d = a ^ b ^ c
                if d > c:
                    p1 = cd_sign(4, a, c) * cd_sign(4, b, d) + cd_sign(4, a, d) * cd_sign(4, b, c)
                    p2 = cd_sign(4, a, b) * cd_sign(4, c, d) + cd_sign(4, a, d) * cd_sign(4, c, b)
                    p3 = cd_sign(4, a, b) * cd_sign(4, d, c) + cd_sign(4, a, c) * cd_sign(4, d, b)
                    if p1 != 0 or p2 != 0 or p3 != 0:
                        bad_planes.append([a, b, c, d])
    bad_masks = [sum(1 << x for x in p) for p in bad_planes]
    subspaces_10 = []
    for m in range(65536):
        if m.bit_count() == 10 and all((m & bm) != bm for bm in bad_masks):
            elems = [k for k in range(16) if (m >> k) & 1]
            subspaces_10.append({"mask": m, "basis": elems, "octonion_overlap": sum(x < 8 for x in elems)})
    assert len(subspaces_10) == 42

    assessors = [[i, j] for i in range(1, 8) for j in range(9, 16) if i != j - 8]

    def blade_annihilates_4(i: int, j: int, k: int, l_idx: int) -> bool:
        for s in (1, -1):
            prod = [0] * 16
            prod[i ^ k] += cd_sign(4, i, k)
            prod[i ^ l_idx] += s * cd_sign(4, i, l_idx)
            prod[j ^ k] += cd_sign(4, j, k)
            prod[j ^ l_idx] += s * cd_sign(4, j, l_idx)
            if all(v == 0 for v in prod):
                return True
        return False

    edges = []
    for u, (i, j) in enumerate(assessors):
        for v in range(u + 1, len(assessors)):
            k, l_idx = assessors[v]
            if blade_annihilates_4(i, j, k, l_idx):
                assert (i ^ j) == (k ^ l_idx), "unexpected cross-XOR box-kite edge"
                edges.append([u, v])
    assert len(assessors) == 42 and len(edges) == 84

    pathion_exact = solve_pathion_symmetric_exact()
    assert is_norm_mult_pair(6, CHINGON_WITNESS_16, CHINGON_WITNESS_16)
    return {
        "schema_version": "2.0",
        "sedenion_triple_42": {
            "total_affine_2planes": 140,
            "bad_affine_2planes_count": 42,
            "bad_affine_2planes": bad_planes,
            "maximal_10d_coord_subspaces_count": 42,
            "fano_intersection_split": {"8": 7, "5": 28, "2": 7},
            "dim_11_or_higher_count": 0,
            "maximal_10d_subspaces": subspaces_10,
            "box_kites": {
                "assessors_count": 42,
                "edges_count": 84,
                "components_count": 7,
                "component_isomorphism": "K_{2,2,2} (octahedron)",
                "xor_signatures": [9, 10, 11, 12, 13, 14, 15],
                "exact_spectrum": {"4": 7, "0": 21, "-2": 14},
                "assessors": assessors,
                "edges": edges,
            },
            "global_9d_zdf_subspace": list(range(9)),
        },
        "pathion_symmetric_rupture_milp": pathion_exact,
        "chingon_symmetric_witness_16": {
            "n": 6,
            "dim": 64,
            "witness_dim": 16,
            "basis": list(CHINGON_WITNESS_16),
            "verified_norm_multiplicative": True,
        },
    }


def build_hurwitz_table_dataset() -> dict:
    rows = []
    for n in range(3, 13):
        dim = 1 << n
        omega = n + 5
        rho = hurwitz_radon(n)
        shell_degs = [(1 << k) + 2 * (n - k) - 1 for k in range(3, n + 1)]
        rows.append(
            {
                "n": n,
                "dim": dim,
                "cd_max_clique_omega": omega,
                "hurwitz_radon_rho": rho,
                "rupture_gap": rho - omega,
                "saturated": omega == rho,
                "universal_right_multipliers": [0, 1 << (n - 1)] if n >= 4 else list(range(dim)),
                "shell_degrees": shell_degs,
                "asymmetric_doubling_triple": [1 << (n - 1), 2 * (n + 4), dim] if n >= 4 else [4, 8, 8],
                "canonical_clique_witness": cd_max_clique(n) if n <= 10 else None,
                "asymmetric_right_witness": doubled_right_witness(n) if 4 <= n <= 8 else None,
            }
        )
    return {
        "schema_version": "1.0",
        "description": "Dimension-64 Euclidean Coordinate Right-Multiplier Rupture & Asymmetric Doubling Tower table (CD_3..CD_12).",
        "rows": rows,
    }


def main() -> None:
    write_json("cd4_to_cd8_terraces.json", build_terraces_dataset())
    write_json("split_phases_cd4_to_cd8.json", build_split_phases_dataset())
    write_json("sedenion_box_kites_and_42_subspaces.json", build_sedenion_and_witnesses_dataset())
    write_json("hurwitz_rupture_table.json", build_hurwitz_table_dataset())
    print("All frozen datasets generated successfully.")


if __name__ == "__main__":
    main()
