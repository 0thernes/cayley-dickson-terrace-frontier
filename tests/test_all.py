# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Comprehensive falsifiable, property-based, metamorphic, negative, surgical-mutation,
schema, Lean-symbol bijection, governance/accessibility/CSP, timestamp, and cross-language
differential verification suite for Cayley-Dickson Terrace Frontier v2.1.0.
"""

from __future__ import annotations

import json
import re
import struct
import subprocess
import sys
from pathlib import Path

import jsonschema
import pytest
import yaml  # type: ignore[import-untyped]
from hypothesis import given, settings
from hypothesis import strategies as st

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT))

from cd_terrace import (
    CHINGON_WITNESS_16,
    PATHION_WITNESS_14,
    block_delta,
    cd_max_clique,
    cd_sign,
    cd_sign_gamma_direct,
    cd_sign_gamma_factored,
    doubled_right_witness,
    hurwitz_radon,
    is_norm_mult_pair,
    non_zd_formula,
    nullity_histogram,
    nullity_histogram_gamma,
    right_compat,
    total_mass_formula,
    twoblade_nullity_direct,
    twoblade_nullity_fast,
    twoblade_nullity_gamma,
)
from reference.oracle import (
    cd_mul_vec,
    flip_to_gammas,
    naive_twoblade_nullity,
    norm_sq_vec,
)


def test_pillar1_naive_oracle_vs_cocycle_and_mirror_law() -> None:
    """First-principles check: naive recursive vector multiplication + Q Gaussian elimination
    must match Pillar 1 sign-cocycle factorization, T1f kernel basis rank, and Nilpotent Mirror Law."""
    test_pairs = [(1, 2), (1, 9), (1, 10), (2, 12), (3, 14), (4, 11), (7, 15)]
    for fl in range(16):
        gammas = flip_to_gammas(4, fl)
        for i in (0, 1, 5, 8, 13):
            ei = [1 if k == i else 0 for k in range(16)]
            for j in (0, 2, 7, 9, 14):
                ej = [1 if k == j else 0 for k in range(16)]
                prod = cd_mul_vec(ei, ej, gammas)
                assert prod[i ^ j] == cd_sign_gamma_direct(4, fl, i, j)
                assert prod[i ^ j] == cd_sign_gamma_factored(4, fl, i, j)
                assert sum(abs(v) for v in prod) == 1
        for i, j in test_pairs:
            nu_q = naive_twoblade_nullity(4, fl, i, j)
            nu_mirror = twoblade_nullity_gamma(4, fl, i, j)
            assert nu_q == nu_mirror


def test_t1f_explicit_z_basis_annihilates_and_spans_kernel() -> None:
    """First-principles check of Theorem T1f across all 16 sedenion signatures:
    explicit 2-sparse Z-basis vectors w_k = e_k - sigma^gamma(i,k)*sigma^gamma(j,k')*e_{k'}
    are pairwise disjoint on their lower representative k, lie strictly in ker L_{e_i + e_j}
    under full recursive cd_mul_vec, and have exact cardinality equal to both twoblade_nullity_gamma
    and exact Q Gaussian elimination rank."""
    test_pairs = [(1, 9), (1, 10), (2, 12), (3, 14), (5, 13), (7, 15)]
    for fl in range(16):
        gammas = flip_to_gammas(4, fl)
        for i, j in test_pairs:
            d = i ^ j
            blade = [1 if t in (i, j) else 0 for t in range(16)]
            reps: list[int] = []
            basis_vecs: list[list[int]] = []
            for k in range(16):
                kp = k ^ d
                if k < kp:
                    delta = (
                        cd_sign_gamma_direct(4, fl, i, k)
                        * cd_sign_gamma_direct(4, fl, i, kp)
                        * cd_sign_gamma_direct(4, fl, j, k)
                        * cd_sign_gamma_direct(4, fl, j, kp)
                    )
                    if delta == 1:
                        reps.append(k)
                        w = [0] * 16
                        w[k] = 1
                        w[kp] = -(cd_sign_gamma_direct(4, fl, i, k) * cd_sign_gamma_direct(4, fl, j, kp))
                        basis_vecs.append(w)
            assert len(reps) == twoblade_nullity_gamma(4, fl, i, j)
            assert len(reps) == naive_twoblade_nullity(4, fl, i, j)
            # Every w_k must annihilate (e_i + e_j) on the right across all 16 coordinates
            for idx, w in enumerate(basis_vecs):
                assert cd_mul_vec(blade, w, gammas) == [0] * 16
                # Disjoint lower-rep unit diagonal guarantees Z-linear independence
                for other_idx, k_other in enumerate(reps):
                    assert w[k_other] == (1 if idx == other_idx else 0)


def test_pillar1_mirror_conservation_and_split_phases_cd4_to_cd6() -> None:
    """Verify exact mirror-pair conservation, invariant midpoint 42*2^(n-4), 2^(n-2) phase counts,
    and T4f dimension-64 split-signature interior spectral gap at flipMask=56."""
    expected_classes = {4: 4, 5: 8, 6: 16}
    for n, exp_cls in expected_classes.items():
        std_h = nullity_histogram(n)
        half = 1 << (n - 1)
        mid = 1 << (n - 2)
        seen = set()
        for fl in range(1 << n):
            h = nullity_histogram_gamma(n, fl)
            assert h[mid] == 42 * (1 << (n - 4))
            for v in range(0, half + 1, 4):
                assert h.get(v, 0) + h.get(half - v, 0) == std_h.get(v, 0) + std_h.get(half - v, 0)
            seen.add(tuple(sorted(h.items())))
        assert len(seen) == exp_cls

    # T4f exact 9-bin histogram at CD_6(flipMask = 56)
    h6_56 = nullity_histogram_gamma(6, 56)
    assert h6_56 == {0: 257, 4: 422, 8: 364, 12: 336, 16: 168, 24: 56, 28: 172, 32: 178}
    assert h6_56.get(20, 0) == 0


def test_pillar2_terrace_law_and_bdi_separation() -> None:
    """Verify total nullity mass, non-ZD count, interleaving, palindrome, top jump, and BDI gap."""
    for n in range(3, 8):
        h = nullity_histogram(n)
        assert h[0] == non_zd_formula(n)
        assert sum(k * v for k, v in h.items()) == total_mass_formula(n)
        if n >= 4:
            top = (1 << (n - 1)) - 4
            assert h[top] == 2 * non_zd_formula(n - 1)
            assert h[1 << (n - 2)] == 42 * (1 << (n - 4))
            # Constructive ceiling attainment witness e_1 + e_{2 + 2^(n-1)} (T2b)
            assert twoblade_nullity_fast(n, 1, 2 + (1 << (n - 1))) == top
            for k in range(1, top // 4):
                assert h.get(4 * k, 0) == h.get(top - 4 * k, 0)
            if n >= 5:
                assert h[top] - h[4] == 3 * ((1 << (n - 1)) - 2)
            bdi = (1 << n) - 4 * n + 4
            if n == 4:
                assert top == bdi
            else:
                assert top < bdi


def test_pillar3_hurwitz_rupture_and_asymmetric_tower() -> None:
    """Verify G_n^comp unification, universal multipliers, dim-64 rupture, and asymmetric tower."""
    for n in range(3, 7):
        dim = 1 << n
        cliq = cd_max_clique(n)
        assert len(cliq) == n + 5
        assert is_norm_mult_pair(n, list(range(dim)), cliq)
        if n <= 5:
            assert len(cliq) == hurwitz_radon(n)
        else:
            assert len(cliq) < hurwitz_radon(n)
        if n >= 4:
            univ = [j for j in range(dim) if all(right_compat(n, j, x) for x in range(dim) if x != j)]
            assert univ == [0, 1 << (n - 1)]
            drw = doubled_right_witness(n)
            assert len(drw) == 2 * (n + 4)
            assert is_norm_mult_pair(n, list(range(dim // 2)), drw)


def test_pillar4_witnesses_exact_vector_norm_multiplicativity() -> None:
    """First-principles check: naive recursive vector multiplication preserves ||xy||^2 == ||x||^2||y||^2
    on the [14, 14, 32] Pathion (strict 7+7) and [16, 16, 64] Chingon witnesses, while failing on 11D sedenions."""
    assert sum(x < 16 for x in PATHION_WITNESS_14) == 7
    assert sum(x >= 16 for x in PATHION_WITNESS_14) == 7
    for n, witness in [(5, PATHION_WITNESS_14), (6, CHINGON_WITNESS_16)]:
        assert is_norm_mult_pair(n, witness, witness)
        dim = 1 << n
        gammas = flip_to_gammas(n, 0)
        x = [0] * dim
        y = [0] * dim
        for idx, b in enumerate(witness):
            x[b] = 3 * idx - 11
            y[b] = 7 * idx - 19
        z = cd_mul_vec(x, y, gammas)
        assert norm_sq_vec(z) == norm_sq_vec(x) * norm_sq_vec(y)

    # Negative: 11D sedenion {0..10} MUST violate ||xy||^2 == ||x||^2 ||y||^2 on an explicit vector pair
    assert not is_norm_mult_pair(4, list(range(11)), list(range(11)))
    x_bad = [1 if k in (4, 9) else 0 for k in range(16)]
    y_bad = [1 if k in (7, 10) else 0 for k in range(16)]
    z_bad = cd_mul_vec(x_bad, y_bad, flip_to_gammas(4, 0))
    assert norm_sq_vec(z_bad) != norm_sq_vec(x_bad) * norm_sq_vec(y_bad)

    # Negative: adding ANY 15th coordinate to PATHION_WITNESS_14 MUST break norm-multiplicativity (T4e)
    for extra in range(32):
        if extra not in PATHION_WITNESS_14:
            cand = list(PATHION_WITNESS_14) + [extra]
            assert not is_norm_mult_pair(5, cand, cand)


def test_negative_boundaries_and_error_handling() -> None:
    """Verify sharp negative boundaries and clean invalid-input rejections (including upper bounds >= 2^n)."""
    assert not right_compat(4, 1, 10)
    assert not right_compat(4, 5, 5)
    assert not right_compat(4, -1, 2)
    assert not is_norm_mult_pair(4, [0, 1, 1], [0, 1])
    assert not is_norm_mult_pair(4, [0, 16], [0, 1])
    with pytest.raises(ValueError):
        cd_sign(-1, 0, 0)
    with pytest.raises(ValueError):
        cd_sign(4, 16, 0)
    with pytest.raises(ValueError):
        cd_sign(4, 0, 16)
    with pytest.raises(ValueError):
        cd_sign_gamma_direct(4, 0, 16, 1)
    with pytest.raises(ValueError):
        cd_sign_gamma_factored(4, 0, 1, 16)
    with pytest.raises(ValueError):
        block_delta(4, 1, 2, 16)
    with pytest.raises(ValueError):
        twoblade_nullity_direct(4, 1, 16)
    with pytest.raises(ValueError):
        twoblade_nullity_fast(4, 1, 16)
    with pytest.raises(ValueError):
        twoblade_nullity_gamma(4, 0, 16, 1)
    with pytest.raises(ValueError):
        non_zd_formula(2)
    with pytest.raises(ValueError):
        total_mass_formula(2)
    with pytest.raises(ValueError):
        cd_max_clique(2)
    with pytest.raises(ValueError):
        doubled_right_witness(3)


@settings(max_examples=200, deadline=None)
@given(
    n=st.integers(min_value=1, max_value=6),
    seed_flip=st.integers(min_value=0, max_value=63),
    seed_i=st.integers(min_value=0, max_value=63),
    seed_j=st.integers(min_value=0, max_value=63),
)
def test_hypothesis_cocycle_and_doubling_properties(
    n: int, seed_flip: int, seed_i: int, seed_j: int
) -> None:
    """Property-based & metamorphic test of Pillar 1 cocycle factorization, doubling recurrence, and symmetry."""
    mask = (1 << n) - 1
    fl = seed_flip & mask
    i = seed_i & mask
    j = seed_j & mask
    assert cd_sign_gamma_direct(n, fl, i, j) == cd_sign_gamma_factored(n, fl, i, j)
    if i > 0 and j > 0 and i != j:
        assert cd_sign(n, i, j) == -cd_sign(n, j, i)
        assert cd_sign_gamma_factored(n, fl, i, j) == -cd_sign_gamma_factored(n, fl, j, i)
        nu_f = twoblade_nullity_fast(n, i, j)
        assert nu_f == twoblade_nullity_direct(n, i, j)
        assert nu_f == twoblade_nullity_fast(n, j, i)
        assert (nu_f == 0) == right_compat(n, i, j)
        assert twoblade_nullity_fast(n + 1, i, j) == 2 * nu_f
        h = 1 << n
        assert twoblade_nullity_fast(n + 1, i + h, j + h) == 2 * nu_f


def test_frozen_data_schemas_and_consistency() -> None:
    """Verify all frozen JSON files in data/ exist, parse cleanly, and match live computations."""
    data_dir = ROOT / "data"
    terraces = json.loads((data_dir / "cd4_to_cd8_terraces.json").read_text(encoding="utf-8"))
    splits = json.loads((data_dir / "split_phases_cd4_to_cd8.json").read_text(encoding="utf-8"))
    sed = json.loads((data_dir / "sedenion_box_kites_and_42_subspaces.json").read_text(encoding="utf-8"))
    hurw = json.loads((data_dir / "hurwitz_rupture_table.json").read_text(encoding="utf-8"))

    assert len(terraces["algebras"]) == 6
    for entry in terraces["algebras"]:
        n = entry["n"]
        assert entry["non_zd_count"] == non_zd_formula(n)
        assert entry["total_nullity_mass"] == total_mass_formula(n)
    assert [lvl["distinct_phases"] for lvl in splits["levels"]] == [4, 8, 16, 32, 64]
    assert [lvl["invariant_midpoint_count"] for lvl in splits["levels"]] == [42, 84, 168, 336, 672]
    assert sed["sedenion_triple_42"]["bad_affine_2planes_count"] == 42
    assert sed["sedenion_triple_42"]["maximal_10d_coord_subspaces_count"] == 42
    assert sed["sedenion_triple_42"]["dim_11_or_higher_count"] == 0
    assert sed["sedenion_triple_42"]["fano_intersection_split"] == {"8": 7, "5": 28, "2": 7}
    p5 = sed["pathion_symmetric_rupture_milp"]
    assert p5["exact_max_symmetric_coord_dim"] == 14
    assert p5["lean_kernel_proved"] is True
    assert p5["strict_7_plus_7_balance"] is True
    assert p5["exact_14d_subspace_count"] == 280
    assert p5["greedy_clique_cover_failures"] == 0
    assert hurw["rows"][3]["n"] == 6 and hurw["rows"][3]["rupture_gap"] == 1


def test_cross_language_rust_differential() -> None:
    """Run the compiled Rust release binary in --json mode and verify 100% agreement with Python."""
    exe_name = "cd-terrace.exe" if sys.platform == "win32" else "cd-terrace"
    rust_bin = ROOT / "rust" / "target" / "release" / exe_name
    assert rust_bin.exists(), f"Missing Rust release binary at {rust_bin}; run cargo build --release"
    proc = subprocess.run([str(rust_bin), "--json"], capture_output=True, text=True, check=True)
    rust_out = json.loads(proc.stdout)
    assert rust_out["status"] == "PASS"
    assert rust_out["sedenion_bad_planes"] == 42
    assert rust_out["sedenion_10d_count"] == 42
    assert rust_out["sedenion_11d_count"] == 0
    assert rust_out["sedenion_fano_split"] == [7, 28, 7]
    assert rust_out["sedenion_box_kites_ok"] is True
    assert rust_out["pathion_14_ok"] is True
    assert rust_out["pathion_exact_max_dim"] == 14
    assert rust_out["pathion_14d_count"] == 280
    assert rust_out["pathion_greedy_ge8_failures"] == 0
    assert rust_out["pathion_all_14d_balanced_7_7"] is True
    assert rust_out["pathion_all_14d_contain_0_16"] is True
    assert rust_out["cd6_flip56_gap_bin20"] == 0
    assert rust_out["chingon_16_ok"] is True
    for n in range(3, 8):
        py_h = {str(k): v for k, v in nullity_histogram(n).items()}
        assert rust_out["euclidean_histograms"][f"CD_{n}"] == py_h


def test_surgical_mutation_suite_kills_8_mutants() -> None:
    """Surgical mutation test (B13): verify 8 distinct algebraic/boundary mutants are each killed."""
    # Mutant 1: omit nilpotent mirror inversion in split sedenions (flip_mask = 8)
    true_h = nullity_histogram_gamma(4, 8)
    mutant_no_mirror = nullity_histogram(4)
    assert mutant_no_mirror.get(0, 0) != true_h.get(0, 0)
    assert mutant_no_mirror.get(8, 0) != true_h.get(8, 0)

    # Mutant 2: off-by-one BDI ceiling at n = 5 (falsely claiming 2-blades saturate BDI at n = 5)
    max_nu_5 = max(nullity_histogram(5).keys())
    bdi_5 = (1 << 5) - 4 * 5 + 4
    assert max_nu_5 == 12 and bdi_5 == 16 and max_nu_5 < bdi_5

    # Mutant 3: flip a single sedenion sign entry (e_1 * e_2) -> breaks octonion alternativity
    bad_sign = -cd_sign(4, 1, 2)
    assert bad_sign * cd_sign(4, 1, 1 ^ 2) != -1

    # Mutant 4: drop the -4 offset in cross-half doubling recurrence -> violates nu_4(1, 10) == 4
    wrong_cross_4 = (1 << 3) - 2 * twoblade_nullity_fast(3, 1, 2)
    assert wrong_cross_4 != twoblade_nullity_fast(4, 1, 10)

    # Mutant 5: replace (i & j & flip) with (i | j & flip) in Pillar 1 cocycle -> disagrees with direct sign
    fl_m, i_m, j_m = 8, 1, 8
    wrong_parity = (((i_m | j_m) & fl_m).bit_count() & 1) == 1
    wrong_sign = -cd_sign(4, i_m, j_m) if wrong_parity else cd_sign(4, i_m, j_m)
    assert wrong_sign != cd_sign_gamma_direct(4, fl_m, i_m, j_m)

    # Mutant 6: wrong Hurwitz-Radon period (4 instead of 8) -> disagrees at n = 6 (dim 64)
    wrong_hr6 = 4 * (6 // 4) + (1 << (6 % 4))
    assert wrong_hr6 != hurwitz_radon(6)

    # Mutant 7: claim CD_6(flip=56) has no interior spectral gap -> killed by bin 20 == 0
    assert nullity_histogram_gamma(6, 56).get(20, 0) == 0

    # Mutant 8: swap one upper element of PATHION_WITNESS_14 into lower half (8 + 6 unbalanced 14D)
    unbalanced_14 = [0, 1, 2, 3, 4, 5, 8, 10, 16, 17, 18, 20, 21, 24]
    assert len(unbalanced_14) == 14 and sum(x < 16 for x in unbalanced_14) == 8
    assert not is_norm_mult_pair(5, unbalanced_14, unbalanced_14)


def test_repo_yaml_validates_against_schema_and_social_preview_png() -> None:
    """Enforce strict JSON Schema validation of repo.yaml against repo-standard.schema.json
    and Build Standard A26 1280x640 PNG social preview."""
    schema = json.loads((ROOT / "repo-standard.schema.json").read_text(encoding="utf-8"))
    manifest = yaml.safe_load((ROOT / "repo.yaml").read_text(encoding="utf-8"))
    jsonschema.validate(instance=manifest, schema=schema)

    png_path = ROOT / "docs" / "media" / "social-preview.png"
    assert png_path.exists(), "Missing docs/media/social-preview.png (Build Standard A26)"
    raw = png_path.read_bytes()
    assert raw[:8] == b"\x89PNG\r\n\x1a\n"
    w, h = struct.unpack(">II", raw[16:24])
    assert (w, h) == (1280, 640), f"social-preview.png must be 1280x640, got {w}x{h}"
    assert len(raw) < 1024 * 1024, f"social-preview.png must be < 1 MiB, got {len(raw)} bytes"


def test_documentation_bijections_lean_symbols_and_no_stale_prose() -> None:
    """Anti-drift regression guard locking:
    1. Every Lean identifier referenced in docs/statement-fidelity.md and paper/main.tex exists in lean/**/*.lean.
    2. 100% 30-key bijection across paper/references.bib, paper/main.tex, and docs/literature-search-log.md.
    3. 100% 23-target bijection (T1a..T4f + ALL) across Challenge.lean, comparator.json, formalization.yaml,
       docs/statement-fidelity.md, and docs/site/blueprint.html.
    4. Canonical title consistency and absence of previously caught stale formulas or Bott-Rupture labels.
    """
    # 1. Extract all declared Lean identifiers (including @[expose] / @[inline] attributed defs)
    lean_decls: set[str] = set()
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?:theorem|lemma|def|abbrev|inductive|structure|class|axiom)\s+([A-Za-z_][A-Za-z0-9_']*)",
        re.MULTILINE,
    )
    for lean_file in (ROOT / "lean").rglob("*.lean"):
        if ".lake" in lean_file.parts:
            continue
        lean_decls.update(decl_re.findall(lean_file.read_text(encoding="utf-8")))
    lean_modules = {
        "Basic", "MirrorConservation", "TerraceLaw", "HurwitzRupture",
        "FiniteCertificates", "PathionRupture", "NonVacuity", "AdversarialTests",
    }

    # Check every CDTerrace.<sym> and known Lean identifier in docs/statement-fidelity.md
    sf_text = (ROOT / "docs" / "statement-fidelity.md").read_text(encoding="utf-8")
    for sym in re.findall(r"`CDTerrace\.([A-Za-z_][A-Za-z0-9_']*)`", sf_text):
        if sym in lean_modules:
            continue
        assert sym in lean_decls, f"Non-existent Lean symbol CDTerrace.{sym} in docs/statement-fidelity.md"
    for sym in ("leftMulTwoBladeCoord", "isBoxKiteAssessor", "hasCrossEdgeFast", "checkPathionLoChunk_0"):
        assert sym not in sf_text, f"Stale non-existent Lean symbol {sym} in docs/statement-fidelity.md"

    tex_text = (ROOT / "paper" / "main.tex").read_text(encoding="utf-8")
    for sym in ("leftMulTwoBladeCoord", "isBoxKiteAssessor", "hasCrossEdgeFast", "checkPathionLoChunk_0"):
        assert sym not in tex_text, f"Stale non-existent Lean symbol {sym} in paper/main.tex"
    # Verify every identifier-like \code{...} token in paper/main.tex that matches camelCase/snake_case Lean names
    ignore_code_tokens = {
        "ERRATA.md", "Solution.lean", "PalomarChallenge.lean", "Challenge.lean", "PalomarSolution.lean",
        "VerifyAxioms.lean", "FiniteCertificates.lean", "PathionRupture.lean", "comparator.json",
        "check_readme_axioms.py", "data/MANIFEST.sha256", "MANIFEST.sha256", "data/MANIFEST.sha256.tsr",
        "data/MANIFEST.sha256.ots", "propext", "Classical.choice", "Quot.sound", "native_decide", "rfl",
        "Nat.bitwise", "CDTerrace.Basic", "CDTerrace.MirrorConservation", "CDTerrace.TerraceLaw",
        "CDTerrace.HurwitzRupture", "CDTerrace.FiniteCertificates", "CDTerrace.NonVacuity",
        "CDTerrace.AdversarialTests", "lean/CDTerrace/*.lean", "rightCompat_doubling_*",
        "ALG-035", "ALG-039", "COMB-040", "T1f", "T4e", "T4f", "15",
    }
    for tok in re.findall(r"\\code\{([^}]+)\}", tex_text):
        if (
            tok in ignore_code_tokens
            or "/" in tok
            or "[" in tok
            or " " in tok
            or ("." in tok and tok.endswith((".lean", ".py", ".md", ".json", ".tsr", ".ots", ".sha256")))
        ):
            continue
        base = tok.split(".")[-1]
        if base in {"lower", "upper", "axis", "cross", "odd", "15"} or re.fullmatch(r"T[1-4][a-f]", base):
            continue
        assert base in lean_decls, f"paper/main.tex \\code{{{tok}}} references undeclared Lean symbol {base!r}"

    # 2. Exact 30-key BibTeX / LaTeX / docs/literature-search-log.md bijection
    bib_keys = set(re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", (ROOT / "paper" / "references.bib").read_text(encoding="utf-8")))
    tex_cites: set[str] = set()
    for m in re.findall(r"\\cite(?:\[[^\]]*\])*\{([^}]+)\}", tex_text):
        tex_cites.update(k.strip() for k in m.split(",") if k.strip())
    log_text = (ROOT / "docs" / "literature-search-log.md").read_text(encoding="utf-8")
    log_keys = set(re.findall(r"^\|\s*`([^`]+)`\s*\|", log_text, re.MULTILINE))
    assert len(bib_keys) == 30
    assert bib_keys == tex_cites, f"BibTeX vs main.tex mismatch: {bib_keys ^ tex_cites}"
    assert bib_keys == log_keys, f"BibTeX vs literature-search-log.md mismatch: {bib_keys ^ log_keys}"

    # 3. Exact 22-theorem + ALL bijection across Lean, formalization.yaml, statement-fidelity.md, blueprint.html
    expected_ids = [
        "T1a", "T1b", "T1c", "T1d", "T1e", "T1f",
        "T2a", "T2b", "T2c", "T2d", "T2e", "T2f",
        "T3a", "T3b", "T3c", "T3d",
        "T4a", "T4b", "T4c", "T4d", "T4e", "T4f",
    ]
    ch_text = (ROOT / "lean" / "Challenge.lean").read_text(encoding="utf-8")
    comp = json.loads((ROOT / "lean" / "comparator.json").read_text(encoding="utf-8"))
    fy = yaml.safe_load((ROOT / "lean" / "formalization.yaml").read_text(encoding="utf-8"))
    bp_text = (ROOT / "docs" / "site" / "blueprint.html").read_text(encoding="utf-8")

    assert len(comp["theorem_names"]) == 23
    assert [t["id"] for t in fy["theorems"]] == expected_ids
    for tid in expected_ids:
        assert f"abbrev {tid}Stmt" in ch_text, f"Missing {tid}Stmt in Challenge.lean"
        assert f"| `{tid}` |" in sf_text, f"Missing {tid} row in docs/statement-fidelity.md"
        assert f'data-id="{tid}"' in bp_text, f"Missing {tid} node in blueprint.html"
    assert "| `ALL` |" in sf_text and 'data-id="ALL"' in bp_text

    # 4. Canonical title consistency & zero stale wrong formulas / Bott-Rupture / LLC regressions
    canonical_title = (
        "The Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation, "
        "and Coordinate Norm-Multiplicativity Ruptures Across Cayley-Dickson Algebras"
    )
    cff = yaml.safe_load((ROOT / "CITATION.cff").read_text(encoding="utf-8"))
    zen = json.loads((ROOT / ".zenodo.json").read_text(encoding="utf-8"))
    sub_text = (ROOT / "docs" / "submission-packet.md").read_text(encoding="utf-8")
    assert cff["title"] == canonical_title
    assert fy["title"] == canonical_title
    assert zen["title"] == canonical_title
    assert canonical_title.replace("Cayley-Dickson", "Cayley--Dickson") in sub_text

    # Required Palomar fields in formalization.yaml
    for field in ("authorship", "origin", "sources", "automation", "limitations", "review_status"):
        assert field in fy, f"Missing Palomar field {field!r} in lean/formalization.yaml"

    # Guard against regression of previously fixed wrong formulas or Bott-Rupture / 0thernes LLC strings
    for bad_formula in ("2^{n-2}(2^{n-1}-1)(2^{n-2}-1)", "4^n + 3\\cdot 2^n - 4"):
        assert bad_formula not in sf_text
        assert bad_formula not in tex_text
    for rel in (
        "docs/site/index.html",
        "data/hurwitz_rupture_table.json",
        "scripts/generate_figures.py",
        "examples/quickstart_demo.py",
        "lean/CDTerrace/HurwitzRupture.lean",
    ):
        txt = (ROOT / rel).read_text(encoding="utf-8")
        assert "Bott" not in txt, f"Stale 'Bott' overstatement found in {rel}"
    for rel in ("README.md", "CITATION.cff", ".zenodo.json", "lean/formalization.yaml", "paper/main.tex"):
        assert "0thernes LLC" not in (ROOT / rel).read_text(encoding="utf-8")

    # Verify C11 fuzzer genuinely fuzzes CD_1..CD_7 as documented
    fuzz_c = (ROOT / "c" / "tests" / "fuzz_cd_terrace.c").read_text(encoding="utf-8")
    assert "(r % 7u)" in fuzz_c, "fuzz_cd_terrace.c must fuzz CD_1..CD_7 (% 7u)"


def test_version_governance_accessibility_and_csp() -> None:
    """Verify single version source consistency, honest repo.yaml flags, inline SPDX headers,
    WCAG 2.2 AA & CSP in web UI, and zero raw LaTeX leaks or WebGL misrepresentations."""
    ver = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    assert re.match(r"^\d+\.\d+\.\d+$", ver)
    for rel, pattern in (
        ("pyproject.toml", rf'^version\s*=\s*"{re.escape(ver)}"'),
        ("rust/Cargo.toml", rf'^version\s*=\s*"{re.escape(ver)}"'),
        ("c/include/cd_terrace.h", rf'^#define CD_TERRACE_VERSION "{re.escape(ver)}"'),
        ("lean/lakefile.toml", rf'^version\s*=\s*"{re.escape(ver)}"'),
        ("lean/formalization.yaml", rf'^version:\s*"{re.escape(ver)}"'),
        ("CITATION.cff", rf'^version:\s*"{re.escape(ver)}"'),
        (".zenodo.json", rf'"version":\s*"{re.escape(ver)}"'),
        ("CHANGELOG.md", rf"^## \[?v?{re.escape(ver)}\]?"),
    ):
        txt = (ROOT / rel).read_text(encoding="utf-8")
        assert re.search(pattern, txt, re.MULTILINE), f"Version {ver} missing/mismatched in {rel}"

    # Verify CITATION.cff ORCID
    cff = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    assert "0009-0006-8168-9648" in cff

    # Verify honest repo.yaml flags (no hiding visual/ui/deployed!)
    ry = (ROOT / "repo.yaml").read_text(encoding="utf-8")
    for flag in ("public: true", "visual: true", "ui: true", "deployed: true", "formal: true"):
        assert flag in ry, f"Expected honest flag {flag!r} in repo.yaml"

    # Verify inline SPDX headers on HTML, REUSE.toml, and Cursor rule
    for rel in ("docs/site/index.html", "docs/site/blueprint.html", "REUSE.toml", ".cursor/rules/build-standard.mdc"):
        assert "SPDX-License-Identifier:" in (ROOT / rel).read_text(encoding="utf-8"), f"Missing SPDX in {rel}"

    # Verify WCAG 2.2 AA & strict CSP in docs/site/index.html & blueprint.html
    for html_rel in ("docs/site/index.html", "docs/site/blueprint.html"):
        h = (ROOT / html_rel).read_text(encoding="utf-8")
        assert 'http-equiv="Content-Security-Policy"' in h, f"Missing CSP in {html_rel}"
        assert 'class="skip-link"' in h, f"Missing WCAG skip-link in {html_rel}"
        assert 'aria-live="polite"' in h, f"Missing aria-live region in {html_rel}"
        assert "WebGL" not in h, f"Dishonest WebGL label found in {html_rel}"
        assert "$7 \\times" not in h, f"Raw unrendered LaTeX found in {html_rel}"
    idx_h = (ROOT / "docs/site/index.html").read_text(encoding="utf-8")
    assert "prefers-reduced-motion" in idx_h
    assert "ArrowRight" in idx_h and "ArrowLeft" in idx_h
    assert 'id="bk-prev"' in idx_h and 'id="bk-next"' in idx_h
    assert 'addEventListener("resize"' in idx_h

    # Verify blueprint.html T2b node specifically states n >= 5 (not n >= 6)
    bp_h = (ROOT / "docs/site/blueprint.html").read_text(encoding="utf-8")
    t2b_match = re.search(r'<article[^>]*data-id="T2b"[^>]*>.*?</article>', bp_h, re.DOTALL)
    assert t2b_match is not None, "Missing T2b node in blueprint.html"
    assert "n ≥ 5" in t2b_match.group(0) and "n ≥ 6" not in t2b_match.group(0)


def test_cryptographic_timestamps_verify_and_reject_tamper() -> None:
    """Unconditionally verify RFC 3161 (.tsr) and 3-calendar Bitcoin OTS (.ots) proofs match
    data/MANIFEST.sha256 and reject a 1-byte tampered copy (no silent skip)."""
    assert (ROOT / "data" / "MANIFEST.sha256.tsr").exists(), "Missing data/MANIFEST.sha256.tsr"
    assert (ROOT / "data" / "MANIFEST.sha256.ots").exists(), "Missing data/MANIFEST.sha256.ots"
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "stamp_timestamps.py"), "--verify", "--negative-test"],
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, f"Timestamp check failed:\n{proc.stdout}\n{proc.stderr}"
