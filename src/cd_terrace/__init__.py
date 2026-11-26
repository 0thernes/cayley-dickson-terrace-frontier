# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Exact arithmetic engine for Generalized Cayley-Dickson Algebras CD_n(gamma)."""

from .core import (
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

__version__ = "1.0.0"

__all__ = [
    "CHINGON_WITNESS_16",
    "PATHION_WITNESS_14",
    "__version__",
    "block_delta",
    "cd_max_clique",
    "cd_sign",
    "cd_sign_gamma_direct",
    "cd_sign_gamma_factored",
    "doubled_right_witness",
    "hurwitz_radon",
    "is_norm_mult_pair",
    "non_zd_formula",
    "nullity_histogram",
    "nullity_histogram_gamma",
    "right_compat",
    "total_mass_formula",
    "twoblade_nullity_direct",
    "twoblade_nullity_fast",
    "twoblade_nullity_gamma",
]
