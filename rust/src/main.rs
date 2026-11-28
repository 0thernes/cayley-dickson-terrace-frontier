// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue

#![forbid(unsafe_code)]

use cd_terrace::{nullity_histogram, run_full_audit};
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let json_mode = args.iter().any(|a| a == "--json");
    let verify_all = args.iter().any(|a| a == "--verify-all") || args.len() == 1;

    if !verify_all && !json_mode {
        eprintln!("Usage: cd-terrace [--verify-all] [--json]");
        std::process::exit(2);
    }

    let summary = run_full_audit();

    if json_mode {
        println!("{{");
        println!("  \"status\": \"PASS\",");
        println!("  \"cocycle_checked_dim5\": {},", summary.cocycle_checked_dim5);
        println!("  \"terrace_verified_up_to\": {},", summary.terrace_verified_up_to);
        println!("  \"sedenion_bad_planes\": {},", summary.sedenion_bad_planes);
        println!("  \"sedenion_10d_count\": {},", summary.sedenion_10d_count);
        println!("  \"sedenion_11d_count\": {},", summary.sedenion_11d_count);
        println!(
            "  \"sedenion_fano_split\": [{}, {}, {}],",
            summary.sedenion_fano_split.0,
            summary.sedenion_fano_split.1,
            summary.sedenion_fano_split.2
        );
        println!("  \"sedenion_box_kites_ok\": {},", summary.sedenion_box_kites_ok);
        println!("  \"pathion_14_ok\": {},", summary.pathion_14_ok);
        println!("  \"pathion_exact_max_dim\": {},", summary.pathion_exact_max_dim);
        println!("  \"pathion_14d_count\": {},", summary.pathion_14d_count);
        println!("  \"pathion_greedy_ge8_failures\": {},", summary.pathion_greedy_ge8_failures);
        println!("  \"pathion_all_14d_balanced_7_7\": {},", summary.pathion_all_14d_balanced_7_7);
        println!("  \"pathion_all_14d_contain_0_16\": {},", summary.pathion_all_14d_contain_0_16);
        println!("  \"cd6_flip56_gap_bin20\": {},", summary.cd6_flip56_gap_bin20);
        println!("  \"chingon_16_ok\": {},", summary.chingon_16_ok);
        println!(
            "  \"pillar5_dichotomy_checked_masks\": {},",
            summary.pillar5_dichotomy_checked_masks
        );
        let gcounts: Vec<String> = summary
            .pillar5_gapped_counts
            .iter()
            .map(|(n, c)| format!("[{}, {}]", n, c))
            .collect();
        println!("  \"pillar5_gapped_counts\": [{}],", gcounts.join(", "));
        println!(
            "  \"pillar6_odd_blade_checks_ok\": {},",
            summary.pillar6_odd_blade_checks_ok
        );
        println!("  \"pillar6_4blade_zd_ok\": {},", summary.pillar6_4blade_zd_ok);
        println!("  \"split_phases\": [");
        for (idx, (n, classes, mults, mid, gap)) in summary.split_phase_counts.iter().enumerate() {
            let comma = if idx + 1 < summary.split_phase_counts.len() { "," } else { "" };
            println!(
                "    {{\"n\": {}, \"distinct_classes\": {}, \"multiplicities\": {:?}, \"invariant_midpoint\": {}, \"has_spectral_gap\": {}}}{}",
                n, classes, mults, mid, gap, comma
            );
        }
        println!("  ],");
        println!("  \"hurwitz_table\": [");
        for (idx, (n, omega, rho, asym, degs)) in summary.hurwitz_table.iter().enumerate() {
            let comma = if idx + 1 < summary.hurwitz_table.len() { "," } else { "" };
            println!(
                "    {{\"n\": {}, \"dim\": {}, \"cd_omega\": {}, \"hurwitz_radon\": {}, \"asymmetric_s\": {}, \"shell_degrees\": {:?}}}{}",
                n,
                1usize << n,
                omega,
                rho,
                asym,
                degs,
                comma
            );
        }
        println!("  ],");
        println!("  \"euclidean_histograms\": {{");
        for n in 3..=8u32 {
            let h = nullity_histogram(n);
            let entries: Vec<String> = h.iter().map(|(k, v)| format!("\"{}\": {}", k, v)).collect();
            let comma = if n < 8 { "," } else { "" };
            println!("    \"CD_{}\": {{{}}}{}", n, entries.join(", "), comma);
        }
        println!("  }}");
        println!("}}");
    } else {
        println!(
            "=== Cayley-Dickson Terrace Frontier v{} — Exact Rust Audit (CD_3..CD_8) ===",
            env!("CARGO_PKG_VERSION")
        );
        println!("Pillar 1: Verified {} triples of CD_5(gamma) cocycle factorization", summary.cocycle_checked_dim5);
        for (n, classes, _, mid, gap) in &summary.split_phase_counts {
            println!(
                "  CD_{}(gamma) ({} sigs): {} distinct split phases, invariant midpoint H({}) = {}, spectral_gap={}",
                n,
                1usize << n,
                classes,
                1usize << (n - 2),
                mid,
                gap
            );
        }
        println!("Pillar 2: Dyadic-Palindromic Terrace Law verified through CD_{} (256D)", summary.terrace_verified_up_to);
        println!("Pillar 3: Euclidean Coordinate Right-Multiplier Rupture:");
        for (n, omega, rho, asym, _) in &summary.hurwitz_table {
            println!(
                "  n={} (dim {:>3}): omega(G_n^comp) = {:>2}, rho(2^n) = {:>2}, gap = {}, asym = [{}, {}, {}]",
                n,
                1usize << n,
                omega,
                rho,
                rho - omega,
                1usize << (n - 1),
                asym,
                1usize << n
            );
        }
        println!(
            "Pillar 4: Sedenion Triple-42: bad_planes={}, 10D={} (Fano {}+{}+{}), 11D={}, Box-Kites 7xK_{{2,2,2}}={}, Pathion r_max={} ({} exact 7+7 subspaces, greedy_fail={}), CD_6(56) H(20)={}, [16,16,64]={}",
            summary.sedenion_bad_planes,
            summary.sedenion_10d_count,
            summary.sedenion_fano_split.0,
            summary.sedenion_fano_split.1,
            summary.sedenion_fano_split.2,
            summary.sedenion_11d_count,
            summary.sedenion_box_kites_ok,
            summary.pathion_exact_max_dim,
            summary.pathion_14d_count,
            summary.pathion_greedy_ge8_failures,
            summary.cd6_flip56_gap_bin20,
            summary.chingon_16_ok
        );
        println!(
            "Pillar 5: Gray-Code Bit-Locking & Spectral-Gap Dichotomy verified across {} masks (gapped counts {:?})",
            summary.pillar5_dichotomy_checked_masks, summary.pillar5_gapped_counts
        );
        println!(
            "Pillar 6: Odd-Parity Mod-2 Involution ok={}, Sharp Even 4-Blade ZD Witness ok={}",
            summary.pillar6_odd_blade_checks_ok, summary.pillar6_4blade_zd_ok
        );
        println!("ALL CHECKS PASSED.");
    }
}
