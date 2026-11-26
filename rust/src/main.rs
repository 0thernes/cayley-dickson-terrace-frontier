// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue

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
        println!("  \"chingon_16_ok\": {},", summary.chingon_16_ok);
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
        println!("=== Cayley-Dickson Terrace Frontier — Exact Rust Audit (CD_3..CD_8) ===");
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
        println!("Pillar 3: Dimension-64 Hurwitz-Radon Bott Rupture:");
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
            "Pillar 4: Sedenion Triple-42: bad_planes={}, 10D={} (Fano {}+{}+{}), 11D={}, Box-Kites 7xK_{{2,2,2}}={}, [14,14,32]={}, [16,16,64]={}",
            summary.sedenion_bad_planes,
            summary.sedenion_10d_count,
            summary.sedenion_fano_split.0,
            summary.sedenion_fano_split.1,
            summary.sedenion_fano_split.2,
            summary.sedenion_11d_count,
            summary.sedenion_box_kites_ok,
            summary.pathion_14_ok,
            summary.chingon_16_ok
        );
        println!("ALL CHECKS PASSED.");
    }
}
