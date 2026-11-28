# Agent & Contributor Guide (`AGENTS.md`)

This repository (`cayley-dickson-terrace-frontier`, Archive ID `0TH-2026-019`) is a formally verified mathematical research project following the **Build Standard for LLMs v1.2.0** (`docs/build-standard.md`).

## Non-Negotiable Rules
1. **Lean 4.35.0 Strictness (`lean/`):**
   - Zero Mathlib. Every `.lean` file begins with `module`.
   - Zero `sorry` (except the intentional statement-only contract `lean/PalomarChallenge.lean`, which is excluded from `defaultTargets`), zero `admit`, zero `native_decide`, zero custom axioms.
   - Every headline theorem (`T1a`–`T6c` + master conjunction, 29 Palomar targets), 6 non-vacuity witnesses (`NV1`–`NV6`), and 10 adversarial refutations (`A1`–`A10`) (45 audited declarations) must audit via `VerifyAxioms.lean` strictly within `{propext, Classical.choice, Quot.sound}`.
   - `README.md` must contain the exact verbatim output of `results/lean_axioms.txt` (enforced by `scripts/check_readme_axioms.py`).
2. **Epistemic Integrity:**
   - Strictly separate `[LEAN-6K]` (6-kernel machine-checked), `[EXACT-COMP]` (deterministic exact Rust/C11/Python certificates), and `[OPEN]` claims. Never claim `ALG-035`, `ALG-039`, `COMB-040`, or general real sums-of-squares solved.
3. **Author Identity & Licensing:**
   - Author: `Alexander Stephen Donahue` (`Independent Researcher, Spokane, WA, USA`, ORCID `0009-0006-8168-9648`, `0_0@0thernes.art`).
   - Dual license: `Apache-2.0` (code) + `CC-BY-4.0` (paper, figures, data, docs), declared in `REUSE.toml`.
4. **Git & CI Conventions:**
   - Commit and push directly to `main`; unsigned commits and tags; report-only CI (`ci.yml`) and static Pages deployment (`pages.yml`).
   - Normalize all tracked text files (except `.ps1`/`.bat`/`.cmd`) to LF (`\n`) before regenerating `data/MANIFEST.sha256` and `MANIFEST.sha256` via `python scripts/generate_manifests.py`.
