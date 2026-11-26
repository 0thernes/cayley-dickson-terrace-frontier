# Security & Soundness Policy (`SECURITY.md`)

## Scope
This repository contains formal Lean 4.35.0 proofs, offline mathematical verifiers (Rust, ISO C11, Python), static HTML/JS visualization assets, and LaTeX manuscript sources. Security- and soundness-critical defects include:
- Any Lean kernel soundness bypass, unintended axiom, statement-fidelity mismatch in `Challenge.lean`/`PalomarChallenge.lean`, or hidden `sorry`/`native_decide`.
- Memory-safety bugs, undefined behavior, or integer overflows in the ISO C11 verifier (`c/`).
- Supply-chain, CI workflow injection, or checksum integrity issues.

## Reporting a Vulnerability or Soundness Bug
Please report suspected security or soundness issues privately via [GitHub Security Advisories](https://github.com/0thernes/cayley-dickson-terrace-frontier/security/advisories/new) or by email to `0_0@0thernes.art`. We aim to acknowledge reports within 72 hours and publish verified fixes alongside transparent entries in [`ERRATA.md`](ERRATA.md).
