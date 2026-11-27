# ADR-0004: Pure-Kernel Pathion $2^{32}$ Exhaustion (`T4e`), Full Kernel Basis (`T1f`) & Dual Timestamps

- **Status:** Accepted (2026-11-26)
- **Context:** In `v1.0.0`, the Pathion ceiling $r_{\max}(\mathrm{CD}_5) = 14$ relied on an external floating-point HiGHS MILP solver (`[EXACT-COMP]`), the dimension-64 split interior spectral gap $H_6^{56}(20) = 0$ was purely computational, Lean nullity was stated on block counts without a formalized bilinear product, and frozen manifests lacked independent third-party cryptographic timestamps.
- **Decision:**
  1. Formalize the exact integer bilinear multiplication `cdMulCoordGamma` and prove an explicit $\mathbb{Z}$-basis isomorphism for $\ker L_{e_i+e_j}$ (`T1f`) directly in zero-Mathlib Lean 4.35.0.
  2. Replace the MILP trust assumption for $r_{\max}(\mathrm{CD}_5) = 14$ with pure-kernel exhaustion over all $2^{32}$ masks and duplicate-free lists (`T4e`, `CDTerrace.PathionRupture`) using half-swap symmetry, `Forb8` branch-and-bound pruning, and an O(1) constructor-dispatched `Vtx` clique-cover pigeonhole certificate (`popcount16_le_clique_cover`), simultaneously proving strict $7+7$ half-balance rigidity.
  3. Certify the complete 9-bin histogram at $\mathrm{CD}_6(56)$ in the pure Lean kernel (`T4f`, `cd6QuadTree56` + mirror conservation).
  4. Stamp `data/MANIFEST.sha256` with independent DigiCert RFC 3161 (`.tsr`) and 3-calendar Bitcoin OpenTimestamps (`.ots`) proofs verified with an automated negative tamper check, and harden CI with a real tamper-injecting negative comparator/axiom gate.
- **Consequences:**
  - *Positive:* Retires HiGHS MILP completely from the proof trust base; eliminates all 7 statement-fidelity gaps from the 2026-11-26 audit; provides third-party existence timestamps alongside SLSA Rekor attestations.
  - *Trade-off:* Increases the Lean proof suite to 22 headline theorems (23 Palomar targets, 35 audited declarations), requiring careful kernel-reduction engineering (`Vtx` constructor matching and balanced binary trees) to keep all 6 independent kernels fast.
