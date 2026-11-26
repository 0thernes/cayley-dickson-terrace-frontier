# ADR-0001: Zero-Mathlib Lean 4.35.0 & Six-Kernel Palomar Verification

- **Status:** Accepted (2026-11-26)
- **Context:** Large formalizations depending on Mathlib carry millions of lines of transitive code, long cache downloads, and heavy elaboration overhead when replaying proofs across independent external typecheckers (`lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Decision:** Formalize the entire Cayley–Dickson Terrace, Mirror Conservation, Hurwitz–Radon Rupture, and Sedenion Triple-42 theory directly on Lean 4.35.0 core (`leanprover/lean4:v4.35.0`) with zero Mathlib dependency, zero `native_decide`, pure C-primitive kernel reduction (`rfl`) for finite certificates, and a Palomar Comparator statement contract (`PalomarChallenge` vs. `PalomarSolution`).
- **Consequences:**
  - *Positive:* Minimal trusted computing base, ~90s clean build from scratch, deterministic 6-kernel replay (`lake check --paranoid`, `lake comparator --paranoid`), and clean `leanchecker-paranoid --fresh` verification.
  - *Trade-off:* Elementary arithmetic and list combinatorics lemmas (`sumNat`, `countPred`, `sumUnordered`, `xor` bit identities) are proved explicitly in-repo (~4,200 lines total), which also improves standalone human auditability.
