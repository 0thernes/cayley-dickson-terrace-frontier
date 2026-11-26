# ADR-0002: Dual Apache-2.0 / CC-BY-4.0 Licensing & Cryptographic Provenance

- **Status:** Accepted (2026-11-26)
- **Context:** Scientific research repositories combine executable code/proof scripts (best served by a patent-granting open-source license) with academic prose, figures, and frozen datasets (best served by an attribution license).
- **Decision:** Adopt dual licensing (`Apache-2.0` in `LICENSE` for code/proofs/CI; `CC-BY-4.0` in `LICENSE-DOCS` for manuscript/figures/data/documentation), declared declaratively in `REUSE.toml`, alongside LF-normalized SHA-256 manifests (`data/MANIFEST.sha256`, `MANIFEST.sha256`), GitHub Actions SLSA build provenance attestation (`actions/attest-build-provenance@v2`), and Software Heritage archival.
- **Consequences:**
  - *Positive:* Zero licensing ambiguity for downstream mathematicians and software engineers; tamper-evident archival integrity for the frozen PDF, arXiv tarball, and JSON datasets.
  - *Trade-off:* All text files must remain LF-normalized prior to regenerating manifests so Linux CI `sha256sum -c` matches Windows generation bit-for-bit.
