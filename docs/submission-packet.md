# Archival Submission Packet (`docs/submission-packet.md`)

This packet consolidates all metadata, integrity checklists, provenance proofs, and mandatory compliance disclosures for archiving **Cayley--Dickson Terrace Frontier (`0TH-2026-019`, `v2.1.0`)** across GitHub Releases, arXiv, Zenodo, and Software Heritage.

## 1. Canonical Bibliographic Metadata
- **Title:** *The Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation, and Coordinate Norm-Multiplicativity Ruptures Across Cayley--Dickson Algebras*
- **Author:** Alexander Stephen Donahue (`Alexander S. Donahue`)
- **Affiliation:** Independent Researcher, Spokane, WA, USA
- **ORCID:** [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648)
- **Contact:** `0_0@0thernes.art` · `https://0thernes.art`
- **Repository:** `https://github.com/0thernes/cayley-dickson-terrace-frontier`
- **Release Version:** `v2.1.0` (superseding `v2.0.0` and `v1.0.0`; all 23 v1.0.0 errata and 34 Cycle 1–3 hardening findings resolved)
- **Archive Registration ID:** `0TH-2026-019` (`0thernes/0thernes-research-archive`)
- **Suggested MSC 2020:** `17A35`, `17A75`, `11E25` (Primary); `05C69`, `68V20` (Secondary)
- **Suggested arXiv Categories:** `math.RA` (Primary), `math.CO`, `cs.LO`
- **Licenses:** Apache-2.0 (`LICENSE`, code and Lean formalization) / CC-BY-4.0 (`LICENSE-DOCS`, manuscript, figures, and datasets)

## 2. Frozen Release Artifacts
- `dist/Donahue_2026_cayley_dickson_terrace_frontier.pdf` — 21-page AMS-LaTeX preprint compiled with Tectonic (0 errors, 0 warnings).
- `dist/arxiv_submission.tar.gz` — Deterministic GNU-tar clean-room arXiv bundle (`main.tex`, `references.bib`, `main.bbl`, `00README.XXX`, `figures/*.pdf`), verified by clean-room compilation in an isolated temp directory.
- `data/MANIFEST.sha256` — SHA-256 manifest of all 4 frozen JSON datasets (`cd4_to_cd8_terraces.json`, `split_phases_cd4_to_cd8.json`, `sedenion_box_kites_and_42_subspaces.json`, `hurwitz_rupture_table.json`).
- `data/MANIFEST.sha256.tsr` — RFC 3161 trusted timestamp response from DigiCert TSA (`http://timestamp.digicert.com`) over `data/MANIFEST.sha256`.
- `data/MANIFEST.sha256.ots` — Multi-calendar Bitcoin OpenTimestamps proof (`alice`, `bob`, `finney`) over `data/MANIFEST.sha256`.
- `MANIFEST.sha256` — Root SHA-256 manifest covering frozen PDF, arXiv tarball, datasets, timestamp proofs, `results/lean_axioms.txt`, and `llms-full.txt`.
- GitHub Actions SLSA Build Provenance Attestation (`actions/attest-build-provenance@v4`) recorded in the Sigstore Rekor transparency log.
- `.zenodo.json` & `docs/gold-standard-checklist.md` — Archival metadata and transparent 43-item Playbook v1.3 release ledger.

## 3. Mandatory Research Integrity & Compliance Disclosures
- **CRediT Author Contribution Statement:** Alexander Stephen Donahue: Conceptualization, Methodology, Formal Analysis, Software, Validation, Visualization, Writing -- Original Draft, Writing -- Review & Editing.
- **AI-Assistance Disclosure (Transparent & arXiv/Zenodo Compliant):** Large language model coding and proof-engineering assistants were used during exploration, Lean 4 proof drafting, tri-language test harness construction, and LaTeX typesetting. Every mathematical claim tagged `[LEAN-6K]` is independently typechecked from scratch by six separate Lean 4.35.0 proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) with zero `sorry`, zero `admit`, zero `native_decide`, and strictly standard axioms `[propext, Classical.choice, Quot.sound]`; every `[EXACT-COMP]` claim is independently cross-verified by Rust, strict ISO C11, and exact rational Python engines; every bibliography entry was verified live against Crossref/arXiv. The human author takes full scholarly responsibility for the manuscript and formal artifacts.
- **Conflict of Interest:** The author declares no competing financial or non-financial interests.
- **Funding:** This research received no external grant funding.
- **Human Subjects / Dual-Use / Export Control:** Pure mathematics and formal proof verification; involves no human subjects, biological agents, personal data, or export-controlled technologies.
- **Prior External Submission Status:** As of the `v2.1.0` freeze, this preprint has not been submitted to a peer-reviewed journal or assigned an arXiv/Zenodo DOI. No external peer review or DOI is claimed prior to actual submission.

## 4. Independent Verification Commands for Reviewers
```bash
# 1. Verify frozen checksums and RFC 3161 / Bitcoin OTS timestamps
sha256sum -c data/MANIFEST.sha256
sha256sum -c MANIFEST.sha256
python scripts/stamp_timestamps.py --verify --negative-test

# 2. Verify all 22 Lean theorems (23 Palomar targets, 35 axiom-audited declarations)
cd lean && lake build && lake env lean VerifyAxioms.lean > ../results/lean_axioms_local.txt
diff -u ../results/lean_axioms.txt ../results/lean_axioms_local.txt
lake env leanchecker --fresh PalomarSolution
lake env leanchecker-paranoid --fresh PalomarSolution
```
