# Configuration Reference (`docs/configuration.md`)

This project requires **zero runtime secrets, API keys, or external services** for core verification. All tool configurations are version-controlled and deterministic:

| File | Purpose |
| --- | --- |
| `lean/lean-toolchain` | Pins `leanprover/lean4:v4.35.0` |
| `lean/lakefile.toml` | Zero-Mathlib Lake configuration (`autoImplicit = false`, `relaxedAutoImplicit = false`, `linter.unusedVariables = true`, `defaultTargets = ["CDTerrace", "Challenge", "Solution", "PalomarSolution"]`) |
| `lean/comparator.json` | Palomar Comparator 23-target statement contract & allowed axiom list |
| `lean/formalization.yaml` | Machine-readable formalization metadata |
| `rust/Cargo.toml` | Zero-dependency Rust 2021 edition configuration |
| `c/Makefile` | Strict ISO C11 flags (`-std=c11 -Wall -Wextra -Wpedantic -Werror -Wshadow -Wconversion`), ASan/UBSan & fuzz targets |
| `pyproject.toml` & `requirements.lock.txt` | Python package, pytest, ruff, mypy settings and exact pinned dev dependencies |
| `repo.yaml` & `REUSE.toml` | Build Standard v1.2.0 metadata and SPDX dual-license annotations |
| `.env.example` | Optional environment variables (`PYTHONPATH=src:.`) |
