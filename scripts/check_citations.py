# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Citation syntax, retraction, and live Crossref / arXiv verification for paper/references.bib."""

from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIB_PATH = ROOT / "paper" / "references.bib"

DOI_RE = re.compile(r"doi\s*=\s*\{([^}]+)\}", re.IGNORECASE)
ARXIV_RE = re.compile(r"eprint\s*=\s*\{([^}]+)\}", re.IGNORECASE)
ENTRY_RE = re.compile(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", re.IGNORECASE)


def parse_bib(text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    matches = list(ENTRY_RE.finditer(text))
    for idx, m in enumerate(matches):
        start = m.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        block = text[start:end]
        doi_m = DOI_RE.search(block)
        arxiv_m = ARXIV_RE.search(block)
        entries.append(
            {
                "type": m.group(1).lower(),
                "key": m.group(2),
                "doi": doi_m.group(1).strip() if doi_m else "",
                "arxiv": arxiv_m.group(1).strip() if arxiv_m else "",
            }
        )
    return entries


def check_doi_live(doi: str) -> tuple[bool, str]:
    url = f"https://api.crossref.org/works/{urllib.parse.quote(doi, safe='')}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "cayley-dickson-terrace-frontier/1.0 (mailto:0_0@0thernes.art)"},
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            if resp.status not in (200, 202):
                return False, f"HTTP {resp.status}"
            data = json.loads(resp.read().decode("utf-8"))
            msg = data.get("message", {})
            # Check Crossref update-to for retraction
            for upd in msg.get("update-to", []) or []:
                if str(upd.get("type", "")).lower() == "retraction":
                    return False, "RETRACTED"
            title = (msg.get("title") or ["(untitled)"])[0][:70]
            return True, f"200 OK ({title})"
    except urllib.error.URLError as exc:
        return False, f"URLError: {exc}"


def check_arxiv_live(arxiv_id: str) -> tuple[bool, str]:
    clean_id = arxiv_id.replace("arXiv:", "").strip()
    url = f"https://export.arxiv.org/api/query?id_list={urllib.parse.quote(clean_id, safe='/')}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "cayley-dickson-terrace-frontier/1.0 (mailto:0_0@0thernes.art)"},
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            body = resp.read().decode("utf-8", errors="replace")
            if resp.status not in (200, 202) or "<entry>" not in body or "<title>Error</title>" in body:
                return False, f"arXiv lookup failed (HTTP {resp.status})"
            title_m = re.search(r"<entry>.*?<title>(.*?)</title>", body, re.DOTALL)
            title = " ".join(title_m.group(1).split())[:70] if title_m else "(entry found)"
            return True, f"200 OK ({title})"
    except urllib.error.URLError as exc:
        return False, f"URLError: {exc}"


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify paper/references.bib entries.")
    parser.add_argument("--live", action="store_true", help="Query live Crossref and arXiv APIs.")
    args = parser.parse_args()

    if not BIB_PATH.exists():
        print(f"ERROR: missing {BIB_PATH}", file=sys.stderr)
        return 1

    text = BIB_PATH.read_text(encoding="utf-8")
    entries = parse_bib(text)
    if len(entries) < 15:
        print(f"ERROR: expected >= 15 bibliography entries, found {len(entries)}", file=sys.stderr)
        return 1

    keys = [e["key"] for e in entries]
    if len(keys) != len(set(keys)):
        print("ERROR: duplicate BibTeX keys detected", file=sys.stderr)
        return 1

    failures = 0
    for e in entries:
        doi = e["doi"]
        arxiv = e["arxiv"]
        if doi and not re.match(r"^10\.\d{4,9}/\S+$", doi):
            print(f"FAIL [{e['key']}]: malformed DOI '{doi}'", file=sys.stderr)
            failures += 1
        if args.live:
            if doi:
                ok, info = check_doi_live(doi)
                status = "OK" if ok else "FAIL"
                print(f"  [{status}] {e['key']} DOI {doi} -> {info}")
                if not ok:
                    failures += 1
            if arxiv:
                ok, info = check_arxiv_live(arxiv)
                status = "OK" if ok else "FAIL"
                print(f"  [{status}] {e['key']} arXiv {arxiv} -> {info}")
                if not ok:
                    failures += 1

    if failures:
        print(f"ERROR: {failures} citation check(s) failed.", file=sys.stderr)
        return 1
    mode = "LIVE Crossref/arXiv" if args.live else "offline syntax/uniqueness"
    print(f"PASS: {len(entries)} BibTeX entries verified ({mode}).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
