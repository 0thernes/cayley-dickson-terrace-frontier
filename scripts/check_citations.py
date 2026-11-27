# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Citation syntax, title/author/year matching, full Crossref retraction checks,
bijective \\cite{} coverage against paper/main.tex, and polite live Crossref/arXiv verification."""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIB_PATH = ROOT / "paper" / "references.bib"
TEX_PATH = ROOT / "paper" / "main.tex"
VERSION_PATH = ROOT / "VERSION"
REPO_VERSION = VERSION_PATH.read_text(encoding="utf-8").strip() if VERSION_PATH.exists() else "2.1.0"
USER_AGENT = f"cayley-dickson-terrace-frontier/{REPO_VERSION} (mailto:0_0@0thernes.art)"

ENTRY_RE = re.compile(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", re.IGNORECASE)
CITE_RE = re.compile(r"\\cite(?:\[[^\]]*\])*\{([^}]+)\}")
STOPWORDS = {
    "the", "of", "and", "in", "on", "for", "a", "an", "to", "with", "by", "from",
    "at", "as", "is", "are", "der", "die", "das", "und", "von", "uber", "ueber",
}


def _ascii_fold(text: str) -> str:
    clean = re.sub(r"\\[a-zA-Z'\"`^~]+\{([^}]*)\}", r"\1", text)
    clean = re.sub(r"[{}]", "", clean)
    return unicodedata.normalize("NFKD", clean).encode("ascii", "ignore").decode("ascii").lower()


def _title_words(text: str) -> set[str]:
    clean = re.sub(r"[^a-z0-9]+", " ", _ascii_fold(text))
    return {w for w in clean.split() if len(w) >= 3 and w not in STOPWORDS}


def title_overlap(expected: str, actual: str) -> float:
    ew = _title_words(expected)
    aw = _title_words(actual)
    if not ew or not aw:
        return 0.0
    return len(ew & aw) / min(len(ew), len(aw))


def _first_author_surname(author_field: str) -> str:
    first = author_field.split(" and ")[0].strip()
    if "," in first:
        return _ascii_fold(first.split(",", 1)[0]).strip()
    parts = _ascii_fold(first).split()
    return parts[-1] if parts else ""


def parse_bib(text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    matches = list(ENTRY_RE.finditer(text))
    for idx, m in enumerate(matches):
        start = m.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        block = text[start:end]

        def field(name: str) -> str:
            fm = re.search(rf"\b{name}\s*=\s*\{{((?:[^{{}}]|\{{[^{{}}]*\}})*)\}}", block, re.IGNORECASE | re.DOTALL)
            return " ".join(fm.group(1).split()) if fm else ""

        entries.append(
            {
                "type": m.group(1).lower(),
                "key": m.group(2),
                "title": field("title"),
                "author": field("author"),
                "year": field("year"),
                "doi": field("doi"),
                "arxiv": field("eprint"),
            }
        )
    return entries


def extract_cited_keys(tex_text: str) -> set[str]:
    cited: set[str] = set()
    for m in CITE_RE.finditer(tex_text):
        for raw_key in m.group(1).split(","):
            k = raw_key.strip()
            if k:
                cited.add(k)
    return cited


def _crossref_is_retracted(msg: dict) -> str | None:
    if "retract" in str(msg.get("type", "")).lower():
        return f"RETRACTED (type={msg.get('type')})"
    for field_name in ("update-to", "update-by"):
        for upd in msg.get(field_name, []) or []:
            if "retract" in str(upd.get("type", "")).lower() or "retract" in str(upd.get("label", "")).lower():
                return f"RETRACTED ({field_name}: {upd.get('type') or upd.get('label')})"
    rel = msg.get("relation") or {}
    if isinstance(rel, dict):
        for rel_key in ("is-retracted-by", "has-retraction", "is-withdrawn-by"):
            if rel.get(rel_key):
                return f"RETRACTED (relation.{rel_key})"
    return None


def check_doi_live(
    doi: str,
    expected_title: str = "",
    expected_author: str = "",
    expected_year: str = "",
) -> tuple[bool, str]:
    url = f"https://api.crossref.org/works/{urllib.parse.quote(doi, safe='')}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": USER_AGENT},
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            if resp.status not in (200, 202):
                return False, f"HTTP {resp.status}"
            data = json.loads(resp.read().decode("utf-8"))
            msg = data.get("message", {})
            retracted = _crossref_is_retracted(msg)
            if retracted:
                return False, retracted
            title = (msg.get("title") or [""])[0].replace("\n", " ").strip()
            if expected_title and title:
                ov = title_overlap(expected_title, title)
                if ov < 0.45:
                    return False, f"TITLE MISMATCH (ov={ov:.2f}, got={title[:60]!r})"
            surname = _first_author_surname(expected_author)
            cr_authors = [_ascii_fold(str(a.get("family", ""))) for a in (msg.get("author") or []) if a.get("family")]
            if surname and cr_authors and not any(surname in a or a in surname for a in cr_authors):
                return False, f"AUTHOR MISMATCH (expected={surname!r}, got={cr_authors[:3]})"
            if expected_year.isdigit():
                years: set[int] = set()
                for key_name in ("published-print", "published-online", "issued", "created"):
                    parts = (msg.get(key_name) or {}).get("date-parts") or []
                    if parts and parts[0] and isinstance(parts[0][0], int):
                        years.add(parts[0][0])
                if years and min(abs(y - int(expected_year)) for y in years) > 5:
                    return False, f"YEAR MISMATCH (expected={expected_year}, crossref={sorted(years)})"
            return True, f"200 OK ({title[:70] or '(untitled)'})"
    except urllib.error.URLError as exc:
        return False, f"URLError: {exc}"


def check_arxiv_live(
    arxiv_id: str,
    expected_title: str = "",
    expected_author: str = "",
) -> tuple[bool, str]:
    clean_id = arxiv_id.replace("arXiv:", "").strip()
    url = f"https://export.arxiv.org/api/query?id_list={urllib.parse.quote(clean_id, safe='/')}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": USER_AGENT},
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            body = resp.read().decode("utf-8", errors="replace")
            if resp.status not in (200, 202) or "<entry>" not in body or "<title>Error</title>" in body:
                return False, f"arXiv lookup failed (HTTP {resp.status})"
            title_m = re.search(r"<entry>.*?<title>(.*?)</title>", body, re.DOTALL)
            title = " ".join(title_m.group(1).split()) if title_m else ""
            if expected_title and title:
                ov = title_overlap(expected_title, title)
                if ov < 0.45:
                    return False, f"TITLE MISMATCH (ov={ov:.2f}, got={title[:60]!r})"
            surname = _first_author_surname(expected_author)
            arx_authors = [_ascii_fold(m) for m in re.findall(r"<author>\s*<name>(.*?)</name>", body, re.DOTALL)]
            if surname and arx_authors and not any(surname in a for a in arx_authors):
                return False, f"AUTHOR MISMATCH (expected={surname!r}, got={arx_authors[:3]})"
            return True, f"200 OK ({title[:70] or '(entry found)'})"
    except urllib.error.URLError as exc:
        return False, f"URLError: {exc}"


def write_literature_log(
    out_path: Path,
    entries: list[dict[str, str]],
    records: list[dict[str, str]],
    verified_live: int,
    unverified_no_id: list[str],
) -> None:
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    lines = [
        "# Literature Search & Live Verification Log (`docs/literature-search-log.md`)",
        "",
        f"*Generated programmatically by `scripts/check_citations.py --live --write-log` on {stamp} "
        f"(version `v{REPO_VERSION}`).*",
        "",
        "## Search Scope & Databases Queried",
        "- **Primary Databases:** Crossref REST API (`https://api.crossref.org/works/{doi}`), "
        "arXiv Export API (`https://export.arxiv.org/api/query`), and mathematical historical primary sources.",
        "- **Queries & Thematic Clusters:**",
        "  1. *Cayley–Dickson algebras, twisted group algebras & sign cocycles:* "
        "`hurwitz1898`, `dickson1919`, `schafer1954`, `albuquerque1999`, `baez2002`, `moriergenoud2011`.",
        "  2. *Zero divisors, annihilator bounds, box-kites, alternative elements & orthogonality graphs:* "
        "`moreno1998`, `demarrais2000`, `demarrais2002`, `cawagas2004`, `moreno2004`, "
        "`biss2007ii`, `biss2008i`, `biss2009eigen`, `zhilina2021i`, `zhilina2021ii`, `reggiani2024sedenions`.",
        "  3. *Hurwitz–Radon theorem & sums-of-squares composition of quadratic forms:* "
        "`hurwitz1922`, `radon1922`, `adams1962`, `adem1975`, `lam1985`, `yiu1987`, "
        "`lamyiu1987`, `yiu1990`, `yiu1994`, `shapiro2000`, `zhangzhu2026hurwitz`.",
        "  4. *Formal proof systems & independent kernel replay:* `demoura2021lean4`, `carneiro2024lean4lean`.",
        "",
        "## Live Verification Summary",
        f"- **Total BibTeX entries (`paper/references.bib`):** `{len(entries)}` "
        f"(100% bijective with `\\cite{{}}` keys in `paper/main.tex`).",
        f"- **Live API verified (title overlap, primary author surname, year, zero retraction):** "
        f"`{verified_live}/{len(entries)}`.",
        f"- **Print-only classical works without DOI/arXiv (explicitly reported, never counted as live-verified):** "
        f"`{len(unverified_no_id)}` ({', '.join(f'`{k}`' for k in unverified_no_id)}).",
        "",
        "## Complete 30-Entry Verification Table",
        "",
        "| BibTeX Key | Year | First Author | Identifier(s) | Live Check Result |",
        "| --- | --- | --- | --- | --- |",
    ]
    for rec in records:
        safe_res = rec["result"].replace("|", "\\|")
        safe_id = rec["identifier"].replace("|", "\\|")
        lines.append(
            f"| `{rec['key']}` | {rec['year']} | {rec['author']} | {safe_id} | {safe_res} |"
        )
    lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_bytes(("\n".join(lines)).encode("utf-8"))
    print(f"Wrote programmatic literature log -> {out_path.relative_to(ROOT)} ({len(records)} entries)")


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify paper/references.bib entries and \\cite{} coverage.")
    parser.add_argument("--live", action="store_true", help="Query live Crossref and arXiv APIs.")
    parser.add_argument(
        "--write-log",
        type=Path,
        default=None,
        help="Write programmatic Markdown verification log (requires --live).",
    )
    args = parser.parse_args()
    if args.write_log is not None and not args.live:
        print("ERROR: --write-log requires --live so the log only contains live API results.", file=sys.stderr)
        return 1

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

    # Bijective \cite{} check against paper/main.tex
    if TEX_PATH.exists():
        cited_keys = extract_cited_keys(TEX_PATH.read_text(encoding="utf-8"))
        bib_key_set = set(keys)
        missing_in_bib = sorted(cited_keys - bib_key_set)
        uncited_in_tex = sorted(bib_key_set - cited_keys)
        if missing_in_bib:
            print(f"FAIL: cited in main.tex but missing in references.bib: {missing_in_bib}", file=sys.stderr)
            failures += len(missing_in_bib)
        if uncited_in_tex:
            print(f"FAIL: present in references.bib but uncited in main.tex: {uncited_in_tex}", file=sys.stderr)
            failures += len(uncited_in_tex)

    verified_live = 0
    unverified_no_id: list[str] = []
    log_records: list[dict[str, str]] = []
    for e in entries:
        doi = e["doi"]
        arxiv = e["arxiv"]
        if doi and not re.match(r"^10\.\d{4,9}/\S+$", doi):
            print(f"FAIL [{e['key']}]: malformed DOI '{doi}'", file=sys.stderr)
            failures += 1
        id_parts = []
        if doi:
            id_parts.append(f"DOI `{doi}`")
        if arxiv:
            id_parts.append(f"arXiv `{arxiv}`")
        id_str = "; ".join(id_parts) if id_parts else "Print-only classic (no DOI/arXiv)"
        first_author = e["author"].split(" and ")[0].strip()

        if not doi and not arxiv:
            unverified_no_id.append(e["key"])
            if args.live:
                print(f"  [NO-ID] {e['key']} (classic print/proceedings entry without DOI/arXiv — unverified live)")
                log_records.append(
                    {
                        "key": e["key"],
                        "year": e["year"],
                        "author": first_author,
                        "identifier": id_str,
                        "result": "Print-only classic (no DOI/arXiv; not counted as live-verified)",
                    }
                )
            continue
        if args.live:
            entry_ok = True
            notes: list[str] = []
            if doi:
                ok, info = check_doi_live(
                    doi,
                    expected_title=e["title"],
                    expected_author=e["author"],
                    expected_year=e["year"],
                )
                status = "OK" if ok else "FAIL"
                print(f"  [{status}] {e['key']} DOI {doi} -> {info}")
                notes.append(f"Crossref {status}: {info}")
                if not ok:
                    failures += 1
                    entry_ok = False
                time.sleep(0.5)
            if arxiv:
                ok, info = check_arxiv_live(
                    arxiv,
                    expected_title=e["title"],
                    expected_author=e["author"],
                )
                status = "OK" if ok else "FAIL"
                print(f"  [{status}] {e['key']} arXiv {arxiv} -> {info}")
                notes.append(f"arXiv {status}: {info}")
                if not ok:
                    failures += 1
                    entry_ok = False
                time.sleep(0.5)
            if entry_ok:
                verified_live += 1
            log_records.append(
                {
                    "key": e["key"],
                    "year": e["year"],
                    "author": first_author,
                    "identifier": id_str,
                    "result": "; ".join(notes),
                }
            )

    if failures:
        print(f"ERROR: {failures} citation check(s) failed.", file=sys.stderr)
        return 1
    if args.live and args.write_log is not None:
        out_path = args.write_log if args.write_log.is_absolute() else (ROOT / args.write_log)
        write_literature_log(out_path, entries, log_records, verified_live, unverified_no_id)
    if args.live:
        print(
            f"PASS (LIVE Crossref/arXiv title+author+year+retraction+cite-bijection): "
            f"{verified_live}/{len(entries)} entries verified live; "
            f"{len(unverified_no_id)} identifier-less print entries reported ({', '.join(unverified_no_id)})."
        )
    else:
        print(
            f"PASS (offline syntax/uniqueness/cite-bijection): {len(entries)} BibTeX entries parsed "
            f"({len(entries) - len(unverified_no_id)} with DOI/arXiv, "
            f"{len(unverified_no_id)} print-only: {', '.join(unverified_no_id)})."
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
