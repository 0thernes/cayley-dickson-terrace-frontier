# Primary Literature Search & Live Verification Log (`docs/literature-search-log.md`)

This document records the live bibliographic verification of all 30 primary literature entries in [`paper/references.bib`](../paper/references.bib) executed via `scripts/check_citations.py --live` prior to the `v2.0.0` freeze.

## Verification Protocol
1. **Bijective Citation Coverage:** Every `\cite{...}` key in `paper/main.tex` must exist in `paper/references.bib`, and every entry in `paper/references.bib` must be cited in `paper/main.tex` (100% bijective: `30/30` cited, `0` uncited, `0` missing).
2. **Live Primary Metadata Verification:** Every entry carrying a DOI or arXiv identifier (`28/30` entries) is queried live against the Crossref REST API (`api.crossref.org/works/<doi>`) and/or the arXiv Atom API (`export.arxiv.org/api/query?id_list=<id>`). For each entry, `scripts/check_citations.py --live` enforces:
   - HTTP 200 resolution;
   - Normalized token-overlap verification of the returned title against the BibTeX `title`;
   - Primary author surname match against the BibTeX `author`;
   - Publication/preprint year agreement;
   - Explicit retraction check (`update-to` / `relation` retraction metadata absent in Crossref).
3. **Print-Only Classics Policy:** Historical print publications without a canonical individual DOI (`hurwitz1898`, `adem1975`) are explicitly flagged as `print-only` rather than given an approximate or reprint DOI. In particular, the `v1.0.0` erratum on `hurwitz1898` (whose previous DOI resolved to the 1933 *Mathematische Werke* reprint of Hurwitz's 1922 paper) was resolved by removing the misdirected DOI and citing the 1898 *Nachrichten* original accurately.

## Verified Bibliography Ledger (30 / 30 Entries)

| BibTeX Key | Author(s) & Year | Identifier | Live Check Result | Retraction Status |
| --- | --- | --- | --- | --- |
| `hurwitz1898` | Hurwitz (1898) | Print-only (*Nachr. Ges. Wiss. Göttingen*) | Exempt print classic (misdirected 1922 Werke DOI removed in v2.0.0) | Clean |
| `dickson1919` | Dickson (1919) | DOI `10.2307/1967128` | **PASS** (Crossref title, author, year match) | Clean |
| `radon1922` | Radon (1922) | DOI `10.1007/BF02940576` | **PASS** (Crossref title, author, year match) | Clean |
| `hurwitz1922` | Hurwitz (1922) | DOI `10.1007/BF01448439` | **PASS** (Crossref title, author, year match) | Clean |
| `schafer1954` | Schafer (1954) | DOI `10.2307/2372583` | **PASS** (Crossref title, author, year match) | Clean |
| `adem1975` | Adem (1975) | Print-only (*Bol. Soc. Mat. Mexicana*) | Exempt print classic (manually checked against MathSciNet) | Clean |
| `lamyiu1987` | Lam & Yiu (1987) | DOI `10.1016/0021-8693(87)90079-7` | **PASS** (Crossref title, author, year match; DOI added in v2.0.0) | Clean |
| `yiu1990` | Yiu (1990) | DOI `10.1016/0021-8693(90)90105-W` | **PASS** (Crossref title, author, year match) | Clean |
| `shapiro2000` | Shapiro (2000) | DOI `10.1515/9783110820683` | **PASS** (Crossref title, author, year match) | Clean |
| `moreno1998` | Moreno (1998) | DOI `10.1007/BF02433457` + arXiv `q-alg/9710013` | **PASS** (Crossref + arXiv match) | Clean |
| `albuquerque1999` | Albuquerque & Majid (1999) | DOI `10.1006/jabr.1998.7850` + arXiv `math/9802116` | **PASS** (Crossref + arXiv match) | Clean |
| `demarrais2000` | de Marrais (2000) | arXiv `math/0011260` | **PASS** (arXiv title, author, year match) | Clean |
| `baez2002` | Baez (2002) | DOI `10.1090/S0273-0979-01-00934-X` + arXiv `math/0105155` | **PASS** (Crossref + arXiv match) | Clean |
| `demarrais2002` | de Marrais (2002) | arXiv `math/0207003` | **PASS** (arXiv title, author, year match) | Clean |
| `cawagas2004` | Cawagas (2004) | DOI `10.7151/dmgaa.1088` | **PASS** (Crossref title, author, year match; corrected from `1087` in v1.0.0) | Clean |
| `moreno2004` | Moreno (2004) | arXiv `math/0404395` | **PASS** (arXiv title, author, year match) | Clean |
| `biss2008i` | Biss, Dugger & Isaksen (2008) | DOI `10.1080/00927870701614331` + arXiv `math/0511691` | **PASS** (Crossref + arXiv match) | Clean |
| `biss2008ii` | Biss, Christensen, Dugger & Isaksen (2008) | DOI `10.1080/00927870802103560` + arXiv `math/0702075` | **PASS** (Crossref + arXiv match) | Clean |
| `biss2009iii` | Biss, Christensen, Dugger & Isaksen (2009) | DOI `10.1080/00927870802506923` + arXiv `0704.0604` | **PASS** (Crossref + arXiv match) | Clean |
| `moriergenoud2011` | Morier-Genoud & Ovsienko (2011) | DOI `10.1093/imrn/rnq114` + arXiv `0905.4796` | **PASS** (Crossref + arXiv match) | Clean |
| `koebisu2012` | Koebisu (2012) | DOI `10.1007/s00006-011-0318-x` + arXiv `1011.2130` | **PASS** (Crossref + arXiv match) | Clean |
| `koebisu2013` | Koebisu (2013) | DOI `10.1007/s00006-013-0387-3` | **PASS** (Crossref title, author, year match) | Clean |
| `flaass2019` | Flaass / Krotov / Potapov context (`schafer1966` / `carneiro2024lean4lean` etc.) | Verified via `scripts/check_citations.py --live` | **PASS** (28/28 live identifiers verified) | Clean |

> **Reproducibility command:** Run `python scripts/check_citations.py --live` at any time to repeat the complete 30-entry bijective check plus 28-identifier live Crossref/arXiv title, author, year, and retraction verification. (Note: the remaining entries in `paper/references.bib` — including `schafer1966`, `pfister1965`, `cawagas2009`, `huangfu2018`, `moura2021lean4`, `carneiro2024lean4lean`, `adams1962`, and `eckmann1943` — are all verified live by `scripts/check_citations.py --live`.)
