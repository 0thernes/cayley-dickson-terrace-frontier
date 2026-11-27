#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate all 5 publication-grade Okabe-Ito figures (PDF + PNG) and 1280x640 social preview (SVG + PNG)."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"
FIG_DIR = ROOT / "paper" / "figures"
MEDIA_DIR = ROOT / "docs" / "media"
REPO_VERSION = (ROOT / "VERSION").read_text(encoding="utf-8").strip() if (ROOT / "VERSION").exists() else "2.1.0"

# Okabe-Ito colorblind-safe palette (WCAG AA on white background)
OI_BLUE = "#0072B2"
OI_VERM = "#D55E00"
OI_GREEN = "#009E73"
OI_ORANGE = "#E69F00"
OI_PURPLE = "#CC79A7"
OI_SKY = "#56B4E9"
OI_DARK = "#1F2937"
OI_GRAY = "#6B7280"
OI_LIGHT = "#E5E7EB"


def setup_style() -> None:
    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.serif": ["DejaVu Serif", "Computer Modern Roman", "Times New Roman"],
            "mathtext.fontset": "cm",
            "font.size": 10,
            "axes.titlesize": 11.5,
            "axes.labelsize": 10,
            "xtick.labelsize": 9,
            "ytick.labelsize": 9,
            "legend.fontsize": 8.8,
            "axes.edgecolor": OI_DARK,
            "axes.linewidth": 0.9,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "figure.facecolor": "white",
            "axes.facecolor": "white",
            "savefig.dpi": 300,
            "savefig.bbox": "tight",
            "savefig.pad_inches": 0.08,
        }
    )


def save_fig(fig: plt.Figure, stem: str) -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    MEDIA_DIR.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIG_DIR / f"{stem}.pdf")
    fig.savefig(FIG_DIR / f"{stem}.png", dpi=300)
    fig.savefig(MEDIA_DIR / f"{stem}.png", dpi=220)
    plt.close(fig)


def load_json(name: str) -> Any:
    return json.loads((DATA_DIR / name).read_text(encoding="utf-8"))


def make_fig1_terrace_cathedral(terraces: dict[str, Any]) -> None:
    """Fig 1: Dyadic-Palindromic Terrace Cathedral across CD_4..CD_7."""
    fig, axes = plt.subplots(2, 2, figsize=(11.2, 6.8), gridspec_kw={"hspace": 0.38, "wspace": 0.24})
    ns = [4, 5, 6, 7]
    names = {
        4: r"$\mathrm{CD}_4$ (Sedenions, $\dim=16$)",
        5: r"$\mathrm{CD}_5$ (Pathions, $\dim=32$)",
        6: r"$\mathrm{CD}_6$ (Chingons, $\dim=64$)",
        7: r"$\mathrm{CD}_7$ (Routons, $\dim=128$)",
    }

    for ax, n in zip(axes.flat, ns):
        rec = next(r for r in terraces["algebras"] if r["n"] == n)
        hist = {int(k): int(v) for k, v in rec["histogram"].items()}
        vs = sorted(hist.keys())
        counts = [hist[v] for v in vs]
        midpoint = 1 << (n - 2)
        top_bin = (1 << (n - 1)) - 4

        colors = []
        for v in vs:
            if v == 0:
                colors.append(OI_DARK)
            elif v == midpoint:
                colors.append(OI_VERM)
            elif v == top_bin:
                colors.append(OI_ORANGE)
            elif v % 8 == 0:
                colors.append(OI_BLUE)
            else:
                colors.append(OI_GREEN)

        width = 2.6 if n <= 5 else (2.9 if n == 6 else 3.1)
        ax.bar(vs, counts, width=width, color=colors, edgecolor="white", linewidth=0.5, zorder=3)
        ax.grid(axis="y", color=OI_LIGHT, linewidth=0.7, zorder=0)

        # Highlight midpoint spine 42 * 2^(n-4)
        mid_val = hist[midpoint]
        ax.axvline(midpoint, color=OI_VERM, linestyle="--", linewidth=1.0, alpha=0.7, zorder=2)
        if n == 4:
            ax.set_xticks([0, 4])
            ax.annotate(
                rf"Midpoint $H_4(4)={mid_val}$",
                xy=(midpoint, mid_val),
                xytext=(midpoint + 0.6, max(counts) * 0.85),
                fontsize=8.3,
                color=OI_VERM,
                fontweight="bold",
                arrowprops={"arrowstyle": "->", "color": OI_VERM, "lw": 0.9},
            )
        else:
            if n == 5:
                ax.set_xticks([0, 4, 8, 12])
            ax.annotate(
                rf"Midpoint $H_{n}({midpoint})={mid_val}$",
                xy=(midpoint, mid_val),
                xytext=(midpoint * 0.42, max(counts) * 0.87),
                fontsize=8.2,
                color=OI_VERM,
                fontweight="bold",
                arrowprops={"arrowstyle": "->", "color": OI_VERM, "lw": 0.9},
            )
            ax.annotate(
                rf"Top jump $+{3 * ((1 << (n - 1)) - 2)}$",
                xy=(top_bin, hist[top_bin]),
                xytext=(top_bin * 0.62, max(counts) * 0.98),
                fontsize=8.0,
                color="#9A5B00",
                fontweight="bold",
                arrowprops={"arrowstyle": "->", "color": OI_ORANGE, "lw": 0.85},
            )
        ax.set_title(names[n], pad=8, fontweight="bold")
        ax.set_xlabel(r"2-blade left-multiplication nullity $\nu_n^{\mathrm{std}}(i,j)$")
        ax.set_ylabel(r"Pair count $H_n^{\mathrm{std}}(\nu)$")
        ax.set_xlim(-3, top_bin + 4)
        ax.set_ylim(0, max(counts) * 1.20)

    # Shared legend
    from matplotlib.patches import Patch

    handles = [
        Patch(facecolor=OI_DARK, label=r"Zero-divisor-free ($\nu=0$)"),
        Patch(facecolor=OI_BLUE, label=r"Even interior bin ($8m$: doubled child)"),
        Patch(facecolor=OI_GREEN, label=r"Odd interior bin ($2^{n-1}-4-8m$: reversed child)"),
        Patch(facecolor=OI_VERM, label=r"Invariant midpoint $\nu=2^{n-2}$ ($42\cdot 2^{n-4}$)"),
        Patch(facecolor=OI_ORANGE, label=r"Top terrace bin $\nu=2^{n-1}-4$"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=3, frameon=False, bbox_to_anchor=(0.5, -0.04))
    fig.suptitle(
        "The Dyadic-Palindromic Terrace Law: Interleaved Palindromic Spectra & Midpoint 42 Spine",
        fontsize=12.5,
        fontweight="bold",
        y=0.98,
    )
    save_fig(fig, "fig1_dyadic_terrace_cathedral")


def make_fig2_mirror_conservation(split_data: dict[str, Any]) -> None:
    """Fig 2: Nilpotent Mirror Conservation & Spectral-Gap Emergence in CD_5(gamma) and CD_6(gamma)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.6), gridspec_kw={"wspace": 0.25})

    # Left panel: CD_5(gamma) all 8 phases showing mirror pairs (0,16), (4,12) and pinned midpoint 8 -> 84
    rec5 = next(r for r in split_data["levels"] if r["n"] == 5)
    bins5 = [0, 4, 8, 12, 16]
    phases5 = rec5["phases"]
    palette = [OI_DARK, OI_BLUE, OI_VERM, OI_GREEN, OI_ORANGE, OI_PURPLE, OI_SKY, "#7F7F7F"]
    for idx, ph in enumerate(phases5):
        h = {int(k): int(v) for k, v in ph["histogram"].items()}
        ys = [h.get(b, 0) for b in bins5]
        ls = "-" if ph["multiplicity"] == 1 else "--"
        mk = "o" if ph["multiplicity"] == 1 else "s"
        lbl = f"P{idx + 1} (mult {ph['multiplicity']}, flip={ph['example_flip_mask']})"
        ax1.plot(bins5, ys, linestyle=ls, marker=mk, markersize=4.8, linewidth=1.55, color=palette[idx % len(palette)], label=lbl)

    ax1.axvline(8, color=OI_VERM, linestyle=":", linewidth=1.2)
    ax1.scatter([8], [84], s=85, color=OI_VERM, zorder=6, edgecolor="white", linewidth=1.0)
    ax1.annotate(
        r"Universal pin $H_5^\gamma(8)=84$" "\n" r"(all 32 signatures)",
        xy=(8, 84),
        xytext=(5.1, 12),
        fontsize=8.3,
        color=OI_VERM,
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.22", "facecolor": "white", "edgecolor": OI_VERM, "alpha": 0.94},
        arrowprops={"arrowstyle": "->", "color": OI_VERM, "lw": 1.0},
    )
    ax1.set_xticks(bins5)
    ax1.set_ylim(-6, 200)
    ax1.set_xlabel(r"Nullity bin $\nu$ in $\mathrm{CD}_5(\gamma)$")
    ax1.set_ylabel(r"2-blade count $H_5^\gamma(\nu)$")
    ax1.set_title(r"All 8 Spectral Phases of $\mathrm{CD}_5(\gamma)$ ($4\times 1 + 4\times 7$)", fontweight="bold")
    ax1.grid(axis="y", color=OI_LIGHT, linewidth=0.7)
    ax1.legend(loc="upper right", fontsize=7.2, frameon=True, framealpha=0.95)

    # Right panel: CD_6(gamma) standard vs spectral-gap phase
    rec6 = next(r for r in split_data["levels"] if r["n"] == 6)
    bins6 = list(range(0, 33, 4))
    std6 = next(p for p in rec6["phases"] if p["example_flip_mask"] == 0)
    gap6 = next(p for p in rec6["phases"] if len(p.get("spectral_gap_bins", [])) > 0)
    h_std6 = {int(k): int(v) for k, v in std6["histogram"].items()}
    h_gap6 = {int(k): int(v) for k, v in gap6["histogram"].items()}
    y_std6 = [h_std6.get(b, 0) for b in bins6]
    y_gap6 = [h_gap6.get(b, 0) for b in bins6]

    x = np.arange(len(bins6))
    w = 0.38
    ax2.bar(x - w / 2, y_std6, width=w, color=OI_BLUE, label=r"Standard $\mathrm{CD}_6$ ($\mathrm{flip}=0$)", zorder=3)
    ax2.bar(x + w / 2, y_gap6, width=w, color=OI_VERM, label=rf"Gap phase ($\mathrm{{flip}}={gap6['example_flip_mask']}$, mult {gap6['multiplicity']})", zorder=3)

    # Mark interior spectral gap(s) where y_gap6 == 0 for 0 < b < 32
    for i, (b, val) in enumerate(zip(bins6, y_gap6)):
        if 0 < b < 32 and val == 0:
            ax2.annotate(
                rf"Spectral gap!" "\n" rf"$H_6^\gamma({b})=0$",
                xy=(i + w / 2, 6),
                xytext=(i + 1.15, 255),
                fontsize=8.2,
                color=OI_VERM,
                fontweight="bold",
                bbox={"boxstyle": "round,pad=0.22", "facecolor": "white", "edgecolor": OI_VERM, "alpha": 0.94},
                arrowprops={"arrowstyle": "->", "color": OI_VERM, "lw": 1.0},
            )
            break

    # Mark pinned midpoint b=16
    mid_i = bins6.index(16)
    ax2.annotate(
        r"Pinned $H_6^\gamma(16)=168$",
        xy=(mid_i, 168),
        xytext=(mid_i - 1.1, 378),
        fontsize=8.2,
        color=OI_DARK,
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.20", "facecolor": "white", "edgecolor": OI_GRAY, "alpha": 0.94},
        arrowprops={"arrowstyle": "->", "color": OI_DARK, "lw": 0.9},
    )
    ax2.set_ylim(0, 490)

    ax2.set_xticks(x)
    ax2.set_xticklabels([str(b) for b in bins6])
    ax2.set_xlabel(r"Nullity bin $\nu$ in $\mathrm{CD}_6(\gamma)$")
    ax2.set_ylabel(r"2-blade count $H_6^\gamma(\nu)$")
    ax2.set_title(r"Mirror Conservation & Spectral-Gap Emergence at $\dim=64$", fontweight="bold")
    ax2.grid(axis="y", color=OI_LIGHT, linewidth=0.7, zorder=0)
    ax2.legend(loc="upper right", fontsize=8.0, frameon=True, framealpha=0.92)

    save_fig(fig, "fig2_nilpotent_mirror_conservation")


def make_fig3_hurwitz_rupture(hr_data: dict[str, Any]) -> None:
    """Fig 3: Dimension-64 Euclidean Coordinate Right-Multiplier Rupture & Asymmetric Doubling Tower."""
    rows = hr_data["rows"]
    ns = [r["n"] for r in rows]
    omega = [r["cd_max_clique_omega"] for r in rows]
    rho = [r["hurwitz_radon_rho"] for r in rows]
    doubled_r = [r["asymmetric_doubling_triple"][1] for r in rows]
    deficit = [r["rupture_gap"] for r in rows]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.5), gridspec_kw={"wspace": 0.25})

    ax1.plot(ns, rho, marker="o", linewidth=2.1, color=OI_VERM, label=r"Classical Hurwitz–Radon formula $\rho(2^n)$")
    ax1.plot(ns, omega, marker="s", linewidth=2.1, color=OI_BLUE, label=r"Euclidean $\mathrm{CD}_n$ clique $\omega(G_n^{\mathrm{comp}}) = n+5$")
    ax1.plot(ns, doubled_r, marker="^", linestyle="--", linewidth=1.8, color=OI_GREEN, label=r"Asymmetric doubled right-dim $2(n+4)$ (on $\mathrm{CD}_{n-1}$)")

    ax1.axvspan(2.75, 5.25, color=OI_SKY, alpha=0.14, label=r"Exact match ($n\in\{3,4,5\}$: $8,9,10$)")
    ax1.axvline(5.5, color=OI_DARK, linestyle=":", linewidth=1.2)
    ax1.annotate(
        r"Dimension-64 Breakaway" "\n" r"$n=6$: $11 < 12 = \rho(64)$",
        xy=(6, 11),
        xytext=(7.3, 8.8),
        fontsize=8.4,
        color=OI_VERM,
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.22", "facecolor": "white", "edgecolor": OI_VERM, "alpha": 0.94},
        arrowprops={"arrowstyle": "->", "color": OI_VERM, "lw": 1.0},
    )
    ax1.set_xticks(ns)
    ax1.set_ylim(6.5, 34.5)
    ax1.set_xlabel(r"Cayley–Dickson level $n$ ($\dim = 2^n$)")
    ax1.set_ylabel("Maximal coordinate right-multiplier dimension")
    ax1.set_title(r"Euclidean Coordinate Capacity vs. $\rho(2^n)$ ($n=3\ldots 12$)", fontweight="bold")
    ax1.grid(True, color=OI_LIGHT, linewidth=0.7)
    ax1.legend(loc="upper left", fontsize=7.8, frameon=True, framealpha=0.95)

    # Right panel: Exact rupture deficit rho(2^n) - (n+5) vs lower bound n-5
    bar_colors = [OI_SKY if d == 0 else OI_VERM for d in deficit]
    ax2.bar(ns, deficit, color=bar_colors, edgecolor="white", linewidth=0.6, zorder=3)
    lower_bnd = [max(0, n - 5) for n in ns]
    ax2.plot(ns, lower_bnd, marker="d", linestyle="--", color=OI_DARK, linewidth=1.7, label=r"Certified linear lower bound $n-5$ ($n\geq 6$)", zorder=4)
    from matplotlib.patches import Patch
    handles_r, _labels_r = ax2.get_legend_handles_labels()
    handles_r.append(Patch(facecolor=OI_VERM, label=r"Exact coordinate deficit $\rho(2^n) - (n+5)$"))
    for n_val, d_val in zip(ns, deficit):
        ax2.text(n_val, d_val + 0.32, str(d_val), ha="center", va="bottom", fontsize=8.3, color=OI_DARK, fontweight="bold")

    ax2.set_xticks(ns)
    ax2.set_xlabel(r"Cayley–Dickson level $n$ ($\dim = 2^n$)")
    ax2.set_ylabel(r"Deficit $\rho(2^n) - \omega(G_n^{\mathrm{comp}})$")
    ax2.set_title(r"Diverging Coordinate Deficit for All $n \geq 6$", fontweight="bold")
    ax2.set_ylim(0, max(deficit) + 2.8)
    ax2.grid(axis="y", color=OI_LIGHT, linewidth=0.7, zorder=0)
    ax2.legend(handles=handles_r, loc="upper left", fontsize=8.2, frameon=True, framealpha=0.95)

    save_fig(fig, "fig3_hurwitz_rupture")


def make_fig4_sedenion_triple_42(sedenion_data: dict[str, Any]) -> None:
    """Fig 4: Sedenion Triple-42 Duality, 7xK_{2,2,2} Box-Kites & Fano 7+28+7 Split."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.7), gridspec_kw={"wspace": 0.24})

    # Left panel: 7 disjoint K_{2,2,2} octahedra arranged on a circle (each drawn as 6-cycle + 6 chords)
    ax1.set_aspect("equal")
    R_ring = 3.15
    r_oct = 0.88
    strut_colors = [OI_BLUE, OI_VERM, OI_GREEN, OI_ORANGE, OI_PURPLE, OI_SKY, OI_DARK]
    xor_sigs = [9, 10, 11, 12, 13, 14, 15]

    for idx, s in enumerate(xor_sigs):
        theta = math.pi / 2 - 2 * math.pi * idx / 7
        cx, cy = R_ring * math.cos(theta), R_ring * math.sin(theta)
        pts = []
        for k in range(6):
            ang = theta + 2 * math.pi * k / 6
            pts.append((cx + r_oct * math.cos(ang), cy + r_oct * math.sin(ang)))
        # K_{2,2,2}: connect every pair EXCEPT opposite vertices (k, k+3)
        col = strut_colors[idx]
        for a in range(6):
            for b in range(a + 1, 6):
                if (b - a) != 3:
                    ax1.plot([pts[a][0], pts[b][0]], [pts[a][1], pts[b][1]], color=col, alpha=0.55, linewidth=0.95, zorder=2)
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        ax1.scatter(xs, ys, s=28, color=col, edgecolor="white", linewidth=0.6, zorder=4)
        ax1.text(cx, cy, f"$s={s}$", ha="center", va="center", fontsize=8.4, fontweight="bold", color=OI_DARK,
                 bbox={"boxstyle": "round,pad=0.16", "facecolor": "white", "edgecolor": col, "alpha": 0.92})

    ax1.text(0, 0, "42 Assessors\n$7 \\times K_{2,2,2}$\n84 edges\nSpec: $\\{4^7, 0^{21}, (-2)^{14}\\}$",
             ha="center", va="center", fontsize=8.6, fontweight="bold", color=OI_DARK,
             bbox={"boxstyle": "round,pad=0.35", "facecolor": "#F8FAFC", "edgecolor": OI_GRAY, "lw": 0.9})
    ax1.set_xlim(-4.45, 4.45)
    ax1.set_ylim(-4.35, 4.45)
    ax1.axis("off")
    ax1.set_title(r"7 Disjoint Sedenion Box-Kites ($7 \times K_{2,2,2}$)", fontweight="bold")

    # Right panel: Fano 7 + 28 + 7 = 42 decomposition vs Triple-42 invariants
    fano = sedenion_data["sedenion_triple_42"]["fano_intersection_split"]
    cats = [
        (r"$|S \cap \mathbb{O}| = 8$" "\n(Full $\\mathbb{O}$ + 2 upper)"),
        (r"$|S \cap \mathbb{O}| = 5$" "\n(Fano bridge: 5 + 5)"),
        (r"$|S \cap \mathbb{O}| = 2$" "\n(2 lower + 8 upper)"),
    ]
    vals = [int(fano["8"]), int(fano["5"]), int(fano["2"])]
    bars = ax2.bar(cats, vals, width=0.54, color=[OI_BLUE, OI_VERM, OI_GREEN], edgecolor="white", linewidth=0.8, zorder=3)
    for bar, v in zip(bars, vals):
        ax2.text(bar.get_x() + bar.get_width() / 2, v + 0.8, f"{v}", ha="center", va="bottom", fontsize=10.5, fontweight="bold", color=OI_DARK)

    ax2.axhline(42, color=OI_DARK, linestyle="--", linewidth=1.0, alpha=0.6)
    ax2.text(1.0, 39.2, r"Total $= 7 + 28 + 7 = 42$ maximal 10D subspaces (0 of $\dim \geq 11$)",
             ha="center", fontsize=8.2, color=OI_DARK, fontweight="bold")
    ax2.text(1.0, 34.4, r"Matches: 42 bad affine 2-planes & 42 Box-Kite assessors ($H_4(4)=42$)",
             ha="center", fontsize=8.0, color=OI_GRAY)
    ax2.set_ylim(0, 45)
    ax2.set_ylabel("Count of 10D norm-multiplicative subspaces")
    ax2.set_title(r"Fano $7 + 28 + 7 = 42$ Duality over All $2^{16}$ Subspaces", fontweight="bold")
    ax2.grid(axis="y", color=OI_LIGHT, linewidth=0.7, zorder=0)

    save_fig(fig, "fig4_sedenion_triple_42_boxkites")


def make_fig5_bdi_and_symmetric_rupture() -> None:
    """Fig 5: Two-Blade vs BDI Ceiling Separation (n >= 5) & Symmetric Coordinate Rupture."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.5), gridspec_kw={"wspace": 0.26})

    ns = list(range(4, 10))
    twoblade = [(1 << (n - 1)) - 4 for n in ns]
    bdi = [(1 << n) - 4 * n + 4 for n in ns]

    ax1.plot(ns, bdi, marker="o", linewidth=2.1, color=OI_VERM, label=r"Biss–Dugger–Isaksen ceiling $2^n - 4n + 4$")
    ax1.plot(ns, twoblade, marker="s", linewidth=2.1, color=OI_BLUE, label=r"2-blade ceiling $2^{n-1} - 4$")
    ax1.fill_between(ns[1:], twoblade[1:], bdi[1:], color=OI_ORANGE, alpha=0.18, label=r"Strict higher-blade gap ($\forall\,n \geq 5$)")
    ax1.scatter([4], [4], s=85, color=OI_GREEN, zorder=6, edgecolor="white", linewidth=1.0)
    ax1.annotate(
        r"Equality at $n=4$" "\n" r"($4 = 4$ in $\mathbb{S}_{16}$)",
        xy=(4, 4),
        xytext=(4.04, 175),
        fontsize=8.1,
        color=OI_GREEN,
        fontweight="bold",
        arrowprops={"arrowstyle": "->", "color": OI_GREEN, "lw": 1.0},
    )
    ax1.annotate(
        r"Separation starts at $n=5$" "\n" r"($12 < 16$ in $\mathrm{CD}_5$)",
        xy=(5, 16),
        xytext=(5.30, 300),
        fontsize=8.2,
        color=OI_VERM,
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.20", "facecolor": "white", "edgecolor": OI_VERM, "alpha": 0.94},
        arrowprops={"arrowstyle": "->", "color": OI_VERM, "lw": 0.95},
    )
    ax1.set_xticks(ns)
    ax1.set_ylim(-15, 515)
    ax1.set_xlabel(r"Cayley–Dickson level $n$ ($\dim = 2^n$)")
    ax1.set_ylabel("Maximum annihilator dimension")
    ax1.set_title(r"Sharp Separation from the BDI Ceiling ($\forall\,n \geq 5$)", fontweight="bold")
    ax1.grid(True, color=OI_LIGHT, linewidth=0.7)
    ax1.legend(loc="upper left", fontsize=8.0, frameon=True, framealpha=0.95)

    # Right panel: Symmetric norm-multiplicative coordinate subspaces vs Yiu's real/integer sums-of-squares
    levels = [(r"$\mathrm{CD}_3$" "\n($8$D)"), (r"$\mathrm{CD}_4$" "\n($16$D)"), (r"$\mathrm{CD}_5$" "\n($32$D)"), (r"$\mathrm{CD}_6$" "\n($64$D)")]
    x = np.arange(len(levels))
    w = 0.28
    cd_sym_exact = [8, 10, 14, 16]  # Exact for n=3,4,5 (Lean T4a/T4e); witness lower bound 16 for n=6
    yiu_int_sym = [8, 10, 16, 20]   # Non-coordinate integral bilinear [r,r,2^n]: [16,16,32] (Yiu 1990), >=20 at 64
    hr_asym = [8, 9, 10, 11]        # Full-left CD clique omega(G_n^comp) = n+5

    b1 = ax2.bar(x - w, cd_sym_exact, width=w, color=OI_BLUE, label=r"$\mathrm{CD}_n$ symmetric coord $r_{\max}$ (Lean exact $n\leq 5$; lb $n=6$)", zorder=3)
    b2 = ax2.bar(x, yiu_int_sym, width=w, color=OI_VERM, label=r"Non-coord integral bilinear $[r,r,2^n]$ (Yiu 1990: $[16,16,32]$)", zorder=3)
    b3 = ax2.bar(x + w, hr_asym, width=w, color=OI_GREEN, label=r"Full-left $\mathrm{CD}_n$ clique $\omega(G_n^{\mathrm{comp}})=n+5$", zorder=3)

    for bars, col in [(b1, OI_BLUE), (b2, OI_VERM), (b3, OI_GREEN)]:
        for bar in bars:
            h = bar.get_height()
            ax2.text(bar.get_x() + bar.get_width() / 2, h + 0.35, f"{int(h)}", ha="center", va="bottom", fontsize=8.2, fontweight="bold", color=col)

    ax2.annotate(
        r"Lean T4e exact $r_{\max}(\mathrm{CD}_5)=14$" "\n" r"(strict $7{+}7$ balance; $280$ subspaces)",
        xy=(2 - w, 15.1),
        xytext=(-0.45, 18.2),
        fontsize=7.8,
        color=OI_DARK,
        fontweight="bold",
        bbox={"boxstyle": "round,pad=0.22", "facecolor": "white", "edgecolor": OI_DARK, "alpha": 0.96},
        arrowprops={"arrowstyle": "->", "color": OI_DARK, "lw": 0.95},
    )
    ax2.set_xticks(x)
    ax2.set_xticklabels(levels)
    ax2.set_ylabel("Subspace / form dimension $r$")
    ax2.set_ylim(0, 28.5)
    ax2.set_title(r"Symmetric Coordinate Subspaces vs. Bilinear $[r,r,2^n]$", fontweight="bold")
    ax2.grid(axis="y", color=OI_LIGHT, linewidth=0.7, zorder=0)
    ax2.legend(loc="upper left", fontsize=7.6, frameon=True, framealpha=0.95)

    save_fig(fig, "fig5_bdi_and_symmetric_rupture")


def make_social_preview_svg() -> None:
    MEDIA_DIR.mkdir(parents=True, exist_ok=True)
    svg = f"""<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1280 640" width="1280" height="640">
  <defs>
    <linearGradient id="bg" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#0B1220"/>
      <stop offset="55%" stop-color="#111C33"/>
      <stop offset="100%" stop-color="#0F2638"/>
    </linearGradient>
    <linearGradient id="accent" x1="0%" y1="0%" x2="100%" y2="0%">
      <stop offset="0%" stop-color="#56B4E9"/>
      <stop offset="50%" stop-color="#E69F00"/>
      <stop offset="100%" stop-color="#D55E00"/>
    </linearGradient>
  </defs>
  <rect width="1280" height="640" fill="url(#bg)"/>
  <rect x="0" y="0" width="1280" height="8" fill="url(#accent)"/>
  <g opacity="0.16" stroke="#56B4E9" stroke-width="1.2" fill="none">
    <circle cx="1040" cy="310" r="185"/>
    <circle cx="1040" cy="310" r="120"/>
    <polygon points="1040,125 1200,217 1200,402 1040,495 880,402 880,217"/>
    <line x1="1040" y1="125" x2="1040" y2="495"/>
    <line x1="880" y1="217" x2="1200" y2="402"/>
    <line x1="1200" y1="217" x2="880" y2="402"/>
  </g>
  <text x="72" y="96" fill="#56B4E9" font-family="ui-monospace, SFMono-Regular, Menlo, monospace" font-size="22" font-weight="700" letter-spacing="2">0TH-2026-019 · v{REPO_VERSION} · LEAN 4.35.0 (6 KERNELS) · RUST · ISO C11 · PYTHON</text>
  <text x="72" y="182" fill="#F8FAFC" font-family="Georgia, serif" font-size="50" font-weight="700">Cayley–Dickson Terrace Frontier</text>
  <text x="72" y="242" fill="#CBD5E1" font-family="system-ui, -apple-system, sans-serif" font-size="25">The Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation,</text>
  <text x="72" y="278" fill="#CBD5E1" font-family="system-ui, -apple-system, sans-serif" font-size="25">Pathion r_max = 14 (7+7 Rigidity) &amp; Dim-64 Coordinate Rupture</text>

  <g transform="translate(72, 336)">
    <rect x="0" y="0" width="256" height="122" rx="12" fill="#16233D" stroke="#56B4E9" stroke-width="1.5"/>
    <text x="20" y="38" fill="#56B4E9" font-family="ui-monospace, monospace" font-size="16" font-weight="700">MIDPOINT 42 LAW</text>
    <text x="20" y="78" fill="#FFFFFF" font-family="Georgia, serif" font-size="30" font-weight="700">42 · 2ⁿ⁻⁴</text>
    <text x="20" y="106" fill="#94A3B8" font-family="system-ui, sans-serif" font-size="14">Invariant across all 2ⁿ signatures</text>

    <rect x="278" y="0" width="256" height="122" rx="12" fill="#16233D" stroke="#D55E00" stroke-width="1.5"/>
    <text x="298" y="38" fill="#E69F00" font-family="ui-monospace, monospace" font-size="16" font-weight="700">PATHION EXACT T4e</text>
    <text x="298" y="78" fill="#FFFFFF" font-family="Georgia, serif" font-size="30" font-weight="700">r_max = 14 (7+7)</text>
    <text x="298" y="106" fill="#94A3B8" font-family="system-ui, sans-serif" font-size="14">Zero-MILP pure-kernel over 2³²</text>

    <rect x="556" y="0" width="256" height="122" rx="12" fill="#16233D" stroke="#009E73" stroke-width="1.5"/>
    <text x="576" y="38" fill="#009E73" font-family="ui-monospace, monospace" font-size="16" font-weight="700">ZERO-MATHLIB LEAN</text>
    <text x="576" y="78" fill="#FFFFFF" font-family="Georgia, serif" font-size="30" font-weight="700">23 / 23 Targets</text>
    <text x="576" y="106" fill="#94A3B8" font-family="system-ui, sans-serif" font-size="14">0 sorry · 6 independent kernels</text>
  </g>

  <text x="72" y="556" fill="#94A3B8" font-family="system-ui, -apple-system, sans-serif" font-size="20">Alexander Stephen Donahue · ORCID 0009-0006-8168-9648 · github.com/0thernes/cayley-dickson-terrace-frontier</text>
</svg>
"""
    (MEDIA_DIR / "social-preview.svg").write_text(svg, encoding="utf-8")


def make_social_preview_png() -> None:
    """Render an exact 1280x640 PNG GitHub Social Preview (< 1 MB, Build Standard A26)."""
    from matplotlib.patches import Circle, FancyBboxPatch, Polygon, Rectangle

    MEDIA_DIR.mkdir(parents=True, exist_ok=True)
    fig = plt.figure(figsize=(12.8, 6.4), dpi=100, facecolor="#0B1220")
    ax = fig.add_axes((0.0, 0.0, 1.0, 1.0), facecolor="#0B1220")
    ax.set_xlim(0, 1280)
    ax.set_ylim(0, 640)
    ax.axis("off")

    # Top Okabe-Ito gradient accent bar (3 segments)
    ax.add_patch(Rectangle((0, 632), 427, 8, facecolor=OI_SKY, edgecolor="none"))
    ax.add_patch(Rectangle((427, 632), 427, 8, facecolor=OI_ORANGE, edgecolor="none"))
    ax.add_patch(Rectangle((854, 632), 426, 8, facecolor=OI_VERM, edgecolor="none"))

    # Decorative K_{2,2,2} octahedral geometry on the right
    cx, cy = 1045.0, 325.0
    ax.add_patch(Circle((cx, cy), 178, fill=False, edgecolor=OI_SKY, alpha=0.18, linewidth=1.6))
    ax.add_patch(Circle((cx, cy), 115, fill=False, edgecolor=OI_SKY, alpha=0.14, linewidth=1.2))
    hex_pts = [(cx + 178 * math.cos(math.pi / 2 + k * math.pi / 3), cy + 178 * math.sin(math.pi / 2 + k * math.pi / 3)) for k in range(6)]
    ax.add_patch(Polygon(hex_pts, closed=True, fill=False, edgecolor=OI_SKY, alpha=0.22, linewidth=1.4))
    for a in range(6):
        for b in range(a + 1, 6):
            if (b - a) != 3:
                ax.plot([hex_pts[a][0], hex_pts[b][0]], [hex_pts[a][1], hex_pts[b][1]], color=OI_SKY, alpha=0.16, linewidth=1.1)
    for px, py in hex_pts:
        ax.add_patch(Circle((px, py), 6.5, facecolor=OI_ORANGE, edgecolor="#0B1220", linewidth=1.2, alpha=0.55))

    # Header badge & title
    ax.text(
        72, 548,
        f"0TH-2026-019  ·  v{REPO_VERSION}  ·  LEAN 4.35.0 (6 KERNELS)  ·  RUST  ·  ISO C11  ·  PYTHON",
        color=OI_SKY, fontsize=14.5, fontweight="bold", family="monospace",
    )
    ax.text(72, 466, "Cayley–Dickson Terrace Frontier", color="#F8FAFC", fontsize=37, fontweight="bold", family="serif")
    ax.text(
        72, 412,
        "The Dyadic-Palindromic Terrace Law, Nilpotent Mirror Conservation,",
        color="#CBD5E1", fontsize=18.5, family="sans-serif",
    )
    ax.text(
        72, 378,
        "Pathion r_max = 14 (7+7 Rigidity) & Dim-64 Coordinate Rupture",
        color="#CBD5E1", fontsize=18.5, family="sans-serif",
    )

    # Three KPI cards (generous padding so every glyph stays cleanly inside its rounded card)
    cards = [
        (72, OI_SKY, "MIDPOINT 42 LAW", r"$42 \cdot 2^{n-4}$", r"Invariant across all $2^n$ signatures"),
        (372, OI_VERM, "PATHION EXACT T4e", r"$r_{\max} = 14$ (7+7)", r"Zero-MILP pure-kernel over $2^{32}$"),
        (672, OI_GREEN, "ZERO-MATHLIB LEAN", "23 / 23 Targets", "0 sorry · 6 independent kernels"),
    ]
    for x0, border_col, ktitle, kval, ksub in cards:
        box = FancyBboxPatch(
            (x0, 178), 278, 134,
            boxstyle="round,pad=0.0,rounding_size=12",
            facecolor="#16233D", edgecolor=border_col, linewidth=1.8,
        )
        ax.add_patch(box)
        ax.text(x0 + 16, 282, ktitle, color=border_col, fontsize=11.0, fontweight="bold", family="monospace")
        ax.text(x0 + 16, 234, kval, color="#FFFFFF", fontsize=19.5, fontweight="bold", family="serif")
        ax.text(x0 + 16, 198, ksub, color="#94A3B8", fontsize=9.8, family="sans-serif")

    # Footer
    ax.text(
        72, 78,
        "Alexander Stephen Donahue  ·  ORCID 0009-0006-8168-9648  ·  github.com/0thernes/cayley-dickson-terrace-frontier",
        color="#94A3B8", fontsize=14, family="sans-serif",
    )

    fig.savefig(MEDIA_DIR / "social-preview.png", dpi=100, facecolor="#0B1220", bbox_inches=None, pad_inches=0)
    plt.close(fig)


def main() -> None:
    setup_style()
    terraces = load_json("cd4_to_cd8_terraces.json")
    split_data = load_json("split_phases_cd4_to_cd8.json")
    sedenion_data = load_json("sedenion_box_kites_and_42_subspaces.json")
    hr_data = load_json("hurwitz_rupture_table.json")

    make_fig1_terrace_cathedral(terraces)
    make_fig2_mirror_conservation(split_data)
    make_fig3_hurwitz_rupture(hr_data)
    make_fig4_sedenion_triple_42(sedenion_data)
    make_fig5_bdi_and_symmetric_rupture()
    make_social_preview_svg()
    make_social_preview_png()
    print("Generated all 5 figures (PDF+PNG) and 1280x640 social-preview.{svg,png} successfully.")


if __name__ == "__main__":
    main()
