"""Generate 3 publication-quality PNG figures for CNOT-HARD-CERT-1.0."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from src.cnot_hardness_verifier import build_lemma2_reduction, exact_min_vertex_cover


def main() -> None:
    out = Path(__file__).resolve().parent.parent / "paper" / "figures"
    out.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.size": 10,
        "axes.titlesize": 11,
        "axes.labelsize": 10,
        "legend.fontsize": 8.5,
        "figure.dpi": 300,
    })

    # Figure 1: Exact XOR vs CNOT Distance Sandwich on Linear Oracles B_G (Lemma 4)
    graphs = [
        (r"$P_4$", 4, [(0, 1), (1, 2), (2, 3)]),
        (r"$C_4+e$", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)]),
        (r"$K_4$", 4, [(i, j) for i in range(4) for j in range(i + 1, 4)]),
        (r"$G(K_2)$", *build_lemma2_reduction(2, [(0, 1)])[:2]),
    ]
    labels = [g[0] for g in graphs]
    d_fg = []
    d_bg_xor = []
    d_bg_cnot = []
    for _, n, edges in graphs:
        tau, _ = exact_min_vertex_cover(n, edges)
        m = len(edges)
        d_fg.append(m + tau)
        d_bg_xor.append(2 * m + tau)
        d_bg_cnot.append(2 * m + tau + 1)

    x = list(range(len(labels)))
    w = 0.26
    fig, ax = plt.subplots(figsize=(6.4, 3.7))
    ax.bar([i - w for i in x], d_fg, width=w, color="#0284c7", label=r"$D_{\mathrm{XOR}}(F_G) = m + \tau(G)$")
    ax.bar(x, d_bg_xor, width=w, color="#059669", label=r"$D_{\mathrm{XOR}}(B_G) = 2m + \tau(G)$")
    ax.bar([i + w for i in x], d_bg_cnot, width=w, color="#b91c1c", label=r"Synthesized CNOT $= 2m + \tau(G) + 1$")
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.set_ylabel("Exact gate count")
    ax.set_title("Lemma 3–4 Gate Counts: Edge Forms $F_G$ vs. Linear Oracles $B_G$")
    ax.grid(True, axis="y", linestyle=":", alpha=0.5)
    ax.legend(loc="upper left", frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig1_xor_cnot_oracle_counts.png", dpi=300)
    plt.close(fig)

    # Figure 2: Lemma 2 Promise Vertex Cover Reduction Scaling tau(G) = 2*tau(H) + 2n
    hs = [
        (r"$K_2$", 2, [(0, 1)]),
        (r"$P_3$", 3, [(0, 1), (1, 2)]),
        (r"$K_3$", 3, [(0, 1), (1, 2), (0, 2)]),
        (r"$K_{1,3}$", 4, [(0, 1), (0, 2), (0, 3)]),
        (r"$C_4$", 4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
    ]
    h_lbls = [h[0] for h in hs]
    tau_hs = []
    tau_gs = []
    clique_pen = []
    for _, n, e in hs:
        th, _ = exact_min_vertex_cover(n, e)
        tau_hs.append(th)
        tau_gs.append(2 * th + 2 * n)
        clique_pen.append(4 * n - 1)

    xs = list(range(len(hs)))
    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    ax.plot(xs, clique_pen, "^--", color="#9333ea", linewidth=1.8, markersize=6, label=r"Missed-clique penalty $4n - 1$")
    ax.plot(xs, tau_gs, "o-", color="#b91c1c", linewidth=2.2, markersize=6, label=r"Exact even $\tau(G) = 2\tau(H) + 2n$")
    ax.plot(xs, tau_hs, "s:", color="#0284c7", linewidth=1.8, markersize=5.5, label=r"Source $\tau(H)$")
    ax.set_xticks(xs)
    ax.set_xticklabels(h_lbls)
    ax.set_ylabel("Vertex cover cardinality")
    ax.set_title(r"Lemma 2 Promise Reduction Dominance: $2\tau(H)+2n < 4n-1$")
    ax.grid(True, linestyle=":", alpha=0.5)
    ax.legend(loc="upper left", frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig2_lemma2_promise_reduction.png", dpi=300)
    plt.close(fig)

    # Figure 3: Theorem 5 Parity Decision Gap Separating YES vs NO Instances
    ks = [0, 1, 2, 3, 4, 5, 6, 7]
    m_ex = 24  # G(K_2) has m=24, tau=6 (even)
    tau_ex = 6
    K_vals = [2 * m_ex + (k if k % 2 == 0 else k - 1) + 1 for k in ks]
    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    ax.step(ks, K_vals, where="mid", color="#1d4ed8", linewidth=2.2, label=r"Decision budget $K(k) = 2m + k' + 1$")
    ax.axhspan(2 * m_ex + tau_ex, 2 * m_ex + tau_ex + 1, color="#fca5a5", alpha=0.55,
               label=r"$D_{\mathrm{CNOT}}(B_G) \in [2m+\tau, 2m+\tau+1]$ ($[54, 55]$)")
    ax.axvline(5.5, color="#b91c1c", linestyle="--", linewidth=1.5, label=r"Exact YES/NO split at $k = \tau(G) = 6$")
    ax.set_xlabel(r"Vertex cover query budget $k$ on $G(K_2)$ ($m=24, \tau=6$)")
    ax.set_ylabel("CNOT gate budget $K$")
    ax.set_title(r"Theorem 5 Parity-Rounding Separation ($\tau \leq k \Leftrightarrow D_{\mathrm{CNOT}}(B_G) \leq K$)")
    ax.set_xticks(ks)
    ax.grid(True, linestyle=":", alpha=0.5)
    ax.legend(loc="upper left", fontsize=8.0, frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig3_theorem5_parity_gap.png", dpi=300)
    plt.close(fig)

    print("Generated 3 figures in", out)


if __name__ == "__main__":
    main()
