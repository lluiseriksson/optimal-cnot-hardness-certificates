"""Generate 16 canonical exact F_2 certificates (C01-C16) for CNOT-HARD-CERT-1.0."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from src.cnot_hardness_verifier import (
    SCHEMA,
    build_lemma2_reduction,
    exact_min_vertex_cover,
    verify_certificate,
)


def _optimal_xor_edge_forms(n: int, edges: List[Tuple[int, int]]) -> List[List[int]]:
    _, vc = exact_min_vertex_cover(n, edges)
    gates: List[List[int]] = []
    t_wire: Dict[int, int] = {}
    for v in vc:
        t_wire[v] = (n + 1) + len(gates)
        gates.append([0, v + 1])
    vc_set = set(vc)
    for u, v in edges:
        piv, oth = (u, v) if u in vc_set else (v, u)
        gates.append([t_wire[piv], oth + 1])
    return gates


def _build_lemma4_ops(n: int, edges: List[Tuple[int, int]], ham_vc: List[int]) -> List[List[Any]]:
    vc_set = set(ham_vc)
    edge_idx = {e: n + 1 + idx for idx, e in enumerate(edges)}
    path_edges = {(min(a, b), max(a, b)) for a, b in zip(ham_vc, ham_vc[1:])}
    assigned: Dict[int, List[Tuple[Tuple[int, int], int]]] = {v: [] for v in ham_vc}
    for e in edges:
        if e in path_edges:
            continue
        u, v = e
        if u in vc_set:
            assigned[u].append((e, v))
        else:
            assigned[v].append((e, u))
    ops: List[List[Any]] = []
    ops.append(["CNOT", 0, ham_vc[0] + 1])
    for i, si in enumerate(ham_vc):
        for e, oth in assigned[si]:
            wy = edge_idx[e]
            ops.append(["CNOT", wy, 0])
            ops.append(["CNOT", wy, oth + 1])
        if i + 1 < len(ham_vc):
            sip1 = ham_vc[i + 1]
            pe = (min(si, sip1), max(si, sip1))
            wy = edge_idx[pe]
            ops.append(["CNOT", 0, sip1 + 1])
            ops.append(["CNOT", wy, 0])
            ops.append(["CNOT", 0, si + 1])
    ops.append(["CNOT", 0, ham_vc[-1] + 1])
    return ops


def generate_all(out_dir: Path) -> List[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)

    # Benchmark graphs H for Mode 1 (Lemma 2 reduction H -> G = H1 U H2 U K_{2n})
    h_p3 = (3, [(0, 1), (1, 2)])             # tau=1 -> tau(G)=8, n_G=12
    h_c4 = (4, [(0, 1), (1, 2), (2, 3), (3, 0)])  # tau=2 -> tau(G)=12, n_G=16
    h_k3 = (3, [(0, 1), (1, 2), (0, 2)])     # tau=2 -> tau(G)=10, n_G=12
    h_star4 = (4, [(0, 1), (0, 2), (0, 3)])  # tau=1 -> tau(G)=10, n_G=16

    # Benchmark graphs for Mode 2 (Lemma 3 gate elimination)
    g_p4 = (4, [(0, 1), (1, 2), (2, 3)])
    g_c5 = (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])
    g_k4 = (4, [(i, j) for i in range(4) for j in range(i + 1, 4)])
    # A non-optimal XOR circuit on P_4 that triggers Case (b) x_u + x_w merges!
    # Wires: 0=z, 1=x0, 2=x1, 3=x2, 4=x3
    # g0=x0+x1 (5), g1=z+g0 (6) [e01], g2=x1+x2 (7), g3=z+g2 (8) [e12], g4=x2+x3 (9), g5=z+g4 (10) [e23]
    p4_case_b_gates = [[1, 2], [0, 5], [2, 3], [0, 7], [3, 4], [0, 9]]

    # Benchmark graphs with Hamiltonian minimum vertex covers for Mode 3 (Lemma 4)
    # P_4: min VC = [1, 2] (adjacent -> Ham path of length 2!)
    # C_4 + diagonal (0,2): min VC = [0, 2] (adjacent!)
    g_c4_diag = (4, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)])
    # K_4: min VC = [0, 1, 2] (clique -> Ham path [0,1,2]!)
    # Lemma 2 image of K_2 (n_H=2, edges=[(0,1)] -> n_G=8, tau(G)=6, Ham path built by Lemma 2!)
    n_l2_k2, e_l2_k2, ham_l2_k2 = build_lemma2_reduction(2, [(0, 1)])

    # Mode 4 graphs (even tau(G) + Hamiltonian min VC):
    # P_4 (tau=2, m=3, d=8): K for k=2 -> K=9 (YES), K for k=1 -> k'=0 -> K=7 (NO)
    p4_ops_base = _build_lemma4_ops(4, g_p4[1], [1, 2])
    # Augmented circuit implementing B_G on wires 0..7 with 2 clean ancillas (wires 8, 9 = 0):
    # - ["CNOT", 1, 9]: zero-control no-op (control=ancilla 9 is 0 -> dropped in XOR translation!)
    # - ["CNOT", 8, 0]: zero-target copy (target=ancilla 8 is 0 -> free copy of z in XOR translation!)
    # - Run Lemma 4 using ancilla 8 as the working z-copy (leaves wire 0 untouched as z,
    #   and outputs all B_G rows on wires 0..7 with translated XOR count == 9 <= K=9!)
    p4_ops_aug1 = (
        [["CNOT", 1, 9], ["CNOT", 8, 0], ["SWAP", 0, 8]]
        + p4_ops_base
        + [["SWAP", 0, 8]]
    )
    # Pure free-SWAP augmented circuit on C_4+diag (n=4, m=5, tau=2, d=10): swaps wires (1, 3) and back around Lemma 4 circuit
    c4d_ops_base = _build_lemma4_ops(4, g_c4_diag[1], [0, 2])
    c4d_ops_swap = [["SWAP", 1, 3]] + [
        ["CNOT", (3 if g[1] == 1 else (1 if g[1] == 3 else g[1])),
                 (3 if g[2] == 1 else (1 if g[2] == 3 else g[2]))] for g in c4d_ops_base
    ] + [["SWAP", 1, 3]]

    # Lemma 2 image of K_2 (n=8, m=24, tau=6 even): build its exact Lemma 4 circuit
    l2_k2_ops = _build_lemma4_ops(n_l2_k2, e_l2_k2, ham_l2_k2)

    certs: List[Dict[str, Any]] = [
        # Mode 1: Lemma 2 promise VC reduction H -> G = H1 U H2 U K_{2n}
        {
            "schema": SCHEMA, "id": "C01", "mode": "promise_vc_reduction_lemma2",
            "description": "Lemma 2 reduction on H=P_3 (n=3, tau=1) -> G (n=12, tau=8 even, Ham path verified)",
            "graph_H": {"n": h_p3[0], "edges": [list(e) for e in h_p3[1]]},
            "claimed_tau_H": 1, "claimed_tau_G": 8,
        },
        {
            "schema": SCHEMA, "id": "C02", "mode": "promise_vc_reduction_lemma2",
            "description": "Lemma 2 reduction on H=K_3 (n=3, tau=2) -> G (n=12, tau=10 even, Ham path verified)",
            "graph_H": {"n": h_k3[0], "edges": [list(e) for e in h_k3[1]]},
            "claimed_tau_H": 2, "claimed_tau_G": 10,
        },
        {
            "schema": SCHEMA, "id": "C03", "mode": "promise_vc_reduction_lemma2",
            "description": "Lemma 2 reduction on H=C_4 (n=4, tau=2) -> G (n=16, tau=12 even, independent branch-and-bound)",
            "graph_H": {"n": h_c4[0], "edges": [list(e) for e in h_c4[1]]},
            "claimed_tau_H": 2, "claimed_tau_G": 12,
        },
        {
            "schema": SCHEMA, "id": "C04", "mode": "promise_vc_reduction_lemma2",
            "description": "Lemma 2 reduction on H=K_{1,3} (n=4, tau=1) -> G (n=16, tau=10 even, Ham path verified)",
            "graph_H": {"n": h_star4[0], "edges": [list(e) for e in h_star4[1]]},
            "claimed_tau_H": 1, "claimed_tau_G": 10,
        },
        # Mode 2: Lemma 3 localized gate elimination & optimal XOR circuit
        {
            "schema": SCHEMA, "id": "C05", "mode": "gate_elimination_lemma3",
            "description": "Optimal 5-gate XOR circuit on P_4 (m=3, tau=2): full Case (a) gate elimination",
            "graph": {"n": g_p4[0], "edges": [list(e) for e in g_p4[1]]},
            "xor_gates": _optimal_xor_edge_forms(*g_p4),
            "claimed_tau": 2, "claimed_DXOR_FG": 5,
        },
        {
            "schema": SCHEMA, "id": "C06", "mode": "gate_elimination_lemma3",
            "description": "Non-optimal 6-gate XOR circuit on P_4 exercising Case (b) vertex-merge projections x_u -> x_w",
            "graph": {"n": g_p4[0], "edges": [list(e) for e in g_p4[1]]},
            "xor_gates": p4_case_b_gates,
            "claimed_tau": 2, "claimed_DXOR_FG": 5,
        },
        {
            "schema": SCHEMA, "id": "C07", "mode": "gate_elimination_lemma3",
            "description": "Optimal 8-gate XOR circuit on C_5 (m=5, tau=3): exact telescoping gate elimination",
            "graph": {"n": g_c5[0], "edges": [list(e) for e in g_c5[1]]},
            "xor_gates": _optimal_xor_edge_forms(*g_c5),
            "claimed_tau": 3, "claimed_DXOR_FG": 8,
        },
        {
            "schema": SCHEMA, "id": "C08", "mode": "gate_elimination_lemma3",
            "description": "Optimal 9-gate XOR circuit on K_4 (m=6, tau=3): exact telescoping gate elimination",
            "graph": {"n": g_k4[0], "edges": [list(e) for e in g_k4[1]]},
            "xor_gates": _optimal_xor_edge_forms(*g_k4),
            "claimed_tau": 3, "claimed_DXOR_FG": 9,
        },
        # Mode 3: Lemma 4 linear oracle involution B_G^2=I + Hamiltonian-path CNOT synthesis over F_2
        {
            "schema": SCHEMA, "id": "C09", "mode": "linear_oracle_cnot_lemma4",
            "description": "P_4 linear oracle B_G in GL(8,2): B_G^2=I and exact 9-gate (2m+tau+1) CNOT synthesis",
            "graph": {"n": g_p4[0], "edges": [list(e) for e in g_p4[1]]},
            "hamiltonian_min_vc": [1, 2], "claimed_cnot_size": 9, "claimed_DXOR_BG": 8,
        },
        {
            "schema": SCHEMA, "id": "C10", "mode": "linear_oracle_cnot_lemma4",
            "description": "C_4+diag linear oracle B_G in GL(10,2): B_G^2=I and exact 13-gate CNOT synthesis",
            "graph": {"n": g_c4_diag[0], "edges": [list(e) for e in g_c4_diag[1]]},
            "hamiltonian_min_vc": [0, 2], "claimed_cnot_size": 13, "claimed_DXOR_BG": 12,
        },
        {
            "schema": SCHEMA, "id": "C11", "mode": "linear_oracle_cnot_lemma4",
            "description": "K_4 linear oracle B_G in GL(11,2): B_G^2=I and exact 16-gate CNOT synthesis",
            "graph": {"n": g_k4[0], "edges": [list(e) for e in g_k4[1]]},
            "hamiltonian_min_vc": [0, 1, 2], "claimed_cnot_size": 16, "claimed_DXOR_BG": 15,
        },
        {
            "schema": SCHEMA, "id": "C12", "mode": "linear_oracle_cnot_lemma4",
            "description": "Lemma 2 reduced graph G(K_2) (n=8, m=24, tau=6): B_G in GL(33,2), B_G^2=I, exact 55-gate CNOT circuit",
            "graph": {"n": n_l2_k2, "edges": [list(e) for e in e_l2_k2]},
            "hamiltonian_min_vc": ham_l2_k2, "claimed_cnot_size": 55, "claimed_DXOR_BG": 54,
        },
        # Mode 4: Theorem 5 parity reduction + free-SWAP/free-ancilla syntactic XOR translation
        {
            "schema": SCHEMA, "id": "C13", "mode": "free_resources_and_parity_thm5",
            "description": "Theorem 5 YES instance on P_4 (tau=2, k=2 -> K=9) exercising zero-control no-op, zero-target copy, and free SWAP translation",
            "graph": {"n": g_p4[0], "edges": [list(e) for e in g_p4[1]]},
            "vc_budget_k": 2, "claimed_yes_instance": True,
            "n_clean_ancillas": 2, "augmented_circuit_ops": p4_ops_aug1,
        },
        {
            "schema": SCHEMA, "id": "C14", "mode": "free_resources_and_parity_thm5",
            "description": "Theorem 5 NO instance with odd budget rounding on P_4 (tau=2, k=1 -> k'=0, K=7)",
            "graph": {"n": g_p4[0], "edges": [list(e) for e in g_p4[1]]},
            "vc_budget_k": 1, "claimed_yes_instance": False,
            "n_clean_ancillas": 0, "augmented_circuit_ops": p4_ops_base,
        },
        {
            "schema": SCHEMA, "id": "C15", "mode": "free_resources_and_parity_thm5",
            "description": "Theorem 5 YES instance on C_4+diag (tau=2, k=3 -> k'=2, K=13) with free SWAP translation",
            "graph": {"n": g_c4_diag[0], "edges": [list(e) for e in g_c4_diag[1]]},
            "vc_budget_k": 3, "claimed_yes_instance": True,
            "n_clean_ancillas": 0, "augmented_circuit_ops": c4d_ops_swap,
        },
        {
            "schema": SCHEMA, "id": "C16", "mode": "free_resources_and_parity_thm5",
            "description": "Theorem 5 NO instance on Lemma 2 image G(K_2) (m=24, tau=6, k=5 -> k'=4, K=53 < 54)",
            "graph": {"n": n_l2_k2, "edges": [list(e) for e in e_l2_k2]},
            "vc_budget_k": 5, "claimed_yes_instance": False,
            "n_clean_ancillas": 0, "augmented_circuit_ops": l2_k2_ops,
        },
    ]

    written: List[Path] = []
    for cert in certs:
        verify_certificate(cert)
        p = out_dir / f"{cert['id']}.json"
        p.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        written.append(p)
    return written


if __name__ == "__main__":
    root = Path(__file__).resolve().parent.parent
    files = generate_all(root / "certificates")
    print(f"Generated and verified {len(files)} certificates in {root / 'certificates'}.")
