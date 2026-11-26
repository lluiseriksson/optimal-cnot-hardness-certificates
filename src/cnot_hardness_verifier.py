r"""Zero-float exact F_2 verifier for Optimal CNOT Circuit NP-Completeness.

Certifies Lemma 2 promise vertex-cover reduction (G = H_1 U H_2 U K_{2n},
tau(G) = 2*tau(H) + 2n even, explicit Hamiltonian path on G[S]), Lemma 3
localized gate elimination <C_0, G_0> -> ... -> <C_q, G_q> on XOR edge forms
F_G = {z + x_u + x_v}, Lemma 4 linear-oracle involution B_G^2 = I and exact
(2m + tau(G) + 1)-gate Hamiltonian-path CNOT synthesis over F_2, and Theorem 5
parity reduction + free-SWAP/free-ancilla syntactic XOR translation from
Andreas Pavlogiannis (arXiv:2611.34138v1, Nov 2026).

Schema: CNOT-HARD-CERT-1.0
Zero floats: uses strictly `int` bitmasks over F_2 (no `float`, no `math`).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Sequence, Set, Tuple

SCHEMA = "CNOT-HARD-CERT-1.0"


def _req_int(obj: Dict[str, Any], key: str) -> int:
    if key not in obj:
        raise ValueError(f"missing integer field '{key}'")
    v = obj[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(f"field '{key}' must be exact int")
    return v


def _req_bool(obj: Dict[str, Any], key: str) -> bool:
    if key not in obj:
        raise ValueError(f"missing boolean field '{key}'")
    v = obj[key]
    if not isinstance(v, bool):
        raise ValueError(f"field '{key}' must be bool")
    return v


def _req_list(obj: Dict[str, Any], key: str) -> List[Any]:
    if key not in obj:
        raise ValueError(f"missing list field '{key}'")
    v = obj[key]
    if not isinstance(v, list):
        raise ValueError(f"field '{key}' must be list")
    return v


def parse_graph(spec: Dict[str, Any]) -> Tuple[int, List[Tuple[int, int]]]:
    if not isinstance(spec, dict):
        raise ValueError("graph must be JSON object")
    n = _req_int(spec, "n")
    raw = _req_list(spec, "edges")
    if n < 1:
        raise ValueError("graph requires n >= 1")
    seen: Set[Tuple[int, int]] = set()
    edges: List[Tuple[int, int]] = []
    for e in raw:
        if not (isinstance(e, list) and len(e) == 2):
            raise ValueError("edge must be [u, v]")
        u, v = _req_int({"x": e[0]}, "x"), _req_int({"x": e[1]}, "x")
        if not (0 <= u < n and 0 <= v < n and u != v):
            raise ValueError("invalid edge endpoints")
        pair = (min(u, v), max(u, v))
        if pair in seen:
            raise ValueError("duplicate edge")
        seen.add(pair)
        edges.append(pair)
    edges.sort()
    return n, edges


def exact_min_vertex_cover(n: int, edges: List[Tuple[int, int]]) -> Tuple[int, List[int]]:
    """Exact minimum vertex cover via branch-and-bound on edge endpoints."""
    best: List[int] = list(range(n))

    def bt(rem_edges: List[Tuple[int, int]], chosen: List[int]) -> None:
        nonlocal best
        if len(chosen) >= len(best):
            return
        if not rem_edges:
            best = chosen[:]
            return
        u, v = rem_edges[0]
        # Branch 1: pick u
        e_u = [(a, b) for (a, b) in rem_edges if a != u and b != u]
        chosen.append(u)
        bt(e_u, chosen)
        chosen.pop()
        # Branch 2: pick v
        e_v = [(a, b) for (a, b) in rem_edges if a != v and b != v]
        chosen.append(v)
        bt(e_v, chosen)
        chosen.pop()

    bt(edges, [])
    return len(best), sorted(best)


def build_lemma2_reduction(n_h: int, edges_h: List[Tuple[int, int]]) -> Tuple[int, List[Tuple[int, int]], List[int]]:
    """Construct G = H1 U H2 U K_{2n} with every vertex of K_{2n} adjacent to every vertex of H1 U H2."""
    n_g = 4 * n_h
    edges_g: Set[Tuple[int, int]] = set()
    # H1 on 0..n_h-1, H2 on n_h..2*n_h-1, U = K_{2n} on 2*n_h..4*n_h-1
    for u, v in edges_h:
        edges_g.add((min(u, v), max(u, v)))
        edges_g.add((min(u + n_h, v + n_h), max(u + n_h, v + n_h)))
    u_start = 2 * n_h
    for i in range(u_start, n_g):
        for j in range(i + 1, n_g):
            edges_g.add((i, j))
        for h_v in range(u_start):
            edges_g.add((h_v, i))
    tau_h, s_h = exact_min_vertex_cover(n_h, edges_h)
    s12 = s_h + [v + n_h for v in s_h]
    t = len(s12)
    ham_path: List[int] = []
    for idx in range(t):
        ham_path.append(s12[idx])
        ham_path.append(u_start + idx)
    for idx in range(t, 2 * n_h):
        ham_path.append(u_start + idx)
    return n_g, sorted(edges_g), ham_path


def _is_valid_ham_path(edges_set: Set[Tuple[int, int]], path: List[int]) -> bool:
    if len(path) != len(set(path)):
        return False
    for a, b in zip(path, path[1:]):
        if (min(a, b), max(a, b)) not in edges_set:
            return False
    return True


def verify_promise_vc_reduction_lemma2(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Exact Lemma 2 reduction H -> G = H1 U H2 U K_{2n}, even tau(G), Hamiltonian path."""
    n_h, edges_h = parse_graph(cert["graph_H"])
    claimed_tau_h = _req_int(cert, "claimed_tau_H")
    claimed_tau_g = _req_int(cert, "claimed_tau_G")
    tau_h, _ = exact_min_vertex_cover(n_h, edges_h)
    if tau_h != claimed_tau_h:
        raise ValueError(f"tau(H) mismatch: exact {tau_h}, claimed {claimed_tau_h}")
    n_g, edges_g, ham_path = build_lemma2_reduction(n_h, edges_h)
    expected_tau_g = 2 * tau_h + 2 * n_h
    if expected_tau_g != claimed_tau_g or expected_tau_g % 2 != 0:
        raise ValueError(f"tau(G) mismatch: exact {expected_tau_g}, claimed {claimed_tau_g}")
    # For small H (n_h <= 4 => n_g <= 16), independently verify exact tau(G) via branch-and-bound!
    if n_g <= 16:
        exact_tau_g, _ = exact_min_vertex_cover(n_g, edges_g)
        if exact_tau_g != expected_tau_g:
            raise ValueError(f"independent branch-and-bound tau(G)={exact_tau_g} != {expected_tau_g}")
    # Verify ham_path is a valid vertex cover of G and induces a Hamiltonian path in G[S]
    s_set = set(ham_path)
    if len(s_set) != expected_tau_g:
        raise ValueError("Hamiltonian cover size mismatch")
    for u, v in edges_g:
        if u not in s_set and v not in s_set:
            raise ValueError(f"edge ({u},{v}) uncovered by S")
    if not _is_valid_ham_path(set(edges_g), ham_path):
        raise ValueError("constructed Hamiltonian path is invalid in G[S]")
    return {
        "mode": "promise_vc_reduction_lemma2",
        "n_H": n_h,
        "tau_H": tau_h,
        "n_G": n_g,
        "tau_G": expected_tau_g,
    }


def _eval_xor_circuit(n_inputs: int, gates: List[Tuple[int, int]]) -> List[int]:
    """Evaluate XOR circuit over F_2 bitmasks; inputs are 0..n_inputs-1, gate l is n_inputs+l."""
    vals = [1 << i for i in range(n_inputs)]
    for idx, (a, b) in enumerate(gates):
        cur = n_inputs + idx
        if not (0 <= a < cur and 0 <= b < cur):
            raise ValueError(f"gate {idx} references out-of-range wire ({a}, {b})")
        vals.append(vals[a] ^ vals[b])
    return vals


def _simplify_projected_xor_circuit(
    active_inputs: List[int],
    gates: List[Tuple[int, int]],
    proj_from: int,
    proj_to: int,
) -> Tuple[List[int], List[Tuple[int, int]], int]:
    """Syntactically project input wire proj_from -> proj_to and delete all redundant gates."""
    # Evaluate original gates under the projection to find exact simplified DAG
    # Map old wire id -> new wire id (or -1 for constant 0)
    new_inputs = [w for w in active_inputs if w != proj_from]
    # Represent expressions as bitmasks over new_inputs positions
    pos_map = {w: i for i, w in enumerate(new_inputs)}
    wire_expr: Dict[int, int] = {}
    for w in new_inputs:
        wire_expr[w] = 1 << pos_map[w]
    wire_expr[proj_from] = wire_expr[proj_to]

    # Map expression bitmask -> earliest wire index in new circuit (-1 for 0)
    expr_to_new: Dict[int, int] = {0: -1}
    for i, w in enumerate(new_inputs):
        expr_to_new[1 << i] = i

    new_gates: List[Tuple[int, int]] = []
    # Re-index old gate ids assuming old wires were 0..len(active_inputs)-1 + gates
    n_old_in = len(active_inputs)
    old_to_new: Dict[int, int] = {}
    for old_idx, w in enumerate(active_inputs):
        if w == proj_from:
            old_to_new[old_idx] = pos_map[proj_to]
        else:
            old_to_new[old_idx] = pos_map[w]

    # Compute masks for every old wire
    old_masks: List[int] = [wire_expr[w] for w in active_inputs]
    deleted = 0
    for g_idx, (a, b) in enumerate(gates):
        m = old_masks[a] ^ old_masks[b]
        old_masks.append(m)
        old_wire = n_old_in + g_idx
        if m in expr_to_new:
            old_to_new[old_wire] = expr_to_new[m]
            deleted += 1
        else:
            na, nb = old_to_new[a], old_to_new[b]
            if na == -1 or nb == -1:
                raise ValueError("unexpected zero operand in non-redundant gate")
            new_wire = len(new_inputs) + len(new_gates)
            new_gates.append((na, nb))
            expr_to_new[m] = new_wire
            old_to_new[old_wire] = new_wire
    return new_inputs, new_gates, deleted


def verify_gate_elimination_lemma3(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Execute Pavlogiannis's exact gate-elimination algorithm & optimal XOR upper bound."""
    n, edges = parse_graph(cert["graph"])
    raw_gates = _req_list(cert, "xor_gates")
    claimed_tau = _req_int(cert, "claimed_tau")
    claimed_dxor = _req_int(cert, "claimed_DXOR_FG")

    # Input wire convention: wire 0 = z, wire (u + 1) = x_u for u in 0..n-1
    gates: List[Tuple[int, int]] = []
    for g in raw_gates:
        if not (isinstance(g, list) and len(g) == 2):
            raise ValueError("XOR gate must be [a, b]")
        gates.append((_req_int({"x": g[0]}, "x"), _req_int({"x": g[1]}, "x")))

    tau, min_vc = exact_min_vertex_cover(n, edges)
    if tau != claimed_tau:
        raise ValueError(f"tau(G) mismatch: exact {tau}, claimed {claimed_tau}")
    if len(edges) + tau != claimed_dxor:
        raise ValueError(f"DXOR(F_G) mismatch: exact {len(edges) + tau}, claimed {claimed_dxor}")

    # 1. Verify supplied XOR circuit implements every edge form z + x_u + x_v
    vals = _eval_xor_circuit(n + 1, gates)
    val_set = set(vals)
    for u, v in edges:
        target = 1 | (1 << (u + 1)) | (1 << (v + 1))
        if target not in val_set:
            raise ValueError(f"supplied XOR circuit fails to compute edge form for ({u},{v})")

    # 2. Run Pavlogiannis's exact gate-elimination sequence <C_0, G_0> -> ... -> <C_q, G_q>
    active_inputs = list(range(n + 1))  # 0 is z, 1..n are original vertex labels
    cur_gates = gates[:]
    cur_edges = edges[:]
    extracted_vc: List[int] = []
    steps = 0
    while cur_edges:
        cur_vals = _eval_xor_circuit(len(active_inputs), cur_gates)
        # Find first gate whose two operands evaluate to distinct inputs (at least one is some x_u)
        found = None
        for g_idx, (a, b) in enumerate(cur_gates):
            ma, mb = cur_vals[a], cur_vals[b]
            if ma.bit_count() == 1 and mb.bit_count() == 1 and ma != mb:
                ia = ma.bit_length() - 1
                ib = mb.bit_length() - 1
                found = (g_idx, active_inputs[ia], active_inputs[ib])
                break
        if found is None:
            raise ValueError("gate elimination stuck: no two-input gate found despite nonempty edges")
        _, wa, wb = found
        # Ensure wa is a vertex wire (> 0)
        if wa == 0:
            wa, wb = wb, wa
        u_vert = wa - 1
        extracted_vc.append(u_vert)

        # Compute tau(G_i) before step
        old_tau, _ = exact_min_vertex_cover(n, cur_edges)
        old_e = len(cur_edges)
        old_c = len(cur_gates)

        if wb == 0:
            # Case (a): delete u and project x_u -> z
            nxt_edges = [(x, y) for (x, y) in cur_edges if x != u_vert and y != u_vert]
        else:
            # Case (b): merge u into w and project x_u -> x_w
            w_vert = wb - 1
            nxt_set: Set[Tuple[int, int]] = set()
            for x, y in cur_edges:
                nx = w_vert if x == u_vert else x
                ny = w_vert if y == u_vert else y
                if nx != ny:
                    nxt_set.add((min(nx, ny), max(nx, ny)))
            nxt_edges = sorted(nxt_set)

        nxt_inputs, nxt_gates, _ = _simplify_projected_xor_circuit(active_inputs, cur_gates, wa, wb)
        new_tau, _ = exact_min_vertex_cover(n, nxt_edges)
        new_e = len(nxt_edges)
        new_c = len(nxt_gates)

        # Verify Item (3) telescoping invariant at every single step!
        if (old_c - new_c) < (old_e - new_e) + (old_tau - new_tau):
            raise ValueError(f"Item (3) telescoping invariant violated at step {steps}")
        # Verify Item (1): C_{i+1} implements F_{G_{i+1}}
        nxt_vals = set(_eval_xor_circuit(len(nxt_inputs), nxt_gates))
        pos = {w: i for i, w in enumerate(nxt_inputs)}
        for x, y in nxt_edges:
            t_mask = (1 << pos[0]) | (1 << pos[x + 1]) | (1 << pos[y + 1])
            if t_mask not in nxt_vals:
                raise ValueError(f"Item (1) edge-form invariant broken at step {steps}")

        active_inputs, cur_gates, cur_edges = nxt_inputs, nxt_gates, nxt_edges
        steps += 1

    # Verify extracted vertices form a valid vertex cover of original G
    ext_set = set(extracted_vc)
    for u, v in edges:
        if u not in ext_set and v not in ext_set:
            raise ValueError("gate-elimination extracted vertices do not cover all edges of G")
    if len(gates) < len(edges) + tau:
        raise ValueError("impossible: circuit smaller than m + tau(G)")

    # 3. Independently verify optimal (m + tau(G))-gate upper-bound XOR circuit construction
    ub_gates: List[Tuple[int, int]] = []
    t_wire: Dict[int, int] = {}
    for v in min_vc:
        t_wire[v] = (n + 1) + len(ub_gates)
        ub_gates.append((0, v + 1))  # t_v <- z + x_v
    vc_set = set(min_vc)
    for u, v in edges:
        pivot, other = (u, v) if u in vc_set else (v, u)
        ub_gates.append((t_wire[pivot], other + 1))
    ub_vals = set(_eval_xor_circuit(n + 1, ub_gates))
    for u, v in edges:
        if (1 | (1 << (u + 1)) | (1 << (v + 1))) not in ub_vals:
            raise ValueError("upper-bound XOR circuit failed")
    if len(ub_gates) != len(edges) + tau:
        raise ValueError("upper-bound XOR circuit size mismatch")

    return {
        "mode": "gate_elimination_lemma3",
        "n": n,
        "m": len(edges),
        "tau": tau,
        "supplied_gates": len(gates),
        "elimination_steps": steps,
    }


def _simulate_cnot_matrix(d: int, cnot_gates: List[Tuple[int, int]]) -> List[int]:
    """Simulate in-place CNOT circuit (target, control) on d wires; return row bitmasks over F_2."""
    rows = [1 << i for i in range(d)]
    for t, c in cnot_gates:
        if not (0 <= t < d and 0 <= c < d and t != c):
            raise ValueError(f"invalid CNOT gate ({t}, {c})")
        rows[t] ^= rows[c]
    return rows


def _mat_mul_f2(A: List[int], B: List[int], d: int) -> List[int]:
    """Multiply two d x d F_2 matrices represented as row bitmasks."""
    out = [0] * d
    for i in range(d):
        acc = 0
        row_a = A[i]
        for k in range(d):
            if (row_a >> k) & 1:
                acc ^= B[k]
        out[i] = acc
    return out


def verify_linear_oracle_cnot_lemma4(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Build B_G, verify B_G^2 = I, synthesize & simulate exact (2m+tau+1)-gate CNOT circuit."""
    n, edges = parse_graph(cert["graph"])
    ham_vc = [_req_int({"x": v}, "x") for v in _req_list(cert, "hamiltonian_min_vc")]
    claimed_cnot_size = _req_int(cert, "claimed_cnot_size")
    claimed_dxor_bg = _req_int(cert, "claimed_DXOR_BG")

    m = len(edges)
    tau, _ = exact_min_vertex_cover(n, edges)
    if len(ham_vc) != tau:
        raise ValueError(f"hamiltonian_min_vc size {len(ham_vc)} != exact tau(G)={tau}")
    if any(not (0 <= v < n) for v in ham_vc):
        raise ValueError("hamiltonian_min_vc contains out-of-range vertex")
    vc_set = set(ham_vc)
    if len(vc_set) != tau or not _is_valid_ham_path(set(edges), ham_vc):
        raise ValueError("hamiltonian_min_vc does not induce a valid Hamiltonian path")
    for u, v in edges:
        if u not in vc_set and v not in vc_set:
            raise ValueError("hamiltonian_min_vc is not a vertex cover")
    if tau < 1:
        raise ValueError("Lemma 4 synthesis requires tau >= 1")

    # Build target linear oracle B_G in GL(n + 1 + m, 2)
    # Wires: 0 = z, 1..n = x_0..x_{n-1}, (n+1)..(n+m) = y_{e_0}..y_{e_{m-1}}
    d = n + 1 + m
    BG = [1 << i for i in range(d)]
    edge_idx = {e: n + 1 + idx for idx, e in enumerate(edges)}
    for idx, (u, v) in enumerate(edges):
        w_y = n + 1 + idx
        BG[w_y] = (1 << w_y) | 1 | (1 << (u + 1)) | (1 << (v + 1))

    # 1. Verify B_G is an involution: B_G^2 == I_d
    ident = [1 << i for i in range(d)]
    if _mat_mul_f2(BG, BG, d) != ident:
        raise ValueError("B_G failed involution check B_G^2 == I")

    # 2. Synthesize Pavlogiannis's exact Lemma 4 Hamiltonian-path CNOT circuit
    path_edges = {(min(a, b), max(a, b)) for a, b in zip(ham_vc, ham_vc[1:])}
    cnot_gates: List[Tuple[int, int]] = []  # (target, control)
    # Step (1): z <- z + x_{s_1}
    cnot_gates.append((0, ham_vc[0] + 1))
    # Partition non-path edges to an endpoint in ham_vc
    assigned: Dict[int, List[Tuple[int, int]]] = {v: [] for v in ham_vc}
    for e in edges:
        if e in path_edges:
            continue
        u, v = e
        if u in vc_set:
            assigned[u].append((e, v))
        else:
            assigned[v].append((e, u))
    # Step (2)
    for i, si in enumerate(ham_vc):
        # (2a) non-path edges assigned to s_i
        for e, other in assigned[si]:
            wy = edge_idx[e]
            cnot_gates.append((wy, 0))
            cnot_gates.append((wy, other + 1))
        # (2b) path edge {s_i, s_{i+1}}
        if i + 1 < tau:
            sip1 = ham_vc[i + 1]
            pe = (min(si, sip1), max(si, sip1))
            wy = edge_idx[pe]
            cnot_gates.append((0, sip1 + 1))
            cnot_gates.append((wy, 0))
            cnot_gates.append((0, si + 1))
    # Step (3): z <- z + x_{s_k}
    cnot_gates.append((0, ham_vc[-1] + 1))

    expected_cnot = 2 * m + tau + 1
    if len(cnot_gates) != expected_cnot or expected_cnot != claimed_cnot_size:
        raise ValueError(f"CNOT circuit size mismatch: {len(cnot_gates)} vs {claimed_cnot_size}")
    if 2 * m + tau != claimed_dxor_bg:
        raise ValueError(f"DXOR(B_G) mismatch: {2*m + tau} vs {claimed_dxor_bg}")

    # 3. Simulate CNOT circuit in-place over F_2 and verify exact matrix equality with B_G!
    sim = _simulate_cnot_matrix(d, cnot_gates)
    if sim != BG:
        raise ValueError("simulated CNOT circuit matrix does not match B_G!")

    return {
        "mode": "linear_oracle_cnot_lemma4",
        "n": n,
        "m": m,
        "tau": tau,
        "dim_BG": d,
        "cnot_gates": len(cnot_gates),
        "involution_verified": True,
    }


def verify_free_resources_and_parity_thm5(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Theorem 5 parity decision equivalence + free-SWAP/free-ancilla -> XOR simulation."""
    n, edges = parse_graph(cert["graph"])
    budget_k = _req_int(cert, "vc_budget_k")
    claimed_yes = _req_bool(cert, "claimed_yes_instance")
    ops = _req_list(cert, "augmented_circuit_ops")
    n_ancillas = _req_int(cert, "n_clean_ancillas")
    if budget_k < 0 or n_ancillas < 0:
        raise ValueError("invalid budget_k or n_clean_ancillas")

    m = len(edges)
    tau, _ = exact_min_vertex_cover(n, edges)
    if tau % 2 != 0:
        raise ValueError("Theorem 5 promise requires tau(G) to be even")
    k_prime = budget_k if budget_k % 2 == 0 else budget_k - 1
    K = 2 * m + k_prime + 1
    # Check both bounds of Lemma 4 agree on the decision
    d_lo, d_hi = 2 * m + tau, 2 * m + tau + 1
    yes_vc = tau <= budget_k
    if (d_lo <= K) != yes_vc or (d_hi <= K) != yes_vc:
        raise ValueError("Theorem 5 parity decision equivalence violated")
    if yes_vc != claimed_yes:
        raise ValueError(f"decision mismatch: exact {yes_vc}, claimed {claimed_yes}")

    # Simulate augmented CNOT + SWAP + clean-ancilla circuit and execute Pavlogiannis's
    # exact syntactic translation to an XOR circuit of <= (# CNOT gates) computing the same rows!
    d = n + 1 + m
    total_wires = d + n_ancillas
    # Direct state simulation (clean ancillas initialized to 0 bitmask)
    state = [1 << i for i in range(d)] + [0] * n_ancillas
    # Syntactic XOR translation: track each wire's current XOR wire id (-1 for constant 0)
    xor_wire = list(range(d)) + [-1] * n_ancillas
    xor_gates: List[Tuple[int, int]] = []
    cnot_count = 0
    swap_count = 0
    for op in ops:
        if not isinstance(op, list) or len(op) != 3:
            raise ValueError("op must be ['CNOT'|'SWAP', a, b]")
        kind = op[0]
        a = _req_int({"x": op[1]}, "x")
        b = _req_int({"x": op[2]}, "x")
        if not (0 <= a < total_wires and 0 <= b < total_wires and a != b):
            raise ValueError("invalid op wire indices")
        if kind == "SWAP":
            swap_count += 1
            state[a], state[b] = state[b], state[a]
            xor_wire[a], xor_wire[b] = xor_wire[b], xor_wire[a]
        elif kind == "CNOT":
            # a = target, b = control: a <- a + b
            cnot_count += 1
            state[a] ^= state[b]
            if xor_wire[b] == -1:
                pass  # control is 0 -> no-op
            elif xor_wire[a] == -1:
                xor_wire[a] = xor_wire[b]  # target is 0 -> free copy
            else:
                new_id = d + len(xor_gates)
                xor_gates.append((xor_wire[a], xor_wire[b]))
                xor_wire[a] = new_id
        else:
            raise ValueError(f"unknown op kind '{kind}'")

    # Verify translated XOR circuit has <= cnot_count gates AND matches the exact output rows!
    if len(xor_gates) > cnot_count:
        raise ValueError("translated XOR circuit exceeded CNOT count")
    xor_vals = _eval_xor_circuit(d, xor_gates)
    for i in range(total_wires):
        got = 0 if xor_wire[i] == -1 else xor_vals[xor_wire[i]]
        if got != state[i]:
            raise ValueError(f"syntactic XOR translation disagreed on wire {i}")
    # Unconditionally require that the augmented circuit computes every row of B_G (up to wire permutation)
    # and verify that the translated XOR circuit obeys the 2m + tau lower bound (and <= K on YES instances).
    target_BG_rows = {1 << i for i in range(n + 1)}
    for idx, (u, v) in enumerate(edges):
        w_y = n + 1 + idx
        target_BG_rows.add((1 << w_y) | 1 | (1 << (u + 1)) | (1 << (v + 1)))
    if not target_BG_rows.issubset(set(state)):
        raise ValueError("augmented_circuit_ops does not compute all rows of B_G")
    if len(xor_gates) < 2 * m + tau:
        raise ValueError("impossible: translated XOR circuit beat 2m + tau lower bound")
    if yes_vc and len(xor_gates) > K:
        raise ValueError(f"YES instance translated XOR size {len(xor_gates)} exceeds budget K={K}")
    return {
        "mode": "free_resources_and_parity_thm5",
        "tau": tau,
        "K": K,
        "yes_instance": yes_vc,
        "cnot_count": cnot_count,
        "swap_count": swap_count,
        "translated_xor_gates": len(xor_gates),
    }


def verify_certificate(cert: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(cert, dict):
        raise ValueError("certificate must be JSON object")
    if cert.get("schema") != SCHEMA:
        raise ValueError(f"expected schema '{SCHEMA}', got '{cert.get('schema')}'")
    mode = cert.get("mode")
    if mode == "promise_vc_reduction_lemma2":
        return verify_promise_vc_reduction_lemma2(cert)
    if mode == "gate_elimination_lemma3":
        return verify_gate_elimination_lemma3(cert)
    if mode == "linear_oracle_cnot_lemma4":
        return verify_linear_oracle_cnot_lemma4(cert)
    if mode == "free_resources_and_parity_thm5":
        return verify_free_resources_and_parity_thm5(cert)
    raise ValueError(f"unknown mode '{mode}'")


def verify_file(path: Path) -> Dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    res = verify_certificate(data)
    res["file"] = path.name
    return res


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args:
        print("Usage: python -m src.cnot_hardness_verifier <cert_or_dir> [...]")
        return 2
    files: List[Path] = []
    for a in args:
        p = Path(a)
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.")
        return 1
    for f in files:
        res = verify_file(f)
        print(f"PASS  {f.name}  ({res['mode']})")
    print(f"VERIFIED {len(files)}/{len(files)} certificates under {SCHEMA}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
