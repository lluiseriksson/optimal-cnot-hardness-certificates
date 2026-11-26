"""Unit, AST zero-float, and adversarial forgery tests for CNOT-HARD-CERT-1.0."""

from __future__ import annotations

import ast
import copy
import json
from pathlib import Path

import pytest

from src.cnot_hardness_verifier import SCHEMA, verify_certificate, verify_file

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"
VERIFIER_PATH = ROOT / "src" / "cnot_hardness_verifier.py"


def _load(cid: str) -> dict:
    return json.loads((CERT_DIR / f"{cid}.json").read_text(encoding="utf-8"))


@pytest.mark.parametrize("cid", [f"C{i:02d}" for i in range(1, 17)])
def test_canonical_certificate_passes(cid: str) -> None:
    res = verify_file(CERT_DIR / f"{cid}.json")
    assert res["file"] == f"{cid}.json"


def test_verifier_is_ast_zero_float() -> None:
    tree = ast.parse(VERIFIER_PATH.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"float literal found: {node.value}")
        if isinstance(node, ast.Name) and node.id == "float":
            pytest.fail("float builtin referenced")
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name not in {"math", "numpy", "scipy", "decimal"}
        if isinstance(node, ast.ImportFrom):
            assert node.module not in {"math", "numpy", "scipy", "decimal"}


def test_reject_wrong_schema() -> None:
    c = _load("C01")
    c["schema"] = "WRONG-1.0"
    with pytest.raises(ValueError, match="schema"):
        verify_certificate(c)


def test_reject_unknown_mode() -> None:
    c = _load("C01")
    c["mode"] = "bogus"
    with pytest.raises(ValueError, match="unknown mode"):
        verify_certificate(c)


def test_reject_bool_as_int() -> None:
    c = _load("C01")
    c["claimed_tau_H"] = True
    with pytest.raises(ValueError, match="exact int"):
        verify_certificate(c)


def test_reject_float_as_int() -> None:
    c = _load("C01")
    c["claimed_tau_G"] = 8.0
    with pytest.raises(ValueError, match="exact int"):
        verify_certificate(c)


def test_reject_forged_tau_H_mode1() -> None:
    c = _load("C01")
    c["claimed_tau_H"] = 2
    with pytest.raises(ValueError, match="tau\\(H\\) mismatch"):
        verify_certificate(c)


def test_reject_forged_tau_G_mode1() -> None:
    c = _load("C01")
    c["claimed_tau_G"] = 9
    with pytest.raises(ValueError, match="tau\\(G\\) mismatch"):
        verify_certificate(c)


def test_reject_incomplete_xor_circuit_mode2() -> None:
    c = copy.deepcopy(_load("C05"))
    c["xor_gates"].pop()
    with pytest.raises(ValueError, match="fails to compute edge form"):
        verify_certificate(c)


def test_reject_forged_dxor_mode2() -> None:
    c = _load("C07")
    c["claimed_DXOR_FG"] = 7
    with pytest.raises(ValueError, match="DXOR\\(F_G\\) mismatch"):
        verify_certificate(c)


def test_reject_out_of_range_gate_wire_mode2() -> None:
    c = copy.deepcopy(_load("C05"))
    c["xor_gates"][0] = [0, 99]
    with pytest.raises(ValueError, match="out-of-range wire"):
        verify_certificate(c)


def test_reject_non_hamiltonian_vc_mode3() -> None:
    c = copy.deepcopy(_load("C09"))
    # [0, 2] is a min VC of P_4 (edges 0-1, 1-2, 2-3), NOT adjacent -> no Hamiltonian path!
    c["hamiltonian_min_vc"] = [0, 2]
    with pytest.raises(ValueError, match="valid Hamiltonian path"):
        verify_certificate(c)


def test_reject_non_vc_hamiltonian_path_mode3() -> None:
    c = copy.deepcopy(_load("C09"))
    c["hamiltonian_min_vc"] = [0, 1]  # misses edge (2,3)
    with pytest.raises(ValueError, match="not a vertex cover"):
        verify_certificate(c)


def test_reject_forged_cnot_size_mode3() -> None:
    c = _load("C12")
    c["claimed_cnot_size"] = 54
    with pytest.raises(ValueError, match="CNOT circuit size mismatch"):
        verify_certificate(c)


def test_reject_odd_tau_in_mode4() -> None:
    c = copy.deepcopy(_load("C13"))
    c["graph"] = {"n": 3, "edges": [[0, 1], [1, 2]]}  # P_3 has tau=1 (odd)
    with pytest.raises(ValueError, match="tau\\(G\\) to be even"):
        verify_certificate(c)


def test_reject_flipped_decision_mode4() -> None:
    c = _load("C14")
    c["claimed_yes_instance"] = True
    with pytest.raises(ValueError, match="decision mismatch"):
        verify_certificate(c)


def test_reject_unknown_op_mode4() -> None:
    c = copy.deepcopy(_load("C13"))
    c["augmented_circuit_ops"].append(["TOFFOLI", 0, 1])
    with pytest.raises(ValueError, match="unknown op kind"):
        verify_certificate(c)


def test_reject_self_loop_graph() -> None:
    c = copy.deepcopy(_load("C01"))
    c["graph_H"]["edges"].append([0, 0])
    with pytest.raises(ValueError, match="invalid edge endpoints"):
        verify_certificate(c)


def test_reject_duplicate_edge_graph() -> None:
    c = copy.deepcopy(_load("C01"))
    c["graph_H"]["edges"].append([1, 0])
    with pytest.raises(ValueError, match="duplicate edge"):
        verify_certificate(c)


def test_reject_empty_circuit_in_mode4() -> None:
    c = copy.deepcopy(_load("C13"))
    c["augmented_circuit_ops"] = []
    with pytest.raises(ValueError, match="does not compute all rows of B_G"):
        verify_certificate(c)


def test_c13_exercises_zero_control_and_zero_target_reduction() -> None:
    res = verify_file(CERT_DIR / "C13.json")
    # C13 has 11 CNOTs (9 core + 1 zero-control no-op + 1 zero-target copy) translating to 9 XOR gates == K
    assert res["cnot_count"] == 11
    assert res["translated_xor_gates"] == 9
    assert res["translated_xor_gates"] <= res["K"]
