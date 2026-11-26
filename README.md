# Formal Certification of the NP-Completeness Proof for Optimal CNOT Synthesis on Linear Oracles (`CNOT-HARD-CERT-1.0`)

**Author:** Lluis Eriksson  
**Target Preprint:** Andreas Pavlogiannis, *"On the Hardness of Optimal CNOT Circuits"* (`arXiv:2611.34138v1`, November 2026)  
**Licenses:** Manuscript & figures `CC-BY-4.0`; Lean 4 kernel, verifier, tests, and certificates `MIT`

## Artifact Overview

This repository provides an independent, machine-checked Lean 4.35.0 kernel and zero-float $\mathbb{F}_2$ circuit verification suite (`CNOT-HARD-CERT-1.0`) auditing the proof of NP-completeness of optimal CNOT synthesis on linear oracles (`arXiv:2611.34138v1`):

1. **Constructive Lean 4.35.0 Kernel (`lean/CnotHardnessCert.lean`):** 18 constructive theorems (`0 sorry`, `0` custom axioms, `0 Classical.choice`, `0` warnings) formalizing Boolean/$\mathbb{F}_2$ linear-oracle involution ($B_G^2 = I$), 3-CNOT SWAP equivalence, free-ancilla reduction identities, Lemma 2 promise vertex-cover dominance and Hamiltonian interleaving, Lemma 3 gate-elimination Case (a)/(b) projections and telescoping step, Lemma 4 wire-update invariant, $z$-wire restoration, and exact gate count $2 + 3(k-1) + 2(m-k+1) = 2m + k + 1$, Theorem 5 even-budget rounding and NP-completeness reduction soundness, and free-resource sandwich bounds.
2. **AST-Audited Zero-Float $\mathbb{F}_2$ Circuit Verifier (`src/cnot_hardness_verifier.py`):** Four executable verification modes (`promise_vc_reduction_lemma2`, `gate_elimination_lemma3` running the exact projection sequence $\langle C_0, G_0 \rangle \to \dots \to \langle C_q, G_q \rangle$, `linear_oracle_cnot_lemma4` simulating the synthesized $(2m+\tau+1)$-gate CNOT circuit over $\mathbb{F}_2$ and checking $B_G^2 = I$, and `free_resources_and_parity_thm5` executing the syntactic free-SWAP/free-ancilla to XOR translation).
3. **16 Canonical Certificates (`certificates/C01.json`–`C16.json`)** and **36 Unit & Adversarial Forgery Tests (`tests/test_verifier.py`)**.

## Quick Reproduction

```bash
cd lean && lake build && cd ..
python scripts/generate_certificates.py
python -m src.cnot_hardness_verifier certificates/
pytest -q
python scripts/generate_figures.py
```
