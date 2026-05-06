Discrete Algorithmic Physics (DAP) – Formal Verification

This repository contains the Lean 4 source code for the formal verification of the 8 mechanical laws of Discrete Algorithmic Physics (DAP) , a novel experimental framework for the Collatz conjecture.

Overview

The DAP framework re-interprets Collatz dynamics as a dissipative physical system governed by verifiable laws, including a gravitational threshold and a binary fuel exhaustion principle. This repository provides machine-checked proofs of all core rules using the native_decide tactic.

Key Modules

· Basic.lean: Core definitions and trajectories.
· Rule1–Rule5.lean: Verification of the original five DAP rules.
· PhaseTransition.lean: Proof of the Phase Transition Law.
· CrossAlgorithm.lean: Verification of non-trivial cycles in chaotic maps.

Reference

The full theoretical framework is available as a preprint on Zenodo:
https://zenodo.org/badge/DOI/10.5281/zenodo.19956125.svg

License

This project is licensed under the MIT License.
