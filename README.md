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
https://doi.org/10.5281/zenodo.19956125

License

This project is licensed under the MIT License.
## How to Build and Run

### Prerequisites
- [Lean 4](https://leanprover.org/) (installed via `elan`)
- [Python 3](https://www.python.org/) (for computational tests)

### Lean 4 Formal Verification

```bash
# Clone the repository
git clone https://github.com/M-RAMDHAN/discrete-algorithmic-physics.git
cd discrete-algorithmic-physics

# Build the project
lake build

# Run the full DAP verification suite (all 8 rules)
lake exe dap-verify
```

**Expected output:** The program verifies all 8 DAP rules with `native_decide` and `rfl`. Zero `sorry` or `admit` are used anywhere in the proofs.

### Python Computational Tests

```bash
python dap_python_verification.py
```

**Expected output:** 32,015 tests across 5 algorithms. All 8 DAP rules verified.

### Project Structure

| File | Purpose |
| :--- | :--- |
| `Basic.lean` | Core definitions (collatzStep, popcount, trajectories) |
| `Rule5.lean` | mod 4 Glue Rule (formal proof) |
| `Rule6.lean` | Phase Transition Law (formal proof) |
| `Rule7.lean` | Catalytic Reversal Law (formal proof) |
| `Cycles.lean` | Non-trivial cycle verification (5n+1, 3n-1) |
| `Computational.lean` | Extensive computational verification |
| `Main.lean` | Grand unified verification of all 8 rules |
| `dap_python_verification.py` | Python testing suite (32,015 tests) |
| `DAP_VERIFICATION_REPORT.md` | Comprehensive verification report |

### Note on Methodology

This project is part of the **Discrete Algorithmic Physics (DAP)** framework, an approach grounded in Experimental Mathematics. The Lean 4 formalization was developed with the assistance of an AI agent capable of executing code in its own terminal environment. The agent successfully ran `lake build` and `lake exe dap-verify` in its environment.

This repository is now open for **independent human verification** — a core principle of the DAP methodology. If you encounter any issues building or running the project, please open an issue or submit a pull request.

### References

- **Full paper (Zenodo):** [https://doi.org/10.5281/zenodo.19956125](https://doi.org/10.5281/zenodo.19956125)
- **Preprint (Preprints.org):** [Pending — ID 212323]
