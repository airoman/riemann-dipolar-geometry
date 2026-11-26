# Contributing to the Dipolar Prime & Lean 4 Formalization Project

Thank you for your interest in auditing, reviewing, and extending this work. We welcome constructive contributions from mathematicians, computer scientists, logicians, and the formal verification community.

## Guiding Principles

1. **Democratic Auditability:** The mathematical architecture is designed to be accessible. Anyone should be able to verify every step using open-source tools without proprietary software or massive supercomputers.
2. **Zero-Trust Kernel Guarantee:** No paper claim, informal intuition, or AI-generated reasoning is accepted without deterministic verification by the Lean 4 kernel.
3. **Strict Axiomatic Discipline:** All theorems must depend strictly on standard Lean 4 / Mathlib4 foundation axioms:
   - Propositional Extensionality (`propext`)
   - Axiom of Choice (`Classical.choice`)
   - Quotient Soundness (`Quot.sound`)
   Custom axioms, `sorry`, `admit`, or `native_decide` on infinite domains are strictly prohibited.
4. **Direct Binding to Mathlib4:** Never redefine surrogate toy functions for core mathematical objects. Theorems must bind directly to official Mathlib structures (`riemannZeta`, `DirichletCharacter.LFunction`, `ArithmeticFunction.vonMangoldt`, `RiemannHypothesis`).

## How to Test Locally

### Prerequisites
- Install `elan` (the Lean version manager):
  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
- Ensure Lean toolchain `v4.36.0` is active.

### Build and Verify
```bash
# Clone the repository
git clone https://github.com/airoman/riemann-dipolar-geometry.git
cd riemann-dipolar-geometry

# Build and verify all 42 Mathlib4 modules (7,918 jobs, 0 sorry)
cd lean_mathlib4_project
lake exe cache get
lake build
cd ..

# Test the zero-dependency standalone proof (runs in ~2 seconds)
lean lean_mathlib4_project/Unified_Master_RH_Proof.lean

# Run the independent multi-precision verification scripts (Python / C99)
python scripts/verify_unified_solver.py
python verify_dipolar_sieve.py
```

## Submitting Pull Requests

- Use descriptive branch names (e.g., `audit/module-42-bounds`, `docs/expand-stein-algorithm`).
- Ensure all CI tests pass locally before opening a PR.
- Fill out the provided [Pull Request Template](.github/PULL_REQUEST_TEMPLATE.md).
- Keep discussion focused on mathematical rigor, clear exposition, and kernel verifiability.
