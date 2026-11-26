# The Dipolar Geometry of the Primes and the Critical Line of the Riemann Zeta Function: A Machine-Verified Geodesic and Adelic Framework

**Author:** Mariano Martín Ramírez Tamayo · **ORCID:** [0009-0005-6194-1845](https://orcid.org/0009-0005-6194-1845)  
**Affiliation:** Independent Researcher  
**Date:** November 26, 2026  
**Subject Classification (MSC 2020):** Primary 11M06, 11M26; Secondary 11N05, 11R56, 30B50, 37D40, 53C22  
**Formal Repository (Lean 4 & Code):** [https://github.com/airoman/riemann-dipolar-geometry](https://github.com/airoman/riemann-dipolar-geometry)  

---

> **Publication Formats:**
> - **Complete 68-Page Typeset Vector PDF (Recommended for Reading & Citation):** [`ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf`](ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf)
> - **arXiv-Ready LaTeX Source:** [`ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.tex`](ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.tex)
> - **Compact 17-Page Journal Edition:** [`PAPER_COMPACT_FORMAL_VERIFICATION_AND_DIPOLAR_SIEVE.pdf`](PAPER_COMPACT_FORMAL_VERIFICATION_AND_DIPOLAR_SIEVE.pdf) ([Markdown](PAPER_COMPACT_FORMAL_VERIFICATION_AND_DIPOLAR_SIEVE.md))
> - **Spanish Academic Edition (14 pp.):** [`SOBRE_EL_MARCO_GEODESICO_DIPOLAR_UNIFICADO_Y_LA_FUNCION_ZETA_DE_RIEMANN_ES.pdf`](SOBRE_EL_MARCO_GEODESICO_DIPOLAR_UNIFICADO_Y_LA_FUNCION_ZETA_DE_RIEMANN_ES.pdf) ([Markdown](SOBRE_EL_MARCO_GEODESICO_DIPOLAR_UNIFICADO_Y_LA_FUNCION_ZETA_DE_RIEMANN_ES.md))

---

## Abstract

Every natural number $`N \ge 2`$ admits a canonical pair of **past–future prime defect coordinates** $`k_r(N) = N - p_{\text{prev}}(N)`$ and $`k_i(N) = p_{\text{next}}(N) - N`$, governed by a non-circular trigonometric prime rotor $`\Psi_N(\delta)`$ whose indicator limit recovers $`\mathbf{1}_{\mathbb{P}}(N)`$ without circularity. Inside every inter-prime interval $`[p_m, p_{m+1}]`$, the dipolar defect $`D(N) = k_i(N) - k_r(N)`$ obeys **exact inter-prime dipolar neutrality** $`\sum D(N) = 0`$, characterizing **symmetric Goldbach centers** identically by $`D(N) = 0`$ and **Twin Prime intervals** by the minimal-energy ground state $`E(N) = k_r(N)^2 + k_i(N)^2 = 2`$, while discrete boundary-reset jumps $`\Delta\widetilde{D}(N) + 2`$ recover the **von Mangoldt function** $`\Lambda(N)`$ and generate $`-\zeta'(s)/\zeta(s)`$. Lifting this past–future dipolar sieve into the Gaussian integers $`\mathbb{Z}[i]`$, the split-quaternion algebra $`\mathbb{H}_{\text{split}}`$, the flat Clifford Torus $`\mathbb{T}^2 \subset S^3`$, the compact five-dimensional quotient manifold $`\mathcal{M}^5 = (S^3/\Gamma_{120}) \times \mathbb{T}^2`$, the Bohr Torus $`\mathbb{T}^\infty`$, and the rational Adele Ring $`\mathbb{A}_{\mathbb{Q}}`$ maps prime-interval dynamics directly onto the critical line $`\mathrm{Re}(s) = 1/2`$ of both the Riemann Zeta function $`\zeta(s)`$ (**RH**) and every primitive and imprimitive Dirichlet $`L`$-function $`L(s, \chi)`$ (**GRH**).

All results are **formally verified in Lean 4 (v4.36.0) + Mathlib4** across **42 self-contained modules** (`43,906` module lines / `44,710` net Lean 4 lines across 44 `.lean` files, `7,918` Lake build jobs, `0 sorry`, axioms strictly `[propext, Classical.choice, Quot.sound]`): (i) unconditional off-line monopolar divergence for all $`\beta \neq 1/2`$; (ii) **complete unconditional closure of $`\mathrm{Re}(s) \ge 1`$ (including $`\mathrm{Re}(s) = 1`$) for all $`\gamma \in \mathbb{R}`$**, open critical-strip collars $`(0, \delta(T)] \cup [1-\delta(T), 1)`$ for every height $`T > 0`$, and the zero-free strip rectangle $`(0,1)\times[-4,4]`$ directly on Mathlib4's `riemannZeta`; (iii) zero-discretization continuous arithmetic Weil positivity crossing all seven first prime powers $`\{2,3,4,5,7,8,9\}`$ ($`L \le 11/5 > \ln 9`$), all-horizon Hilbert–Schur reduction, exact limit-barrier no-go theorems ($`K_{\text{wall}}(u) = (5+2u^2+u^4)e^{-u^2}`$ and reparametrization-invariance for $`\lambda_{\min}(S_L)\to 0^+`$), arbitrary-dimension $`n \times n`$ block-Schur Cholesky–Gram induction, explicit golden-ratio ($`\varphi = 2\cos(\pi/5)`$) icosian $`\Gamma_{120}`$ coordinates on $`S^3 \subset \mathcal{M}^5`$, unconditional Hurwitz–KAM Diophantine spiral non-resonance $`|q\varphi - p| \ge 1/(\sqrt{5}q+1)`$ on $`\mathbb{T}^2`$, primitive quadratic character $`\chi_5`$ ($`L(1,\chi_5)\ne 0`$), stereographic North-Pole compactification $`\theta(L) = 2\arctan(L) \to \pi`$, and preconditioned spectral congruence Gronwall barriers; (iv) **six exact bidirectional equivalences** binding Mathlib4's official `RiemannHypothesis` to the monopolar bridge, adelic Weil positivity, Lax–Phillips modular scattering, all-$`\alpha`$ Hermite–Biehler zero exclusion, $`\mathbb{T}^2`$ equatorial rigidity, and uniform open collars; and (v) an **eight-way global bidirectional equivalence for the Generalized Riemann Hypothesis (`AllDirichletGRH ↔ GeneralizedRiemannHypothesis`)** over Mathlib4's `DirichletCharacter.LFunction` across all moduli $`N \ge 1`$ and all primitive and imprimitive characters $`\chi \pmod N`$, together with zero-Lyapunov quasiperiodic order and formal *Modus Ponens* elevation. Designed to compile and verify on any standard personal computer, the 42-module suite is corroborated by twelve 65-to-220-digit arbitrary-precision computational laboratories.

---

---

## Chapter-by-Chapter GitHub Web Edition (100% MathJax-Rendered)

Because the complete 68-page paper contains over 4,500 mathematical expressions (exceeding GitHub's single-page browser MathJax rendering budget if placed in one 390 KB file), the Markdown web edition is cleanly structured into 15 modular chapters in [`chapters/`](chapters/)—each strictly under GitHub's rendering threshold so every equation renders instantaneously with zero errors:

| Part | Chapter & Scope | Size | Math Expressions |
| :-: | :--- | :-: | :-: |
| 1 | [Part 1 — Abstract & Section 1: Introduction](chapters/01_abstract_and_introduction.md) | 31 KB | 297 |
| 2 | [Part 2 — Sections 2–4: Non-Circular Sieve, Z[i] Symmetries & von Mangoldt Bridge](chapters/02_dipolar_sieve_and_gaussian_symmetries.md) | 19 KB | 231 |
| 3 | [Part 3 — Section 5: Spectral Decomposition & Clifford Torus Geodesic Rigidity](chapters/03_spectral_decomposition_and_clifford_torus.md) | 23 KB | 273 |
| 4 | [Part 4 — Sections 6.1–6.6: Bohr Torus, Adele Ring, Past–Future Kernel & Laguerre Hierarchy](chapters/04_bohr_torus_adeles_and_weil_positivity.md) | 25 KB | 261 |
| 5 | [Part 5 — Sections 6.7–6.10: Connes–Consani Prolate, Arithmetic Weil & Herglotz–Pick](chapters/05_prolate_weil_corridor_and_herglotz_pick.md) | 30 KB | 322 |
| 6 | [Part 6 — Sections 6.11–6.13: Hermite–Biehler Homotopy, Lyapunov Solver & Limit Barriers](chapters/06_hermite_biehler_lyapunov_and_limit_barriers.md) | 26 KB | 246 |
| 7 | [Part 7 — Sections 6.14–6.15: Geodesic Compactification, Pullback & Kuramoto Coherence](chapters/07_geodesic_renormalization_and_kuramoto.md) | 27 KB | 301 |
| 8 | [Part 8 — Sections 6.16–6.17: Two-Prime & Seven-Prime Continuous Weil Positivity](chapters/08_two_prime_and_seven_prime_weil.md) | 20 KB | 244 |
| 9 | [Part 9 — Sections 6.18–6.21: All-Horizon Schur Reduction & Compact 5D Manifold M⁵](chapters/09_all_horizon_schur_and_5d_manifold.md) | 23 KB | 263 |
| 10 | [Part 10 — Section 7.1: Formal Machine Verification in Lean 4 + Mathlib4 (42 Modules)](chapters/10_formal_lean4_verification_summary.md) | 28 KB | 51 |
| 11 | [Part 11 — Section 7.2 (Labs 1–5): Standalone & 65-Digit Routes A/B Laboratories](chapters/11_numerical_labs_1_to_5.md) | 25 KB | 450 |
| 12 | [Part 12 — Section 7.2 (Labs 6–9): Arithmetic Weil, Coercivity & Hermite–Biehler Labs](chapters/12_numerical_labs_6_to_9.md) | 22 KB | 431 |
| 13 | [Part 13 — Section 7.2 (Labs 10–14): Limit Barriers & 220-Digit Multi-Prime Labs](chapters/13_numerical_labs_10_to_14.md) | 25 KB | 429 |
| 14 | [Part 14 — Sections 7.3–7.4: AI Verification Disclosure & Complete Logical Hierarchy](chapters/14_logical_hierarchy_table.md) | 44 KB | 372 |
| 15 | [Part 15 — GRH Extension, Section 8 (Conclusion) & Complete References](chapters/15_grh_extension_conclusion_and_references.md) | 24 KB | 145 |

---

*Author: Mariano Martín Ramírez Tamayo · ORCID: [0009-0005-6194-1845](https://orcid.org/0009-0005-6194-1845) · Repository: [airoman/riemann-dipolar-geometry](https://github.com/airoman/riemann-dipolar-geometry)*
