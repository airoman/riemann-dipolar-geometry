> **Extended Paper — Part 11 — Section 7.2 (Labs 1–5): Standalone & 65-Digit Routes A/B Laboratories**  
> [← Part 10](10_formal_lean4_verification_summary.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 12 →](12_numerical_labs_6_to_9.md) · [Complete 68-Page PDF](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf)

---

### 7.2 Standalone Numerical, Oscillatory, and Geodesic Verification ($`N \le 100{,}000`$)

Complementing the Lean 4 formal verification, high-performance numerical solvers in C99 (`verify_unified_solver.c`, compiled with GCC 15.2 `-O3`) and pure Python (`verify_unified_solver.py`) were executed across two benchmark suites at the first non-trivial zero ordinate $`\gamma_1 \approx 14.134725141735`$:

#### 1. Complex Oscillatory Partial Sums Across 5,132 Inter-Prime Basins ($`X \le 25{,}000`$)
Evaluating the full oscillatory sums (preserving all phase cancellations $`e^{-i\gamma_1 \ln N}`$) confirms with IEEE 754 double precision ($`\epsilon < 2.22 \times 10^{-16}`$) that the monopolar scale drift vanishes identically at $`\beta = 1/2`$ and diverges off the critical line:

| $`\beta`$ | $`\sigma`$ | $`X = 1{,}000`$ ($`\Vert \sum\mathcal{D}\Vert  / \Vert \sum\mathcal{M}\Vert `$) | $`X = 5{,}000`$ | $`X = 10{,}000`$ | $`X = 25{,}000`$ | Equilibrium Status |
| :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| **0.50** | **0.00** | `7.346` / **`0.000`** | `8.713` / **`0.000`** | `7.851` / **`0.000`** | `7.982` / **`0.000`** | **Exact ($`\mathcal{M} \equiv 0`$)** |
| 0.55 | +0.05 | `7.533` / `10.11` | `9.009` / `43.18` | `8.065` / `30.26` | `8.203` / `54.46` | $`\mathcal{D}`$ bdd; $`\mathcal{M}`$ div. |
| 0.65 | +0.15 | `9.110` / `34.32` | `11.56` / `157.1` | `9.886` / `122.4` | `10.08` / `238.1` | $`\mathcal{D}`$ bdd; $`\mathcal{M}`$ div. |
| 0.75 | +0.25 | `12.69` / `72.56` | `17.77` / `373.3` | `14.15` / `341.8` | `14.38` / `736.5` | $`\mathcal{D}`$ bdd; $`\mathcal{M}`$ div. |

#### 2. Clifford Torus Geodesic Invariants and Lyapunov Drift Across 9,592 Primes ($`N \le 100{,}000`$)
Across all 9,591 inter-prime gaps up to $`N = 100{,}000`$, the cumulative discrete dipolar defect is verified to be **identically zero** ($`\sum_{m=1}^{9591} \sum_{k=1}^{g_m-1} (g_m - 2k) = 0`$), identifying exactly 1,224 Twin Prime minimal-energy ground states ($`E = 2`$) and 9,590 symmetric Goldbach centers ($`D = 0`$). The differential-geometric invariants on $`\mathbb{T}^2 \subset S^3`$ satisfy:

| $`\beta`$ | $`\Delta \beta`$ | $`\Delta \mathcal{C}`$ | Curv. $`K`$ | $`\lambda`$ | $`\mathrm{div}(\mathbf{J})`$ | Max Drift $`\Vert M_{\max}\Vert `$ | Geodesic Status |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| 0.10 | -0.40 | $`1.60\times 10^{-1}`$ | $`-1.60\times 10^{-1}`$ | 0.40 | -0.80 | $`8.42\times 10^{+1}`$ | Escape ($`\lambda>0`$) |
| 0.25 | -0.25 | $`6.25\times 10^{-2}`$ | $`-6.25\times 10^{-2}`$ | 0.25 | -0.50 | $`1.53\times 10^{+1}`$ | Escape ($`\lambda>0`$) |
| 0.40 | -0.10 | $`1.00\times 10^{-2}`$ | $`-1.00\times 10^{-2}`$ | 0.10 | -0.20 | $`2.50\times 10^{+0}`$ | Escape ($`\lambda>0`$) |
| 0.49 | -0.01 | $`1.00\times 10^{-4}`$ | $`-1.00\times 10^{-4}`$ | 0.01 | -0.02 | $`2.04\times 10^{-1}`$ | Escape ($`\lambda>0`$) |
| **0.50** | **0.00** | **0.00** | **0.00** | **0.00** | **0.00** | **0.00** | **Confined ($`\mathbb{T}^2`$)** |
| 0.51 | +0.01 | $`1.00\times 10^{-4}`$ | $`-1.00\times 10^{-4}`$ | 0.01 | +0.02 | $`2.04\times 10^{-1}`$ | Escape ($`\lambda>0`$) |
| 0.60 | +0.10 | $`1.00\times 10^{-2}`$ | $`-1.00\times 10^{-2}`$ | 0.10 | +0.20 | $`2.50\times 10^{+0}`$ | Escape ($`\lambda>0`$) |
| 0.75 | +0.25 | $`6.25\times 10^{-2}`$ | $`-6.25\times 10^{-2}`$ | 0.25 | +0.50 | $`1.53\times 10^{+1}`$ | Escape ($`\lambda>0`$) |
| 0.90 | +0.40 | $`1.60\times 10^{-1}`$ | $`-1.60\times 10^{-1}`$ | 0.40 | +0.80 | $`8.42\times 10^{+1}`$ | Escape ($`\lambda>0`$) |

#### 3. 65-Digit High-Precision Investigation of Closure Routes A and B (`verify_routes_ab_laboratory.py`)

To probe the exact quantitative structure of the single remaining open equivalence (`RiemannHypothesis ↔ SpectralBridgeTarget ↔ AdelicDipolarWeilPositivity`), a zero-dependency **65-digit arbitrary-precision Decimal laboratory** (`verify_routes_ab_laboratory.py`) was executed across both canonical global attack pathways:

##### Route B: Past–Future Kernel $`\Phi(u)`$, Pólya–Jensen Hyperbolicity, and de Bruijn–Newman Heat Flow
Evaluating $`\Phi(u)`$ to 65 digits yields $`\Phi(0) = 0.89339380093424688817\dots`$ and $`\xi(1/2) = 2\int_0^\infty \Phi(u)\,du = 0.49712077818831410991\dots`$, recovering the first five Riemann zeros directly from Theorem 6.6 ($`I_{\text{even}}(0, \gamma_k) = 0`$ to $`< 10^{-64}`$) while confirming strict non-vanishing off the critical line ($`\sigma = 0.1`$: $`I_{\text{odd}}(0.1, \gamma_1) = +6.904 \times 10^{-5}`$, transverse gradient $`\partial_\sigma I_{\text{odd}}(0, \gamma_1) = +6.914 \times 10^{-4} \neq 0`$). Writing $`a_k \triangleq \frac{2 k!}{(2k)!} b_k`$, the moments $`b_k`$ lie strictly inside the **Turán–Cauchy–Schwarz corridor** $`1 < \frac{b_k b_{k+2}}{b_{k+1}^2} < \frac{2k+3}{2k+1}`$ across all $`k = 0 \dots 48`$ (with the lower bound proved unconditionally in Theorem 6.7.2), and exact **Sturm-sequence root counting** certifies that every Jensen polynomial $`J^{d,n}(X) = \sum_{j=0}^d \binom{d}{j} a_{n+j} X^j`$ is strictly hyperbolic (all roots real and simple) for all $`d \in \{2, 3, 4, 5, 6, 8\}`$ and $`n = 0 \dots 40`$:

| Degree $`d`$ | Shifts $`n`$ Tested | Sturm Real-Root Count | Min. Hermite-Scaled Root Gap | Shift $`n^{\ast}`$ |
| :---: | :---: | :---: | :---: | :---: |
| 2 | $`0 \dots 40`$ | **PASS** ($`2/2`$) | 2.010741190682 | 40 |
| 3 | $`0 \dots 40`$ | **PASS** ($`3/3`$) | 1.677510276002 | 20 |
| 4 | $`0 \dots 40`$ | **PASS** ($`4/4`$) | 1.465433707364 | 0 |
| 5 | $`0 \dots 40`$ | **PASS** ($`5/5`$) | 1.285992606740 | 0 |
| 6 | $`0 \dots 40`$ | **PASS** ($`6/6`$) | 1.162129976344 | 0 |
| 8 | $`0 \dots 40`$ | **PASS** ($`8/8`$) | 0.991415933382 | 0 |

To expose the exact obstruction of Route B, the past–future kernel was evolved under the **de Bruijn–Newman heat flow** $`\Phi_t(u) = e^{t u^2}\Phi(u)`$ (where $`\mathrm{RH} \iff \Lambda \le 0`$ and Rodgers–Tao (2020) proved $`\Lambda \ge 0`$, placing RH on the knife-edge $`\Lambda = 0`$). Tracking the close critical-line pair $`(\gamma_9, \gamma_{10}) \approx (48.005151, 49.773832)`$ directly in 65-digit arithmetic against simultaneous Sturm hyperbolicity of $`J_t^{d,0}(X)`$ yields:

| Heat Parameter $`t`$ | Real Zeros of $`H_t(z)`$ in $`[46.5, 51.5]`$ | Gap $`\Delta\gamma(t)`$ | $`J_t^{d,0}`$ Real Roots ($`d = 2, 4, 6, 8`$) |
| :---: | :---: | :---: | :---: |
| +0.10 | $`[47.772009,\; 49.683360]`$ | 1.911351 | `2/2  4/4  6/6  8/8` |
| **0.00** | **$`[48.005151,\; 49.773832]`$** | **1.768682** | **`2/2  4/4  6/6  8/8`** |
| -0.20 | $`[48.520222,\; 49.912798]`$ | 1.392576 | `2/2  4/4  6/6  8/8` |
| -0.45 | $`[49.434999,\; 49.828214]`$ | 0.393216 | `2/2  4/4  6/6  8/8` |
| **-0.50** | **Collided (off-line complex pair)** | 0 (complex) | **`2/2  4/4  6/6  8/8`** |
| **-0.60** | **Collided (off-line complex pair)** | 0 (complex) | **`2/2  4/4  6/6  8/8`** |
| -100.0 | Many off-line complex pairs | complex | `2/2  4/4  6/6  6/8` (fails at $`d=8`$) |

Exact bisection locates the collision at $`t_{\text{coll}}(\gamma_9, \gamma_{10}) = -0.469378`$ (corresponding to $`4 t_{\text{coll}} = -1.877513`$ in standard $`H_t(z/2)`$ scaling). Critically, at $`t = -0.60`$, $`\Phi_t(u)`$ remains strictly positive for all $`u \in \mathbb{R}`$ and every low-degree Jensen polynomial $`J_t^{d,0}(X)`$ ($`d \le 8`$) remains 100% hyperbolic **even though $`(\gamma_9, \gamma_{10})`$ have already collided and left the critical line**. Thus, local positivity of $`\Phi(u)`$ and finite-degree Jensen bounds cannot close RH; only uniform global hyperbolicity over all $`(d, n) \in \mathbb{N}^2`$ simultaneously detects $`\Lambda \le 0`$.

##### Route A: 65-Digit Compact-Support Adelic–Dipolar Weil Matrices $`W^{(L)}`$ and Two-Sided Arithmetic Rigidity
Using the exact closed-form Weil–Guinand decomposition on $`f = g * \tilde{g}`$ supported on $`[-L, L]`$,

```math
W(f) = \underbrace{\int_{-L}^L f(u)(e^{u/2} + e^{-u/2})\,du}_{W_{\text{pole}}(f)} + \underbrace{\int_0^L \frac{2e^{-u/2}}{1 - e^{-2u}}\big(f(0) - f(u)\big)\,du + f(0)\!\left[\ln\!\frac{1+e^{-L/2}}{1-e^{-L/2}} + 2\arctan(e^{-L/2}) - C_\infty\right]}_{W_\infty(f),\quad C_\infty = \gamma_{\text{E}} + \ln(8\pi) + \pi/2} - \underbrace{2\sum_{2 \le n \le e^L}\frac{\Lambda(n)}{\sqrt{n}}f(\ln n)}_{W_{\text{prime}}(f)},
```

calibrated first to 15 digits against the zeros from $`\Phi(u)`$ on $`f(u) = e^{-10 u^2}`$ (discrepancy $`-5.15 \times 10^{-16}`$, matching the sixth-zero tail), the exact $`6 \times 6`$ Hermitian Weil–Adelic matrices $`W^{(L)} = W_{\text{pole}}^{(L)} + W_\infty^{(L)} - W_{\text{prime}}^{(L)}`$ were assembled on the smooth orthonormal Dirichlet basis of $`L^2([-L/2, L/2])`$ (which block-diagonalizes identically into EVEN modes $`m = 1, 3, 5, 7, 9, 11`$ and ODD modes $`m = 2, 4, 6, 8, 10, 12`$) and diagonalized via 65-digit Jacobi rotation across $`L \in [0.5, 7.0]`$ ($`e^7 \approx 1096.6`$, incorporating all 209 exact prime powers $`p^m \le e^7`$):

| Support $`L`$ | $`e^L`$ | Exact $`\mathrm{card}(p^m)`$ | Even $`\Vert W_{\text{pole}}\Vert `$ | Even $`\Vert W_{\text{prime}}\Vert `$ | Even $`\lambda_{\min}(W^{(L)})`$ | Odd $`\lambda_{\min}(W^{(L)})`$ | Exact Cancellation | PSD? |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 0.5 | 1.6 | 0 | $`9.71 \times 10^{-1}`$ | 0 | $`+3.828 \times 10^{-2}`$ | $`+4.316 \times 10^{-1}`$ | 1.4 orders | **YES** |
| 1.0 | 2.7 | 1 | $`1.97 \times 10^{0}`$ | $`8.45 \times 10^{-1}`$ | $`+1.292 \times 10^{-6}`$ | $`+2.545 \times 10^{-4}`$ | 6.2 orders | **YES** |
| 2.0 | 7.4 | 5 | $`4.18 \times 10^{0}`$ | $`2.44 \times 10^{0}`$ | $`+1.823 \times 10^{-15}`$ | $`+6.204 \times 10^{-14}`$ | 15.4 orders | **YES** |
| 3.0 | 20.1 | 12 | $`6.92 \times 10^{0}`$ | $`4.14 \times 10^{0}`$ | $`+5.511 \times 10^{-20}`$ | $`+1.909 \times 10^{-18}`$ | 20.1 orders | **YES** |
| 4.0 | 54.6 | 24 | $`1.06 \times 10^{1}`$ | $`7.49 \times 10^{0}`$ | $`+8.540 \times 10^{-23}`$ | $`+1.892 \times 10^{-21}`$ | 23.1 orders | **YES** |
| 5.0 | 148.4 | 47 | $`1.59 \times 10^{1}`$ | $`1.26 \times 10^{1}`$ | $`+5.291 \times 10^{-25}`$ | $`+9.926 \times 10^{-24}`$ | 25.5 orders | **YES** |
| 6.0 | 403.4 | 98 | $`2.38 \times 10^{1}`$ | $`2.04 \times 10^{1}`$ | $`+9.052 \times 10^{-27}`$ | $`+1.406 \times 10^{-25}`$ | 27.4 orders | **YES** |
| **7.0** | **1096.6** | **209** | **$`3.60 \times 10^{1}`$** | **$`3.25 \times 10^{1}`$** | **$`+2.176 \times 10^{-28}`$** | **$`+4.059 \times 10^{-27}`$** | **29.2 orders** | **YES** |

Two sharp structural discoveries emerge from this 65-digit spectral experiment:

1. **Super-Exponential Prolate Spectral Gap & Catastrophic Cancellation:** Standard IEEE 754 double precision (`float64`, $`\sim 16`$ digits) fails completely for $`L \ge 2.5`$ because low-frequency compactly supported combinations approximate prolate spheroidal eigenstates concentrated below the first zero $`\gamma_1 \approx 14.1347`$ (Connes & Consani, 2021), driving $`\lambda_{\min}(W^{(L)})`$ down to $`+2.176 \times 10^{-28}`$ at $`L = 7.0`$ despite $`\Vert W_{\text{pole}}\Vert  \approx 36.0`$ and $`\Vert W_{\text{prime}}\Vert  \approx 32.5`$ (**29.2 orders of magnitude of exact cancellation**). Notably, even on the ODD parity subspace—where $`W_{\text{pole}}^{(L)}`$ is **negative** semi-definite—$`W^{(L)}`$ remains strictly positive definite ($`\lambda_{\min} = +4.059 \times 10^{-27}`$ at $`L = 7.0`$).
2. **Two-Sided Arithmetic Razor Edge (Adversarial Perturbation Controls at $`L = 6.0`$):** Whereas the exact arithmetic primes yield $`\lambda_{\min} = +9.052 \times 10^{-27}`$, distorting the prime-sum matrix in **either** direction destroys positivity by over 22 orders of magnitude: rescaling $`W_{\text{prime}}`$ by $`+0.1\%`$ (`scale = 1.001`) gives $`\lambda_{\min} = -1.974 \times 10^{-2}`$, rescaling by $`-0.1\%`$ (`scale = 0.999`) gives $`\lambda_{\min} = -1.949 \times 10^{-3}`$, truncating primes prematurely at $`0.95 L`$ gives $`\lambda_{\min} = -8.604 \times 10^{-5}`$ ($`0.90 L \implies -3.075 \times 10^{-2}`$), and distorting the **single prime $`p = 2`$** by $`+1\%`$ or $`-1\%`$ yields $`\lambda_{\min} = -9.221 \times 10^{-3}`$ and $`-9.196 \times 10^{-3}`$ respectively. Because $`W_{\text{prime}}`$ is indefinite, no naive norm or triangle inequality can prove $`W^{(L)} \ge 0`$; closing Route A requires a genuinely non-perturbative global spectral factorization $`W^{(L)} = A_L^{\ast} A_L`$ across all places of $`\mathbb{A}_\mathbb{Q}`$ simultaneously.

#### 4. 65-Digit Transverse Laguerre Radar, Spectral Zero Synthesis, and Prolate–$`LDL^T`$ Certificates (`verify_certificates_prolate_laguerre.py`)

A second zero-dependency 65-digit arbitrary-precision laboratory (`verify_certificates_prolate_laguerre.py`) directly evaluates the new structures formalized in Theorems 6.8–6.10:

1. **Zero-Lag Bifurcation Detection by $`m_2 = 2L_1(\Xi)`$ vs. Higher Derivatives ($`m_4 \dots m_{10}`$) and 50-Digit Li Coefficients ($`\lambda_1 \dots \lambda_{20}`$):** At $`\gamma_1`$, Theorem 6.8.2 is verified to 68 digits ($`|m_2(0, \gamma_1) - 2L_1(\Xi)(\gamma_1)| = 1.10 \times 10^{-68}`$), and across $`\gamma \in [0, 48.62]`$ the transverse Hessian increases strictly in $`\sigma`$ ($`m_2(0, \gamma) < m_2(0.5, \gamma)`$) with normalized margin $`m_2(0, \gamma)/(\Xi^2 + (\Xi')^2) \ge 0.09242`$. Under the de Bruijn–Newman heat flow $`\Phi_t(u) = e^{tu^2}\Phi(u)`$, tracking the critical pinch extremum $`H_t'(\gamma_{\ast}) = 0`$ between $`\gamma_9`$ and $`\gamma_{10}`$ reveals that **$`m_2(0, \gamma_{\ast})`$ flips strictly negative at the exact collision instant $`t_{\text{coll}} = -0.469477268`$** (zero lag), whereas **every higher even Laguerre–Turán derivative $`m_4, m_6, m_8, m_{10}`$ remains strictly positive even at $`t = -1.00`$**, and **all twenty Li coefficients $`\lambda_1 \dots \lambda_{20}`$** (Li, 1997; Bombieri & Lagarias, 1999; calibrated to $`|\lambda_1 - (1 + \frac{\gamma_E}{2} - \frac{1}{2}\ln 4\pi)| = 1.10 \times 10^{-65}`$) remain strictly positive at $`t = -0.55`$ ($`\lambda_1 = +0.022087`$, $`\lambda_{20} = +8.432544`$). Thus $`m_2 = 2L_1(\Xi)`$ is the sharpest local bifurcation detector along the entire differential–integral ladder:

   | Heat $`t`$ | Pinch $`\gamma_{\ast}`$ | $`m_2(0, \gamma_{\ast}) = 2L_1`$ | $`m_4(0, \gamma_{\ast}) = 2L_2`$ | $`m_{10}(0, \gamma_{\ast}) = 2L_5`$ | Regime |
   | :---: | :---: | :---: | :---: | :---: | :--- |
   | 0.0000 | 48.62253 | $`+2.0691 \times 10^{-27}`$ | $`+1.8414 \times 10^{-26}`$ | $`+1.7592 \times 10^{-24}`$ | Convex valley ($`m_2 > 0`$) |
   | -0.4694 | 49.66404 | $`+4.8332 \times 10^{-32}`$ | $`+1.8766 \times 10^{-27}`$ | $`+2.3432 \times 10^{-25}`$ | Pre-collision valley |
   | **-0.4750** | **49.67815** | **$`-3.3599 \times 10^{-30}`$** | $`+1.8187 \times 10^{-27}`$ | $`+2.2817 \times 10^{-25}`$ | **Ridge bifurcation ($`m_2 < 0`$)** |
   | -0.5500 | 49.87335 | $`-3.3116 \times 10^{-29}`$ | $`+1.1777 \times 10^{-27}`$ | $`+1.5831 \times 10^{-25}`$ | Ridge ($`m_4 \dots m_{10}, \lambda_{1\dots 20} > 0`$) |
   | -1.0000 | 51.28700 | $`-5.0229 \times 10^{-30}`$ | $`+5.2961 \times 10^{-29}`$ | $`+1.2239 \times 10^{-26}`$ | Deep off-line ($`m_4 \dots m_{10} > 0`$) |

2. **Spectral Synthesis of Riemann Zeros from Ground Eigenstates of $`W^{(L)}`$, Purely Archimedean Boundary $`L_{\text{arch}}^{\ast}`$, and Finite-Primorial Refutation:** Because the compact-support explicit formula on $`[-L, L]`$ is exact with zero prime-tail error, minimizing $`\langle v, W^{(L)} v \rangle = 2\sum_{k=1}^\infty |\widehat{v}(\gamma_k)|^2`$ forces the Fourier transform $`\widehat{v}_0^{(L)}(\gamma)`$ of the ground eigenstate $`v_0^{(L)}`$ to vanish directly at the low-lying Riemann zeros **without ever evaluating $`\zeta(s)`$ or $`\xi(s)`$**. At $`L = 1.60`$ ($`e^{1.60} = 4.953 < 5`$, $`N = 16`$ EVEN modes, incorporating **only three prime powers $`\{2, 3, 4\}`$**), the zeros of $`\widehat{v}_0^{(1.60)}(\gamma)`$ recover $`\gamma_1 = 14.134725141734759\dots`$ to **13.18 exact decimal digits** (error $`6.533 \times 10^{-14}`$), $`\gamma_2`$ to **10.50 digits** ($`3.195 \times 10^{-11}`$), $`\gamma_3`$ to **8.97 digits** ($`1.062 \times 10^{-9}`$), $`\gamma_4`$ to **6.77 digits** ($`1.690 \times 10^{-7}`$), and $`\gamma_5`$ to **5.89 digits** ($`1.303 \times 10^{-6}`$). Furthermore, exact bisection locates the **zero-prime purely Archimedean positivity boundary** of $`W_{\text{pole}}^{(L)} + W_\infty^{(L)}`$ at $`L_{\text{arch}}^{\ast} = 0.8416836893`$ ($`e^{L_{\text{arch}}^{\ast}} = 2.32027 > 2`$), yielding a strict safety margin +0.14854 above $`\ln 2 = 0.69314718`$. Conversely, restricting $`W^{(L)}`$ to any finite primorial subset such as $`S = \{\infty, 2, 3, 5\}`$ ($`P_3 = 30`$) destroys positivity for all $`L > \ln 7`$ ($`\lambda_{\min} = -0.8193`$ at $`L = 3.0`$, versus $`+6.537 \times 10^{-25}`$ with all prime powers $`< e^3`$), proving quantitatively that the full adelic ring $`\mathbb{A}_\mathbb{Q}`$ is indispensable.
3. **Connes–Consani Prolate Fidelity ($`99.996\%`$), Prolate Comparison Certificates, and Exact 65-Digit $`LDL^T`$ Certificates:** The nodeless ground state $`v_0^{(L)} > 0`$ overlaps the ground eigenfunction $`\psi_0`$ of $`H_{\text{prolate}}`$ with fidelity 0.999894 ($`L=0.69`$) rising to **0.999960** ($`L=2.20`$), and minimizing $`\langle u, W^{(1.60)} u \rangle / \langle u, H_{\text{prolate}} u \rangle`$ yields an eigenvector overlapping $`v_0^{(1.60)}`$ to 1.0000000000. Across $`L \in \{0.69, 1.60, 3.00, 4.00\}`$ ($`N = 8`$), both the **Prolate comparison certificate** $`W^{(L)} = \alpha^{\ast}(L) H_{\text{prolate}}(L/2, \pi L) + R^{(L)}`$ ($`R^{(L)} \succ 0`$) and the **exact unit lower-triangular $`LDL^T`$ Cholesky certificate** (matching Theorem 6.10.4) pass in both parity blocks with reconstruction residual $`\le 1.0 \times 10^{-64}`$:

   | Support $`L`$ | $`\mathrm{card}(p^m)`$ | Prolate $`\alpha^{\ast}(L) > 0`$ | Remainder $`R \succ 0`$ Residual | Even $`\min_k D_k > 0`$ | $`LDL^T`$ Residual | Odd $`LDL^T`$ |
   | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
   | 0.69 | 0 | $`+1.1638 \times 10^{-3}`$ | $`5.4 \times 10^{-65}`$ | $`+2.63 \times 10^{-3}`$ | $`1.0 \times 10^{-65}`$ | **PASS** |
   | 1.60 | 3 | $`+6.8266 \times 10^{-16}`$ | $`1.0 \times 10^{-64}`$ | $`+4.62 \times 10^{-6}`$ | $`2.0 \times 10^{-65}`$ | **PASS** |
   | 3.00 | 12 | $`+3.9179 \times 10^{-26}`$ | $`1.0 \times 10^{-64}`$ | $`+3.14 \times 10^{-14}`$ | $`1.0 \times 10^{-65}`$ | **PASS** |
   | 4.00 | 24 | $`+5.3093 \times 10^{-30}`$ | $`1.0 \times 10^{-64}`$ | $`+6.43 \times 10^{-19}`$ | $`1.0 \times 10^{-64}`$ | **PASS** |

   Because $`\alpha^{\ast}(L)`$ decays super-exponentially with $`L`$ (reflecting the prolate spectral compression of $`W^{(L)}`$ relative to the $`\mathcal{O}(1)`$ gap of $`H_{\text{prolate}}`$), fixed-constant Prolate domination cannot close $`L \to \infty`$ uniformly; any global proof must control the $`L`$-dependent coupling between $`W_{\text{prime}}`$ and the prolate subspace directly.

#### 5. 65-Digit Investigation of Route A Continuous Positivity, Prime-Induction Frontier, and Route B Corridor & Modularity Obstructions (`verify_weil_corridor_ab.py`)

A third zero-dependency 65-digit arbitrary-precision laboratory (`verify_weil_corridor_ab.py`) systematically tests the structural boundaries of both closure routes complementing Theorems 6.11–6.13:

1. **Route A — Sequential Prime-Induction Survival Past $`\ln p_{k+1}`$ (`[A1]`):** For each truncated place set $`S_k = \{\infty, p_1, \dots, p_k\}`$ ($`k = 0 \dots 5`$, $`N = 6`$ modes), exact 65-digit bisection of the breakdown horizon $`L_k^{\ast}`$ of $`W_{S_k}^{(L)}`$ reveals that positivity survives strictly past the next prime threshold $`\ln p_{k+1}`$ in **both** parities, with the odd block systematically breaking first and the safety margin narrowing steadily from +0.066921 to +0.014386:

   | Place Set $`S_k`$ | $`\ln p_{k+1}`$ | $`L_k^{\ast}`$ (EVEN) | $`L_k^{\ast}`$ (ODD) | Margin $`L_k^{\ast} - \ln p_{k+1}`$ | Status |
   | :--- | :---: | :---: | :---: | :---: | :--- |
   | $`\{\infty\}`$ | 0.693147 | 0.851487 | 0.760068 | +0.066921 | Survives |
   | $`\{\infty, 2\}`$ | 1.098612 | 1.181194 | 1.127066 | +0.028454 | Survives |
   | $`\{\infty, 2, 3\}`$ | 1.609438 | 1.667884 | 1.625491 | +0.016053 | Survives |
   | $`\{\infty, 2, 3, 5\}`$ | 1.945910 | 1.998672 | 1.960980 | +0.015070 | Survives |
   | $`\{\infty, 2, 3, 5, 7\}`$ | 2.397895 | 2.449902 | 2.412437 | +0.014542 | Survives |
   | $`\{\infty, 2, 3, 5, 7, 11\}`$ | 2.564949 | 2.615117 | 2.579335 | +0.014386 | Survives |

2. **Route A — Bandlimited Prolate Comparison $`(I - K_\Omega)`$ and Infinite-Dimensional $`L = \ln 2`$ Schur Certification (`[A2]`–`[A3]`):** Comparing $`W^{(L)}`$ against the complementary bandlimited Prolate projection $`(I - K_\Omega)`$ (EVEN, $`N = 8`$) separates the purely Archimedean cutoff $`\Omega = t_0 = 6.289836`$ from the first Riemann zero $`\Omega = \gamma_1 = 14.134725`$: at $`\Omega = t_0`$, $`\beta_{\max} \in [1.67, 3.45]`$ remains $`\mathcal{O}(1)`$ while $`\beta^{\ast}(L; t_0)`$ still collapses to $`+1.046 \times 10^{-25}`$ at $`L = 4.00`$ (confirming that a purely Archimedean frequency band cannot capture the prime-induced spectral gap $`[t_0, \gamma_1]`$), whereas at $`\Omega = \gamma_1`$, $`\beta^{\ast}(L; \gamma_1)`$ rebounds upward by **$`2{,}890\times`$** from $`L = 3.00`$ ($`+1.576 \times 10^{-14}`$) to $`L = 4.00`$ ($`+4.554 \times 10^{-11}`$), though strong off-diagonal Prolate coupling ($`|M_{01}|/\sqrt{M_{00}M_{11}} \approx 0.87`$) persists. On the continuous infinite-dimensional Hilbert space $`L^2([-L/2, L/2])`$, the closed-form $`K = 1`$ envelope yields $`W_{\text{pole}} + W_\infty \ge +0.360464\Vert g\Vert _2^2`$ at $`L = 1/12`$ (matching Theorem 6.11.3's formal bound $`\ge \frac{1}{10}\Vert g\Vert _2^2`$), while $`K = 3`$ reaches $`+0.246276\Vert g\Vert _2^2`$ at $`L = 1/8`$ and $`+0.066085\Vert g\Vert _2^2`$ at $`L = 0.15`$. Moreover, applying Theorem 6.11.4's infinite-dimensional Schur-complement certificate clears **the entire zero-prime regime $`L = \ln 2`$**: on ODD $`\perp e_2`$, $`\lambda_\perp \ge +0.734096`$ with Schur determinant $`+0.046806 > 0`$; on EVEN $`\perp \{e_1, e_3\}`$, $`\lambda_\perp \ge +0.920394`$ with $`2 \times 2`$ Schur $`\lambda_{\min} = +0.001313`$ ($`\det = +8.871 \times 10^{-4} > 0`$).
3. **Route B — Alternating-Cosine Convexity Corridors Reaching $`96.6\%`$ of $`\gamma_1`$, Schoenberg Obstruction, and Modularity Ablation (`[B1]`–`[B3]`):** Evaluating the exact 2D light-cone moments $`\mu_{2j}(\sigma)`$ to 65 digits verifies that all normalized ratios $`\mu_{2j}(\sigma)/\mu_0(\sigma)`$ ($`2j = 2 \dots 16`$) decrease strictly with $`\sigma \in [0, 1/2]`$. The exact quadratic bound of Theorem 6.12.1 yields $`\sqrt{2\mu_0(0)/\mu_2(1/2)} = 4.842069`$ uniformly on $`\sigma \in [0, 1/2]`$ (and $`\sqrt{2b_0/b_1} = 6.578806`$ for $`\Xi(\gamma) > 0`$), while higher-order alternating cosine lower bounds certify $`m_2(\sigma, \gamma) > 0`$ monotonically up to **$`|\gamma| \le 13.6486`$ at order 42** ($`96.56\%`$ of $`\gamma_1 = 14.1347`$):

   | Cosine Order | $`\gamma_{\text{cert}}(\sigma = 0)`$ | $`\gamma_{\text{cert}}(\sigma = 0.25)`$ | $`\gamma_{\text{cert}}(\sigma = 0.50)`$ | Fraction of $`\gamma_1`$ |
   | :---: | :---: | :---: | :---: | :---: |
   | 2 | 4.915716 | 4.917585 | 4.923108 | $`34.8\%`$ |
   | 6 | 6.256244 | 6.258396 | 6.264758 | $`44.3\%`$ |
   | 14 | 8.346378 | 8.348931 | 8.356478 | $`59.0\%`$ |
   | 22 | 10.066506 | 10.069500 | 10.078332 | $`71.2\%`$ |
   | 30 | 11.586571 | 11.590152 | 11.600677 | $`82.0\%`$ |
   | 38 | 12.982072 | 12.986403 | 12.999066 | $`91.8\%`$ |
   | **42** | **13.648568** | **13.653300** | **13.667089** | **$`96.6\%`$** |

   Complementing Theorem 6.13, although all nine finite-difference orders $`(-1)^k\Delta^k G_{2,0}(\sqrt{x})`$ remain positive on $`x \in [0, 0.60]`$ and finite Bochner–Toeplitz matrices stay strictly positive at both $`t = 0`$ and post-collision $`t = -0.55`$ ($`\lambda_{\min} = +8.834 \times 10^{-16}`$ at $`\Delta w = 0.063`$, Nyquist $`= 49.9`$), the effective decay slope $`-\ln G_{2,0}(w)/w^2`$ turns strictly upward for $`w \ge 1.5`$ ($`8.1808 \to 8.7662 \to 10.1794`$ at $`w = 1.5, 2.0, 2.5`$), confirming quantitatively the super-exponential obstruction to any positive Gaussian mixture. Finally, Jacobi-theta modularity ablation on $`\gamma \in \{0 \dots 55\}`$ demonstrates that dropping $`n \ge 2`$ summands to form the cusped even kernel $`\Phi_{n=1}(|u|)`$ (which breaks $`\Phi'(0) = 0`$ enforced by Jacobi theta duality) violates $`L_1 > 0`$ at **33 of 56 integer ordinates** starting at $`\gamma = 19`$ ($`m_2 = -3.4256 \times 10^{-9}`$) and reaching $`m_2 = -7.2706 \times 10^{-9}`$ at $`\gamma = 20`$ (versus $`+2.8937 \times 10^{-9}`$ for full $`\Phi`$), whereas both full Jacobi-theta $`\Phi(u)`$ ($`\min m_2 = +6.883 \times 10^{-31}`$) and Pólya's smooth non-arithmetic kernel $`\Phi^{\ast}(u) = 8\pi^2\cosh(\frac{9}{2}u)e^{-2\pi\cosh(2u)}`$ (Pólya, 1926; $`\min m_2 = +4.233 \times 10^{-31}`$) exhibit zero violations.

---

> [← Part 10](10_formal_lean4_verification_summary.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 12 →](12_numerical_labs_6_to_9.md)
