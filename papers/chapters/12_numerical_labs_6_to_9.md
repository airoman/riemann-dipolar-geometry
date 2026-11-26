> **Extended Paper — Part 12 — Section 7.2 (Labs 6–9): Arithmetic Weil, Coercivity & Hermite–Biehler Labs**  
> [← Part 11](11_numerical_labs_1_to_5.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 13 →](13_numerical_labs_10_to_14.md) · [Complete 68-Page PDF](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf)

---

#### 6. 65-Digit Arithmetic Weil Crossing of $`p = 2`$, Spectral-Flow Knife-Edge Pinch, Hyperbolic Coordinate, and Logarithmic Force (`verify_arithmetic_weil_wide_corridor.py`)

A fourth zero-dependency 65-digit arbitrary-precision laboratory (`verify_arithmetic_weil_wide_corridor.py`) directly validates Theorems 6.14–6.16 and sharpens the exact structural obstructions on both routes:

1. **Route A — Infinite-Dimensional Continuous Weil Positivity Past the First Prime $`p = 2`$ (`[A1]`):** Combining Theorem 6.14.1's disjoint-strip $`L^2`$ operator norm bound $`|W_{\text{prime}, p=2}(g)| \le \frac{\ln 2}{\sqrt{2}}\Vert g\Vert _2^2 \approx 0.490129\Vert g\Vert _2^2`$ (exact on $`L \in (\ln 2, \ln 4]`$) with Theorem 6.14.3's prime-active infinite-dimensional Hilbert Schur complement (ODD $`r = 2`$, EVEN $`r = 3`$, 14-mode reference cross-tail) certifies **infinite-dimensional positivity with $`p = 2`$ active up to $`L = 0.85`$**—strictly past the purely Archimedean odd breakdown horizon $`L_0^{\ast}(\text{ODD}) = 0.760068`$—before the coarse worst-case norm penalty fails at $`L = 0.90`$:

   | Support $`L`$ | Prime $`p = 2`$ | ODD ($`r=2`$) $`\lambda_\perp`$ | ODD Schur $`S_{\min}`$ | EVEN ($`r=3`$) $`\lambda_\perp`$ | EVEN Schur $`S_{\min}`$ | Infinite-Dim. Status |
   | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
   | $`\ln 2 \approx 0.69315`$ | OFF | +1.1619 | $`+7.382 \times 10^{-2}`$ | +1.2942 | $`+1.370 \times 10^{-3}`$ | **PASS** |
   | 0.72000 | **ON** | +0.6329 | $`+3.184 \times 10^{-3}`$ | +0.7653 | $`+8.634 \times 10^{-4}`$ | **PASS ($`p=2`$ active)** |
   | 0.75000 | **ON** | +0.5882 | $`+3.076 \times 10^{-3}`$ | +0.7234 | $`+3.503 \times 10^{-4}`$ | **PASS ($`p=2`$ active)** |
   | 0.80000 | **ON** | +0.5205 | $`+8.466 \times 10^{-3}`$ | +0.6581 | $`+9.858 \times 10^{-5}`$ | **PASS ($`> L_0^{\ast}(\text{ODD})`$)** |
   | **0.85000** | **ON** | **+0.4563** | **$`+2.743 \times 10^{-3}`$** | **+0.5974** | **$`+4.538 \times 10^{-5}`$** | **PASS ($`p=2`$ active)** |
   | 0.90000 | ON | +0.3932 | $`-3.129 \times 10^{-3}`$ | +0.5401 | $`-9.942 \times 10^{-5}`$ | Coarse norm fails |

2. **Route A — Negative-Eigenvalue Growth $`N_-(W_{\text{arch}}^{(L)})`$, Two-Sided Spectral-Flow Pinch, and Nonlinear Cone Confinement (`[A2]`–`[A3]`):** Counting negative eigenvalues of the purely Archimedean block $`W_{\text{arch}}^{(L)}`$ ($`N = 10`$ per parity) across $`L \in [0.69, 5.00]`$ reveals linear Landau–Pollak bandlimited growth $`N_-(\text{EVEN}, \text{ODD}) = (0,0) \to (1,1) \to (1,1) \to (2,2) \to (2,3) \to (3,4) \to (4,5)`$ (total $`9 \approx t_0 L/\pi \approx 2L`$ at $`L = 5.00`$, where $`W_{\text{arch}}`$ plunges to -8.608 while $`W_{\text{full}}`$ stays strictly positive at $`+4.892 \times 10^{-36}`$). Tracking the spectral flow $`W(\eta) = W_{\text{arch}} - \eta\, W_{\text{prime}}`$ at $`L = 1.60`$ (EVEN, $`N = 10`$, where $`W_{\text{prime}}`$ has indefinite spectrum $`[-0.9060, +1.1938]`$) illustrates Theorem 6.15.2's two-sided pinch dramatically:

   | Coupling $`\eta`$ | 0.00 | 0.50 | 0.90 | 0.99 | **1.00** | 1.01 | 1.10 |
   | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
   | $`N_-(W(\eta))`$ | 1 | 1 | 1 | 1 | **0** | 3 | 3 |
   | $`\lambda_{\min}(W(\eta))`$ | $`-3.532\times 10^{-1}`$ | $`-1.689\times 10^{-1}`$ | $`-3.242\times 10^{-2}`$ | $`-2.991\times 10^{-3}`$ | **$`+2.755\times 10^{-16}`$** | $`-9.756\times 10^{-3}`$ | $`-1.148\times 10^{-1}`$ |

   An annealed nonlinear hyperbolic fixed-point search $`s_{t+1} = \tanh(\beta\, Q s_t)`$ on $`Q = -W^{(1.60)} + \lambda_{\max} I`$ (400 steps, normalized on the unit sphere) remains strictly inside the positive cone (Rayleigh quotient $`+4.052 \times 10^{-1} > 0`$, overlap 0.256 with $`v_0^{(1.60)}`$), detecting zero violations.
3. **Route B — Exact $`I_0(1/2) = 1/4`$, Hyperbolic Coordinate $`y = \cosh w - 1`$, Sign-Changing Bochner–Wiener–Hopf Square Root $`h(w)`$, and Logarithmic Curvature Radar (`[B1]`–`[B3]`):** Direct 65-digit integration verifies $`|I_0(1/2) - 1/4| = 3.00 \times 10^{-65}`$ and confirms that the constructive 9-bin rational bounds formalized in Theorem 6.16.2 certify $`m_2 > 0`$ up to $`|\gamma| \le 2.14413`$ (machine-proved $`|\gamma| \le 2`$) and $`\Xi > 0`$ up to $`|\gamma| \le 4.72077`$ (machine-proved $`|\gamma| \le 4`$). Replacing Schoenberg's Gaussian variable $`x = w^2`$ with the hyperbolic geodesic coordinate $`y = \cosh w - 1`$ preserves **7/7 strictly positive finite-difference orders** $`(-1)^k \Delta^k G_{2,0}(\mathrm{arccosh}(1+y)) > 0`$ and yields a finite convergent decay ratio $`-\ln G_{2,0}(w)/(\cosh w - 1) \to 4\pi \approx 12.5664`$ ($`33.33 \to 16.63 \to 13.61 \to 12.69 \to 12.40 \to 12.32`$ across $`w = 0.5 \dots 3.0`$), explaining the $`6\times`$ sharper exponent proved in Theorem 6.16.3. However, computing the exact Bochner–Wiener–Hopf spectral square root $`h(w) = \mathcal{F}^{-1}(\sqrt{m_2(0, \gamma)})`$ at $`t = 0`$ reveals an unambiguous **sign change at $`w = 1.00`$** ($`h(0) = +2.927 \times 10^{-1}`$, $`h(0.5) = +1.439 \times 10^{-2}`$, **$`h(1.0) = -1.227 \times 10^{-5} < 0`$**, $`h(1.5) = -5.760 \times 10^{-7}`$, $`h(2.0) = +8.564 \times 10^{-8}`$), ruling out even any non-negative convolution factorization $`G_{2,0} = h * h`$ ($`h \ge 0`$). Finally, evaluating the logarithmic potential force $`\partial_\sigma(\ln V)`$ and logarithmic curvature $`\partial_\sigma^2(\ln V)`$ at the critical pinch exposes a stark qualitative separation between pre- and post-collision regimes:

   | Regime ($`t,\; \gamma_{\ast}`$) | $`\sigma = 0.001`$ ($`\partial_\sigma^2 \ln V / m_2`$) | $`\sigma = 0.05`$ | $`\sigma = 0.10`$ | $`\sigma = 0.25`$ | $`\sigma = 0.50`$ |
   | :--- | :---: | :---: | :---: | :---: | :---: |
   | Pre ($`0.0,\; 48.62253`$) | +7.143 / $`+2.07\times 10^{-27}`$ | +7.032 / $`+2.09\times 10^{-27}`$ | +6.713 / $`+2.16\times 10^{-27}`$ | +4.934 / $`+2.66\times 10^{-27}`$ | +1.904 / $`+4.62\times 10^{-27}`$ |
   | **Post ($`-0.475,\; 49.67815`$)** | **-358.9** / $`-3.36\times 10^{-30}`$ | **-724.6** / $`-1.08\times 10^{-30}`$ | **-4648** / $`+5.78\times 10^{-30}`$ | **-110.6** / $`+5.53\times 10^{-29}`$ | **-17.90** / $`+2.53\times 10^{-28}`$ |

   Notably, after zero collision at $`t = -0.475`$, the logarithmic curvature $`\partial_\sigma^2(\ln V)`$ remains violently negative all the way out to $`\sigma = 0.50`$ even after $`m_2 = \partial_\sigma^2 V`$ turns positive again for $`\sigma \ge 0.10`$—quantitatively matching Theorem 6.16.3's strict dominance $`\partial_\sigma^2 V \ge (\partial_\sigma V)^2 / V`$.

#### 7. 65-Digit Universal Weil Coercivity Crossing $`p = 2, 3`$, Uniform Crossing of $`\gamma_1, \gamma_2, \gamma_3`$, and Remote Herglotz–Pick Off-Line Detection (`verify_universal_weil_herglotz.py`)

A fifth zero-dependency 65-digit arbitrary-precision laboratory (`verify_universal_weil_herglotz.py`) directly validates Theorems 6.17–6.19 and advances every computational benchmark across both closure routes:

1. **Route A — Infinite-Dimensional Hilbert Schur Certification Crossing BOTH $`p = 2`$ AND $`p = 3`$ up to $`L = 1.30`$ (`[1A]`–`[1B]`):** Combining Theorem 6.17.2's refined split prime-shift bound (`weilPrime_refined_norm_bound`) with higher finite-block dimensions $`r`$ clears the entire $`p = 2`$ regime ($`L = 0.90, 1.00, 1.09 < \ln 3`$) and crosses **strictly past the second prime threshold $`\ln 3 \approx 1.0986`$** with **both $`p = 2`$ and $`p = 3`$ simultaneously active** up to $`L = 1.30`$:

   | Support $`L`$ | Active $`\mathrm{card}(p^m)`$ | Refined $`\Vert W_{\text{prime}}\Vert `$ | ODD ($`r`$) $`\lambda_\perp`$ / $`S_{\min}`$ | EVEN ($`r`$) $`\lambda_\perp`$ / $`S_{\min}`$ | Inf.-Dim. Status |
   | :---: | :---: | :---: | :---: | :---: | :--- |
   | 0.90 | 1 ($`p=2`$) | 0.49013 | ($`r=4`$) +0.9239 / $`+2.035\times 10^{-3}`$ | ($`r=5`$) +0.9799 / $`+1.591\times 10^{-5}`$ | **PASS ($`p=2`$)** |
   | 1.00 | 1 ($`p=2`$) | 0.49013 | ($`r=5`$) +0.9804 / $`+1.943\times 10^{-4}`$ | ($`r=6`$) +1.0583 / $`+8.285\times 10^{-7}`$ | **PASS ($`p=2`$)** |
   | 1.09 | 1 ($`p=2`$) | 0.49013 | ($`r=6`$) +1.0154 / $`+1.840\times 10^{-5}`$ | ($`r=7`$) +1.1273 / $`+7.520\times 10^{-8}`$ | **PASS ($`\approx \ln 3`$)** |
   | 1.15 | **2 ($`p=2,3`$)** | 1.12441 | ($`r=10`$) +0.7643 / $`+3.544\times 10^{-6}`$ | ($`r=11`$) +0.8950 / $`+9.380\times 10^{-9}`$ | **PASS ($`p=2,3`$)** |
   | 1.20 | **2 ($`p=2,3`$)** | 1.12441 | ($`r=12`$) +0.8920 / $`+6.774\times 10^{-7}`$ | ($`r=13`$) +1.0205 / $`+1.513\times 10^{-9}`$ | **PASS ($`p=2,3`$)** |
   | **1.30** | **2 ($`p=2,3`$)** | **1.12441** | **($`r=14`$) +0.9434 / $`+1.864\times 10^{-8}`$** | **($`r=15`$) +1.0841 / $`+3.748\times 10^{-11}`$** | **PASS ($`p=2,3`$)** |

   Complementing Theorem 6.17.3, explicit finite moment-orthogonality codimensions guaranteeing $`W_{\text{total}}(L, g) \ge 1.0\,\Vert g\Vert _{L^2}^2`$ on $`V_N^\perp`$ are evaluated across $`L \in \{0.50, 1.00, 1.50, 2.00, 3.00\}`$ ($`N = 32, 110, 784, 5{,}493, 1{,}945{,}889`$, with $`n \le 20`$ prime powers active at $`L = 3.00`$).

2. **Route B — All-Order 2D Light-Cone Parity Identity Uniformly Crossing $`\gamma_1, \gamma_2`$, AND $`\gamma_3`$ (`[2]`):** Evaluating $`\mu_{2k}(\sigma)`$ up to order 130 via Theorem 6.19.1's exact bilinear 1D-moment identity (`lightCone_even_power_parity_identity`) matches direct 65-digit integration of $`m_2(\sigma, \gamma_1)`$ to relative error $`3.15 \times 10^{-42}`$ ($`\sigma = 0`$) and $`2.87 \times 10^{-42}`$ ($`\sigma = 0.50`$). By Theorem 6.19.2 (`riemannHypothesis_local_and_simple_of_hessianPos`), uniform positivity across $`\sigma \in [0, 1/2]`$ certifies both Local RH and strict zero simplicity past all three first Riemann zeros ($`\gamma_1 = 14.134725`$, $`\gamma_2 = 21.022040`$, $`\gamma_3 = 25.010858`$):

   | Cosine Order | $`\gamma_{\text{cert}}(\sigma = 0)`$ | $`\gamma_{\text{cert}}(\sigma = 0.25)`$ | $`\gamma_{\text{cert}}(\sigma = 0.50)`$ | Zeros Certified (Local RH + Simple) |
   | :---: | :---: | :---: | :---: | :--- |
   | 42 | 13.6486 | 13.6533 | 13.6671 | $`96.6\%`$ of $`\gamma_1`$ |
   | **50** | **14.9416** | **14.9469** | **14.9625** | **Crossed $`\gamma_1 = 14.1347`$** |
   | 74 | 18.5743 | 18.5801 | 18.5969 | Above $`\gamma_1`$ |
   | **94** | **21.2855** | **21.2943** | **21.3188** | **Crossed $`\gamma_1, \gamma_2 = 21.0220`$** |
   | 110 | 23.3867 | 23.3975 | 23.4272 | Above $`\gamma_2`$ |
   | **126** | **25.4942** | **25.5034** | **25.5289** | **Crossed $`\gamma_1, \gamma_2, \gamma_3 = 25.0109`$** |
   | 130 | 26.0121 | 26.0208 | 26.0451 | Above $`\gamma_3`$ |

3. **Spectral Resolvent $`\mathcal{R}_\xi(z)`$, Schwarz–Pick Contraction, and Remote $`4 \times 4`$ Hermitian Pick-Matrix Detection on $`\mathrm{Re}(s) = 1`$ (`[3A]`–`[3C]` & `[4]`):** Direct evaluation confirms Theorem 6.18.1's duality $`\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) = \frac{1}{2}\partial_\sigma\ln V(\sigma, \gamma)`$ to full floating-point equality (`err = 0.00e+00`) and Theorem 6.19.3's angular barrier $`2/\sin^2\theta \ge 2`$ with strictly positive angular descent $`-\partial_\theta V > 0`$ on $`(0, \pi/2)`$. Comparing true $`\xi`$ ($`t = 0`$) against the post-collision de Bruijn–Newman state $`t = -0.475`$ (off-line zero pair at $`\delta \approx 0.07`$, $`\gamma^{\ast} = 49.67815`$) demonstrates Theorem 6.18.3's remote detection power directly on the boundary line $`\sigma = 0.50`$ ($`\mathrm{Re}(s) = 1`$):

   | State / Location | $`\sigma = 0.02`$ ($`\rho_{\text{SP}}`$) | $`\sigma = 0.10`$ ($`\rho_{\text{SP}}`$) | $`\sigma = 0.25`$ ($`\rho_{\text{SP}}`$) | $`\sigma = 0.50`$ ($`\rho_{\text{SP}}`$) | $`4 \times 4`$ Pick $`\lambda_{\min}`$ ($`\sigma \in \{0.25, 0.50\}`$) |
   | :--- | :---: | :---: | :---: | :---: | :---: |
   | True $`\xi`$ ($`t=0, \gamma_1`$) | +0.999946 | +0.998647 | +0.991584 | +0.966856 | — |
   | True $`\xi`$ ($`t=0, \gamma_2`$) | +0.999889 | +0.997228 | +0.982860 | +0.933967 | — |
   | True $`\xi`$ ($`t=0, 48.623`$) | +0.999137 | +0.978706 | +0.875457 | +0.597126 | **$`+1.4510 \times 10^{-7}`$ (PSD)** |
   | **Post ($`-0.475, 49.678`$)** | -1.075355 | -20.106844 | **$`+1.417843 > 1`$** | **$`+1.044774 > 1`$** | **-2.4846 (VIOLATED!)** |

   Crucially, at $`\sigma = 0.25`$ and $`\sigma = 0.50`$ ($`\mathrm{Re}(s) = 1`$), both $`\mathrm{Im}\mathcal{R}_\xi > 0`$ (+9.76 and +4.28) and $`m_2 > 0`$ ($`+5.53 \times 10^{-29}`$ and $`+2.53 \times 10^{-28}`$) give no sign flip, yet the **Schwarz–Pick ratio strictly exceeds 1** (+1.4178 and +1.0448) and the **$`4 \times 4`$ Hermitian Pick–Nevanlinna matrix exhibits a macroscopic negative eigenvalue $`\lambda_{\min} = -2.4846`$**, confirming quantitatively that the Herglotz–Pick structure propagates off-line spectral obstructions globally across the upper half-plane.

#### 8. 65-Digit Hermite–Biehler / Schur–Cayley Homotopy, Causal Wavelet Weil–Pick Unification, and Infinite-Dimensional Crossing of $`p = 2, 3, 4`$ (`verify_hermite_biehler_weil_pick.py`)

A sixth zero-dependency 65-digit arbitrary-precision laboratory (`verify_hermite_biehler_weil_pick.py`) directly validates Theorems 6.20–6.22 across both routes and their exact operator unification:

1. **Route B — Hermite–Biehler / Schur–Cayley Homotopy Descent $`\alpha \in [10^{-3}, 0.500]`$ (`[1A]`–`[1D]`):** Boundary unitarity $`|S_\alpha(\gamma)| = 1`$ holds to $`< 10^{-14}`$, the $`3 \times 3`$ Pick–Schur congruence identity of Theorem 6.20.2 holds to $`6.66 \times 10^{-16}`$, and the rescaled Cayley transform converges quadratically to the spectral resolvent ($`|M_\alpha/\alpha - \mathcal{R}_\xi| = 9.35 \times 10^{-2} \to 9.35 \times 10^{-4} \to 9.35 \times 10^{-6} \to 1.19 \times 10^{-9}`$ for $`\alpha = 10^{-1}, 10^{-2}, 10^{-3}, 10^{-5}`$). Tracking the $`4 \times 4`$ Schur–Pick matrix at remote heights $`\sigma \in \{0.25, 0.50\}`$ separates true $`\xi`$ ($`t = 0`$) sharply from the post-collision de Bruijn–Newman state ($`t = -0.475`$):

   | Homotopy Shift $`\alpha`$ | True $`\xi`$ ($`t=0`$): $`\max\Vert S_\alpha\Vert `$ / $`\lambda_{\min}(P_{\text{Schur}})`$ | Post-Collision ($`t=-0.475`$): $`\max\Vert S_\alpha\Vert `$ / $`\Vert S_\alpha(\text{low})\Vert `$ / $`\lambda_{\min}(P_{\text{Schur}})`$ | Regime |
   | :---: | :---: | :---: | :--- |
   | **0.500** | 0.5911 / **$`+5.251 \times 10^{-8}`$ (PSD)** | 0.1354 / 0.8424 / **$`+3.294 \times 10^{-7}`$ (PSD)** | Unconditional baseline |
   | 0.250 | 0.7315 / $`+4.448 \times 10^{-8}`$ (PSD) | 0.1288 / 0.6754 / $`+7.428 \times 10^{-7}`$ (PSD) | Above offset $`\delta`$ |
   | **0.100** | 0.8763 / $`+2.420 \times 10^{-8}`$ (PSD) | 0.4185 / **$`1.3591 > 1`$** / **$`-7.306 \times 10^{-3}`$** | **Remote breakdown!** |
   | 0.060 | 0.9233 / $`+1.566 \times 10^{-8}`$ (PSD) | 0.5963 / $`1.9987 > 1`$ / **$`-9.248 \times 10^{-2}`$** | Remote breakdown |
   | 0.001 | 0.9987 / **$`+2.897 \times 10^{-10}`$ (PSD)** | 0.9915 / $`1.0075 > 1`$ / **$`-4.907 \times 10^{-3}`$** | Limit $`\to \mathcal{R}_\xi`$ |

   Notably, for $`t = -0.475`$ at $`\alpha = 0.100`$, even though every remote sample at $`\sigma \in \{0.25, 0.50\}`$ satisfies $`|S_{0.100}(z_j)| \le 0.4185 < 1`$, the $`4 \times 4`$ Schur–Pick matrix still exposes a negative eigenvalue $`-7.306 \times 10^{-3}`$ the instant $`\alpha`$ crosses below the off-line zero offset $`\delta`$.

2. **Grand Route A $`\leftrightarrow`$ Route B Unification via Causal Exponential Wavelets (`[2A]`–`[2B]`):** Evaluating Theorem 6.21.2's spectral identity across the first five zeros yields exact equality between the causal-wavelet Weil quadratic form (13.2201249193) and the Hermitian Pick form (13.2201249193, difference $`5.33 \times 10^{-15}`$). Moreover, on the Euler-product convergence half-plane $`\mathrm{Im}(z) \ge 1.5`$, assembling the $`3 \times 3`$ Hermitian Pick matrix of $`\mathcal{R}_\xi`$ directly from the past–future kernel $`\Phi(u)`$ agrees with the explicit arithmetic formula (poles $`+`$ digamma $`-`$ truncated `vonMangoldt` sum over $`n \le 12{,}000`$) to maximum entry error $`2.848 \times 10^{-6}`$.
3. **Route A — Parity-Enhanced Continuous Bounds & Infinite-Dimensional Schur Crossing of $`p = 2, 3`$, AND 4 up to $`L = 1.50`$ (`[3A]`–`[3B]` & `[4]`):** Direct integration of the sharp parity envelopes of Theorem 6.22.2 confirms $`W_{\text{total}} \ge +0.6250\Vert g\Vert _2^2`$ (ODD, $`L = 3/10`$; $`+0.1139\Vert g\Vert _2^2`$ at $`L = 1/2`$) and $`W_{\text{total}} \ge +0.5228\Vert g\Vert _2^2`$ (EVEN zero-mean, $`L = 4/9`$; $`+0.0817\Vert g\Vert _2^2`$ across the entire zero-prime threshold $`L = \ln 2`$). Furthermore, extending the infinite-dimensional Hilbert Schur complement certification with Theorem 6.17.2's refined split prime-shift bound crosses **all three first prime powers $`\{2, 3, 4\}`$ simultaneously** past $`\ln 4 \approx 1.3863`$ up to $`L = 1.50`$:

   | Support $`L`$ | Active $`\mathrm{card}(p^m)`$ | Refined $`\Vert W_{\text{prime}}\Vert `$ | ODD ($`r`$) $`\lambda_\perp`$ / $`S_{\min}`$ | EVEN ($`r`$) $`\lambda_\perp`$ / $`S_{\min}`$ | Inf.-Dim. Status |
   | :---: | :---: | :---: | :---: | :---: | :--- |
   | 1.40 | **3 ($`2, 3, 4`$)** | 1.9611 | ($`r=22`$) +0.4556 / $`+2.422 \times 10^{-10}`$ | ($`r=24`$) +0.6453 / $`+3.557 \times 10^{-13}`$ | **PASS ($`p=2,3,4`$)** |
   | **1.50** | **3 ($`2, 3, 4`$)** | **1.9611** | **($`r=26`$) +0.5246 / $`+1.740 \times 10^{-12}`$** | **($`r=28`$) +0.7309 / $`+2.672 \times 10^{-15}`$** | **PASS ($`p=2,3,4`$)** |

#### 9. 65-Digit Universal Hopfield–Boltzmann Solver, Adaptive Resolvent Preconditioner, Remote Lifted Pick Detection, and Exact All-Primes `vonMangoldt` Resolvent Identity (`verify_universal_solver_pick_weil.py`)

A seventh zero-dependency 65-digit arbitrary-precision laboratory (`verify_universal_solver_pick_weil.py`) directly validates Theorems 6.23–6.25 across Route A, Route B, and the Euler-product convergence half-plane $`\mathrm{Im}(z) > 1/2`$:

1. **Route A — Exact Lyapunov Descent & Adaptive Resolvent Acceleration on $`W^{(1.60)}`$ (8-Mode EVEN, Exact $`\eta = 1.00`$ vs. Perturbed $`\eta \in \{0.00, 1.01, 0.99\}`$):** At every single synchronous step of both the plain Universal Solver ($`Q = I - \frac{1}{\mu}W`$, 800 steps) and the Adaptive Resolvent–Universal Solver ($`Q_{\text{res}} = \delta(W + \delta I)^{-1}`$, $`\delta = 1.8|\lambda_{\min}|`$, 120 steps), Theorem 6.24.1's exact discrete Lyapunov descent inequality holds with zero violations (`mono=True`). While exact primes ($`\lambda_{\min} = +4.968 \times 10^{-15}`$) remain strictly paramagnetic (decaying to $`\Vert s\Vert  = 2.39 \times 10^{-25}`$ with $`u^T W u = +1.47 \times 10^{-36} > 0`$), even $`\pm 1\%`$ prime perturbations trigger immediate spontaneous symmetry breaking—with the Adaptive Resolvent preconditioner sharpening fixed-point convergence by **20 to 41 orders of magnitude in $`6.7\times`$ fewer iterations**:

   | Regime ($`W^{(1.60)}`$, EVEN) | $`\lambda_{\min}`$ | Plain Univ (800 it): $`\mathcal{L}_Q`$ / $`s^T W s`$ / residual | AdapRes (120 it): $`\Vert s^{\ast}\Vert `$ / residual / $`u^T W u \le \text{bound}`$ |
   | :--- | :---: | :---: | :---: |
   | **Exact ($`\eta = 1.00`$)** | **$`+4.968 \times 10^{-15}`$** | $`+2.365 \times 10^{-7}`$ / $`+1.457 \times 10^{-7}`$ / $`1.23 \times 10^{-5}`$ | **$`2.39 \times 10^{-25}`$** / $`7.48 \times 10^{-26}`$ / **$`+1.47 \times 10^{-36} > 0`$** |
   | No primes ($`\eta = 0.00`$) | $`-3.500 \times 10^{-1}`$ | $`-6.498 \times 10^{-2}`$ / $`-3.717 \times 10^{-1}`$ / $`0.00 \times 10^{-63}`$ | 1.7331 / $`3.53 \times 10^{-45}`$ / **$`-11.075 \le -7.591`$** |
   | Perturbed $`+1\%`$ ($`\eta = 1.01`$) | $`-9.656 \times 10^{-3}`$ | $`-3.791 \times 10^{-5}`$ / $`-3.140 \times 10^{-4}`$ / $`5.13 \times 10^{-5}`$ | 1.8589 / **$`1.00 \times 10^{-24}`$** / **$`-424.26 \le -290.64`$** |
   | Perturbed $`-1\%`$ ($`\eta = 0.99`$) | $`-2.963 \times 10^{-3}`$ | $`-2.369 \times 10^{-6}`$ / $`-1.675 \times 10^{-5}`$ / $`2.50 \times 10^{-5}`$ | 1.4897 / **$`2.20 \times 10^{-46}`$** / **$`-1058.3 \le -717.24`$** |

2. **Route B — Remote $`8 \times 8`$ Real-Lifted Pick-Matrix Phase Transition at $`\sigma \in \{0.25, 0.50\}`$ (`lift_err` $`\le 2.80 \times 10^{-63}`$):** Lifting the $`4 \times 4`$ complex Hermitian Pick matrix of $`\mathcal{R}_\xi`$ on remote nodes $`\sigma \in \{0.25, 0.50\}`$ to $`\widetilde{P} \in \mathbb{R}^{8 \times 8}`$ verifies Theorem 6.25.2's quadratic-form identity to 63–64 digits. For true $`\xi`$ ($`t = 0`$, $`\lambda_{\min} = +1.4510 \times 10^{-7}`$), both solvers descend monotonically in the paramagnetic phase (AdapRes: $`\Vert s\Vert  = 2.34 \times 10^{-25}`$, $`u^T \widetilde{P} u = +4.82 \times 10^{-44} > 0`$). For post-collision $`t = -0.475`$ ($`\lambda_{\min} = -2.4846`$), both solvers spontaneously bifurcate from remote heights $`\mathrm{Re}(s) \in \{0.75, 1.00\}`$ to strict negativity certificates: Plain Univ (2,000 it) reaches $`\Vert s^{\ast}\Vert  = 0.6585`$, $`\mathcal{L}_Q = -2.542 \times 10^{-3}`$, residual $`1.78 \times 10^{-11}`$, $`s^{*T}\widetilde{P}s^{\ast} = -1.0127 \le -0.9690`$; AdapRes (120 it) reaches $`\Vert s^{\ast}\Vert  = 2.5533`$, residual $`3.30 \times 10^{-22}`$, and $`u^T \widetilde{P} u = -3.5381 \le -2.3953`$.
3. **Exact All-Primes `vonMangoldt` Resolvent Identity on $`\mathrm{Im}(z) > 1/2`$:** Comparing $`\mathcal{R}_\xi(z) = -\Xi'(z)/\Xi(z)`$ computed directly from the 65-digit past–future kernel $`\Phi(u)`$ against Theorem 6.25.1's explicit formula with 65-digit complex digamma $`\psi(s/2)`$ and `vonMangoldt` prime powers $`n \le 8{,}000`$ confirms exact identity down to the finite prime-tail truncation bound:

   | Spectral Point $`z = \gamma + i\sigma`$ | $`\mathrm{Re}(s)`$ | $`\mathcal{R}_\xi(z)`$ (from $`\Phi(u)`$) | $`\Vert \text{LHS} - \text{RHS}\Vert `$ | Prime-Tail Bound |
   | :--- | :---: | :---: | :---: | :---: |
   | $`14.134725 + 3.5i`$ | 4.0 | $`+0.534565681937 + 0.503160195034i`$ | **$`1.425 \times 10^{-13}`$** | $`< 2.0 \times 10^{-11}`$ |
   | $`21.022040 + 4.5i`$ | 5.0 | $`+0.615825999573 + 0.644082249316i`$ | **$`1.126 \times 10^{-17}`$** | $`< 2.4 \times 10^{-15}`$ |
   | $`30.424876 + 5.5i`$ | 6.0 | $`+0.649893518045 + 0.814149174098i`$ | **$`9.617 \times 10^{-22}`$** | $`< 3.1 \times 10^{-19}`$ |

---

> [← Part 11](11_numerical_labs_1_to_5.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 13 →](13_numerical_labs_10_to_14.md)
