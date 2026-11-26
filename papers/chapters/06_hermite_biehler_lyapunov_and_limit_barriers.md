> **Extended Paper — Part 6 — Sections 6.11–6.13: Hermite–Biehler Homotopy, Lyapunov Solver & Limit Barriers**  
> [← Part 5](05_prolate_weil_corridor_and_herglotz_pick.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 7 →](07_geodesic_renormalization_and_kuramoto.md) · [Complete 68-Page PDF](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf)

---

### 6.11 Hermite–Biehler / Schur–Cayley Homotopy, Causal Wavelet Weil–Pick Unification, and Parity-Decoupled Continuous Weil Positivity

To embed the spectral resolvent $`\mathcal{R}_\xi(z)`$ inside a continuous homotopy starting from an unconditionally holomorphic strip-boundary baseline, establish an exact operator unification between Route A (Weil positivity) and Route B (Herglotz–Pick resolvent positivity), and extend zero-discretization continuous arithmetic Weil positivity across wider support horizons, `HermiteBiehlerHomotopyAndWeilPick.lean` (**1,781 lines, 17 headline theorems**, `0 sorry`, axioms strictly `[propext, Classical.choice, Quot.sound]`) establishes three further unconditional theorem groups directly in Lean 4 + Mathlib4:

#### Theorem 6.20 (Route B — Hermite–Biehler / Schur–Cayley Homotopy $`E_\alpha, S_\alpha, M_\alpha`$ for $`\alpha \in (0, 1/2]`$)
*For each shift parameter $`\alpha \in \mathbb{R}`$, define the shifted entire function $`E_\alpha(z) \triangleq \xi(\frac{1}{2} + \alpha - iz)`$, its Schwarz conjugate $`E_\alpha^{\sharp}(z) \triangleq \xi(\frac{1}{2} + \alpha + iz)`$, the Schur scattering ratio $`S_\alpha(z) \triangleq E_\alpha^{\sharp}(z)/E_\alpha(z)`$ (Schur, 1917; de Branges, 1968), and the Cayley–Herglotz transform $`M_\alpha(z) \triangleq i\,\frac{1 - S_\alpha(z)}{1 + S_\alpha(z)}`$. Then in Lean 4 + Mathlib4 (`HermiteBiehlerHomotopyAndWeilPick.lean`):*

1. *(Exact Schwarz Conjugation, Boundary Unitarity, & Potential Duality — `xiShiftE_schwarz_and_boundary_unitary`):* For every $`\alpha \in \mathbb{R}`$ and $`z \in \mathbb{C}`$, $`E_\alpha^{\sharp}(z) = \overline{E_\alpha(\bar{z})} = \xi(\frac{1}{2} - \alpha - iz)`$, $`\Vert S_\alpha(\gamma)\Vert  = 1`$ identically on $`\mathbb{R}`$ wherever $`E_\alpha(\gamma) \neq 0`$, and at $`z = \gamma + i\sigma`$:

```math
\Vert E_\alpha(\gamma + i\sigma)\Vert ^2 = V(\alpha + \sigma, \gamma), \qquad \Vert E_\alpha^{\sharp}(\gamma + i\sigma)\Vert ^2 = V(\alpha - \sigma, \gamma).
```

2. *(Exact Cayley–Schur Equivalence & All-Order Pick–Schur Congruence — `cayley_schur_iff_herglotz`, `pickMatrix_cayley_schur_congruence`):* For every $`w \in \mathbb{C}`$ with $`1 + w \neq 0`$, $`\mathrm{Im}\big(i\frac{1 - w}{1 + w}\big) = \frac{1 - \Vert w\Vert ^2}{\Vert 1 + w\Vert ^2}`$, so $`\Vert w\Vert  < 1 \iff \mathrm{Im}\big(i\frac{1 - w}{1 + w}\big) > 0`$. Moreover, for any $`n \in \mathbb{N}`$ and $`\tilde{c}_j \triangleq c_j / (1 + S_j)`$,

```math
\sum_{j,k=1}^n c_j\,\overline{c_k}\,\frac{M_j - \overline{M_k}}{z_j - \overline{z_k}} = 2\sum_{j,k=1}^n \tilde{c}_j\,\overline{\tilde{c}_k}\,\frac{1 - S_j\overline{S_k}}{-i(z_j - \overline{z_k})},
```

   proving that the $`n \times n`$ Herglotz–Pick matrix of $`M_\alpha`$ is positive semi-definite if and only if the $`n \times n`$ Schur–Pick matrix of $`S_\alpha`$ is positive semi-definite.
3. *(Unconditional Strip-Boundary Baseline at $`\alpha = 1/2`$, Zero-Free Strip Exclusion, Infinitesimal Limit, & Quartet Converse — `xiShiftE_half_zeroFree_uhp`, `zeroFreeStrip_of_hermiteBiehler`, `riemannHypothesis_of_hermiteBiehler_all`, `xiCayley_div_alpha_tendsto_xiResolvent`, `finiteStripQuartet_hermiteBiehler_exact_threshold`):*
   - At $`\alpha = 1/2`$, $`E_{1/2}(z) = \xi(1 - iz) \neq 0`$ for every $`z`$ in the closed upper half-plane $`\mathrm{Im}(z) \ge 0`$, so $`S_{1/2}(z) = \xi(1 + iz)/\xi(1 - iz)`$ is **unconditionally pole-free on $`\overline{\mathbb{H}}`$**;
   - For any $`\alpha > 0`$, the strict Hermite–Biehler inequality $`\Vert E_\alpha^{\sharp}(\gamma + i\sigma)\Vert  < \Vert E_\alpha(\gamma + i\sigma)\Vert `$ on $`\mathbb{H}`$ excludes every zero of $`\xi(s)`$ in $`|\mathrm{Re}(s) - 1/2| > \alpha`$, and its survival across all $`\alpha \in (0, 1/2)`$ implies Mathlib4's official `RiemannHypothesis` unconditionally;
   - At every $`z`$ where $`\xi(\frac{1}{2} - iz) \neq 0`$, $`\lim_{\alpha \to 0} \frac{M_\alpha(z)}{\alpha} = \mathcal{R}_\xi(z) = i\,(\xi'/\xi)(\frac{1}{2} - iz)`$, identifying $`\mathcal{R}_\xi`$ as the exact infinitesimal generator of the homotopy;
   - Conversely, for every nonempty finite real-symmetric strip quartet product $`Q(s) = \prod_{m \in I} \big((s - \frac{1}{2} - \delta_m)^2 + \gamma_m^2\big)\big((s - \frac{1}{2} + \delta_m)^2 + \gamma_m^2\big)`$ with $`|\delta_m| \le \Delta`$, strict Hermite–Biehler holds for **every $`\alpha > \Delta`$** (unconditionally at $`\alpha = 1/2`$ whenever $`\Delta < 1/2`$, and for every $`\alpha > 0`$ on the critical line $`\Delta = 0`$). ■

#### Theorem 6.21 (Grand Route A $`\leftrightarrow`$ Route B Unification — Causal Exponential Wavelets & Weil–Pick Identity)
*For each $`z \in \mathbb{H}`$ ($`\mathrm{Im}(z) > 0`$), define the causal future-only exponential wavelet $`g_z(u) \triangleq e^{izu}\,\mathbf{1}_{u \ge 0}`$. Then in Lean 4 + Mathlib4 (`HermiteBiehlerHomotopyAndWeilPick.lean`):*

1. *(Exact Laplace–Fourier & Cross-Correlation Kernels — `causalWavelet_fourier_eq_resolvent_kernel`, `causalWavelet_autocorrelation_eq`):* For every $`z, z_1, z_2 \in \mathbb{H}`$, $`t \in \mathbb{R}`$, and $`u \ge 0`$,

```math
\int_0^\infty g_z(u)\,e^{-itu}\,du = \frac{-i}{t - z}, \qquad \int_0^\infty \overline{g_{z_1}(v)}\,g_{z_2}(v + u)\,dv = \frac{i}{z_2 - \overline{z_1}}\,e^{iz_2 u}.
```

2. *(Exact Causal Wavelet Weil–Pick Unification Identity — `weilSpectralSum_causalWavelet_eq_pickForm`):* For any finite real spectral family $`\{(\gamma_m, w_m)\}_{m \in I}`$, any $`z_1, \dots, z_n \in \mathbb{H}`$, and any weights $`c_1, \dots, c_n \in \mathbb{C}`$, evaluating the Weil spectral quadratic form on the causal wavelet superposition $`g(u) = \sum_{j=1}^n c_j\,g_{z_j}(u)`$ equals **identically** the Hermitian Pick–Nevanlinna quadratic form of the resolvent $`G(z) = \sum_{m \in I} \frac{w_m}{\gamma_m - z}`$:

```math
\sum_{m \in I} w_m \left\Vert \sum_{j=1}^n c_j \int_0^\infty g_{z_j}(u)\,e^{-i\gamma_m u}\,du\right\Vert ^2 = \mathrm{Re}\sum_{j,k=1}^n \overline{c_j}\,c_k\,\frac{G(z_k) - \overline{G(z_j)}}{z_k - \overline{z_j}}.
```

   Thus Route A (Weil positivity on compactly supported test functions) and Route B (Hermitian Pick–Nevanlinna positivity of the spectral resolvent) are exact restrictions of the same global quadratic form to compactly supported vs. causal exponential test subspaces. ■

#### Theorem 6.22 (Route A Continuous Even–Odd Decoupling & Parity-Enhanced Zero-Discretization Positivity; Route B Order-6 Cosine Bound)
*In Lean 4 + Mathlib4 (`HermiteBiehlerHomotopyAndWeilPick.lean`), advancing both routes unconditionally:*

1. *(Exact Continuous Even–Odd Decoupling of $`W_{\text{total}}`$ for ALL $`L > 0`$ — `weilTotal_even_odd_decouple`):* For **every $`L > 0`$** (including all active `vonMangoldt` prime-shift terms), every continuous even $`g_e`$, and every continuous odd $`g_o`$ obeying Archimedean integrability, the pole, Archimedean, and prime-shift functionals all decouple orthogonally without remainder:

```math
W_{\text{total}}(L, g_e + g_o) = W_{\text{total}}(L, g_e) + W_{\text{total}}(L, g_o).
```

2. *(Sharp Parity Fourier Suppression & Wider Zero-Discretization Positivity — `compactFourier_odd_norm_sq_le`, `compactFourier_even_zeroMean_norm_sq_le`, `weilTotal_continuous_pos_odd_up_to_three_tenths`, `weilTotal_continuous_pos_even_zeroMean_up_to_four_ninths`):* Every continuous odd $`g`$ on $`[-L/2, L/2]`$ satisfies $`\Vert \widehat{g}(t)\Vert ^2 \le \min\big(L, \frac{L^3 t^2}{12}\big)\Vert g\Vert _{L^2}^2`$, and every continuous even zero-mean $`g`$ ($`\int_{-L/2}^{L/2} g = 0`$) satisfies $`\Vert \widehat{g}(t)\Vert ^2 \le \min\big(L, \frac{L^5 t^4}{320}\big)\Vert g\Vert _{L^2}^2`$. Combining these sharp parity envelopes with piecewise rational bounds on $`\psi_{\text{lb}3}(16) - \psi_{\text{lb}3}(t)`$ proves **with zero discretization**:
   - $`W_{\text{total}}(L, g) \ge \frac{1}{100}\Vert g\Vert _{L^2}^2`$ for all continuous odd $`g`$ on $`0 < L \le \frac{3}{10}`$ (**$`2.4\times`$ wider** than Theorem 6.14.2's $`L \le \frac{1}{8}`$);
   - $`W_{\text{total}}(L, g) \ge \frac{1}{25}\Vert g\Vert _{L^2}^2`$ for all continuous even zero-mean $`g`$ on $`0 < L \le \frac{4}{9}`$ (**$`3.56\times`$ wider** than $`L \le \frac{1}{8}`$).
3. *(Exact Order-6 Global Cosine Lower Bound — `cos_ge_taylor_six`):* For every $`x \in \mathbb{R}`$, $`1 - \frac{x^2}{2} + \frac{x^4}{24} - \frac{x^6}{720} \le \cos x`$, directly underpinning higher-order alternating-cosine light-cone corridors on Route B. ■

### 6.12 Universal Hopfield–Boltzmann Solver Lyapunov Theory, Adaptive Resolvent Preconditioner, and Exact All-Primes `vonMangoldt` Resolvent Bridge

To test whether continuous hyperbolic fixed-point dynamics of the Hopfield–Boltzmann type $`s^{(t+1)} = \tanh(\beta(Q s^{(t)} + B))`$ (Hopfield, 1984) coupled with its integral free-energy potential, Bregman convexity derivative, and shifted-resolvent preconditioner can certify or refute Pick–Weil positivity across both closure routes without false positives, the fourteenth Lean 4 + Mathlib4 module (`UniversalSolverLyapunovAndPrimeResolvent.lean`, 969 lines, 16 public theorems, `0 sorry`, axioms strictly `[propext, Classical.choice, Quot.sound]`) establishes the complete variational, dynamical, and arithmetic-resolvent bridge:

#### Theorem 6.23 (Exact Binary Entropy Barrier, Quartic Bounds, and 1-Strong Bregman Convexity)
*For $`x \in (-1, 1)`$, define $`\mathrm{artanh}(x) \triangleq \frac{1}{2}\ln\big(\frac{1+x}{1-x}\big)`$ and the Legendre dual binary entropy barrier $`\Phi_{\text{ent}}(x) \triangleq \frac{1+x}{2}\ln(1+x) + \frac{1-x}{2}\ln(1-x) = \int_0^x \mathrm{artanh}(u)\,du`$. Then unconditionally in Lean 4 + Mathlib4:*

1. *(Exact Bijection & Derivatives — `tanh_abs_lt_one`, `artanh_tanh_eq`, `tanh_artanh_eq`, `hasDerivAt_artanh`, `hasDerivAt_binEntropy`):* $`|\tanh y| < 1`$ for all $`y \in \mathbb{R}`$; $`\mathrm{artanh}(\tanh y) = y`$ and $`\tanh(\mathrm{artanh} x) = x`$ for $`|x| < 1`$; $`\frac{d}{dx}\mathrm{artanh}(x) = \frac{1}{1 - x^2} \ge 1`$ and $`\frac{d}{dx}\Phi_{\text{ent}}(x) = \mathrm{artanh}(x)`$ on $`(-1, 1)`$.
2. *(Sharp Global Quartic Barriers — `artanh_mul_sub_sq_ge_quartic`, `binEntropy_sub_half_sq_ge_quartic`):* For every $`x \in (-1, 1)`$,

```math
x\mathrm{artanh}(x) - x^2 \ge \frac{x^4}{3}, \qquad \Phi_{\text{ent}}(x) - \frac{x^2}{2} \ge \frac{x^4}{12}.
```

3. *(Exact 1-Strong Bregman Convexity — `binEntropy_bregman_ge_half_sq`):* For every $`x, y \in (-1, 1)`$,

```math
\Phi_{\text{ent}}(x) - \Phi_{\text{ent}}(y) - \mathrm{artanh}(y)(x - y) \ge \frac{1}{2}(x - y)^2. \quad \blacksquare
```

#### Theorem 6.24 (Exact Discrete Lyapunov Descent, Phase-Transition Equivalence, and Adaptive Resolvent–Universal Preconditioner)
*For any symmetric real matrix $`W \in \mathbb{R}^{N \times N}`$, spectral scale $`\mu > 0`$, shifted coupling $`Q \triangleq I - \frac{1}{\mu}W`$, and Boltzmann–Hopfield free energy $`\mathcal{L}_Q(s) \triangleq -\frac{1}{2}s^T Q s + \sum_{i=1}^N \Phi_{\text{ent}}(s_i) = \frac{1}{2\mu}s^T W s + \sum_{i=1}^N \big(\Phi_{\text{ent}}(s_i) - \frac{1}{2}s_i^2\big)`$, the following hold unconditionally in Lean 4 + Mathlib4:*

1. *(Exact Discrete Lyapunov Descent & Period-2 Exclusion — `universalSolver_exact_lyapunov_descent`):* For every symmetric PSD coupling $`Q \succeq 0`$ and every state $`s \in (-1, 1)^N`$, one synchronous update $`s' = \tanh(Q s)`$ satisfies

```math
\mathcal{L}_Q(s') + \frac{1}{2}(s' - s)^T Q(s' - s) + \frac{1}{2}\Vert s' - s\Vert _2^2 \le \mathcal{L}_Q(s).
```

   In particular, $`\mathcal{L}_Q`$ decreases strictly along every non-stationary step and admits no period-2 limit cycles.
2. *(Zero-False-Positive Fixed-Point Negativity Witness & Paramagnetic Uniqueness — `universalSolver_neg_witness_of_nonzero_fixedPoint`, `universalSolver_unique_zero_of_psd`):* Every fixed point $`s = \tanh\big((I - \frac{1}{\mu}W)s\big)`$ obeys

```math
s^T W s \le -\frac{\mu}{3}\sum_{i=1}^N s_i^4.
```

   Consequently, any non-zero fixed point ($`s \neq 0`$) certifies $`s^T W s < 0`$ with zero false positives, whereas $`W \succeq 0`$ forces $`\mathcal{L}_Q(s) \ge \frac{1}{12}\sum_{i=1}^N s_i^4 > 0`$ on $`(-1, 1)^N \setminus \{0\}`$ and makes $`s = 0`$ the unique fixed point.
3. *(Exact Biconditional Phase-Transition Equivalence — `universalSolver_psd_iff_freeEnergy_nonneg`):* For every matrix $`W`$ and every $`\mu > 0`$,

```math
\big(\forall v \in \mathbb{R}^N,\; v^T W v \ge 0\big) \iff \big(\forall s \in (-1, 1)^N,\; \mathcal{L}_{I - (1/\mu)W}(s) \ge 0\big).
```

4. *(Adaptive Resolvent–Universal Preconditioner — `adaptiveResolventUniversal_neg_witness_and_unique_zero`, `adaptiveResolventUniversal_unique_zero_of_psd`):* To eliminate critical slowing down when $`|\lambda_{\min}(W)| \ll \mu`$, replace $`I - \frac{1}{\mu}W`$ by the shifted resolvent coupling $`Q_{\text{res}}(\delta) \triangleq \delta(W + \delta I)^{-1}`$ ($`\delta > 0`$), which maps negative modes $`\lambda \in (-\delta, 0)`$ to $`\frac{\delta}{\delta + \lambda} > 1`$ while keeping $`Q_{\text{res}}(\delta) \succ 0`$ (hence preserving exact Lyapunov descent whenever $`\delta > \max(0, -\lambda_{\min}(W))`$). For every pair $`(s, u)`$ solving $`(W + \delta I)u = s`$ and $`s = \tanh(\delta u)`$, the resolvent-mapped vector $`u = (W + \delta I)^{-1} s`$ obeys the amplified strict negativity certificate

```math
u^T W u \le -\frac{1}{\delta}\Vert W u\Vert _2^2 - \frac{1}{3\delta}\sum_{i=1}^N s_i^4.
```

   Thus $`W \succeq 0`$ enforces $`s = u = 0`$ uniquely for every $`\delta > 0`$, while any non-zero fixed point certifies $`u^T W u < 0`$. ■

#### Theorem 6.25 (Exact All-Primes `vonMangoldt` Resolvent Identity and Real-Lifted Hermitian Pick Equivalence)
*Unconditionally in Lean 4 + Mathlib4 (`UniversalSolverLyapunovAndPrimeResolvent.lean`):*

1. *(Exact All-Primes `vonMangoldt` Resolvent Bridge on $`\mathrm{Im}(z) > 1/2`$ — `xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im`):* For every $`z \in \mathbb{C}`$ with $`\mathrm{Im}(z) > 1/2`$ (equivalently $`s = \frac{1}{2} - iz`$ lies in the absolute Euler-product half-plane $`\mathrm{Re}(s) > 1`$), Mathlib4's `LSeries ↗ArithmeticFunction.vonMangoldt` and `Complex.digamma` connect all infinitely many primes directly to the spectral resolvent:

```math
\mathcal{R}_\xi(z) = i\left(\frac{1}{s} + \frac{1}{s - 1} - \frac{1}{2}\ln\pi + \frac{1}{2}\psi\!\left(\frac{s}{2}\right) - \sum_{n=1}^\infty \frac{\Lambda(n)}{n^s}\right).
```

2. *(Real-Lifted Hermitian Pick Equivalence — `universalSolver_realLifted_pick_iff_hermitian_psd`):* For every $`n \times n`$ complex Hermitian matrix $`P`$ (in particular any Pick–Nevanlinna matrix $`P_{jk} = \frac{\mathcal{R}_\xi(z_j) - \overline{\mathcal{R}_\xi(z_k)}}{z_j - \overline{z_k}}`$ or Schur–Pick matrix of $`S_\alpha`$) and its $`2n \times 2n`$ real symmetric lifting $`\widetilde{P} = \begin{pmatrix} \mathrm{Re} P & -\mathrm{Im} P \\ \mathrm{Im} P & \mathrm{Re} P \end{pmatrix}`$, the following three conditions are **100% logically equivalent** for every $`\mu > 0`$:

```math
P \succeq_{\text{Herm}} 0 \iff \widetilde{P} \succeq_{\mathbb{R}} 0 \iff \forall s \in (-1, 1)^{2n},\; \mathcal{L}_{I - (1/\mu)\widetilde{P}}(s) \ge 0.
```

   *Epistemological boundary:* Theorems 6.23–6.25 establish an exact, non-perturbative, Lyapunov-monotone phase-transition oracle for **every** finite-dimensional Weil truncation $`W^{(L)}`$ and **every** finite $`n \times n`$ Pick–Nevanlinna or Schur–Pick matrix. However, because every dynamical solver evaluation acts on a finite-dimensional operator ($`L < \infty`$ or $`n < \infty`$), while the Two-Sided Spectral-Flow Pinch (Theorem 6.15.2) and finite-primorial refutations show that global Pick–Weil positivity depends simultaneously on all infinitely many primes across all heights $`\gamma \in \mathbb{R}`$, no finite-horizon solver run by itself closes the infinite-dimensional Clay Millennium equivalence without an analytic global factorization $`W^{(L)} = A_L^{\ast} A_L`$ or global Pick-positivity extension from $`\mathrm{Im}(z) > 1/2`$ down to $`\mathbb{H}`$. ■

### 6.13 Exact Limit Barriers on Routes A and B, de Branges Boundary Phase Synthesis, and Log-Concave Kernel Obstruction

To characterize precisely how far each closure pathway can be pushed using purely analytic, operator-norm, and differential–integral techniques—and to establish exact unconditional mathematical walls separating local/finite-prime methods from the global Millennium equivalence—Module #15 (`RouteABLimitBarriersAndDeBrangesSynthesis.lean`, 1,650 lines, 16 public theorems, axioms strictly `[propext, Classical.choice, Quot.sound]`) formalizes both the sharp positive advances and the exact no-go barriers on Routes A and B simultaneously.

#### Theorem 6.26 (Route A Global Archimedean Upper Bound, Finite-Prime Impossibility Wall, and Exponential Prime-Cancellation Necessity)
*Unconditionally in Lean 4 + Mathlib4 (`RouteABLimitBarriersAndDeBrangesSynthesis.lean`):*

1. *(Global Archimedean Upper Bound — `archimedeanWeilConst_gt_four`, `psiArch_le_half_sq`):* The Archimedean constant satisfies $`4 < C_\infty = \gamma_{\text{E}} + \ln(8\pi) + \frac{\pi}{2}`$, and the Archimedean spectral symbol satisfies the global quadratic envelope

```math
\psi_{\text{arch}}(t) = -C_\infty + \sum_{n=0}^\infty \frac{t^2/4}{(n + 1/4)\big((n + 1/4)^2 + t^2/4\big)} \le \frac{t^2}{2} \qquad (\forall t \in \mathbb{R}).
```

2. *(Exact Odd Dirichlet Mode Pole and Universal Archimedean Ceiling — `oddSinMode_L2_norm_sq`, `oddSinMode_weilPole_exact`, `oddSinMode_compactFourier_norm_sq_le`, `oddSinMode_weilArch_upper`):* For every $`L > 0`$, the explicit continuous odd Dirichlet mode $`g_L(x) = \sin(2\pi x / L)`$ on $`[-L/2, L/2]`$ satisfies $`\Vert g_L\Vert _{L^2}^2 = L/2`$, has exact Fourier modulus

```math
\left|\widehat{g}_L(t)\right| = \left|\frac{4\pi L \sin(Lt/2)}{4\pi^2 - L^2 t^2}\right| \qquad \left(t \neq \pm \frac{2\pi}{L}\right),
```

   yields the exact exponentially negative pole quadratic form

```math
W_{\text{pole}}(L, g_L) = -\frac{32\pi^2 L^2}{(L^2/4 + 4\pi^2)^2}\sinh^2\!\left(\frac{L}{4}\right) < 0,
```

   and satisfies the universal vanishing-Rayleigh Archimedean ceiling

```math
W_\infty(L, g_L) = \frac{1}{2\pi}\int_{-\infty}^{\infty} \psi_{\text{arch}}(t)\left|\widehat{g}_L(t)\right|^2 dt \le \frac{90}{L} = \frac{180}{L^2}\,\Vert g_L\Vert _{L^2}^2.
```

3. *(Route A Finite-Prime Impossibility Wall — `weilTruncated_finitePrimes_eventually_neg`):* Let $`W_{\text{prime}, \le N_{\max}}(L, g)`$ denote the arithmetic prime-shift functional truncated at any fixed finite cutoff $`N_{\max} \in \mathbb{N}`$. For **every** $`N_{\max} \in \mathbb{N}`$—regardless of how large—there exists an explicit horizon $`L_0 = \max\!\big(100,\, M(N_{\max}) + 1000\big) > 0`$ (where $`M(N_{\max}) = 2\sum_{n=2}^{N_{\max}} \Lambda(n)/\sqrt{n}`$) such that for **every** $`L \ge L_0`$:

```math
W_{\text{pole}}(L, g_L) + W_\infty(L, g_L) - W_{\text{prime}, \le N_{\max}}(L, g_L) < 0.
```

   Hence **no** finite subset of primes and **no** bounded-norm perturbation of the Archimedean operator can ever sustain Weil positivity globally across all horizons $`L > 0`$.
4. *(Exponential Prime-Cancellation Necessity of RH on Route A — `weilTotal_pos_forces_exponential_prime_cancellation`):* For every $`L > 0`$, non-negativity of the full arithmetic Weil functional $`W_{\text{total}}(L, g_L) \ge 0`$ unconditionally forces the infinite `vonMangoldt` prime-shift operator to deliver exponentially growing negative cancellation compensating the pole:

```math
-\frac{W_{\text{prime}}(L, g_L)}{\Vert g_L\Vert _{L^2}^2} \ge \frac{64\pi^2 L}{(L^2/4 + 4\pi^2)^2}\sinh^2\!\left(\frac{L}{4}\right) - \frac{180}{L^2} \sim \frac{16\pi^2}{L^3}\,e^{L/2}.
```

   Analytically, this is the exact operator reflection of the Prime Number Theorem: the macro-term $`dx`$ in $`d\psi(x) = dx + d(\psi(x) - x)`$ cancels the pole density $`e^{u/2} + e^{-u/2}`$ identically, leaving RH governed entirely by the subtle oscillatory prime-fluctuation integral. ■

#### Theorem 6.27 (Route B Exact Schur–Potential Modulus Biconditional, de Branges Boundary Phase-Velocity Closed Loop, and Unconditional Corridor Contraction)
*Unconditionally in Lean 4 + Mathlib4 (`RouteABLimitBarriersAndDeBrangesSynthesis.lean`):*

1. *(Exact Hermite–Biehler Schur Modulus = Transverse Potential Ratio — `xiSchur_norm_sq_eq_xiNormSq_ratio`):* For every $`\alpha, \sigma, \gamma \in \mathbb{R}`$, the shifted Hermite–Biehler pair $`E_\alpha(z) = \xi(1/2 + \alpha - iz)`$ and $`E_\alpha^{\sharp}(z) = \xi(1/2 + \alpha + iz)`$ satisfies identically

```math
\Vert E_\alpha^{\sharp}(\gamma + i\sigma)\Vert ^2 = V(|\sigma - \alpha|,\, \gamma), \qquad \Vert E_\alpha(\gamma + i\sigma)\Vert ^2 = V(\sigma + \alpha,\, \gamma),
```

   and hence whenever $`E_\alpha(\gamma + i\sigma) \neq 0`$:

```math
\Vert S_\alpha(\gamma + i\sigma)\Vert ^2 = \frac{V(|\sigma - \alpha|,\, \gamma)}{V(\sigma + \alpha,\, \gamma)}.
```

2. *(Exact Global Biconditional Equivalence — `hermiteBiehler_all_iff_xiNormSq_strictMono_all`):* Strict Hermite–Biehler Schur contraction across all shifts $`\alpha > 0`$ and all upper half-plane points $`\gamma + i\sigma`$ ($`\sigma > 0`$) is **100% logically equivalent** to strict transverse monotonicity of $`V(\cdot, \gamma)`$ on $`[0, \infty)`$ for every $`\gamma \in \mathbb{R}`$ (with explicit midpoint inversion $`\alpha = (s_2 - s_1)/2`$, $`\sigma = (s_2 + s_1)/2`$), and implies Mathlib4's official `RiemannHypothesis`:

```math
\Big(\forall \alpha > 0,\, \forall \sigma > 0,\, \forall \gamma \in \mathbb{R},\; \Vert E_\alpha^{\sharp}(\gamma + i\sigma)\Vert  < \Vert E_\alpha(\gamma + i\sigma)\Vert \Big) \iff \Big(\forall \gamma \in \mathbb{R},\; \mathrm{StrictMonoOn}\big(V(\cdot, \gamma),\, [0, \infty)\big)\Big) \implies \mathrm{RH}.
```

3. *(Exact de Branges Boundary Phase-Velocity Closed Loop on $`\mathbb{R}`$ — `xiSchur_boundary_logDeriv_eq_I_mul_logForce`):* For every $`\alpha, \gamma \in \mathbb{R}`$ with $`E_\alpha(\gamma) \neq 0`$, the complex logarithmic derivative of the unimodular boundary Schur function $`S_\alpha(\gamma) = e^{i\phi_\alpha(\gamma)}`$ along the real axis is **purely imaginary** and unifies the entire differential–integral ladder (logarithmic potential force, Schur modulus, de Branges boundary phase velocity $`\phi_\alpha'(\gamma)`$, spectral resolvent $`\mathcal{R}_\xi`$, and integrated density of states):

```math
\mathrm{logDeriv} S_\alpha(\gamma) = i \cdot 2\mathrm{Im}\mathcal{R}_\xi(\gamma + i\alpha) = i\,\partial_\sigma\ln V(\alpha, \gamma).
```

4. *(Unconditional Constructive Corridor Herglotz Positivity, Schur Contraction, and Positive Phase Velocity — `xiResolvent_herglotz_and_schur_contraction_on_corridor_two`):* Upgrading Theorem 6.16.2 unconditionally across the entire explicit corridor $`|\gamma| \le 2`$:
   - $`\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) > 0`$ for every $`\sigma \in (0, 1/2]`$ (Herglotz positivity);
   - $`\Vert S_\alpha(\gamma + i\sigma)\Vert  < 1`$ for every $`\alpha > 0, \sigma > 0`$ with $`\alpha + \sigma \le 1/2`$ (strict Schur contraction);
   - $`\mathrm{Im}\big(\mathrm{logDeriv} S_\alpha(\gamma)\big) > 0`$ for every $`\alpha \in (0, 1/2]`$ (strictly monotone de Branges boundary phase). ■

#### Theorem 6.28 (Route B Exact Log-Concave Decreasing Kernel Wall / No-Go Theorem)
*Unconditionally in Lean 4 + Mathlib4 (`RouteABLimitBarriersAndDeBrangesSynthesis.lean`):*

Consider the explicit elementary kernel

```math
K_{\text{wall}}(u) \triangleq (5 + 2u^2 + u^4)\,e^{-u^2} \qquad (u \in \mathbb{R}).
```

1. *(Every Standard Analytic Kernel Property Holds Globally — `wallKernel_pos_even_antitone_logConcave`, `wallKernel_hankel_psd`):* $`K_{\text{wall}}`$ is strictly positive ($`K_{\text{wall}}(u) > 0`$), even ($`K_{\text{wall}}(-u) = K_{\text{wall}}(u)`$), $`C^\infty`$, **strictly decreasing** on $`[0, \infty)`$ ($`K_{\text{wall}}'(u) = -2u(3 + u^4)e^{-u^2} < 0`$ for $`u > 0`$), **strictly log-concave on ALL of $`\mathbb{R}`$**:

```math
\frac{d^2}{du^2}\ln K_{\text{wall}}(u) = \frac{-28 - 2(1 - 3u^2)^2 - 14u^4 - 12u^6 - 2u^8}{(5 + 2u^2 + u^4)^2} \le -\frac{28}{(5 + 2u^2 + u^4)^2} < 0 \qquad (\forall u \in \mathbb{R}),
```

   super-exponentially decaying ($`\mathcal{O}(u^4 e^{-u^2})`$), and possesses **all-order positive semi-definite Stieltjes–Hamburger Hankel matrices** $`\sum_{i,j} c_i c_j \int_0^\infty u^{2(i+j)} K_{\text{wall}}(u)\,du \ge 0`$ for every $`N \in \mathbb{N}`$ and every $`c \in \mathbb{R}^N`$.
2. *(Exact Closed-Form Fourier–Laplace Transform — `wallKernel_fourierLaplace_exact`):* For every $`z \in \mathbb{C}`$,

```math
F_{\text{wall}}(z) \triangleq \int_{-\infty}^{\infty} K_{\text{wall}}(u)\,e^{izu}\,du = \sqrt{\pi}\,e^{-z^2/4}\!\left(\frac{z^4}{16} - \frac{5z^2}{4} + \frac{27}{4}\right).
```

3. *(Strict Positivity on $`\mathbb{R}`$, Explicit Off-Line Complex Zero, and Exact Laguerre Violation — `wallKernel_real_pos_yet_offline_zero_and_laguerre_neg`):* Despite possessing every smooth convexity and moment-positivity property verified above, $`F_{\text{wall}}`$:
   - is strictly positive on all of $`\mathbb{R}`$ ($`F_{\text{wall}}(x) \ge \frac{\sqrt{\pi}}{2}e^{-x^2/4} > 0`$ for all $`x \in \mathbb{R}`$);
   - possesses an **explicit strictly off-line complex zero**

```math
z_{\ast} = \sqrt{5 + 3\sqrt{3}} + i\sqrt{3\sqrt{3} - 5}, \qquad \mathrm{Im}(z_{\ast}) = \sqrt{3\sqrt{3} - 5} \approx +0.442891 > 0, \qquad F_{\text{wall}}(z_{\ast}) = 0;
```

   - and **strictly violates Laguerre's inequality at the integer $`\gamma = 3`$**:

```math
L_1(F_{\text{wall}})(3) = \big(F_{\text{wall}}'(3)\big)^2 - F_{\text{wall}}(3)\,F_{\text{wall}}''(3) = -\frac{95}{18}\,\big(F_{\text{wall}}(3)\big)^2 < 0.
```

   *Epistemological consequence:* Theorem 6.28 is strictly stronger than the Schoenberg Complete-Monotonicity No-Go Theorem (Theorem 6.13): it proves unconditionally that **no** proof of RH along Route B can proceed solely from positivity, evenness, smoothness, monotonicity, strict global log-concavity, Gaussian/super-exponential decay, or all-order Hankel positivity of the Fourier–Laplace kernel $`\Phi(u)`$. Any genuine closure of Route B must exploit a **strictly deeper Pólya–Laguerre / Jacobi-theta modular structure** specific to $`\Phi(u)`$ (such as membership in the Laguerre–Pólya class $`\mathcal{LP}`$ via the full modular symmetry of $`\theta`$ and the arithmetic Euler product). ■

---

> [← Part 5](05_prolate_weil_corridor_and_herglotz_pick.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 7 →](07_geodesic_renormalization_and_kuramoto.md)
