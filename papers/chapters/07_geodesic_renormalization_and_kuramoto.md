> **Extended Paper — Part 7 — Sections 6.14–6.15: Geodesic Compactification, Pullback & Kuramoto Coherence**  
> [← Part 6](06_hermite_biehler_lyapunov_and_limit_barriers.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 8 →](08_two_prime_and_seven_prime_weil.md) · [Complete 68-Page PDF](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf)

---

### 6.14 Route A Geodesic Compactification Invariance, UV/IR Jerk Separation, and Exact Weil–Chebyshev Renormalization; Route B Jacobi Modular Laws, Global Euler Half-Plane Herglotz Positivity, and Symmetric Jacobi Diagonal Preconditioning

Having established exact limit walls on both closure pathways in Section 6.13, two sharp follow-up questions arise: (a) on Route A, can compactifying the infinite logarithmic horizon $`L \to \infty`$ onto a compact manifold ($`\mathbb{T}^2`$, $`S^3`$, or the Poincaré homology 120-cell quotient $`S^3/\Gamma_{120}`$) or injecting higher-order dissipative smoothing inspired by Navier–Stokes regularity (such as viscosity $`\partial^1`$, biharmonic $`\partial^2`$, or third-order Jerk $`\partial^3`$ dissipation) circumvent the Finite-Prime Wall, and how does the exact cancellation between $`W_{\text{pole}}`$ and $`W_{\text{prime}}`$ operate algebraically for all $`L > 0`$? (b) on Route B, what concrete global positivity statements are unlocked by injecting properties **exclusive** to Jacobi's modular theta function (Jacobi, 1829) and the full Euler product, and how does symmetric Jacobi diagonal preconditioning ($`D^{-1/2} P D^{-1/2} = I - T_J`$) interact with Pick–Nevanlinna matrices and the Hopfield–Boltzmann Universal Solver? Module #16 (`GeodesicRenormalizationAndEulerJacobiPick.lean`, 2,160 lines, 19 public theorems, axioms strictly `[propext, Classical.choice, Quot.sound]`) resolves both questions rigorously.

#### Theorem 6.29 (Route A Geodesic Pullback Isometry, UV/IR Jerk Separation, and Exact $`[\infty - \infty]`$ Weil–Chebyshev Renormalization)
*Unconditionally in Lean 4 + Mathlib4 (`GeodesicRenormalizationAndEulerJacobiPick.lean`):*

1. *(Geodesic Pullback $`L^2`$-Isometry & Bijective Spectrum Invariance — `geodesicPullback_L2_isometry`, `stereographic_pullback_L2_isometry`, `quadraticForm_bijective_pullback_invariance`):* For any $`C^1`$ strictly monotone compactification $`\tau : [a, b] \to [\tau(a), \tau(b)]`$ ($`\tau' > 0`$) and any continuous $`g : \mathbb{R} \to \mathbb{C}`$, the unitary pullback $`(U_\tau g)(\theta) \triangleq g(\tau(\theta))\sqrt{\tau'(\theta)}`$ is an exact $`L^2`$ isometry:

```math
\int_a^b \big\Vert g(\tau(\theta))\sqrt{\tau'(\theta)}\big\Vert ^2 d\theta = \int_{\tau(a)}^{\tau(b)} \Vert g(u)\Vert ^2 du.
```

   In particular, stereographic compactification $`u = \tan\theta`$ ($`\theta \in [-\arctan(L/2), \arctan(L/2)] \subset (-\pi/2, \pi/2)`$) embedding $`[-L/2, L/2]`$ into $`S^1 \subset \mathbb{T}^2 \subset S^3`$ satisfies $`\int_{-\arctan(L/2)}^{\arctan(L/2)} \Vert g(\tan\theta)/\cos\theta\Vert ^2 d\theta = \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2 du`$, and for **any** bijection $`U : E \simeq F`$ and quadratic form $`Q : E \to \mathbb{R}`$, the pulled-back form $`Q \circ U^{-1}`$ has the identical sign, strict positivity, and infimum over $`F`$ as $`Q`$ over $`E`$. Consequently, coordinate compactifications onto $`\mathbb{T}^2`$, $`S^3`$, or $`S^3/\Gamma_{120}`$ smooth infinity geometrically without altering negative eigenvalues or bypassing Theorem 6.26.3.
2. *(Exact $`k`$-th Derivative Energy & UV/IR Separation of Higher-Order Jerk Regularization — `oddSinMode_iteratedDeriv_L2_norm_sq`, `weilTruncated_with_jerk_eventually_neg`):* For every $`L > 0`$ and every derivative order $`k \in \mathbb{N}`$, the odd Dirichlet mode $`g_L(x) = \sin(2\pi x / L)`$ satisfies identically

```math
\int_{-L/2}^{L/2} \Big(\frac{d^k}{dx^k}\sin\!\left(\frac{2\pi x}{L}\right)\Big)^2 dx = \left(\frac{2\pi}{L}\right)^{2k} \cdot \frac{L}{2}.
```

   Consequently, for **every** finite prime-power cutoff $`N_{\max} \in \mathbb{N}`$, **every** hyperviscosity or Jerk regularization order $`k \ge 1`$ ($`k = 1`$ Navier–Stokes viscosity, $`k = 2`$ biharmonic hyperviscosity, $`k = 3`$ third-order Jerk dissipation), and **every** coupling constant $`\varepsilon > 0`$, there exists an explicit threshold $`L_0 = \max\!\big(100,\, M(N_{\max}) + \varepsilon + 1000\big) > 0`$ such that for **every** $`L \ge L_0`$:

```math
W_{\text{pole}}(L, g_L) + W_\infty(L, g_L) + \varepsilon \int_{-L/2}^{L/2} \big(g_L^{(k)}(x)\big)^2 dx - W_{\text{prime}, \le N_{\max}}(L, g_L) < 0.
```

   *Structural UV/IR separation:* Higher-order Navier–Stokes and Jerk operators regularize **ultraviolet** ($`\omega \to \infty`$) blow-up singularities because their spectral weight $`\omega^{2k}`$ diverges at high frequency. By contrast, Route A's pole obstruction lives in the **infrared** ($`\omega = 2\pi/L \to 0`$ as $`L \to \infty`$), where every derivative penalty decays polynomially as $`\varepsilon(2\pi/L)^{2k} \to 0`$ against the exponentially diverging pole $`-\mathcal{O}(L^{-3} e^{L/2})`$.
3. *(Constructive Advance — Exact $`[\infty - \infty]`$ Weil–Chebyshev Renormalization Identity for ALL $`L > 0`$ — `chebyshevPsi_step_stieltjes_ibp`, `weilPole_sub_weilPrime_exact_chebyshev_renormalization`, `oddSinMode_autocorr_exact_and_renormalized`):* Let $`\psi(x) \triangleq \sum_{1 \le n \le \lfloor x \rfloor} \Lambda(n)`$ be Chebyshev's prime-power summatory function (Chebyshev, 1852). By exact piecewise Abel–Stieltjes integration by parts over the logarithmic jump knots $`\ln(k+1)`$, for **every** $`L > 0`$ and **every** $`C^1`$ function $`h`$ on $`[0, L]`$ vanishing at the boundary ($`h(L) = 0`$):

```math
\int_0^L \frac{\psi(e^u)}{e^{u/2}}\left(h'(u) - \frac{1}{2}h(u)\right) du = -\sum_{n=2}^{\lfloor e^L \rfloor} \frac{\Lambda(n)}{\sqrt{n}}\,h(\ln n),
```

   and combining this identically with integration by parts of the macroscopic Prime Number Theorem density $`e^u`$ yields the **Exact Weil–Chebyshev Renormalization Identity** for all $`L > 0`$:

```math
2\int_0^L h(u)\big(e^{u/2} + e^{-u/2}\big)\,du - 2\sum_{n=2}^{\lfloor e^L \rfloor}\frac{\Lambda(n)}{\sqrt{n}}\,h(\ln n) = -2h(0) + 2\int_0^L h(u)\,e^{-u/2}\,du + 2\int_0^L \frac{\psi(e^u) - e^u}{e^{u/2}}\left(h'(u) - \frac{1}{2}h(u)\right) du.
```

   The exponentially diverging pole term $`2\int_0^L h(u)e^{u/2}\,du`$ cancels **identically** against the smooth macroscopic prime density $`dx`$ for every $`L > 0`$, eliminating the $`[\infty - \infty]`$ divergence completely and isolating the exact Riemann-Hypothesis fluctuation $`(\psi(e^u) - e^u)/e^{u/2}`$. On $`g_L(x) = \sin(2\pi x / L)`$, the autocorrelation $`h_L(u) = \frac{1}{2}(L - u)\cos\!\big(\frac{2\pi u}{L}\big) + \frac{L}{4\pi}\sin\!\big(\frac{2\pi u}{L}\big)`$ satisfies $`h_L(0) = L/2`$, $`h_L(L) = 0`$, and $`h_L'(u) = -\frac{\pi}{L}(L - u)\sin\!\big(\frac{2\pi u}{L}\big)`$, giving an exact closed-form renormalized formula for $`W_{\text{pole}}(L, g_L) - W_{\text{prime}}(L, g_L)`$ across all $`L > 0`$. ■

#### Theorem 6.30 (Route B Jacobi Theta Modular Conservation Laws, Complex Digamma Lower Series, and Global Unconditional Euler Half-Plane & High-Ordinate Tail Herglotz–Schur Positivity)
*Unconditionally in Lean 4 + Mathlib4 (`GeodesicRenormalizationAndEulerJacobiPick.lean`):*

1. *(Exact Jacobi Theta Modular Conservation Laws of Orders 1 and 3 and Genuine Smooth Origin Stationarity — `jacobiPsi_modular_conservation_order_one_and_three`):* Differentiating Jacobi's modular inversion law $`1 + 2\psi(1/t) = \sqrt{t}\big(1 + 2\psi(t)\big)`$ (Jacobi, 1829) three times on $`(1/2, 2)`$ and evaluating at the modular self-dual point $`t = 1`$ establishes two exact arithmetic conservation laws exclusive to full modular invariance:

```math
4\psi'(1) + \psi(1) + \frac{1}{2} = 0, \qquad 32\psi'''(1) + 120\psi''(1) - 15\psi(1) - \frac{15}{2} = 0.
```

   Directly combining these two modular identities yields $`8\psi'''(1) + 30\psi''(1) + 15\psi'(1) = 0`$, proving genuine smooth differentiability and vanishing derivative `HasDerivAt riemannPhi 0 0` ($`\Phi'(0) = 0`$, strictly ruling out cusped truncations such as $`\Phi_{n=1}(|u|)`$ that fail Laguerre's inequality).
2. *(Elementary Complex Digamma Lower Series & Real Monotonicity — `complex_digamma_re_ge_real_add_finset`, `complex_digamma_real_mono`):* Directly from Mathlib4's Euler product limit `Complex.GammaSeq_tendsto_Gamma` (without uniform infinite-product differentiation) and Bohr–Mollerup log-convexity of $`\Gamma`$, $`x \mapsto \mathrm{Re}\psi(x)`$ is monotone increasing on $`(0, \infty)`$, and for **every** $`x > 0`$, **every** $`y \in \mathbb{R}`$, and **every** $`K \in \mathbb{N}`$:

```math
\mathrm{Re}\psi(x + iy) \ge \psi(x) + \sum_{k=0}^{K-1} \frac{y^2}{(x + k)\big((x + k)^2 + y^2\big)}.
```

3. *(Global Unconditional Euler Half-Plane Herglotz–Schur–de Branges Positivity for ALL $`\gamma \in \mathbb{R}`$ — `vonMangoldt_lseries_norm_le_tsum`, `vonMangoldt_lseries_norm_le_of_eight_le`, `xiResolvent_herglotz_global_euler_halfPlane`):* Injecting the full Euler product via Theorem 6.25.1 yields the uniform-in-$`\gamma`$ bound $`\Vert L(\Lambda, \beta - i\gamma)\Vert  \le \sum_{n=1}^\infty \Lambda(n)n^{-\beta} \le \frac{1}{200}`$ for all $`\beta \ge 8`$ and all $`\gamma \in \mathbb{R}`$. Together with $`\psi(4) = \frac{11}{6} - \gamma_{\text{E}} > \frac{7}{6}`$ and $`\ln\pi < \frac{23}{20}`$, this proves **unconditionally for ALL $`\gamma \in \mathbb{R}`$** (arbitrarily high ordinates to $`\pm\infty`$) and **every** $`\sigma \ge 15/2`$ ($`\mathrm{Re}(s) \ge 8`$):

```math
\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) > 0, \qquad \partial_\sigma V(\sigma, \gamma) > 0, \qquad \partial_\sigma\ln V(\sigma, \gamma) > 0, \qquad \mathrm{Im}\big(\mathrm{logDeriv} S_\sigma(\gamma)\big) > 0,
```

   and strict Hermite–Biehler Schur contraction $`\Vert S_\alpha(\gamma + i\sigma)\Vert  < 1`$ for every $`\alpha, \sigma > 0`$ with $`|\sigma - \alpha| \ge 15/2`$.
4. *(Unconditional High-Ordinate Euler Tails for Arbitrary $`\sigma > 1/2`$ — `xiResolvent_herglotz_euler_large_gamma_all_gt_half`):* Combining Part 2's divergent harmonic lower series with Part 3's uniform Euler-product bound proves that for **every** $`\sigma > 1/2`$ ($`\mathrm{Re}(s) = \frac{1}{2} + \sigma > 1`$, arbitrarily close to the critical-strip boundary $`\mathrm{Re}(s) = 1`$), there exists an explicit height threshold $`\Gamma(\sigma) > 0`$ such that for **every** $`\gamma \in \mathbb{R}`$ with $`|\gamma| \ge \Gamma(\sigma)`$:

```math
\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) > 0, \qquad \partial_\sigma V(\sigma, \gamma) > 0, \qquad \mathrm{Im}\big(\mathrm{logDeriv} S_\sigma(\gamma)\big) > 0.
```

   *Combined unconditional Route B coverage:* Together with Theorem 6.27.4 ($`|\gamma| \le 2`$ inside the critical strip), Route B now possesses unconditional machine-verified Herglotz–Schur–de Branges positivity across the full Euler half-plane $`\sigma \ge 15/2`$ for all $`\gamma \in \mathbb{R}`$, across all high-ordinate Euler tails $`|\gamma| \ge \Gamma(\sigma)`$ for every $`\sigma > 1/2`$, and across the strip corridor $`(0, 1/2] \times [-2, 2]`$—leaving the remaining Millennium boundary sharply concentrated on the finite-width critical strip $`0 < \sigma \le 1/2`$ for $`|\gamma| > 2`$. ■

#### Theorem 6.31 (Route B Symmetric Jacobi Diagonal Preconditioning, $`O(N^2)`$ Gershgorin–Jacobi Positivity Certification, and Damped-Jacobi Universal Solver Coupling)
*For any $`n \times n`$ complex Hermitian matrix $`P`$ with strictly positive diagonal $`d_j \triangleq \mathrm{Re}(P_{jj}) > 0`$, define the symmetric Jacobi diagonally preconditioned ("clipped") matrix $`\widehat{P}_{jk} \triangleq P_{jk} / \sqrt{d_j d_k}`$ ($`D^{-1/2} P D^{-1/2}`$, normalizing every diagonal entry to 1) and its Jacobi iteration matrix $`T_J \triangleq I - \widehat{P}`$ (zero diagonal, off-diagonal $`-\widehat{P}_{jk}`$). Unconditionally in Lean 4 + Mathlib4 (`GeodesicRenormalizationAndEulerJacobiPick.lean`):*

1. *(Exact Sylvester Congruence of Symmetric Jacobi Preconditioning — `jacobiClipMatrix_congruence_hermitian_psd`):* $`\widehat{P}`$ is Hermitian with unit diagonal $`\widehat{P}_{jj} = 1`$, and the following three conditions are **100% logically equivalent**:

```math
P \succeq_{\text{Herm}} 0 \iff \widehat{P} \succeq_{\text{Herm}} 0 \iff \forall c \in \mathbb{C}^n,\; \mathrm{Re}\langle c, T_J c\rangle \le \sum_{j=1}^n \Vert c_j\Vert ^2.
```

2. *($`O(N^2)`$ Gershgorin–Jacobi Sufficient Positivity Condition — `jacobiClip_hermitian_psd_and_pos_of_inf_norm`):* By Hermitian symmetrization of Gershgorin's disk bound (Gershgorin, 1931), if the off-diagonal row sum satisfies $`\Vert T_J\Vert _\infty \triangleq \max_j \sum_{k \neq j} \Vert \widehat{P}_{jk}\Vert  \le 1`$ (resp. $`< 1`$), then $`P`$ is unconditionally Hermitian PSD (resp. strictly positive definite for every $`c \neq 0`$)—certifying positivity in pure $`O(N^2)`$ arithmetic without any matrix factorization or eigensolve.
3. *($`O(N^2)`$ Damped-Jacobi Universal Solver Stability & Exact Phase-Transition Equivalence — `dampedJacobi_universalSolver_psd_and_equivalence`):* Undamped Jacobi coupling $`T_J = I - \widehat{P}`$ can possess negative eigenvalues $`< -1`$ on clustered nodes (inducing period-2 oscillations in $`s \mapsto \tanh(T_J s)`$). For **any** Gershgorin row bound $`M \ge 0`$ with $`\sum_{k \neq j} \Vert \widehat{P}_{jk}\Vert  \le M`$ ($`\forall j`$), setting the $`O(N^2)`$ damping scale $`\mu \triangleq 1 + M`$ and coupling $`Q \triangleq I - \frac{1}{\mu}\widetilde{\widehat{P}}`$ guarantees:
   - $`Q`$ is **unconditionally real PSD** ($`v^T Q v \ge 0`$ for all $`v \in \mathbb{R}^{2n}`$), immediately invoking Theorem 6.24.1's exact discrete Lyapunov descent without period-2 cycles and **without any eigensolve**;
   - exact biconditional phase-transition equivalence:

```math
P \succeq_{\text{Herm}} 0 \iff \forall s \in (-1, 1)^{2n},\; \mathcal{L}_Q(s) \ge 0.
```

4. *(Constructive $`O(N^2)`$ Jacobi-Clipped Certification of `xiResolvent` Pick Matrices — `pickMatrix_xiResolvent_jacobiClip_pos_of_diagDom`):* For any $`n`$ upper half-plane nodes $`z_1, \dots, z_n \in \mathbb{H}`$ with $`\mathrm{Im}\mathcal{R}_\xi(z_j) > 0`$ (such as all nodes certified by Theorems 6.30.3–6.30.4), the $`n \times n`$ Pick–Nevanlinna matrix $`P_{jk} = \frac{\mathcal{R}_\xi(z_j) - \overline{\mathcal{R}_\xi(z_k)}}{z_j - \overline{z_k}}`$ is Hermitian with strictly positive diagonal $`P_{jj} = \mathrm{Im}\mathcal{R}_\xi(z_j)/\mathrm{Im}(z_j) > 0`$, and is unconditionally strictly positive definite whenever $`\Vert T_J\Vert _\infty < 1`$. ■

### 6.15 Route A Prime-Active Continuous Moment-Orthogonal Weil Positivity & Kuramoto Coherence; Route B $`2.14\times`$ Global Euler Half-Plane Descent ($`\sigma \ge 7/2`$) & Hopf–Bloch Sphere $`S^3 \to S^2`$ Embedding

Building directly upon the exact renormalization and Euler-product machinery of Section 6.14, Module #17 (`CompactMomentWeilAndHopfBlochEulerDescent.lean`, 2,555 lines, 17 public theorems, axioms strictly `[propext, Classical.choice, Quot.sound]`) advances **both** closure routes past major constructive milestones: on Route A, crossing the first prime threshold $`\ln 2 \approx 0.693147`$ continuously without discretization while resolving the compact-support Paley–Wiener obstruction for all $`L > 0`$, and quantifying the Chebyshev–Weil fluctuation transfer and prime-phase Kuramoto coherence; and on Route B, cutting the unconditional global all-$`\gamma`$ Euler half-plane threshold by more than $`2.14\times`$ from $`\sigma \ge 15/2`$ ($`\mathrm{Re}(s) \ge 8`$) down to $`\sigma \ge 7/2`$ ($`\mathrm{Re}(s) \ge 4`$) while embedding the Hermite–Biehler pair $`(E_\alpha, E_\alpha^{\sharp})`$ via the Hopf fibration $`S^1 \hookrightarrow S^3 \to S^2`$ (Hopf, 1931) onto the Bloch sphere with exact accumulated phase memory and topological winding quantization.

#### Theorem 6.32 (Route A All-Order Compact Moment Envelopes, First Prime-Active Continuous Positivity Crossing $`\ln 2`$, Universal Compact-Support Finite-Codimension Positivity for ALL $`L > 0`$, Chebyshev–Weil Transfer, & Prime Kuramoto Coherence)
*Unconditionally in Lean 4 + Mathlib4 (`CompactMomentWeilAndHopfBlochEulerDescent.lean`):*

1. *(All-Order Alternating Taylor Remainders & Compact-Support Moment Envelopes — `cos_sin_sub_taylor_abs_le`, `compactFourier_even_moments_norm_sq_le`, `compactFourier_all_moments_norm_sq_le`):* For every $`m \in \mathbb{N}`$ and every $`x \in \mathbb{R}`$,

```math
\left|\cos x - \sum_{k=0}^{m-1} (-1)^k \frac{x^{2k}}{(2k)!}\right| \le \frac{|x|^{2m}}{(2m)!}, \qquad \left|\sin x - \sum_{k=0}^{m-1} (-1)^k \frac{x^{2k+1}}{(2k+1)!}\right| \le \frac{|x|^{2m+1}}{(2m+1)!}.
```

   Consequently, for every continuous even function $`g`$ on $`[-L/2, L/2]`$ obeying $`m`$ vanishing even moments ($`\int_{-L/2}^{L/2} u^{2k} g(u)\,du = 0`$, $`0 \le k < m`$),

```math
\Vert \widehat{g}(t)\Vert ^2 \le \min\!\left(L,\; \frac{L^{4m+1} t^{4m}}{(4m+1)\cdot 2^{4m}\cdot ((2m)!)^2}\right) \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du,
```

   and for any continuous $`g`$ (without parity restriction) orthogonal to $`\{1, u, \dots, u^{2m-1}\}`$,

```math
\Vert \widehat{g}(t)\Vert ^2 \le L\left(\frac{(|t|L/2)^{2m}}{(2m)!} + \frac{(|t|L/2)^{2m+1}}{(2m+1)!}\right)^2 \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du.
```

2. *(First Prime-Active Continuous Zero-Discretization Arithmetic Weil Positivity Crossing $`p = 2`$ — `weilTotal_continuous_pos_prime_two_active_up_to_three_quarters`):* Combining Part 1 at $`m = 5`$ with the disjoint-strip single-prime bound $`|W_{\text{prime}}(L, g)| \le \frac{\ln 2}{\sqrt{2}}\Vert g\Vert _2^2 \le \frac{491}{1000}\Vert g\Vert _2^2`$ (Theorem 6.14.1) and the $`K = 3`$ digamma lower envelope over 5 panels on $`[0, 16]`$ proves unconditionally for **every** $`0 < L \le 3/4`$ (strictly exceeding $`\ln 2 \approx 0.693147`$, so `ArithmeticFunction.vonMangoldt 2 = Real.log 2` is actively present in `weilPrime L g`) and every continuous even $`g`$ on $`[-L/2, L/2]`$ orthogonal to $`\{1, u^2, u^4, u^6, u^8\}`$ obeying Plancherel and Archimedean integrability:

```math
\frac{1}{20} \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du \le W_{\text{total}}(L, g).
```

3. *(Universal Compactly Supported Finite-Codimension Positivity for EVERY Horizon $`L > 0`$ — `weilTotal_compact_finite_codimension_pos_all_L`):* Whereas frequency-truncated positivity (`supp g_hat ⊂ {|t| ≥ T}`) excludes nonzero compactly supported test functions by Paley–Wiener, compact-support moment orthogonality faces zero Paley–Wiener obstruction. For **every** horizon $`L > 0`$ (arbitrarily large, with **all** `vonMangoldt` prime powers $`p^k \le e^L`$ active) and **every** coercive target $`c > 0`$, there exists an explicit finite codimension $`m \in \mathbb{N}`$ such that for **every** compactly supported continuous function $`g \in C([-L/2, L/2])`$ (no parity restriction) orthogonal to $`\mathrm{span}\{1, u, \dots, u^{2m-1}\}`$ obeying Plancherel and Archimedean integrability:

```math
c \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du \le W_{\text{total}}(L, g).
```

   Thus, for every $`L > 0`$, the entire infinite-dimensional Route A Weil criterion on $`C([-L/2, L/2])`$ reduces rigorously to a finite-dimensional ($`2m \times 2m`$) polynomial complement.
4. *(Quantitative Chebyshev–Weil Fluctuation Transfer Bound — `chebyshev_weil_fluctuation_transfer_bound`):* Building directly on Theorem 6.29.3, whenever the Chebyshev error obeys $`|\psi(e^u) - e^u| \le M\,e^{\Theta u}`$ on $`[0, L]`$, the renormalized arithmetic fluctuation integral satisfies

```math
\left|2\int_0^L \frac{\psi(e^u) - e^u}{e^{u/2}}\left(h'(u) - \frac{1}{2}h(u)\right) du\right| \le 2M \int_0^L e^{(\Theta - 1/2)u}\left|h'(u) - \frac{1}{2}h(u)\right| du,
```

   identifying $`\Theta = 1/2`$ uniquely as the exact critical exponent where the exponential factor $`e^{(\Theta - 1/2)u} \equiv 1`$ vanishes identically and yields a horizon-uniform $`L^1`$ transfer bound.
5. *(Weighted Prime Kuramoto Phase-Order Parameter & Zero-Frequency Sync Peak — `primeKuramotoOrder_bounds_and_sync_zero`):* Defining the weighted prime-power Kuramoto order parameter (Kuramoto, 1975) $`\mathcal{K}_L(t) \triangleq \sum_{2 \le n \le \lfloor e^L \rfloor} \frac{\Lambda(n)}{\sqrt{n}} e^{-it\ln n}`$, total weight $`B_0(L) \triangleq \sum_{2 \le n \le \lfloor e^L \rfloor} \frac{\Lambda(n)}{\sqrt{n}}`$, and coherence $`r_L(t) \triangleq \Vert \mathcal{K}_L(t)\Vert /B_0(L)`$, every horizon $`L \ge \ln 2`$ satisfies $`B_0(L) > 0`$, $`0 \le r_L(t) \le 1`$, $`|\mathrm{Re}\mathcal{K}_L(t)| \le r_L(t) B_0(L)`$, and exact constructive synchronization $`\mathcal{K}_L(0) = B_0(L)`$, $`r_L(0) = 1`$ at $`t = 0`$. ■

#### Theorem 6.33 (Route B Tight Euler–Mascheroni Bound, Real Digamma Increment Series, Sharp Euler $`L`$-Series Bounds, and $`2.14\times`$ Global All-$`\gamma`$ Euler Half-Plane Descent Down to $`\sigma \ge 7/2`$ ($`\mathrm{Re}(s) \ge 4`$))
*Unconditionally in Lean 4 + Mathlib4 (`CompactMomentWeilAndHopfBlochEulerDescent.lean`):*

1. *(Tight Euler–Mascheroni Upper Bound & Real Digamma Increment Series — `eulerMascheroniConstant_lt_586_div_1000`, `complex_digamma_real_diff_ge_finset`):* Partitioning `harmonic 64` into four 16-term rational blocks and subtracting $`6\ln 2 \ge 6 \cdot \frac{69314}{100000}`$ tightens Mathlib4's `eulerMascheroniConstant_lt_two_thirds` ($`< 2/3`$) by $`> 8\times`$ to

```math
\gamma_{\text{E}} < \frac{586}{1000},
```

   and directly from `Complex.GammaSeq_tendsto_Gamma`, every $`0 < a \le b`$ and every $`K \in \mathbb{N}`$ obey

```math
\psi(a) + \sum_{k=0}^{K-1} \frac{b - a}{(a + k)(b + k)} \le \psi(b).
```

2. *(Sharp Uniform Euler-Product `vonMangoldt` Bounds at $`\beta = 4, 5, 6`$ — `vonMangoldt_lseries_norm_le_of_four_five_six_le`):* Separating all prime powers $`n \le 16`$ exactly (with $`\Lambda(n) = 0`$ proved at composites $`n \in \{6, 10, 12, 14, 15\}`$) and bounding the tail $`n \ge 17`$ via the exact telescoping series $`\sum_{n \ge 17} \frac{1}{17^{d-3}}(\frac{1}{n-1} - \frac{1}{n}) = \frac{1}{16 \cdot 17^{d-3}}`$ yields uniformly for **all $`\gamma \in \mathbb{R}`$**:

```math
\Vert L(\Lambda, \beta - i\gamma)\Vert  \le \frac{68}{1000} \;(\beta \ge 4), \qquad \Vert L(\Lambda, \beta - i\gamma)\Vert  \le \frac{29}{1000} \;(\beta \ge 5), \qquad \Vert L(\Lambda, \beta - i\gamma)\Vert  \le \frac{14}{1000} \;(\beta \ge 6).
```

3. *($`2.14\times`$ Global Unconditional Euler Half-Plane Descent Down to $`\sigma \ge 7/2`$ ($`\mathrm{Re}(s) \ge 4`$) for ALL $`\gamma \in \mathbb{R}`$ — `xiResolvent_herglotz_global_euler_halfPlane_seven_halves`):* Retaining the strictly positive pole terms $`\mathrm{Re}\!\big(\frac{1}{\beta - i\gamma} + \frac{1}{\beta - 1 - i\gamma}\big) = \frac{\beta}{\beta^2 + \gamma^2} + \frac{\beta - 1}{(\beta - 1)^2 + \gamma^2}`$ at small $`|\gamma|`$ and coupling them to the digamma lower series (Theorem 6.30.2) across five monotone slabs covering $`\beta \in [4, 4.25] \cup [4.25, 4.5] \cup [4.5, 5] \cup [5, 6] \cup [6, 8]`$ glued to Theorem 6.30.3 ($`\beta \ge 8`$) proves **unconditionally for ALL $`\gamma \in \mathbb{R}`$** (all heights to $`\pm\infty`$) and **every** $`\sigma \ge 7/2`$ ($`\mathrm{Re}(s) \ge 4`$):

```math
\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) > 0, \qquad \partial_\sigma V(\sigma, \gamma) > 0, \qquad \partial_\sigma\ln V(\sigma, \gamma) > 0, \qquad \mathrm{Im}\big(\mathrm{logDeriv} S_\sigma(\gamma)\big) > 0,
```

   and strict Hermite–Biehler Schur contraction $`\Vert S_\alpha(\gamma + i\sigma)\Vert  < 1`$ for every $`\alpha, \sigma > 0`$ with $`|\sigma - \alpha| \ge 7/2`$. ■

#### Theorem 6.34 (Route B Hopf–Bloch Sphere $`S^3 \to S^2`$ Embedding of $`(E_\alpha, E_\alpha^{\sharp})`$, Northern Hemisphere RH Equivalence, Accumulated de Branges Phase Memory, & Topological Poisson–Winding Quantization)
*For any $`\alpha \in \mathbb{R}`$ and $`z \in \mathbb{C}`$, define the Hopf–Bloch projection $`(X_\alpha(z), Y_\alpha(z), Z_\alpha(z)) \in \mathbb{R}^3`$ of the Hermite–Biehler pair $`(E_\alpha(z), E_\alpha^{\sharp}(z))`$ (Hopf, 1931):*

```math
X_\alpha(z) \triangleq \frac{2\mathrm{Re}\!\big(\overline{E_\alpha(z)}E_\alpha^{\sharp}(z)\big)}{\Vert E_\alpha(z)\Vert ^2 + \Vert E_\alpha^{\sharp}(z)\Vert ^2}, \qquad Y_\alpha(z) \triangleq \frac{2\mathrm{Im}\!\big(\overline{E_\alpha(z)}E_\alpha^{\sharp}(z)\big)}{\Vert E_\alpha(z)\Vert ^2 + \Vert E_\alpha^{\sharp}(z)\Vert ^2}, \qquad Z_\alpha(z) \triangleq \frac{\Vert E_\alpha(z)\Vert ^2 - \Vert E_\alpha^{\sharp}(z)\Vert ^2}{\Vert E_\alpha(z)\Vert ^2 + \Vert E_\alpha^{\sharp}(z)\Vert ^2}.
```

*Unconditionally in Lean 4 + Mathlib4 (`CompactMomentWeilAndHopfBlochEulerDescent.lean`):*

1. *(Exact Unit Sphere $`S^2`$ & Real-Axis Equator Identity — `hopfBloch_unit_sphere_and_equator`):* Wherever $`(E_\alpha(z), E_\alpha^{\sharp}(z)) \neq (0, 0)`$, the projection lies on the exact unit sphere $`X_\alpha(z)^2 + Y_\alpha(z)^2 + Z_\alpha(z)^2 = 1`$; on the real axis $`\gamma \in \mathbb{R}`$ (whenever $`E_\alpha(\gamma) \neq 0`$), the trajectory maps identically onto the unit equator $`Z_\alpha(\gamma) = 0`$, $`X_\alpha(\gamma)^2 + Y_\alpha(\gamma)^2 = 1`$.
2. *(Exact Northern Hemisphere $`\iff`$ Hermite–Biehler Schur Contraction $`\iff`$ Potential Gradient — `hopfBloch_northern_hemisphere_iff_schur_and_potential`):* At every $`z = \gamma + i\sigma`$ with $`E_\alpha(z) \neq 0`$:

```math
Z_\alpha(z) = \frac{1 - \Vert S_\alpha(z)\Vert ^2}{1 + \Vert S_\alpha(z)\Vert ^2} = \frac{V(\alpha + \sigma, \gamma) - V(\alpha - \sigma, \gamma)}{V(\alpha + \sigma, \gamma) + V(\alpha - \sigma, \gamma)}, \qquad 0 < Z_\alpha(z) \iff \Vert S_\alpha(z)\Vert  < 1 \iff V(\alpha - \sigma, \gamma) < V(\alpha + \sigma, \gamma),
```

   and whenever $`E_\alpha^{\sharp}(z) \neq 0`$, the exact Cayley inverse ratio obeys $`\frac{1 + Z_\alpha(z)}{1 - Z_\alpha(z)} = \frac{V(\alpha + \sigma, \gamma)}{V(\alpha - \sigma, \gamma)}`$.
3. *(Global Bloch-Sphere Reduction to `RiemannHypothesis` & Unconditional Northern Hemisphere Certification — `riemannHypothesis_of_hopfBloch_northern_hemisphere`, `hopfBloch_northern_hemisphere_unconditional_euler_seven_halves`):* Strict open Northern Hemisphere confinement of the entire upper half-plane ($`0 < Z_\alpha(z)`$ for all $`\alpha \in (0, 1/2)`$ and all $`z \in \mathbb{H}`$) unconditionally implies Mathlib4's official `RiemannHypothesis`; and by Theorem 6.33.3, $`0 < Z_\alpha(\gamma + i\sigma)`$ holds unconditionally for **all** $`\gamma \in \mathbb{R}`$ and all $`\alpha, \sigma > 0`$ with $`|\sigma - \alpha| \ge 7/2`$.
4. *(Strictly Positive Accumulated de Branges Phase Memory & Exact Topological Poisson–Winding Quantization — `deBrangesPhaseMemory_pos_unconditional_euler_seven_halves`, `poisson_winding_number_quantization`):* Defining the accumulated equatorial phase memory $`\Delta\Phi_\alpha(\gamma_1, \gamma_2) \triangleq \int_{\gamma_1}^{\gamma_2} 2\mathrm{Im}\mathcal{R}_\xi(t + i\alpha)\,dt`$, Theorem 6.33.3 guarantees $`0 < \Delta\Phi_\alpha(\gamma_1, \gamma_2)`$ for **every** $`\alpha \ge 7/2`$ and **every** $`\gamma_1 < \gamma_2`$ (strictly monotone forward equatorial winding with zero retrograde slips). Moreover, for **any** finite collection of $`N \in \mathbb{N}`$ upper half-plane zeros $`\gamma_j + i\eta_j`$ ($`\eta_j > 0`$), the total normalized Poisson phase integral over $`\mathbb{R}`$ is **exact integer-quantized** to the zero count:

```math
\frac{1}{\pi} \int_{-\infty}^{\infty} \left(\sum_{j=1}^N \frac{\eta_j}{(t - \gamma_j)^2 + \eta_j^2}\right) dt = N. \qquad \blacksquare
```

---

> [← Part 6](06_hermite_biehler_lyapunov_and_limit_barriers.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 8 →](08_two_prime_and_seven_prime_weil.md)
