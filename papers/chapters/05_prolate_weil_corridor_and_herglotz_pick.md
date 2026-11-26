> **Extended Paper — Part 5 — Sections 6.7–6.10: Connes–Consani Prolate, Arithmetic Weil & Herglotz–Pick**  
> [← Part 4](04_bohr_torus_adeles_and_weil_positivity.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 6 →](06_hermite_biehler_lyapunov_and_limit_barriers.md) · [Complete 68-Page PDF](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.pdf)

---

### 6.7 Connes–Consani Prolate Spectral Positivity, Darboux Factorization, and Exact Positivity Certificates

To anchor Route A with a rigorously positive-definite compactified differential comparison operator (Connes & Consani, 2021) and exact finite-dimensional algebraic certificates, define on $`[-a, a]`$ ($`a > 0`$, $`c \in \mathbb{R}`$) the **Prolate Spheroidal Differential Operator**:

```math
H_{\text{prolate}}(a, c, f)(x) \triangleq -\frac{d}{dx}\Big((a^2 - x^2)\,f'(x)\Big) + c^2 x^2 f(x) = -(a^2 - x^2) f''(x) + 2x f'(x) + c^2 x^2 f(x).
```

#### Theorem 6.10 (Machine-Verified Prolate–Darboux Spectral Theory and Positivity Certificates)
*In Lean 4 + Mathlib4 (`UnconditionalCorridorAndProlate.lean` and `CertificateAndSpectralBridge.lean`, `0 sorry`, `[propext, Classical.choice, Quot.sound]`):*

1. *(Boundary-Free Integration by Parts & Formal Self-Adjointness — `prolate_integration_by_parts`, `prolate_symmetric`):* Because $`(a^2 - x^2)`$ vanishes identically at both endpoints $`x = \pm a`$, every pair of $`C^2`$ real functions $`f, g`$ satisfies—with **zero boundary conditions**—

```math
\int_{-a}^{a} f(x)\,H_{\text{prolate}}(a, c, g)(x)\,dx = \int_{-a}^{a} \Big[(a^2 - x^2)\,f'(x)\,g'(x) + c^2 x^2 f(x)\,g(x)\Big]\,dx = \int_{-a}^{a} H_{\text{prolate}}(a, c, f)(x)\,g(x)\,dx.
```

2. *(Strict Positive-Definiteness, Positive Eigenvalues, & Orthogonality — `prolate_quadratic_pos_of_ne_zero`, `prolate_eigenvalue_pos`, `prolate_eigenvectors_orthogonal`):* For $`a > 0`$ and $`c \neq 0`$, every $`C^2`$ function $`f`$ non-zero somewhere in $`(-a, a)`$ satisfies $`\langle f, H_{\text{prolate}}(a, c, f) \rangle > 0`$; hence every non-trivial $`C^2`$ eigenfunction has strictly positive eigenvalue $`\mu > 0`$, and eigenfunctions with distinct eigenvalues are orthogonal in $`L^2([-a, a])`$.
3. *(Supersymmetric Darboux Factorization — `darboux_supersymmetric_factorization`, `darboux_supersymmetric_nonneg`):* For any strictly positive $`C^2`$ ground state $`v_0 > 0`$ on $`[-a, a]`$ (such as the nodeless Weil–Adelic ground eigenfunction $`v_0^{(L)} > 0`$) and any $`C^2`$ perturbation $`f`$ with $`f(-a) = f(a) = 0`$, the effective potential $`V_{\text{eff}}(x) = v_0''(x)/v_0(x)`$ satisfies

```math
\int_{-a}^{a} f(x)\Big(-f''(x) + V_{\text{eff}}(x)\,f(x)\Big)\,dx = \int_{-a}^{a} \left(f'(x) - \frac{v_0'(x)}{v_0(x)} f(x)\right)^2 dx \ge 0.
```

4. *(Exact $`LDL^T`$ Cholesky & Prolate-Comparison Positivity Certificates — `cholesky_ldl_quadratic_pos_of_unit_lower`, `prolate_comparison_quadratic_pos`):* (i) Any symmetric matrix $`W = L D L^T`$ with unit lower-triangular $`L`$ and strictly positive pivots $`D_k > 0`$ satisfies $`v^T W v = \sum_k D_k (\sum_i v_i L_{ik})^2 > 0`$ for every $`v \neq 0`$; (ii) any quadratic energy functional decomposing as $`Q(f) = \alpha \langle f, H_{\text{prolate}}(a, c, f) \rangle + R(f)`$ with $`\alpha > 0`$, $`c \neq 0`$, and $`R(f) \ge 0`$ is strictly positive on every non-trivial $`C^2`$ test function on $`(-a, a)`$. ■

### 6.8 Infinite-Dimensional Continuous Weil Positivity, Constructive Explicit Zero-Free Rectangle, and Schoenberg No-Go Theorem

To advance both closure pathways simultaneously beyond finite-dimensional matrices (Route A) and non-constructive compactness existence (Route B), `WeilArchimedeanAndExplicitCorridor.lean` (**2,740 lines, 24 headline theorems**, `0 sorry`, axioms strictly `[propext, Classical.choice, Quot.sound]`) formalizes three major unconditional results directly in Lean 4 + Mathlib4:

#### Theorem 6.11 (Route A — Infinite-Dimensional Continuous Weil–Archimedean Positivity & Hilbert Schur Certificates)
*Define the exact continuous Archimedean Weil spectral weight on $`\mathbb{R}`$ via Mathlib4's `Real.eulerMascheroniConstant`,*

```math
C_\infty \triangleq \gamma_{\text{E}} + \ln(8\pi) + \frac{\pi}{2}, \qquad \psi_{\text{arch}}(t) \triangleq -C_\infty + \sum_{n=0}^\infty \frac{t^2/4}{\big(n + \tfrac{1}{4}\big)\big((n + \tfrac{1}{4})^2 + t^2/4\big)},
```

*and its closed-form one-term plus integral-test lower envelope $`\psi_{\text{lb}1}(t) \triangleq -C_\infty + \frac{4t^2}{1/4 + t^2} + \frac{1}{2}\ln\!\left(1 + \frac{4t^2}{25}\right)`$. For any continuous complex test function $`g : \mathbb{R} \to \mathbb{C}`$ supported on $`[-L/2, L/2]`$ ($`L > 0`$), define its Fourier transform $`\widehat{g}(t) = \int_{-L/2}^{L/2} g(u)e^{-itu}\,du`$ and polar functional $`W_{\text{pole}}(g) \triangleq 2\big|\int_{-L/2}^{L/2} g(u)\cosh(u/2)\,du\big|^2 - 2\big|\int_{-L/2}^{L/2} g(u)\sinh(u/2)\,du\big|^2`$. Then in Lean 4 + Mathlib4:*

1. *(Exact Spectral Weight Properties & Antiderivative — `archimedeanWeilConst_lt`, `psiArch_summable`, `psiArch_even`, `psiArch_strictMono_nonneg`, `psiArch_ge_psiLb1`, `integral_psiLb1_gap_eq`):* $`C_\infty < 11/2`$, the digamma series converges unconditionally on all of $`\mathbb{R}`$, $`\psi_{\text{arch}}`$ is even and strictly increasing on $`[0, \infty)`$, satisfies $`\psi_{\text{arch}}(t) \ge \psi_{\text{lb}1}(t)`$ everywhere, and its cutoff deficit has the exact closed-form antiderivative

```math
\int_0^T \big(\psi_{\text{lb}1}(T) - \psi_{\text{lb}1}(t)\big)\,dt = 2\arctan(2T) - \frac{T}{1/4 + T^2} + T - \frac{5}{2}\arctan\!\left(\frac{2T}{5}\right).
```

2. *(Paley–Wiener $`L^2`$ Bound & Polar Even/Odd Decoupling — `fourierTransform_norm_sq_le_L_mul_L2`, `weilPole_eq_cosh_sub_sinh`, `weilPole_even_nonneg`, `weilPole_lower_bound_all`):* Every continuous $`g`$ on $`[-L/2, L/2]`$ obeys $`\Vert \widehat{g}(t)\Vert ^2 \le L \Vert g\Vert _{L^2}^2`$, even test functions satisfy $`W_{\text{pole}}(g) \ge 0`$, and arbitrary test functions (including odd parity) satisfy the universal bound $`W_{\text{pole}}(g) \ge -2(\sinh(L/2) - L/2)\Vert g\Vert _{L^2}^2`$.
3. *(Unconditional Infinite-Dimensional Continuous Weil Positivity — `weilArch_continuous_cutoff_lower_bound`, `weilArch_continuous_pos_on_small_support`):* Combining Plancherel's identity $`\frac{1}{2\pi}\int_{-\infty}^\infty \Vert \widehat{g}(t)\Vert ^2\,dt = \Vert g\Vert _{L^2}^2`$ with the cutoff estimate at $`T = 30`$ yields, **with zero discretization and no finite-basis truncation**, for every $`0 < L \le 1/12`$ and every continuous $`g`$ on $`[-L/2, L/2]`$:

```math
W_{\text{pole}}(g) + \frac{1}{2\pi}\int_{-\infty}^\infty \psi_{\text{arch}}(t)\,\Vert \widehat{g}(t)\Vert ^2\,dt \ge \frac{1}{10}\,\Vert g\Vert _{L^2([-L/2, L/2])}^2 > 0 \qquad (\text{whenever } g \not\equiv 0).
```

4. *(Infinite-Dimensional Schur-Complement & Bandlimited Prolate Certificates — `schur_complement_hilbert_pos`, `bandlimited_prolate_comparison_pos`):* Any quadratic functional decomposing across an orthogonal splitting $`V = V_0 \oplus V_0^\perp`$ with tail coercivity $`\lambda_\perp > 0`$ and positive Schur complement on $`V_0`$ is strictly positive on the entire infinite-dimensional Hilbert space $`V`$; likewise, domination by a complementary bandlimited Prolate projection $`(I - K_\Omega)`$ with margin $`\beta > 0`$ certifies positivity unconditionally. ■

#### Theorem 6.12 (Route B — General 2D Light-Cone Hessian Identity and Constructive Explicit Zero-Free Rectangle $`(0, 1) \times [-1/5, 1/5]`$)
*In Lean 4 + Mathlib4 (`WeilArchimedeanAndExplicitCorridor.lean`), extending Theorem 6.8.2 from $`\sigma = 0`$ to arbitrary $`(\sigma, \gamma) \in \mathbb{R}^2`$ and replacing the non-constructive Tube Lemma (Theorem 6.8.4) by explicit rational moment bounds:*

1. *(Exact 2D Past–Future Light-Cone Formula & Algebraic Odd-Moment Cancellation — `xiNormSq_deriv2_eq_pastFuture_double_integral`, `xiNormSq_deriv2_ge_moment_quadratic`, `xiCritical_ge_moment_quadratic`):* For every $`(\sigma, \gamma) \in \mathbb{R}^2`$,

```math
\frac{\partial^2 V}{\partial \sigma^2}(\sigma, \gamma) = 2\int_0^\infty\!\!\int_0^\infty \Phi(u)\Phi(v)\Big[(u+v)^2\cosh(\sigma(u+v))\cos(\gamma(u-v)) + (u-v)^2\cosh(\sigma(u-v))\cos(\gamma(u+v))\Big]\,dv\,du.
```

   Applying $`\cos\theta \ge 1 - \theta^2/2`$ triggers the exact algebraic factorization $`(u+v)^2(u-v)^2 = (u^2 - v^2)^2 = u^4 - 2u^2v^2 + v^4`$ together with $`\cosh(\sigma(u+v)) + \cosh(\sigma(u-v)) = 2\cosh(\sigma u)\cosh(\sigma v)`$, **eliminating all odd moments identically** and yielding uniformly for all $`\sigma \in [0, 1/2]`$ and $`\gamma \in \mathbb{R}`$:

```math
\frac{\partial^2 V}{\partial \sigma^2}(\sigma, \gamma) \ge 8\,I_0(0)\,I_2(0) - 4\gamma^2\Big(I_0\!\left(\tfrac{1}{2}\right) I_4\!\left(\tfrac{1}{2}\right) - I_2(0)^2\Big), \qquad \Xi(\gamma) \ge 2\,I_0(0) - \gamma^2 I_2(0),
```

   where $`I_{2k}(\sigma) \triangleq \int_0^\infty u^{2k}\cosh(\sigma u)\Phi(u)\,du`$.
2. *(Constructive Explicit Convexity Corridor & Zero-Free Rectangle on Mathlib4's `riemannZeta` — `xiNormSq_deriv2_pos_explicit_corridor`, `xiNormSq_deriv1_pos_explicit_corridor`, `riemannXi_critical_pos_explicit_corridor`, `riemannZeta_ne_zero_explicit_strip_rectangle`):* Bounding $`I_0(0), I_2(0)`$ from below on $`[0, 1/4]`$ via antitonicity of the $`n=1`$ summand and $`I_0(1/2), I_2(0), I_4(1/2)`$ from above via geometric summation over $`n \ge 1`$ and quadratic completion of $`e^{2u} \ge 1 + 2u + 2u^2`$ certifies purely analytically—with **zero numerical approximations**—that for all $`\sigma \in [0, 1/2]`$ and $`|\gamma| \le 1/5`$, $`\partial_\sigma^2 V(\sigma, \gamma) > 0`$, $`\partial_\sigma V(\sigma, \gamma) > 0`$ ($`\sigma > 0`$), $`\Xi(\gamma) > 0`$, and consequently:

```math
\forall s \in \mathbb{C}, \qquad 0 < \mathrm{Re}(s) < 1 \;\land\; |\mathrm{Im}(s)| \le \frac{1}{5} \;\Longrightarrow\; \zeta(s) \neq 0. \qquad \blacksquare
```

#### Theorem 6.13 (Route B — Schoenberg Complete-Monotonicity No-Go Theorem)
*Writing $`m_2(0, \gamma) = \int_0^\infty G_{2,0}(w)\cos(\gamma w)\,dw`$ with 1D cosine kernel $`G_{2,0}(w) = \int_{-\infty}^\infty r^2 \Phi(\frac{r+w}{2})\Phi(\frac{r-w}{2})\,dr`$ ($`w \ge 0`$), a classical sufficient criterion for global Fourier-cosine positivity $`m_2(0, \gamma) > 0`$ would be complete monotonicity of $`x \mapsto G_{2,0}(\sqrt{x})`$ on $`(0, \infty)`$ (Schoenberg, 1938), i.e., a positive Gaussian/Laplace mixture representation $`G_{2,0}(\sqrt{x}) = \int_0^\infty e^{-\alpha x}\,d\mu(\alpha)`$. In Lean 4 + Mathlib4 (`WeilArchimedeanAndExplicitCorridor.lean`):*

1. *(Exponential Lower Bound for Positive Laplace Transforms — `schoenberg_laplace_exp_lower_bound`):* For every non-zero finite positive measure $`\mu`$ on $`[0, \infty)`$, there exist constants $`c > 0`$ and $`\alpha_1 > 0`$ such that $`\int_0^\infty e^{-\alpha x}\,d\mu(\alpha) \ge c\,e^{-\alpha_1 x}`$ for all $`x \ge 0`$.
2. *(Super-Exponential Decay & No-Go Obstruction — `riemannLaguerreKernel1D_superexp_le`, `riemannLaguerreKernel1D_not_schoenberg_laplace`):* Because $`\Phi(u)`$ decays doubly exponentially in $`|u|`$, $`G_{2,0}(w)`$ obeys a strict super-exponential upper bound $`G_{2,0}(w) \le C \exp(-\frac{\pi}{4} e^w)`$ for all $`w \ge 0`$. Therefore **no non-zero finite positive measure $`\mu`$ on $`[0, \infty)`$ can represent $`G_{2,0}(\sqrt{x})`$ as a Laplace transform**; any global proof of $`m_2(0, \gamma) > 0`$ along Route B must go strictly beyond Schoenberg Gaussian mixtures. ■

### 6.9 Arithmetic Continuous Weil Functional with Primes, Spectral-Flow Knife-Edge Pinch, and $`10\times`$ Expanded Constructive Strip Rectangle $`(0, 1) \times [-2, 2]`$

To carry Route A across the first arithmetic prime threshold $`L = \ln 2`$ in infinite dimensions, formalize the exact spectral-flow obstruction behind the prime-shift operator, and push Route B's constructive zero-free strip rectangle by an order of magnitude, `ArithmeticWeilAndWideCorridor.lean` (**2,187 lines, 26 headline theorems**, `0 sorry`, axioms strictly `[propext, Classical.choice, Quot.sound]`) establishes three further unconditional theorem groups directly in Lean 4 + Mathlib4:

#### Theorem 6.14 (Route A — Exact Continuous Arithmetic Weil Functional with `vonMangoldt`, Disjoint-Strip $`1/2`$-Factor Prime Bound, and $`L \le 1/8`$ Positivity)
*For any $`L > 0`$ and continuous $`g : \mathbb{R} \to \mathbb{C}`$ supported on $`[-L/2, L/2]`$, define the exact continuous prime-shift functional and total arithmetic Weil quadratic functional using Mathlib4's `ArithmeticFunction.vonMangoldt`:*

```math
W_{\text{prime}}(L, g) \triangleq 2\sum_{2 \le n \le \lfloor e^L \rfloor} \frac{\Lambda(n)}{\sqrt{n}}\,\mathrm{Re}\!\left(\int_{-L/2 + \ln n}^{L/2} g(u)\,\overline{g(u - \ln n)}\,du\right), \qquad W_{\text{total}}(L, g) \triangleq W_{\text{pole}}(L, g) + W_\infty(L, g) - W_{\text{prime}}(L, g).
```

*Define also the closed-form $`K = 3`$ digamma lower envelope $`\psi_{\text{lb}3}(t) \triangleq -C_\infty + \frac{4t^2}{1/4 + t^2} + \frac{(4/5)t^2}{25/4 + t^2} + \frac{(4/9)t^2}{81/4 + t^2} + \frac{1}{2}\ln\!\left(1 + \frac{4t^2}{169}\right)`$. Then in Lean 4 + Mathlib4:*

1. *(Exact Zero-Prime Cutoff & Disjoint-Strip $`1/2`$-Factor Shift Bound — `weilPrime_eq_zero_of_le_log_two`, `shift_overlap_re_le_L2`, `shift_overlap_re_le_half_L2_of_disjoint`, `weilPrime_single_prime_two_bound`, `weilPrime_general_norm_bound`):* For every $`0 < L \le \ln 2`$, $`W_{\text{prime}}(L, g) = 0`$. For any shift $`\delta \in [L/2, L]`$, the strips $`[-L/2, L/2 - \delta]`$ and $`[-L/2 + \delta, L/2]`$ are disjoint, cutting the standard Cauchy–Schwarz overlap bound cleanly in half via AM–GM:

```math
\left|\mathrm{Re}\int_{-L/2 + \delta}^{L/2} g(u)\,\overline{g(u - \delta)}\,du\right| \le \frac{1}{2}\int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du \qquad (L/2 \le \delta \le L).
```

   Consequently, throughout the entire single-prime regime $`\ln 2 < L < \ln 3`$ (and indeed for the $`p = 2`$ term on all $`L \in (\ln 2, \ln 4]`$), the prime functional obeys the sharp infinite-dimensional $`L^2`$ operator norm bound $`|W_{\text{prime}}(L, g)| \le \frac{\ln 2}{\sqrt{2}}\Vert g\Vert _{L^2}^2`$, while for arbitrary $`L > 0`$, $`|W_{\text{prime}}(L, g)| \le \big(2\sum_{2 \le n \le \lfloor e^L \rfloor} \Lambda(n)/\sqrt{n}\big)\Vert g\Vert _{L^2}^2`$.
2. *($`K = 3`$ Digamma Envelope & Unconditional Continuous Arithmetic Positivity on $`0 < L \le 1/8`$ — `psiArch_ge_psiLb3`, `integral_psiLb3_gap_eq`, `weilTotal_continuous_pos_up_to_one_eighth`):* $`\psi_{\text{arch}}(t) \ge \psi_{\text{lb}3}(t)`$ for all $`t \in \mathbb{R}`$, the cutoff gap $`\int_0^T (\psi_{\text{lb}3}(T) - \psi_{\text{lb}3}(t))\,dt`$ admits an exact closed-form elementary antiderivative, and evaluating at $`T = 25`$ certifies **with zero discretization** for all $`0 < L \le 1/8`$ ($`1.5\times`$ wider than Theorem 6.11.3) and every continuous $`g`$ on $`[-L/2, L/2]`$:

```math
W_{\text{total}}(L, g) \ge \frac{1}{20}\,\Vert g\Vert _{L^2([-L/2, L/2])}^2 > 0 \qquad (\text{whenever } g \not\equiv 0).
```

3. *(Prime-Active Infinite-Dimensional Hilbert Schur Complement — `schur_complement_hilbert_pos_with_primes`):* Across an orthogonal splitting $`v = v_0 + v_\perp`$, whenever tail Archimedean coercivity $`\lambda_\perp`$ strictly dominates the prime-shift operator norm $`p_{\text{norm}}`$ ($`\lambda_\perp - p_{\text{norm}} > 0`$), cross-coupling obeys $`|B(v_0, v_\perp)| \le C\Vert v_0\Vert \Vert v_\perp\Vert `$, and the finite-dimensional block satisfies $`Q_0(v_0) \ge (C^2/(\lambda_\perp - p_{\text{norm}}) + \delta)\Vert v_0\Vert ^2`$ ($`\delta > 0`$), the full arithmetic quadratic form $`Q_0 + 2B + Q_{\perp,\text{arch}} - Q_{\perp,\text{prime}}`$ is strictly positive on every non-zero vector $`(v_0, v_\perp)`$. ■

#### Theorem 6.15 (Route A — Spectral-Flow Concavity, Two-Sided Knife-Edge Pinch, Partition Function Convexity, and Resolvent Positivity)
*For any real quadratic forms $`Q_{\text{arch}}, Q_{\text{prime}} : V \to \mathbb{R}`$ parameterized by the spectral-flow coupling $`\eta \in \mathbb{R}`$ as $`Q_\eta(v) \triangleq Q_{\text{arch}}(v) - \eta\, Q_{\text{prime}}(v)`$, Lean 4 + Mathlib4 (`ArithmeticWeilAndWideCorridor.lean`) establishes unconditionally:*

1. *(Spectral-Flow Concavity & Convexity of the Positivity Coupling Set — `spectral_flow_min_concave`, `spectral_flow_pos_set_convex`):* The pointwise infimum $`\eta \mapsto \inf_{v \in S} Q_\eta(v)`$ is concave on $`\mathbb{R}`$, and the positivity coupling set $`\{\eta \in \mathbb{R} : \forall v \in V,\; Q_{\text{arch}}(v) - \eta\, Q_{\text{prime}}(v) \ge 0\}`$ is convex.
2. *(Two-Sided Knife-Edge Coupling Pinch — `spectral_flow_arch_neg_forces_prime_neg`, `spectral_flow_two_sided_pinch`):* Whenever $`Q_{\text{arch}}`$ develops a negative mode $`Q_{\text{arch}}(v_-) < 0`$ (which occurs for every $`L > L_0^{\ast}(\text{ODD}) \approx 0.760068`$) and $`Q_{\text{prime}}`$ admits a positive mode $`Q_{\text{prime}}(v_+) > 0`$, any coupling $`\eta \ge 0`$ restoring global positivity $`Q_\eta \ge 0`$ forces $`Q_{\text{prime}}(v_-) < 0`$ and traps $`\eta`$ strictly inside the two-sided pinch:

```math
\frac{Q_{\text{arch}}(v_-)}{Q_{\text{prime}}(v_-)} \;\le\; \eta \;\le\; \frac{Q_{\text{arch}}(v_+)}{Q_{\text{prime}}(v_+)}.
```

   In particular, positivity of the full Weil form ($`\eta = 1`$) cannot arise from any positive-definite norm bound on $`W_{\text{prime}}`$: the indefinite prime operator must cancel every negative Archimedean mode simultaneously from below while never overshooting any positive prime mode from above.
3. *(Spectral Partition Function & Resolvent Characterization — `spectral_partition_pos_and_convex`, `spectral_resolvent_pos_iff_nonneg`):* For any nonempty finite spectrum $`\{\lambda_k\}_{k \in I}`$, the spectral partition function $`Z(\beta) = \sum_{k \in I} e^{-\beta \lambda_k}`$ is strictly positive and convex on $`\mathbb{R}`$; moreover, for any quadratic energy $`Q`$ and norm $`N > 0`$, shifted resolvent positivity $`Q + E\,N > 0`$ for all $`E > 0`$ holds if and only if $`Q \ge 0`$. ■

#### Theorem 6.16 (Route B — Exact Identity $`I_0(1/2) = 1/4`$, $`10\times`$ Expanded Constructive Strip Rectangle $`(0, 1) \times [-2, 2]`$, Sharp Hyperbolic Decay, and Logarithmic Force Reduction)
*In Lean 4 + Mathlib4 (`ArithmeticWeilAndWideCorridor.lean`), sharpening both the constructive zero-free corridor (Theorem 6.12) and the decay/potential hierarchy (Theorems 6.8 and 6.13):*

1. *(Exact Closed-Form Boundary Moment & Antitonicity of $`\Phi`$ — `integral_phi_cosh_half_eq_quarter`, `riemannPhi_antitoneOn_from_one_fiftieth`):* Evaluating `riemannXi_re_im_pastFuture_phi` at $`s = 1`$ ($`\xi(1) = 1/2 = 2 I_0(1/2)`$) proves the **exact closed-form identity**

```math
I_0\!\left(\tfrac{1}{2}\right) = \int_0^\infty \Phi(u)\cosh\!\left(\tfrac{u}{2}\right) du = \frac{1}{4}
```

   with zero approximation loss. Furthermore, differentiating term-by-term shows that every summand $`\Phi_n(u)`$ satisfies $`\Phi_n'(u) = X(-8X^2 + 30X - 15)\theta_n(u) \le 0`$ whenever $`X = \pi(n+1)^2 e^{2u} \ge 16/5`$, proving unconditionally that $`\Phi(u)`$ is antitone on $`[1/50, \infty)`$.
2. *($`10\times`$ Expanded Constructive Strip Rectangle $`(0, 1) \times [-2, 2]`$ and $`20\times`$ Critical-Line Positivity $`|\gamma| \le 4`$ — `xiNormSq_deriv2_pos_corridor_two`, `xiNormSq_deriv1_pos_corridor_two`, `riemannXi_critical_pos_corridor_four`, `riemannZeta_ne_zero_explicit_strip_rectangle_two`):* Combining $`I_0(1/2) = 1/4`$ with a 9-bin antitone Riemann grid on $`[0, 1]`$ and an exact analytic exponential tail on $`[1, \infty)`$ certifies purely analytically that $`I_0(0) \ge 195/1000`$, $`77/10000 \le I_2(0) \le 175/10000`$, and $`I_4(1/2) \le 285/100000`$. Consequently, $`\partial_\sigma^2 V(\sigma, \gamma) > 0`$ on $`[0, 1/2] \times [-2, 2]`$, $`\partial_\sigma V(\sigma, \gamma) > 0`$ on $`(0, 1/2] \times [-2, 2]`$, $`\Xi(\gamma) > 0`$ for all $`|\gamma| \le 4`$, and directly on Mathlib4's `riemannZeta`:

```math
\forall s \in \mathbb{C}, \qquad 0 < \mathrm{Re}(s) < 1 \;\land\; |\mathrm{Im}(s)| \le 2 \;\Longrightarrow\; \zeta(s) \neq 0.
```

3. *(Sharp Hyperbolic-Type Decay & Logarithmic Potential Force Equivalence — `riemannLaguerreKernel1D_sharp_hyperbolic_le`, `xiLogForce_eq_force_div_normSq`, `xiLogForce_pos_iff_force_pos`, `riemannHypothesis_of_xiLogForcePos`, `xiTransverseHessian_ge_of_logConvex`):* Tightening Theorem 6.13.2 by a factor of $`6\times`$ yields $`G_{2,0}(w) \le C \exp(-\frac{3\pi}{2} e^w)`$ for all $`w \ge 0`$, matching the exact exponential growth scale in the hyperbolic geodesic variable $`y = \cosh w - 1`$. Defining the logarithmic transverse force $`\partial_\sigma (\ln V(\sigma, \gamma)) = \partial_\sigma V / V = 2\mathrm{Re}(\xi'/\xi)`$ (Lagarias, 1999), positivity of $`\partial_\sigma(\ln V)`$ on $`(0, 1/2) \times \mathbb{R}`$ implies `RiemannHypothesis` unconditionally, while logarithmic convexity $`\partial_\sigma^2(\ln V) \ge 0`$ strictly dominates transverse convexity via $`\partial_\sigma^2 V \ge (\partial_\sigma V)^2 / V \ge 0`$. ■

### 6.10 Universal Finite-Codimension Weil Coercivity, Herglotz–Pick Spectral Resolvent Remote Detection, All-Order Light-Cone Parity Separation, and Angular Strip Compactification

To prove unconditionally that infinite-dimensional tail coercivity holds for **every** support horizon $`L > 0`$ regardless of how many primes are active, introduce a global analytic continuation detector capable of identifying off-line zeros remotely from $`\mathrm{Re}(s) = 1`$, and extend Route B's exact 2D light-cone machinery to arbitrary orders alongside zero simplicity and angular strip compactification, `UniversalWeilAndHerglotzResolvent.lean` (**1,454 lines, 18 headline theorems**, `0 sorry`, axioms strictly `[propext, Classical.choice, Quot.sound]`) establishes three further unconditional theorem groups directly in Lean 4 + Mathlib4:

#### Theorem 6.17 (Route A — Universal Finite-Codimension Coercivity of the Full Arithmetic Weil Functional for ALL $`L > 0`$)
*For every support width $`L > 0`$, define the refined split prime-shift weight $`P_{\text{ref}}(L) \triangleq \sum_{2 \le n \le \lfloor e^L \rfloor} \big(\mathbf{1}_{L/2 \le \ln n} + 2\,\mathbf{1}_{\ln n < L/2}\big)\frac{\Lambda(n)}{\sqrt{n}}`$. Then in Lean 4 + Mathlib4 (`UniversalWeilAndHerglotzResolvent.lean`):*

1. *(Unit-Circle Complex Taylor Remainder & Moment-Orthogonal Fourier Suppression — `norm_exp_neg_I_sub_taylor_le`, `exists_pow_div_factorial_lt`, `compactFourier_norm_sq_le_of_moment_orthog`):* For every $`N \in \mathbb{N}`$ and $`x \in \mathbb{R}`$,

```math
\left\Vert e^{-ix} - \sum_{m=0}^{N-1} \frac{(-ix)^m}{m!}\right\Vert  \le \frac{|x|^N}{N!}.
```

   Consequently, whenever a continuous function $`g : \mathbb{R} \to \mathbb{C}`$ on $`[-L/2, L/2]`$ is orthogonal to the finite polynomial subspace $`V_N = \mathrm{span}\{1, u, \dots, u^{N-1}\}`$ ($`\int_{-L/2}^{L/2} g(u)\,u^m\,du = 0`$ for all $`m < N`$), its compact Fourier transform is super-exponentially suppressed on every low-frequency band $`|t| \le T`$:

```math
\Vert \widehat{g}(t)\Vert ^2 \le L\left(\frac{(L T / 2)^N}{N!}\right)^2 \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du \qquad (|t| \le T).
```

2. *(Refined Split Prime-Shift Bound — `weilPrime_refined_norm_bound`):* Separating prime powers into disjoint shifts ($`\ln n \ge L/2`$, Theorem 6.14.1's $`1/2`$-factor) and overlapping shifts ($`\ln n < L/2`$) sharpens the universal prime-shift norm bound for every $`L > 0`$ to $`|W_{\text{prime}}(L, g)| \le P_{\text{ref}}(L)\,\Vert g\Vert _{L^2}^2`$.
3. *(Universal Finite-Codimension Coercivity & Strict Positivity for ALL $`L > 0`$ — `weilTotal_universal_finite_codim_coercive`, `weilTotal_strict_pos_on_finite_codim`):* Because $`\psi_{\text{arch}}(t) \ge \psi_{\text{lb}3}(t) \to +\infty`$ logarithmically while $`W_{\text{pole}}`$ and $`W_{\text{prime}}`$ are bounded $`L^2`$-operators for each fixed $`L > 0`$, for **every $`L > 0`$** (with arbitrarily many active `vonMangoldt` primes) and **every coercivity level $`c \in \mathbb{R}`$**, there exists an explicit finite codimension $`N \in \mathbb{N}`$ such that every continuous $`g`$ orthogonal to $`V_N`$ obeying Plancherel satisfies:

```math
W_{\text{total}}(L, g) \ge c \int_{-L/2}^{L/2} \Vert g(u)\Vert ^2\,du,
```

   and in particular $`W_{\text{total}}(L, g) > 0`$ whenever $`\Vert g\Vert _{L^2} > 0`$. This proves unconditionally with zero discretization that the essential high-frequency spectrum of the full arithmetic Weil operator is $`+\infty`$ for **every** $`L > 0`$, reducing infinite-dimensional Weil positivity on any compact support $`[-L, L]`$ strictly to a finite-dimensional complement block. ■

#### Theorem 6.18 (Spectral Resolvent $`\mathcal{R}_\xi`$, Cauchy–Riemann Phase Law, Herglotz–Pick Matrix PSD, Stieltjes–Perron IDOS, and Remote Off-Line Zero Detection)
*Define the spectral resolvent of Mathlib4's completed Xi function on the upper half-plane $`\mathbb{H} = \{z = \gamma + i\sigma : \sigma > 0\}`$ by:*

```math
\mathcal{R}_\xi(z) \triangleq i\,\frac{\xi'}{\xi}\!\left(\frac{1}{2} - i z\right).
```

*Then in Lean 4 + Mathlib4 (`UniversalWeilAndHerglotzResolvent.lean`):*

1. *(Exact Logarithmic-Force & Cauchy–Riemann Phase-Derivative Duality — `xiResolvent_im_eq_logForce_half`, `xiResolvent_im_eq_phase_deriv_gamma`, `riemannHypothesis_of_xiResolventHerglotz`):* At every point $`z = \gamma + i\sigma`$ where $`\xi(\frac{1}{2} + \sigma + i\gamma) \neq 0`$,

```math
\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) = \mathrm{Re}\!\left(\frac{\xi'}{\xi}\!\left(\frac{1}{2} + \sigma + i\gamma\right)\right) = \frac{1}{2}\,\partial_\sigma\ln V(\sigma, \gamma) = \partial_\gamma \Theta(\sigma, \gamma),
```

   where $`\partial_\gamma \Theta \triangleq \frac{\mathrm{Re}(\xi)\,\partial_\gamma\mathrm{Im}(\xi) - \mathrm{Im}(\xi)\,\partial_\gamma\mathrm{Re}(\xi)}{\Vert \xi\Vert ^2}`$ is the exact unwrapped phase derivative along the vertical line $`\mathrm{Re}(s) = \frac{1}{2} + \sigma`$. Consequently, the Herglotz–Nevanlinna positivity condition $`\mathrm{Im}\mathcal{R}_\xi(\gamma + i\sigma) > 0`$ on $`0 < \sigma < 1/2`$ implies Mathlib4's official `RiemannHypothesis` unconditionally.
2. *(Exact Herglotz–Pick–Nevanlinna & Stieltjes–Perron IDOS Laws for Critical-Line Pole Families — `resolventCritSum_herglotz_and_schwarzPick`, `resolventCritSum_pickMatrix_psd`, `resolventCritSum_idos_integral`):* For any finite family of real poles $`\{\gamma_m\}_{m \in I}`$ with weights $`w_m > 0`$, the critical-line resolvent $`G(z) = \sum_{m \in I} \frac{w_m}{\gamma_m - z}`$ obeys unconditionally for all $`z, z_1, \dots, z_n \in \mathbb{H}`$ and $`c \in \mathbb{C}^n`$:
   - Herglotz positivity $`\mathrm{Im} G(z) > 0`$ and exact **Schwarz–Pick hyperbolic contraction** $`\mathrm{Im}(z)\,\Vert G'(z)\Vert  \le \mathrm{Im} G(z)`$;
   - **All-order Hermitian Pick–Nevanlinna Matrix PSD** (Pick, 1916; Herglotz, 1911):

```math
\mathrm{Re}\sum_{j, k} \overline{c_j}\,c_k\,\frac{G(z_j) - \overline{G(z_k)}}{z_j - \overline{z_k}} = \sum_{m \in I} w_m\left\Vert \sum_j \frac{c_j}{\gamma_m - z_j}\right\Vert ^2 \ge 0;
```

   - **Exact Stieltjes–Perron Integrated Density of States (IDOS) Integral** (Stieltjes, 1894):

```math
\frac{1}{\pi}\int_{-\infty}^\infty \mathrm{Im} G(\gamma + i\sigma)\,d\gamma = \sum_{m \in I} w_m \qquad (\forall \sigma > 0).
```

3. *(Remote Off-Line Zero Detection Theorem — `resolventOfflinePair_exact_and_remote_violation`):* For any symmetric off-line zero pair $`\frac{1}{2} \pm \delta + i\gamma_0`$ ($`\delta > 0`$), the dipole resolvent $`G_{\text{off}}(z) = \frac{1}{\gamma_0 + i\delta - z} + \frac{1}{\gamma_0 - i\delta - z}`$ satisfies $`\mathrm{Im} G_{\text{off}}(\gamma_0 + i\sigma) = \frac{2\sigma}{\sigma^2 - \delta^2} < 0`$ inside $`0 < \sigma < \delta`$, **and for every remote height $`\sigma > \delta`$ (even at $`\sigma = 1/2`$, i.e. $`\mathrm{Re}(s) = 1`$, where $`\mathrm{Im} G_{\text{off}} > 0`$ and $`m_2 > 0`$ are blind)** it strictly violates Schwarz–Pick hyperbolic contraction with the exact ratio:

```math
\frac{\sigma\,\Vert G_{\text{off}}'(\gamma_0 + i\sigma)\Vert }{\mathrm{Im} G_{\text{off}}(\gamma_0 + i\sigma)} = \frac{\sigma^2 + \delta^2}{\sigma^2 - \delta^2} > 1 \qquad (\forall \sigma > \delta). \qquad \blacksquare
```

#### Theorem 6.19 (Route B — All-Order 2D Light-Cone Parity Separation, Local RH + Zero-Simplicity Theorem, and Compactified Angular Strip $`\beta(\theta) = \cos^2(\theta/2)`$)
*In Lean 4 + Mathlib4 (`UniversalWeilAndHerglotzResolvent.lean`), completing the all-order light-cone and angular-coordinate formalization of Route B:*

1. *(All-Order 2D Light-Cone Parity Separation Identity — `lightCone_even_power_parity_identity`):* Generalizing Theorem 6.12.1's $`k = 1`$ identity to every even order $`2k \in 2\mathbb{N}`$,

```math
\begin{aligned}
&(u + v)^2 (u - v)^{2k}\cosh(\sigma(u + v)) + (u - v)^2 (u + v)^{2k}\cosh(\sigma(u - v)) \\
&\quad = \Big[(u + v)^2(u - v)^{2k} + (u - v)^2(u + v)^{2k}\Big]\cosh(\sigma u)\cosh(\sigma v) + \Big[(u + v)^2(u - v)^{2k} - (u - v)^2(u + v)^{2k}\Big]\sinh(\sigma u)\sinh(\sigma v),
\end{aligned}
```

   reducing every Taylor coefficient $`\mu_{2k}(\sigma)`$ of $`m_2(\sigma, \gamma)`$ identically to a finite bilinear combination of 1D $`\cosh`$- and $`\sinh`$-moments of $`\Phi(u)`$.
2. *(Local RH & Strict Zero-Simplicity Theorem — `riemannHypothesis_local_and_simple_of_hessianPos`):* For any height $`\Gamma \ge 0`$, if $`\partial_\sigma^2 V(\sigma, \gamma) > 0`$ uniformly on $`[0, 1/2] \times [-\Gamma, \Gamma]`$, then unconditionally:
   - **Local RH:** every zero $`s`$ of Mathlib4's `riemannZeta` in the critical strip $`0 < \mathrm{Re}(s) < 1`$ with $`|\mathrm{Im}(s)| \le \Gamma`$ lies strictly on the critical line $`\mathrm{Re}(s) = 1/2`$; and
   - **Strict Simplicity:** every critical-line zero $`\Xi(\gamma) = 0`$ with $`|\gamma| \le \Gamma`$ is strictly simple ($`\Xi'(\gamma) \neq 0`$), directly via Theorem 6.8.2's identity $`\partial_\sigma^2 V|_{0} = 2((\Xi')^2 - \Xi\Xi'')`$.
3. *(Compactified Angular Strip Coordinate & Kinetic Barrier — `stripAngle_geometry_and_barrier`, `xiNormSq_angular_deriv_eq`, `riemannHypothesis_of_angularDescent`):* Parameterizing the open critical strip $`(0, 1)`$ by the angular coordinate $`\theta \in (0, \pi)`$ via $`\beta(\theta) \triangleq \cos^2(\theta/2) = \frac{1}{2} + \frac{1}{2}\cos\theta`$ maps functional reflection cleanly to $`\beta(\pi - \theta) = 1 - \beta(\theta)`$, carries the exact positive-definite kinetic barrier

```math
\frac{1}{2\beta(\theta)(1 - \beta(\theta))} = \frac{2}{\sin^2\theta} \ge 2 \qquad (\text{uniquely minimized at } \theta = \tfrac{\pi}{2} \iff \beta = \tfrac{1}{2}),
```

   satisfies $`\partial_\theta V(\frac{1}{2}\cos\theta, \gamma) = -\frac{1}{2}\sin\theta\,\partial_\sigma V(\frac{1}{2}\cos\theta, \gamma)`$, and yields an unconditional angular-descent reduction $`-\partial_\theta V(\frac{1}{2}\cos\theta, \gamma) > 0`$ on $`(0, \pi/2) \times \mathbb{R} \implies`$ `RiemannHypothesis`. ■

---

> [← Part 4](04_bohr_torus_adeles_and_weil_positivity.md) · [Paper Index](../ON_THE_UNIFIED_GEODESIC_DIPOLAR_FRAMEWORK_AND_RIEMANN_ZETA.md) · [Part 6 →](06_hermite_biehler_lyapunov_and_limit_barriers.md)
