/-
  ==============================================================================
  MODULE #16: ROUTE A GEODESIC PULLBACK INVARIANCE, UV/IR JERK SEPARATION, AND
              EXACT WEIL-CHEBYSHEV RENORMALIZATION; ROUTE B JACOBI THETA MODULAR
              CONSERVATION LAWS, GLOBAL EULER HALF-PLANE HERGLOTZ POSITIVITY,
              AND SYMMETRIC JACOBI DIAGONAL PRECONDITIONING ON PICK MATRICES
              (LEAN 4 + MATHLIB4)
  ==============================================================================

  Author: Mariano Martín Ramírez Tamayo
  Affiliation: Independent Researcher

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):

  PART I (ROUTE A — GEODESIC COMPACTIFICATION INVARIANCE, UV/IR SEPARATION OF
          HIGHER-ORDER JERK REGULARIZATION, & EXACT WEIL-CHEBYSHEV [∞ - ∞]
          RENORMALIZATION IDENTITY):
    1. `geodesicPullback_L2_isometry`, `stereographic_pullback_L2_isometry`, &
       `quadraticForm_bijective_pullback_invariance`:
       Any smooth monotone compactification `τ : [a, b] → [τ a, τ b]` (specifically
       stereographic compactification `u = tan θ` into `S^1 ⊂ T^2 ⊂ S^3`) induces
       an exact L^2 isometry `(U_τ g)(θ) = g(τ θ) * √(τ' θ)`, preserving the exact
       Rayleigh quotient infimum and sign structure of any Hermitian quadratic form.
       Hence geodesic compactification smooths coordinates at infinity without
       altering negative eigenvalues or circumventing the Finite-Prime Wall.
    2. `oddSinMode_iteratedDeriv_L2_norm_sq`:
       Exact closed-form energy of the `k`-th spatial derivative on `oddSinMode L`:
         `∫_{-L/2}^{L/2} (iteratedDeriv k (fun x => sin (2πx / L)) x)^2 dx = (2π / L)^(2k) * (L / 2)`.
       Covers Navier-Stokes viscosity (`k = 1`), biharmonic (`k = 2`), and 3rd-order
       Jerk dissipation (`k = 3`).
    3. `weilTruncated_with_jerk_eventually_neg` (UV/IR SEPARATION THEOREM):
       For EVERY finite prime cutoff `N_max : ℕ`, EVERY hyperviscosity/Jerk order `k ≥ 1`,
       and EVERY regularization coupling `ε > 0`, there exists `L_0 > 0` such that for
       EVERY `L ≥ L_0`:
         `W_pole(L, g_L) + W_∞(L, g_L) + ε * ‖g_L^(k)‖_2^2 - W_{prime, ≤ N_max}(L, g_L) < 0`.
       Formally separates UV blow-up obstructions (Navier-Stokes, where `(2π/L)^(2k) → ∞`
       as `L → 0`) from Route A's IR pole obstruction (`(2π/L)^(2k) → 0` as `L → ∞`).
    4. `chebyshevPsi_step_stieltjes_ibp`, `weilPole_sub_weilPrime_exact_chebyshev_renormalization`,
       & `oddSinMode_autocorr_exact_and_renormalized`:
       EXACT `[∞ - ∞]` WEIL-CHEBYSHEV RENORMALIZATION FOR EVERY `L > 0`:
       For EVERY `L > 0` and EVERY `C^1` function `h` on `[0, L]` with `h(L) = 0`,
       the exponentially growing pole term `2 ∫_0^L h(u) e^{u/2} du` cancels IDENTICALLY
       against the macroscopic PNT term `dx` of `dψ(x) = dx + d(ψ(x) - x)`:
         `2 ∫_0^L h(u) (e^{u/2} + e^{-u/2}) du - 2 ∑_{n=2}^{⌊e^L⌋} (Λ(n)/√n) h(log n)
           = -2 h(0) + 2 ∫_0^L h(u) e^{-u/2} du
             + 2 ∫_0^L ((ψ(e^u) - e^u) / e^{u/2}) * (h'(u) - (1/2) h(u)) du`.

  PART II (ROUTE B — JACOBI THETA MODULAR CONSERVATION LAWS & GLOBAL UNCONDITIONAL
           EULER HALF-PLANE HERGLOTZ-SCHUR-DE BRANGES POSITIVITY):
    5. `jacobiPsi_modular_conservation_order_one_and_three`:
       Directly from Jacobi theta modular duality `1 + 2 ψ(1/t) = √t (1 + 2 ψ(t))`, proves
       the exact modular conservation laws at `t = 1`:
         Order 1: `4 ψ'(1) + ψ(1) + 1/2 = 0`,
         Order 3: `32 ψ'''(1) + 120 ψ''(1) - 15 ψ(1) - 15/2 = 0`,
       and genuine smooth stationarity `HasDerivAt riemannPhi 0 0`.
    6. `complex_digamma_re_ge_real_add_finset` & `complex_digamma_real_mono`:
       Elementary proof via `Complex.GammaSeq_tendsto_Gamma` and log-convexity of `Real.Gamma`
       that for ALL `x > 0`, `y : ℝ`, and `K : ℕ`:
         `(Complex.digamma ⟨x, y⟩).re ≥ (Complex.digamma x).re + ∑_{k < K} y^2 / ((x+k)((x+k)^2 + y^2))`.
    7. `vonMangoldt_lseries_norm_le_tsum` & `vonMangoldt_lseries_norm_le_of_eight_le`:
       Uniform-in-`γ` Euler-product `LSeries` norm bounds for `ArithmeticFunction.vonMangoldt`,
       proving `‖L(Λ, ⟨β, -γ⟩)‖ ≤ 1 / 200` for all `β ≥ 8` and all `γ : ℝ`.
    8. `xiResolvent_herglotz_global_euler_halfPlane` (GLOBAL EULER HALF-PLANE POSITIVITY):
       For EVERY `σ ≥ 15 / 2` (`Re(s) ≥ 8`) and EVERY `γ : ℝ` (all heights to `±∞`!):
         (a) `0 < (xiResolvent (γ + iσ)).im` (global Herglotz positivity),
         (b) `0 < deriv (fun s => xiNormSq s γ) σ` and `0 < xiLogForce σ γ`,
         (c) `0 < (logDeriv (xiSchur σ) γ).im` (positive de Branges boundary phase velocity),
         (d) `‖xiSchur α (γ + iσ)‖ < 1` whenever `0 < α`, `0 < σ`, `15 / 2 ≤ |σ - α|`.
    9. `xiResolvent_herglotz_euler_large_gamma_all_gt_half` (HIGH-ORDINATE EULER TAILS):
       For EVERY `σ > 1 / 2` (arbitrarily close to the critical strip boundary `Re(s) = 1`),
       there exists `Γ > 0` such that for EVERY `γ : ℝ` with `Γ ≤ |γ|`:
         `0 < (xiResolvent (γ + iσ)).im`, `0 < deriv (fun s => xiNormSq s γ) σ`, and
         `0 < (logDeriv (xiSchur σ) γ).im`.

  PART III (ROUTE B — SYMMETRIC JACOBI DIAGONAL CLIPPER `D^{-1/2} P D^{-1/2} = I - T_J`
            COUPLED TO THE UNIVERSAL HOPFIELD-BOLTZMANN SOLVER ON PICK MATRICES):
   10. `jacobiClipMatrix_congruence_hermitian_psd`:
       Exact Sylvester congruence equivalence for any Hermitian matrix `P` with positive diagonal:
         `P ⪰_Herm 0 ↔ D^{-1/2} P D^{-1/2} ⪰_Herm 0 ↔ ∀ c, Re⟨c, T_J c⟩ ≤ ‖c‖_2^2`.
   11. `jacobiClip_hermitian_psd_of_inf_norm_le_one` & `jacobiClip_hermitian_pos_of_inf_norm_lt_one`:
       O(N^2) Gershgorin-Jacobi certification: `‖T_J‖_∞ ≤ 1` (`< 1`) unconditionally implies
       `P ⪰_Herm 0` (`P ≻_Herm 0`).
   12. `dampedJacobi_universalSolver_coupling_psd` &
       `jacobiClip_pick_iff_universalSolver_freeEnergy_nonneg`:
       Setting `μ = 1 + M` where `‖T_J‖_∞ ≤ M` guarantees in O(N^2) (without eigensolving)
       that the damped Jacobi Universal Solver coupling `Q = I - (1/μ) P_hat_tilde` is PSD
       (excluding period-2 cycles via Module #14), with exact equivalence
         `P ⪰_Herm 0 ↔ ∀ s ∈ (-1, 1)^{2n}, L_Q(s) ≥ 0`.
   13. `pickMatrix_jacobiClip_unconditional_pos_of_diagDom`:
       Unconditional strict positive-definiteness of any `n × n` Pick-Nevanlinna matrix of
       `xiResolvent` on upper half-plane nodes satisfying `Im R_ξ(z_j) > 0` and `‖T_J‖_∞ < 1`.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import RiemannDipolar.RouteABLimitBarriersAndDeBrangesSynthesis

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators Pointwise
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick UniversalSolverLyapunovAndPrimeResolvent
open RouteABLimitBarriersAndDeBrangesSynthesis

namespace GeodesicRenormalizationAndEulerJacobiPick

-- ==============================================================================
-- PART I: ROUTE A — GEODESIC PULLBACK ISOMETRY, UV/IR JERK SEPARATION, AND
--         EXACT WEIL-CHEBYSHEV [∞ - ∞] RENORMALIZATION IDENTITY
-- ==============================================================================

/-- THEOREM I.1A (EXACT L^2 ISOMETRY OF SMOOTH MONOTONE GEODESIC PULLBACK):
    For any smooth coordinate map `τ` with continuous non-negative derivative `τ'` on `[a, b]`
    and any continuous `g : ℝ → ℂ`, the weighted pullback `(U_τ g)(θ) = g(τ θ) * √(τ' θ)`
    is an EXACT L^2 isometry onto `[τ a, τ b]`. -/
theorem geodesicPullback_L2_isometry {a b : ℝ} {τ τ' : ℝ → ℝ}
    (hderiv : ∀ θ ∈ Set.uIcc a b, HasDerivAt τ (τ' θ) θ)
    (hcont' : ContinuousOn τ' (Set.uIcc a b))
    (hnn' : ∀ θ ∈ Set.uIcc a b, 0 ≤ τ' θ)
    {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ θ in a..b, ‖g (τ θ) * ((Real.sqrt (τ' θ) : ℝ) : ℂ)‖ ^ 2 =
      ∫ u in (τ a)..(τ b), ‖g u‖ ^ 2 := by
  have heq : ∀ θ ∈ Set.uIcc a b,
      ‖g (τ θ) * ((Real.sqrt (τ' θ) : ℝ) : ℂ)‖ ^ 2 = ((fun u => ‖g u‖ ^ 2) ∘ τ) θ * τ' θ := by
    intro θ hθ
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (hnn' θ hθ)]
    rfl
  rw [intervalIntegral.integral_congr heq]
  exact intervalIntegral.integral_comp_mul_deriv hderiv hcont' ((continuous_norm.comp hg).pow 2)

/-- THEOREM I.1B (STEREOGRAPHIC COMPACTIFICATION PULLBACK `u = tan θ` ON `S^1 ⊂ T^2 ⊂ S^3`):
    Mapping `[-L/2, L/2] ⊂ ℝ` into the compact circular arc `[arctan(-L/2), arctan(L/2)] ⊂ (-π/2, π/2)`
    via `u = tan θ` (`du = dθ / cos^2 θ`) yields an exact L^2 isometry for every `L > 0`. -/
theorem stereographic_pullback_L2_isometry {L : ℝ} {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ θ in (Real.arctan (-L / 2))..(Real.arctan (L / 2)),
      ‖g (Real.tan θ) / ((Real.cos θ : ℝ) : ℂ)‖ ^ 2 =
    ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hcos_pos : ∀ θ ∈ Set.uIcc (Real.arctan (-L / 2)) (Real.arctan (L / 2)), 0 < Real.cos θ := by
    intro θ hθ
    have h1 : -(Real.pi / 2) < Real.arctan (-L / 2) := Real.neg_pi_div_two_lt_arctan _
    have h2 : Real.arctan (-L / 2) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have h3 : -(Real.pi / 2) < Real.arctan (L / 2) := Real.neg_pi_div_two_lt_arctan _
    have h4 : Real.arctan (L / 2) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hlo : -(Real.pi / 2) < θ := lt_of_lt_of_le (lt_min h1 h3) hθ.1
    have hhi : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 (max_lt h2 h4)
    exact Real.cos_pos_of_mem_Ioo ⟨hlo, hhi⟩
  have hderiv : ∀ θ ∈ Set.uIcc (Real.arctan (-L / 2)) (Real.arctan (L / 2)),
      HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ :=
    fun θ hθ => Real.hasDerivAt_tan (ne_of_gt (hcos_pos θ hθ))
  have hcont' : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2)
      (Set.uIcc (Real.arctan (-L / 2)) (Real.arctan (L / 2))) :=
    continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
      (fun θ hθ => pow_ne_zero 2 (ne_of_gt (hcos_pos θ hθ)))
  have hnn' : ∀ θ ∈ Set.uIcc (Real.arctan (-L / 2)) (Real.arctan (L / 2)),
      0 ≤ 1 / Real.cos θ ^ 2 := fun θ _ => by positivity
  have hiso := geodesicPullback_L2_isometry hderiv hcont' hnn' hg
  rw [Real.tan_arctan, Real.tan_arctan] at hiso
  rw [← hiso]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  have hc := hcos_pos θ hθ
  have hsq : Real.sqrt (1 / Real.cos θ ^ 2) = 1 / Real.cos θ := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq (le_of_lt hc)]
  rw [hsq]
  simp only [div_eq_mul_inv, Complex.ofReal_inv, one_mul]

/-- THEOREM I.1C (SPECTRAL / SIGN INVARIANCE UNDER ANY BIJECTIVE GEODESIC PULLBACK):
    If `U : E ≃ F` is ANY bijection between function spaces (e.g. compactification onto `T^2`,
    `S^3`, or `S^3 / Γ_120`, or a Sundman time reparametrization), then the transported quadratic
    form `Q_compact(v) = Q(U.symm v)` is non-negative on `F` if and only if `Q` is non-negative
    on `E`. No geodesic compactification can remove a negative eigenvalue or evade Route A's wall. -/
theorem quadraticForm_bijective_pullback_invariance {E F : Type*} (U : E ≃ F) (Q : E → ℝ) :
    (∀ v : F, 0 ≤ Q (U.symm v)) ↔ (∀ u : E, 0 ≤ Q u) := by
  constructor
  · intro hF u
    simpa using hF (U u)
  · intro hE v
    exact hE (U.symm v)

/-- Helper: exact iterated derivative of `sin(ω * x)` and `cos(ω * x)` for every order `k : ℕ`. -/
private lemma iteratedDeriv_sin_cos_mul (ω : ℝ) :
    ∀ k : ℕ,
      (iteratedDeriv k (fun x : ℝ => Real.sin (ω * x)) =
        fun x => if k % 2 = 0 then ((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.sin (ω * x)
                 else ((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.cos (ω * x)) ∧
      (iteratedDeriv k (fun x : ℝ => Real.cos (ω * x)) =
        fun x => if k % 2 = 0 then ((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.cos (ω * x)
                 else -((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.sin (ω * x)) := by
  intro k
  induction k with
  | zero =>
    constructor <;> (ext x; simp)
  | succ k ih =>
    constructor
    · rw [iteratedDeriv_succ, ih.1]
      ext x
      by_cases hk : k % 2 = 0
      · have hk1 : (k + 1) % 2 ≠ 0 := by omega
        have hdiv : (k + 1) / 2 = k / 2 := by omega
        simp only [hk, ↓reduceIte, hk1, hdiv]
        have hd : HasDerivAt (fun t : ℝ => ((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.sin (ω * t))
            (((-1 : ℝ) ^ (k / 2) * ω ^ k) * (Real.cos (ω * x) * ω)) x := by
          have ha : HasDerivAt (fun t : ℝ => ω * t) ω x := by
            simpa using (hasDerivAt_id' x).const_mul ω
          exact (ha.sin).const_mul _
        rw [hd.deriv, pow_succ]; ring
      · have hk1 : (k + 1) % 2 = 0 := by omega
        have hdiv : (k + 1) / 2 = k / 2 + 1 := by omega
        simp only [hk, ↓reduceIte, hk1, hdiv]
        have hd : HasDerivAt (fun t : ℝ => ((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.cos (ω * t))
            (((-1 : ℝ) ^ (k / 2) * ω ^ k) * (-(Real.sin (ω * x)) * ω)) x := by
          have ha : HasDerivAt (fun t : ℝ => ω * t) ω x := by
            simpa using (hasDerivAt_id' x).const_mul ω
          exact (ha.cos).const_mul _
        rw [hd.deriv, pow_succ, pow_succ]; ring
    · rw [iteratedDeriv_succ, ih.2]
      ext x
      by_cases hk : k % 2 = 0
      · have hk1 : (k + 1) % 2 ≠ 0 := by omega
        have hdiv : (k + 1) / 2 = k / 2 := by omega
        simp only [hk, ↓reduceIte, hk1, hdiv]
        have hd : HasDerivAt (fun t : ℝ => ((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.cos (ω * t))
            (((-1 : ℝ) ^ (k / 2) * ω ^ k) * (-(Real.sin (ω * x)) * ω)) x := by
          have ha : HasDerivAt (fun t : ℝ => ω * t) ω x := by
            simpa using (hasDerivAt_id' x).const_mul ω
          exact (ha.cos).const_mul _
        rw [hd.deriv, pow_succ]; ring
      · have hk1 : (k + 1) % 2 = 0 := by omega
        have hdiv : (k + 1) / 2 = k / 2 + 1 := by omega
        simp only [hk, ↓reduceIte, hk1, hdiv]
        have hd : HasDerivAt (fun t : ℝ => -((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.sin (ω * t))
            (-((-1 : ℝ) ^ (k / 2) * ω ^ k) * (Real.cos (ω * x) * ω)) x := by
          have ha : HasDerivAt (fun t : ℝ => ω * t) ω x := by
            simpa using (hasDerivAt_id' x).const_mul ω
          exact (ha.sin).const_mul _
        rw [hd.deriv, pow_succ, pow_succ]; ring

/-- THEOREM I.2 (EXACT HIGHER-ORDER / JERK DERIVATIVE ENERGY ON `oddSinMode L`):
    For EVERY `L > 0` and EVERY derivative order `k : ℕ` (including `k = 1` Navier-Stokes
    viscosity, `k = 2` biharmonic hyperviscosity, and `k = 3` third-order Jerk dissipation):
      `∫ x in (-L/2)..(L/2), (iteratedDeriv k (fun x => sin (2πx / L)) x)^2 = (2π / L)^(2k) * (L / 2)`. -/
theorem oddSinMode_iteratedDeriv_L2_norm_sq {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ∫ x in (-L / 2)..(L / 2), (iteratedDeriv k (fun t : ℝ => Real.sin (2 * Real.pi / L * t)) x) ^ 2 =
      (2 * Real.pi / L) ^ (2 * k) * (L / 2) := by
  set ω : ℝ := 2 * Real.pi / L
  rw [(iteratedDeriv_sin_cos_mul ω k).1]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hω_ne : ω ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL_ne
  have hsin_sq : ∫ x in (-L / 2)..(L / 2), Real.sin (ω * x) ^ 2 = L / 2 := by
    have hL2 := oddSinMode_L2_norm_sq hL
    have heq : ∀ x : ℝ, ‖oddSinMode L x‖ ^ 2 = Real.sin (ω * x) ^ 2 := by
      intro x; dsimp [oddSinMode, ω]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      congr 2; ring
    simp_rw [heq] at hL2
    exact hL2
  have hcos_sq : ∫ x in (-L / 2)..(L / 2), Real.cos (ω * x) ^ 2 = L / 2 := by
    have hsum : ∫ x in (-L / 2)..(L / 2), (Real.sin (ω * x) ^ 2 + Real.cos (ω * x) ^ 2) = L := by
      simp_rw [Real.sin_sq_add_cos_sq, intervalIntegral.integral_const, smul_eq_mul, mul_one]
      ring
    rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), hsin_sq] at hsum
    linarith
  by_cases hk : k % 2 = 0
  · simp only [hk, ↓reduceIte]
    have hfun : (fun x : ℝ => (((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.sin (ω * x)) ^ 2) =
        fun x => ω ^ (2 * k) * Real.sin (ω * x) ^ 2 := by
      ext x
      have h1 : ((-1 : ℝ) ^ (k / 2)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h2 : (ω ^ k) ^ 2 = ω ^ (2 * k) := by rw [← pow_mul, mul_comm]
      rw [mul_pow, mul_pow, h1, one_mul, h2]
    rw [hfun, intervalIntegral.integral_const_mul, hsin_sq]
  · simp only [hk, ↓reduceIte]
    have hfun : (fun x : ℝ => (((-1 : ℝ) ^ (k / 2) * ω ^ k) * Real.cos (ω * x)) ^ 2) =
        fun x => ω ^ (2 * k) * Real.cos (ω * x) ^ 2 := by
      ext x
      have h1 : ((-1 : ℝ) ^ (k / 2)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h2 : (ω ^ k) ^ 2 = ω ^ (2 * k) := by rw [← pow_mul, mul_comm]
      rw [mul_pow, mul_pow, h1, one_mul, h2]
    rw [hfun, intervalIntegral.integral_const_mul, hcos_sq]

/-- THEOREM I.3 (UV/IR SEPARATION — ROUTE A INFRARED IMMUNITY TO HIGHER-ORDER JERK REGULARIZATION):
    For EVERY finite prime-power cutoff `N_max : ℕ`, EVERY hyperviscosity / Jerk order `k ≥ 1`
    (including `k = 1` viscosity, `k = 2` biharmonic, `k = 3` third-order Jerk), and EVERY
    coupling constant `ε > 0`, there exists `L_0 > 0` such that for EVERY `L ≥ L_0`:
      `W_pole(L, g_L) + W_∞(L, g_L) + ε * ‖g_L^(k)‖_2^2 - W_{prime, ≤ N_max}(L, g_L) < 0`.
    While higher-order Jerk regularization suppresses ultraviolet (`ω → ∞`) singularities in
    fluid dynamics, Route A's pole obstruction is infrared (`ω = 2π/L → 0` as `L → ∞`), where
    Jerk dissipation decays polynomially as `O(L^{-2k})` against an exponentially growing pole. -/
theorem weilTruncated_with_jerk_eventually_neg (N_max k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ L_0 : ℝ, 0 < L_0 ∧ ∀ L : ℝ, L_0 ≤ L →
      weilPole L (oddSinMode L) +
        (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) +
        ε * (∫ x in (-L / 2)..(L / 2),
          (iteratedDeriv k (fun t : ℝ => Real.sin (2 * Real.pi / L * t)) x) ^ 2) -
        weilPrimeTruncated N_max L (oddSinMode L) < 0 := by
  set M : ℝ := 2 * ∑ n ∈ Finset.Icc 2 N_max, ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
  have hM_nn : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  refine ⟨max 100 (M + ε + 1000), by positivity, fun L hL_ge => ?_⟩
  have hL100 : (100 : ℝ) ≤ L := le_trans (le_max_left _ _) hL_ge
  have hLM : M + ε + 1000 ≤ L := le_trans (le_max_right _ _) hL_ge
  have hL : 0 < L := by linarith
  have hpole := oddSinMode_weilPole_exact hL
  have harch := oddSinMode_weilArch_upper hL
  have hjerk := oddSinMode_iteratedDeriv_L2_norm_sq hL k
  -- Bound finite prime truncation directly using `shift_overlap_re_le_L2`
  have hprime_neg : -weilPrimeTruncated N_max L (oddSinMode L) ≤ M * (L / 2) := by
    have habs : |weilPrimeTruncated N_max L (oddSinMode L)| ≤ M * (L / 2) := by
      dsimp [weilPrimeTruncated, M]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri : |∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
          (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
            (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
              oddSinMode L u * starRingEnd ℂ (oddSinMode L (u - Real.log (n : ℝ)))).re| ≤
          (∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
            ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) * (L / 2) := by
        rw [Finset.sum_mul]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n hn => ?_)
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn_fl : n ≤ Nat.floor (Real.exp L) := le_trans (Finset.mem_Icc.mp hn).2 (min_le_right _ _)
        have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
        have hlog_le : Real.log (n : ℝ) ≤ L := by
          have hn_le_exp : (n : ℝ) ≤ Real.exp L :=
            le_trans (Nat.cast_le.mpr hn_fl) (Nat.floor_le (le_of_lt (Real.exp_pos L)))
          exact (Real.log_le_iff_le_exp (by positivity)).mpr hn_le_exp
        have hw_nn : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) :=
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
        rw [abs_mul, abs_of_nonneg hw_nn]
        have hsh := shift_overlap_re_le_L2 hlog_nn hlog_le (continuous_oddSinMode L)
        rw [oddSinMode_L2_norm_sq hL] at hsh
        exact mul_le_mul_of_nonneg_left hsh hw_nn
      have hsub : Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))) ⊆ Finset.Icc 2 N_max := fun n hn =>
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 (min_le_left _ _)⟩
      have hmono : ∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
          ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) ≤
          ∑ n ∈ Finset.Icc 2 N_max, ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right hmono (by positivity : 0 ≤ L / 2)
      linarith
    linarith [(abs_le.mp habs).1]
  -- Since L ≥ 100 > 2π, (2π / L)^(2k) ≤ 1, so ε * jerk ≤ ε * (L / 2)!
  have hpi_lt315 : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  have hω_le1 : 2 * Real.pi / L ≤ 1 := by
    rw [div_le_one hL]; linarith
  have hω_nn : 0 ≤ 2 * Real.pi / L := by positivity
  have hpow_le1 : (2 * Real.pi / L) ^ (2 * k) ≤ 1 := pow_le_one₀ hω_nn hω_le1
  have hjerk_le : ε * (∫ x in (-L / 2)..(L / 2),
      (iteratedDeriv k (fun t : ℝ => Real.sin (2 * Real.pi / L * t)) x) ^ 2) ≤ ε * (L / 2) := by
    rw [hjerk]
    have h1 : (2 * Real.pi / L) ^ (2 * k) * (L / 2) ≤ 1 * (L / 2) :=
      mul_le_mul_of_nonneg_right hpow_le1 (by positivity)
    nlinarith
  -- Same exponential pole lower bound `-W_pole ≥ L^6 / 131072 ≥ 2 * L^2 > (M + ε)*(L/2) + 90/L`!
  have hsinh_lb : (L / 4) ^ 4 / 48 ≤ Real.sinh (L / 4) := by
    rw [Real.sinh_eq]
    have hx : 0 ≤ L / 4 := by linarith
    have hexp_ge := Real.sum_le_exp_of_nonneg hx 5
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp_ge
    have hexp_neg : Real.exp (-(L / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    norm_num at hexp_ge
    have h1 : 0 ≤ L / 4 := by linarith
    have h2 : 0 ≤ (L / 4) ^ 2 / 2 := by positivity
    have h3 : 0 ≤ (L / 4) ^ 3 / 6 := by positivity
    linarith
  have hsinh_sq : ((L / 4) ^ 4 / 48) ^ 2 ≤ Real.sinh (L / 4) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsinh_lb 2
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpi2_lt : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos, hpi_lt315]
  have hden_le : L ^ 2 / 4 + 4 * Real.pi ^ 2 ≤ L ^ 2 / 2 := by nlinarith [hL100, hpi2_lt]
  have hden_sq : (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2 ≤ (L ^ 2 / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hden_le 2
  have hfrac_lb : 1152 / L ^ 2 ≤ 32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2 := by
    have h1 : 288 * L ^ 2 ≤ 32 * Real.pi ^ 2 * L ^ 2 := by nlinarith [sq_nonneg L, hpi2]
    have h2 : 288 * L ^ 2 / (L ^ 2 / 2) ^ 2 ≤ 32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2 :=
      div_le_div₀ (by positivity) h1 (by positivity) hden_sq
    have h3 : 1152 / L ^ 2 = 288 * L ^ 2 / (L ^ 2 / 2) ^ 2 := by field_simp [ne_of_gt hL]; ring
    linarith
  have hmag_lb : L ^ 6 / 131072 ≤
      (32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 := by
    have hsimp : L ^ 6 / 131072 = (1152 / L ^ 2) * ((L / 4) ^ 4 / 48) ^ 2 := by
      field_simp [ne_of_gt hL]; ring
    rw [hsimp]
    exact mul_le_mul hfrac_lb hsinh_sq (by positivity) (by positivity)
  have hL4_big : (262144 : ℝ) ≤ L ^ 4 := by
    have : (100 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL100 4
    norm_num at this; linarith
  have hL6_gt : 2 * L ^ 2 ≤ L ^ 6 / 131072 := by nlinarith [sq_nonneg L]
  have h90_le : 90 / L ≤ 1 := by rw [div_le_one hL]; linarith
  have hM_lt : (M + ε) * (L / 2) + 1 < 2 * L ^ 2 := by nlinarith
  have _ := hk
  linarith

/-- Chebyshev's prime-power summatory function `ψ(x) = ∑_{1 ≤ n ≤ ⌊x⌋} Λ(n)`. -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), ArithmeticFunction.vonMangoldt n

/-- Helper: on the open step interval `(log k, log (k + 1))` for `k ≥ 1`, `chebyshevPsi (exp u)`
    is identically equal to the constant `chebyshevPsi k`. -/
private lemma chebyshevPsi_exp_eq_of_Ioo {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hu_lo : Real.log (k : ℝ) < u) (hu_hi : u < Real.log ((k + 1 : ℕ) : ℝ)) :
    chebyshevPsi (Real.exp u) = chebyshevPsi (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hexp_lo : (k : ℝ) < Real.exp u := by
    calc (k : ℝ) = Real.exp (Real.log (k : ℝ)) := (Real.exp_log hk_pos).symm
      _ < Real.exp u := Real.exp_lt_exp.mpr hu_lo
  have hexp_hi : Real.exp u < ((k + 1 : ℕ) : ℝ) := by
    calc Real.exp u < Real.exp (Real.log ((k + 1 : ℕ) : ℝ)) := Real.exp_lt_exp.mpr hu_hi
      _ = ((k + 1 : ℕ) : ℝ) := Real.exp_log hk1_pos
  have hfl : Nat.floor (Real.exp u) = k := by
    rw [Nat.floor_eq_iff (le_of_lt (Real.exp_pos u))]
    exact ⟨le_of_lt hexp_lo, by simpa using hexp_hi⟩
  dsimp [chebyshevPsi]
  rw [hfl, Nat.floor_natCast]

/-- Helper: on `(log ⌊e^L⌋, L)`, `chebyshevPsi (exp u)` is identically `chebyshevPsi ⌊e^L⌋`. -/
private lemma chebyshevPsi_exp_eq_top {L : ℝ} (hL : 0 < L) {u : ℝ}
    (hu_lo : Real.log ((Nat.floor (Real.exp L) : ℕ) : ℝ) < u) (hu_hi : u < L) :
    chebyshevPsi (Real.exp u) = chebyshevPsi ((Nat.floor (Real.exp L) : ℕ) : ℝ) := by
  set M : ℕ := Nat.floor (Real.exp L)
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < Real.exp L := Real.one_lt_exp_iff.mpr hL
    exact Nat.le_floor (le_of_lt this)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hexp_lo : (M : ℝ) < Real.exp u := by
    calc (M : ℝ) = Real.exp (Real.log (M : ℝ)) := (Real.exp_log hM_pos).symm
      _ < Real.exp u := Real.exp_lt_exp.mpr hu_lo
  have hexp_hi : Real.exp u < ((M + 1 : ℕ) : ℝ) := by
    have h1 : Real.exp u < Real.exp L := Real.exp_lt_exp.mpr hu_hi
    have h2 : Real.exp L < (M : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp L)
    push_cast; linarith
  have hfl : Nat.floor (Real.exp u) = M := by
    rw [Nat.floor_eq_iff (le_of_lt (Real.exp_pos u))]
    exact ⟨le_of_lt hexp_lo, by simpa using hexp_hi⟩
  dsimp [chebyshevPsi]
  rw [hfl, Nat.floor_natCast]

/-- THEOREM I.4A (EXACT ABEL-STIELTJES INTEGRATION BY PARTS FOR CHEBYSHEV'S `ψ(e^u)`):
    For EVERY `L > 0` and EVERY `h` differentiable on `[0, L]` with continuous derivative `h'`
    and boundary vanishing `h L = 0`:
      `∫ u in 0..L, (chebyshevPsi (exp u) / exp (u / 2)) * (h' u - (1 / 2) * h u)
         = - ∑ n ∈ Finset.Icc 2 ⌊e^L⌋, (Λ(n) / √n) * h (log n)`. -/
theorem chebyshevPsi_step_stieltjes_ibp {L : ℝ} (hL : 0 < L)
    {h h' : ℝ → ℝ} (hderiv : ∀ u ∈ Set.uIcc 0 L, HasDerivAt h (h' u) u)
    (hcont' : ContinuousOn h' (Set.uIcc 0 L)) (hL_zero : h L = 0) :
    ∫ u in (0 : ℝ)..L,
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u) =
      -∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) * h (Real.log (n : ℝ)) := by
  set M : ℕ := Nat.floor (Real.exp L)
  have hM1 : 1 ≤ M := Nat.le_floor (le_of_lt (Real.one_lt_exp_iff.mpr hL))
  -- Partition [0, L] at knots p(k) = log(k+1) for k < M and p(M) = L:
  let p : ℕ → ℝ := fun k => if k < M then Real.log ((k + 1 : ℕ) : ℝ) else L
  have hp0 : p 0 = 0 := by
    dsimp [p]; simp [show 0 < M by omega]
  have hpM : p M = L := by
    dsimp [p]; simp
  have hp_in : ∀ k ≤ M, p k ∈ Set.Icc (0 : ℝ) L := by
    intro k hk
    dsimp [p]
    split_ifs with hlt
    · refine ⟨Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k + 1)), ?_⟩
      have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ Real.exp L := by
        have h1 : k + 1 ≤ M := by omega
        exact le_trans (Nat.cast_le.mpr h1) (Nat.floor_le (le_of_lt (Real.exp_pos L)))
      exact (Real.log_le_iff_le_exp (by positivity)).mpr hk1_le
    · exact ⟨le_of_lt hL, le_rfl⟩
  have hp_mono : ∀ k < M, p k ≤ p (k + 1) := by
    intro k hk
    dsimp [p]
    simp only [hk, ↓reduceIte]
    split_ifs with h2
    · exact Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 1 ≤ k + 2))
    · have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ Real.exp L :=
        le_trans (Nat.cast_le.mpr (by omega : k + 1 ≤ M)) (Nat.floor_le (le_of_lt (Real.exp_pos L)))
      exact (Real.log_le_iff_le_exp (by positivity)).mpr hk1_le
  -- Helper: primitive of `e^{-u/2} * (h' u - (1/2) * h u)` is `h u * e^{-u/2}`!
  let F : ℝ → ℝ := fun u => h u * Real.exp (-u / 2)
  have hF_deriv : ∀ u ∈ Set.uIcc 0 L,
      HasDerivAt F (Real.exp (-u / 2) * (h' u - (1 / 2 : ℝ) * h u)) u := by
    intro u hu
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-u / 2) * (-(1 / 2 : ℝ))) u := by
      have hlin : HasDerivAt (fun t : ℝ => -t / 2) (-(1 / 2 : ℝ)) u :=
        ((hasDerivAt_id' u).neg.div_const 2).congr_deriv (by ring)
      exact hlin.exp
    exact ((hderiv u hu).mul he).congr_deriv (by ring)
  have hcont_h : ContinuousOn h (Set.uIcc 0 L) := fun u hu =>
    (hderiv u hu).continuousAt.continuousWithinAt
  have hcont_g : ContinuousOn (fun u : ℝ => Real.exp (-u / 2) * (h' u - (1 / 2 : ℝ) * h u)) (Set.uIcc 0 L) :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousOn.mul
      (hcont'.sub (continuousOn_const.mul hcont_h))
  -- On each subinterval [p k, p (k+1)] (k < M), integrand equals a.e. constant `chebyshevPsi (k+1) * g u`!
  have hstep : ∀ k < M,
      (IntervalIntegrable (fun u : ℝ =>
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u)) volume (p k) (p (k + 1))) ∧
      (∫ u in (p k)..(p (k + 1)),
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u) =
        chebyshevPsi ((k + 1 : ℕ) : ℝ) * (F (p (k + 1)) - F (p k))) := by
    intro k hk
    have hle := hp_mono k hk
    have hsub : Set.uIcc (p k) (p (k + 1)) ⊆ Set.uIcc (0 : ℝ) L := by
      rw [Set.uIcc_of_le hle, Set.uIcc_of_le (le_of_lt hL)]
      exact Set.Icc_subset_Icc (hp_in k (le_of_lt hk)).1 (hp_in (k + 1) hk).2
    have hconst_int : IntervalIntegrable (fun u : ℝ =>
        chebyshevPsi ((k + 1 : ℕ) : ℝ) * (Real.exp (-u / 2) * (h' u - (1 / 2 : ℝ) * h u)))
        volume (p k) (p (k + 1)) :=
      ((hcont_g.mono hsub).intervalIntegrable).const_mul _
    -- Prove a.e. equality on uIoc (p k) (p (k + 1)) (differs at most at right endpoint `p (k + 1)`!)
    have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc (p k) (p (k + 1)) →
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u) =
          chebyshevPsi ((k + 1 : ℕ) : ℝ) * (Real.exp (-u / 2) * (h' u - (1 / 2 : ℝ) * h u)) := by
      have hae_ne : ∀ᵐ u : ℝ, u ≠ p (k + 1) := by
        rw [ae_iff]; simp
      filter_upwards [hae_ne] with u hne hu
      rw [Set.uIoc_of_le hle] at hu
      have hu_lo : p k < u := hu.1
      have hu_hi : u < p (k + 1) := lt_of_le_of_ne hu.2 hne
      have hpsi_eq : chebyshevPsi (Real.exp u) = chebyshevPsi ((k + 1 : ℕ) : ℝ) := by
        dsimp [p] at hu_lo hu_hi
        simp only [hk, ↓reduceIte] at hu_lo
        by_cases hk1 : k + 1 < M
        · simp only [hk1, ↓reduceIte] at hu_hi
          exact chebyshevPsi_exp_eq_of_Ioo (by omega) hu_lo (by simpa using hu_hi)
        · simp only [hk1, ↓reduceIte] at hu_hi
          have hkeq : k + 1 = M := by omega
          rw [hkeq] at hu_lo ⊢
          exact chebyshevPsi_exp_eq_top hL hu_lo hu_hi
      rw [hpsi_eq, div_eq_mul_inv, ← Real.exp_neg, show -(u / 2) = -u / 2 by ring]
      ring
    have hint_k : IntervalIntegrable (fun u : ℝ =>
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u))
        volume (p k) (p (k + 1)) := by
      refine hconst_int.congr_ae ?_
      change ∀ᵐ u ∂volume.restrict (Set.uIoc (p k) (p (k + 1))), _ = _
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hae] with u hu hmem
      exact (hu hmem).symm
    refine ⟨hint_k, ?_⟩
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hF_deriv u (hsub hu))
      ((hcont_g.mono hsub).intervalIntegrable)]
  -- Sum over k ∈ Finset.range M via `sum_integral_adjacent_intervals`
  have hsum_adj := intervalIntegral.sum_integral_adjacent_intervals (a := p) (n := M)
    (fun k hk => (hstep k hk).1)
  rw [hp0, hpM] at hsum_adj
  rw [← hsum_adj]
  have hsum_eval : ∑ k ∈ Finset.range M,
      ∫ u in (p k)..(p (k + 1)),
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u) =
      ∑ k ∈ Finset.range M, chebyshevPsi ((k + 1 : ℕ) : ℝ) * (F (p (k + 1)) - F (p k)) :=
    Finset.sum_congr rfl fun k hk => (hstep k (Finset.mem_range.mp hk)).2
  rw [hsum_eval]
  -- Exact Abel summation by parts on `∑_{k < M} ψ(k+1) * (F(p(k+1)) - F(p k))`!
  -- Using ψ(1) = 0, F(p M) = F(L) = 0, and ψ(n) - ψ(n-1) = Λ(n)!
  have hpsi1 : chebyshevPsi ((1 : ℕ) : ℝ) = 0 := by
    dsimp [chebyshevPsi]
    rw [Nat.floor_natCast, Finset.Icc_self, Finset.sum_singleton]
    exact ArithmeticFunction.vonMangoldt_apply_one
  have hpsi_diff : ∀ n : ℕ, 1 ≤ n →
      chebyshevPsi ((n + 1 : ℕ) : ℝ) - chebyshevPsi (n : ℝ) = ArithmeticFunction.vonMangoldt (n + 1) := by
    intro n hn
    dsimp [chebyshevPsi]
    rw [Nat.floor_natCast, Nat.floor_natCast]
    have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    rw [hsplit, Finset.sum_insert hnot]
    ring
  have hFM : F (p M) = 0 := by
    rw [hpM]; dsimp [F]; rw [hL_zero, zero_mul]
  -- Prove by induction on M ≥ 1 (generalized to any sequence A with A 0 = 0 and B M = 0):
  --   ∑_{k < M} A(k) * (B(k+1) - B(k)) = - ∑_{k ∈ range (M - 1)} (A(k+1) - A(k)) * B(k+1)
  have habel : ∀ (m : ℕ) (A B : ℕ → ℝ), A 0 = 0 → B m = 0 →
      ∑ k ∈ Finset.range m, A k * (B (k + 1) - B k) =
        -∑ k ∈ Finset.range (m - 1), (A (k + 1) - A k) * B (k + 1) := by
    intro m
    induction m with
    | zero => intro A B _ _; simp
    | succ m _ =>
      intro A B hA0 hBm
      cases m with
      | zero => simp [hA0]
      | succ m =>
        have htele : ∑ k ∈ Finset.range (m + 2), A k * (B (k + 1) - B k) =
            (∑ k ∈ Finset.range (m + 2), A k * B (k + 1)) -
            (∑ k ∈ Finset.range (m + 2), A k * B k) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        have hs1 : ∑ k ∈ Finset.range (m + 2), A k * B (k + 1) =
            ∑ k ∈ Finset.range (m + 1), A k * B (k + 1) := by
          rw [Finset.sum_range_succ, hBm, mul_zero, add_zero]
        have hs2 : ∑ k ∈ Finset.range (m + 2), A k * B k =
            ∑ k ∈ Finset.range (m + 1), A (k + 1) * B (k + 1) := by
          rw [Finset.sum_range_succ', hA0, zero_mul, add_zero]
        rw [htele, hs1, hs2, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        simp only [Nat.add_sub_cancel]
        refine Finset.sum_congr rfl fun k _ => by ring
  have habel_app := habel M (fun k => chebyshevPsi ((k + 1 : ℕ) : ℝ)) (fun k => F (p k)) hpsi1 hFM
  rw [habel_app]
  congr 1
  -- Reindex `k ∈ Finset.range (M - 1)` ↔ `n = k + 2 ∈ Finset.Icc 2 M`!
  refine Finset.sum_nbij (fun k => k + 2) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ _ k₂ _ heq; dsimp at heq; omega
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h2, hM⟩
    exact ⟨n - 2, Finset.mem_range.mpr (by omega), by dsimp; omega⟩
  · intro k hk
    rw [Finset.mem_range] at hk
    have hdiff := hpsi_diff (k + 1) (by omega)
    have hpk1 : p (k + 1) = Real.log ((k + 2 : ℕ) : ℝ) := by
      dsimp [p]
      simp only [show k + 1 < M by omega, ↓reduceIte]
    rw [hdiff, hpk1]
    dsimp [F]
    have hsqrt : Real.exp (-Real.log ((k + 2 : ℕ) : ℝ) / 2) = (Real.sqrt ((k + 2 : ℕ) : ℝ))⁻¹ := by
      have hpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hpos), Real.rpow_def_of_pos hpos]
      congr 1; ring
    rw [hsqrt, div_eq_mul_inv]
    ring

/-- THEOREM I.4B (EXACT `[∞ - ∞]` WEIL-CHEBYSHEV RENORMALIZATION IDENTITY FOR ALL `L > 0`):
    For EVERY `L > 0` and EVERY `h` differentiable on `[0, L]` with continuous derivative `h'`
    and boundary vanishing `h L = 0` (such as `h(u) = Re(g * g~)(u)` for any smooth `g`
    supported on `[-L/2, L/2]`):
      `2 ∫_0^L h(u) (e^{u/2} + e^{-u/2}) du - 2 ∑_{n=2}^{⌊e^L⌋} (Λ(n) / √n) h(log n)
         = -2 h(0) + 2 ∫_0^L h(u) e^{-u/2} du
           + 2 ∫_0^L ((ψ(e^u) - e^u) / e^{u/2}) * (h'(u) - (1/2) h(u)) du`.
    The exponentially diverging pole term `2 ∫_0^L h(u) e^{u/2} du` cancels IDENTICALLY against
    the macroscopic Prime Number Theorem term `dx` inside `dψ(x) = dx + d(ψ(x) - x)`. -/
theorem weilPole_sub_weilPrime_exact_chebyshev_renormalization {L : ℝ} (hL : 0 < L)
    {h h' : ℝ → ℝ} (hderiv : ∀ u ∈ Set.uIcc 0 L, HasDerivAt h (h' u) u)
    (hcont' : ContinuousOn h' (Set.uIcc 0 L)) (hL_zero : h L = 0) :
    2 * (∫ u in (0 : ℝ)..L, h u * (Real.exp (u / 2) + Real.exp (-u / 2))) -
      2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) * h (Real.log (n : ℝ)) =
      -2 * h 0 + 2 * (∫ u in (0 : ℝ)..L, h u * Real.exp (-u / 2)) +
        2 * (∫ u in (0 : ℝ)..L,
          ((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
            (h' u - (1 / 2 : ℝ) * h u)) := by
  have hcont_h : ContinuousOn h (Set.uIcc 0 L) := fun u hu =>
    (hderiv u hu).continuousAt.continuousWithinAt
  have hstieltjes := chebyshevPsi_step_stieltjes_ibp hL hderiv hcont' hL_zero
  -- Exact IBP for the macroscopic PNT term:
  --   ∫_0^L e^{u/2} (h'(u) - (1/2) h(u)) du = [h(u) e^{u/2}]_0^L - ∫_0^L h(u) e^{u/2} du
  --                                         = -h(0) - ∫_0^L h(u) e^{u/2} du!
  have hpnt_ibp : ∫ u in (0 : ℝ)..L, Real.exp (u / 2) * (h' u - (1 / 2 : ℝ) * h u) =
      -h 0 - ∫ u in (0 : ℝ)..L, h u * Real.exp (u / 2) := by
    have hftc : ∫ u in (0 : ℝ)..L,
        (h' u * Real.exp (u / 2) + h u * (Real.exp (u / 2) * (1 / 2 : ℝ))) =
        h L * Real.exp (L / 2) - h 0 * Real.exp (0 / 2) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => h u * Real.exp (u / 2)) (fun u hu => ?_) ?_
      · have he : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (u / 2) * (1 / 2 : ℝ)) u := by
          have hlin : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) u :=
            ((hasDerivAt_id' u).div_const 2).congr_deriv (by ring)
          exact hlin.exp
        exact (hderiv u hu).mul he
      · have hc1 : ContinuousOn (fun u => h' u * Real.exp (u / 2)) (Set.uIcc 0 L) :=
          hcont'.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
        have hc2 : ContinuousOn (fun u => h u * (Real.exp (u / 2) * (1 / 2 : ℝ))) (Set.uIcc 0 L) :=
          hcont_h.mul ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.mul continuousOn_const)
        exact (hc1.add hc2).intervalIntegrable
    rw [hL_zero, zero_mul, zero_div, Real.exp_zero, mul_one, zero_sub] at hftc
    have hsplit : (fun u : ℝ => Real.exp (u / 2) * (h' u - (1 / 2 : ℝ) * h u)) =
        fun u => (h' u * Real.exp (u / 2) + h u * (Real.exp (u / 2) * (1 / 2 : ℝ))) -
          h u * Real.exp (u / 2) := by ext u; ring
    rw [hsplit]
    have hi1 : IntervalIntegrable (fun u => h' u * Real.exp (u / 2) + h u * (Real.exp (u / 2) * (1 / 2 : ℝ)))
        volume 0 L :=
      ((hcont'.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn).add
        (hcont_h.mul ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.mul
          continuousOn_const))).intervalIntegrable
    have hi2 : IntervalIntegrable (fun u => h u * Real.exp (u / 2)) volume 0 L :=
      (hcont_h.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn).intervalIntegrable
    rw [intervalIntegral.integral_sub hi1 hi2, hftc]
  -- Split `((ψ(e^u) - e^u)/e^{u/2})*(h' - h/2)` into the Stieltjes term minus the PNT term!
  have hfun_split : (fun u : ℝ =>
      ((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u)) =
      fun u =>
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u) -
        Real.exp (u / 2) * (h' u - (1 / 2 : ℝ) * h u) := by
    ext u
    have heq : Real.exp u / Real.exp (u / 2) = Real.exp (u / 2) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [sub_div, heq]; ring
  -- Integrability of the step Stieltjes integrand on [0, L]
  have hint_st : IntervalIntegrable (fun u : ℝ =>
      (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u)) volume 0 L := by
    -- Reuse the exact partition proof: piecewise continuous on finitely many subintervals!
    set M : ℕ := Nat.floor (Real.exp L)
    have hM1 : 1 ≤ M := Nat.le_floor (le_of_lt (Real.one_lt_exp_iff.mpr hL))
    let p : ℕ → ℝ := fun k => if k < M then Real.log ((k + 1 : ℕ) : ℝ) else L
    have hp0 : p 0 = 0 := by dsimp [p]; simp [show 0 < M by omega]
    have hpM : p M = L := by dsimp [p]; simp
    have hcont_g : ContinuousOn (fun u : ℝ => Real.exp (-u / 2) * (h' u - (1 / 2 : ℝ) * h u)) (Set.uIcc 0 L) :=
      (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousOn.mul
        (hcont'.sub (continuousOn_const.mul hcont_h))
    have hpiece : ∀ k < M, IntervalIntegrable (fun u : ℝ =>
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u)) volume (p k) (p (k + 1)) := by
      intro k hk
      have hp_in : ∀ j ≤ M, p j ∈ Set.Icc (0 : ℝ) L := by
        intro j hj; dsimp [p]
        split_ifs with hlt
        · refine ⟨Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j + 1)), ?_⟩
          exact (Real.log_le_iff_le_exp (by positivity)).mpr
            (le_trans (Nat.cast_le.mpr (by omega : j + 1 ≤ M)) (Nat.floor_le (le_of_lt (Real.exp_pos L))))
        · exact ⟨le_of_lt hL, le_rfl⟩
      have hle : p k ≤ p (k + 1) := by
        dsimp [p]
        simp only [hk, ↓reduceIte]
        split_ifs with h2
        · exact Real.log_le_log (by positivity) (by exact_mod_cast (by omega : k + 1 ≤ k + 2))
        · exact (Real.log_le_iff_le_exp (by positivity)).mpr
            (le_trans (Nat.cast_le.mpr (by omega : k + 1 ≤ M)) (Nat.floor_le (le_of_lt (Real.exp_pos L))))
      have hsub : Set.uIcc (p k) (p (k + 1)) ⊆ Set.uIcc (0 : ℝ) L := by
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le (le_of_lt hL)]
        exact Set.Icc_subset_Icc (hp_in k (le_of_lt hk)).1 (hp_in (k + 1) hk).2
      refine (((hcont_g.mono hsub).intervalIntegrable).const_mul (chebyshevPsi ((k + 1 : ℕ) : ℝ))).congr_ae ?_
      change ∀ᵐ u ∂volume.restrict (Set.uIoc (p k) (p (k + 1))), _ = _
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      have hae_ne : ∀ᵐ u : ℝ, u ≠ p (k + 1) := by rw [ae_iff]; simp
      filter_upwards [hae_ne] with u hne hu
      rw [Set.uIoc_of_le hle] at hu
      have hu_lo : p k < u := hu.1
      have hu_hi : u < p (k + 1) := lt_of_le_of_ne hu.2 hne
      have hpsi_eq : chebyshevPsi (Real.exp u) = chebyshevPsi ((k + 1 : ℕ) : ℝ) := by
        dsimp [p] at hu_lo hu_hi
        simp only [hk, ↓reduceIte] at hu_lo
        by_cases hk1 : k + 1 < M
        · simp only [hk1, ↓reduceIte] at hu_hi
          exact chebyshevPsi_exp_eq_of_Ioo (by omega) hu_lo (by simpa using hu_hi)
        · simp only [hk1, ↓reduceIte] at hu_hi
          have hkeq : k + 1 = M := by omega
          rw [hkeq] at hu_lo ⊢
          exact chebyshevPsi_exp_eq_top hL hu_lo hu_hi
      rw [hpsi_eq, show chebyshevPsi ((k + 1 : ℕ) : ℝ) / Real.exp (u / 2) =
          chebyshevPsi ((k + 1 : ℕ) : ℝ) * Real.exp (-u / 2) by
        rw [div_eq_mul_inv, ← Real.exp_neg, show -(u / 2) = -u / 2 by ring]]
      ring
    have hind : ∀ m ≤ M, IntervalIntegrable (fun u : ℝ =>
        (chebyshevPsi (Real.exp u) / Real.exp (u / 2)) * (h' u - (1 / 2 : ℝ) * h u)) volume (p 0) (p m) := by
      intro m
      induction m with
      | zero => intro _; exact IntervalIntegrable.refl
      | succ m ih => intro hm; exact (ih (by omega)).trans (hpiece m (by omega))
    simpa [hp0, hpM] using hind M le_rfl
  have hint_pnt : IntervalIntegrable (fun u : ℝ => Real.exp (u / 2) * (h' u - (1 / 2 : ℝ) * h u)) volume 0 L :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.mul
      (hcont'.sub (continuousOn_const.mul hcont_h))).intervalIntegrable
  rw [hfun_split, intervalIntegral.integral_sub hint_st hint_pnt, hstieltjes, hpnt_ibp]
  -- Split `∫ h(u) (e^{u/2} + e^{-u/2}) = ∫ h(u) e^{u/2} + ∫ h(u) e^{-u/2}`
  have hpole_split : ∫ u in (0 : ℝ)..L, h u * (Real.exp (u / 2) + Real.exp (-u / 2)) =
      (∫ u in (0 : ℝ)..L, h u * Real.exp (u / 2)) + (∫ u in (0 : ℝ)..L, h u * Real.exp (-u / 2)) := by
    have hf : (fun u => h u * (Real.exp (u / 2) + Real.exp (-u / 2))) =
        fun u => h u * Real.exp (u / 2) + h u * Real.exp (-u / 2) := by ext u; ring
    rw [hf]
    exact intervalIntegral.integral_add
      (hcont_h.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn).intervalIntegrable
      (hcont_h.mul (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousOn).intervalIntegrable
  rw [hpole_split]
  ring

/-- THEOREM I.4C (EXACT CLOSED-FORM AUTOCORRELATION & RENORMALIZATION OF `oddSinMode L`):
    The exact autocorrelation `h_L(u) = ((L - u) / 2) * cos(2πu / L) + (L / (4π)) * sin(2πu / L)`
    of `oddSinMode L` satisfies `h_L(0) = L / 2`, `h_L(L) = 0`, `h_L'(u) = -(π / L) * (L - u) * sin(2πu / L)`,
    and obeys the exact `[∞ - ∞]` Weil-Chebyshev renormalization identity for EVERY `L > 0`. -/
theorem oddSinMode_autocorr_exact_and_renormalized {L : ℝ} (hL : 0 < L) :
    let hL_ac : ℝ → ℝ := fun u =>
      ((L - u) / 2) * Real.cos (2 * Real.pi / L * u) + (L / (4 * Real.pi)) * Real.sin (2 * Real.pi / L * u)
    let hL_ac' : ℝ → ℝ := fun u => -(Real.pi / L) * (L - u) * Real.sin (2 * Real.pi / L * u)
    hL_ac 0 = L / 2 ∧ hL_ac L = 0 ∧
    (∀ u : ℝ, HasDerivAt hL_ac (hL_ac' u) u) ∧
    (2 * (∫ u in (0 : ℝ)..L, hL_ac u * (Real.exp (u / 2) + Real.exp (-u / 2))) -
      2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) * hL_ac (Real.log (n : ℝ)) =
      -L + 2 * (∫ u in (0 : ℝ)..L, hL_ac u * Real.exp (-u / 2)) +
        2 * (∫ u in (0 : ℝ)..L,
          ((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
            (hL_ac' u - (1 / 2 : ℝ) * hL_ac u))) := by
  intro hL_ac hL_ac'
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have h0 : hL_ac 0 = L / 2 := by dsimp [hL_ac]; simp
  have hend : hL_ac L = 0 := by
    dsimp [hL_ac]
    have harg : 2 * Real.pi / L * L = 2 * Real.pi := by field_simp [hL_ne]
    rw [harg, Real.sin_two_pi]; ring
  have hd : ∀ u : ℝ, HasDerivAt hL_ac (hL_ac' u) u := by
    intro u
    dsimp [hL_ac, hL_ac']
    have hlin1 : HasDerivAt (fun t : ℝ => (L - t) / 2) (-(1 / 2 : ℝ)) u := by
      have := ((hasDerivAt_const u L).fun_sub (hasDerivAt_id' u)).div_const 2
      exact this.congr_deriv (by ring)
    have harg : HasDerivAt (fun t : ℝ => 2 * Real.pi / L * t) (2 * Real.pi / L) u := by
      simpa using (hasDerivAt_id' u).const_mul (2 * Real.pi / L)
    have ht1 := hlin1.mul harg.cos
    have ht2 := harg.sin.const_mul (L / (4 * Real.pi))
    refine (ht1.add ht2).congr_deriv ?_
    field_simp [hL_ne, Real.pi_ne_zero]
    ring
  have hren := weilPole_sub_weilPrime_exact_chebyshev_renormalization hL
    (fun u _ => hd u) (by fun_prop) hend
  rw [h0, show -2 * (L / 2) = -L by ring] at hren
  exact ⟨h0, hend, hd, hren⟩

-- ==============================================================================
-- PART II: ROUTE B — JACOBI THETA MODULAR CONSERVATION LAWS (ORDERS 1 & 3) AND
--          GLOBAL UNCONDITIONAL EULER HALF-PLANE HERGLOTZ-SCHUR POSITIVITY
-- ==============================================================================

/-- Individual term of the `k`-th derivative of `jacobiPsi(t)`. -/
private noncomputable def jacobiPsiDerivTerm (k n : ℕ) (t : ℝ) : ℝ :=
  (-(Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)) ^ k *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)

/-- Exact `k`-th derivative of the Jacobi theta tail `ψ(t) = ∑_{n ≥ 1} exp(-π n^2 t)` at `t > 0`. -/
noncomputable def jacobiPsiDeriv (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, jacobiPsiDerivTerm k n t

/-- Helper: summable exponential majorant for `k`-th derivative of `jacobiPsi` on `[1/2, ∞)`. -/
private lemma summable_jacobiPsiDeriv_bound (k : ℕ) :
    Summable (fun n : ℕ =>
      (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) ^ k *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ))) := by
  have h := (summable_pow_mul_exp_neg_sq (2 * k) (c := Real.pi * (1 / 2 : ℝ)) (by positivity)).mul_left (Real.pi ^ k)
  refine h.congr fun n => ?_
  rw [mul_pow, ← pow_mul, mul_comm 2 k]
  have harg : -(Real.pi * (1 / 2 : ℝ)) * ((n + 1 : ℕ) : ℝ) ^ 2 =
      -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) := by ring
  rw [harg]; ring

private lemma hasDerivAt_jacobiPsiDerivTerm (k n : ℕ) (s : ℝ) :
    HasDerivAt (jacobiPsiDerivTerm k n) (jacobiPsiDerivTerm (k + 1) n s) s := by
  dsimp [jacobiPsiDerivTerm]
  have hlin : HasDerivAt (fun r : ℝ => -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * r)
      (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) s :=
    ((hasDerivAt_id' s).const_mul (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)).congr_deriv (by ring)
  refine (hlin.exp.const_mul _).congr_deriv ?_
  rw [pow_succ]; ring

private lemma norm_jacobiPsiDerivTerm_le (k n : ℕ) {s : ℝ} (hs : 1 / 2 < s) :
    ‖jacobiPsiDerivTerm k n s‖ ≤
      (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) ^ k *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ)) := by
  dsimp [jacobiPsiDerivTerm]
  rw [abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2),
      abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hpos : 0 ≤ Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

/-- Helper: term-by-term derivative of `jacobiPsiDeriv k` on `(1/2, ∞)`. -/
private lemma hasDerivAt_jacobiPsiDeriv (k : ℕ) {t : ℝ} (ht : 1 / 2 < t) :
    HasDerivAt (jacobiPsiDeriv k) (jacobiPsiDeriv (k + 1) t) t := by
  have hsum0 : Summable (fun n : ℕ => jacobiPsiDerivTerm k n 1) :=
    (summable_jacobiPsiDeriv_bound k).of_norm_bounded fun n =>
      norm_jacobiPsiDerivTerm_le k n (by norm_num)
  exact hasDerivAt_tsum_of_isPreconnected (g := jacobiPsiDerivTerm k) (g' := jacobiPsiDerivTerm (k + 1))
    (summable_jacobiPsiDeriv_bound (k + 1)) isOpen_Ioi
    (convex_Ioi (1 / 2 : ℝ)).isPreconnected
    (fun n s _ => hasDerivAt_jacobiPsiDerivTerm k n s)
    (fun n s hs => norm_jacobiPsiDerivTerm_le (k + 1) n hs)
    (show (1 : ℝ) ∈ Set.Ioi (1 / 2 : ℝ) by norm_num) hsum0 ht

/-- Helper: Orders 1 and 3 modular conservation laws of `jacobiPsi` at `t = 1`. -/
private lemma jacobiPsi_modular_laws_one_and_three :
    4 * jacobiPsiDeriv 1 1 + jacobiPsi 1 + 1 / 2 = 0 ∧
    32 * jacobiPsiDeriv 3 1 + 120 * jacobiPsiDeriv 2 1 - 15 * jacobiPsi 1 - 15 / 2 = 0 := by
  have h0_eq : jacobiPsiDeriv 0 = jacobiPsi := by
    ext t; dsimp [jacobiPsiDeriv, jacobiPsiDerivTerm, jacobiPsi]
    exact tsum_congr fun n => by simp
  let L : ℝ → ℝ := fun t => 1 + 2 * jacobiPsiDeriv 0 (1 / t)
  let R : ℝ → ℝ := fun t => Real.sqrt t * (1 + 2 * jacobiPsiDeriv 0 t)
  have hLR : Set.EqOn L R (Set.Ioo (1 / 2 : ℝ) 2) := by
    intro t ht; dsimp [L, R]; rw [h0_eq]
    exact jacobiPsi_functional_duality (by linarith [ht.1])
  let L1 : ℝ → ℝ := fun t => -2 * t ^ (-2 : ℤ) * jacobiPsiDeriv 1 (1 / t)
  let L2 : ℝ → ℝ := fun t =>
    4 * t ^ (-3 : ℤ) * jacobiPsiDeriv 1 (1 / t) + 2 * t ^ (-4 : ℤ) * jacobiPsiDeriv 2 (1 / t)
  let L3 : ℝ → ℝ := fun t =>
    -12 * t ^ (-4 : ℤ) * jacobiPsiDeriv 1 (1 / t) -
      12 * t ^ (-5 : ℤ) * jacobiPsiDeriv 2 (1 / t) -
      2 * t ^ (-6 : ℤ) * jacobiPsiDeriv 3 (1 / t)
  let R1 : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * (Real.sqrt t)⁻¹ * (1 + 2 * jacobiPsiDeriv 0 t) +
      2 * Real.sqrt t * jacobiPsiDeriv 1 t
  let R2 : ℝ → ℝ := fun t =>
    -(1 / 4 : ℝ) * t⁻¹ * (Real.sqrt t)⁻¹ * (1 + 2 * jacobiPsiDeriv 0 t) +
      2 * (Real.sqrt t)⁻¹ * jacobiPsiDeriv 1 t +
      2 * Real.sqrt t * jacobiPsiDeriv 2 t
  let R3 : ℝ → ℝ := fun t =>
    (3 / 8 : ℝ) * t⁻¹ ^ 2 * (Real.sqrt t)⁻¹ * (1 + 2 * jacobiPsiDeriv 0 t) -
      (3 / 2 : ℝ) * t⁻¹ * (Real.sqrt t)⁻¹ * jacobiPsiDeriv 1 t +
      3 * (Real.sqrt t)⁻¹ * jacobiPsiDeriv 2 t +
      2 * Real.sqrt t * jacobiPsiDeriv 3 t
  have hinv_gt : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, (1 / 2 : ℝ) < 1 / t := by
    intro t ht; rw [lt_div_iff₀ (by linarith [ht.1])]; linarith [ht.2]
  have hd_inv : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun s : ℝ => 1 / s) (-(t ^ (-2 : ℤ))) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => one_div s) |>.congr_deriv ?_
    simp [zpow_neg]
  have hd_comp : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Ioo (1 / 2 : ℝ) 2 →
      HasDerivAt (fun s : ℝ => jacobiPsiDeriv k (1 / s))
        (-(t ^ (-2 : ℤ)) * jacobiPsiDeriv (k + 1) (1 / t)) t := by
    intro k t ht
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    exact ((hasDerivAt_jacobiPsiDeriv k (hinv_gt t ht)).comp t (hd_inv t ht_ne)).congr_deriv (by ring)
  have hd_L : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt L (L1 t) t := by
    intro t ht; dsimp [L, L1]
    exact ((hasDerivAt_const t (1 : ℝ)).fun_add ((hd_comp 0 t ht).const_mul 2)).congr_deriv (by ring)
  have hd_L1 : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt L1 (L2 t) t := by
    intro t ht
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    dsimp [L1, L2]
    have hp := (hasDerivAt_zpow (-2 : ℤ) t (Or.inl ht_ne)).const_mul (-2 : ℝ)
    refine (hp.fun_mul (hd_comp 1 t ht)).congr_deriv ?_
    have hc : ((-2 : ℤ) : ℝ) = -2 := by norm_num
    have hz1 : t ^ (-2 - 1 : ℤ) = t ^ (-3 : ℤ) := rfl
    have hz2 : t ^ (-2 : ℤ) * t ^ (-2 : ℤ) = t ^ (-4 : ℤ) := by rw [← zpow_add₀ ht_ne]; rfl
    rw [hc, hz1]
    linear_combination 2 * jacobiPsiDeriv 2 (1 / t) * hz2
  have hd_L2 : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt L2 (L3 t) t := by
    intro t ht
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    dsimp [L2, L3]
    have hp1 := (hasDerivAt_zpow (-3 : ℤ) t (Or.inl ht_ne)).const_mul (4 : ℝ)
    have hp2 := (hasDerivAt_zpow (-4 : ℤ) t (Or.inl ht_ne)).const_mul (2 : ℝ)
    refine ((hp1.fun_mul (hd_comp 1 t ht)).fun_add (hp2.fun_mul (hd_comp 2 t ht))).congr_deriv ?_
    have hc3 : ((-3 : ℤ) : ℝ) = -3 := by norm_num
    have hc4 : ((-4 : ℤ) : ℝ) = -4 := by norm_num
    have hz1 : t ^ (-3 - 1 : ℤ) = t ^ (-4 : ℤ) := rfl
    have hz2 : t ^ (-4 - 1 : ℤ) = t ^ (-5 : ℤ) := rfl
    have hz3 : t ^ (-3 : ℤ) * t ^ (-2 : ℤ) = t ^ (-5 : ℤ) := by rw [← zpow_add₀ ht_ne]; rfl
    have hz4 : t ^ (-4 : ℤ) * t ^ (-2 : ℤ) = t ^ (-6 : ℤ) := by rw [← zpow_add₀ ht_ne]; rfl
    rw [hc3, hc4, hz1, hz2]
    linear_combination -4 * jacobiPsiDeriv 2 (1 / t) * hz3 - 2 * jacobiPsiDeriv 3 (1 / t) * hz4
  have hd_sqrt_inv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => (Real.sqrt s)⁻¹) (-(1 / 2 : ℝ) * t⁻¹ * (Real.sqrt t)⁻¹) t := by
    intro t ht
    have hsq_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hsq_ne : Real.sqrt t ≠ 0 := ne_of_gt hsq_pos
    have hd := (Real.hasDerivAt_sqrt (ne_of_gt ht)).inv hsq_ne
    refine hd.congr_deriv ?_
    have hsq2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
    field_simp [hsq_ne, ne_of_gt ht]
    nlinarith [hsq2]
  have hd_R : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt R (R1 t) t := by
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1]
    dsimp [R, R1]
    have h1 := Real.hasDerivAt_sqrt (ne_of_gt ht_pos)
    have h2 := (hasDerivAt_const t (1 : ℝ)).fun_add ((hasDerivAt_jacobiPsiDeriv 0 ht.1).const_mul 2)
    refine (h1.fun_mul h2).congr_deriv ?_
    ring
  have hd_R1 : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt R1 (R2 t) t := by
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1]
    dsimp [R1, R2]
    have h1 := ((hd_sqrt_inv t ht_pos).const_mul (1 / 2 : ℝ)).fun_mul
      ((hasDerivAt_const t (1 : ℝ)).fun_add ((hasDerivAt_jacobiPsiDeriv 0 ht.1).const_mul 2))
    have h2 := ((Real.hasDerivAt_sqrt (ne_of_gt ht_pos)).const_mul 2).fun_mul
      (hasDerivAt_jacobiPsiDeriv 1 ht.1)
    refine (h1.fun_add h2).congr_deriv ?_
    ring
  have hd_R2 : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt R2 (R3 t) t := by
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    dsimp [R2, R3]
    have hprod_d : HasDerivAt (fun s : ℝ => -(1 / 4 : ℝ) * s⁻¹ * (Real.sqrt s)⁻¹)
        ((3 / 8 : ℝ) * t⁻¹ ^ 2 * (Real.sqrt t)⁻¹) t := by
      have h1 := ((hasDerivAt_inv ht_ne).const_mul (-(1 / 4 : ℝ))).fun_mul (hd_sqrt_inv t ht_pos)
      refine h1.congr_deriv ?_
      field_simp [ht_ne, ne_of_gt (Real.sqrt_pos.mpr ht_pos)]
      ring
    have ht1 := hprod_d.fun_mul
      ((hasDerivAt_const t (1 : ℝ)).fun_add ((hasDerivAt_jacobiPsiDeriv 0 ht.1).const_mul 2))
    have ht2 := ((hd_sqrt_inv t ht_pos).const_mul 2).fun_mul (hasDerivAt_jacobiPsiDeriv 1 ht.1)
    have ht3 := ((Real.hasDerivAt_sqrt (ne_of_gt ht_pos)).const_mul 2).fun_mul (hasDerivAt_jacobiPsiDeriv 2 ht.1)
    refine ((ht1.fun_add ht2).fun_add ht3).congr_deriv ?_
    ring
  have hL1R1 : Set.EqOn L1 R1 (Set.Ioo (1 / 2 : ℝ) 2) := by
    intro t ht
    have hnhds : L =ᶠ[𝓝 t] R := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) hLR
    rw [← (hd_L t ht).deriv, ← (hd_R t ht).deriv]
    exact hnhds.deriv_eq
  have hL2R2 : Set.EqOn L2 R2 (Set.Ioo (1 / 2 : ℝ) 2) := by
    intro t ht
    have hnhds : L1 =ᶠ[𝓝 t] R1 := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) hL1R1
    rw [← (hd_L1 t ht).deriv, ← (hd_R1 t ht).deriv]
    exact hnhds.deriv_eq
  have hL3R3 : L3 1 = R3 1 := by
    have h1_mem : (1 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 2 := by norm_num
    have hnhds : L2 =ᶠ[𝓝 (1 : ℝ)] R2 := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds h1_mem) hL2R2
    rw [← (hd_L2 1 h1_mem).deriv, ← (hd_R2 1 h1_mem).deriv]
    exact hnhds.deriv_eq
  have hlaw1_raw := hL1R1 (show (1 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 2 by norm_num)
  dsimp [L1, R1] at hlaw1_raw
  dsimp [L3, R3] at hL3R3
  rw [h0_eq] at hlaw1_raw hL3R3
  norm_num at hlaw1_raw hL3R3
  exact ⟨by linarith, by linarith⟩

/-- Helper: near `u = 0`, `riemannPhi u` equals an explicit finite linear combination of
    `jacobiPsiDeriv 2 (exp (2u))` and `jacobiPsiDeriv 1 (exp (2u))`. -/
private lemma riemannPhi_eventuallyEq_jacobiPsiDeriv_zero :
    riemannPhi =ᶠ[𝓝 (0 : ℝ)] fun u : ℝ =>
      2 * Real.exp (u / 2) *
        (2 * Real.exp (4 * u) * jacobiPsiDeriv 2 (Real.exp (2 * u)) +
          3 * Real.exp (2 * u) * jacobiPsiDeriv 1 (Real.exp (2 * u))) := by
  have hopen : IsOpen {u : ℝ | (1 / 2 : ℝ) < Real.exp (2 * u)} :=
    isOpen_lt continuous_const (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  filter_upwards [hopen.mem_nhds (by simp; norm_num : (1 / 2 : ℝ) < Real.exp (2 * (0 : ℝ)))] with u hu
  have hsum_k : ∀ k : ℕ, Summable (fun n : ℕ => jacobiPsiDerivTerm k n (Real.exp (2 * u))) := fun k =>
    (summable_jacobiPsiDeriv_bound k).of_norm_bounded fun n => norm_jacobiPsiDerivTerm_le k n hu
  dsimp only [riemannPhi, jacobiPsiDeriv]
  rw [← tsum_mul_left, ← tsum_mul_left,
      ← ((hsum_k 2).mul_left _).tsum_add ((hsum_k 1).mul_left _), ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  dsimp [riemannPhiTerm, thetaHalfTerm, jacobiPsiDerivTerm]
  have hexp : Real.exp (u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
      Real.exp (u / 2) * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]; ring

/-- Helper: chain rule for `u ↦ jacobiPsiDeriv k (exp (2u))` at any `u` with `1/2 < exp(2u)`. -/
private lemma hasDerivAt_jacobiPsiDeriv_exp2 (k : ℕ) {u : ℝ} (hu : 1 / 2 < Real.exp (2 * u)) :
    HasDerivAt (fun x : ℝ => jacobiPsiDeriv k (Real.exp (2 * x)))
      (2 * Real.exp (2 * u) * jacobiPsiDeriv (k + 1) (Real.exp (2 * u))) u := by
  have he2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * u) * 2) u := by
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 u :=
      ((hasDerivAt_id' u).const_mul 2).congr_deriv (by ring)
    exact hlin.exp
  refine ((hasDerivAt_jacobiPsiDeriv k hu).comp u he2).congr_deriv ?_
  ring

/-- Helper: genuine smooth stationarity `HasDerivAt riemannPhi 0 0` proved directly from the
    Order-1 and Order-3 Jacobi modular conservation laws (`8 ψ'''(1) + 30 ψ''(1) + 15 ψ'(1) = 0`),
    proving both differentiability at `0` and vanishing derivative (excluding cusps such as `n = 1`). -/
private lemma hasDerivAt_riemannPhi_zero : HasDerivAt riemannPhi 0 0 := by
  have hgt : (1 / 2 : ℝ) < Real.exp (2 * (0 : ℝ)) := by simp; norm_num
  have he_half : HasDerivAt (fun u : ℝ => 2 * Real.exp (u / 2)) 1 0 := by
    have hlin : HasDerivAt (fun u : ℝ => u / 2) (1 / 2 : ℝ) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).div_const 2).congr_deriv (by ring)
    exact (hlin.exp.const_mul 2).congr_deriv (by simp)
  have he2 : HasDerivAt (fun u : ℝ => Real.exp (2 * u)) 2 0 := by
    have hlin : HasDerivAt (fun u : ℝ => 2 * u) 2 0 :=
      ((hasDerivAt_id' (0 : ℝ)).const_mul 2).congr_deriv (by ring)
    exact hlin.exp.congr_deriv (by simp)
  have he4 : HasDerivAt (fun u : ℝ => Real.exp (4 * u)) 4 0 := by
    have hlin : HasDerivAt (fun u : ℝ => 4 * u) 4 0 :=
      ((hasDerivAt_id' (0 : ℝ)).const_mul 4).congr_deriv (by ring)
    exact hlin.exp.congr_deriv (by simp)
  have hd1 := hasDerivAt_jacobiPsiDeriv_exp2 1 hgt
  have hd2 := hasDerivAt_jacobiPsiDeriv_exp2 2 hgt
  have ht2 := (he4.const_mul 2).fun_mul hd2
  have ht1 := (he2.const_mul 3).fun_mul hd1
  have hprod := he_half.fun_mul (ht2.fun_add ht1)
  refine (hprod.congr_of_eventuallyEq riemannPhi_eventuallyEq_jacobiPsiDeriv_zero).congr_deriv ?_
  have hlaws := jacobiPsi_modular_laws_one_and_three
  simp only [mul_zero, zero_div, Real.exp_zero]
  linarith [hlaws.1, hlaws.2]

/-- THEOREM II.1 (JACOBI THETA MODULAR CONSERVATION LAWS AT `t = 1` OF ORDERS 1 AND 3,
    AND GENUINE SMOOTH BOUNDARY STATIONARITY `HasDerivAt riemannPhi 0 0`):
    Directly from Jacobi's modular inversion identity `1 + 2 ψ(1/t) = √t (1 + 2 ψ(t))`:
    (1) Order 1 Modular Law: `4 * ψ'(1) + ψ(1) + 1/2 = 0`,
    (2) Order 3 Modular Law: `32 * ψ'''(1) + 120 * ψ''(1) - 15 * ψ(1) - 15/2 = 0`,
    (3) Genuine smooth differentiability and vanishing derivative `HasDerivAt riemannPhi 0 0`. -/
theorem jacobiPsi_modular_conservation_order_one_and_three :
    4 * jacobiPsiDeriv 1 1 + jacobiPsi 1 + 1 / 2 = 0 ∧
    32 * jacobiPsiDeriv 3 1 + 120 * jacobiPsiDeriv 2 1 - 15 * jacobiPsi 1 - 15 / 2 = 0 ∧
    HasDerivAt riemannPhi 0 0 :=
  ⟨jacobiPsi_modular_laws_one_and_three.1,
   jacobiPsi_modular_laws_one_and_three.2,
   hasDerivAt_riemannPhi_zero⟩

/-- Helper: exact `log ‖Gamma (x + i y)‖` derivative wrt `x > 0` equals `(Complex.digamma ⟨x, y⟩).re`. -/
private lemma hasDerivAt_log_norm_Gamma_re {x y : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log ‖Complex.Gamma (⟨t, y⟩ : ℂ)‖)
      (Complex.digamma (⟨x, y⟩ : ℂ)).re x := by
  have hre : 0 < (⟨x, y⟩ : ℂ).re := hx
  have hgnz : Complex.Gamma (⟨x, y⟩ : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hdiffG : DifferentiableAt ℂ Complex.Gamma (⟨x, y⟩ : ℂ) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    have hre_eq := congrArg Complex.re hm
    simp at hre_eq; linarith
  have hshift : HasDerivAt (fun z : ℂ => Complex.Gamma (z + Complex.I * (y : ℂ)))
      (deriv Complex.Gamma (⟨x, y⟩ : ℂ)) (x : ℂ) := by
    have h1 : (x : ℂ) + Complex.I * (y : ℂ) = (⟨x, y⟩ : ℂ) := by apply Complex.ext <;> simp
    have hd : HasDerivAt Complex.Gamma (deriv Complex.Gamma (⟨x, y⟩ : ℂ)) ((x : ℂ) + Complex.I * (y : ℂ)) := by
      rw [h1]; exact hdiffG.hasDerivAt
    have h2 : HasDerivAt (Complex.Gamma ∘ fun z : ℂ => z + Complex.I * (y : ℂ))
        (deriv Complex.Gamma (⟨x, y⟩ : ℂ) * 1) (x : ℂ) :=
      hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (Complex.I * (y : ℂ)))
    exact h2.congr_deriv (mul_one _)
  have hcomp : HasDerivAt (fun t : ℝ => Complex.Gamma (⟨t, y⟩ : ℂ))
      (deriv Complex.Gamma (⟨x, y⟩ : ℂ)) x := by
    have heq : (fun t : ℝ => Complex.Gamma (⟨t, y⟩ : ℂ)) =
        fun t : ℝ => Complex.Gamma ((t : ℂ) + Complex.I * (y : ℂ)) := by
      ext t; congr 1; apply Complex.ext <;> simp
    rw [heq]
    exact hshift.comp_ofReal
  -- Derivative of `‖f t‖^2 = (f t).re^2 + (f t).im^2` divided by `2 * ‖f x‖^2` equals `Re(f' x / f x)`!
  have hnorm_sq : HasDerivAt (fun t : ℝ => ‖Complex.Gamma (⟨t, y⟩ : ℂ)‖ ^ 2)
      (2 * ((Complex.Gamma (⟨x, y⟩ : ℂ)).re * (deriv Complex.Gamma (⟨x, y⟩ : ℂ)).re +
            (Complex.Gamma (⟨x, y⟩ : ℂ)).im * (deriv Complex.Gamma (⟨x, y⟩ : ℂ)).im)) x := by
    have heq : (fun t : ℝ => ‖Complex.Gamma (⟨t, y⟩ : ℂ)‖ ^ 2) =
        fun t => (Complex.Gamma (⟨t, y⟩ : ℂ)).re ^ 2 + (Complex.Gamma (⟨t, y⟩ : ℂ)).im ^ 2 := by
      ext t; rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [heq]
    have hre_d : HasDerivAt (fun t : ℝ => (Complex.Gamma (⟨t, y⟩ : ℂ)).re)
        (deriv Complex.Gamma (⟨x, y⟩ : ℂ)).re x := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp
    have him_d : HasDerivAt (fun t : ℝ => (Complex.Gamma (⟨t, y⟩ : ℂ)).im)
        (deriv Complex.Gamma (⟨x, y⟩ : ℂ)).im x := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hcomp
    exact ((hre_d.pow 2).add (him_d.pow 2)).congr_deriv (by ring)
  have hpos_sq : ‖Complex.Gamma (⟨x, y⟩ : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hgnz)
  have hlog_sq := (hnorm_sq.log hpos_sq).const_mul (1 / 2 : ℝ)
  have hlog_eq : (fun t : ℝ => (1 / 2 : ℝ) * Real.log (‖Complex.Gamma (⟨t, y⟩ : ℂ)‖ ^ 2)) =
      fun t => Real.log ‖Complex.Gamma (⟨t, y⟩ : ℂ)‖ := by
    ext t; rw [Real.log_pow]; push_cast; ring
  rw [hlog_eq] at hlog_sq
  refine hlog_sq.congr_deriv ?_
  rw [Complex.digamma_def, logDeriv_apply, Complex.div_re, Complex.sq_norm]
  have hns : Complex.normSq (Complex.Gamma (⟨x, y⟩ : ℂ)) ≠ 0 :=
    Complex.normSq_pos.mpr hgnz |>.ne'
  field_simp [hns]

/-- THEOREM II.2A (ELEMENTARY MONOTONICITY & LOWER SERIES OF `Re(Complex.digamma(x + iy))`):
    Directly from `Complex.GammaSeq_tendsto_Gamma` (with ZERO uniform differentiation of infinite
    products), for EVERY `x > 0`, EVERY `y : ℝ`, and EVERY `K : ℕ`:
      `(Complex.digamma ⟨x, y⟩).re ≥ (Complex.digamma x).re + ∑ k ∈ Finset.range K, y^2 / ((x+k)((x+k)^2 + y^2))`. -/
theorem complex_digamma_re_ge_real_add_finset {x : ℝ} (hx : 0 < x) (y : ℝ) (K : ℕ) :
    (Complex.digamma (x : ℂ)).re +
      ∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2)) ≤
      (Complex.digamma (⟨x, y⟩ : ℂ)).re := by
  -- Step 1: Prove `H(t) = log ‖Γ(t+iy)‖ - log ‖Γ(t)‖ - (1/2) ∑_{k<K} log((t+k)^2 / ((t+k)^2 + y^2))`
  -- is MonotoneOn (Ioi 0) directly from `GammaSeq_tendsto_Gamma`!
  let H : ℝ → ℝ := fun t =>
    Real.log ‖Complex.Gamma (⟨t, y⟩ : ℂ)‖ - Real.log ‖Complex.Gamma (t : ℂ)‖ -
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range K, Real.log ((t + (k : ℝ)) ^ 2 / ((t + (k : ℝ)) ^ 2 + y ^ 2))
  have hH_mono : MonotoneOn H (Set.Ioi (0 : ℝ)) := by
    intro t₁ ht₁ t₂ ht₂ hle
    have ht1 : 0 < t₁ := ht₁
    have ht2 : 0 < t₂ := ht₂
    -- Ratio of norms of GammaSeq for all n ≥ K + 1:
    have hseq_ratio : ∀ n : ℕ, K ≤ n → 1 ≤ n →
        (‖Complex.GammaSeq (⟨t₁, y⟩ : ℂ) n‖ ^ 2 / ‖Complex.GammaSeq (t₁ : ℂ) n‖ ^ 2) *
          (∏ k ∈ Finset.range K, ((t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2))) ≤
        (‖Complex.GammaSeq (⟨t₂, y⟩ : ℂ) n‖ ^ 2 / ‖Complex.GammaSeq (t₂ : ℂ) n‖ ^ 2) *
          (∏ k ∈ Finset.range K, ((t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2))) := by
      intro n hKn hn1
      have hratio_eval : ∀ t : ℝ, 0 < t →
          ‖Complex.GammaSeq (⟨t, y⟩ : ℂ) n‖ ^ 2 / ‖Complex.GammaSeq (t : ℂ) n‖ ^ 2 =
            ∏ k ∈ Finset.range (n + 1), ((t + (k : ℝ)) ^ 2 / ((t + (k : ℝ)) ^ 2 + y ^ 2)) := by
        intro t ht
        dsimp [Complex.GammaSeq]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hcpow : ‖((n : ℂ) ^ (⟨t, y⟩ : ℂ))‖ = ‖((n : ℂ) ^ (t : ℂ))‖ := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
              Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
          simp
        have hnum_ne : ‖((n : ℂ) ^ (t : ℂ)) * (n.factorial : ℂ)‖ ≠ 0 := by
          rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
              Complex.norm_natCast]
          exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hn_pos _))
            (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
        have hden1_ne : ‖∏ j ∈ Finset.range (n + 1), ((⟨t, y⟩ : ℂ) + (j : ℂ))‖ ≠ 0 := by
          rw [norm_prod]
          refine Finset.prod_ne_zero_iff.mpr fun j _ => norm_ne_zero_iff.mpr fun h0 => ?_
          have hre := congrArg Complex.re h0; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) j]
        have hden2_ne : ‖∏ j ∈ Finset.range (n + 1), ((t : ℂ) + (j : ℂ))‖ ≠ 0 := by
          rw [norm_prod]
          refine Finset.prod_ne_zero_iff.mpr fun j _ => norm_ne_zero_iff.mpr fun h0 => ?_
          have hre := congrArg Complex.re h0; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) j]
        rw [norm_div, norm_div, norm_mul, norm_mul, hcpow, div_pow, div_pow]
        have halg : ∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
            (a ^ 2 / b ^ 2) / (a ^ 2 / c ^ 2) = c ^ 2 / b ^ 2 := by
          intro a b c ha hb hc; field_simp [ha, hb, hc]
        rw [halg _ _ _ (by rw [← norm_mul]; exact hnum_ne) hden1_ne hden2_ne]
        rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp; ring
      rw [hratio_eval t₁ ht1, hratio_eval t₂ ht2]
      -- Split `range (n + 1)` into `range K` and `Ico K (n + 1)`!
      have hsplit : ∀ f : ℕ → ℝ,
          ∏ k ∈ Finset.range (n + 1), f k =
            (∏ k ∈ Finset.range K, f k) * (∏ k ∈ Finset.Ico K (n + 1), f k) := by
        intro f
        have hdisj : Disjoint (Finset.range K) (Finset.Ico K (n + 1)) := by
          rw [Finset.disjoint_left]; intro k hk1 hk2
          rw [Finset.mem_range] at hk1; rw [Finset.mem_Ico] at hk2; omega
        have hunion : Finset.range K ∪ Finset.Ico K (n + 1) = Finset.range (n + 1) := by
          ext k; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
        rw [← hunion, Finset.prod_union hdisj]
      rw [hsplit, hsplit]
      have hfac_nn : 0 ≤ (∏ k ∈ Finset.range K, ((t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2))) *
          (∏ k ∈ Finset.range K, ((t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2))) :=
        mul_nonneg (Finset.prod_nonneg fun k _ => by positivity)
          (Finset.prod_nonneg fun k _ => by positivity)
      have hterm_le : ∀ k : ℕ,
          (t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2) ≤
          (t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2) := by
        intro k
        have hd1 : 0 < (t₁ + (k : ℝ)) ^ 2 + y ^ 2 := by positivity
        have hd2 : 0 < (t₂ + (k : ℝ)) ^ 2 + y ^ 2 := by positivity
        rw [div_le_div_iff₀ hd1 hd2]
        have hsq_le : (t₁ + (k : ℝ)) ^ 2 ≤ (t₂ + (k : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        nlinarith [sq_nonneg y]
      have htail_le : ∏ k ∈ Finset.Ico K (n + 1), ((t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2)) ≤
          ∏ k ∈ Finset.Ico K (n + 1), ((t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2)) := by
        induction (Finset.Ico K (n + 1)) using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.prod_insert ha]
          exact mul_le_mul (hterm_le a) ih (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
      have hmul := mul_le_mul_of_nonneg_left htail_le hfac_nn
      linarith
    -- Pass to the limit n → ∞ via `Complex.GammaSeq_tendsto_Gamma`!
    have hgnz1 : Complex.Gamma (t₁ : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht1)
    have hgnz2 : Complex.Gamma (t₂ : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht2)
    have hlim1 : Tendsto (fun n => (‖Complex.GammaSeq (⟨t₁, y⟩ : ℂ) n‖ ^ 2 / ‖Complex.GammaSeq (t₁ : ℂ) n‖ ^ 2) *
        (∏ k ∈ Finset.range K, ((t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2)))) atTop
        (𝓝 ((‖Complex.Gamma (⟨t₁, y⟩ : ℂ)‖ ^ 2 / ‖Complex.Gamma (t₁ : ℂ)‖ ^ 2) *
          (∏ k ∈ Finset.range K, ((t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2))))) :=
      ((((Complex.GammaSeq_tendsto_Gamma _).norm.pow 2).div
        ((Complex.GammaSeq_tendsto_Gamma _).norm.pow 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr hgnz1)))).mul_const _
    have hlim2 : Tendsto (fun n => (‖Complex.GammaSeq (⟨t₂, y⟩ : ℂ) n‖ ^ 2 / ‖Complex.GammaSeq (t₂ : ℂ) n‖ ^ 2) *
        (∏ k ∈ Finset.range K, ((t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2)))) atTop
        (𝓝 ((‖Complex.Gamma (⟨t₂, y⟩ : ℂ)‖ ^ 2 / ‖Complex.Gamma (t₂ : ℂ)‖ ^ 2) *
          (∏ k ∈ Finset.range K, ((t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2))))) :=
      ((((Complex.GammaSeq_tendsto_Gamma _).norm.pow 2).div
        ((Complex.GammaSeq_tendsto_Gamma _).norm.pow 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr hgnz2)))).mul_const _
    have hineq : (‖Complex.Gamma (⟨t₁, y⟩ : ℂ)‖ ^ 2 / ‖Complex.Gamma (t₁ : ℂ)‖ ^ 2) *
          (∏ k ∈ Finset.range K, ((t₂ + (k : ℝ)) ^ 2 / ((t₂ + (k : ℝ)) ^ 2 + y ^ 2))) ≤
        (‖Complex.Gamma (⟨t₂, y⟩ : ℂ)‖ ^ 2 / ‖Complex.Gamma (t₂ : ℂ)‖ ^ 2) *
          (∏ k ∈ Finset.range K, ((t₁ + (k : ℝ)) ^ 2 / ((t₁ + (k : ℝ)) ^ 2 + y ^ 2))) :=
      le_of_tendsto_of_tendsto hlim1 hlim2
        (Filter.eventually_atTop.mpr ⟨max K 1, fun n hn =>
          hseq_ratio n (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)⟩)
    -- Take (1/2) * log of both sides!
    have hp1 : 0 < ‖Complex.Gamma (⟨t₁, y⟩ : ℂ)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos ht1)
    have hp2 : 0 < ‖Complex.Gamma (⟨t₂, y⟩ : ℂ)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos ht2)
    have hq1 : 0 < ‖Complex.Gamma (t₁ : ℂ)‖ := norm_pos_iff.mpr hgnz1
    have hq2 : 0 < ‖Complex.Gamma (t₂ : ℂ)‖ := norm_pos_iff.mpr hgnz2
    have hprod_pos : ∀ t : ℝ, 0 < t → 0 < ∏ k ∈ Finset.range K, ((t + (k : ℝ)) ^ 2 / ((t + (k : ℝ)) ^ 2 + y ^ 2)) :=
      fun t ht => Finset.prod_pos fun k _ => by positivity
    have hlog := Real.log_le_log (mul_pos (div_pos (sq_pos_of_pos hp1) (sq_pos_of_pos hq1)) (hprod_pos t₂ ht2)) hineq
    rw [Real.log_mul (ne_of_gt (div_pos (sq_pos_of_pos hp1) (sq_pos_of_pos hq1))) (ne_of_gt (hprod_pos t₂ ht2)),
        Real.log_mul (ne_of_gt (div_pos (sq_pos_of_pos hp2) (sq_pos_of_pos hq2))) (ne_of_gt (hprod_pos t₁ ht1)),
        Real.log_div (ne_of_gt (sq_pos_of_pos hp1)) (ne_of_gt (sq_pos_of_pos hq1)),
        Real.log_div (ne_of_gt (sq_pos_of_pos hp2)) (ne_of_gt (sq_pos_of_pos hq2)),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
        Real.log_prod (fun k _ => by positivity), Real.log_prod (fun k _ => by positivity)] at hlog
    dsimp [H]
    push_cast at hlog
    linarith
  -- Step 2: Compute `HasDerivAt H (...) x` and conclude `0 ≤ deriv H x` from `MonotoneOn H (Ioi 0)`!
  have hd_H : HasDerivAt H
      ((Complex.digamma (⟨x, y⟩ : ℂ)).re - (Complex.digamma (x : ℂ)).re -
        ∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2))) x := by
    have h1 := hasDerivAt_log_norm_Gamma_re (y := y) hx
    have h2 : HasDerivAt (fun t : ℝ => Real.log ‖Complex.Gamma (t : ℂ)‖) (Complex.digamma (x : ℂ)).re x := by
      have heq : (fun t : ℝ => Real.log ‖Complex.Gamma (t : ℂ)‖) =
          fun t => Real.log ‖Complex.Gamma (⟨t, 0⟩ : ℂ)‖ := by ext t; rfl
      rw [heq]; exact hasDerivAt_log_norm_Gamma_re (y := 0) hx
    have h3 : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * ∑ k ∈ Finset.range K,
        Real.log ((t + (k : ℝ)) ^ 2 / ((t + (k : ℝ)) ^ 2 + y ^ 2)))
        (∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2))) x := by
      have hterm : ∀ k ∈ Finset.range K,
          HasDerivAt (fun t : ℝ => Real.log ((t + (k : ℝ)) ^ 2 / ((t + (k : ℝ)) ^ 2 + y ^ 2)))
            (2 * y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2))) x := by
        intro k _
        have hxk : 0 < x + (k : ℝ) := by positivity
        have hden : 0 < (x + (k : ℝ)) ^ 2 + y ^ 2 := by positivity
        have hloc : (fun t : ℝ => Real.log ((t + (k : ℝ)) ^ 2 / ((t + (k : ℝ)) ^ 2 + y ^ 2))) =ᶠ[𝓝 x]
            fun t => 2 * Real.log (t + (k : ℝ)) - Real.log ((t + (k : ℝ)) ^ 2 + y ^ 2) := by
          filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Set.Ioi (0 : ℝ) from hx)] with t ht
          have ht0 : 0 < t := ht
          have htk : 0 < t + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
          rw [Real.log_div (by positivity) (by positivity), Real.log_pow]; push_cast; ring
        have hd_a : HasDerivAt (fun t : ℝ => 2 * Real.log (t + (k : ℝ))) (2 / (x + (k : ℝ))) x := by
          have ha : HasDerivAt (fun t : ℝ => t + (k : ℝ)) 1 x := (hasDerivAt_id' x).add_const (k : ℝ)
          exact ((ha.log (ne_of_gt hxk)).const_mul 2).congr_deriv (by ring)
        have hd_b : HasDerivAt (fun t : ℝ => Real.log ((t + (k : ℝ)) ^ 2 + y ^ 2))
            (2 * (x + (k : ℝ)) / ((x + (k : ℝ)) ^ 2 + y ^ 2)) x := by
          have ha : HasDerivAt (fun t : ℝ => (t + (k : ℝ)) ^ 2 + y ^ 2) (2 * (x + (k : ℝ))) x := by
            have hlin : HasDerivAt (fun t : ℝ => t + (k : ℝ)) 1 x := (hasDerivAt_id' x).add_const (k : ℝ)
            exact ((hlin.pow 2).add_const (y ^ 2)).congr_deriv (by ring)
          exact (ha.log (ne_of_gt hden)).congr_deriv (by ring)
        refine (hd_a.sub hd_b).congr_of_eventuallyEq hloc |>.congr_deriv ?_
        field_simp [ne_of_gt hxk, ne_of_gt hden]; ring
      have hsum := (HasDerivAt.fun_sum hterm).const_mul (1 / 2 : ℝ)
      refine hsum.congr_deriv ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    exact (h1.sub h2).sub h3
  -- Since `H` is MonotoneOn (Ioi 0), its derivative at `x ∈ Ioi 0` is ≥ 0!
  have hd_nn : 0 ≤ (Complex.digamma (⟨x, y⟩ : ℂ)).re - (Complex.digamma (x : ℂ)).re -
      ∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2)) := by
    have htend := (hasDerivAt_iff_tendsto_slope.mp hd_H).mono_left
      (nhdsWithin_mono x (fun t (ht : t ∈ Set.Ioi x) => ne_of_gt ht))
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hgt : x < t := ht
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hH_mono hx (lt_trans hx hgt) (le_of_lt hgt))) (sub_nonneg.mpr (le_of_lt hgt))
  linarith

/-- THEOREM II.2B (MONOTONICITY OF REAL DIGAMMA ON `(0, ∞)`):
    Directly from Mathlib4's Bohr-Mollerup `Real.convexOn_log_Gamma`, `x ↦ (Complex.digamma x).re`
    is monotone increasing on `(0, ∞)`. -/
theorem complex_digamma_real_mono :
    MonotoneOn (fun x : ℝ => (Complex.digamma (x : ℂ)).re) (Set.Ioi (0 : ℝ)) := by
  have heq : ∀ x : ℝ, 0 < x →
      (Complex.digamma (x : ℂ)).re = deriv (fun t : ℝ => Real.log (Real.Gamma t)) x := by
    intro x hx
    have h1 := hasDerivAt_log_norm_Gamma_re (y := 0) hx
    have hloc : (fun t : ℝ => Real.log ‖Complex.Gamma (⟨t, 0⟩ : ℂ)‖) =ᶠ[𝓝 x]
        fun t => Real.log (Real.Gamma t) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Set.Ioi (0 : ℝ) from hx)] with t ht
      have ht0 : 0 < t := ht
      have hG : Complex.Gamma (⟨t, 0⟩ : ℂ) = (Real.Gamma t : ℂ) := by
        change Complex.Gamma (t : ℂ) = (Real.Gamma t : ℂ)
        exact Complex.Gamma_ofReal t
      rw [hG, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos ht0)]
    have h2 : HasDerivAt (fun t : ℝ => Real.log (Real.Gamma t)) (Complex.digamma (x : ℂ)).re x :=
      (h1.congr_of_eventuallyEq hloc.symm).congr_deriv rfl
    exact h2.deriv.symm
  intro x hx y hy hxy
  dsimp only
  rw [heq x hx, heq y hy]
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun s => Real.log (Real.Gamma s)) t := by
    intro t ht
    have ht0 : 0 < t := ht
    exact (Real.differentiableAt_Gamma fun m => by linarith [Nat.cast_nonneg (α := ℝ) m]).log
      (ne_of_gt (Real.Gamma_pos_of_pos ht0))
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact le_trans (Real.convexOn_log_Gamma.deriv_le_slope hx hy hlt (hdiff x hx))
      (Real.convexOn_log_Gamma.slope_le_deriv hx hy hlt (hdiff y hy))

/-- THEOREM II.3A (UNIFORM-IN-`γ` EULER-PRODUCT `vonMangoldt` L-SERIES NORM BOUND):
    For EVERY `β > 1` and EVERY `γ : ℝ`:
      `‖LSeries (fun n => (Λ(n) : ℂ)) ⟨β, -γ⟩‖ ≤ ∑' n : ℕ, Λ(n) / (n : ℝ) ^ β`. -/
theorem vonMangoldt_lseries_norm_le_tsum {β : ℝ} (hβ : 1 < β) (γ : ℝ) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β) ∧
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β := by
  have hs_re : 1 < (⟨β, -γ⟩ : ℂ).re := hβ
  have hsumm : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs_re
  have hterm_norm : ∀ n : ℕ,
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (⟨β, -γ⟩ : ℂ) n‖ =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β := by
    intro n
    cases n with
    | zero => simp [LSeries.term]
    | succ m =>
      simp only [LSeries.term, Nat.succ_ne_zero, ↓reduceIte, norm_div, Complex.norm_real,
                 Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m)]
  have hsum_real : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β) := by
    simpa [hterm_norm] using hsumm.norm
  refine ⟨hsum_real, ?_⟩
  dsimp [LSeries]
  have hle := norm_tsum_le_tsum_norm hsumm.norm
  simpa [hterm_norm] using hle

/-- THEOREM II.3B (EXPLICIT NUMERICAL EULER-PRODUCT BOUND FOR `β ≥ 8`):
    For EVERY `β ≥ 8` and EVERY `γ : ℝ`, `‖L(Λ, ⟨β, -γ⟩)‖ ≤ 1 / 200`. -/
theorem vonMangoldt_lseries_norm_le_of_eight_le {β : ℝ} (hβ : 8 ≤ β) (γ : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ 1 / 200 := by
  have hβ1 : 1 < β := by linarith
  rcases vonMangoldt_lseries_norm_le_tsum hβ1 γ with ⟨hsum, hnorm⟩
  refine le_trans hnorm ?_
  -- Bound each term: n=0,1 are 0; n=2 is log 2 / 2^β ≤ 1/256; n ≥ 3 is Λ(n)/n^β ≤ n / n^8 = 1/n^7!
  -- Actually even simpler: for n ≥ 3, Λ(n) ≤ log n ≤ n - 1 ≤ n, and 1/n^7 ≤ 1/(n*(n-1)) * (1/3^5) = (1/243)*(1/(n-1) - 1/n)!
  -- Sum over n ≥ 3 of (1/(n-1) - 1/n) telescopes to 1/2!
  -- So ∑_{n ≥ 3} Λ(n)/n^8 ≤ (1/243) * (1/2) = 1/486, wait: 1/256 + 1/486 = 0.00391 + 0.00206 = 0.00597 > 0.005!
  -- Refine n=2 with `log 2 ≤ 3/4` (gives 3/1024 = 0.00293) and `n ≥ 3`: `1/n^7 ≤ (1/3^5) * (1/(n-1) - 1/n)` gives `1/486 = 0.002057`:
  -- 3/1024 + 1/486 = 0.0029297 + 0.0020576 = 0.004987 < 0.005 = 1/200!! PURE ELEMENTARY ARITHMETIC!
  let B : ℕ → ℝ := fun n =>
    if n ≤ 1 then 0
    else if n = 2 then 3 / 1024
    else (1 / 243 : ℝ) * (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ))
  have htele_sum : HasSum (fun k : ℕ => (1 / 243 : ℝ) * (1 / ((k + 2 : ℕ) : ℝ) - 1 / ((k + 3 : ℕ) : ℝ)))
      ((1 / 243 : ℝ) * (1 / 2 : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N,
          (1 / 243 : ℝ) * (1 / ((k + 2 : ℕ) : ℝ) - 1 / ((k + 3 : ℕ) : ℝ)) =
          (1 / 243 : ℝ) * (1 / 2 - 1 / ((N + 2 : ℕ) : ℝ)) := by
        intro N
        rw [← Finset.mul_sum]
        congr 1
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast; ring
      simp_rw [hpart]
      have h0 : Tendsto (fun N : ℕ => 1 / ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1) |> fun h =>
          h.congr (fun N => by dsimp [Function.comp_def]; push_cast; ring_nf)
      simpa using (tendsto_const_nhds.sub h0).const_mul (1 / 243 : ℝ)
    · intro k
      have h1 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
      have h2 : ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ k + 3)
      have h3 : 1 / ((k + 3 : ℕ) : ℝ) ≤ 1 / ((k + 2 : ℕ) : ℝ) := one_div_le_one_div_of_le h1 h2
      linarith
  have hB_hasSum : HasSum B (3 / 1024 + (1 / 243 : ℝ) * (1 / 2 : ℝ)) := by
    rw [← hasSum_nat_add_iff' 3]
    have hshift : (fun k : ℕ => B (k + 3)) =
        fun k => (1 / 243 : ℝ) * (1 / ((k + 2 : ℕ) : ℝ) - 1 / ((k + 3 : ℕ) : ℝ)) := by
      ext k; dsimp [B]
    rw [hshift]
    have hhead : ∑ i ∈ Finset.range 3, B i = 3 / 1024 := by
      simp [Finset.sum_range_succ, B]
    rw [hhead]
    convert htele_sum using 1; ring
  have hle_B : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β ≤ B n := by
    intro n
    dsimp [B]
    by_cases h01 : n ≤ 1
    · simp only [h01, ↓reduceIte]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h01 with rfl | rfl <;>
        simp [ArithmeticFunction.vonMangoldt_apply_one]
    · simp only [h01, ↓reduceIte]
      by_cases h2 : n = 2
      · subst h2
        simp only [↓reduceIte]
        have hvm2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
          simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
        have hlog2 : Real.log 2 ≤ 3 / 4 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          have hge := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num) 4
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hge
          norm_num at hge; linarith
        have hpow2 : (256 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ β := by
          have h1 : ((2 : ℕ) : ℝ) ^ (8 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ β :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
          have h2' : ((2 : ℕ) : ℝ) ^ (8 : ℝ) = 256 := by
            rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
          linarith
        rw [hvm2]
        calc Real.log 2 / ((2 : ℕ) : ℝ) ^ β
          _ ≤ (3 / 4 : ℝ) / 256 := div_le_div₀ (by norm_num) hlog2 (by norm_num) hpow2
          _ = 3 / 1024 := by norm_num
      · simp only [h2, ↓reduceIte]
        have hn3 : 3 ≤ n := by omega
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have hn1_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        have hvm_le : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := by
          have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log
          have h2' : Real.log (n : ℝ) ≤ (n : ℝ) := le_trans (Real.log_le_sub_one_of_pos hn_pos) (by linarith)
          linarith
        have hpow_ge : (n : ℝ) ^ (8 : ℕ) ≤ (n : ℝ) ^ β := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hn1_ge1 (by norm_num; exact hβ)
        have hsub : 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) = 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
          have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          have hne1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
          rw [hcast]; field_simp [ne_of_gt hn_pos, show (n : ℝ) - 1 ≠ 0 by rw [← hcast]; exact hne1]; ring
        rw [hsub]
        have hnm1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
        have hden_ge : (243 : ℝ) * (((n - 1 : ℕ) : ℝ) * (n : ℝ)) ≤ (n : ℝ) ^ 7 := by
          have hn3_r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
          have h5 : (243 : ℝ) ≤ (n : ℝ) ^ 5 := by
            have : (3 : ℝ) ^ 5 ≤ (n : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hn3_r 5
            norm_num at this; linarith
          have hnm1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n 1)
          have hmul1 : ((n - 1 : ℕ) : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
          have hmul2 : (243 : ℝ) * (((n - 1 : ℕ) : ℝ) * (n : ℝ)) ≤ (n : ℝ) ^ 5 * (n : ℝ) ^ 2 :=
            mul_le_mul h5 hmul1 (by positivity) (by positivity)
          linarith [show (n : ℝ) ^ 5 * (n : ℝ) ^ 2 = (n : ℝ) ^ 7 by ring]
        calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β
          _ ≤ (n : ℝ) / (n : ℝ) ^ 8 := div_le_div₀ (le_of_lt hn_pos) hvm_le (by positivity) hpow_ge
          _ = 1 / (n : ℝ) ^ 7 := by field_simp [ne_of_gt hn_pos]
          _ ≤ 1 / ((243 : ℝ) * (((n - 1 : ℕ) : ℝ) * (n : ℝ))) :=
              one_div_le_one_div_of_le (by positivity) hden_ge
          _ = (1 / 243 : ℝ) * (1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ))) := by ring
  have htsum_le : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β ≤
      3 / 1024 + (1 / 243 : ℝ) * (1 / 2 : ℝ) := by
    rw [← hB_hasSum.tsum_eq]
    exact hsum.tsum_le_tsum hle_B hB_hasSum.summable
  linarith

/-- Helper: elementary explicit bound `Real.log Real.pi < 23 / 20` (`= 1.15`). -/
private lemma log_pi_lt_twenty_three_twentieths : Real.log Real.pi < 23 / 20 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have hpi : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  have hexp := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 23 / 20 by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp
  norm_num at hexp
  linarith

/-- THEOREM II.4 (GLOBAL UNCONDITIONAL EULER HALF-PLANE HERGLOTZ, POTENTIAL FORCE,
    DE BRANGES BOUNDARY PHASE VELOCITY, AND SCHUR CONTRACTION FOR ALL `γ ∈ ℝ`!):
    Injecting the full arithmetic Euler product (`vonMangoldt` on `Re(s) > 1`) together with
    `Complex.digamma`, for EVERY `γ : ℝ` (arbitrarily high ordinates to `±∞`!) and EVERY `σ ≥ 15 / 2`:
    (1) `0 < (xiResolvent (γ + iσ)).im` (global Herglotz positivity on `Im z ≥ 15/2`),
    (2) `0 < deriv (fun s => xiNormSq s γ) σ` and `0 < xiLogForce σ γ` (global radial force),
    (3) `0 < (logDeriv (xiSchur σ) γ).im` (global positive de Branges boundary phase velocity),
    (4) For ALL `α > 0, σ > 0` with `15 / 2 ≤ |σ - α|`: `‖xiSchur α (γ + iσ)‖ < 1`! -/
theorem xiResolvent_herglotz_global_euler_halfPlane :
    (∀ σ γ : ℝ, 15 / 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im) ∧
    (∀ α σ γ : ℝ, 0 < α → 0 < σ → 15 / 2 ≤ |σ - α| →
      ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ < 1) := by
  have hmain : ∀ σ γ : ℝ, 15 / 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
    intro σ γ hσ
    set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
    have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; linarith
    have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
    dsimp only at hexp
    set s : ℂ := 1 / 2 - Complex.I * z
    have hs_eq : s = (⟨1 / 2 + σ, -γ⟩ : ℂ) := by
      dsimp [s, z]; apply Complex.ext <;> simp
    have hβ : (8 : ℝ) ≤ 1 / 2 + σ := by linarith
    -- Take imaginary part of `xiResolvent z = I * (1/s + 1/(s-1) - (1/2) log π + (1/2) digamma(s/2) - L(Λ, s))`
    have him_eq : (xiResolvent z).im =
        (1 / s).re + (1 / (s - 1)).re - (1 / 2 : ℝ) * Real.log Real.pi +
          (1 / 2 : ℝ) * (Complex.digamma (s / 2)).re -
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
      rw [hexp]
      have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
        rw [← Complex.ofReal_log (le_of_lt Real.pi_pos), Complex.ofReal_re]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
                 Complex.sub_re, Complex.add_re, Complex.mul_re]
      norm_num [hlogpi]
    -- Bound each of the 4 terms:
    have hp1 : 0 < (1 / s).re := by
      rw [hs_eq, one_div, Complex.inv_re]
      have hns : 0 < Complex.normSq (⟨1 / 2 + σ, -γ⟩ : ℂ) :=
        Complex.normSq_pos.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
      exact div_pos (by simp; linarith) hns
    have hp2 : 0 < (1 / (s - 1)).re := by
      have hs1 : s - 1 = (⟨σ - 1 / 2, -γ⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp; ring
      rw [hs1, one_div, Complex.inv_re]
      have hns : 0 < Complex.normSq (⟨σ - 1 / 2, -γ⟩ : ℂ) :=
        Complex.normSq_pos.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
      exact div_pos (by simp; linarith) hns
    have hdig_lb : 7 / 6 < (Complex.digamma (s / 2)).re := by
      have hs2 : s / 2 = (⟨(1 / 2 + σ) / 2, -γ / 2⟩ : ℂ) := by
        rw [hs_eq]; apply Complex.ext <;> simp
      rw [hs2]
      have h1 := complex_digamma_re_ge_real_add_finset
        (show (0 : ℝ) < (1 / 2 + σ) / 2 by linarith) (-γ / 2) 0
      simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h1
      have h2 := complex_digamma_real_mono
        (show (4 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num)
        (show (1 / 2 + σ) / 2 ∈ Set.Ioi (0 : ℝ) by simp; linarith) (by linarith)
      have hdig4 : (Complex.digamma ((4 : ℝ) : ℂ)).re = 11 / 6 - Real.eulerMascheroniConstant := by
        have hnat := Complex.digamma_nat_add_one 3
        have h4eq : ((3 : ℕ) : ℂ) + 1 = ((4 : ℝ) : ℂ) := by norm_num
        rw [h4eq] at hnat
        rw [hnat]
        have hh3 : (harmonic 3 : ℂ) = (11 / 6 : ℂ) := by
          simp [harmonic, Finset.sum_range_succ]; norm_num
        rw [hh3]; simp
      have hγ_lt : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
      linarith
    have hlogpi_lt : Real.log Real.pi < 23 / 20 := log_pi_lt_twenty_three_twentieths
    have hlser_le : (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤ 1 / 200 := by
      rw [hs_eq]
      exact le_trans (Complex.re_le_norm _) (vonMangoldt_lseries_norm_le_of_eight_le hβ γ)
    have hR_pos : 0 < (xiResolvent z).im := by linarith
    -- Deduce `0 < deriv (xiNormSq · γ) σ`, `0 < xiLogForce σ γ`, and `0 < (logDeriv (xiSchur σ) γ).im`!
    have hxi_ne : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
      have hre : 1 ≤ (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)).re := by simp; linarith
      exact riemannXi_ne_zero_of_one_le_re hre
    have hV_pos : 0 < xiNormSq σ γ := by
      dsimp [xiNormSq]
      have harg : (⟨1 / 2 + σ, γ⟩ : ℂ) = ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
        apply Complex.ext <;> simp
      rw [harg]
      exact sq_pos_of_pos (norm_pos_iff.mpr hxi_ne)
    have hlogF := xiResolvent_im_eq_logForce_half hxi_ne
    have hLF_pos : 0 < xiLogForce σ γ := by linarith [hlogF.2]
    have hF_pos : 0 < deriv (fun t : ℝ => xiNormSq t γ) σ := by
      rw [xiLogForce_eq_force_div_normSq hV_pos] at hLF_pos
      exact (div_pos_iff_of_pos_right hV_pos).mp hLF_pos
    have hE_ne : xiShiftE σ (γ : ℂ) ≠ 0 := by
      dsimp [xiShiftE]
      exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
    have hphase := xiSchur_boundary_logDeriv_eq_I_mul_logForce hE_ne
    have hph_pos : 0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
      rw [hphase.2]; simp; exact hLF_pos
    exact ⟨hR_pos, hF_pos, hLF_pos, hph_pos⟩
  refine ⟨hmain, fun α σ γ hα hσ hge => ?_⟩
  -- Strict monotonicity of `s ↦ xiNormSq s γ` on `[15/2, ∞)` gives `V(|σ-α|, γ) < V(σ+α, γ)`!
  have hmono : StrictMonoOn (fun s : ℝ => xiNormSq s γ) (Set.Ici (15 / 2 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (15 / 2 : ℝ))
      (fun s _ => (hasDerivAt_xiNormSq_sigma s γ).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ici] at hs
    exact (hmain s γ (le_of_lt hs)).2.1
  have hlt_arg : |σ - α| < σ + α := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hV_lt : xiNormSq |σ - α| γ < xiNormSq (σ + α) γ :=
    hmono hge (le_trans hge (le_of_lt hlt_arg)) hlt_arg
  have hE_ne : xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0 := by
    dsimp [xiShiftE]
    exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hrat := xiSchur_norm_sq_eq_xiNormSq_ratio α σ γ
  have hden_pos : 0 < xiNormSq (σ + α) γ := by
    rw [← hrat.2.1]; exact sq_pos_of_pos (norm_pos_iff.mpr hE_ne)
  have hsq_lt : ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 < 1 := by
    rw [hrat.2.2 hE_ne, div_lt_one hden_pos]; exact hV_lt
  nlinarith [norm_nonneg (xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ)))]

/-- THEOREM II.5 (HIGH-ORDINATE EULER TAILS FOR ARBITRARY `σ > 1 / 2`, ARBITRARILY CLOSE
    TO THE CRITICAL STRIP BOUNDARY `Re(s) = 1`):
    For EVERY `σ > 1 / 2` (equivalently `β = 1/2 + σ > 1`), there exists an explicit height
    threshold `Γ > 0` such that for EVERY `γ : ℝ` with `Γ ≤ |γ|`:
      `0 < (xiResolvent (γ + iσ)).im`, `0 < deriv (fun s => xiNormSq s γ) σ`, and
      `0 < (logDeriv (xiSchur σ) γ).im`. -/
theorem xiResolvent_herglotz_euler_large_gamma_all_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ γ : ℝ, Γ ≤ |γ| →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
  set β : ℝ := 1 / 2 + σ
  have hβ1 : 1 < β := by dsimp [β]; linarith
  have hhalf_pos : 0 < β / 2 := by linarith
  set C_euler : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β
  -- Since the harmonic series `∑ 1/(k + β/2)` diverges, pick K such that
  -- `(1/2) * ∑_{k < K} 1 / (2*(k + β/2)) > C_euler + (1/2) * log π - (1/2) * Re(digamma (β/2))`!
  set target : ℝ := 4 * (C_euler + (1 / 2 : ℝ) * Real.log Real.pi - (1 / 2 : ℝ) * (Complex.digamma ((β / 2 : ℝ) : ℂ)).re + 1)
  -- For any integer M ≥ β/2, ∑_{k < K} 1 / (k + β/2) ≥ ∑_{k < K} 1 / (k + M) = harmonic (K + M - 1) - harmonic (M - 1) → ∞!
  -- Even simpler: use `Real.not_summable_one_div_natCast` via `tendsto_atTop_of_not_summable`!
  have hdiv : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, 1 / (β / 2 + (k : ℝ))) atTop atTop := by
    have hnot : ¬Summable (fun k : ℕ => 1 / (β / 2 + (k : ℝ))) := by
      intro hsum
      set M : ℕ := Nat.ceil (β / 2)
      have hM_ge : β / 2 ≤ (M : ℝ) := Nat.le_ceil _
      have hshift : Summable (fun k : ℕ => 1 / ((k + M + 1 : ℕ) : ℝ)) := by
        refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
        exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
      have hall : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
        rw [← summable_nat_add_iff (M + 1)]
        exact hshift.congr fun k => by congr 1
      exact Real.not_summable_one_div_natCast hall
    exact not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => by positivity) |>.mp hnot
  rcases Filter.eventually_atTop.mp (hdiv.eventually_gt_atTop (max target 1)) with ⟨K, hK⟩
  have hK_sum : target < ∑ k ∈ Finset.range K, 1 / (β / 2 + (k : ℝ)) :=
    lt_of_le_of_lt (le_max_left _ _) (hK K le_rfl)
  -- Choose Γ = 2 * (β / 2 + K) + 1: then for |γ| ≥ Γ, |γ|/2 ≥ β/2 + k for every k < K,
  -- so (γ/2)^2 / ((β/2 + k)^2 + (γ/2)^2) ≥ 1 / 2!
  refine ⟨2 * (β / 2 + (K : ℝ)) + 1, by positivity, fun γ hγ => ?_⟩
  set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; linarith
  have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
  dsimp only at hexp
  set s : ℂ := 1 / 2 - Complex.I * z
  have hs_eq : s = (⟨β, -γ⟩ : ℂ) := by dsimp [s, z, β]; apply Complex.ext <;> simp
  have him_eq : (xiResolvent z).im =
      (1 / s).re + (1 / (s - 1)).re - (1 / 2 : ℝ) * Real.log Real.pi +
        (1 / 2 : ℝ) * (Complex.digamma (s / 2)).re -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
    rw [hexp]
    have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
      rw [← Complex.ofReal_log (le_of_lt Real.pi_pos), Complex.ofReal_re]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
               Complex.sub_re, Complex.add_re, Complex.mul_re]
    norm_num [hlogpi]
  have hp1 : 0 < (1 / s).re := by
    rw [hs_eq, one_div, Complex.inv_re]
    have hns : 0 < Complex.normSq (⟨β, -γ⟩ : ℂ) :=
      Complex.normSq_pos.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    exact div_pos (by simp; linarith) hns
  have hp2 : 0 < (1 / (s - 1)).re := by
    have hs1 : s - 1 = (⟨β - 1, -γ⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs1, one_div, Complex.inv_re]
    have hns : 0 < Complex.normSq (⟨β - 1, -γ⟩ : ℂ) :=
      Complex.normSq_pos.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    exact div_pos (by simp; linarith) hns
  have hdig : (Complex.digamma ((β / 2 : ℝ) : ℂ)).re +
      (1 / 2 : ℝ) * (∑ k ∈ Finset.range K, 1 / (β / 2 + (k : ℝ))) ≤
      (Complex.digamma (s / 2)).re := by
    have hs2 : s / 2 = (⟨β / 2, -γ / 2⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs2]
    have hge := complex_digamma_re_ge_real_add_finset hhalf_pos (-γ / 2) K
    refine le_trans ?_ hge
    rw [Finset.mul_sum]
    have hsum_le : ∑ k ∈ Finset.range K, (1 / 2 : ℝ) * (1 / (β / 2 + (k : ℝ))) ≤
        ∑ k ∈ Finset.range K, (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : (k : ℝ) < (K : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hk)
      have hy_ge : β / 2 + (k : ℝ) ≤ |γ| / 2 := by linarith
      have hy_sq : (β / 2 + (k : ℝ)) ^ 2 ≤ (-γ / 2) ^ 2 := by
        have h1 : (β / 2 + (k : ℝ)) ^ 2 ≤ (|γ| / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hy_ge 2
        have h2 : (|γ| / 2) ^ 2 = (-γ / 2) ^ 2 := by rw [div_pow, div_pow, sq_abs]; ring
        linarith
      have hden1 : 0 < β / 2 + (k : ℝ) := by positivity
      have hden2 : 0 < (β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2 := by positivity
      have hfrac : (1 / 2 : ℝ) ≤ (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2) := by
        rw [le_div_iff₀ hden2]; linarith
      calc (1 / 2 : ℝ) * (1 / (β / 2 + (k : ℝ)))
        _ ≤ ((-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) * (1 / (β / 2 + (k : ℝ))) :=
            mul_le_mul_of_nonneg_right hfrac (by positivity)
        _ = (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
            field_simp [ne_of_gt hden1, ne_of_gt hden2]
    linarith
  have hlser : (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤ C_euler := by
    rw [hs_eq]
    exact le_trans (Complex.re_le_norm _) (vonMangoldt_lseries_norm_le_tsum hβ1 γ).2
  have hR_pos : 0 < (xiResolvent z).im := by dsimp [target] at hK_sum; linarith
  have hxi_ne : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 :=
    riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hV_pos : 0 < xiNormSq σ γ := by
    dsimp [xiNormSq]
    have harg : (⟨1 / 2 + σ, γ⟩ : ℂ) = ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
      apply Complex.ext <;> simp
    rw [harg]; exact sq_pos_of_pos (norm_pos_iff.mpr hxi_ne)
  have hlogF := xiResolvent_im_eq_logForce_half hxi_ne
  have hLF_pos : 0 < xiLogForce σ γ := by linarith [hlogF.2]
  have hF_pos : 0 < deriv (fun t : ℝ => xiNormSq t γ) σ := by
    rw [xiLogForce_eq_force_div_normSq hV_pos] at hLF_pos
    exact (div_pos_iff_of_pos_right hV_pos).mp hLF_pos
  have hE_ne : xiShiftE σ (γ : ℂ) ≠ 0 :=
    riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hphase := xiSchur_boundary_logDeriv_eq_I_mul_logForce hE_ne
  have hph_pos : 0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by rw [hphase.2]; simp; exact hLF_pos
  exact ⟨hR_pos, hF_pos, hph_pos⟩

-- ==============================================================================
-- PART III: ROUTE B — SYMMETRIC JACOBI DIAGONAL CLIPPER `D^{-1/2} P D^{-1/2} = I - T_J`
--           COUPLED TO THE UNIVERSAL HOPFIELD-BOLTZMANN SOLVER ON PICK MATRICES
-- ==============================================================================

/-- Symmetric Jacobi diagonal preconditioning / clipping `P_hat_{jk} = P_{jk} / √(d_j d_k)`
    (normalizing every positive diagonal entry to `1`). -/
noncomputable def jacobiClipMatrix {n : ℕ} (P : Fin n → Fin n → ℂ) (j k : Fin n) : ℂ :=
  P j k / ((Real.sqrt (P j j).re * Real.sqrt (P k k).re : ℝ) : ℂ)

/-- Jacobi iteration matrix `T_J = I - P_hat` (zero diagonal, off-diagonal `-P_hat_{jk}`). -/
noncomputable def jacobiIterMatrix {n : ℕ} (P : Fin n → Fin n → ℂ) (j k : Fin n) : ℂ :=
  if j = k then 0 else -jacobiClipMatrix P j k

/-- Helper: `jacobiClipMatrix P` is Hermitian with unit diagonal `1` whenever `P` is Hermitian
    with strictly positive diagonal. -/
private lemma jacobiClipMatrix_herm_and_diag {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) (hdiag : ∀ j, 0 < (P j j).re) :
    (∀ j k, jacobiClipMatrix P k j = starRingEnd ℂ (jacobiClipMatrix P j k)) ∧
    (∀ j, jacobiClipMatrix P j j = 1) := by
  have hdiag_im : ∀ j, (P j j).im = 0 := by
    intro j
    have h := congrArg Complex.im (hHerm j j)
    simp at h; linarith
  constructor
  · intro j k
    dsimp [jacobiClipMatrix]
    rw [map_div₀, Complex.conj_ofReal, hHerm j k, mul_comm (Real.sqrt (P k k).re)]
  · intro j
    dsimp [jacobiClipMatrix]
    have hPjj : P j j = ((P j j).re : ℂ) := by apply Complex.ext <;> simp [hdiag_im j]
    have hsq : Real.sqrt (P j j).re * Real.sqrt (P j j).re = (P j j).re :=
      Real.mul_self_sqrt (le_of_lt (hdiag j))
    rw [hsq, hPjj]
    exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt (hdiag j)))

/-- THEOREM III.1 (EXACT SYLVESTER CONGRUENCE OF SYMMETRIC JACOBI CLIPPING):
    For EVERY `n × n` Hermitian matrix `P` with strictly positive diagonal `0 < (P j j).re`:
    (1) `P` is Hermitian PSD ↔ `jacobiClipMatrix P = D^{-1/2} P D^{-1/2}` is Hermitian PSD,
    (2) Both are 100% equivalent to `∀ c : Fin n → ℂ, Re⟨c, T_J c⟩ ≤ ∑ j, ‖c j‖^2`. -/
theorem jacobiClipMatrix_congruence_hermitian_psd {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) (hdiag : ∀ j, 0 < (P j j).re) :
    ((∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ↔
     (∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re)) ∧
    ((∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re) ↔
     (∀ c : Fin n → ℂ, (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k).re ≤
       ∑ j : Fin n, ‖c j‖ ^ 2)) := by
  have hhd := jacobiClipMatrix_herm_and_diag P hHerm hdiag
  -- (1) Exact Sylvester congruence: `c' j = c j / √d_j`
  have h1 : (∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ↔
      (∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re) := by
    constructor
    · intro hP c
      let c' : Fin n → ℂ := fun j => c j / ((Real.sqrt (P j j).re : ℝ) : ℂ)
      have heq : ∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c' j) * P j k * c' k =
          ∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        dsimp [c', jacobiClipMatrix]
        rw [map_div₀, Complex.conj_ofReal, Complex.ofReal_mul]
        ring
      rw [← heq]; exact hP c'
    · intro hPh c
      let c' : Fin n → ℂ := fun j => c j * ((Real.sqrt (P j j).re : ℝ) : ℂ)
      have heq : ∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c' j) * jacobiClipMatrix P j k * c' k =
          ∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        dsimp [c', jacobiClipMatrix]
        have hsj : ((Real.sqrt (P j j).re : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hdiag j)))
        have hsk : ((Real.sqrt (P k k).re : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hdiag k)))
        rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
        field_simp [hsj, hsk]
      rw [← heq]; exact hPh c'
  -- (2) Identity: `⟨c, P_hat c⟩ = ‖c‖^2 - ⟨c, T_J c⟩`
  have h2_id : ∀ c : Fin n → ℂ,
      (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re =
        (∑ j : Fin n, ‖c j‖ ^ 2) -
        (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k).re := by
    intro c
    have hsplit : ∀ j k : Fin n,
        starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k =
          (if j = k then starRingEnd ℂ (c j) * c j else 0) -
          starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k := by
      intro j k
      dsimp [jacobiIterMatrix]
      split_ifs with hjk
      · subst hjk; rw [hhd.2 j]; ring
      · ring
    simp_rw [hsplit, Finset.sum_sub_distrib, Complex.sub_re]
    congr 1
    have hdiag_sum : ∑ j : Fin n, ∑ k : Fin n, (if j = k then starRingEnd ℂ (c j) * c j else 0) =
        ∑ j : Fin n, starRingEnd ℂ (c j) * c j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp
    rw [hdiag_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  refine ⟨h1, ⟨fun h c => by linarith [h c, h2_id c], fun h c => by linarith [h c, h2_id c]⟩⟩

/-- Helper: Hermitian Gershgorin bound for the off-diagonal Jacobi iteration matrix `T_J`:
    `|(∑ j, ∑ k, conj(c j) * T_J j k * c k).re| ≤ ∑ j, (∑ k ∈ univ.erase j, ‖P_hat j k‖) * ‖c j‖^2`. -/
private lemma jacobiIterMatrix_quadForm_abs_le {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) (hdiag : ∀ j, 0 < (P j j).re)
    (c : Fin n → ℂ) :
    |(∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k).re| ≤
      ∑ j : Fin n, (∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖) * ‖c j‖ ^ 2 := by
  have hhd := jacobiClipMatrix_herm_and_diag P hHerm hdiag
  have h1 : |(∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k).re| ≤
      ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * (‖c j‖ * ‖c k‖) := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]; linarith
  -- Apply AM-GM: `‖c j‖ * ‖c k‖ ≤ (1/2) * (‖c j‖^2 + ‖c k‖^2)` and Hermitian symmetry `‖T_J j k‖ = ‖T_J k j‖`!
  have h2 : ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * (‖c j‖ * ‖c k‖) ≤
      ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ((1 / 2 : ℝ) * (‖c j‖ ^ 2 + ‖c k‖ ^ 2)) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖c j‖ - ‖c k‖)]) (norm_nonneg _)
  have hsymm : ∀ j k : Fin n, ‖jacobiIterMatrix P k j‖ = ‖jacobiIterMatrix P j k‖ := by
    intro j k
    dsimp [jacobiIterMatrix]
    by_cases hjk : j = k
    · subst hjk; simp
    · have hkj : k ≠ j := Ne.symm hjk
      simp only [hjk, hkj, ↓reduceIte, norm_neg]
      rw [hhd.1 j k, Complex.norm_conj]
  have h3 : ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ((1 / 2 : ℝ) * (‖c j‖ ^ 2 + ‖c k‖ ^ 2)) =
      ∑ j : Fin n, (∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖) * ‖c j‖ ^ 2 := by
    have hsplit : ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ((1 / 2 : ℝ) * (‖c j‖ ^ 2 + ‖c k‖ ^ 2)) =
        (1 / 2 : ℝ) * (∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c j‖ ^ 2) +
        (1 / 2 : ℝ) * (∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c k‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit]
    have hswap : ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c k‖ ^ 2 =
        ∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c j‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hsymm]
    rw [hswap]
    have hcomb : (1 / 2 : ℝ) * (∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c j‖ ^ 2) +
        (1 / 2 : ℝ) * (∑ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c j‖ ^ 2) =
        ∑ j : Fin n, (∑ k : Fin n, ‖jacobiIterMatrix P j k‖) * ‖c j‖ ^ 2 := by
      have : ∀ j : Fin n, ∑ k : Fin n, ‖jacobiIterMatrix P j k‖ * ‖c j‖ ^ 2 =
          (∑ k : Fin n, ‖jacobiIterMatrix P j k‖) * ‖c j‖ ^ 2 := fun j => (Finset.sum_mul _ _ _).symm
      simp_rw [this]; ring
    rw [hcomb]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have h0 : ‖jacobiIterMatrix P j j‖ = 0 := by dsimp [jacobiIterMatrix]; simp
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hne : j ≠ k := Ne.symm (Finset.ne_of_mem_erase hk)
    dsimp [jacobiIterMatrix]; simp [hne]
  linarith

/-- THEOREM III.2 (GERSHGORIN-JACOBI O(N^2) SUFFICIENT CONDITION FOR HERMITIAN POSITIVITY):
    If `P` is Hermitian with strictly positive diagonal and its Jacobi iteration matrix
    satisfies `‖T_J‖_∞ ≤ 1` (resp. `< 1`), then `P` is unconditionally Hermitian PSD
    (resp. strictly positive definite for every `c ≠ 0`). -/
theorem jacobiClip_hermitian_psd_and_pos_of_inf_norm {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) (hdiag : ∀ j, 0 < (P j j).re) :
    ((∀ j : Fin n, ∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖ ≤ 1) →
      ∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ∧
    ((∀ j : Fin n, ∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖ < 1) →
      ∀ c : Fin n → ℂ, (∃ j, c j ≠ 0) →
        0 < (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) := by
  have hcong := jacobiClipMatrix_congruence_hermitian_psd P hHerm hdiag
  constructor
  · intro hle
    rw [hcong.1, hcong.2]
    intro c
    have habs := jacobiIterMatrix_quadForm_abs_le P hHerm hdiag c
    have hsum_le : ∑ j : Fin n, (∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖) * ‖c j‖ ^ 2 ≤
        ∑ j : Fin n, ‖c j‖ ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      have := mul_le_mul_of_nonneg_right (hle j) (sq_nonneg ‖c j‖)
      linarith
    linarith [(abs_le.mp habs).2]
  · intro hlt c ⟨j₀, hj₀⟩
    -- Use the same Sylvester scaling c' j = c j * √(d_j) (still nonzero at j₀!)
    let c' : Fin n → ℂ := fun j => c j * ((Real.sqrt (P j j).re : ℝ) : ℂ)
    have heq : ∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c' j) * jacobiClipMatrix P j k * c' k =
        ∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      dsimp [c', jacobiClipMatrix]
      have hsj : ((Real.sqrt (P j j).re : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hdiag j)))
      have hsk : ((Real.sqrt (P k k).re : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hdiag k)))
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      field_simp [hsj, hsk]
    rw [← heq]
    have hhd := jacobiClipMatrix_herm_and_diag P hHerm hdiag
    have hsplit : (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c' j) * jacobiClipMatrix P j k * c' k).re =
        (∑ j : Fin n, ‖c' j‖ ^ 2) -
        (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c' j) * jacobiIterMatrix P j k * c' k).re := by
      have hpt : ∀ j k : Fin n,
          starRingEnd ℂ (c' j) * jacobiClipMatrix P j k * c' k =
            (if j = k then starRingEnd ℂ (c' j) * c' j else 0) -
            starRingEnd ℂ (c' j) * jacobiIterMatrix P j k * c' k := by
        intro j k; dsimp [jacobiIterMatrix]
        split_ifs with hjk
        · subst hjk; rw [hhd.2 j]; ring
        · ring
      simp_rw [hpt, Finset.sum_sub_distrib, Complex.sub_re]
      congr 1
      have hds : ∑ j : Fin n, ∑ k : Fin n, (if j = k then starRingEnd ℂ (c' j) * c' j else 0) =
          ∑ j : Fin n, starRingEnd ℂ (c' j) * c' j :=
        Finset.sum_congr rfl fun j _ => by simp
      rw [hds, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hsplit]
    have habs := jacobiIterMatrix_quadForm_abs_le P hHerm hdiag c'
    have hstrict : ∑ j : Fin n, (∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖) * ‖c' j‖ ^ 2 <
        ∑ j : Fin n, ‖c' j‖ ^ 2 := by
      refine Finset.sum_lt_sum (fun j _ => by nlinarith [hlt j, sq_nonneg ‖c' j‖]) ⟨j₀, Finset.mem_univ j₀, ?_⟩
      have hc'0 : 0 < ‖c' j₀‖ ^ 2 := by
        dsimp [c']
        exact sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hj₀
          (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hdiag j₀))))))
      nlinarith [hlt j₀]
    linarith [(abs_le.mp habs).2]

/-- THEOREM III.3 (DAMPED JACOBI CLIPPER UNIVERSAL SOLVER — O(N^2) LYAPUNOV STABILITY &
    EXACT BICONDITIONAL PHASE-TRANSITION EQUIVALENCE):
    For EVERY `n × n` Hermitian matrix `P` with positive diagonal and ANY Gershgorin row bound
    `M ≥ 0` with `∀ j, ∑_{k ≠ j} ‖P_hat j k‖ ≤ M`, setting `μ = 1 + M > 0` defines the damped
    Jacobi Universal Solver coupling `Q = shiftedCoupling (realLiftedMatrix (jacobiClipMatrix P)) μ`:
    (1) `Q` is UNCONDITIONALLY real PSD (`∀ v, 0 ≤ realQuadForm Q v`), guaranteeing exact
        discrete Lyapunov descent without period-2 cycles (via Module #14 Theorem 6.24.1)
        purely in O(N^2) arithmetic without any eigensolve!
    (2) `P` is Hermitian PSD ↔ `∀ s ∈ (-1, 1)^{2n}, 0 ≤ universalFreeEnergy Q s`! -/
theorem dampedJacobi_universalSolver_psd_and_equivalence {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) (hdiag : ∀ j, 0 < (P j j).re)
    {M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ j : Fin n, ∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖ ≤ M) :
    let μ : ℝ := 1 + M
    let Q := shiftedCoupling (realLiftedMatrix (jacobiClipMatrix P)) μ
    (∀ v : Fin (n + n) → ℝ, 0 ≤ realQuadForm Q v) ∧
    ((∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ↔
      (∀ s : Fin (n + n) → ℝ, (∀ i, |s i| < 1) → 0 ≤ universalFreeEnergy Q s)) := by
  intro μ Q
  have hμ : 0 < μ := by dsimp [μ]; linarith
  have hhd := jacobiClipMatrix_herm_and_diag P hHerm hdiag
  -- (1) Show `realQuadForm (realLiftedMatrix (jacobiClipMatrix P)) v ≤ μ * ∑ v_i^2`, hence `0 ≤ realQuadForm Q v`!
  have hQ_psd : ∀ v : Fin (n + n) → ℝ, 0 ≤ realQuadForm Q v := by
    intro v
    -- Rewrite realQuadForm Q v = ∑ v_i^2 - (1/μ) * realQuadForm (realLiftedMatrix P_hat) v
    have hQ_eq : realQuadForm Q v =
        (∑ a : Fin (n + n), v a ^ 2) - realQuadForm (realLiftedMatrix (jacobiClipMatrix P)) v / μ := by
      dsimp [Q, shiftedCoupling, realQuadForm]
      have h1 : ∀ a : Fin (n + n),
          ∑ b : Fin (n + n), v a * ((if a = b then (1 : ℝ) else 0) - realLiftedMatrix (jacobiClipMatrix P) a b / μ) * v b =
            v a ^ 2 - (∑ b : Fin (n + n), v a * realLiftedMatrix (jacobiClipMatrix P) a b * v b) / μ := by
        intro a
        have hpt : ∀ b : Fin (n + n),
            v a * ((if a = b then (1 : ℝ) else 0) - realLiftedMatrix (jacobiClipMatrix P) a b / μ) * v b =
              (if a = b then v a ^ 2 else 0) - (v a * realLiftedMatrix (jacobiClipMatrix P) a b * v b) / μ := by
          intro b; split_ifs with hab <;> subst_vars <;> ring
        simp only [hpt, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_div]
      simp only [h1, Finset.sum_sub_distrib, Finset.sum_div]
    rw [hQ_eq]
    -- Use `realLiftedMatrix` complex vector `c j = v j + i v (j + n)`!
    let c : Fin n → ℂ := fun j =>
      ((v ⟨j.val, by omega⟩ : ℝ) : ℂ) + Complex.I * ((v ⟨j.val + n, by omega⟩ : ℝ) : ℂ)
    have hnorm_sum : ∑ j : Fin n, ‖c j‖ ^ 2 = ∑ a : Fin (n + n), v a ^ 2 := by
      have hsplit : ∑ a : Fin (n + n), v a ^ 2 =
          (∑ j : Fin n, v ⟨j.val, by omega⟩ ^ 2) + (∑ j : Fin n, v ⟨j.val + n, by omega⟩ ^ 2) := by
        rw [Fin.sum_univ_add]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 2; ext; dsimp [Fin.natAdd]; omega
      rw [hsplit, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [c]; rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    -- Evaluate `realQuadForm (realLiftedMatrix P_hat) v = Re⟨c, P_hat c⟩`
    have hlift_eq : realQuadForm (realLiftedMatrix (jacobiClipMatrix P)) v =
        (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re := by
      dsimp [realQuadForm]
      have hsp : ∀ f : Fin (n + n) → ℝ,
          ∑ a : Fin (n + n), f a =
            (∑ j : Fin n, f ⟨j.val, by omega⟩) + (∑ j : Fin n, f ⟨j.val + n, by omega⟩) := by
        intro f; rw [Fin.sum_univ_add]; congr 1
        refine Finset.sum_congr rfl fun j _ => by congr 1; ext; dsimp [Fin.natAdd]; omega
      rw [hsp]
      have hin : ∀ a : Fin (n + n),
          ∑ b : Fin (n + n), v a * realLiftedMatrix (jacobiClipMatrix P) a b * v b =
            (∑ k : Fin n, v a * realLiftedMatrix (jacobiClipMatrix P) a ⟨k.val, by omega⟩ * v ⟨k.val, by omega⟩) +
            (∑ k : Fin n, v a * realLiftedMatrix (jacobiClipMatrix P) a ⟨k.val + n, by omega⟩ * v ⟨k.val + n, by omega⟩) :=
        fun a => hsp _
      simp only [hin, Finset.sum_add_distrib]
      have hb00 : ∀ j k : Fin n, realLiftedMatrix (jacobiClipMatrix P) ⟨j.val, by omega⟩ ⟨k.val, by omega⟩ =
          (jacobiClipMatrix P j k).re := by
        intro j k; dsimp [realLiftedMatrix]; simp [j.isLt, k.isLt]
      have hb01 : ∀ j k : Fin n, realLiftedMatrix (jacobiClipMatrix P) ⟨j.val, by omega⟩ ⟨k.val + n, by omega⟩ =
          -(jacobiClipMatrix P j k).im := by
        intro j k; dsimp [realLiftedMatrix]
        have hnot : ¬(k.val + n < n) := by omega
        simp [j.isLt, hnot]
      have hb10 : ∀ j k : Fin n, realLiftedMatrix (jacobiClipMatrix P) ⟨j.val + n, by omega⟩ ⟨k.val, by omega⟩ =
          (jacobiClipMatrix P j k).im := by
        intro j k; dsimp [realLiftedMatrix]
        have hnot : ¬(j.val + n < n) := by omega
        simp [k.isLt, hnot]
      have hb11 : ∀ j k : Fin n, realLiftedMatrix (jacobiClipMatrix P) ⟨j.val + n, by omega⟩ ⟨k.val + n, by omega⟩ =
          (jacobiClipMatrix P j k).re := by
        intro j k; dsimp [realLiftedMatrix]
        have h1 : ¬(j.val + n < n) := by omega
        have h2 : ¬(k.val + n < n) := by omega
        simp [h1, h2]
      simp only [hb00, hb01, hb10, hb11, Complex.re_sum]
      have hrhs : ∑ j : Fin n, ∑ k : Fin n, (starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re =
          ∑ j : Fin n, ∑ k : Fin n,
            (v ⟨j.val, by omega⟩ * (jacobiClipMatrix P j k).re * v ⟨k.val, by omega⟩ +
             v ⟨j.val, by omega⟩ * (-(jacobiClipMatrix P j k).im) * v ⟨k.val + n, by omega⟩ +
             v ⟨j.val + n, by omega⟩ * (jacobiClipMatrix P j k).im * v ⟨k.val, by omega⟩ +
             v ⟨j.val + n, by omega⟩ * (jacobiClipMatrix P j k).re * v ⟨k.val + n, by omega⟩) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        dsimp [c]
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
                   Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
                   Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
      rw [hrhs]; simp only [Finset.sum_add_distrib]; ring
    rw [hlift_eq]
    have hsplit : (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re =
        (∑ j : Fin n, ‖c j‖ ^ 2) -
        (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k).re := by
      have hpt : ∀ j k : Fin n,
          starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k =
            (if j = k then starRingEnd ℂ (c j) * c j else 0) -
            starRingEnd ℂ (c j) * jacobiIterMatrix P j k * c k := by
        intro j k; dsimp [jacobiIterMatrix]
        split_ifs with hjk
        · subst hjk; rw [hhd.2 j]; ring
        · ring
      simp_rw [hpt, Finset.sum_sub_distrib, Complex.sub_re]
      congr 1
      have hds : ∑ j : Fin n, ∑ k : Fin n, (if j = k then starRingEnd ℂ (c j) * c j else 0) =
          ∑ j : Fin n, starRingEnd ℂ (c j) * c j :=
        Finset.sum_congr rfl fun j _ => by simp
      rw [hds, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    have habs := jacobiIterMatrix_quadForm_abs_le P hHerm hdiag c
    have hrow_sum : ∑ j : Fin n, (∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖) * ‖c j‖ ^ 2 ≤
        M * ∑ j : Fin n, ‖c j‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hrow j) (sq_nonneg _)
    have hle_mu : (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re ≤
        μ * ∑ a : Fin (n + n), v a ^ 2 := by
      rw [hsplit, ← hnorm_sum]
      have := (abs_le.mp habs).1
      dsimp [μ]; linarith
    have hdiv : (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * jacobiClipMatrix P j k * c k).re / μ ≤
        ∑ a : Fin (n + n), v a ^ 2 := by
      rw [div_le_iff₀ hμ]; linarith
    linarith
  -- (2) Biconditional phase-transition equivalence directly via Theorem III.1 + Module #14 Theorem III.2!
  have hcong := jacobiClipMatrix_congruence_hermitian_psd P hHerm hdiag
  have huniv := (universalSolver_realLifted_pick_iff_hermitian_psd (jacobiClipMatrix P) hhd.1 hμ).2
  exact ⟨hQ_psd, hcong.1.trans huniv⟩

/-- THEOREM III.4 (CONSTRUCTIVE O(N^2) JACOBI-CLIPPER CERTIFICATION OF `xiResolvent` PICK MATRICES):
    For ANY `n` upper half-plane nodes `z : Fin n → ℂ` (`0 < (z j).im`) where `0 < (xiResolvent (z j)).im`
    (such as ANY nodes in the Euler half-plane `Im(z_j) ≥ 15/2` certified by Theorem II.4 or high-ordinate
    tails certified by Theorem II.5), define the `n × n` Pick-Nevanlinna matrix
      `P_{jk} = (xiResolvent (z j) - conj (xiResolvent (z k))) / (z j - conj (z k))`.
    Then `P` is Hermitian with strictly positive diagonal `Im R_ξ(z_j) / Im(z_j) > 0`, and whenever
    the Jacobi-clipped off-diagonal sum satisfies `‖T_J‖_∞ < 1`, `P` is UNCONDITIONALLY STRICTLY
    POSITIVE DEFINITE! -/
theorem pickMatrix_xiResolvent_jacobiClip_pos_of_diagDom {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ j, 0 < (z j).im) (hR : ∀ j, 0 < (xiResolvent (z j)).im) :
    let P : Fin n → Fin n → ℂ := fun j k =>
      (xiResolvent (z j) - starRingEnd ℂ (xiResolvent (z k))) / (z j - starRingEnd ℂ (z k))
    (∀ j k, P k j = starRingEnd ℂ (P j k)) ∧
    (∀ j, 0 < (P j j).re) ∧
    ((∀ j : Fin n, ∑ k ∈ Finset.univ.erase j, ‖jacobiClipMatrix P j k‖ < 1) →
      ∀ c : Fin n → ℂ, (∃ j, c j ≠ 0) →
        0 < (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) := by
  intro P
  have hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k) := by
    intro j k
    dsimp [P]
    rw [map_div₀, map_sub, map_sub, starRingEnd_self_apply, starRingEnd_self_apply]
    have hneg_num : xiResolvent (z k) - starRingEnd ℂ (xiResolvent (z j)) =
        -(starRingEnd ℂ (xiResolvent (z j)) - xiResolvent (z k)) := by ring
    have hneg_den : z k - starRingEnd ℂ (z j) = -(starRingEnd ℂ (z j) - z k) := by ring
    rw [hneg_num, hneg_den, neg_div_neg_eq]
  have hdiag : ∀ j, 0 < (P j j).re := by
    intro j
    dsimp [P]
    have hsub : ∀ w : ℂ, w - starRingEnd ℂ w = Complex.I * ((2 * w.im : ℝ) : ℂ) := by
      intro w; apply Complex.ext <;> simp; ring
    rw [hsub (xiResolvent (z j)), hsub (z j)]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    rw [mul_div_mul_left _ _ hI]
    have hrat : (((2 * (xiResolvent (z j)).im : ℝ) : ℂ) / ((2 * (z j).im : ℝ) : ℂ)).re =
        (xiResolvent (z j)).im / (z j).im := by
      rw [← Complex.ofReal_div, Complex.ofReal_re]
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      field_simp [h2, ne_of_gt (hz j)]
    rw [hrat]
    exact div_pos (hR j) (hz j)
  exact ⟨hHerm, hdiag, (jacobiClip_hermitian_psd_and_pos_of_inf_norm P hHerm hdiag).2⟩

end GeodesicRenormalizationAndEulerJacobiPick

