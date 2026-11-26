/-
  ==============================================================================
  MODULE #15: ROUTE A FINITE-PRIME IMPOSSIBILITY WALL & EXPONENTIAL CANCELLATION,
              ROUTE B HERMITE-BIEHLER / DE BRANGES PHASE SYNTHESIS, AND EXACT
              LOG-CONCAVE DECREASING KERNEL WALL THEOREM (LEAN 4 + MATHLIB4)
  ==============================================================================

  Author: Mariano Martín Ramírez Tamayo
  Affiliation: Independent Researcher

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):

  PART I (ROUTE A — GLOBAL ARCHIMEDEAN UPPER BOUND, FINITE-PRIME WALL, &
          EXPONENTIAL PRIME-CANCELLATION NECESSITY):
    1. `archimedeanWeilConst_gt_four` & `psiArch_le_half_sq`:
       Unconditional global upper bound `psiArch t ≤ t^2 / 2` for every `t : ℝ`.
    2. `oddSinMode_L2_norm_sq` & `oddSinMode_weilPole_exact`:
       For the explicit odd Dirichlet mode `g_L(x) = sin(2πx / L)` on `[-L/2, L/2]`:
         `‖g_L‖_2^2 = L / 2` and
         `W_pole(L, g_L) = -32 * π^2 * L^2 / (L^2 / 4 + 4 * π^2)^2 * sinh(L / 4)^2`.
    3. `oddSinMode_compactFourier_exact` & `oddSinMode_weilArch_upper`:
       Closed-form Fourier transform of `g_L` and universal Archimedean upper bound:
         `(1 / (2π)) * ∫ psiArch(t) * ‖g_L_hat(t)‖^2 dt ≤ 90 / L = (180 / L^2) * ‖g_L‖_2^2`.
    4. `weilTruncated_finitePrimes_eventually_neg` (ROUTE A FINITE-PRIME WALL):
       For EVERY finite prime-power cutoff `N_max : ℕ`, there exists `L_0 > 0` such that
       for every `L ≥ L_0`,
         `W_pole(L, g_L) + W_∞(L, g_L) - W_{prime, ≤ N_max}(L, g_L) < 0`.
       Hence NO finite-prime truncation or bounded-norm perturbation can close Route A.
    5. `weilTotal_pos_forces_exponential_prime_cancellation`:
       Whenever `W_total(L, g_L) ≥ 0`, the full `vonMangoldt` prime-shift operator MUST
       cancel the exponentially diverging negative pole:
         `-W_prime(L, g_L) / ‖g_L‖_2^2 ≥ 64 * π^2 * L / (L^2 / 4 + 4 * π^2)^2 * sinh(L / 4)^2 - 180 / L^2`.

  PART II (ROUTE B — HERMITE-BIEHLER / POTENTIAL MODULUS SYNTHESIS, DE BRANGES
           BOUNDARY PHASE VELOCITY, & UNCONDITIONAL CORRIDOR CONTRACTION):
    6. `xiSchur_norm_sq_eq_xiNormSq_ratio`:
       Exact identity for all `α > 0`, `σ > 0`, `γ : ℝ` with `E_α(γ + iσ) ≠ 0`:
         `‖S_α(γ + iσ)‖^2 = V(|σ - α|, γ) / V(σ + α, γ)`.
    7. `hermiteBiehler_all_iff_xiNormSq_strictMono_all`:
       Exact global biconditional equivalence between strict Hermite-Biehler Schur
       contraction for all `α > 0` and strict transverse monotonicity of `V(·, γ)` on `[0, ∞)`
       (both implying Mathlib4's official `RiemannHypothesis`).
    8. `xiSchur_boundary_logDeriv_eq_I_mul_logForce`:
       Exact closed-loop boundary phase-velocity identity on `ℝ`:
         `logDeriv (xiSchur α) γ = i * (2 * Im R_ξ(γ + iα)) = i * ∂_σ log V(α, γ)`.
    9. `xiResolvent_herglotz_and_schur_contraction_on_corridor_two`:
       Unconditional constructive Herglotz positivity `Im R_ξ(γ + iσ) > 0` on
       `(0, 1/2] × [-2, 2]`, strict Schur contraction `‖S_α(γ + iσ)‖ < 1` on
       `α > 0, σ > 0, α + σ ≤ 1/2, |γ| ≤ 2`, and positive boundary phase velocity
       `Im(logDeriv S_α(γ)) > 0` on `(0, 1/2] × [-2, 2]`.

  PART III (ROUTE B — EXACT LOG-CONCAVE DECREASING KERNEL WALL THEOREM):
   10. `wallKernel_pos_even_antitone_logConcave` & `wallKernel_hankel_psd`:
       For `K_wall(u) = (5 + 2u^2 + u^4) * exp(-u^2)`: strictly positive, even,
       strictly decreasing on `[0, ∞)`, strictly log-concave on ALL of `ℝ`, with
       all moments positive and all order-N Hankel matrices PSD.
   11. `wallKernel_fourierLaplace_exact`:
       Exact closed-form Fourier-Laplace transform for every `z : ℂ`:
         `∫ u : ℝ, K_wall(u) * exp(i*z*u) du = √π * exp(-z^2/4) * (z^4/16 - 5z^2/4 + 27/4)`.
   12. `wallKernel_real_pos_yet_offline_zero_and_laguerre_neg` (ROUTE B LOG-CONCAVE WALL):
       `F_wall(γ) > 0` on all of `ℝ`, yet `F_wall(z_*) = 0` at the explicit off-line
       complex zero `z_* = √(5 + 3√3) + i √(3√3 - 5)` (`Im z_* > 0`), and Laguerre's
       inequality fails strictly at the integer `γ = 3`:
         `(F_wall'(3))^2 - F_wall(3) * F_wall''(3) = -(95 / 18) * (F_wall(3))^2 < 0`.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import RiemannDipolar.UniversalSolverLyapunovAndPrimeResolvent

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators Pointwise
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick UniversalSolverLyapunovAndPrimeResolvent

namespace RouteABLimitBarriersAndDeBrangesSynthesis

-- ==============================================================================
-- PART I: ROUTE A — GLOBAL ARCHIMEDEAN UPPER BOUND, FINITE-PRIME WALL, &
--         EXPONENTIAL PRIME-CANCELLATION NECESSITY
-- ==============================================================================

/-- THEOREM I.1A (Certified Lower Bound `4 < C_∞`):
    Directly from Mathlib4's `1/2 < γ_E`, `3 < log(8π)`, and `3 < π`. -/
theorem archimedeanWeilConst_gt_four : (4 : ℝ) < archimedeanWeilConst := by
  dsimp [archimedeanWeilConst]
  have h1 : (1 / 2 : ℝ) < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog : (3 : ℝ) < Real.log (8 * Real.pi) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h34 := exp_le_taylor_of_nonneg_le_one (y := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h34
    have h34' : Real.exp (3 / 4 : ℝ) < 212 / 100 := by norm_num at h34; linarith
    have hpow : Real.exp (3 : ℝ) = (Real.exp (3 / 4 : ℝ)) ^ (4 : ℕ) := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    rw [hpow]
    have hlt : (Real.exp (3 / 4 : ℝ)) ^ (4 : ℕ) < (212 / 100 : ℝ) ^ (4 : ℕ) :=
      pow_lt_pow_left₀ h34' (le_of_lt (Real.exp_pos _)) (by norm_num)
    have hnum : (212 / 100 : ℝ) ^ (4 : ℕ) < 24 := by norm_num
    linarith
  linarith

/-- Auxiliary telescoping upper bound `∑' n : ℕ, 1 / (n + 1 : ℝ)^3 ≤ 2`. -/
private lemma tsum_one_div_succ_cube_le_two :
    ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 2 := by
  have hs_cube : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3) := by
    have hp : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (3 : ℕ))) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr hp
  -- Telescoping bound on shifted terms n ≥ 1: 1 / (n + 1)^3 ≤ 1/n - 1/(n+1)
  have htele : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 2 := by
    intro N
    cases N with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ']
      have h0 : (1 : ℝ) / (((0 : ℕ) + 1 : ℕ) : ℝ) ^ 3 = 1 := by norm_num
      rw [h0]
      have hrest : ∑ k ∈ Finset.range m, (1 : ℝ) / (((k + 1) + 1 : ℕ) : ℝ) ^ 3 ≤
          ∑ k ∈ Finset.range m, ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hdiff : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) =
            1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
          push_cast; field_simp [ne_of_gt hk1, ne_of_gt hk2]; ring
        rw [hdiff]
        push_cast
        have hle : ((k : ℝ) + 1) * ((k : ℝ) + 2) ≤ ((k : ℝ) + 1 + 1) ^ 3 := by
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          nlinarith [sq_nonneg ((k : ℝ) + 1)]
        exact one_div_le_one_div_of_le (by positivity) hle
      have hsum_tele : ∑ k ∈ Finset.range m, ((1 : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) =
          1 - 1 / ((m + 1 : ℕ) : ℝ) := by
        clear hrest
        induction m with
        | zero => simp
        | succ r ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast; ring
      have hpos : (0 : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by positivity
      linarith
  exact Real.tsum_le_of_sum_range_le (fun _ => by positivity) htele

/-- THEOREM I.1B (EXACT GLOBAL QUADRATIC UPPER BOUND ON `psiArch`):
    For EVERY `t : ℝ`, `psiArch t ≤ t^2 / 2`. -/
theorem psiArch_le_half_sq (t : ℝ) : psiArch t ≤ t ^ 2 / 2 := by
  dsimp [psiArch]
  have hsum := psiArch_summable t
  rw [hsum.tsum_eq_zero_add]
  have h0 : psiArchTerm t 0 ≤ 4 := by
    dsimp [psiArchTerm]
    have hden : (0 : ℝ) < ((0 : ℕ) + 1 / 4) * (((0 : ℕ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by positivity
    rw [div_le_iff₀ hden]
    norm_num
    nlinarith [sq_nonneg t]
  have htail : ∑' n : ℕ, psiArchTerm t (n + 1) ≤ t ^ 2 / 2 := by
    have hs_cube : Summable (fun n : ℕ => (t ^ 2 / 4) * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3)) := by
      have hp : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (3 : ℕ))) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      exact ((summable_nat_add_iff 1).mpr hp).mul_left (t ^ 2 / 4)
    have hle_pt : ∀ n : ℕ, psiArchTerm t (n + 1) ≤ (t ^ 2 / 4) * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3) := by
      intro n
      dsimp [psiArchTerm]
      rw [mul_one_div]
      have hpos1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hle1 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 / 4 := by linarith
      have hden : ((n + 1 : ℕ) : ℝ) ^ 3 ≤
          (((n + 1 : ℕ) : ℝ) + 1 / 4) * ((((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by
        have h3 : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ (((n + 1 : ℕ) : ℝ) + 1 / 4) ^ 3 :=
          pow_le_pow_left₀ (le_of_lt hpos1) hle1 3
        nlinarith [sq_nonneg t]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have hs_shift : Summable (fun n : ℕ => psiArchTerm t (n + 1)) :=
      (summable_nat_add_iff 1).mpr hsum
    have hts := hs_shift.tsum_le_tsum hle_pt hs_cube
    rw [tsum_mul_left] at hts
    have h2 := tsum_one_div_succ_cube_le_two
    nlinarith [sq_nonneg t]
  have hC := archimedeanWeilConst_gt_four
  linarith

/-- Explicit odd Dirichlet test mode `g_L(x) = sin(2πx / L)` on `[-L/2, L/2]`. -/
noncomputable def oddSinMode (L : ℝ) (x : ℝ) : ℂ :=
  ((Real.sin (2 * Real.pi * x / L) : ℝ) : ℂ)

lemma continuous_oddSinMode (L : ℝ) : Continuous (oddSinMode L) := by
  unfold oddSinMode; fun_prop

/-- THEOREM I.2A (Exact `L^2` Norm of `oddSinMode L` on `[-L/2, L/2]`):
    `∫_{-L/2}^{L/2} ‖oddSinMode L x‖^2 dx = L / 2`. -/
theorem oddSinMode_L2_norm_sq {L : ℝ} (hL : 0 < L) :
    ∫ x in (-L / 2)..(L / 2), ‖oddSinMode L x‖ ^ 2 = L / 2 := by
  have heq : ∀ x : ℝ, ‖oddSinMode L x‖ ^ 2 =
      (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.cos (4 * Real.pi * x / L) := by
    intro x
    dsimp [oddSinMode]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hcos := Real.cos_two_mul (2 * Real.pi * x / L)
    have hsq := Real.sin_sq_add_cos_sq (2 * Real.pi * x / L)
    have harg : 2 * (2 * Real.pi * x / L) = 4 * Real.pi * x / L := by ring
    rw [harg] at hcos
    linarith
  simp_rw [heq]
  -- Exact antiderivative: F(x) = x/2 - (L / (8π)) * sin(4πx / L)
  let F : ℝ → ℝ := fun x => x / 2 - (L / (8 * Real.pi)) * Real.sin (4 * Real.pi * x / L)
  have hderiv : ∀ x ∈ Set.uIcc (-L / 2) (L / 2),
      HasDerivAt F ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.cos (4 * Real.pi * x / L)) x := by
    intro x _
    have hlin : HasDerivAt (fun t : ℝ => 4 * Real.pi * t / L) (4 * Real.pi / L) x := by
      have h1 := ((hasDerivAt_id' x).const_mul (4 * Real.pi)).div_const L
      simpa using h1
    have hsin := hlin.sin
    have h1 := (hasDerivAt_id' x).div_const 2
    have h2 := hsin.const_mul (L / (8 * Real.pi))
    refine (h1.fun_sub h2).congr_deriv ?_
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hL_ne : L ≠ 0 := ne_of_gt hL
    field_simp [hpi_ne, hL_ne]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
  dsimp [F]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have ha1 : 4 * Real.pi * (L / 2) / L = 2 * Real.pi := by field_simp [hL_ne]; ring
  have ha2 : 4 * Real.pi * (-L / 2) / L = -(2 * Real.pi) := by field_simp [hL_ne]; ring
  rw [ha1, ha2, Real.sin_neg, Real.sin_two_pi]
  ring

/-- THEOREM I.2B (EXACT CLOSED-FORM NEGATIVE POLE OF `oddSinMode L`):
    For every `L > 0`,
      `W_pole(L, g_L) = -32 * π^2 * L^2 / (L^2 / 4 + 4 * π^2)^2 * sinh(L / 4)^2`. -/
theorem oddSinMode_weilPole_exact {L : ℝ} (hL : 0 < L) :
    weilPole L (oddSinMode L) =
      -(32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 := by
  rw [weilPole_eq_cosh_sub_sinh L (continuous_oddSinMode L)]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  set ω : ℝ := 2 * Real.pi / L
  -- First, cosh integral vanishes by oddness of sin(ω x) * cosh(x/2)
  have hcosh_zero : ∫ u in (-L / 2)..(L / 2), oddSinMode L u * ((Real.cosh (u / 2) : ℝ) : ℂ) = 0 := by
    have hodd : ∀ u : ℝ, oddSinMode L (-u) * ((Real.cosh ((-u) / 2) : ℝ) : ℂ) =
        -(oddSinMode L u * ((Real.cosh (u / 2) : ℝ) : ℂ)) := by
      intro u
      dsimp [oddSinMode]
      have harg1 : 2 * Real.pi * -u / L = -(2 * Real.pi * u / L) := by ring
      have harg2 : (-u) / 2 = -(u / 2) := by ring
      rw [harg1, harg2, Real.sin_neg, Real.cosh_neg]
      push_cast; ring
    have hsym := intervalIntegral.integral_comp_neg (a := -L / 2) (b := L / 2)
      (f := fun u : ℝ => oddSinMode L u * ((Real.cosh (u / 2) : ℝ) : ℂ))
    have hneg1 : -(-L / 2) = L / 2 := by ring
    have hneg2 : -(L / 2) = -L / 2 := by ring
    rw [hneg1, hneg2] at hsym
    simp_rw [hodd, intervalIntegral.integral_neg] at hsym
    -- hsym : -(∫ u in (-L/2)..(L/2), f u) = ∫ u in (-L/2)..(L/2), f u
    have h2 : (2 : ℂ) * (∫ u in (-L / 2)..(L / 2), oddSinMode L u * ((Real.cosh (u / 2) : ℝ) : ℂ)) = 0 := by
      linear_combination -hsym
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  -- Second, compute exact real integral ∫_{-L/2}^{L/2} sin(ω u) * sinh(u/2) du by FTC!
  have hsinh_real : ∫ u in (-L / 2)..(L / 2), Real.sin (2 * Real.pi * u / L) * Real.sinh (u / 2) =
      4 * Real.pi * L * Real.sinh (L / 4) / (L ^ 2 / 4 + 4 * Real.pi ^ 2) := by
    -- Antiderivative: F(u) = ((1/2)*sin(ω u)*cosh(u/2) - ω*cos(ω u)*sinh(u/2)) / (1/4 + ω^2)
    have hden_pos : 0 < (1 / 4 : ℝ) + ω ^ 2 := by positivity
    let F : ℝ → ℝ := fun u =>
      ((1 / 2 : ℝ) * Real.sin (ω * u) * Real.cosh (u / 2) -
        ω * Real.cos (ω * u) * Real.sinh (u / 2)) / ((1 / 4 : ℝ) + ω ^ 2)
    have hderiv : ∀ u ∈ Set.uIcc (-L / 2) (L / 2),
        HasDerivAt F (Real.sin (2 * Real.pi * u / L) * Real.sinh (u / 2)) u := by
      intro u _
      have hwu : HasDerivAt (fun t : ℝ => ω * t) ω u := by
        simpa using (hasDerivAt_id' u).const_mul ω
      have hu2 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) u := by
        simpa using (hasDerivAt_id' u).div_const 2
      have h1 := ((hwu.sin.const_mul (1 / 2 : ℝ)).fun_mul hu2.cosh)
      have h2 := ((hwu.cos.const_mul ω).fun_mul hu2.sinh)
      have h3 := (h1.fun_sub h2).div_const ((1 / 4 : ℝ) + ω ^ 2)
      refine h3.congr_deriv ?_
      have harg : ω * u = 2 * Real.pi * u / L := by dsimp [ω]; ring
      rw [harg]
      field_simp [ne_of_gt hden_pos]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
    dsimp [F]
    have ha1 : ω * (L / 2) = Real.pi := by dsimp [ω]; field_simp [hL_ne]
    have ha2 : ω * (-L / 2) = -Real.pi := by dsimp [ω]; field_simp [hL_ne]
    have hb1 : (L / 2) / 2 = L / 4 := by ring
    have hb2 : (-L / 2) / 2 = -(L / 4) := by ring
    rw [ha1, ha2, hb1, hb2, Real.sin_neg, Real.cos_neg, Real.sinh_neg, Real.cosh_neg,
        Real.sin_pi, Real.cos_pi]
    dsimp [ω]
    have hden2 : L ^ 2 / 4 + 4 * Real.pi ^ 2 ≠ 0 := by positivity
    field_simp [hL_ne, hden2]
    ring
  have hsinh_c : ∫ u in (-L / 2)..(L / 2), oddSinMode L u * ((Real.sinh (u / 2) : ℝ) : ℂ) =
      ((4 * Real.pi * L * Real.sinh (L / 4) / (L ^ 2 / 4 + 4 * Real.pi ^ 2) : ℝ) : ℂ) := by
    have hcast : ∀ u : ℝ, oddSinMode L u * ((Real.sinh (u / 2) : ℝ) : ℂ) =
        ((Real.sin (2 * Real.pi * u / L) * Real.sinh (u / 2) : ℝ) : ℂ) := fun u => by
      dsimp [oddSinMode]; push_cast; rfl
    simp_rw [hcast]
    rw [intervalIntegral.integral_ofReal, hsinh_real]
  rw [hcosh_zero, hsinh_c, norm_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
  ring

/-- Helper: exact Fourier transform of `oddSinMode L` away from `|t| = 2π / L`, and
    universal pointwise bound `t^2 * ‖compactFourier L (oddSinMode L) t‖^2`. -/
theorem oddSinMode_compactFourier_norm_sq_le {L : ℝ} (hL : 0 < L) {t : ℝ}
    (ht_ne1 : t ≠ 2 * Real.pi / L) (ht_ne2 : t ≠ -(2 * Real.pi / L)) :
    ‖compactFourier L (oddSinMode L) t‖ =
      |4 * Real.pi * L * Real.sin (L * t / 2) / (4 * Real.pi ^ 2 - L ^ 2 * t ^ 2)| := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  set ω : ℝ := 2 * Real.pi / L
  have hne_sub : ω - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht_ne1)
  have hne_add : ω + t ≠ 0 := by
    intro h; apply ht_ne2; linarith
  -- Split exp(I*t*u) = cos(t*u) + I*sin(t*u); real part is odd -> 0!
  have hsplit : ∀ u : ℝ, oddSinMode L u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) =
      ((Real.sin (ω * u) * Real.cos (t * u) : ℝ) : ℂ) +
      Complex.I * ((Real.sin (ω * u) * Real.sin (t * u) : ℝ) : ℂ) := by
    intro u
    dsimp [oddSinMode]
    have harg1 : 2 * Real.pi * u / L = ω * u := by dsimp [ω]; ring
    have harg2 : Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg1, harg2, Complex.exp_mul_I]
    simp only [Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_mul]
    ring
  dsimp [compactFourier]
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  -- Odd cosine part vanishes
  have hre_zero : ∫ u in (-L / 2)..(L / 2), Real.sin (ω * u) * Real.cos (t * u) = 0 := by
    have hodd : ∀ u : ℝ, Real.sin (ω * (-u)) * Real.cos (t * (-u)) =
        -(Real.sin (ω * u) * Real.cos (t * u)) := by
      intro u; rw [mul_neg, mul_neg, Real.sin_neg, Real.cos_neg]; ring
    have hsym := intervalIntegral.integral_comp_neg (a := -L / 2) (b := L / 2)
      (f := fun u : ℝ => Real.sin (ω * u) * Real.cos (t * u))
    have hn1 : -(-L / 2) = L / 2 := by ring
    have hn2 : -(L / 2) = -L / 2 := by ring
    rw [hn1, hn2] at hsym
    simp_rw [hodd, intervalIntegral.integral_neg] at hsym
    linarith
  -- Compute exact sine*sine integral by FTC
  have him_val : ∫ u in (-L / 2)..(L / 2), Real.sin (ω * u) * Real.sin (t * u) =
      4 * Real.pi * L * Real.sin (L * t / 2) / (4 * Real.pi ^ 2 - L ^ 2 * t ^ 2) := by
    let F : ℝ → ℝ := fun u =>
      (1 / 2 : ℝ) * (Real.sin ((ω - t) * u) / (ω - t) - Real.sin ((ω + t) * u) / (ω + t))
    have hderiv : ∀ u ∈ Set.uIcc (-L / 2) (L / 2),
        HasDerivAt F (Real.sin (ω * u) * Real.sin (t * u)) u := by
      intro u _
      have h1 : HasDerivAt (fun s : ℝ => Real.sin ((ω - t) * s) / (ω - t)) (Real.cos ((ω - t) * u)) u := by
        have ha : HasDerivAt (fun s : ℝ => (ω - t) * s) (ω - t) u := by
          simpa using (hasDerivAt_id' u).const_mul (ω - t)
        refine (ha.sin.div_const (ω - t)).congr_deriv ?_
        field_simp [hne_sub]
      have h2 : HasDerivAt (fun s : ℝ => Real.sin ((ω + t) * s) / (ω + t)) (Real.cos ((ω + t) * u)) u := by
        have ha : HasDerivAt (fun s : ℝ => (ω + t) * s) (ω + t) u := by
          simpa using (hasDerivAt_id' u).const_mul (ω + t)
        refine (ha.sin.div_const (ω + t)).congr_deriv ?_
        field_simp [hne_add]
      refine ((h1.fun_sub h2).const_mul (1 / 2 : ℝ)).congr_deriv ?_
      have hc1 : Real.cos ((ω - t) * u) = Real.cos (ω * u - t * u) := by ring_nf
      have hc2 : Real.cos ((ω + t) * u) = Real.cos (ω * u + t * u) := by ring_nf
      rw [hc1, hc2, Real.cos_sub, Real.cos_add]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) _ _)]
    dsimp [F]
    have ha1 : (ω - t) * (L / 2) = Real.pi - L * t / 2 := by dsimp [ω]; field_simp [hL_ne]
    have ha2 : (ω + t) * (L / 2) = L * t / 2 + Real.pi := by dsimp [ω]; field_simp [hL_ne]; ring
    have ha3 : (ω - t) * (-L / 2) = -(Real.pi - L * t / 2) := by dsimp [ω]; field_simp [hL_ne]
    have ha4 : (ω + t) * (-L / 2) = -(L * t / 2 + Real.pi) := by dsimp [ω]; field_simp [hL_ne]; ring
    rw [ha1, ha2, ha3, ha4, Real.sin_neg, Real.sin_neg, Real.sin_pi_sub, Real.sin_add_pi]
    have hsq_ne : ω ^ 2 - t ^ 2 ≠ 0 := by
      have hfac : ω ^ 2 - t ^ 2 = (ω - t) * (ω + t) := by ring
      rw [hfac]
      exact mul_ne_zero hne_sub hne_add
    have hcomb : (1 / 2 : ℝ) * (Real.sin (L * t / 2) / (ω - t) - -Real.sin (L * t / 2) / (ω + t)) -
        (1 / 2 : ℝ) * (-Real.sin (L * t / 2) / (ω - t) - - -Real.sin (L * t / 2) / (ω + t)) =
        Real.sin (L * t / 2) * (2 * ω / (ω ^ 2 - t ^ 2)) := by
      field_simp [hne_sub, hne_add, hsq_ne]; ring
    rw [hcomb]
    have hnum_eq : 2 * ω * L ^ 2 = 4 * Real.pi * L := by
      dsimp [ω]; field_simp [hL_ne]; ring
    have hden_eq : (ω ^ 2 - t ^ 2) * L ^ 2 = 4 * Real.pi ^ 2 - L ^ 2 * t ^ 2 := by
      dsimp [ω]; field_simp [hL_ne]; ring
    have hrat : 2 * ω / (ω ^ 2 - t ^ 2) = 4 * Real.pi * L / (4 * Real.pi ^ 2 - L ^ 2 * t ^ 2) := by
      rw [← mul_div_mul_right (2 * ω) (ω ^ 2 - t ^ 2) (pow_ne_zero 2 hL_ne), hnum_eq, hden_eq]
    rw [hrat]; ring
  rw [hre_zero, him_val, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]

/-- Helper: elementary `t^2 * ‖compactFourier L (oddSinMode L) t‖^2` envelope valid a.e. on `ℝ`. -/
private lemma oddSinMode_t2_fourier_bound {L : ℝ} (hL : 0 < L) {t : ℝ}
    (ht_ne1 : t ≠ 2 * Real.pi / L) (ht_ne2 : t ≠ -(2 * Real.pi / L)) :
    (t ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2 ≤
      if |t| ≤ 4 * Real.pi / L then 2 * Real.pi ^ 2
      else (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ) := by
  rw [oddSinMode_compactFourier_norm_sq_le hL ht_ne1 ht_ne2, sq_abs]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  set u : ℝ := L * t / 2
  have hrewrite : (t ^ 2 / 2) * (4 * Real.pi * L * Real.sin (L * t / 2) / (4 * Real.pi ^ 2 - L ^ 2 * t ^ 2)) ^ 2 =
      2 * Real.pi ^ 2 * (u * Real.sin u / (Real.pi ^ 2 - u ^ 2)) ^ 2 := by
    have hu_eq : L * t / 2 = u := rfl
    have ht_eq : t = 2 * u / L := by dsimp [u]; field_simp [hL_ne]
    rw [hu_eq, ht_eq]
    have hden1 : 4 * Real.pi ^ 2 - L ^ 2 * (2 * u / L) ^ 2 = 4 * (Real.pi ^ 2 - u ^ 2) := by
      field_simp [hL_ne]; ring
    rw [hden1]
    have hpi_u_ne : Real.pi ^ 2 - u ^ 2 ≠ 0 := by
      intro h0
      have hfac : (Real.pi - u) * (Real.pi + u) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h1 | h2
      · apply ht_ne1; rw [ht_eq, show u = Real.pi by linarith]
      · apply ht_ne2; rw [ht_eq, show u = -Real.pi by linarith]; ring
    field_simp [hL_ne, hpi_u_ne]
  rw [hrewrite]
  split_ifs with hle
  · -- Case |t| ≤ 4π/L: show |u * sin u / (π^2 - u^2)| ≤ 1!
    have h1 : |u * Real.sin u / (Real.pi ^ 2 - u ^ 2)| ≤ 1 := by
      have hpi_u_ne : Real.pi ^ 2 - u ^ 2 ≠ 0 := by
        intro h0
        have hfac : (Real.pi - u) * (Real.pi + u) = 0 := by linarith
        rcases mul_eq_zero.mp hfac with h1 | h2
        · apply ht_ne1; dsimp [u] at h1; field_simp [hL_ne]; linarith
        · apply ht_ne2; dsimp [u] at h2; field_simp [hL_ne]; linarith
      have hsin_le : |Real.sin u| ≤ abs (|u| - Real.pi) := by
        have heq1 : |Real.sin u| = |Real.sin (abs u)| := by
          rcases le_total 0 u with hu | hu
          · rw [abs_of_nonneg hu]
          · rw [abs_of_nonpos hu, Real.sin_neg, abs_neg]
        have heq2 : |Real.sin (abs u)| = |Real.sin (abs u - Real.pi)| := by
          rw [Real.sin_sub_pi, abs_neg]
        rw [heq1, heq2]
        exact Real.abs_sin_le_abs
      have hden_eq : |Real.pi ^ 2 - u ^ 2| = (Real.pi + |u|) * abs (|u| - Real.pi) := by
        have hsq : Real.pi ^ 2 - u ^ 2 = -((Real.pi + |u|) * (|u| - Real.pi)) := by
          rw [← sq_abs u]; ring
        rw [hsq, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < Real.pi + |u|)]
      rw [abs_div, abs_mul, hden_eq]
      have hdiff_pos : 0 < abs (|u| - Real.pi) := by
        rw [abs_pos]; intro h0
        apply hpi_u_ne
        have : |u| = Real.pi := by linarith
        rw [← sq_abs u, this]; ring
      have hden_pos : 0 < (Real.pi + |u|) * abs (|u| - Real.pi) := by positivity
      rw [div_le_one hden_pos]
      exact mul_le_mul (by linarith [Real.pi_pos]) hsin_le (abs_nonneg _) (by positivity)
    have hsq1 : (u * Real.sin u / (Real.pi ^ 2 - u ^ 2)) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (u * Real.sin u / (Real.pi ^ 2 - u ^ 2))]
    nlinarith [sq_nonneg Real.pi]
  · -- Case |t| > 4π/L => |u| > 2π => u^2 - π^2 ≥ (3/4)*u^2!
    push Not at hle
    have hu_gt : 2 * Real.pi < |u| := by
      dsimp [u]
      rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := (div_lt_iff₀ hL).mp hle
      linarith
    have hu_sq : 4 * Real.pi ^ 2 < u ^ 2 := by
      have : (2 * Real.pi) ^ 2 < |u| ^ 2 := sq_lt_sq' (by linarith [Real.pi_pos]) hu_gt
      rw [sq_abs] at this; linarith
    have hden_lb : (3 / 4 : ℝ) * u ^ 2 ≤ u ^ 2 - Real.pi ^ 2 := by linarith
    have hu_pos : 0 < u ^ 2 := by nlinarith [Real.pi_pos]
    have hsin2 : Real.sin u ^ 2 ≤ 1 := Real.sin_sq_le_one u
    have hfrac : (u * Real.sin u / (Real.pi ^ 2 - u ^ 2)) ^ 2 ≤ (16 / 9 : ℝ) / u ^ 2 := by
      have hsq_eq : (Real.pi ^ 2 - u ^ 2) ^ 2 = (u ^ 2 - Real.pi ^ 2) ^ 2 := by ring
      rw [div_pow, mul_pow, hsq_eq]
      have hden_sq : ((3 / 4 : ℝ) * u ^ 2) ^ 2 ≤ (u ^ 2 - Real.pi ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hden_lb 2
      have hnum : u ^ 2 * Real.sin u ^ 2 ≤ u ^ 2 := by nlinarith
      calc u ^ 2 * Real.sin u ^ 2 / (u ^ 2 - Real.pi ^ 2) ^ 2
        _ ≤ u ^ 2 / ((3 / 4 : ℝ) * u ^ 2) ^ 2 :=
            div_le_div₀ (by positivity) hnum (by positivity) hden_sq
        _ = (16 / 9 : ℝ) / u ^ 2 := by field_simp [ne_of_gt hu_pos]; ring
    have ht_ne0 : t ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hle; linarith [div_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) hL]
    have hrpow : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      simp [zpow_neg]
    rw [hrpow]
    have hrhs_eq : 2 * Real.pi ^ 2 * ((16 / 9 : ℝ) / u ^ 2) =
        (128 * Real.pi ^ 2 / (9 * L ^ 2)) * (t ^ 2)⁻¹ := by
      dsimp [u]; field_simp [hL_ne, ht_ne0]; ring
    nlinarith [sq_nonneg Real.pi]

/-- THEOREM I.3 (UNIVERSAL ARCHIMEDEAN UPPER BOUND ON `oddSinMode L`):
    For EVERY `L > 0`:
      `(1 / (2π)) * ∫ t : ℝ, psiArch t * ‖compactFourier L (oddSinMode L) t‖^2 ≤ 90 / L`.
    Thus `W_∞(L, g_L) / ‖g_L‖_2^2 ≤ 180 / L^2 → 0` as `L → ∞`! -/
theorem oddSinMode_weilArch_upper {L : ℝ} (hL : 0 < L) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) ≤ 90 / L := by
  set a : ℝ := 4 * Real.pi / L
  have ha_pos : 0 < a := by positivity
  -- Define majorant M(t) = (2π^2) on |t| ≤ a, else (128π^2 / (9 L^2)) * t^{-2}
  let M : ℝ → ℝ := fun t =>
    if |t| ≤ a then 2 * Real.pi ^ 2 else (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ)
  have hM_int_Icc : IntegrableOn (fun _ : ℝ => 2 * Real.pi ^ 2) (Icc (-a) a) :=
    integrableOn_const (by simp)
  have hM_int_Ioi : IntegrableOn (fun t : ℝ => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha_pos).const_mul _
  have hM_int_Iio : IntegrableOn (fun t : ℝ => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ)) (Iio (-a)) := by
    have hcomp := hM_int_Ioi.comp_neg
    have hpre : -Ioi a = Iio (-a) := by ext t; simp [lt_neg]
    rw [hpre] at hcomp
    refine hcomp.congr_fun (fun t _ => ?_) measurableSet_Iio
    have heq : (-t) ^ (-2 : ℝ) = t ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, Real.rpow_intCast]
      simp [zpow_neg]
    simp [heq]
  have hM_eq_ind : ∀ t : ℝ, M t =
      (Icc (-a) a).indicator (fun _ => 2 * Real.pi ^ 2) t +
      (Ioi a).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t +
      (Iio (-a)).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t := by
    intro t
    dsimp [M]
    by_cases h1 : |t| ≤ a
    · have hm : t ∈ Icc (-a) a := abs_le.mp h1
      have hno1 : t ∉ Ioi a := by simp; linarith [hm.2]
      have hno2 : t ∉ Iio (-a) := by simp; linarith [hm.1]
      simp [h1, hm, hno1, hno2]
    · push Not at h1
      have hno0 : t ∉ Icc (-a) a := fun hm => absurd (abs_le.mpr hm) (not_le.mpr h1)
      rcases lt_or_gt_of_ne (show t ≠ 0 by intro h0; rw [h0, abs_zero] at h1; linarith) with hneg | hpos
      · have hm2 : t ∈ Iio (-a) := by rw [abs_of_neg hneg] at h1; simp; linarith
        have hno1 : t ∉ Ioi a := by simp; linarith
        simp [not_le.mpr h1, hno0, hno1, hm2]
      · have hm1 : t ∈ Ioi a := by rw [abs_of_pos hpos] at h1; exact h1
        have hno2 : t ∉ Iio (-a) := by simp; linarith
        simp [not_le.mpr h1, hno0, hm1, hno2]
  have hM_integrable : Integrable M := by
    have h1 := (integrable_indicator_iff measurableSet_Icc).mpr hM_int_Icc
    have h2 := (integrable_indicator_iff measurableSet_Ioi).mpr hM_int_Ioi
    have h3 := (integrable_indicator_iff measurableSet_Iio).mpr hM_int_Iio
    exact ((h1.add h2).add h3).congr (ae_of_all _ fun t => (hM_eq_ind t).symm)
  -- Exact integral of M(t)
  have hM_integral : ∫ t : ℝ, M t = 16 * Real.pi ^ 3 / L + 64 * Real.pi / (9 * L) := by
    have h1 : Integrable (fun t => (Icc (-a) a).indicator (fun _ => 2 * Real.pi ^ 2) t) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hM_int_Icc
    have h2 : Integrable (fun t => (Ioi a).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hM_int_Ioi
    have h3 : Integrable (fun t => (Iio (-a)).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t) :=
      (integrable_indicator_iff measurableSet_Iio).mpr hM_int_Iio
    have h12 : Integrable (fun t =>
        (Icc (-a) a).indicator (fun _ => 2 * Real.pi ^ 2) t +
        (Ioi a).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t) := h1.add h2
    calc ∫ t : ℝ, M t
      _ = ∫ t : ℝ, (((Icc (-a) a).indicator (fun _ => 2 * Real.pi ^ 2) t +
          (Ioi a).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t) +
          (Iio (-a)).indicator (fun s => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * s ^ (-2 : ℝ)) t) := by
          simp_rw [hM_eq_ind]
      _ = (∫ t in Icc (-a) a, (2 * Real.pi ^ 2 : ℝ)) +
          (∫ t in Ioi a, (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ)) +
          (∫ t in Iio (-a), (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ)) := by
          rw [integral_add h12 h3, integral_add h1 h2,
              integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioi,
              integral_indicator measurableSet_Iio]
      _ = (2 * a * (2 * Real.pi ^ 2)) + 2 * ((128 * Real.pi ^ 2 / (9 * L ^ 2)) * a⁻¹) := by
          have hi0 : ∫ _ in Icc (-a) a, (2 * Real.pi ^ 2 : ℝ) = 2 * a * (2 * Real.pi ^ 2) := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
            ring
          have hi1 : ∫ t in Ioi a, (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ) =
              (128 * Real.pi ^ 2 / (9 * L ^ 2)) * a⁻¹ := by
            rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha_pos]
            have : (-2 : ℝ) + 1 = -1 := by norm_num
            rw [this, Real.rpow_neg_one]; ring
          have hi2 : ∫ t in Iio (-a), (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ) =
              ∫ t in Ioi a, (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ) := by
            rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
            have hneg := integral_comp_neg_Ioi (c := a)
              (f := fun t : ℝ => (128 * Real.pi ^ 2 / (9 * L ^ 2)) * t ^ (-2 : ℝ))
            rw [← hneg]
            refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
            have heq : (-t) ^ (-2 : ℝ) = t ^ (-2 : ℝ) := by
              rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, Real.rpow_intCast]
              simp [zpow_neg]
            simp [heq]
          rw [hi0, hi2, hi1]; ring
      _ = 16 * Real.pi ^ 3 / L + 64 * Real.pi / (9 * L) := by
          dsimp [a]; field_simp [ne_of_gt hL, Real.pi_ne_zero]; ring
  -- Pointwise a.e. bound psiArch(t) * ‖g_hat(t)‖^2 ≤ M(t) (holds away from {±2π/L})
  have hbad : volume ({2 * Real.pi / L, -(2 * Real.pi / L)} : Set ℝ) = 0 :=
    Set.Countable.measure_zero (Set.to_countable _) volume
  have hae_bad : ∀ᵐ t : ℝ, t ∉ ({2 * Real.pi / L, -(2 * Real.pi / L)} : Set ℝ) :=
    compl_mem_ae_iff.mpr (by simpa using hbad)
  have hle_ae : (fun t : ℝ => psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) ≤ᵐ[volume] M := by
    filter_upwards [hae_bad] with t ht
    have ht1 : t ≠ 2 * Real.pi / L := fun h => ht (by simp [h])
    have ht2 : t ≠ -(2 * Real.pi / L) := fun h => ht (by simp [h])
    have h1 : psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2 ≤
        (t ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (psiArch_le_half_sq t) (sq_nonneg _)
    exact le_trans h1 (oddSinMode_t2_fourier_bound hL ht1 ht2)
  -- Integrability of psiArch(t) * ‖g_hat(t)‖^2
  have hf_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) := by
    have hcont_f : Continuous (fun t : ℝ => compactFourier L (oddSinMode L) t) := by
      dsimp [compactFourier]
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ (-L / 2) (L / 2)
      exact ((continuous_oddSinMode L).comp continuous_snd).mul
        (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul
          (Complex.continuous_ofReal.comp continuous_snd)))
    have hmeas_psi : Measurable psiArch := by
      unfold psiArch
      refine Measurable.const_add ?_ (-archimedeanWeilConst)
      refine Measurable.tsum fun n => ?_
      have hc : Continuous (fun t : ℝ => psiArchTerm t n) := by
        unfold psiArchTerm
        have h1 : Continuous (fun t : ℝ => t ^ 2 / 4) := (continuous_pow 2).div_const 4
        have h2 : Continuous (fun t : ℝ => ((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4)) :=
          continuous_const.mul (continuous_const.add h1)
        exact h1.div h2 (fun t => by positivity)
      exact hc.measurable
    have haesm : AEStronglyMeasurable (fun t : ℝ => psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) volume :=
      (hmeas_psi.mul (hcont_f.norm.pow 2).measurable).aestronglyMeasurable
    -- Dominating integrable bound: on |t| ≤ a, ‖g_hat‖^2 ≤ L^2/2; on |t| > a, ‖g_hat‖^2 ≤ (2/a^2)*M(t)!
    let D : ℝ → ℝ := fun t =>
      (1 + archimedeanWeilConst * (2 / a ^ 2)) * M t +
        archimedeanWeilConst * (Icc (-a) a).indicator (fun _ => L ^ 2 / 2) t
    have hD_int : Integrable D := by
      refine (hM_integrable.const_mul _).add ?_
      exact ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul _
    refine hD_int.mono' haesm ?_
    filter_upwards [hae_bad] with t ht
    have ht1 : t ≠ 2 * Real.pi / L := fun h => ht (by simp [h])
    have ht2 : t ≠ -(2 * Real.pi / L) := fun h => ht (by simp [h])
    have hpsi_lb : -archimedeanWeilConst ≤ psiArch t := by
      dsimp [psiArch]
      have : 0 ≤ ∑' n : ℕ, psiArchTerm t n := tsum_nonneg (psiArchTerm_nonneg t)
      linarith
    have hpsi_abs : |psiArch t| ≤ archimedeanWeilConst + t ^ 2 / 2 := by
      rw [abs_le]
      exact ⟨by linarith [sq_nonneg t], by linarith [psiArch_le_half_sq t, archimedeanWeilConst_gt_four]⟩
    have hM_ge : (t ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2 ≤ M t :=
      oddSinMode_t2_fourier_bound hL ht1 ht2
    have hM_nn : 0 ≤ M t := le_trans (mul_nonneg (by positivity) (sq_nonneg _)) hM_ge
    have hC_pos : 0 < archimedeanWeilConst := by linarith [archimedeanWeilConst_gt_four]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖compactFourier L (oddSinMode L) t‖)]
    have hstep1 : |psiArch t| * ‖compactFourier L (oddSinMode L) t‖ ^ 2 ≤
        archimedeanWeilConst * ‖compactFourier L (oddSinMode L) t‖ ^ 2 + M t := by
      calc |psiArch t| * ‖compactFourier L (oddSinMode L) t‖ ^ 2
        _ ≤ (archimedeanWeilConst + t ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hpsi_abs (sq_nonneg _)
        _ = archimedeanWeilConst * ‖compactFourier L (oddSinMode L) t‖ ^ 2 +
              (t ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2 := by ring
        _ ≤ archimedeanWeilConst * ‖compactFourier L (oddSinMode L) t‖ ^ 2 + M t := by linarith
    have hnorm_le : ‖compactFourier L (oddSinMode L) t‖ ^ 2 ≤
        (2 / a ^ 2) * M t + (Icc (-a) a).indicator (fun _ => L ^ 2 / 2) t := by
      by_cases hta : |t| ≤ a
      · have hmem : t ∈ Icc (-a) a := abs_le.mp hta
        rw [Set.indicator_of_mem hmem]
        have hpw := fourierTransform_norm_sq_le_L_mul_L2 (le_of_lt hL) (continuous_oddSinMode L) t
        rw [oddSinMode_L2_norm_sq hL] at hpw
        have hterm_nn : 0 ≤ (2 / a ^ 2) * M t := mul_nonneg (by positivity) hM_nn
        linarith
      · push Not at hta
        have hnot : t ∉ Icc (-a) a := fun hm => absurd (abs_le.mpr hm) (not_le.mpr hta)
        rw [Set.indicator_of_notMem hnot, add_zero]
        have ha2_lt : a ^ 2 < t ^ 2 := by
          have : a ^ 2 < |t| ^ 2 := sq_lt_sq' (by linarith) hta
          rwa [sq_abs] at this
        have h1 : (a ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2 ≤ M t :=
          le_trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) hM_ge
        have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / a ^ 2)
        have hcancel : (2 / a ^ 2) * ((a ^ 2 / 2) * ‖compactFourier L (oddSinMode L) t‖ ^ 2) =
            ‖compactFourier L (oddSinMode L) t‖ ^ 2 := by
          field_simp [ne_of_gt ha_pos]
        linarith
    dsimp [D]
    nlinarith
  have hint_le := integral_mono_ae hf_int hM_integrable hle_ae
  rw [hM_integral] at hint_le
  have hpi_gt3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_lt315 : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  have hdiv : (1 / (2 * Real.pi)) * (16 * Real.pi ^ 3 / L + 64 * Real.pi / (9 * L)) =
      (8 * Real.pi ^ 2 + 32 / 9) / L := by
    field_simp [ne_of_gt hL, Real.pi_ne_zero]; ring
  have hnum : 8 * Real.pi ^ 2 + 32 / 9 ≤ 90 := by nlinarith
  have hfinal : (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) ≤
      (1 / (2 * Real.pi)) * (16 * Real.pi ^ 3 / L + 64 * Real.pi / (9 * L)) :=
    mul_le_mul_of_nonneg_left hint_le (by positivity)
  rw [hdiv] at hfinal
  exact le_trans hfinal (div_le_div_of_nonneg_right hnum (le_of_lt hL))

/-- Finite prime-power truncation of the arithmetic Weil prime-shift functional up to `N_max : ℕ`. -/
noncomputable def weilPrimeTruncated (N_max : ℕ) (L : ℝ) (g : ℝ → ℂ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
    (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
      (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
        g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re

/-- Auxiliary norm bound on any finite prime-power truncation `weilPrimeTruncated N_max L g`:
    its Rayleigh quotient is uniformly bounded by a constant `M(N_max)` independent of `L`! -/
private lemma weilPrimeTruncated_abs_le (N_max : ℕ) {L : ℝ} (hL : 0 < L)
    {g : ℝ → ℂ} (hg : Continuous g) :
    |weilPrimeTruncated N_max L g| ≤
      (2 * ∑ n ∈ Finset.Icc 2 N_max, ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
  dsimp [weilPrimeTruncated]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htri : |∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| ≤
      ∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
          (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
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
    exact mul_le_mul_of_nonneg_left
      (shift_overlap_re_le_L2 hlog_nn hlog_le hg) hw_nn
  have hsub : Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))) ⊆ Finset.Icc 2 N_max := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 (min_le_left _ _)⟩
  have hL2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hmono_sum : ∑ n ∈ Finset.Icc 2 (min N_max (Nat.floor (Real.exp L))),
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 2 N_max,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
          (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)) hL2_nn
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hmono_sum
  rw [← Finset.sum_mul] at htri
  linarith

/-- THEOREM I.4 (ROUTE A FINITE-PRIME WALL / NO-GO THEOREM):
    For EVERY finite prime-power cutoff `N_max : ℕ` (no matter how large!), there exists an
    explicit horizon `L_0 > 0` such that for EVERY `L ≥ L_0`, the finite-prime truncated
    Weil functional evaluated on `oddSinMode L` is STRICTLY NEGATIVE:
      `W_pole(L, g_L) + W_∞(L, g_L) - W_{prime, ≤ N_max}(L, g_L) < 0`.
    Consequently, NO finite set of primes and NO bounded-norm perturbation of the Archimedean
    operator can ever sustain Weil positivity globally across all horizons `L > 0`. -/
theorem weilTruncated_finitePrimes_eventually_neg (N_max : ℕ) :
    ∃ L_0 : ℝ, 0 < L_0 ∧ ∀ L : ℝ, L_0 ≤ L →
      weilPole L (oddSinMode L) +
        (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L (oddSinMode L) t‖ ^ 2) -
        weilPrimeTruncated N_max L (oddSinMode L) < 0 := by
  set M : ℝ := 2 * ∑ n ∈ Finset.Icc 2 N_max, ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
  have hM_nn : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  -- For L ≥ 4π (so 4π^2 ≤ L^2/4 => L^2/4 + 4π^2 ≤ L^2/2),
  --   pole_RQ = 64π^2 L / (L^2/4 + 4π^2)^2 * sinh(L/4)^2 ≥ (256π^2 / L^3) * sinh(L/4)^2.
  -- Using sinh(x) = (e^x - e^{-x})/2 and e^x ≥ x^5/120 for x ≥ 0 (so for x ≥ 2, e^{-x} ≤ 1/4 ≤ e^x/2,
  --   sinh(x) ≥ e^x/4 ≥ x^5 / 480), we get sinh(L/4)^2 ≥ (L/4)^10 / 480^2, so pole_RQ ≥ c * L^7!
  -- Even simpler: pick L_0 = max 20 (100 * (M + 10)) and use e^{L/4} ≥ (L/4)^4 / 24!
  -- Wait: (L/4)^4 / 24 squared is L^8 / (256*24)^2 -> divided by L^3 gives L^5 / 3.8e7!
  -- Pick x = L/4 ≥ 100 => L ≥ 400; let's just check e^x - 1 ≥ x^4 / 24!
  -- Since sinh(x) = (e^x - e^{-x})/2 ≥ (e^x - 1)/2 ≥ (1 + x + x^2/2 + x^3/6 + x^4/24 - 1)/2 ≥ x^4/48 for x ≥ 0!
  -- Wait: for x ≥ 0, e^{-x} ≤ 1, so sinh(x) = (e^x - e^{-x})/2 ≥ (e^x - 1)/2 ≥ x^4 / 48! ZERO exponentials to invert!!
  -- Then for L ≥ 4π (L ≥ 13): (L^2/4 + 4π^2) ≤ L^2/2, so
  --   -W_pole / (L/2) = 64π^2 L / (L^2/4 + 4π^2)^2 * sinh(L/4)^2
  --                   ≥ (64 * 9 * L / (L^4 / 4)) * (L^4 / (256 * 48))^2
  --                   = (2304 / L^3) * (L^8 / 12288^2) = (2304 / 150994944) * L^5 = L^5 / 65536!
  -- Choose L_0 = max 100 (100 * M + 1000)! Then L_0 ≥ 100 => L^4 ≥ 10^8 > 65536 * 2 => L^5/65536 ≥ 2*L > M + 180/L^2!
  refine ⟨max 100 (M + 1000), by positivity, fun L hL_ge => ?_⟩
  have hL100 : (100 : ℝ) ≤ L := le_trans (le_max_left _ _) hL_ge
  have hLM : M + 1000 ≤ L := le_trans (le_max_right _ _) hL_ge
  have hL : 0 < L := by linarith
  have hpole := oddSinMode_weilPole_exact hL
  have harch := oddSinMode_weilArch_upper hL
  have hprime := weilPrimeTruncated_abs_le N_max hL (continuous_oddSinMode L)
  rw [oddSinMode_L2_norm_sq hL] at hprime
  have hprime_neg : -weilPrimeTruncated N_max L (oddSinMode L) ≤ M * (L / 2) := by
    have := (abs_le.mp hprime).1; linarith
  -- Lower bound sinh(L/4) ≥ (L/4)^4 / 48
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
  have hpi_gt3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_lt315 : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [hpi_gt3]
  have hden_le : L ^ 2 / 4 + 4 * Real.pi ^ 2 ≤ L ^ 2 / 2 := by nlinarith
  have hden_sq : (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2 ≤ (L ^ 2 / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hden_le 2
  -- Show 32 * π^2 * L^2 / (L^2/4 + 4π^2)^2 * sinh(L/4)^2 ≥ L^6 / 131072
  have hfrac_lb : 1152 / L ^ 2 ≤ 32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2 := by
    have h1 : 288 * L ^ 2 ≤ 32 * Real.pi ^ 2 * L ^ 2 := by nlinarith [sq_nonneg L, hpi2]
    have h2 : 288 * L ^ 2 / (L ^ 2 / 2) ^ 2 ≤ 32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2 :=
      div_le_div₀ (by positivity) h1 (by positivity) hden_sq
    have h3 : 1152 / L ^ 2 = 288 * L ^ 2 / (L ^ 2 / 2) ^ 2 := by
      field_simp [ne_of_gt hL]; ring
    linarith
  have hmag_lb : (1152 / L ^ 2) * ((L / 4) ^ 4 / 48) ^ 2 ≤
      (32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 :=
    mul_le_mul hfrac_lb hsinh_sq (by positivity) (by positivity)
  have hsimp_lb : (1152 / L ^ 2) * ((L / 4) ^ 4 / 48) ^ 2 = L ^ 6 / 131072 := by
    field_simp [ne_of_gt hL]; ring
  rw [hsimp_lb] at hmag_lb
  -- Since L ≥ 100, L^4 ≥ 10^8 > 131072 * 2, so L^6 / 131072 > L^2;
  -- and L ≥ M + 1000 => L^2 > M * (L/2) + 90 / L!
  have hL4_big : (262144 : ℝ) ≤ L ^ 4 := by
    have : (100 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL100 4
    norm_num at this; linarith
  have hL6_gt : 2 * L ^ 2 ≤ L ^ 6 / 131072 := by
    have h1 : 262144 * L ^ 2 ≤ L ^ 6 := by nlinarith [sq_nonneg L]
    linarith
  have h90_le : 90 / L ≤ 1 := by
    rw [div_le_one hL]; linarith
  have hM_lt : M * (L / 2) + 1 < 2 * L ^ 2 := by nlinarith
  linarith

/-- THEOREM I.5 (COROLLARY — EXPONENTIAL PRIME-CANCELLATION NECESSITY OF RH ON ROUTE A):
    For EVERY `L > 0`, if the full arithmetic Weil functional is non-negative on `oddSinMode L`
    (`0 ≤ weilTotal L (oddSinMode L)`), then the infinite `vonMangoldt` prime-shift operator MUST
    provide an exponentially growing negative cancellation (positive contribution `-W_prime`):
      `64 * π^2 * L / (L^2/4 + 4*π^2)^2 * sinh(L/4)^2 - 180 / L^2 ≤ -weilPrime L (oddSinMode L) / ‖oddSinMode L‖_2^2`. -/
theorem weilTotal_pos_forces_exponential_prime_cancellation {L : ℝ} (hL : 0 < L)
    (hpos : 0 ≤ weilTotal L (oddSinMode L)) :
    (64 * Real.pi ^ 2 * L / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 - 180 / L ^ 2 ≤
      -weilPrime L (oddSinMode L) / (∫ x in (-L / 2)..(L / 2), ‖oddSinMode L x‖ ^ 2) := by
  dsimp [weilTotal] at hpos
  rw [oddSinMode_weilPole_exact hL] at hpos
  have harch := oddSinMode_weilArch_upper hL
  have hL2 := oddSinMode_L2_norm_sq hL
  rw [hL2]
  have hraw : (32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 -
      90 / L ≤ -weilPrime L (oddSinMode L) := by linarith
  have hdiv := div_le_div_of_nonneg_right hraw (by positivity : 0 ≤ L / 2)
  have hlhs : ((32 * Real.pi ^ 2 * L ^ 2 / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 -
      90 / L) / (L / 2) =
      (64 * Real.pi ^ 2 * L / (L ^ 2 / 4 + 4 * Real.pi ^ 2) ^ 2) * Real.sinh (L / 4) ^ 2 - 180 / L ^ 2 := by
    have hden_ne : L ^ 2 / 4 + 4 * Real.pi ^ 2 ≠ 0 := by positivity
    field_simp [ne_of_gt hL, hden_ne]; ring
  linarith

-- ==============================================================================
-- PART II: ROUTE B — EXACT SCHUR-POTENTIAL MODULUS SYNTHESIS, DE BRANGES
--          BOUNDARY PHASE VELOCITY, & UNCONDITIONAL CORRIDOR CONTRACTION
-- ==============================================================================

/-- THEOREM II.1 (EXACT HERMITE-BIEHLER SCHUR MODULUS = TRANSVERSE POTENTIAL RATIO):
    For EVERY `α : ℝ`, `σ : ℝ`, `γ : ℝ`, the numerator and denominator of `xiSchur α (γ + iσ)`
    satisfy identically:
      `‖xiShiftE_sharp α (γ + iσ)‖^2 = xiNormSq |σ - α| γ`,
      `‖xiShiftE α (γ + iσ)‖^2 = xiNormSq (σ + α) γ`,
    and hence whenever `xiShiftE α (γ + iσ) ≠ 0`:
      `‖xiSchur α (γ + iσ)‖^2 = xiNormSq |σ - α| γ / xiNormSq (σ + α) γ`. -/
theorem xiSchur_norm_sq_eq_xiNormSq_ratio (α σ γ : ℝ) :
    ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 = xiNormSq |σ - α| γ ∧
    ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 = xiNormSq (σ + α) γ ∧
    (xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0 →
      ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 =
        xiNormSq |σ - α| γ / xiNormSq (σ + α) γ) := by
  have h1 : ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 = xiNormSq |σ - α| γ := by
    dsimp [xiShiftE_sharp, xiNormSq]
    have harg : ((1 / 2 + α : ℝ) : ℂ) + Complex.I * ((γ : ℂ) + Complex.I * (σ : ℂ)) =
        ⟨1 / 2 + (α - σ), γ⟩ := by
      apply Complex.ext
      · simp; ring
      · simp
    rw [harg]
    have hres : ‖riemannXi ⟨1 / 2 + (α - σ), γ⟩‖ ^ 2 = xiNormSq (α - σ) γ := rfl
    rw [hres]
    rcases le_total α σ with hle | hle
    · rw [abs_of_nonneg (by linarith : 0 ≤ σ - α)]
      have hneg : α - σ = -(σ - α) := by ring
      rw [hneg, xiNormSq_even_sigma]; rfl
    · rw [abs_of_nonpos (by linarith : σ - α ≤ 0)]
      have heq : -(σ - α) = α - σ := by ring
      rw [heq]; rfl
  have h2 : ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 = xiNormSq (σ + α) γ := by
    dsimp [xiShiftE]
    have harg : ((1 / 2 + α : ℝ) : ℂ) - Complex.I * ((γ : ℂ) + Complex.I * (σ : ℂ)) =
        ⟨1 / 2 + (σ + α), -γ⟩ := by
      apply Complex.ext
      · simp; ring
      · simp
    rw [harg]
    have hres : ‖riemannXi ⟨1 / 2 + (σ + α), -γ⟩‖ ^ 2 = xiNormSq (σ + α) (-γ) := rfl
    rw [hres]
    exact xiNormSq_even_gamma (σ + α) γ
  refine ⟨h1, h2, fun hne => ?_⟩
  dsimp [xiSchur]
  rw [norm_div, div_pow, h1, h2]

/-- THEOREM II.2 (EXACT GLOBAL BICONDITIONAL: ALL-α HERMITE-BIEHLER SCHUR CONTRACTION ↔
    STRICT TRANSVERSE POTENTIAL MONOTONICITY ON `[0, ∞)`, BOTH IMPLYING `RiemannHypothesis`):
    `(∀ α > 0, ∀ σ > 0, ∀ γ, ‖E_α^#(γ + iσ)‖ < ‖E_α(γ + iσ)‖)` is 100% logically equivalent to
    `(∀ γ : ℝ, StrictMonoOn (fun σ => xiNormSq σ γ) (Ici 0))`, and implies `RiemannHypothesis`. -/
theorem hermiteBiehler_all_iff_xiNormSq_strictMono_all :
    ((∀ α : ℝ, 0 < α → ∀ σ γ : ℝ, 0 < σ →
        ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ <
        ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖) ↔
     (∀ γ : ℝ, StrictMonoOn (fun σ : ℝ => xiNormSq σ γ) (Ici 0))) ∧
    ((∀ γ : ℝ, StrictMonoOn (fun σ : ℝ => xiNormSq σ γ) (Ici 0)) → RiemannHypothesis) := by
  have hiff : (∀ α : ℝ, 0 < α → ∀ σ γ : ℝ, 0 < σ →
      ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ <
      ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖) ↔
      (∀ γ : ℝ, StrictMonoOn (fun σ : ℝ => xiNormSq σ γ) (Ici 0)) := by
    constructor
    · intro hHB γ s₁ hs₁ s₂ hs₂ hlt
      -- Set α = (s₂ - s₁) / 2 > 0, σ = (s₂ + s₁) / 2 > 0: then σ + α = s₂ and |σ - α| = s₁!
      have hs1_nn : 0 ≤ s₁ := mem_Ici.mp hs₁
      set α : ℝ := (s₂ - s₁) / 2
      set σ : ℝ := (s₂ + s₁) / 2
      have hα : 0 < α := by dsimp [α]; linarith
      have hσ : 0 < σ := by dsimp [σ]; linarith
      have hlt_norm := hHB α hα σ γ hσ
      have hsq : ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 <
          ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 :=
        pow_lt_pow_left₀ hlt_norm (norm_nonneg _) (by norm_num)
      have hrat := xiSchur_norm_sq_eq_xiNormSq_ratio α σ γ
      rw [hrat.1, hrat.2.1] at hsq
      have heq1 : |σ - α| = s₁ := by
        dsimp [α, σ]
        have : (s₂ + s₁) / 2 - (s₂ - s₁) / 2 = s₁ := by ring
        rw [this, abs_of_nonneg hs1_nn]
      have heq2 : σ + α = s₂ := by dsimp [α, σ]; ring
      rw [heq1, heq2] at hsq
      exact hsq
    · intro hmono α hα σ γ hσ
      have hrat := xiSchur_norm_sq_eq_xiNormSq_ratio α σ γ
      have hlt_arg : |σ - α| < σ + α := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hsq : xiNormSq |σ - α| γ < xiNormSq (σ + α) γ :=
        hmono γ (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (by linarith)) hlt_arg
      rw [← hrat.1, ← hrat.2.1] at hsq
      nlinarith [norm_nonneg (xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))),
                 norm_nonneg (xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)))]
  refine ⟨hiff, fun hmono => ?_⟩
  have hHB := hiff.mpr hmono
  exact riemannHypothesis_of_hermiteBiehler_all (fun α hα _ σ γ hσ => hHB α hα σ γ hσ)

/-- THEOREM II.3 (EXACT 7-LEVEL DE BRANGES BOUNDARY PHASE-VELOCITY IDENTITY ON `ℝ`):
    For EVERY `α : ℝ` and `γ : ℝ` with `xiShiftE α (γ : ℂ) ≠ 0`, the complex logarithmic
    derivative of `xiSchur α` along the real boundary `ℝ` is PURELY IMAGINARY and equals
    identically `i * (2 * Im R_ξ(γ + iα)) = i * ∂_σ log V(α, γ)`:
      `logDeriv (xiSchur α) γ = i * (2 * (xiResolvent (γ + i*α)).im) = i * xiLogForce α γ`. -/
theorem xiSchur_boundary_logDeriv_eq_I_mul_logForce {α γ : ℝ}
    (hE : xiShiftE α (γ : ℂ) ≠ 0) :
    logDeriv (xiSchur α) (γ : ℂ) =
      Complex.I * ((2 * (xiResolvent ((γ : ℂ) + Complex.I * (α : ℂ))).im : ℝ) : ℂ) ∧
    logDeriv (xiSchur α) (γ : ℂ) = Complex.I * ((xiLogForce α γ : ℝ) : ℂ) := by
  set w : ℂ := ((1 / 2 + α : ℝ) : ℂ) + Complex.I * (γ : ℂ)
  have hw_conj : starRingEnd ℂ w = ((1 / 2 + α : ℝ) : ℂ) - Complex.I * (γ : ℂ) := by
    dsimp [w]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hE_eq : xiShiftE α (γ : ℂ) = riemannXi (starRingEnd ℂ w) := by
    dsimp [xiShiftE]; rw [hw_conj]
  have hEs_eq : xiShiftE_sharp α (γ : ℂ) = riemannXi w := rfl
  have hxi_w_ne : riemannXi w ≠ 0 := by
    intro h0
    apply hE
    rw [hE_eq, riemannXi_conj, h0, map_zero]
  -- Exact complex derivatives of E_α and E_α^# at γ
  have hd_Es : HasDerivAt (xiShiftE_sharp α) (Complex.I * deriv riemannXi w) (γ : ℂ) := by
    have harg : HasDerivAt (fun z : ℂ => ((1 / 2 + α : ℝ) : ℂ) + Complex.I * z) Complex.I (γ : ℂ) := by
      simpa using (hasDerivAt_const (γ : ℂ) (((1 / 2 + α : ℝ) : ℂ))).fun_add
        ((hasDerivAt_id' (γ : ℂ)).const_mul Complex.I)
    have hcomp := (riemannXi_entire.differentiableAt (x := w)).hasDerivAt.comp (γ : ℂ) harg
    exact hcomp.congr_deriv (by ring)
  have hd_E : HasDerivAt (xiShiftE α) (-Complex.I * deriv riemannXi (starRingEnd ℂ w)) (γ : ℂ) := by
    have harg : HasDerivAt (fun z : ℂ => ((1 / 2 + α : ℝ) : ℂ) - Complex.I * z) (-Complex.I) (γ : ℂ) := by
      simpa using (hasDerivAt_const (γ : ℂ) (((1 / 2 + α : ℝ) : ℂ))).fun_sub
        ((hasDerivAt_id' (γ : ℂ)).const_mul Complex.I)
    have hcomp := (riemannXi_entire.differentiableAt
      (x := ((1 / 2 + α : ℝ) : ℂ) - Complex.I * (γ : ℂ))).hasDerivAt.comp (γ : ℂ) harg
    have hpt : ((1 / 2 + α : ℝ) : ℂ) - Complex.I * (γ : ℂ) = starRingEnd ℂ w := hw_conj.symm
    rw [hpt] at hcomp
    exact hcomp.congr_deriv (by ring)
  -- Schwarz reflection of `deriv riemannXi`: `deriv riemannXi (conj w) = conj (deriv riemannXi w)`
  have hderiv_conj : deriv riemannXi (starRingEnd ℂ w) = starRingEnd ℂ (deriv riemannXi w) := by
    have h1 := hasDerivAt_iff_tendsto_slope_zero.mp (riemannXi_entire.differentiableAt (x := w)).hasDerivAt
    have h2 := hasDerivAt_iff_tendsto_slope_zero.mp
      (riemannXi_entire.differentiableAt (x := starRingEnd ℂ w)).hasDerivAt
    -- Restrict along real step t → 0:
    have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Complex.ofReal_ne_zero.mpr ht
    have h1r := (Complex.continuous_conj.tendsto (deriv riemannXi w)).comp (h1.comp hreal)
    have h2r := h2.comp hreal
    simp only [Function.comp_def] at h1r h2r
    have hfun_eq : (fun t : ℝ => (starRingEnd ℂ) ((t : ℂ)⁻¹ • (riemannXi (w + (t : ℂ)) - riemannXi w))) =
        (fun t : ℝ => (t : ℂ)⁻¹ • (riemannXi (starRingEnd ℂ w + (t : ℂ)) - riemannXi (starRingEnd ℂ w))) := by
      ext t
      simp only [smul_eq_mul, map_mul, map_inv₀, map_sub, Complex.conj_ofReal, ← riemannXi_conj, map_add]
    rw [hfun_eq] at h1r
    exact tendsto_nhds_unique h2r h1r
  -- Compute logDeriv (xiSchur α) γ via quotient rule `HasDerivAt.fun_div`
  have hd_S := hd_Es.fun_div hd_E hE
  have hlogS : logDeriv (xiSchur α) (γ : ℂ) =
      Complex.I * (deriv riemannXi w / riemannXi w + starRingEnd ℂ (deriv riemannXi w / riemannXi w)) := by
    rw [logDeriv_apply]
    have hfn : xiSchur α = fun z => xiShiftE_sharp α z / xiShiftE α z := rfl
    rw [hfn, hd_S.deriv]
    dsimp only
    rw [hE_eq, hEs_eq, hderiv_conj, riemannXi_conj, map_div₀]
    have hconj_ne : starRingEnd ℂ (riemannXi w) ≠ 0 :=
      fun h => hxi_w_ne ((map_eq_zero (starRingEnd ℂ)).mp h)
    have halg : ∀ a b c d : ℂ, a ≠ 0 → c ≠ 0 →
        ((Complex.I * b * c - a * (-Complex.I * d)) / c ^ 2) / (a / c) =
          Complex.I * (b / a + d / c) := by
      intro a b c d ha hc
      field_simp [ha, hc]
      ring
    exact halg (riemannXi w) (deriv riemannXi w) (starRingEnd ℂ (riemannXi w))
      (starRingEnd ℂ (deriv riemannXi w)) hxi_w_ne hconj_ne
  -- Connect `L + conj L = 2 * Re L = 2 * Im R_ξ(γ + iα) = xiLogForce α γ`
  have hR := xiResolvent_im_eq_logForce_half hxi_w_ne
  have hadd_conj : deriv riemannXi w / riemannXi w + starRingEnd ℂ (deriv riemannXi w / riemannXi w) =
      ((2 * (deriv riemannXi w / riemannXi w).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  have hpart1 : logDeriv (xiSchur α) (γ : ℂ) =
      Complex.I * ((2 * (xiResolvent ((γ : ℂ) + Complex.I * (α : ℂ))).im : ℝ) : ℂ) := by
    rw [hlogS, hadd_conj, hR.1]
  have hpart2 : logDeriv (xiSchur α) (γ : ℂ) = Complex.I * ((xiLogForce α γ : ℝ) : ℂ) := by
    rw [hpart1]
    congr 1
    exact_mod_cast (by linarith [hR.2] : 2 * (xiResolvent ((γ : ℂ) + Complex.I * (α : ℂ))).im = xiLogForce α γ)
  exact ⟨hpart1, hpart2⟩

/-- THEOREM II.4 (UNCONDITIONAL CONSTRUCTIVE CORRIDOR HERGLOTZ POSITIVITY, SCHUR CONTRACTION,
    AND POSITIVE DE BRANGES BOUNDARY PHASE VELOCITY ON `|γ| ≤ 2`):
    Directly from Module #11's explicit convexity corridor (`xiNormSq_deriv1_pos_corridor_two`),
    for EVERY `γ : ℝ` with `|γ| ≤ 2`:
    (1) `0 < (xiResolvent (γ + iσ)).im` for every `σ ∈ (0, 1/2]` (Herglotz positivity),
    (2) `‖xiSchur α (γ + iσ)‖ < 1` for every `α > 0, σ > 0` with `α + σ ≤ 1/2` (Schur contraction),
    (3) `0 < (logDeriv (xiSchur α) γ).im` for every `α ∈ (0, 1/2]` (monotone boundary phase). -/
theorem xiResolvent_herglotz_and_schur_contraction_on_corridor_two {γ : ℝ} (hγ : |γ| ≤ 2) :
    (∀ σ : ℝ, 0 < σ → σ ≤ 1 / 2 → 0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im) ∧
    (∀ α σ : ℝ, 0 < α → 0 < σ → α + σ ≤ 1 / 2 →
      ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ < 1) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 2 → 0 < (logDeriv (xiSchur α) (γ : ℂ)).im) := by
  -- First prove V(s, γ) is strictly increasing on [0, 1/2] and strictly positive on [0, 1/2]!
  have hdiffV : Differentiable ℝ (fun s : ℝ => xiNormSq s γ) :=
    fun s => (hasDerivAt_xiNormSq_sigma s γ).differentiableAt
  have hV_mono : StrictMonoOn (fun s : ℝ => xiNormSq s γ) (Icc 0 (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2)) hdiffV.continuous.continuousOn
    intro s hs
    rw [interior_Icc] at hs
    exact xiNormSq_deriv1_pos_corridor_two hs.1 (le_of_lt hs.2) hγ
  have hV0_pos : 0 < xiNormSq 0 γ := by
    have hxi0 : 0 < xiCritical γ :=
      riemannXi_critical_pos_corridor_four (by linarith [abs_nonneg γ])
    have hne : riemannXi ⟨1 / 2 + 0, γ⟩ ≠ 0 := by
      intro h0
      have harg : (⟨1 / 2 + 0, γ⟩ : ℂ) = ⟨1 / 2, γ⟩ := by apply Complex.ext <;> simp
      rw [harg] at h0
      dsimp [xiCritical] at hxi0
      rw [h0, Complex.zero_re] at hxi0
      linarith
    dsimp [xiNormSq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hV_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 0 < xiNormSq s γ := by
    intro s hs0 hs1
    rcases eq_or_lt_of_le hs0 with rfl | hs_pos
    · exact hV0_pos
    · exact lt_trans hV0_pos (hV_mono (Set.left_mem_Icc.mpr (by norm_num)) ⟨hs0, hs1⟩ hs_pos)
  have hxi_ne : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      riemannXi (((1 / 2 + s : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
    intro s hs0 hs1 h0
    have hp := hV_pos s hs0 hs1
    dsimp [xiNormSq] at hp
    have harg : (⟨1 / 2 + s, γ⟩ : ℂ) = ((1 / 2 + s : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
      apply Complex.ext <;> simp
    rw [harg, h0, norm_zero] at hp
    norm_num at hp
  have hR_pos : ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 2 →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
    intro σ hσ0 hσ1
    have hR := xiResolvent_im_eq_logForce_half (hxi_ne σ (le_of_lt hσ0) hσ1)
    have hlf := xiLogForce_eq_force_div_normSq (hV_pos σ (le_of_lt hσ0) hσ1)
    have hd1 := xiNormSq_deriv1_pos_corridor_two hσ0 hσ1 hγ
    have hlf_pos : 0 < xiLogForce σ γ := by
      rw [hlf]; exact div_pos hd1 (hV_pos σ (le_of_lt hσ0) hσ1)
    linarith [hR.2]
  refine ⟨hR_pos, ?_, ?_⟩
  · intro α σ hα hσ hsum
    have hrat := xiSchur_norm_sq_eq_xiNormSq_ratio α σ γ
    have hE_ne : xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0 := by
      intro h0
      have hp := hV_pos (σ + α) (by linarith) (by linarith)
      rw [← hrat.2.1, h0, norm_zero] at hp
      norm_num at hp
    have hsq_eq := hrat.2.2 hE_ne
    have habs_le : |σ - α| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have habs_lt : |σ - α| < σ + α := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hV_lt : xiNormSq |σ - α| γ < xiNormSq (σ + α) γ :=
      hV_mono ⟨abs_nonneg _, habs_le⟩ ⟨by linarith, by linarith⟩ habs_lt
    have hV_den : 0 < xiNormSq (σ + α) γ := hV_pos (σ + α) (by linarith) (by linarith)
    have hsq_lt : ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 < 1 := by
      rw [hsq_eq, div_lt_one hV_den]; exact hV_lt
    nlinarith [norm_nonneg (xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ)))]
  · intro α hα0 hα1
    have hE_ne : xiShiftE α (γ : ℂ) ≠ 0 := by
      have hne := hxi_ne α (le_of_lt hα0) hα1
      intro h0
      apply hne
      dsimp [xiShiftE] at h0
      have hc : starRingEnd ℂ (((1 / 2 + α : ℝ) : ℂ) - Complex.I * (γ : ℂ)) =
          ((1 / 2 + α : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
        simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
      rw [← hc, riemannXi_conj, h0, map_zero]
    have hbd := (xiSchur_boundary_logDeriv_eq_I_mul_logForce hE_ne).1
    rw [hbd]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
               zero_mul, one_mul]
    have := hR_pos α hα0 hα1
    linarith

-- ==============================================================================
-- PART III: ROUTE B — EXACT LOG-CONCAVE DECREASING KERNEL WALL THEOREM
--           (STRICTLY STRONGER THAN SCHOENBERG COMPLETE-MONOTONICITY NO-GO)
-- ==============================================================================

/-- Explicit elementary Route B wall kernel `K_wall(u) = (5 + 2u^2 + u^4) * exp(-u^2)`. -/
noncomputable def wallKernel (u : ℝ) : ℝ :=
  (5 + 2 * u ^ 2 + u ^ 4) * Real.exp (-u ^ 2)

/-- Closed-form Fourier-Laplace transform of `wallKernel`:
    `F_wall(z) = √π * exp(-z^2 / 4) * (z^4 / 16 - 5 * z^2 / 4 + 27 / 4)`. -/
noncomputable def wallTransform (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2 / 4) * (z ^ 4 / 16 - 5 * z ^ 2 / 4 + 27 / 4)

/-- Real restriction of `wallTransform` along `ℝ`. -/
noncomputable def wallTransformReal (x : ℝ) : ℝ :=
  Real.sqrt Real.pi * Real.exp (-x ^ 2 / 4) * (x ^ 4 / 16 - 5 * x ^ 2 / 4 + 27 / 4)

/-- THEOREM III.1A (STRICT POSITIVITY, EVENNESS, STRICT MONOTONICITY, AND STRICT
    LOG-CONCAVITY OF `wallKernel` ON ALL OF `ℝ`):
    `K_wall(u) = (5 + 2u^2 + u^4) * exp(-u^2)` simultaneously satisfies:
    (1) `0 < wallKernel u` for all `u : ℝ`,
    (2) `wallKernel (-u) = wallKernel u` for all `u : ℝ`,
    (3) `StrictAntiOn wallKernel (Ici 0)` (strictly decreasing on `[0, ∞)`),
    (4) `deriv (deriv (fun u => Real.log (wallKernel u))) u < 0` for ALL `u : ℝ` (strictly log-concave!). -/
theorem wallKernel_pos_even_antitone_logConcave :
    (∀ u : ℝ, 0 < wallKernel u) ∧
    (∀ u : ℝ, wallKernel (-u) = wallKernel u) ∧
    StrictAntiOn wallKernel (Ici 0) ∧
    (∀ u : ℝ, deriv (deriv (fun t : ℝ => Real.log (wallKernel t))) u < 0) := by
  have hpoly_pos : ∀ u : ℝ, 0 < 5 + 2 * u ^ 2 + u ^ 4 := fun u => by positivity
  have hpos : ∀ u : ℝ, 0 < wallKernel u := fun u =>
    mul_pos (hpoly_pos u) (Real.exp_pos _)
  have heven : ∀ u : ℝ, wallKernel (-u) = wallKernel u := fun u => by
    dsimp [wallKernel]; ring_nf
  -- Exact derivative K'(u) = -2*u*(3 + u^4) * exp(-u^2) < 0 on (0, ∞)
  have hderivK : ∀ u : ℝ, HasDerivAt wallKernel (-2 * u * (3 + u ^ 4) * Real.exp (-u ^ 2)) u := by
    intro u
    have hp : HasDerivAt (fun t : ℝ => 5 + 2 * t ^ 2 + t ^ 4) (4 * u + 4 * u ^ 3) u := by
      have h1 := ((hasDerivAt_const u (5 : ℝ)).fun_add ((hasDerivAt_pow 2 u).const_mul 2)).fun_add (hasDerivAt_pow 4 u)
      exact h1.congr_deriv (by norm_num; ring)
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2)) (-2 * u * Real.exp (-u ^ 2)) u := by
      have h1 := (hasDerivAt_pow 2 u).neg.exp
      exact h1.congr_deriv (by norm_num; ring)
    exact (hp.fun_mul he).congr_deriv (by ring)
  have hanti : StrictAntiOn wallKernel (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact fun u _ => (hderivK u).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      rw [(hderivK u).deriv]
      have h1 : 0 < 2 * u * (3 + u ^ 4) * Real.exp (-u ^ 2) := by
        have hpos_u : 0 < u := hu
        have hpos_e : 0 < Real.exp (-u ^ 2) := Real.exp_pos _
        positivity
      linarith
  -- Strict log-concavity: (log K_wall)''(u) < 0 for ALL u : ℝ!
  have hlog_d1 : ∀ u : ℝ, HasDerivAt (fun t : ℝ => Real.log (wallKernel t))
      ((4 * u + 4 * u ^ 3) / (5 + 2 * u ^ 2 + u ^ 4) - 2 * u) u := by
    intro u
    have hlog_eq : (fun t : ℝ => Real.log (wallKernel t)) =
        fun t => Real.log (5 + 2 * t ^ 2 + t ^ 4) - t ^ 2 := by
      ext t
      dsimp [wallKernel]
      rw [Real.log_mul (ne_of_gt (hpoly_pos t)) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      ring
    rw [hlog_eq]
    have hp : HasDerivAt (fun t : ℝ => 5 + 2 * t ^ 2 + t ^ 4) (4 * u + 4 * u ^ 3) u := by
      have h1 := ((hasDerivAt_const u (5 : ℝ)).fun_add ((hasDerivAt_pow 2 u).const_mul 2)).fun_add (hasDerivAt_pow 4 u)
      exact h1.congr_deriv (by norm_num; ring)
    have h1 := hp.log (ne_of_gt (hpoly_pos u))
    have h2 := hasDerivAt_pow 2 u
    exact (h1.fun_sub h2).congr_deriv (by simp)
  have hlog_conc : ∀ u : ℝ, deriv (deriv (fun t : ℝ => Real.log (wallKernel t))) u < 0 := by
    intro u
    have hderiv_fn : deriv (fun t : ℝ => Real.log (wallKernel t)) =
        fun t => (4 * t + 4 * t ^ 3) / (5 + 2 * t ^ 2 + t ^ 4) - 2 * t := by
      ext t; exact (hlog_d1 t).deriv
    rw [hderiv_fn]
    have hn : HasDerivAt (fun t : ℝ => 4 * t + 4 * t ^ 3) (4 + 12 * u ^ 2) u := by
      have h1 := ((hasDerivAt_id' u).const_mul 4).fun_add ((hasDerivAt_pow 3 u).const_mul 4)
      exact h1.congr_deriv (by norm_num; ring)
    have hd : HasDerivAt (fun t : ℝ => 5 + 2 * t ^ 2 + t ^ 4) (4 * u + 4 * u ^ 3) u := by
      have h1 := ((hasDerivAt_const u (5 : ℝ)).fun_add ((hasDerivAt_pow 2 u).const_mul 2)).fun_add (hasDerivAt_pow 4 u)
      exact h1.congr_deriv (by norm_num; ring)
    have hq := (hn.fun_div hd (ne_of_gt (hpoly_pos u))).fun_sub ((hasDerivAt_id' u).const_mul 2)
    rw [hq.deriv]
    have hden_pos : 0 < (5 + 2 * u ^ 2 + u ^ 4) ^ 2 := by positivity
    have hnum_eq : ((4 + 12 * u ^ 2) * (5 + 2 * u ^ 2 + u ^ 4) -
        (4 * u + 4 * u ^ 3) * (4 * u + 4 * u ^ 3)) / (5 + 2 * u ^ 2 + u ^ 4) ^ 2 - 2 * 1 =
        (-30 + 12 * u ^ 2 - 32 * u ^ 4 - 12 * u ^ 6 - 2 * u ^ 8) / (5 + 2 * u ^ 2 + u ^ 4) ^ 2 := by
      field_simp [ne_of_gt (hpoly_pos u)]; ring
    rw [hnum_eq]
    have hnum_neg : -30 + 12 * u ^ 2 - 32 * u ^ 4 - 12 * u ^ 6 - 2 * u ^ 8 < 0 := by
      -- -30 + 12 x - 32 x^2 = -28 - 2*(1 - 3x)^2 - 14 x^2 ≤ -28 < 0!
      have hsq1 : 0 ≤ (1 - 3 * u ^ 2) ^ 2 := sq_nonneg _
      have hsq2 : 0 ≤ u ^ 4 := by positivity
      have hsq3 : 0 ≤ u ^ 6 := by positivity
      have hsq4 : 0 ≤ u ^ 8 := by positivity
      nlinarith
    exact div_neg_of_neg_of_pos hnum_neg hden_pos
  exact ⟨hpos, heven, hanti, hlog_conc⟩

/-- THEOREM III.1B (ALL-ORDER HANKEL POSITIVITY OF `wallKernel`):
    Every moment `∫ u in Ioi 0, u^(2k) * K_wall(u) du` is strictly positive and EVERY
    order-`N` Hankel matrix `H_{ij} = M_{i+j}` of `K_wall` is positive semi-definite. -/
theorem wallKernel_hankel_psd (N : ℕ) (c : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      c i * c j * (∫ u in Ioi (0 : ℝ), u ^ (2 * (i.val + j.val)) * wallKernel u) := by
  have hint : ∀ k : ℕ, IntegrableOn (fun u : ℝ => u ^ (2 * k) * wallKernel u) (Ioi (0 : ℝ)) := by
    intro k
    have hmem : Integrable (fun u : ℝ => u ^ (2 * k) * wallKernel u) := by
      have heq : (fun u : ℝ => u ^ (2 * k) * wallKernel u) =
          fun u => 5 * (u ^ (2 * k) * Real.exp (-u ^ 2)) +
            2 * (u ^ (2 * k + 2) * Real.exp (-u ^ 2)) +
            (u ^ (2 * k + 4) * Real.exp (-u ^ 2)) := by
        ext u; dsimp [wallKernel]; ring
      rw [heq]
      have hpow_exp : ∀ m : ℕ, Integrable (fun u : ℝ => u ^ m * Real.exp (-u ^ 2)) := by
        intro m
        have h1 : Integrable (fun u : ℝ => |u| ^ m * Real.exp (-1 * u ^ 2)) := by
          have hm : (-1 : ℝ) < (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m]
          have hg := integrableOn_rpow_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num) hm
          have hpos : IntegrableOn (fun u : ℝ => u ^ m * Real.exp (-1 * u ^ 2)) (Ioi 0) := by
            refine hg.congr_fun (fun u _ => ?_) measurableSet_Ioi
            dsimp only
            rw [Real.rpow_natCast]
          have hneg : IntegrableOn (fun u : ℝ => (-u) ^ m * Real.exp (-1 * u ^ 2)) (Iio 0) := by
            have hc := hpos.comp_neg
            have hpre : -Ioi (0 : ℝ) = Iio 0 := by ext t; simp
            rw [hpre] at hc
            refine hc.congr_fun (fun u _ => ?_) measurableSet_Iio
            simp
          have hi1 := (integrable_indicator_iff measurableSet_Ioi).mpr hpos
          have hi2 := (integrable_indicator_iff measurableSet_Iio).mpr hneg
          refine (hi1.add hi2).congr ?_
          have hzero : volume ({0} : Set ℝ) = 0 := Set.Countable.measure_zero (Set.to_countable _) volume
          have hae0 : ∀ᵐ u : ℝ, u ∉ ({0} : Set ℝ) := by rw [ae_iff]; simp [hzero]
          filter_upwards [hae0] with u hu
          have hne : u ≠ 0 := fun h => hu (by simp [h])
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hm1 : u ∉ Ioi (0 : ℝ) := by simp; linarith
            have hm2 : u ∈ Iio (0 : ℝ) := hlt
            simp [hm1, hm2, abs_of_neg hlt]
          · have hm1 : u ∈ Ioi (0 : ℝ) := hgt
            have hm2 : u ∉ Iio (0 : ℝ) := by simp; linarith
            simp [hm1, hm2, abs_of_pos hgt]
        refine h1.mono' (by fun_prop) (ae_of_all _ fun u => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
        simp
      exact (((hpow_exp (2 * k)).const_mul 5).add ((hpow_exp (2 * k + 2)).const_mul 2)).add
        (hpow_exp (2 * k + 4))
    exact hmem.integrableOn
  -- Rewrite double sum as ∫_{Ioi 0} (∑_i c_i u^{2i})^2 * wallKernel u ≥ 0!
  have hsum_eq : ∑ i : Fin N, ∑ j : Fin N,
      c i * c j * (∫ u in Ioi (0 : ℝ), u ^ (2 * (i.val + j.val)) * wallKernel u) =
      ∫ u in Ioi (0 : ℝ), (∑ i : Fin N, c i * u ^ (2 * i.val)) ^ 2 * wallKernel u := by
    have hpt : ∀ u : ℝ, (∑ i : Fin N, c i * u ^ (2 * i.val)) ^ 2 * wallKernel u =
        ∑ i : Fin N, ∑ j : Fin N, c i * c j * (u ^ (2 * (i.val + j.val)) * wallKernel u) := by
      intro u
      rw [sq, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_add, pow_add]; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hint (i.val + j.val)).const_mul (c i * c j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint (i.val + j.val)).const_mul (c i * c j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  rw [hsum_eq]
  exact setIntegral_nonneg measurableSet_Ioi fun u _ =>
    mul_nonneg (sq_nonneg _) (le_of_lt (wallKernel_pos_even_antitone_logConcave.1 u))

/-- Auxiliary integrability and vanishing at `±∞` of `u^m * cexp(-u^2 + i*z*u)`. -/
private lemma integrable_pow_cexp_gauss (z : ℂ) (m : ℕ) :
    Integrable (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ))) := by
  have hnorm_bound : ∀ u : ℝ,
      ‖(u : ℂ) ^ m * Complex.exp (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ))‖ ≤
        Real.exp (|z.im| ^ 2 / 2) * (|u| ^ m * Real.exp (-(1 / 2 : ℝ) * u ^ 2)) := by
    intro u
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ)).re = -u ^ 2 - z.im * u := by
      simp [sq, Complex.mul_re, Complex.mul_im]; ring
    rw [hre]
    have hexp_le : -u ^ 2 - z.im * u ≤ |z.im| ^ 2 / 2 + (-(1 / 2 : ℝ) * u ^ 2) := by
      have h2 : -z.im * u ≤ |z.im| * |u| := by
        have := neg_le_abs (z.im * u)
        rw [abs_mul] at this; linarith
      nlinarith [sq_nonneg (|u| - |z.im|), sq_abs u]
    have he := Real.exp_le_exp.mpr hexp_le
    rw [Real.exp_add] at he
    have := mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg u) m)
    linarith
  have hdom : Integrable (fun u : ℝ => Real.exp (|z.im| ^ 2 / 2) * (|u| ^ m * Real.exp (-(1 / 2 : ℝ) * u ^ 2))) := by
    have hm : (-1 : ℝ) < (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hg := integrableOn_rpow_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num) hm
    have hpos : IntegrableOn (fun u : ℝ => u ^ m * Real.exp (-(1 / 2 : ℝ) * u ^ 2)) (Ioi 0) := by
      refine hg.congr_fun (fun u _ => ?_) measurableSet_Ioi
      dsimp only
      rw [Real.rpow_natCast]
    have hneg : IntegrableOn (fun u : ℝ => (-u) ^ m * Real.exp (-(1 / 2 : ℝ) * u ^ 2)) (Iio 0) := by
      have hc := hpos.comp_neg
      have hpre : -Ioi (0 : ℝ) = Iio 0 := by ext t; simp
      rw [hpre] at hc
      refine hc.congr_fun (fun u _ => ?_) measurableSet_Iio
      simp
    have hi1 := (integrable_indicator_iff measurableSet_Ioi).mpr hpos
    have hi2 := (integrable_indicator_iff measurableSet_Iio).mpr hneg
    have hbase : Integrable (fun u : ℝ => |u| ^ m * Real.exp (-(1 / 2 : ℝ) * u ^ 2)) := by
      refine (hi1.add hi2).congr ?_
      have hzero : volume ({0} : Set ℝ) = 0 := Set.Countable.measure_zero (Set.to_countable _) volume
      have hae0 : ∀ᵐ u : ℝ, u ∉ ({0} : Set ℝ) := by rw [ae_iff]; simp [hzero]
      filter_upwards [hae0] with u hu
      have hne : u ≠ 0 := fun h => hu (by simp [h])
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hm1 : u ∉ Ioi (0 : ℝ) := by simp; linarith
        have hm2 : u ∈ Iio (0 : ℝ) := hlt
        simp [hm1, hm2, abs_of_neg hlt]
      · have hm1 : u ∈ Ioi (0 : ℝ) := hgt
        have hm2 : u ∉ Iio (0 : ℝ) := by simp; linarith
        simp [hm1, hm2, abs_of_pos hgt]
    exact hbase.const_mul _
  exact hdom.mono' (by fun_prop) (ae_of_all _ hnorm_bound)

private lemma tendsto_pow_cexp_gauss_zero (z : ℂ) (m : ℕ) :
    Tendsto (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ))) atTop (𝓝 0) ∧
    Tendsto (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ))) atBot (𝓝 0) := by
  have hnorm_tend : ∀ l : Filter ℝ, Tendsto (fun u : ℝ => |u|) l atTop →
      Tendsto (fun u : ℝ => (u : ℂ) ^ m * Complex.exp (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ))) l (𝓝 0) := by
    intro l hl
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero_norm'
      (a := fun u : ℝ => Real.exp (|z.im| ^ 2 / 2) * (|u| ^ m * Real.exp (-(1 / 2 : ℝ) * |u| ^ 2)))
      (Filter.Eventually.of_forall fun u => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_exp]
      have hre : (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ)).re = -u ^ 2 - z.im * u := by
        simp [sq, Complex.mul_re, Complex.mul_im]; ring
      rw [hre, sq_abs u]
      have hexp_le : -u ^ 2 - z.im * u ≤ |z.im| ^ 2 / 2 + (-(1 / 2 : ℝ) * u ^ 2) := by
        have h2 : -z.im * u ≤ |z.im| * |u| := by
          have := neg_le_abs (z.im * u); rw [abs_mul] at this; linarith
        nlinarith [sq_nonneg (|u| - |z.im|), sq_abs u]
      have he := Real.exp_le_exp.mpr hexp_le
      rw [Real.exp_add] at he
      have := mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg u) m)
      linarith
    · have hbase : Tendsto (fun r : ℝ => r ^ m * Real.exp (-(1 / 2 : ℝ) * r)) atTop (𝓝 0) := by
        have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
        have hcomp := h.comp (tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
        have hmul := hcomp.const_mul ((2 : ℝ) ^ m)
        simp only [mul_zero] at hmul
        refine hmul.congr fun r => ?_
        dsimp
        rw [mul_pow]
        have : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
        have harg : -((1 / 2 : ℝ) * r) = -(1 / 2 : ℝ) * r := by ring
        rw [harg]; linear_combination (r ^ m * Real.exp (-(1 / 2 : ℝ) * r)) * this
      have hsq_le : ∀ᶠ r : ℝ in atTop, r ^ m * Real.exp (-(1 / 2 : ℝ) * r ^ 2) ≤ r ^ m * Real.exp (-(1 / 2 : ℝ) * r) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith
      have hsq_t : Tendsto (fun r : ℝ => r ^ m * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) atTop (𝓝 0) :=
        squeeze_zero' (eventually_atTop.mpr ⟨0, fun r hr => by positivity⟩) hsq_le hbase
      have hfin := (hsq_t.comp hl).const_mul (Real.exp (|z.im| ^ 2 / 2))
      simpa using hfin
  exact ⟨hnorm_tend atTop (tendsto_abs_atTop_atTop), hnorm_tend atBot (tendsto_abs_atBot_atTop)⟩

/-- THEOREM III.2 (EXACT CLOSED-FORM FOURIER-LAPLACE TRANSFORM OF `wallKernel`):
    For EVERY `z : ℂ`:
      `∫ u : ℝ, (wallKernel u : ℂ) * Complex.exp (Complex.I * z * u) = wallTransform z`. -/
theorem wallKernel_fourierLaplace_exact (z : ℂ) :
    ∫ u : ℝ, ((wallKernel u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ)) =
      wallTransform z := by
  let E : ℝ → ℂ := fun u => Complex.exp (-((u : ℂ) ^ 2) + Complex.I * z * (u : ℂ))
  -- Step 0: Base Gaussian integral I_0 = ∫ E(u) du = √π * exp(-z^2/4)
  have hI0 : ∫ u : ℝ, E u = (Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2 / 4) := by
    have hg := integral_cexp_quadratic (b := (-1 : ℂ)) (by simp) (Complex.I * z) 0
    have heq_fn : (fun u : ℝ => Complex.exp ((-1 : ℂ) * (u : ℂ) ^ 2 + Complex.I * z * (u : ℂ) + 0)) = E := by
      ext u; dsimp [E]; congr 1; ring
    rw [heq_fn] at hg
    rw [hg]
    have hpi_sqrt : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
      rw [neg_neg, div_one, Real.sqrt_eq_rpow,
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
    have hexp_eq : (0 : ℂ) - (Complex.I * z) ^ 2 / (4 * (-1 : ℂ)) = -z ^ 2 / 4 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [hpi_sqrt, hexp_eq]
  -- Helper IBP step: ∫ (u^m * E(u))' du = 0
  have hibp : ∀ m : ℕ,
      (m : ℂ) * (∫ u : ℝ, (u : ℂ) ^ (m - 1) * E u) -
      2 * (∫ u : ℝ, (u : ℂ) ^ (m + 1) * E u) +
      Complex.I * z * (∫ u : ℝ, (u : ℂ) ^ m * E u) = 0 := by
    intro m
    have hd : ∀ u : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ m * E t)
        ((m : ℂ) * (u : ℂ) ^ (m - 1) * E u - 2 * (u : ℂ) ^ (m + 1) * E u +
          Complex.I * z * (u : ℂ) ^ m * E u) u := by
      intro u
      have hofR : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) u :=
        (hasDerivAt_id' u).ofReal_comp
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ m) ((m : ℂ) * (u : ℂ) ^ (m - 1)) u := by
        simpa using hofR.fun_pow m
      have h2 : HasDerivAt E ((-2 * (u : ℂ) + Complex.I * z) * E u) u := by
        have harg : HasDerivAt (fun t : ℝ => -((t : ℂ) ^ 2) + Complex.I * z * (t : ℂ))
            (-2 * (u : ℂ) + Complex.I * z) u := by
          have ha := (hofR.fun_pow 2).fun_neg
          have hb := hofR.const_mul (Complex.I * z)
          exact (ha.fun_add hb).congr_deriv (by simp)
        exact harg.cexp.congr_deriv (by ring)
      exact (h1.fun_mul h2).congr_deriv (by rw [pow_succ]; ring)
    have hfun : (fun u : ℝ =>
        (m : ℂ) * (u : ℂ) ^ (m - 1) * E u - 2 * (u : ℂ) ^ (m + 1) * E u +
          Complex.I * z * (u : ℂ) ^ m * E u) =
        fun u : ℝ =>
          ((m : ℂ) * ((u : ℂ) ^ (m - 1) * E u) - (2 : ℂ) * ((u : ℂ) ^ (m + 1) * E u)) +
            (Complex.I * z) * ((u : ℂ) ^ m * E u) := by
      ext u; ring
    have hm1 : Integrable (fun u : ℝ => (m : ℂ) * ((u : ℂ) ^ (m - 1) * E u)) :=
      (integrable_pow_cexp_gauss z (m - 1)).const_mul (m : ℂ)
    have hm2 : Integrable (fun u : ℝ => (2 : ℂ) * ((u : ℂ) ^ (m + 1) * E u)) :=
      (integrable_pow_cexp_gauss z (m + 1)).const_mul (2 : ℂ)
    have hm0 : Integrable (fun u : ℝ => (Complex.I * z) * ((u : ℂ) ^ m * E u)) :=
      (integrable_pow_cexp_gauss z m).const_mul (Complex.I * z)
    have hm12 : Integrable (fun u : ℝ =>
        (m : ℂ) * ((u : ℂ) ^ (m - 1) * E u) - (2 : ℂ) * ((u : ℂ) ^ (m + 1) * E u)) :=
      hm1.sub hm2
    have hint_d : Integrable (fun u : ℝ =>
        (m : ℂ) * (u : ℂ) ^ (m - 1) * E u - 2 * (u : ℂ) ^ (m + 1) * E u +
          Complex.I * z * (u : ℂ) ^ m * E u) := by
      rw [hfun]; exact hm12.add hm0
    have htend := tendsto_pow_cexp_gauss_zero z m
    have hzero := MeasureTheory.integral_of_hasDerivAt_of_tendsto hd hint_d htend.2 htend.1
    rw [sub_self, hfun, integral_add hm12 hm0, integral_sub hm1 hm2,
        integral_const_mul, integral_const_mul, integral_const_mul] at hzero
    exact hzero
  -- Unroll m = 0, 1, 2, 3 to get I_1, I_2, I_3, I_4 in terms of I_0!
  have h_m0 := hibp 0
  have h_m1 := hibp 1
  have h_m2 := hibp 2
  have h_m3 := hibp 3
  simp only [Nat.cast_zero, zero_mul, zero_sub, pow_zero, one_mul, Nat.cast_one, Nat.sub_self,
             Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, pow_one] at h_m0 h_m1 h_m2 h_m3
  set I0 : ℂ := ∫ u : ℝ, E u
  set I1 : ℂ := ∫ u : ℝ, (u : ℂ) * E u
  set I2 : ℂ := ∫ u : ℝ, (u : ℂ) ^ 2 * E u
  set I3 : ℂ := ∫ u : ℝ, (u : ℂ) ^ 3 * E u
  set I4 : ℂ := ∫ u : ℝ, (u : ℂ) ^ 4 * E u
  have hI1 : I1 = (Complex.I * z / 2) * I0 := by
    have : -(2 * I1) + Complex.I * z * I0 = 0 := h_m0
    linear_combination -(1 / 2 : ℂ) * this
  have hI2 : I2 = (1 / 2 - z ^ 2 / 4) * I0 := by
    have : I0 - 2 * I2 + Complex.I * z * I1 = 0 := h_m1
    rw [hI1] at this
    have hI2sq : (Complex.I * z) * (Complex.I * z / 2) = -z ^ 2 / 2 := by
      have : Complex.I * Complex.I = -1 := by rw [← sq, Complex.I_sq]
      linear_combination (z ^ 2 / 2) * this
    linear_combination -(1 / 2 : ℂ) * this + (1 / 2 : ℂ) * I0 * hI2sq
  have hI3 : I3 = (Complex.I * z * (3 / 4 - z ^ 2 / 8)) * I0 := by
    have : 2 * I1 - 2 * I3 + Complex.I * z * I2 = 0 := h_m2
    rw [hI1, hI2] at this
    linear_combination -(1 / 2 : ℂ) * this
  have hI4 : I4 = (3 / 4 - 3 * z ^ 2 / 4 + z ^ 4 / 16) * I0 := by
    have : 3 * I2 - 2 * I4 + Complex.I * z * I3 = 0 := h_m3
    rw [hI2, hI3] at this
    have hIsq : Complex.I * Complex.I = -1 := by rw [← sq, Complex.I_sq]
    linear_combination -(1 / 2 : ℂ) * this + (1 / 2 : ℂ) * z ^ 2 * (3 / 4 - z ^ 2 / 8) * I0 * hIsq
  -- Combine 5*I0 + 2*I2 + I4 = (z^4/16 - 5*z^2/4 + 27/4)*I0 = wallTransform z!
  have hsplit_fn : (fun u : ℝ => ((wallKernel u : ℝ) : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))) =
      fun u => 5 * E u + 2 * ((u : ℂ) ^ 2 * E u) + (u : ℂ) ^ 4 * E u := by
    ext u
    dsimp [wallKernel, E]
    rw [Complex.exp_add]
    push_cast
    ring
  rw [hsplit_fn]
  have hint0 : Integrable E := (integrable_pow_cexp_gauss z 0).congr (ae_of_all _ fun u => by simp [E])
  have hint2 := integrable_pow_cexp_gauss z 2
  have hint4 := integrable_pow_cexp_gauss z 4
  have h50 : Integrable (fun u : ℝ => (5 : ℂ) * E u) := hint0.const_mul 5
  have h22 : Integrable (fun u : ℝ => (2 : ℂ) * ((u : ℂ) ^ 2 * E u)) := hint2.const_mul 2
  have h5022 : Integrable (fun u : ℝ => (5 : ℂ) * E u + (2 : ℂ) * ((u : ℂ) ^ 2 * E u)) := h50.add h22
  rw [integral_add h5022 hint4, integral_add h50 h22, integral_const_mul, integral_const_mul]
  change 5 * I0 + 2 * I2 + I4 = wallTransform z
  rw [hI2, hI4]
  dsimp [wallTransform]
  rw [← hI0]
  change 5 * I0 + 2 * ((1 / 2 - z ^ 2 / 4) * I0) + (3 / 4 - 3 * z ^ 2 / 4 + z ^ 4 / 16) * I0 =
    I0 * (z ^ 4 / 16 - 5 * z ^ 2 / 4 + 27 / 4)
  ring

/-- THEOREM III.3 (ROUTE B EXACT LOG-CONCAVE KERNEL WALL / NO-GO THEOREM):
    Although `wallKernel(u) = (5 + 2u^2 + u^4) * exp(-u^2)` is strictly positive, even, smooth,
    strictly decreasing on `[0, ∞)`, strictly log-concave on ALL of `ℝ`, super-exponentially
    decaying, and has all-order PSD Hankel matrices:
    (1) Its Fourier transform is STRICTLY POSITIVE on all of `ℝ` (`∀ γ, 0 < wallTransformReal γ`),
    (2) Yet it possesses an EXPLICIT STRICTLY OFF-LINE COMPLEX ZERO
          `z_* = √(5 + 3√3) + i √(3√3 - 5)` (`0 < z_*.im`, `wallTransform z_* = 0`),
    (3) AND it STRICTLY VIOLATES LAGUERRE'S INEQUALITY AT THE INTEGER `γ = 3`:
          `(deriv wallTransformReal 3)^2 - wallTransformReal 3 * deriv (deriv wallTransformReal) 3
            = -(95 / 18) * (wallTransformReal 3)^2 < 0`!
    Consequently, NO proof of RH on Route B can proceed solely from positivity, evenness,
    monotonicity, log-concavity, super-exponential decay, or Hankel positivity of `Φ(u)`. -/
theorem wallKernel_real_pos_yet_offline_zero_and_laguerre_neg :
    (∀ x : ℝ, 0 < wallTransformReal x) ∧
    (∃ z : ℂ, 0 < z.im ∧ wallTransform z = 0) ∧
    (deriv wallTransformReal 3) ^ 2 - wallTransformReal 3 * deriv (deriv wallTransformReal) 3 < 0 := by
  -- (1) Strict positivity on ℝ: x^4/16 - 5x^2/4 + 27/4 = ((x^2 - 10)^2 + 8) / 16 ≥ 1/2 > 0
  have hreal_pos : ∀ x : ℝ, 0 < wallTransformReal x := by
    intro x
    dsimp [wallTransformReal]
    have hq : 0 < x ^ 4 / 16 - 5 * x ^ 2 / 4 + 27 / 4 := by
      have : x ^ 4 / 16 - 5 * x ^ 2 / 4 + 27 / 4 = ((x ^ 2 - 10) ^ 2 + 8) / 16 := by ring
      rw [this]; positivity
    exact mul_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)) hq
  -- (2) Explicit off-line complex zero z_* = √(5 + 3√3) + i √(3√3 - 5)
  have h3rt3 : (5 : ℝ) < 3 * Real.sqrt 3 := by
    have h1 : (25 : ℝ) < (3 * Real.sqrt 3) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  have hoff_zero : ∃ z : ℂ, 0 < z.im ∧ wallTransform z = 0 := by
    set a : ℝ := Real.sqrt (5 + 3 * Real.sqrt 3)
    set b : ℝ := Real.sqrt (3 * Real.sqrt 3 - 5)
    refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_, ?_⟩
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                 Complex.ofReal_re, zero_mul, one_mul, zero_add]
      exact Real.sqrt_pos.mpr (by linarith)
    · dsimp [wallTransform]
      have hfactor : ((a : ℂ) + Complex.I * (b : ℂ)) ^ 4 / 16 -
          5 * ((a : ℂ) + Complex.I * (b : ℂ)) ^ 2 / 4 + 27 / 4 = 0 := by
        have ha2 : a ^ 2 = 5 + 3 * Real.sqrt 3 := Real.sq_sqrt (by linarith)
        have hb2 : b ^ 2 = 3 * Real.sqrt 3 - 5 := Real.sq_sqrt (by linarith)
        have hab2 : (a * b) ^ 2 = 2 := by
          rw [mul_pow, ha2, hb2]
          have hrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          nlinarith
        have hz2 : ((a : ℂ) + Complex.I * (b : ℂ)) ^ 2 =
            (10 : ℂ) + Complex.I * ((2 * a * b : ℝ) : ℂ) := by
          have h1 : ((a : ℂ) + Complex.I * (b : ℂ)) ^ 2 =
              ((a ^ 2 - b ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * a * b : ℝ) : ℂ) := by
            push_cast; ring_nf; rw [Complex.I_sq]; ring
          rw [h1, ha2, hb2]
          push_cast; ring
        have hz4 : ((a : ℂ) + Complex.I * (b : ℂ)) ^ 4 =
            (((10 : ℂ) + Complex.I * ((2 * a * b : ℝ) : ℂ)) ^ 2) := by
          rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hz2]
        rw [hz4, hz2]
        have hab_c : (((2 * a * b : ℝ) : ℂ)) ^ 2 = (8 : ℂ) := by
          have : (2 * a * b) ^ 2 = 8 := by linear_combination 4 * hab2
          exact_mod_cast this
        have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
        linear_combination (1 / 16 : ℂ) * ((2 * a * b : ℝ) : ℂ) ^ 2 * hI2 - (1 / 16 : ℂ) * hab_c
      rw [hfactor, mul_zero]
  -- (3) Exact Laguerre violation at integer x = 3:
  --   wallTransformReal x = √π * exp(-x^2/4) * Q(x)
  --   At x = 3: Q(3) = 9/16, Q'(3) = -3/4, Q''(3) = 17/4,
  --   F'(3) = √π e^{-9/4} * (-3/2 * Q(3) + Q'(3)) = √π e^{-9/4} * (-51/32),
  --   F''(3) = √π e^{-9/4} * ((9/4 - 1/2)*Q(3) - 3*Q'(3) + Q''(3)) = √π e^{-9/4} * (479/64),
  --   F'(3)^2 - F(3) * F''(3) = π e^{-9/2} * (2601/1024 - 4311/1024) = -1710/1024 * π e^{-9/2} < 0!
  have hlag_neg : (deriv wallTransformReal 3) ^ 2 -
      wallTransformReal 3 * deriv (deriv wallTransformReal) 3 < 0 := by
    have hd1 : ∀ x : ℝ, HasDerivAt wallTransformReal
        (Real.sqrt Real.pi * Real.exp (-x ^ 2 / 4) *
          (-(x / 2) * (x ^ 4 / 16 - 5 * x ^ 2 / 4 + 27 / 4) + (x ^ 3 / 4 - 5 * x / 2))) x := by
      intro x
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2 / 4))
          (-(x / 2) * Real.exp (-x ^ 2 / 4)) x := by
        have harg : HasDerivAt (fun t : ℝ => -t ^ 2 / 4) (-(x / 2)) x := by
          exact ((hasDerivAt_pow 2 x).neg.div_const 4).congr_deriv (by norm_num; ring)
        exact harg.exp.congr_deriv (by ring)
      have hq : HasDerivAt (fun t : ℝ => t ^ 4 / 16 - 5 * t ^ 2 / 4 + 27 / 4)
          (x ^ 3 / 4 - 5 * x / 2) x := by
        have h1 := (((hasDerivAt_pow 4 x).div_const 16).fun_sub
          (((hasDerivAt_pow 2 x).const_mul 5).div_const 4)).fun_add (hasDerivAt_const x (27 / 4 : ℝ))
        exact h1.congr_deriv (by norm_num; ring)
      exact ((he.const_mul (Real.sqrt Real.pi)).fun_mul hq).congr_deriv (by ring)
    have hderiv_fn : deriv wallTransformReal = fun x : ℝ =>
        Real.sqrt Real.pi * Real.exp (-x ^ 2 / 4) *
          (-x ^ 5 / 32 + 7 * x ^ 3 / 8 - 47 * x / 8) := by
      ext x
      rw [(hd1 x).deriv]
      ring
    have hd2_at3 : HasDerivAt (deriv wallTransformReal)
        (Real.sqrt Real.pi * Real.exp (-(3 : ℝ) ^ 2 / 4) *
          (-(3 / 2 : ℝ) * (-(3 : ℝ) ^ 5 / 32 + 7 * (3 : ℝ) ^ 3 / 8 - 47 * 3 / 8) +
            (-5 * (3 : ℝ) ^ 4 / 32 + 21 * (3 : ℝ) ^ 2 / 8 - 47 / 8))) 3 := by
      rw [hderiv_fn]
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2 / 4))
          (-(3 / 2 : ℝ) * Real.exp (-(3 : ℝ) ^ 2 / 4)) 3 := by
        have harg : HasDerivAt (fun t : ℝ => -t ^ 2 / 4) (-(3 / 2 : ℝ)) 3 := by
          exact ((hasDerivAt_pow 2 (3 : ℝ)).neg.div_const 4).congr_deriv (by norm_num)
        exact harg.exp.congr_deriv (by ring)
      have hp : HasDerivAt (fun t : ℝ => -t ^ 5 / 32 + 7 * t ^ 3 / 8 - 47 * t / 8)
          (-5 * (3 : ℝ) ^ 4 / 32 + 21 * (3 : ℝ) ^ 2 / 8 - 47 / 8) 3 := by
        have h1 := (((hasDerivAt_pow 5 (3 : ℝ)).neg.div_const 32).fun_add
          (((hasDerivAt_pow 3 (3 : ℝ)).const_mul 7).div_const 8)).fun_sub
          (((hasDerivAt_id' (3 : ℝ)).const_mul 47).div_const 8)
        exact h1.congr_deriv (by norm_num)
      exact ((he.const_mul (Real.sqrt Real.pi)).fun_mul hp).congr_deriv (by ring)
    have hF3 : wallTransformReal 3 = Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) * (9 / 16) := by
      dsimp [wallTransformReal]; norm_num
    have hFp3 : deriv wallTransformReal 3 = Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) * (-(51 / 32)) := by
      rw [hderiv_fn]; norm_num
    have hFpp3 : deriv (deriv wallTransformReal) 3 = Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) * (479 / 64) := by
      rw [hd2_at3.deriv]; norm_num
    rw [hF3, hFp3, hFpp3]
    have hpos_fac : 0 < (Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ))) ^ 2 := by
      have : 0 < Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) :=
        mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)
      exact sq_pos_of_pos this
    have heq_neg : (Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) * -(51 / 32)) ^ 2 -
        Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) * (9 / 16) *
          (Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ)) * (479 / 64)) =
        -(855 / 512 : ℝ) * (Real.sqrt Real.pi * Real.exp (-(9 / 4 : ℝ))) ^ 2 := by ring
    rw [heq_neg]
    nlinarith
  exact ⟨hreal_pos, hoff_zero, hlag_neg⟩

end RouteABLimitBarriersAndDeBrangesSynthesis
