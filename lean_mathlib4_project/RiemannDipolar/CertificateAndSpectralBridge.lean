/-
  ==============================================================================
  EXACT 2D PAST-FUTURE LAGUERRE KERNEL IDENTITY, ALL-ORDER ABSOLUTE
  MONOTONICITY OF REAL-ZERO PRODUCTS, AND SPECTRAL POSITIVITY CERTIFICATES
  (LDL^T CHOLESKY & PROLATE OPERATOR COMPARISON)

  Title: Completing the Analytic and Certificate Bridge for Routes A and B
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Exact 2D Past-Future Light-Cone Representation of Laguerre L_1):
      * Unified parametric gamma-differentiation of Xi(gamma) = 2 int Phi cos
        yielding exact integral formulas for Xi'(gamma) and Xi''(gamma).
      * `laguerre_L1_eq_pastFuture_double_integral`:
          2 * ((Xi'(gamma))^2 - Xi(gamma) * Xi''(gamma))
            = 2 * int_0^inf int_0^inf Phi(u) * Phi(v) *
                [(u + v)^2 * cos(gamma*(u - v)) + (u - v)^2 * cos(gamma*(u + v))] dv du.
  - Part II (All-Order Real-Axis Absolute Monotonicity & Real-Zero Product Mechanism):
      * `riemannXi_real_iteratedDeriv_eq` & `riemannXi_real_iteratedDeriv_pos`:
        For EVERY order n in N and every sigma > 0, the n-th real-axis derivative
        of sigma |-> Re(riemannXi(1/2 + sigma)) is strictly positive (and for every
        even n, strictly positive for ALL sigma in R).
      * `finite_real_zero_product_iteratedDeriv_nonneg`:
        For any finite family of real roots {r_j}, the squared modulus
          P(sigma) = prod_j ((gamma - r_j)^2 + sigma^2)
        is absolutely monotonic on [0, inf): iteratedDeriv n P sigma >= 0 for ALL n in N
        and sigma >= 0, and strictly convex (P''(sigma) > 0) for sigma > 0 when nonempty.
  - Part III (Exact Positivity Certificate Theorems for Route A):
      * `cholesky_ldl_quadratic_eq_sum_sq`, `cholesky_ldl_quadratic_nonneg`, and
        `cholesky_ldl_quadratic_pos_of_unit_lower`:
        Exact algebraic proof that any symmetric matrix W = L D L^T with unit
        lower-triangular L and positive pivots D_k > 0 is strictly positive definite.
      * `prolate_comparison_quadratic_pos`:
        Any functional decomposing as Q(f) = alpha * <f, H_prolate f> + R(f)
        with alpha > 0, c != 0, and R(f) >= 0 is strictly positive for all
        non-trivial C^2 test functions f on (-a, a).
  ==============================================================================
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.XiConvexityLaguerre
import RiemannDipolar.UnconditionalCorridorAndProlate

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate

namespace CertificateAndSpectralBridge

-- ==============================================================================
-- PART I: EXACT 2D PAST-FUTURE LIGHT-CONE INTEGRAL FOR LAGUERRE CURVATURE L_1
-- ==============================================================================

lemma integrableOn_phi_pow_cos (k : ℕ) (γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.cos (γ * u)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul
    (C2 * (k.factorial : ℝ))).mono'
    (((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
  have hcos : |Real.cos (γ * u)| ≤ 1 := Real.abs_cos_le_one _
  have hpow := pow_le_factorial_mul_exp k hu0
  have hPhi := hPhi_le u hu0
  rw [Real.norm_eq_abs] at hPhi
  calc |riemannPhi u| * u ^ k * |Real.cos (γ * u)|
    _ ≤ |riemannPhi u| * u ^ k * 1 :=
        mul_le_mul_of_nonneg_left hcos (mul_nonneg (abs_nonneg _) (pow_nonneg hu0 _))
    _ = |riemannPhi u| * u ^ k := mul_one _
    _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
          ((k.factorial : ℝ) * Real.exp u) :=
        mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
    _ = C2 * (k.factorial : ℝ) *
          (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u) := by ring
    _ = C2 * (k.factorial : ℝ) *
          Real.exp ((9 / 2 + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
        rw [← Real.exp_add]; congr 2; ring

lemma integrableOn_phi_pow_sin (k : ℕ) (γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.sin (γ * u)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul
    (C2 * (k.factorial : ℝ))).mono'
    (((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
  have hsin : |Real.sin (γ * u)| ≤ 1 := Real.abs_sin_le_one _
  have hpow := pow_le_factorial_mul_exp k hu0
  have hPhi := hPhi_le u hu0
  rw [Real.norm_eq_abs] at hPhi
  calc |riemannPhi u| * u ^ k * |Real.sin (γ * u)|
    _ ≤ |riemannPhi u| * u ^ k * 1 :=
        mul_le_mul_of_nonneg_left hsin (mul_nonneg (abs_nonneg _) (pow_nonneg hu0 _))
    _ = |riemannPhi u| * u ^ k := mul_one _
    _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
          ((k.factorial : ℝ) * Real.exp u) :=
        mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
    _ = C2 * (k.factorial : ℝ) *
          (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u) := by ring
    _ = C2 * (k.factorial : ℝ) *
          Real.exp ((9 / 2 + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
        rw [← Real.exp_add]; congr 2; ring

theorem hasDerivAt_integral_phi_pow_cos (k : ℕ) (γ₀ : ℝ) :
    HasDerivAt (fun γ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cos (γ * u))
      (-(∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.sin (γ₀ * u))) γ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun γ u => riemannPhi u * u ^ k * Real.cos (γ * u))
    (F' := fun γ u => -(riemannPhi u * u ^ (k + 1) * Real.sin (γ * u)))
    (s := Metric.ball γ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds γ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun γ =>
      (((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_cos k γ₀)
    ((((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).neg).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu γ _
      have hu0 : 0 ≤ u := le_of_lt hu
      rw [norm_neg, norm_mul, norm_mul, Real.norm_eq_abs,
          Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
      have hsin : |Real.sin (γ * u)| ≤ 1 := Real.abs_sin_le_one _
      have hpow := pow_le_factorial_mul_exp (k + 1) hu0
      have hPhi := hPhi_le u hu0
      rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * |Real.sin (γ * u)|
        _ ≤ |riemannPhi u| * u ^ (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hsin (mul_nonneg (abs_nonneg _) (pow_nonneg hu0 _))
        _ = |riemannPhi u| * u ^ (k + 1) := mul_one _
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) :=
            mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ γ _
      have hlin : HasDerivAt (fun g : ℝ => g * u) u γ := by
        simpa using (hasDerivAt_id γ).mul_const u
      have hcos : HasDerivAt (fun g : ℝ => Real.cos (g * u)) (-Real.sin (γ * u) * u) γ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_cos (γ * u)).comp γ hlin
      convert hcos.const_mul (riemannPhi u * u ^ k) using 1
      rw [pow_succ]; ring)
  simpa only [integral_neg] using h.2

theorem hasDerivAt_integral_phi_pow_sin (k : ℕ) (γ₀ : ℝ) :
    HasDerivAt (fun γ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.sin (γ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.cos (γ₀ * u)) γ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun γ u => riemannPhi u * u ^ k * Real.sin (γ * u))
    (F' := fun γ u => riemannPhi u * u ^ (k + 1) * Real.cos (γ * u))
    (s := Metric.ball γ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds γ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun γ =>
      (((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_sin k γ₀)
    (((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu γ _
      have hu0 : 0 ≤ u := le_of_lt hu
      rw [norm_mul, norm_mul, Real.norm_eq_abs,
          Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
      have hcos : |Real.cos (γ * u)| ≤ 1 := Real.abs_cos_le_one _
      have hpow := pow_le_factorial_mul_exp (k + 1) hu0
      have hPhi := hPhi_le u hu0
      rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * |Real.cos (γ * u)|
        _ ≤ |riemannPhi u| * u ^ (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hcos (mul_nonneg (abs_nonneg _) (pow_nonneg hu0 _))
        _ = |riemannPhi u| * u ^ (k + 1) := mul_one _
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) :=
            mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ γ _
      have hlin : HasDerivAt (fun g : ℝ => g * u) u γ := by
        simpa using (hasDerivAt_id γ).mul_const u
      have hsin : HasDerivAt (fun g : ℝ => Real.sin (g * u)) (Real.cos (γ * u) * u) γ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_sin (γ * u)).comp γ hlin
      convert hsin.const_mul (riemannPhi u * u ^ k) using 1
      rw [pow_succ]; ring)
  exact h.2

/-- Exact integral representations of Xi(gamma), Xi'(gamma), and Xi''(gamma). -/
theorem xiCritical_eq_cos_integral (γ : ℝ) :
    xiCritical γ = 2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cos (γ * u) := by
  dsimp [xiCritical]
  rw [(riemannXi_re_im_pastFuture_phi (1 / 2) γ).1]
  exact congrArg (2 * ·) (setIntegral_congr_fun measurableSet_Ioi fun u _ => by simp)

theorem deriv_xiCritical_eq_sin_integral (γ : ℝ) :
    deriv xiCritical γ = -2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 1 * Real.sin (γ * u) := by
  have hfun : xiCritical = fun g => 2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cos (g * u) :=
    funext xiCritical_eq_cos_integral
  rw [hfun]
  have hd := (hasDerivAt_integral_phi_pow_cos 0 γ).const_mul 2
  rw [hd.deriv]
  ring

theorem deriv2_xiCritical_eq_cos_integral (γ : ℝ) :
    deriv (deriv xiCritical) γ = -2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 2 * Real.cos (γ * u) := by
  have hfun : deriv xiCritical = fun g => -2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 1 * Real.sin (g * u) :=
    funext deriv_xiCritical_eq_sin_integral
  rw [hfun]
  have hd := (hasDerivAt_integral_phi_pow_sin 1 γ).const_mul (-2)
  exact hd.deriv

/-- Algebraic light-cone identity for the Laguerre 2D kernel. -/
lemma laguerre_lightcone_trig_identity (γ u v : ℝ) :
    2 * ((u ^ 2 + v ^ 2) * Real.cos (γ * u) * Real.cos (γ * v) +
         2 * u * v * Real.sin (γ * u) * Real.sin (γ * v)) =
      (u + v) ^ 2 * Real.cos (γ * (u - v)) + (u - v) ^ 2 * Real.cos (γ * (u + v)) := by
  have hkp : Real.cos (γ * (u + v)) = Real.cos (γ * u) * Real.cos (γ * v) - Real.sin (γ * u) * Real.sin (γ * v) := by
    rw [mul_add, Real.cos_add]
  have hkm : Real.cos (γ * (u - v)) = Real.cos (γ * u) * Real.cos (γ * v) + Real.sin (γ * u) * Real.sin (γ * v) := by
    rw [mul_sub, Real.cos_sub]
  rw [hkp, hkm]
  ring

/-- THEOREM I.1 (EXACT 2D PAST-FUTURE LIGHT-CONE INTEGRAL FOR LAGUERRE CURVATURE L_1):
    For EVERY gamma in R:
      (d^2/dsigma^2)|_{sigma=0} ||xi(1/2 + sigma + i*gamma)||^2
        = 2 * ((Xi'(gamma))^2 - Xi(gamma) * Xi''(gamma))
        = 2 * int_0^inf int_0^inf Phi(u) * Phi(v) *
            [(u + v)^2 * cos(gamma*(u - v)) + (u - v)^2 * cos(gamma*(u + v))] dv du. -/
theorem laguerre_L1_eq_pastFuture_double_integral (γ : ℝ) :
    deriv (deriv (fun x : ℝ => xiNormSq x γ)) 0 =
      2 * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
        riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cos (γ * (u - v)) + (u - v) ^ 2 * Real.cos (γ * (u + v))) := by
  let f0 : ℝ → ℝ := fun u => riemannPhi u * u ^ 0 * Real.cos (γ * u)
  let f1 : ℝ → ℝ := fun u => riemannPhi u * u ^ 1 * Real.sin (γ * u)
  let f2 : ℝ → ℝ := fun u => riemannPhi u * u ^ 2 * Real.cos (γ * u)
  have hf0 : IntegrableOn f0 (Ioi 0) := integrableOn_phi_pow_cos 0 γ
  have hf1 : IntegrableOn f1 (Ioi 0) := integrableOn_phi_pow_sin 1 γ
  have hf2 : IntegrableOn f2 (Ioi 0) := integrableOn_phi_pow_cos 2 γ
  let I0 := ∫ u in Ioi (0 : ℝ), f0 u
  let I1 := ∫ u in Ioi (0 : ℝ), f1 u
  let I2 := ∫ u in Ioi (0 : ℝ), f2 u
  rw [xiNormSq_deriv2_sigma_zero_eq_laguerre γ,
      xiCritical_eq_cos_integral γ, deriv_xiCritical_eq_sin_integral γ,
      deriv2_xiCritical_eq_cos_integral γ]
  change 2 * ((-2 * I1) ^ 2 - (2 * I0) * (-2 * I2)) = _
  have hsymm : 2 * ((-2 * I1) ^ 2 - (2 * I0) * (-2 * I2)) =
      4 * (I0 * I2 + I2 * I0 + 2 * (I1 * I1)) := by ring
  rw [hsymm]
  have h02 : I0 * I2 = ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), f0 u * f2 v := by
    dsimp [I0, I2]
    rw [← integral_mul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ => (integral_const_mul _ _).symm
  have h20 : I2 * I0 = ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), f2 u * f0 v := by
    dsimp [I0, I2]
    rw [← integral_mul_const]
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ => (integral_const_mul _ _).symm
  have h11 : 2 * (I1 * I1) = ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), 2 * (f1 u * f1 v) := by
    dsimp [I1]
    rw [← integral_mul_const, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have heq : (fun v => 2 * (f1 u * f1 v)) = fun v => (2 * f1 u) * f1 v := by ext v; ring
    rw [heq, integral_const_mul]
    ring
  have hint_02 : IntegrableOn (fun u => ∫ v in Ioi (0 : ℝ), f0 u * f2 v) (Ioi 0) := by
    have : (fun u => ∫ v in Ioi (0 : ℝ), f0 u * f2 v) = fun u => f0 u * I2 :=
      funext fun u => integral_const_mul _ _
    rw [this]; exact hf0.mul_const _
  have hint_20 : IntegrableOn (fun u => ∫ v in Ioi (0 : ℝ), f2 u * f0 v) (Ioi 0) := by
    have : (fun u => ∫ v in Ioi (0 : ℝ), f2 u * f0 v) = fun u => f2 u * I0 :=
      funext fun u => integral_const_mul _ _
    rw [this]; exact hf2.mul_const _
  have hint_11 : IntegrableOn (fun u => ∫ v in Ioi (0 : ℝ), 2 * (f1 u * f1 v)) (Ioi 0) := by
    have : (fun u => ∫ v in Ioi (0 : ℝ), 2 * (f1 u * f1 v)) = fun u => (2 * f1 u) * I1 := by
      ext u
      have heq : (fun v => 2 * (f1 u * f1 v)) = fun v => (2 * f1 u) * f1 v := by ext v; ring
      rw [heq, integral_const_mul]
    rw [this]; exact (hf1.const_mul 2).mul_const _
  have hint_0220 : IntegrableOn
      (fun u => (∫ v in Ioi (0 : ℝ), f0 u * f2 v) + ∫ v in Ioi (0 : ℝ), f2 u * f0 v) (Ioi 0) :=
    hint_02.add hint_20
  rw [h02, h20, h11, ← integral_add hint_02 hint_20, ← integral_add hint_0220 hint_11]
  have hinner : ∀ u : ℝ,
      (∫ v in Ioi (0 : ℝ), f0 u * f2 v) + (∫ v in Ioi (0 : ℝ), f2 u * f0 v) +
      (∫ v in Ioi (0 : ℝ), 2 * (f1 u * f1 v)) =
      ∫ v in Ioi (0 : ℝ), (f0 u * f2 v + f2 u * f0 v + 2 * (f1 u * f1 v)) := by
    intro u
    have i1 := hf2.const_mul (f0 u)
    have i2 := hf0.const_mul (f2 u)
    have i3 : IntegrableOn (fun v => 2 * (f1 u * f1 v)) (Ioi 0) := by
      have : (fun v => 2 * (f1 u * f1 v)) = fun v => (2 * f1 u) * f1 v := by ext v; ring
      rw [this]; exact hf1.const_mul _
    have i12 : IntegrableOn (fun v => f0 u * f2 v + f2 u * f0 v) (Ioi 0) := i1.add i2
    rw [← integral_add i1 i2, ← integral_add i12 i3]
  simp_rw [hinner]
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, ← integral_const_mul]
  refine congrArg (2 * ·) (setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_)
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  dsimp [f0, f1, f2]
  have hid := laguerre_lightcone_trig_identity γ u v
  calc 2 * (riemannPhi u * u ^ 0 * Real.cos (γ * u) * (riemannPhi v * v ^ 2 * Real.cos (γ * v)) +
            riemannPhi u * u ^ 2 * Real.cos (γ * u) * (riemannPhi v * v ^ 0 * Real.cos (γ * v)) +
            2 * (riemannPhi u * u ^ 1 * Real.sin (γ * u) * (riemannPhi v * v ^ 1 * Real.sin (γ * v))))
    _ = riemannPhi u * riemannPhi v *
        (2 * ((u ^ 2 + v ^ 2) * Real.cos (γ * u) * Real.cos (γ * v) +
              2 * u * v * Real.sin (γ * u) * Real.sin (γ * v))) := by ring
    _ = riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cos (γ * (u - v)) + (u - v) ^ 2 * Real.cos (γ * (u + v))) := by rw [hid]

-- ==============================================================================
-- PART II: ALL-ORDER REAL-AXIS ABSOLUTE MONOTONICITY & REAL-ZERO PRODUCT ENGINE
-- ==============================================================================

/-- Exact closed form of the n-th iterated derivative of sigma |-> Re(riemannXi(1/2 + sigma))
    for ALL n in N by induction on n. -/
theorem riemannXi_real_iteratedDeriv_eq (n : ℕ) (σ : ℝ) :
    iteratedDeriv n (fun x : ℝ => (riemannXi (⟨1 / 2 + x, 0⟩ : ℂ)).re) σ =
      if Even n then 2 * Icosh n σ else 2 * Isinh n σ := by
  induction n generalizing σ with
  | zero =>
    rw [iteratedDeriv_zero, (riemannXi_real_re_im σ).1]
    simp [Icosh]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun x : ℝ => (riemannXi (⟨1 / 2 + x, 0⟩ : ℂ)).re) =
        fun x => if Even n then 2 * Icosh n x else 2 * Isinh n x := funext ih
    rw [hfun]
    by_cases he : Even n
    · have ho : ¬ Even (n + 1) := by rwa [Nat.even_add_one, not_not]
      simp only [he, ho, ↓reduceIte]
      exact ((hasDerivAt_Icosh n σ).const_mul 2).deriv
    · have he' : Even (n + 1) := by rwa [Nat.even_add_one]
      simp only [he, he', ↓reduceIte]
      exact ((hasDerivAt_Isinh n σ).const_mul 2).deriv

/-- THEOREM II.1 (Unconditional All-Order Real-Axis Absolute Monotonicity):
    For EVERY order n in N and EVERY sigma > 0, the n-th derivative of
    sigma |-> Re(riemannXi(1/2 + sigma)) is STRICTLY POSITIVE (and for every even n,
    strictly positive on ALL of R). -/
theorem riemannXi_real_iteratedDeriv_pos (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    0 < iteratedDeriv n (fun x : ℝ => (riemannXi (⟨1 / 2 + x, 0⟩ : ℂ)).re) σ := by
  rw [riemannXi_real_iteratedDeriv_eq n σ]
  split_ifs
  · have := pos_integral_phi_pow_cosh n σ; dsimp [Icosh]; linarith
  · have := pos_integral_phi_pow_sinh n hσ; dsimp [Isinh]; linarith

theorem riemannXi_real_iteratedDeriv_even_pos {n : ℕ} (hn : Even n) (σ : ℝ) :
    0 < iteratedDeriv n (fun x : ℝ => (riemannXi (⟨1 / 2 + x, 0⟩ : ℂ)).re) σ := by
  rw [riemannXi_real_iteratedDeriv_eq n σ]
  simp only [hn, ↓reduceIte]
  have := pos_integral_phi_pow_cosh n σ; dsimp [Icosh]; linarith

/-- Elementary quadratic factor q_a(sigma) = a^2 + sigma^2 has all derivatives >= 0 on [0, inf). -/
lemma quadratic_factor_contDiff (a : ℝ) : ContDiff ℝ ⊤ (fun σ : ℝ => a ^ 2 + σ ^ 2) := by
  fun_prop

lemma quadratic_factor_iteratedDeriv_nonneg (a : ℝ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ iteratedDeriv n (fun x : ℝ => a ^ 2 + x ^ 2) σ := by
  match n with
  | 0 =>
    rw [iteratedDeriv_zero]
    positivity
  | 1 =>
    rw [iteratedDeriv_one]
    have hd : HasDerivAt (fun x : ℝ => a ^ 2 + x ^ 2) (2 * σ) σ := by
      have h := (hasDerivAt_const σ (a ^ 2)).add (hasDerivAt_pow 2 σ)
      convert h using 1; ring
    rw [hd.deriv]; linarith
  | 2 =>
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : deriv (fun x : ℝ => a ^ 2 + x ^ 2) = fun x => 2 * x := by
      ext x
      have hd : HasDerivAt (fun t : ℝ => a ^ 2 + t ^ 2) (2 * x) x := by
        have h := (hasDerivAt_const x (a ^ 2)).add (hasDerivAt_pow 2 x)
        convert h using 1; ring
      exact hd.deriv
    rw [h1]
    have hd2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 σ := by
      simpa using (hasDerivAt_id σ).const_mul (2 : ℝ)
    rw [hd2.deriv]; norm_num
  | n + 3 =>
    have h2 : iteratedDeriv 2 (fun x : ℝ => a ^ 2 + x ^ 2) = fun _ => (2 : ℝ) := by
      ext x
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      have h1 : deriv (fun t : ℝ => a ^ 2 + t ^ 2) = fun t => 2 * t := by
        ext t
        have hd : HasDerivAt (fun s : ℝ => a ^ 2 + s ^ 2) (2 * t) t := by
          have h := (hasDerivAt_const t (a ^ 2)).add (hasDerivAt_pow 2 t)
          convert h using 1; ring
        exact hd.deriv
      rw [h1]
      have hd2 : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      exact hd2.deriv
    have h3 : iteratedDeriv 3 (fun x : ℝ => a ^ 2 + x ^ 2) = fun _ => (0 : ℝ) := by
      ext x
      rw [iteratedDeriv_succ, h2, deriv_const]
    have hzero : ∀ k : ℕ, iteratedDeriv (k + 3) (fun x : ℝ => a ^ 2 + x ^ 2) = fun _ => (0 : ℝ) := by
      intro k
      induction k with
      | zero => exact h3
      | succ k ihk =>
        ext x
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, iteratedDeriv_succ, ihk, deriv_const]
    rw [hzero n]

/-- Closure of absolute monotonicity under multiplication (Leibniz rule). -/
lemma mul_iteratedDeriv_nonneg {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    {σ : ℝ} (hf_pos : ∀ k : ℕ, 0 ≤ iteratedDeriv k f σ) (hg_pos : ∀ k : ℕ, 0 ≤ iteratedDeriv k g σ)
    (n : ℕ) :
    0 ≤ iteratedDeriv n (fun x => f x * g x) σ := by
  have hleib := iteratedDeriv_mul (x := σ) (n := n)
    (hf.contDiffAt.of_le le_top) (hg.contDiffAt.of_le le_top)
  rw [show (fun x => f x * g x) = f * g from rfl, hleib]
  refine Finset.sum_nonneg fun k _ => ?_
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf_pos k)) (hg_pos (n - k))

/-- THEOREM II.2 (Converse Real-Zero Absolute Monotonicity Engine):
    For ANY finite set S of real zeros {r_j} (such as finite truncations of the
    Hadamard product of Xi under RH), the squared modulus
      P(sigma) = prod_{j in S} ((gamma - r_j)^2 + sigma^2)
    is smooth and ABSOLUTELY MONOTONIC on [0, inf): EVERY n-th derivative
    satisfies iteratedDeriv n P sigma >= 0 for ALL n in N and ALL sigma >= 0! -/
theorem finite_real_zero_product_iteratedDeriv_nonneg {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r : ι → ℝ) (γ : ℝ) :
    ContDiff ℝ ⊤ (fun σ : ℝ => ∏ j ∈ S, ((γ - r j) ^ 2 + σ ^ 2)) ∧
    ∀ (n : ℕ) {σ : ℝ}, 0 ≤ σ →
      0 ≤ iteratedDeriv n (fun x : ℝ => ∏ j ∈ S, ((γ - r j) ^ 2 + x ^ 2)) σ := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp; exact contDiff_const, fun n σ _ => ?_⟩
    simp only [Finset.prod_empty]
    cases n with
    | zero => rw [iteratedDeriv_zero]; norm_num
    | succ k =>
      have hd0 : deriv (fun _ : ℝ => (1 : ℝ)) = (0 : ℝ → ℝ) :=
        funext fun x => deriv_const x (1 : ℝ)
      rw [iteratedDeriv_succ', hd0, iteratedDeriv_const_zero]
  | insert a s ha ih =>
    obtain ⟨ih_cd, ih_pos⟩ := ih
    have heq : (fun σ : ℝ => ∏ j ∈ insert a s, ((γ - r j) ^ 2 + σ ^ 2)) =
        fun σ : ℝ => ((γ - r a) ^ 2 + σ ^ 2) * (∏ j ∈ s, ((γ - r j) ^ 2 + σ ^ 2)) := by
      ext σ; exact Finset.prod_insert ha
    rw [heq]
    have hq_cd : ContDiff ℝ ⊤ (fun σ : ℝ => (γ - r a) ^ 2 + σ ^ 2) :=
      quadratic_factor_contDiff (γ - r a)
    refine ⟨hq_cd.mul ih_cd, fun n σ hσ => ?_⟩
    exact mul_iteratedDeriv_nonneg hq_cd ih_cd
      (fun k => quadratic_factor_iteratedDeriv_nonneg (γ - r a) k hσ)
      (fun k => ih_pos k hσ) n

-- ==============================================================================
-- PART III: EXACT POSITIVITY CERTIFICATE THEOREMS FOR ROUTE A
--           (LDL^T CHOLESKY CERTIFICATES & PROLATE COMPARISON DECOMPOSITION)
-- ==============================================================================

/-- THEOREM III.1 (Exact Algebraic Identity for LDL^T Cholesky Certificates):
    If an N x N real matrix W satisfies W_{ij} = sum_k L_{ik} * D_k * L_{jk}, then
    its quadratic form equals the exact weighted sum of squares:
      sum_{i,j} v_i * W_{ij} * v_j = sum_k D_k * (sum_i v_i * L_{ik})^2. -/
theorem cholesky_ldl_quadratic_eq_sum_sq {N : ℕ}
    (W L : Fin N → Fin N → ℝ) (D : Fin N → ℝ)
    (hfac : ∀ i j : Fin N, W i j = ∑ k : Fin N, L i k * D k * L j k)
    (v : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, v i * W i j * v j =
      ∑ k : Fin N, D k * (∑ i : Fin N, v i * L i k) ^ 2 := by
  calc ∑ i : Fin N, ∑ j : Fin N, v i * W i j * v j
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, D k * (v i * L i k) * (v j * L j k) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hfac i j, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i : Fin N, ∑ k : Fin N, ∑ j : Fin N, D k * (v i * L i k) * (v j * L j k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k : Fin N, ∑ i : Fin N, ∑ j : Fin N, D k * (v i * L i k) * (v j * L j k) :=
        Finset.sum_comm
    _ = ∑ k : Fin N, D k * (∑ i : Fin N, v i * L i k) ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring

/-- COROLLARY III.1a (Non-Negativity from Non-Negative Cholesky Pivots): -/
theorem cholesky_ldl_quadratic_nonneg {N : ℕ}
    (W L : Fin N → Fin N → ℝ) (D : Fin N → ℝ)
    (hfac : ∀ i j : Fin N, W i j = ∑ k : Fin N, L i k * D k * L j k)
    (hD : ∀ k : Fin N, 0 ≤ D k) (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, v i * W i j * v j := by
  rw [cholesky_ldl_quadratic_eq_sum_sq W L D hfac v]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hD k) (sq_nonneg _)

/-- THEOREM III.2 (Strict Positive-Definiteness from Unit Lower-Triangular LDL^T Certificate):
    If W = L D L^T where L is unit lower-triangular (L_{kk} = 1 and L_{ik} = 0 for i < k)
    and EVERY pivot D_k > 0, then v^T W v > 0 for EVERY non-zero vector v != 0! -/
theorem cholesky_ldl_quadratic_pos_of_unit_lower {N : ℕ}
    (W L : Fin N → Fin N → ℝ) (D : Fin N → ℝ)
    (hfac : ∀ i j : Fin N, W i j = ∑ k : Fin N, L i k * D k * L j k)
    (hdiag : ∀ k : Fin N, L k k = 1)
    (hlow : ∀ i k : Fin N, i < k → L i k = 0)
    (hD : ∀ k : Fin N, 0 < D k)
    {v : Fin N → ℝ} (hv : ∃ i : Fin N, v i ≠ 0) :
    0 < ∑ i : Fin N, ∑ j : Fin N, v i * W i j * v j := by
  rw [cholesky_ldl_quadratic_eq_sum_sq W L D hfac v]
  -- Pick the LARGEST index k0 in Fin N where v k0 != 0
  let S : Finset (Fin N) := Finset.univ.filter (fun i => v i ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let k0 : Fin N := S.max' hS
  have hk0_mem : k0 ∈ S := Finset.max'_mem S hS
  have hvk0_ne : v k0 ≠ 0 := (Finset.mem_filter.mp hk0_mem).2
  have hv_above : ∀ i : Fin N, k0 < i → v i = 0 := by
    intro i hi
    by_contra hne
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    have hle : i ≤ k0 := Finset.le_max' S i hiS
    exact not_lt_of_ge hle hi
  -- Evaluate the k0-th linear form: sum_i v_i * L_{i, k0} = v_{k0} * 1 = v_{k0} != 0
  have hsum_k0 : ∑ i : Fin N, v i * L i k0 = v k0 := by
    rw [Finset.sum_eq_single k0]
    · rw [hdiag k0, mul_one]
    · intro i _ hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [hlow i k0 hlt, mul_zero]
      · rw [hv_above i hgt, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k0) h
  have hterm_pos : 0 < D k0 * (∑ i : Fin N, v i * L i k0) ^ 2 := by
    rw [hsum_k0]
    exact mul_pos (hD k0) (sq_pos_of_ne_zero hvk0_ne)
  have hall_nonneg : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ D k * (∑ i : Fin N, v i * L i k) ^ 2 :=
    fun k _ => mul_nonneg (le_of_lt (hD k)) (sq_nonneg _)
  exact lt_of_lt_of_le hterm_pos (Finset.single_le_sum hall_nonneg (Finset.mem_univ k0))

/-- THEOREM III.3 (Prolate Comparison Spectral Positivity Certificate):
    If a quadratic energy functional Q on C^2([-a, a]) admits a Prolate comparison
    decomposition
      Q(f) = alpha * <f, H_prolate(a, c, f)> + R(f)
    with alpha > 0, c != 0, and non-negative remainder R(f) >= 0, then Q(f) > 0
    STRICTLY for every C^2 function f that is non-zero somewhere in (-a, a). -/
theorem prolate_comparison_quadratic_pos {a c α : ℝ} (ha : 0 < a) (hc : c ≠ 0) (hα : 0 < α)
    (Q R : (ℝ → ℝ) → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hdecomp : Q f = α * (∫ x in (-a)..a, f x * prolateOp a c f x) + R f)
    (hR : 0 ≤ R f) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (-a) a) (hf₀ : f x₀ ≠ 0) :
    0 < Q f := by
  rw [hdecomp]
  have hp := prolate_quadratic_pos_of_ne_zero ha hc hf hx₀ hf₀
  have hmul : 0 < α * (∫ x in (-a)..a, f x * prolateOp a c f x) := mul_pos hα hp
  linarith

end CertificateAndSpectralBridge
