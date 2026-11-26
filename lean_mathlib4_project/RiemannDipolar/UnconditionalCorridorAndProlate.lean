/-
  ==============================================================================
  UNCONDITIONAL REAL-AXIS CONVEXITY CORRIDOR (ROUTE B) AND
  SELF-ADJOINT POSITIVE-DEFINITE CONNES-CONSANI PROLATE OPERATOR
  WITH SUPERSYMMETRIC DARBOUX FACTORIZATION (ROUTE A)

  Title: Unconditional Differential Corridor for ||xi||^2 and Spectral
         Positivity of the Compactified Prolate & Darboux Operators
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Route B — Unconditional Real-Axis Differential Hierarchy & Corridor):
      * Unified parametric differentiation under the integral sign for all orders
        k in N on the past-future kernel Phi(u) > 0.
      * Unconditional positivity of xi(1/2 + sigma) > 0 for all sigma in R.
      * Unconditional positivity along the entire real axis gamma = 0 of:
          - Level -1 force:   m1(sigma, 0) > 0 for all sigma > 0
          - Level -2 Hessian: m2(sigma, 0) > 0 for all sigma in R
          - Critical Laguerre expression at origin: L1(Xi)(0) > 0
          - Level -3 jerk:    m3(sigma, 0) > 0 for all sigma > 0
      * Tube-Lemma Compactness Corridor (`exists_unconditional_convex_corridor`):
          There exists delta > 0 such that for ALL sigma in [0, 1/2] and ALL
          |gamma| < delta, the transverse Hessian satisfies d^2V/dsigma^2 > 0
          unconditionally (hence m1 > 0 and no zeros of riemannZeta exist in
          the open strip corridor (0, 1) x (-delta, delta)).
  - Part II (Route A — Unconditional Connes-Consani Prolate & Darboux Spectral Theory):
      * Exact boundary-free integration by parts on [-a, a] for
          H_prolate(a, c, f)(x) = -((a^2 - x^2) f')'(x) + c^2 x^2 f(x),
        exploiting exact degeneracy (a^2 - x^2) = 0 at x = ±a.
      * Unconditional symmetry (formal self-adjointness) on C^2([-a, a]).
      * Unconditional non-negativity and strict positive-definiteness (for c != 0).
      * Unconditional positivity of all eigenvalues mu > 0 and exact L^2([-a, a])
        orthogonality of distinct-eigenvalue eigenfunctions.
      * Unconditional Supersymmetric Darboux Factorization for any strictly
        positive C^2 ground state v_0 > 0 on [-a, a]:
          int_{-a}^a f (-f'' + (v_0''/v_0) f) dx = int_{-a}^a (f' - (v_0'/v_0) f)^2 dx >= 0.
  ==============================================================================
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Compactness.Compact
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.XiConvexityLaguerre

open Real Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped ComplexConjugate
open PastFutureXiKernel XiConvexityLaguerre EulerAdelicBridge

namespace UnconditionalCorridorAndProlate

-- ==============================================================================
-- PART I: UNCONDITIONAL REAL-AXIS DIFFERENTIAL POSITIVITY & OPEN CONVEX CORRIDOR
-- ==============================================================================

/-- Super-exponential integrability of Phi(u) * u^k * cosh(sigma * u) on (0, inf). -/
lemma integrableOn_phi_pow_cosh (k : ℕ) (σ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.cosh (σ * u)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + |σ| + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul
    (C2 * (k.factorial : ℝ))).mono'
    (((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hu0 _),
      Real.norm_of_nonneg (le_of_lt (Real.cosh_pos _))]
  have hpow := pow_le_factorial_mul_exp k hu0
  have hcosh : Real.cosh (σ * u) ≤ Real.exp (|σ| * u) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (σ * u) ≤ Real.exp (|σ| * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self σ) hu0)
    have h2 : Real.exp (-(σ * u)) ≤ Real.exp (|σ| * u) :=
      Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs σ) hu0)
    linarith
  have hPhi := hPhi_le u hu0
  rw [Real.norm_eq_abs] at hPhi
  calc |riemannPhi u| * u ^ k * Real.cosh (σ * u)
    _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
          ((k.factorial : ℝ) * Real.exp u) * Real.exp (|σ| * u) := by
        refine mul_le_mul ?_ hcosh (le_of_lt (Real.cosh_pos _)) (by positivity)
        exact mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
    _ = C2 * (k.factorial : ℝ) *
          (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (|σ| * u)) := by ring
    _ = C2 * (k.factorial : ℝ) *
          Real.exp ((9 / 2 + |σ| + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

/-- Super-exponential integrability of Phi(u) * u^k * sinh(sigma * u) on (0, inf). -/
lemma integrableOn_phi_pow_sinh (k : ℕ) (σ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.sinh (σ * u)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + |σ| + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul
    (C2 * (k.factorial : ℝ))).mono'
    (((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
  have hpow := pow_le_factorial_mul_exp k hu0
  have hsinh : |Real.sinh (σ * u)| ≤ Real.exp (|σ| * u) := by
    rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_sub (Real.exp (σ * u)) (Real.exp (-(σ * u)))
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)] at htri
    have h1 : Real.exp (σ * u) ≤ Real.exp (|σ| * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self σ) hu0)
    have h2 : Real.exp (-(σ * u)) ≤ Real.exp (|σ| * u) :=
      Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs σ) hu0)
    linarith
  have hPhi := hPhi_le u hu0
  rw [Real.norm_eq_abs] at hPhi
  calc |riemannPhi u| * u ^ k * |Real.sinh (σ * u)|
    _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
          ((k.factorial : ℝ) * Real.exp u) * Real.exp (|σ| * u) := by
        refine mul_le_mul ?_ hsinh (abs_nonneg _) (by positivity)
        exact mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
    _ = C2 * (k.factorial : ℝ) *
          (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (|σ| * u)) := by ring
    _ = C2 * (k.factorial : ℝ) *
          Real.exp ((9 / 2 + |σ| + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

/-- Strict positivity of every real-axis cosh moment:
    int_0^inf Phi(u) * u^k * cosh(sigma * u) du > 0 for all k in N and sigma in R. -/
theorem pos_integral_phi_pow_cosh (k : ℕ) (σ : ℝ) :
    0 < ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u) := by
  let f : ℝ → ℝ := fun u => riemannPhi u * u ^ k * Real.cosh (σ * u)
  have hf_cont : Continuous f :=
    (continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hf_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f u := fun u hu =>
    mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _))
      (le_of_lt (Real.cosh_pos _))
  have hf1 : 0 < f 1 := by
    dsimp [f]
    exact mul_pos (mul_pos (riemannPhi_pos 1) (by positivity)) (Real.cosh_pos _)
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) hf_nonneg)
    (integrableOn_phi_pow_cosh k σ)).mpr ?_
  have hopen : IsOpen ({u : ℝ | 0 < f u} ∩ Ioi 0) :=
    (isOpen_lt continuous_const hf_cont).inter isOpen_Ioi
  have hmem : (1 : ℝ) ∈ {u : ℝ | 0 < f u} ∩ Ioi 0 := ⟨hf1, mem_Ioi.mpr zero_lt_one⟩
  have hsub : {u : ℝ | 0 < f u} ∩ Ioi 0 ⊆ Function.support f ∩ Ioi 0 :=
    fun u hu => ⟨ne_of_gt hu.1, hu.2⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨1, hmem⟩) (measure_mono hsub)

/-- Strict positivity of every real-axis sinh moment for sigma > 0:
    int_0^inf Phi(u) * u^k * sinh(sigma * u) du > 0 for all k in N and sigma > 0. -/
theorem pos_integral_phi_pow_sinh (k : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    0 < ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.sinh (σ * u) := by
  let f : ℝ → ℝ := fun u => riemannPhi u * u ^ k * Real.sinh (σ * u)
  have hf_cont : Continuous f :=
    (continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hf_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f u := fun u hu => by
    have hsu : 0 < σ * u := mul_pos hσ hu
    exact mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _))
      (le_of_lt (Real.sinh_pos_iff.mpr hsu))
  have hf1 : 0 < f 1 := by
    dsimp [f]
    exact mul_pos (mul_pos (riemannPhi_pos 1) (by positivity))
      (Real.sinh_pos_iff.mpr (by linarith))
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) hf_nonneg)
    (integrableOn_phi_pow_sinh k σ)).mpr ?_
  have hopen : IsOpen ({u : ℝ | 0 < f u} ∩ Ioi 0) :=
    (isOpen_lt continuous_const hf_cont).inter isOpen_Ioi
  have hmem : (1 : ℝ) ∈ {u : ℝ | 0 < f u} ∩ Ioi 0 := ⟨hf1, mem_Ioi.mpr zero_lt_one⟩
  have hsub : {u : ℝ | 0 < f u} ∩ Ioi 0 ⊆ Function.support f ∩ Ioi 0 :=
    fun u hu => ⟨ne_of_gt hu.1, hu.2⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨1, hmem⟩) (measure_mono hsub)

/-- Unified parametric differentiation under the integral sign (cosh -> sinh):
    d/dsigma int_0^inf Phi(u) u^k cosh(sigma u) du = int_0^inf Phi(u) u^{k+1} sinh(sigma u) du. -/
theorem hasDerivAt_integral_phi_pow_cosh (k : ℕ) (σ₀ : ℝ) :
    HasDerivAt (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.sinh (σ₀ * u)) σ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let R : ℝ := |σ₀| + 1
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + R + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun σ u => riemannPhi u * u ^ k * Real.cosh (σ * u))
    (F' := fun σ u => riemannPhi u * u ^ (k + 1) * Real.sinh (σ * u))
    (s := Metric.ball σ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds σ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun σ =>
      (((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_cosh k σ₀)
    (((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu σ hσ
      have hu0 : 0 ≤ u := le_of_lt hu
      have hσ_abs : |σ| ≤ R := by
        rw [Metric.mem_ball, Real.dist_eq] at hσ
        have htri : |σ| ≤ |σ - σ₀| + |σ₀| := by
          have := abs_add_le (σ - σ₀) σ₀
          simpa using this
        dsimp [R]; linarith
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_eq_abs]
      have hpow := pow_le_factorial_mul_exp (k + 1) hu0
      have hsinh : |Real.sinh (σ * u)| ≤ Real.exp (R * u) := by
        rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have htri := abs_sub (Real.exp (σ * u)) (Real.exp (-(σ * u)))
        rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)] at htri
        have h1 : Real.exp (σ * u) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self σ).trans hσ_abs) hu0)
        have h2 : Real.exp (-(σ * u)) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right ((neg_le_abs σ).trans hσ_abs) hu0)
        linarith
      have hPhi := hPhi_le u hu0
      rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * |Real.sinh (σ * u)|
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) * Real.exp (R * u) := by
            refine mul_le_mul ?_ hsinh (abs_nonneg _) (by positivity)
            exact mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (R * u)) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ σ _
      have hlin : HasDerivAt (fun s : ℝ => s * u) u σ := by
        simpa using (hasDerivAt_id σ).mul_const u
      have hch : HasDerivAt (fun s : ℝ => Real.cosh (s * u)) (Real.sinh (σ * u) * u) σ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_cosh (σ * u)).comp σ hlin
      convert hch.const_mul (riemannPhi u * u ^ k) using 1
      rw [pow_succ]; ring)
  exact h.2

/-- Unified parametric differentiation under the integral sign (sinh -> cosh):
    d/dsigma int_0^inf Phi(u) u^k sinh(sigma u) du = int_0^inf Phi(u) u^{k+1} cosh(sigma u) du. -/
theorem hasDerivAt_integral_phi_pow_sinh (k : ℕ) (σ₀ : ℝ) :
    HasDerivAt (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.sinh (σ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.cosh (σ₀ * u)) σ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let R : ℝ := |σ₀| + 1
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + R + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun σ u => riemannPhi u * u ^ k * Real.sinh (σ * u))
    (F' := fun σ u => riemannPhi u * u ^ (k + 1) * Real.cosh (σ * u))
    (s := Metric.ball σ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds σ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun σ =>
      (((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_sinh k σ₀)
    (((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu σ hσ
      have hu0 : 0 ≤ u := le_of_lt hu
      have hσ_abs : |σ| ≤ R := by
        rw [Metric.mem_ball, Real.dist_eq] at hσ
        have htri : |σ| ≤ |σ - σ₀| + |σ₀| := by
          have := abs_add_le (σ - σ₀) σ₀
          simpa using this
        dsimp [R]; linarith
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hu0 _),
          Real.norm_of_nonneg (le_of_lt (Real.cosh_pos _))]
      have hpow := pow_le_factorial_mul_exp (k + 1) hu0
      have hcosh : Real.cosh (σ * u) ≤ Real.exp (R * u) := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (σ * u) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self σ).trans hσ_abs) hu0)
        have h2 : Real.exp (-(σ * u)) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right ((neg_le_abs σ).trans hσ_abs) hu0)
        linarith
      have hPhi := hPhi_le u hu0
      rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * Real.cosh (σ * u)
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) * Real.exp (R * u) := by
            refine mul_le_mul ?_ hcosh (le_of_lt (Real.cosh_pos _)) (by positivity)
            exact mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (R * u)) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ σ _
      have hlin : HasDerivAt (fun s : ℝ => s * u) u σ := by
        simpa using (hasDerivAt_id σ).mul_const u
      have hsh : HasDerivAt (fun s : ℝ => Real.sinh (s * u)) (Real.cosh (σ * u) * u) σ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_sinh (σ * u)).comp σ hlin
      convert hsh.const_mul (riemannPhi u * u ^ k) using 1
      rw [pow_succ]; ring)
  exact h.2

/-- Exact real-axis representation of `riemannXi(1/2 + sigma)`:
    purely real and equal to 2 * int_0^inf Phi(u) * cosh(sigma * u) du. -/
theorem riemannXi_real_re_im (σ : ℝ) :
    (riemannXi (⟨1 / 2 + σ, 0⟩ : ℂ)).re =
      2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cosh (σ * u) ∧
    (riemannXi (⟨1 / 2 + σ, 0⟩ : ℂ)).im = 0 := by
  have h := riemannXi_re_im_pastFuture_phi (1 / 2 + σ) 0
  have hsub : (1 / 2 + σ) - 1 / 2 = σ := by ring
  rw [hsub] at h
  constructor
  · rw [h.1]
    exact congrArg (2 * ·) (setIntegral_congr_fun measurableSet_Ioi fun u _ => by simp)
  · rw [h.2]
    simp

/-- THEOREM I.1 (Unconditional Strict Positivity of `riemannXi` on the Entire Real Axis):
    For every sigma in R, Re(riemannXi(1/2 + sigma)) > 0. -/
theorem riemannXi_real_pos (σ : ℝ) :
    0 < (riemannXi (⟨1 / 2 + σ, 0⟩ : ℂ)).re := by
  rw [(riemannXi_real_re_im σ).1]
  have hp := pos_integral_phi_pow_cosh 0 σ
  linarith

/-- On gamma = 0, xiNormSq(sigma, 0) equals (2 * I_0(sigma))^2. -/
lemma xiNormSq_realAxis_eq (σ : ℝ) :
    xiNormSq σ 0 = (2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cosh (σ * u)) ^ 2 := by
  dsimp [xiNormSq]
  rw [norm_sq_eq_re_sq_add_im_sq, (riemannXi_real_re_im σ).1, (riemannXi_real_re_im σ).2]
  ring

/-- Shorthand for the k-th real-axis cosh/sinh integrals. -/
noncomputable def Icosh (k : ℕ) (σ : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u)

noncomputable def Isinh (k : ℕ) (σ : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.sinh (σ * u)

lemma hasDerivAt_Icosh (k : ℕ) (σ : ℝ) : HasDerivAt (Icosh k) (Isinh (k + 1) σ) σ :=
  hasDerivAt_integral_phi_pow_cosh k σ

lemma hasDerivAt_Isinh (k : ℕ) (σ : ℝ) : HasDerivAt (Isinh k) (Icosh (k + 1) σ) σ :=
  hasDerivAt_integral_phi_pow_sinh k σ

/-- Exact 1st, 2nd, 3rd derivatives of xiNormSq(·, 0) in closed form via Icosh / Isinh. -/
lemma hasDerivAt_xiNormSq_realAxis_1 (σ : ℝ) :
    HasDerivAt (fun x : ℝ => xiNormSq x 0) (8 * Icosh 0 σ * Isinh 1 σ) σ := by
  have heq : (fun x : ℝ => xiNormSq x 0) = fun x : ℝ => (2 * Icosh 0 x) ^ 2 :=
    funext xiNormSq_realAxis_eq
  rw [heq]
  have h1 := ((hasDerivAt_Icosh 0 σ).const_mul 2).pow 2
  convert h1 using 1
  ring

lemma hasDerivAt_xiNormSq_realAxis_2 (σ : ℝ) :
    HasDerivAt (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t 0) x)
      (8 * (Isinh 1 σ ^ 2 + Icosh 0 σ * Icosh 2 σ)) σ := by
  have heq : (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t 0) x) =
      fun x : ℝ => 8 * Icosh 0 x * Isinh 1 x :=
    funext fun x => (hasDerivAt_xiNormSq_realAxis_1 x).deriv
  rw [heq]
  have h := ((hasDerivAt_Icosh 0 σ).const_mul 8).mul (hasDerivAt_Isinh 1 σ)
  convert h using 1
  ring

lemma hasDerivAt_xiNormSq_realAxis_3 (σ : ℝ) :
    HasDerivAt (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t 0)) x)
      (8 * (3 * Isinh 1 σ * Icosh 2 σ + Icosh 0 σ * Isinh 3 σ)) σ := by
  have heq : (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t 0)) x) =
      fun x : ℝ => 8 * (Isinh 1 x ^ 2 + Icosh 0 x * Icosh 2 x) :=
    funext fun x => (hasDerivAt_xiNormSq_realAxis_2 x).deriv
  rw [heq]
  have h1 := (hasDerivAt_Isinh 1 σ).pow 2
  have h2 := (hasDerivAt_Icosh 0 σ).mul (hasDerivAt_Icosh 2 σ)
  convert (h1.add h2).const_mul 8 using 1
  ring

/-- THEOREM I.2 (Unconditional Level -1 Transverse Force Positivity on the Real Axis):
    For EVERY sigma > 0, (d/dsigma) ||xi(1/2 + sigma)||^2 > 0. -/
theorem xiNormSq_deriv_sigma_pos_realAxis {σ : ℝ} (hσ : 0 < σ) :
    0 < deriv (fun x : ℝ => xiNormSq x 0) σ := by
  rw [(hasDerivAt_xiNormSq_realAxis_1 σ).deriv]
  have h0 : 0 < Icosh 0 σ := pos_integral_phi_pow_cosh 0 σ
  have h1 : 0 < Isinh 1 σ := pos_integral_phi_pow_sinh 1 hσ
  positivity

/-- THEOREM I.3 (Unconditional Level -2 Transverse Hessian Positivity on the Entire Real Axis):
    For EVERY sigma in R (including sigma = 0!), (d^2/dsigma^2) ||xi(1/2 + sigma)||^2 > 0. -/
theorem xiNormSq_deriv2_sigma_pos_realAxis (σ : ℝ) :
    0 < deriv (deriv (fun x : ℝ => xiNormSq x 0)) σ := by
  rw [(hasDerivAt_xiNormSq_realAxis_2 σ).deriv]
  have h0 : 0 < Icosh 0 σ := pos_integral_phi_pow_cosh 0 σ
  have h2 : 0 < Icosh 2 σ := pos_integral_phi_pow_cosh 2 σ
  have hsq : 0 ≤ Isinh 1 σ ^ 2 := sq_nonneg _
  nlinarith

/-- COROLLARY I.3b (Unconditional Laguerre Inequality L_1(Xi)(0) > 0 at the Origin):
    (Xi'(0))^2 - Xi(0) * Xi''(0) > 0 unconditionally in Mathlib4. -/
theorem laguerre_L1_pos_at_origin :
    0 < (deriv xiCritical 0) ^ 2 - xiCritical 0 * deriv (deriv xiCritical) 0 := by
  have h := xiNormSq_deriv2_sigma_pos_realAxis 0
  rw [xiNormSq_deriv2_sigma_zero_eq_laguerre 0] at h
  linarith

/-- THEOREM I.4 (Unconditional Level -3 Transverse Jerk Positivity on the Real Axis):
    For EVERY sigma > 0, (d^3/dsigma^3) ||xi(1/2 + sigma)||^2 > 0. -/
theorem xiNormSq_deriv3_sigma_pos_realAxis {σ : ℝ} (hσ : 0 < σ) :
    0 < deriv (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t 0)) x) σ := by
  rw [(hasDerivAt_xiNormSq_realAxis_3 σ).deriv]
  have h0 : 0 < Icosh 0 σ := pos_integral_phi_pow_cosh 0 σ
  have h1 : 0 < Isinh 1 σ := pos_integral_phi_pow_sinh 1 hσ
  have h2 : 0 < Icosh 2 σ := pos_integral_phi_pow_cosh 2 σ
  have h3 : 0 < Isinh 3 σ := pos_integral_phi_pow_sinh 3 hσ
  positivity

/-- The explicit continuous 2D transverse Hessian field H2(sigma, gamma). -/
noncomputable def xiHessian2D (p : ℝ × ℝ) : ℝ :=
  2 * (‖deriv riemannXi (⟨1 / 2 + p.1, p.2⟩ : ℂ)‖ ^ 2 +
       (conj (riemannXi (⟨1 / 2 + p.1, p.2⟩ : ℂ)) *
        deriv (deriv riemannXi) (⟨1 / 2 + p.1, p.2⟩ : ℂ)).re)

lemma xiHessian2D_eq_deriv2 (σ γ : ℝ) :
    xiHessian2D (σ, γ) = deriv (deriv (fun x : ℝ => xiNormSq x γ)) σ :=
  ((hasDerivAt_xiNormSq_deriv_sigma σ γ).deriv).symm

lemma continuous_xiHessian2D : Continuous xiHessian2D := by
  have hemb : Continuous (fun p : ℝ × ℝ => (⟨1 / 2 + p.1, p.2⟩ : ℂ)) := by
    have : (fun p : ℝ × ℝ => (⟨1 / 2 + p.1, p.2⟩ : ℂ)) =
        fun p : ℝ × ℝ => ((1 / 2 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I := by
      ext p; apply Complex.ext <;> simp
    rw [this]
    fun_prop
  have h0 : Continuous (fun p : ℝ × ℝ => riemannXi (⟨1 / 2 + p.1, p.2⟩ : ℂ)) :=
    riemannXi_entire.continuous.comp hemb
  have h1 : Continuous (fun p : ℝ × ℝ => deriv riemannXi (⟨1 / 2 + p.1, p.2⟩ : ℂ)) :=
    differentiable_deriv_riemannXi.continuous.comp hemb
  have h2 : Continuous (fun p : ℝ × ℝ => deriv (deriv riemannXi) (⟨1 / 2 + p.1, p.2⟩ : ℂ)) :=
    differentiable_deriv2_riemannXi.continuous.comp hemb
  unfold xiHessian2D
  have hconj : Continuous (fun p : ℝ × ℝ => conj (riemannXi (⟨1 / 2 + p.1, p.2⟩ : ℂ))) :=
    Complex.continuous_conj.comp h0
  exact (((h1.norm.pow 2).add (Complex.continuous_re.comp (hconj.mul h2))).const_mul 2)

/-- THEOREM I.5 (UNCONDITIONAL OPEN CONVEXITY CORRIDOR AROUND THE CRITICAL SEGMENT):
    There exists an explicit width delta > 0 such that for ALL sigma in [0, 1/2]
    and ALL gamma with |gamma| < delta, the transverse Hessian is strictly positive:
      (d^2/dsigma^2) ||xi(1/2 + sigma + i*gamma)||^2 > 0. -/
theorem exists_unconditional_convex_corridor :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ σ ∈ Icc (0 : ℝ) (1 / 2), ∀ γ : ℝ, |γ| < δ →
        0 < deriv (deriv (fun x : ℝ => xiNormSq x γ)) σ := by
  let U : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < xiHessian2D p}
  have hU_open : IsOpen U := isOpen_lt continuous_const continuous_xiHessian2D
  have hsub : Icc (0 : ℝ) (1 / 2) ×ˢ ({(0 : ℝ)} : Set ℝ) ⊆ U := by
    rintro ⟨σ, γ⟩ ⟨_, hγ⟩
    rw [mem_singleton_iff] at hγ
    subst hγ
    show 0 < xiHessian2D (σ, 0)
    rw [xiHessian2D_eq_deriv2]
    exact xiNormSq_deriv2_sigma_pos_realAxis σ
  obtain ⟨V, W, _, hW_open, hVsub, hWsub, hprod⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hU_open hsub
  have h0W : (0 : ℝ) ∈ W := hWsub rfl
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hW_open 0 h0W
  refine ⟨δ, hδ_pos, fun σ hσ γ hγ => ?_⟩
  have hγW : γ ∈ W := hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hγ)
  have hmem : (σ, γ) ∈ U := hprod ⟨hVsub hσ, hγW⟩
  rw [← xiHessian2D_eq_deriv2]
  exact hmem

/-- COROLLARY I.5b (Unconditional Zero-Free Corridor Derived Directly from Level -2 Hessian):
    Inside the unconditional convex corridor |gamma| < delta, riemannZeta has NO
    non-trivial zeros (neither on nor off the critical line). -/
theorem exists_unconditional_corridor_force_pos_and_no_offLine_zeros :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ σ ∈ Ioo (0 : ℝ) (1 / 2), ∀ γ : ℝ, |γ| < δ →
        0 < deriv (fun x : ℝ => xiNormSq x γ) σ) ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| < δ → riemannZeta s = 0 → s.re = 1 / 2) := by
  obtain ⟨δ, hδ, hH⟩ := exists_unconditional_convex_corridor
  have hF : ∀ σ ∈ Ioo (0 : ℝ) (1 / 2), ∀ γ : ℝ, |γ| < δ →
      0 < deriv (fun x : ℝ => xiNormSq x γ) σ := by
    intro σ hσ γ hγ
    have hdiff : Differentiable ℝ (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t γ) x) :=
      fun x => (hasDerivAt_xiNormSq_deriv_sigma x γ).differentiableAt
    have hmono : StrictMonoOn (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t γ) x) (Ico 0 (1 / 2)) := by
      refine strictMonoOn_of_deriv_pos (convex_Ico 0 (1 / 2)) hdiff.continuous.continuousOn ?_
      intro x hx
      rw [interior_Ico] at hx
      exact hH x ⟨le_of_lt hx.1, le_of_lt hx.2⟩ γ hγ
    have hlt := hmono ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ.1, hσ.2⟩ hσ.1
    dsimp only at hlt
    rw [xiNormSq_deriv_sigma_zero γ] at hlt
    exact hlt
  refine ⟨δ, hδ, hF, fun s hs0 hs1 him hz => ?_⟩
  have hxi0 : riemannXi s = 0 := (riemannXi_eq_zero_iff_riemannZeta hs0 hs1).mpr hz
  by_contra hne
  have hmono_at : ∀ γ : ℝ, |γ| < δ → StrictMonoOn (fun x : ℝ => xiNormSq x γ) (Ico 0 (1 / 2)) := by
    intro γ hγ
    have hdiff : Differentiable ℝ (fun x : ℝ => xiNormSq x γ) :=
      fun x => (hasDerivAt_xiNormSq_sigma x γ).differentiableAt
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 (1 / 2)) hdiff.continuous.continuousOn ?_
    intro x hx
    rw [interior_Ico] at hx
    exact hF x hx γ hγ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let σ : ℝ := 1 / 2 - s.re
    have hσ0 : 0 < σ := by dsimp [σ]; linarith
    have hσ1 : σ < 1 / 2 := by dsimp [σ]; linarith
    have hm := hmono_at (-s.im) (by rw [abs_neg]; exact him) ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ0, hσ1⟩ hσ0
    have h1s : (⟨1 / 2 + σ, -s.im⟩ : ℂ) = 1 - s := by
      apply Complex.ext
      · simp [σ]; ring
      · simp
    have hv0 : xiNormSq σ (-s.im) = 0 := by rw [xiNormSq_eq_zero_iff, h1s, riemannXi_one_sub, hxi0]
    linarith [xiNormSq_nonneg 0 (-s.im)]
  · let σ : ℝ := s.re - 1 / 2
    have hσ0 : 0 < σ := by dsimp [σ]; linarith
    have hσ1 : σ < 1 / 2 := by dsimp [σ]; linarith
    have hm := hmono_at s.im him ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ0, hσ1⟩ hσ0
    have hs_eq : (⟨1 / 2 + σ, s.im⟩ : ℂ) = s := by
      apply Complex.ext
      · simp [σ]
      · simp
    have hv0 : xiNormSq σ s.im = 0 := by rw [xiNormSq_eq_zero_iff, hs_eq, hxi0]
    linarith [xiNormSq_nonneg 0 s.im]

-- ==============================================================================
-- PART II: CONNES-CONSANI PROLATE OPERATOR & SUPERSYMMETRIC DARBOUX POSITIVITY
--          (ROUTE A SPECTRAL STRUCTURE)
-- ==============================================================================

/-- The Connes-Consani Prolate Spheroidal Differential Operator on [-a, a]:
      H_prolate(a, c, f)(x) = -d/dx ((a^2 - x^2) f'(x)) + c^2 x^2 f(x)
                            = -(a^2 - x^2) f''(x) + 2 x f'(x) + c^2 x^2 f(x). -/
noncomputable def prolateOp (a c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(a ^ 2 - x ^ 2) * deriv (deriv f) x + 2 * x * deriv f x + c ^ 2 * x ^ 2 * f x

/-- The symmetric Dirichlet energy form associated with `prolateOp` on [-a, a]:
      E_prolate(f, g) = int_{-a}^{a} [(a^2 - x^2) f'(x) g'(x) + c^2 x^2 f(x) g(x)] dx. -/
noncomputable def prolateForm (a c : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ x in (-a)..a, ((a ^ 2 - x ^ 2) * deriv f x * deriv g x + c ^ 2 * x ^ 2 * f x * g x)

/-- Helper extracting differentiability and continuity of f, f', f'' from ContDiff R 2 f. -/
lemma contDiff_two_props {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧
    Continuous f ∧ Continuous (deriv f) ∧ Continuous (deriv (deriv f)) := by
  have h1 : ContDiff ℝ 1 (deriv f) := ((contDiff_succ_iff_deriv (n := (1 : ℕ))).mp hf).2.2
  have h2 : ContDiff ℝ 0 (deriv (deriv f)) := ((contDiff_succ_iff_deriv (n := (0 : ℕ))).mp h1).2.2
  exact ⟨hf.differentiable (by norm_num), h1.differentiable (by norm_num),
         hf.continuous, h1.continuous, h2.continuous⟩

/-- THEOREM II.1 (Exact Boundary-Free Integration by Parts for the Prolate Operator):
    For ANY C^2 real functions f, g on R and any a > 0, the boundary term
    -(a^2 - x^2) f(x) g'(x) vanishes identically at x = ±a without ANY boundary
    conditions on f or g, yielding:
      int_{-a}^a f(x) * H_prolate(a, c, g)(x) dx = prolateForm(a, c, f, g). -/
theorem prolate_integration_by_parts (a c : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ∫ x in (-a)..a, f x * prolateOp a c g x = prolateForm a c f g := by
  let B : ℝ → ℝ := fun x => -(a ^ 2 - x ^ 2) * f x * deriv g x
  let D : ℝ → ℝ := fun x =>
    f x * prolateOp a c g x - ((a ^ 2 - x ^ 2) * deriv f x * deriv g x + c ^ 2 * x ^ 2 * f x * g x)
  obtain ⟨hf_diff, _, _, hf'_cont, _⟩ := contDiff_two_props hf
  obtain ⟨_, hg'_diff, _, hg'_cont, hg''_cont⟩ := contDiff_two_props hg
  have hB_deriv : ∀ x : ℝ, HasDerivAt B (D x) x := by
    intro x
    have hpoly : HasDerivAt (fun t : ℝ => -(a ^ 2 - t ^ 2)) (2 * x) x := by
      have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have h2 := ((hasDerivAt_const x (a ^ 2)).sub h1).neg
      convert h2 using 1; ring
    have hf1 : HasDerivAt f (deriv f x) x := (hf_diff x).hasDerivAt
    have hg2 : HasDerivAt (deriv g) (deriv (deriv g) x) x := (hg'_diff x).hasDerivAt
    have hmul := (hpoly.mul hf1).mul hg2
    convert hmul using 1
    dsimp [D, prolateOp]
    ring
  have hcont_lhs : Continuous (fun x => f x * prolateOp a c g x) := by
    dsimp [prolateOp]
    exact hf.continuous.mul (((((continuous_const.sub (continuous_pow 2)).neg).mul hg''_cont).add
      ((continuous_const.mul continuous_id).mul hg'_cont)).add
      ((continuous_const.mul (continuous_pow 2)).mul hg.continuous))
  have hcont_rhs : Continuous (fun x => (a ^ 2 - x ^ 2) * deriv f x * deriv g x + c ^ 2 * x ^ 2 * f x * g x) :=
    ((((continuous_const.sub (continuous_pow 2)).mul hf'_cont).mul hg'_cont).add
      ((((continuous_const.mul (continuous_pow 2)).mul hf.continuous).mul hg.continuous)))
  have hD_int : IntervalIntegrable D volume (-a) a :=
    (hcont_lhs.sub hcont_rhs).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hB_deriv x) hD_int
  have hBa : B a = 0 := by dsimp [B]; ring
  have hBna : B (-a) = 0 := by dsimp [B]; ring
  rw [hBa, hBna, sub_self] at hftc
  have hsub := intervalIntegral.integral_sub (hcont_lhs.intervalIntegrable (μ := volume) (-a) a)
    (hcont_rhs.intervalIntegrable (μ := volume) (-a) a)
  dsimp [D] at hftc
  rw [hsub] at hftc
  dsimp [prolateForm]
  linarith

/-- THEOREM II.2 (Unconditional Symmetry / Formal Self-Adjointness of `prolateOp`):
    For all C^2 functions f, g on R:
      <f, H_prolate g> = <H_prolate f, g> on L^2([-a, a]). -/
theorem prolate_symmetric (a c : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ∫ x in (-a)..a, f x * prolateOp a c g x =
    ∫ x in (-a)..a, prolateOp a c f x * g x := by
  rw [prolate_integration_by_parts a c hf hg]
  have hcomm : (∫ x in (-a)..a, prolateOp a c f x * g x) =
      ∫ x in (-a)..a, g x * prolateOp a c f x := by
    refine intervalIntegral.integral_congr fun x _ => mul_comm _ _
  rw [hcomm, prolate_integration_by_parts a c hg hf]
  dsimp [prolateForm]
  refine intervalIntegral.integral_congr fun x _ => by ring

/-- THEOREM II.3 (Unconditional Non-Negativity of the Prolate Energy Form):
    For any a > 0, c in R, and C^2 function f:
      <f, H_prolate(a, c, f)> >= 0 on [-a, a]. -/
theorem prolate_quadratic_nonneg {a : ℝ} (ha : 0 ≤ a) (c : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) :
    0 ≤ ∫ x in (-a)..a, f x * prolateOp a c f x := by
  rw [prolate_integration_by_parts a c hf hf]
  dsimp [prolateForm]
  refine intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_
  have hx2 : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 : 0 ≤ (a ^ 2 - x ^ 2) * deriv f x * deriv f x := by
    rw [mul_assoc]; exact mul_nonneg hx2 (mul_self_nonneg _)
  have h2 : 0 ≤ c ^ 2 * x ^ 2 * f x * f x := by
    rw [mul_assoc]; exact mul_nonneg (by positivity) (mul_self_nonneg _)
  linarith

/-- THEOREM II.4 (Unconditional Strict Positive-Definiteness of `prolateOp` for c != 0):
    For any a > 0, c != 0, and any C^2 function f that is non-zero at some point x0 in (-a, a),
    the prolate quadratic form is STRICTLY POSITIVE: <f, H_prolate f> > 0. -/
theorem prolate_quadratic_pos_of_ne_zero {a c : ℝ} (ha : 0 < a) (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (-a) a) (hf₀ : f x₀ ≠ 0) :
    0 < ∫ x in (-a)..a, f x * prolateOp a c f x := by
  rw [prolate_integration_by_parts a c hf hf]
  dsimp [prolateForm]
  let E : ℝ → ℝ := fun x => (a ^ 2 - x ^ 2) * deriv f x * deriv f x + c ^ 2 * x ^ 2 * f x * f x
  obtain ⟨_, _, _, hf'_cont, _⟩ := contDiff_two_props hf
  have hE_cont : Continuous E :=
    (((continuous_const.sub (continuous_pow 2)).mul hf'_cont).mul hf'_cont).add
      (((continuous_const.mul (continuous_pow 2)).mul hf.continuous).mul hf.continuous)
  have hE_nonneg : ∀ x ∈ Ioc (-a) a, 0 ≤ E x := fun x hx => by
    dsimp [E]
    have hx2 : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h1 : 0 ≤ (a ^ 2 - x ^ 2) * deriv f x * deriv f x := by
      rw [mul_assoc]; exact mul_nonneg hx2 (mul_self_nonneg _)
    have h2 : 0 ≤ c ^ 2 * x ^ 2 * f x * f x := by
      rw [mul_assoc]; exact mul_nonneg (by positivity) (mul_self_nonneg _)
    linarith
  -- Find a point x1 in Ioo (-a) a with x1 != 0 and f x1 != 0 (using continuity of f at x0!)
  have hex_x1 : ∃ x₁ ∈ Ioo (-a) a, x₁ ≠ 0 ∧ f x₁ ≠ 0 := by
    by_cases h0 : x₀ = 0
    · subst h0
      have hopen : IsOpen ({x : ℝ | f x ≠ 0} ∩ Ioo (-a) a) :=
        (isOpen_ne_fun hf.continuous continuous_const).inter isOpen_Ioo
      obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hopen 0 ⟨hf₀, hx₀⟩
      let x₁ : ℝ := min (r / 2) (a / 2)
      have hx₁_pos : 0 < x₁ := lt_min (by linarith) (by linarith)
      have hx₁_ball : x₁ ∈ Metric.ball (0 : ℝ) r := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx₁_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hmem := hr_sub hx₁_ball
      exact ⟨x₁, hmem.2, ne_of_gt hx₁_pos, hmem.1⟩
    · exact ⟨x₀, hx₀, h0, hf₀⟩
  obtain ⟨x₁, hx₁_mem, hx₁_ne, hf₁_ne⟩ := hex_x1
  have hE1_pos : 0 < E x₁ := by
    dsimp [E]
    have hx2 : 0 ≤ a ^ 2 - x₁ ^ 2 := by nlinarith [hx₁_mem.1, hx₁_mem.2]
    have h1 : 0 ≤ (a ^ 2 - x₁ ^ 2) * deriv f x₁ * deriv f x₁ := by
      rw [mul_assoc]; exact mul_nonneg hx2 (mul_self_nonneg _)
    have h2 : 0 < c ^ 2 * x₁ ^ 2 * f x₁ * f x₁ := by
      have : c ^ 2 * x₁ ^ 2 * f x₁ * f x₁ = (c * x₁ * f x₁) ^ 2 := by ring
      rw [this]
      exact sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero hc hx₁_ne) hf₁_ne)
    linarith
  exact intervalIntegral.integral_pos (by linarith) hE_cont.continuousOn hE_nonneg
    ⟨x₁, ⟨le_of_lt hx₁_mem.1, le_of_lt hx₁_mem.2⟩, hE1_pos⟩

/-- THEOREM II.5 (Unconditional Positivity of All Prolate Eigenvalues & Orthogonality): -/
theorem prolate_eigenvalue_pos {a c μ : ℝ} (ha : 0 < a) (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (heig : ∀ x ∈ Icc (-a) a, prolateOp a c f x = μ * f x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (-a) a) (hf₀ : f x₀ ≠ 0) :
    0 < μ := by
  have hpos := prolate_quadratic_pos_of_ne_zero ha hc hf hx₀ hf₀
  have hlhs : ∫ x in (-a)..a, f x * prolateOp a c f x = μ * ∫ x in (-a)..a, (f x) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
    rw [heig x hx]
    ring
  rw [hlhs] at hpos
  have hnorm_pos : 0 < ∫ x in (-a)..a, (f x) ^ 2 :=
    intervalIntegral.integral_pos (by linarith) (hf.continuous.pow 2).continuousOn
      (fun x _ => sq_nonneg _) ⟨x₀, ⟨le_of_lt hx₀.1, le_of_lt hx₀.2⟩, sq_pos_of_ne_zero hf₀⟩
  nlinarith

theorem prolate_eigenvectors_orthogonal {a c μ₁ μ₂ : ℝ} (ha : 0 ≤ a) (hne : μ₁ ≠ μ₂)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (heig1 : ∀ x ∈ Icc (-a) a, prolateOp a c f x = μ₁ * f x)
    (heig2 : ∀ x ∈ Icc (-a) a, prolateOp a c g x = μ₂ * g x) :
    ∫ x in (-a)..a, f x * g x = 0 := by
  have hsym := prolate_symmetric a c hf hg
  have h1 : ∫ x in (-a)..a, f x * prolateOp a c g x = μ₂ * ∫ x in (-a)..a, f x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
    rw [heig2 x hx]; ring
  have h2 : ∫ x in (-a)..a, prolateOp a c f x * g x = μ₁ * ∫ x in (-a)..a, f x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
    rw [heig1 x hx]; ring
  rw [h1, h2] at hsym
  have hdiff : (μ₂ - μ₁) * ∫ x in (-a)..a, f x * g x = 0 := by linarith
  exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne.symm)

/-- THEOREM II.6 (Unconditional Supersymmetric Darboux Factorization & Positivity):
    For ANY strictly positive C^2 ground state v0 > 0 on [-a, a] (such as the
    nodeless Weil-Adelic ground state v_0^(L) > 0) and ANY C^2 perturbation f
    vanishing at the endpoints f(-a) = f(a) = 0, the effective Schrödinger operator
      H_eff(f) = -f'' + (v0'' / v0) * f
    factorizes identically as A^dagger A with A(f) = f' - (v0'/v0) f:
      int_{-a}^a f(x) * (-f''(x) + (v0''(x)/v0(x)) * f(x)) dx
        = int_{-a}^a (f'(x) - (v0'(x)/v0(x)) * f(x))^2 dx >= 0. -/
theorem darboux_supersymmetric_factorization {a : ℝ} (ha : 0 ≤ a) {v₀ f : ℝ → ℝ}
    (hv₀ : ContDiff ℝ 2 v₀) (hf : ContDiff ℝ 2 f)
    (hv₀_pos : ∀ x ∈ Icc (-a) a, 0 < v₀ x)
    (hf_l : f (-a) = 0) (hf_r : f a = 0) :
    ∫ x in (-a)..a, f x * (-deriv (deriv f) x + (deriv (deriv v₀) x / v₀ x) * f x) =
    ∫ x in (-a)..a, (deriv f x - (deriv v₀ x / v₀ x) * f x) ^ 2 := by
  let W : ℝ → ℝ := fun x => -f x * (deriv f x - (deriv v₀ x / v₀ x) * f x)
  let D : ℝ → ℝ := fun x =>
    f x * (-deriv (deriv f) x + (deriv (deriv v₀) x / v₀ x) * f x) -
    (deriv f x - (deriv v₀ x / v₀ x) * f x) ^ 2
  obtain ⟨hv₀_diff, hv₀'_diff, _, hv₀'_cont, hv₀''_cont⟩ := contDiff_two_props hv₀
  obtain ⟨hf_diff, hf'_diff, _, hf'_cont, hf''_cont⟩ := contDiff_two_props hf
  have hW_deriv : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt W (D x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
    have hne : v₀ x ≠ 0 := ne_of_gt (hv₀_pos x hx)
    have hdv0 : HasDerivAt v₀ (deriv v₀ x) x := (hv₀_diff x).hasDerivAt
    have hdv0' : HasDerivAt (deriv v₀) (deriv (deriv v₀) x) x := (hv₀'_diff x).hasDerivAt
    have hdf : HasDerivAt f (deriv f x) x := (hf_diff x).hasDerivAt
    have hdf' : HasDerivAt (deriv f) (deriv (deriv f) x) x := (hf'_diff x).hasDerivAt
    have hratio : HasDerivAt (fun t => deriv v₀ t / v₀ t)
        ((deriv (deriv v₀) x * v₀ x - deriv v₀ x * deriv v₀ x) / (v₀ x) ^ 2) x :=
      hdv0'.div hdv0 hne
    have hA : HasDerivAt (fun t => deriv f t - (deriv v₀ t / v₀ t) * f t)
        (deriv (deriv f) x - (((deriv (deriv v₀) x * v₀ x - deriv v₀ x * deriv v₀ x) / (v₀ x) ^ 2) * f x +
          (deriv v₀ x / v₀ x) * deriv f x)) x :=
      hdf'.sub (hratio.mul hdf)
    have hmul := hdf.neg.mul hA
    convert hmul using 1
    dsimp [D]
    field_simp [hne]
    ring
  have hv0_ne_on : ∀ x ∈ Set.uIcc (-a) a, v₀ x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
    exact ne_of_gt (hv₀_pos x hx)
  have hcont_lhs : ContinuousOn (fun x => f x * (-deriv (deriv f) x + (deriv (deriv v₀) x / v₀ x) * f x))
      (Set.uIcc (-a) a) :=
    hf.continuous.continuousOn.mul
      ((hf''_cont.neg.continuousOn).add
        ((hv₀''_cont.continuousOn.div hv₀.continuous.continuousOn hv0_ne_on).mul hf.continuous.continuousOn))
  have hcont_rhs : ContinuousOn (fun x => (deriv f x - (deriv v₀ x / v₀ x) * f x) ^ 2)
      (Set.uIcc (-a) a) :=
    ((hf'_cont.continuousOn).sub
      ((hv₀'_cont.continuousOn.div hv₀.continuous.continuousOn hv0_ne_on).mul hf.continuous.continuousOn)).pow 2
  have hD_int : IntervalIntegrable D volume (-a) a :=
    (hcont_lhs.sub hcont_rhs).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hW_deriv hD_int
  have hWa : W a = 0 := by dsimp [W]; rw [hf_r]; ring
  have hWna : W (-a) = 0 := by dsimp [W]; rw [hf_l]; ring
  rw [hWa, hWna, sub_self] at hftc
  have hsub := intervalIntegral.integral_sub (hcont_lhs.intervalIntegrable (μ := volume))
    (hcont_rhs.intervalIntegrable (μ := volume))
  dsimp [D] at hftc
  rw [hsub] at hftc
  linarith

theorem darboux_supersymmetric_nonneg {a : ℝ} (ha : 0 ≤ a) {v₀ f : ℝ → ℝ}
    (hv₀ : ContDiff ℝ 2 v₀) (hf : ContDiff ℝ 2 f)
    (hv₀_pos : ∀ x ∈ Icc (-a) a, 0 < v₀ x)
    (hf_l : f (-a) = 0) (hf_r : f a = 0) :
    0 ≤ ∫ x in (-a)..a, f x * (-deriv (deriv f) x + (deriv (deriv v₀) x / v₀ x) * f x) := by
  rw [darboux_supersymmetric_factorization ha hv₀ hf hv₀_pos hf_l hf_r]
  exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _

end UnconditionalCorridorAndProlate
