/-
  ==============================================================================
  TRANSVERSE POTENTIAL CONVEXITY, CRITICAL-LINE LAGUERRE CURVATURE,
  2D PAST-FUTURE LIGHT-CONE ENERGY INTEGRAL, AND WEIERSTRASS MODULAR
  SCATTERING REDUCTION TO MATHLIB4 `RiemannHypothesis`

  Title: Differential Hierarchy of the Completed Zeta Energy Potential
         V(sigma, gamma) = ||xi(1/2 + sigma + i*gamma)||^2
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I:   Bilateral symmetry of V(sigma, gamma) = ||xi(1/2 + sigma + i*gamma)||^2:
              * `riemannXi_conj`: xi(conj s) = conj (xi s)
              * `riemannXi_ne_zero_of_one_le_re`: xi(s) != 0 for all Re(s) >= 1
              * `xiNormSq_even_sigma`: V(-sigma, gamma) = V(sigma, gamma)
              * `xiNormSq_even_gamma`: V(sigma, -gamma) = V(sigma, gamma)
  - Part II:  Exact Differential Hierarchy (1st, 2nd, 3rd Transverse Derivatives)
              and Subharmonicity Identity:
              * `hasDerivAt_xiNormSq_sigma`:
                  dV/dsigma = 2 * Re(conj(xi) * xi')
              * `xiNormSq_deriv_sigma_zero`:
                  (dV/dsigma)|_{sigma=0} = 0  (exact critical-line stationarity)
              * `hasDerivAt_xiNormSq_deriv_sigma`:
                  d^2V/dsigma^2 = 2 * (||xi'||^2 + Re(conj(xi) * xi''))
              * `xiNormSq_laplacian_eq`:
                  d^2V/dsigma^2 + d^2V/dgamma^2 = 4 * ||xi'||^2 >= 0
              * `xiNormSq_deriv2_sigma_zero_eq_laguerre`:
                  (d^2V/dsigma^2)|_{sigma=0} = 2 * ((Xi')^2 - Xi * Xi'')
                (exact identification of the critical-line transverse Hessian
                 with Laguerre's expression L_1(Xi)(gamma))
              * Critical-line geometry corollaries:
                  - Strictly positive valley curvature at every simple critical zero
                  - Strictly positive valley curvature at every local max of |Xi|
                  - Strictly negative ridge curvature at any non-zero local min of |Xi|
  - Part III: Exact 2D Past-Future Light-Cone Bilinear Energy Representation:
              * `xiNormSq_eq_pastFuture_double_integral`:
                  V(sigma, gamma) = 2 * int_0^inf int_0^inf Phi(u)*Phi(v) *
                    [cosh(sigma*(u+v))*cos(gamma*(u-v)) +
                     cosh(sigma*(u-v))*cos(gamma*(u+v))] dv du
  - Part IV:  Four-Level Differential Reduction Chain directly to Mathlib4
              official `RiemannHypothesis`:
              * `XiTransverseJerkPos` (3rd derivative > 0 & Laguerre >= 0)
                  -> `XiTransverseHessianPos` (2nd derivative > 0)
                  -> `XiTransverseForcePos` (1st derivative > 0)
                  -> `XiModulusStrictMono` (Sondow-Dumitrescu monotonicity)
                  -> `RiemannHypothesis`
                  <-> `SpectralBridgeTarget`
                  <-> `AdelicDipolarWeilPositivity`
  - Part V:   Weierstrass Modular Surface H/SL_2(Z) Scattering Matrix:
              * `modularScattering s := riemannXi (2 * s - 1) / riemannXi (2 * s)`
              * `modularScattering_norm_on_half`: exact unitarity ||phi(1/2 + i*t)|| = 1
              * `modularScattering_pole_iff_offLine_zero`: RH holds iff phi(s) is
                pole-free on the strip 1/4 < Re(s) < 1/2.
  ==============================================================================
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannDipolar.EulerAdelicBridge
import RiemannDipolar.PastFutureXiKernel

open Real Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate
open PastFutureXiKernel EulerAdelicBridge Mathlib4RiemannBridge UnconditionalMonopolarDivergence

namespace XiConvexityLaguerre

-- ==============================================================================
-- PART I: SYMMETRIES AND NON-VANISHING OF riemannXi AND V(sigma, gamma)
-- ==============================================================================

/-- The transverse energy potential on the critical strip:
    V(sigma, gamma) = ||xi(1/2 + sigma + i*gamma)||^2. -/
noncomputable def xiNormSq (σ γ : ℝ) : ℝ :=
  ‖riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)‖ ^ 2

/-- The real-valued critical-line profile Xi(gamma) = Re(xi(1/2 + i*gamma)). -/
noncomputable def xiCritical (γ : ℝ) : ℝ :=
  (riemannXi (⟨1 / 2, γ⟩ : ℂ)).re

/-- THEOREM I.1 (Schwarz Reflection Symmetry of `riemannXi`):
    For every s in C, riemannXi(conj s) = conj(riemannXi s). -/
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  have hcs : conj s = ⟨s.re, -s.im⟩ := by
    apply Complex.ext <;> simp
  have hre1 := (riemannXi_re_im_pastFuture_phi s.re (-s.im)).1
  have him1 := (riemannXi_re_im_pastFuture_phi s.re (-s.im)).2
  have hre2 := (riemannXi_re_im_pastFuture_phi s.re s.im).1
  have him2 := (riemannXi_re_im_pastFuture_phi s.re s.im).2
  rw [Complex.eta s] at hre2 him2
  rw [hcs]
  apply Complex.ext
  · rw [Complex.conj_re, hre1, hre2]
    exact congrArg (2 * ·) (setIntegral_congr_fun measurableSet_Ioi fun u _ => by rw [neg_mul, Real.cos_neg])
  · rw [Complex.conj_im, him1, him2]
    have hneg : (∫ u in Ioi (0 : ℝ), riemannPhi u * Real.sinh ((s.re - 1 / 2) * u) * Real.sin ((-s.im) * u)) =
        -(∫ u in Ioi (0 : ℝ), riemannPhi u * Real.sinh ((s.re - 1 / 2) * u) * Real.sin (s.im * u)) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [neg_mul, Real.sin_neg]
      ring
    rw [hneg]
    ring

/-- Value of `riemannXi` at s = 1: riemannXi(1) = 1/2 != 0. -/
theorem riemannXi_one : riemannXi 1 = (1 / 2 : ℂ) := by
  dsimp [riemannXi]
  simp

/-- THEOREM I.2 (Unconditional Non-Vanishing of `riemannXi` for Re(s) >= 1):
    For every s in C with 1 <= Re(s), riemannXi(s) != 0. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, riemannXi_one]
    norm_num
  · have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hre_pos : 0 < s.re := by linarith
    have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre_pos
    have hZ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannXi_eq_completedRiemannZeta hs0 hs1]
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hcomp : completedRiemannZeta s ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hdef
      exact hZ hdef
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1') hcomp

/-- THEOREM I.3 (Exact Bilateral Transverse Symmetry of V(sigma, gamma)):
    For all sigma, gamma in R, V(-sigma, gamma) = V(sigma, gamma). -/
theorem xiNormSq_even_sigma (σ γ : ℝ) : xiNormSq (-σ) γ = xiNormSq σ γ := by
  dsimp [xiNormSq]
  have h1 : (⟨1 / 2 + -σ, γ⟩ : ℂ) = 1 - conj (⟨1 / 2 + σ, γ⟩ : ℂ) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [h1, riemannXi_one_sub, riemannXi_conj, Complex.norm_conj]

/-- THEOREM I.4 (Exact Vertical Parity of V(sigma, gamma)):
    For all sigma, gamma in R, V(sigma, -gamma) = V(sigma, gamma). -/
theorem xiNormSq_even_gamma (σ γ : ℝ) : xiNormSq σ (-γ) = xiNormSq σ γ := by
  dsimp [xiNormSq]
  have h1 : (⟨1 / 2 + σ, -γ⟩ : ℂ) = conj (⟨1 / 2 + σ, γ⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [h1, riemannXi_conj, Complex.norm_conj]

/-- On the critical line sigma = 0, riemannXi(1/2 + i*gamma) is purely real. -/
theorem xiCritical_ofReal_eq (γ : ℝ) :
    ((xiCritical γ : ℝ) : ℂ) = riemannXi (⟨1 / 2, γ⟩ : ℂ) := by
  apply Complex.ext
  · simp [xiCritical]
  · rw [Complex.ofReal_im, riemannXi_im_half_eq_zero]

theorem xiNormSq_nonneg (σ γ : ℝ) : 0 ≤ xiNormSq σ γ :=
  sq_nonneg _

theorem xiNormSq_eq_zero_iff (σ γ : ℝ) :
    xiNormSq σ γ = 0 ↔ riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ) = 0 := by
  dsimp [xiNormSq]
  rw [sq_eq_zero_iff, norm_eq_zero]

-- ==============================================================================
-- PART II: EXACT DIFFERENTIAL HIERARCHY (m1, m2, m3), SUBHARMONICITY LAPLACIAN,
--          AND CRITICAL-LINE LAGUERRE CURVATURE IDENTITY
-- ==============================================================================

/-- Entireness of the first complex derivative `deriv riemannXi`. -/
lemma differentiable_deriv_riemannXi : Differentiable ℂ (deriv riemannXi) :=
  differentiableOn_univ.mp (riemannXi_entire.differentiableOn.deriv isOpen_univ)

/-- Entireness of the second complex derivative `deriv (deriv riemannXi)`. -/
lemma differentiable_deriv2_riemannXi : Differentiable ℂ (deriv (deriv riemannXi)) :=
  differentiableOn_univ.mp (differentiable_deriv_riemannXi.differentiableOn.deriv isOpen_univ)

/-- Helper: horizontal embedding σ ↦ ⟨1/2 + σ, γ⟩ has derivative 1. -/
lemma hasDerivAt_horiz (σ γ : ℝ) :
    HasDerivAt (fun x : ℝ => (⟨1 / 2 + x, γ⟩ : ℂ)) (1 : ℂ) σ := by
  have heq : (fun x : ℝ => (⟨1 / 2 + x, γ⟩ : ℂ)) =
      fun x : ℝ => ((1 / 2 : ℝ) : ℂ) + (x : ℂ) + (γ : ℂ) * Complex.I := by
    ext x
    apply Complex.ext <;> simp
  rw [heq]
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) σ := (hasDerivAt_id σ).ofReal_comp
  have h1 := ((hasDerivAt_const σ ((1 / 2 : ℝ) : ℂ)).add hx).add (hasDerivAt_const σ ((γ : ℂ) * Complex.I))
  convert h1 using 1
  ring

/-- Helper: vertical embedding γ ↦ ⟨1/2 + σ, γ⟩ has derivative I. -/
lemma hasDerivAt_vert (σ γ : ℝ) :
    HasDerivAt (fun y : ℝ => (⟨1 / 2 + σ, y⟩ : ℂ)) Complex.I γ := by
  have heq : (fun y : ℝ => (⟨1 / 2 + σ, y⟩ : ℂ)) =
      fun y : ℝ => ((1 / 2 + σ : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    ext y
    apply Complex.ext <;> simp
  rw [heq]
  have hy : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) γ := (hasDerivAt_id γ).ofReal_comp
  have h1 := (hasDerivAt_const γ ((1 / 2 + σ : ℝ) : ℂ)).add (hy.mul_const Complex.I)
  convert h1 using 1
  ring

/-- Clean horizontal composition using Mathlib's `HasFDerivAt.comp_hasDerivAt`. -/
lemma hasDerivAt_holo_horiz {f : ℂ → ℂ} (hf : Differentiable ℂ f) (σ γ : ℝ) :
    HasDerivAt (fun x : ℝ => f (⟨1 / 2 + x, γ⟩ : ℂ)) (deriv f (⟨1 / 2 + σ, γ⟩ : ℂ)) σ := by
  have h1 : HasDerivAt f (deriv f (⟨1 / 2 + σ, γ⟩ : ℂ)) (⟨1 / 2 + σ, γ⟩ : ℂ) :=
    (hf (⟨1 / 2 + σ, γ⟩ : ℂ)).hasDerivAt
  have h2 := (h1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt σ (hasDerivAt_horiz σ γ)
  simpa [Function.comp_def] using h2

/-- Clean vertical composition using `HasFDerivAt.comp_hasDerivAt`. -/
lemma hasDerivAt_holo_vert {f : ℂ → ℂ} (hf : Differentiable ℂ f) (σ γ : ℝ) :
    HasDerivAt (fun y : ℝ => f (⟨1 / 2 + σ, y⟩ : ℂ)) (deriv f (⟨1 / 2 + σ, γ⟩ : ℂ) * Complex.I) γ := by
  have h1 : HasDerivAt f (deriv f (⟨1 / 2 + σ, γ⟩ : ℂ)) (⟨1 / 2 + σ, γ⟩ : ℂ) :=
    (hf (⟨1 / 2 + σ, γ⟩ : ℂ)).hasDerivAt
  have h2 := (h1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt γ (hasDerivAt_vert σ γ)
  simpa [Function.comp_def, mul_comm] using h2

/-- Algebraic identity: ‖z‖^2 = z.re^2 + z.im^2. -/
lemma norm_sq_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Helper: real derivative of x ↦ (g x).re from HasDerivAt g g' x (diamond-free). -/
lemma hasDerivAt_re_of_complex {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (h : HasDerivAt g g' x) :
    HasDerivAt (fun t => (g t).re) g'.re x := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at h ⊢
  have hlim := (Complex.continuous_re.tendsto g').comp h
  refine hlim.congr fun t => ?_
  simp [Complex.real_smul]

/-- Helper: real derivative of x ↦ (g x).im from HasDerivAt g g' x (diamond-free). -/
lemma hasDerivAt_im_of_complex {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (h : HasDerivAt g g' x) :
    HasDerivAt (fun t => (g t).im) g'.im x := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at h ⊢
  have hlim := (Complex.continuous_im.tendsto g').comp h
  refine hlim.congr fun t => ?_
  simp [Complex.real_smul]

/-- THEOREM II.1 (Exact 1st Transverse Derivative of V(sigma, gamma)):
    d/dsigma ||xi(1/2 + sigma + i*gamma)||^2 = 2 * Re(conj(xi(s)) * xi'(s)). -/
theorem hasDerivAt_xiNormSq_sigma (σ γ : ℝ) :
    HasDerivAt (fun x : ℝ => xiNormSq x γ)
      (2 * (conj (riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)) * deriv riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)).re) σ := by
  have heq : (fun x : ℝ => xiNormSq x γ) =
      fun x : ℝ => (riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).re ^ 2 +
                   (riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).im ^ 2 := by
    ext x; exact norm_sq_eq_re_sq_add_im_sq _
  rw [heq]
  have hg := hasDerivAt_holo_horiz riemannXi_entire σ γ
  have hre := (hasDerivAt_re_of_complex hg).pow 2
  have him := (hasDerivAt_im_of_complex hg).pow 2
  convert hre.add him using 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- THEOREM II.2 (Exact Critical-Line Transverse Stationarity):
    For every gamma in R, the first transverse derivative vanishes identically on beta = 1/2:
      (d/dsigma)|_{sigma=0} ||xi(1/2 + sigma + i*gamma)||^2 = 0. -/
theorem xiNormSq_deriv_sigma_zero (γ : ℝ) :
    deriv (fun x : ℝ => xiNormSq x γ) 0 = 0 := by
  let f : ℝ → ℝ := fun x => xiNormSq x γ
  have h1 : HasDerivAt f (deriv f 0) 0 := (hasDerivAt_xiNormSq_sigma 0 γ).differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) 0 := hasDerivAt_neg (0 : ℝ)
  have h1' : HasDerivAt f (deriv f 0) (-0 : ℝ) := by simpa only [neg_zero] using h1
  have hneg : HasDerivAt (fun x : ℝ => f (-x)) (-(deriv f 0)) 0 := by
    have hcomp := h1'.comp (0 : ℝ) hn
    simpa only [Function.comp_def, mul_neg_one] using hcomp
  have heven : (fun x : ℝ => f (-x)) = f := funext fun x => xiNormSq_even_sigma x γ
  rw [heven] at hneg
  have heq : deriv f 0 = -(deriv f 0) := h1.unique hneg
  linarith

/-- THEOREM II.3 (Exact 2nd Transverse Derivative — Transverse Hessian):
    d^2/dsigma^2 ||xi(1/2 + sigma + i*gamma)||^2
      = 2 * (||xi'(s)||^2 + Re(conj(xi(s)) * xi''(s))). -/
theorem hasDerivAt_xiNormSq_deriv_sigma (σ γ : ℝ) :
    HasDerivAt (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t γ) x)
      (2 * (‖deriv riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)‖ ^ 2 +
            (conj (riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)) *
             deriv (deriv riemannXi) (⟨1 / 2 + σ, γ⟩ : ℂ)).re)) σ := by
  have hfun : (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t γ) x) =
      fun x : ℝ => 2 * ((riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).re * (deriv riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).re +
                        (riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).im * (deriv riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).im) := by
    ext x
    rw [(hasDerivAt_xiNormSq_sigma x γ).deriv]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hfun]
  have h0 := hasDerivAt_holo_horiz riemannXi_entire σ γ
  have h1 := hasDerivAt_holo_horiz differentiable_deriv_riemannXi σ γ
  have hre0 := hasDerivAt_re_of_complex h0
  have him0 := hasDerivAt_im_of_complex h0
  have hre1 := hasDerivAt_re_of_complex h1
  have him1 := hasDerivAt_im_of_complex h1
  have hcomb := ((hre0.mul hre1).add (him0.mul him1)).const_mul (2 : ℝ)
  convert hcomb using 1
  rw [norm_sq_eq_re_sq_add_im_sq]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- THEOREM II.4 (Exact 1st & 2nd Vertical Derivatives of V(sigma, gamma)): -/
theorem hasDerivAt_xiNormSq_gamma (σ γ : ℝ) :
    HasDerivAt (fun y : ℝ => xiNormSq σ y)
      (2 * (conj (riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)) *
            (deriv riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ) * Complex.I)).re) γ := by
  have heq : (fun y : ℝ => xiNormSq σ y) =
      fun y : ℝ => (riemannXi (⟨1 / 2 + σ, y⟩ : ℂ)).re ^ 2 +
                   (riemannXi (⟨1 / 2 + σ, y⟩ : ℂ)).im ^ 2 := by
    ext y; exact norm_sq_eq_re_sq_add_im_sq _
  rw [heq]
  have hg := hasDerivAt_holo_vert riemannXi_entire σ γ
  have hre := (hasDerivAt_re_of_complex hg).pow 2
  have him := (hasDerivAt_im_of_complex hg).pow 2
  convert hre.add him using 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem hasDerivAt_xiNormSq_deriv_gamma (σ γ : ℝ) :
    HasDerivAt (fun y : ℝ => deriv (fun t : ℝ => xiNormSq σ t) y)
      (2 * (‖deriv riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)‖ ^ 2 -
            (conj (riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)) *
             deriv (deriv riemannXi) (⟨1 / 2 + σ, γ⟩ : ℂ)).re)) γ := by
  have hfun : (fun y : ℝ => deriv (fun t : ℝ => xiNormSq σ t) y) =
      fun y : ℝ => 2 * ((riemannXi (⟨1 / 2 + σ, y⟩ : ℂ)).im * (deriv riemannXi (⟨1 / 2 + σ, y⟩ : ℂ)).re -
                        (riemannXi (⟨1 / 2 + σ, y⟩ : ℂ)).re * (deriv riemannXi (⟨1 / 2 + σ, y⟩ : ℂ)).im) := by
    ext y
    rw [(hasDerivAt_xiNormSq_gamma σ y).deriv]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
               Complex.I_re, Complex.I_im]
    ring
  rw [hfun]
  have h0 := hasDerivAt_holo_vert riemannXi_entire σ γ
  have h1 := hasDerivAt_holo_vert differentiable_deriv_riemannXi σ γ
  have hre0 := hasDerivAt_re_of_complex h0
  have him0 := hasDerivAt_im_of_complex h0
  have hre1 := hasDerivAt_re_of_complex h1
  have him1 := hasDerivAt_im_of_complex h1
  have hcomb := ((him0.mul hre1).sub (hre0.mul him1)).const_mul (2 : ℝ)
  convert hcomb using 1
  rw [norm_sq_eq_re_sq_add_im_sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
             Complex.I_re, Complex.I_im]
  ring

/-- THEOREM II.5 (Exact Subharmonicity / 2D Laplacian Identity):
    For every (sigma, gamma) in R^2:
      d^2V/dsigma^2 + d^2V/dgamma^2 = 4 * ||xi'(1/2 + sigma + i*gamma)||^2 >= 0. -/
theorem xiNormSq_laplacian_eq (σ γ : ℝ) :
    deriv (deriv (fun x : ℝ => xiNormSq x γ)) σ +
    deriv (deriv (fun y : ℝ => xiNormSq σ y)) γ =
      4 * ‖deriv riemannXi (⟨1 / 2 + σ, γ⟩ : ℂ)‖ ^ 2 := by
  rw [(hasDerivAt_xiNormSq_deriv_sigma σ γ).deriv,
      (hasDerivAt_xiNormSq_deriv_gamma σ γ).deriv]
  ring

theorem xiNormSq_laplacian_nonneg (σ γ : ℝ) :
    0 ≤ deriv (deriv (fun x : ℝ => xiNormSq x γ)) σ +
        deriv (deriv (fun y : ℝ => xiNormSq σ y)) γ := by
  rw [xiNormSq_laplacian_eq]
  positivity

/-- Exact Cauchy-Riemann derivatives of the critical-line profile Xi(gamma). -/
lemma hasDerivAt_xiCritical (γ : ℝ) :
    HasDerivAt xiCritical (-(deriv riemannXi (⟨1 / 2, γ⟩ : ℂ)).im) γ := by
  have h := hasDerivAt_re_of_complex (hasDerivAt_holo_vert riemannXi_entire 0 γ)
  have hfun : (fun y : ℝ => (riemannXi (⟨1 / 2 + 0, y⟩ : ℂ)).re) = xiCritical := by
    ext y; simp [xiCritical]
  have hd : (deriv riemannXi (⟨1 / 2 + 0, γ⟩ : ℂ) * Complex.I).re =
      -(deriv riemannXi (⟨1 / 2, γ⟩ : ℂ)).im := by
    simp [Complex.mul_re]
  rw [hfun, hd] at h
  exact h

lemma deriv_riemannXi_half_re_eq_zero (γ : ℝ) :
    (deriv riemannXi (⟨1 / 2, γ⟩ : ℂ)).re = 0 := by
  have h := hasDerivAt_im_of_complex (hasDerivAt_holo_vert riemannXi_entire 0 γ)
  have hfun : (fun y : ℝ => (riemannXi (⟨1 / 2 + 0, y⟩ : ℂ)).im) = fun _ => 0 := by
    ext y; simp only [add_zero]; exact riemannXi_im_half_eq_zero y
  have hd : (deriv riemannXi (⟨1 / 2 + 0, γ⟩ : ℂ) * Complex.I).im =
      (deriv riemannXi (⟨1 / 2, γ⟩ : ℂ)).re := by
    simp [Complex.mul_im]
  rw [hfun, hd] at h
  exact ((hasDerivAt_const γ (0 : ℝ)).unique h).symm

lemma hasDerivAt_deriv_xiCritical (γ : ℝ) :
    HasDerivAt (deriv xiCritical) (-(deriv (deriv riemannXi) (⟨1 / 2, γ⟩ : ℂ)).re) γ := by
  have hfun : deriv xiCritical = fun y : ℝ => -(deriv riemannXi (⟨1 / 2, y⟩ : ℂ)).im :=
    funext fun y => (hasDerivAt_xiCritical y).deriv
  rw [hfun]
  have h := (hasDerivAt_im_of_complex (hasDerivAt_holo_vert differentiable_deriv_riemannXi 0 γ)).neg
  have hfun2 : (-(fun y : ℝ => (deriv riemannXi (⟨1 / 2 + 0, y⟩ : ℂ)).im)) =
      fun y : ℝ => -(deriv riemannXi (⟨1 / 2, y⟩ : ℂ)).im := by
    ext y; simp
  have hd : -(deriv (deriv riemannXi) (⟨1 / 2 + 0, γ⟩ : ℂ) * Complex.I).im =
      -(deriv (deriv riemannXi) (⟨1 / 2, γ⟩ : ℂ)).re := by
    simp [Complex.mul_im]
  rw [hfun2, hd] at h
  exact h

/-- THEOREM II.6 (EXACT CRITICAL-LINE HESSIAN = LAGUERRE CURVATURE IDENTITY):
    For EVERY gamma in R, the second transverse derivative of V(sigma, gamma)
    on the critical line sigma = 0 equals identically twice Laguerre's expression:
      (d^2/dsigma^2)|_{sigma=0} ||xi(1/2 + sigma + i*gamma)||^2
        = 2 * ((Xi'(gamma))^2 - Xi(gamma) * Xi''(gamma)). -/
theorem xiNormSq_deriv2_sigma_zero_eq_laguerre (γ : ℝ) :
    deriv (deriv (fun x : ℝ => xiNormSq x γ)) 0 =
      2 * ((deriv xiCritical γ) ^ 2 - xiCritical γ * deriv (deriv xiCritical) γ) := by
  rw [(hasDerivAt_xiNormSq_deriv_sigma 0 γ).deriv]
  have h0 : (1 / 2 + 0 : ℝ) = 1 / 2 := by ring
  rw [h0, norm_sq_eq_re_sq_add_im_sq]
  have hxi_im : (riemannXi (⟨1 / 2, γ⟩ : ℂ)).im = 0 := riemannXi_im_half_eq_zero γ
  have hxi'_re : (deriv riemannXi (⟨1 / 2, γ⟩ : ℂ)).re = 0 := deriv_riemannXi_half_re_eq_zero γ
  have hX1 : deriv xiCritical γ = -(deriv riemannXi (⟨1 / 2, γ⟩ : ℂ)).im :=
    (hasDerivAt_xiCritical γ).deriv
  have hX2 : deriv (deriv xiCritical) γ = -(deriv (deriv riemannXi) (⟨1 / 2, γ⟩ : ℂ)).re :=
    (hasDerivAt_deriv_xiCritical γ).deriv
  rw [hX1, hX2]
  dsimp [xiCritical]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hxi_im, hxi'_re]
  ring

/-- COROLLARY II.6a (Automatic Convex Valley at Every Simple Critical Zero):
    At any simple zero gamma of Xi (Xi(gamma) = 0, Xi'(gamma) != 0),
    the transverse Hessian is strictly positive: d^2V/dsigma^2(0, gamma) = 2 (Xi'(gamma))^2 > 0. -/
theorem xiNormSq_deriv2_sigma_zero_pos_of_simple_zero {γ : ℝ}
    (h0 : xiCritical γ = 0) (h1 : deriv xiCritical γ ≠ 0) :
    0 < deriv (deriv (fun x : ℝ => xiNormSq x γ)) 0 := by
  rw [xiNormSq_deriv2_sigma_zero_eq_laguerre, h0, zero_mul, sub_zero]
  positivity

/-- COROLLARY II.6b (Automatic Convex Valley at Every Local Maximum of |Xi|):
    Whenever Xi(gamma) * Xi''(gamma) < 0, the transverse Hessian is strictly positive. -/
theorem xiNormSq_deriv2_sigma_zero_pos_of_local_max {γ : ℝ}
    (hmax : xiCritical γ * deriv (deriv xiCritical) γ < 0) :
    0 < deriv (deriv (fun x : ℝ => xiNormSq x γ)) 0 := by
  rw [xiNormSq_deriv2_sigma_zero_eq_laguerre]
  have hsq : 0 ≤ (deriv xiCritical γ) ^ 2 := sq_nonneg _
  linarith

/-- COROLLARY II.6c (Exact Ridge Inversion at Any Missed-Zero Local Minimum of |Xi|):
    Whenever Xi'(gamma) = 0 and Xi(gamma) * Xi''(gamma) > 0 (a strictly positive
    local minimum of |Xi| caused by a pair of colliding zeros leaving Re(s) = 1/2),
    the transverse Hessian flips strictly NEGATIVE (valley -> ridge bifurcation). -/
theorem xiNormSq_deriv2_sigma_zero_neg_of_nonzero_min {γ : ℝ}
    (hcrit : deriv xiCritical γ = 0) (hmin : 0 < xiCritical γ * deriv (deriv xiCritical) γ) :
    deriv (deriv (fun x : ℝ => xiNormSq x γ)) 0 < 0 := by
  rw [xiNormSq_deriv2_sigma_zero_eq_laguerre, hcrit]
  linarith

/-- THEOREM II.7 (Smoothness and Exact 3rd Transverse Derivative — Transverse Jerk):
    The second transverse derivative x ↦ d^2V/dsigma^2(x, gamma) is differentiable
    everywhere on R. -/
theorem differentiable_xiNormSq_deriv2_sigma (γ : ℝ) :
    Differentiable ℝ (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t γ)) x) := by
  have hfun : (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t γ)) x) =
      fun x : ℝ => 2 * ((deriv riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).re ^ 2 +
                        (deriv riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).im ^ 2 +
                        (riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).re *
                          (deriv (deriv riemannXi) (⟨1 / 2 + x, γ⟩ : ℂ)).re +
                        (riemannXi (⟨1 / 2 + x, γ⟩ : ℂ)).im *
                          (deriv (deriv riemannXi) (⟨1 / 2 + x, γ⟩ : ℂ)).im) := by
    ext x
    rw [(hasDerivAt_xiNormSq_deriv_sigma x γ).deriv, norm_sq_eq_re_sq_add_im_sq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hfun]
  intro x
  have h0 := hasDerivAt_holo_horiz riemannXi_entire x γ
  have h1 := hasDerivAt_holo_horiz differentiable_deriv_riemannXi x γ
  have h2 := hasDerivAt_holo_horiz differentiable_deriv2_riemannXi x γ
  have d0r := (hasDerivAt_re_of_complex h0).differentiableAt
  have d0i := (hasDerivAt_im_of_complex h0).differentiableAt
  have d1r := (hasDerivAt_re_of_complex h1).differentiableAt
  have d1i := (hasDerivAt_im_of_complex h1).differentiableAt
  have d2r := (hasDerivAt_re_of_complex h2).differentiableAt
  have d2i := (hasDerivAt_im_of_complex h2).differentiableAt
  exact ((((d1r.pow 2).add (d1i.pow 2)).add (d0r.mul d2r)).add (d0i.mul d2i)).const_mul 2

-- ==============================================================================
-- PART III: EXACT 2D PAST-FUTURE LIGHT-CONE BILINEAR ENERGY INTEGRAL
-- ==============================================================================

lemma integrableOn_phi_cosh_cos (σ γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * Real.cosh (σ * u) * Real.cos (γ * u)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + |σ|) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul C2).mono'
    (((continuous_riemannPhi.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
  have hcos : |Real.cos (γ * u)| ≤ 1 := Real.abs_cos_le_one _
  have hcosh : Real.cosh (σ * u) ≤ Real.exp (|σ| * u) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (σ * u) ≤ Real.exp (|σ| * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self σ) hu0)
    have h2 : Real.exp (-(σ * u)) ≤ Real.exp (|σ| * u) :=
      Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs σ) hu0)
    linarith
  have hPhi := hPhi_le u hu0
  rw [Real.norm_eq_abs] at hPhi
  calc |riemannPhi u| * Real.cosh (σ * u) * |Real.cos (γ * u)|
    _ ≤ |riemannPhi u| * Real.cosh (σ * u) * 1 :=
        mul_le_mul_of_nonneg_left hcos (mul_nonneg (abs_nonneg _) (le_of_lt (Real.cosh_pos _)))
    _ = |riemannPhi u| * Real.cosh (σ * u) := mul_one _
    _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) * Real.exp (|σ| * u) :=
        mul_le_mul hPhi hcosh (le_of_lt (Real.cosh_pos _)) (by positivity)
    _ = C2 * Real.exp ((9 / 2 + |σ|) * u - Real.pi / 2 * Real.exp (2 * u)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma integrableOn_phi_sinh_sin (σ γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * Real.sinh (σ * u) * Real.sin (γ * u)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + |σ|) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul C2).mono'
    (((continuous_riemannPhi.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hsin : |Real.sin (γ * u)| ≤ 1 := Real.abs_sin_le_one _
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
  calc |riemannPhi u| * |Real.sinh (σ * u)| * |Real.sin (γ * u)|
    _ ≤ |riemannPhi u| * |Real.sinh (σ * u)| * 1 :=
        mul_le_mul_of_nonneg_left hsin (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |riemannPhi u| * |Real.sinh (σ * u)| := mul_one _
    _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) * Real.exp (|σ| * u) :=
        mul_le_mul hPhi hsinh (abs_nonneg _) (by positivity)
    _ = C2 * Real.exp ((9 / 2 + |σ|) * u - Real.pi / 2 * Real.exp (2 * u)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Exact trigonometric-hyperbolic light-cone product-to-sum identity. -/
lemma lightcone_trig_hyp_identity (σ γ u v : ℝ) :
    2 * (Real.cosh (σ * u) * Real.cos (γ * u) * (Real.cosh (σ * v) * Real.cos (γ * v)) +
         Real.sinh (σ * u) * Real.sin (γ * u) * (Real.sinh (σ * v) * Real.sin (γ * v))) =
      Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
      Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)) := by
  have hcp : Real.cosh (σ * (u + v)) = Real.cosh (σ * u) * Real.cosh (σ * v) + Real.sinh (σ * u) * Real.sinh (σ * v) := by
    rw [mul_add, Real.cosh_add]
  have hcm : Real.cosh (σ * (u - v)) = Real.cosh (σ * u) * Real.cosh (σ * v) - Real.sinh (σ * u) * Real.sinh (σ * v) := by
    rw [mul_sub, Real.cosh_sub]
  have hkp : Real.cos (γ * (u + v)) = Real.cos (γ * u) * Real.cos (γ * v) - Real.sin (γ * u) * Real.sin (γ * v) := by
    rw [mul_add, Real.cos_add]
  have hkm : Real.cos (γ * (u - v)) = Real.cos (γ * u) * Real.cos (γ * v) + Real.sin (γ * u) * Real.sin (γ * v) := by
    rw [mul_sub, Real.cos_sub]
  rw [hcp, hcm, hkp, hkm]
  ring

/-- THEOREM III.1 (EXACT 2D PAST-FUTURE LIGHT-CONE BILINEAR ENERGY INTEGRAL):
    For ALL sigma, gamma in R, the completed zeta energy potential V(sigma, gamma)
    equals the exact 2D past-future light-cone integral in sum/difference coordinates
    (r = u + v, w = u - v):
      ||xi(1/2 + sigma + i*gamma)||^2
        = 2 * int_0^inf int_0^inf Phi(u)*Phi(v) *
            [cosh(sigma*(u+v))*cos(gamma*(u-v)) + cosh(sigma*(u-v))*cos(gamma*(u+v))] dv du. -/
theorem xiNormSq_eq_pastFuture_double_integral (σ γ : ℝ) :
    xiNormSq σ γ =
      2 * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
        riemannPhi u * riemannPhi v *
          (Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v))) := by
  let f : ℝ → ℝ := fun u => riemannPhi u * Real.cosh (σ * u) * Real.cos (γ * u)
  let g : ℝ → ℝ := fun u => riemannPhi u * Real.sinh (σ * u) * Real.sin (γ * u)
  have hf : IntegrableOn f (Ioi 0) := integrableOn_phi_cosh_cos σ γ
  have hg : IntegrableOn g (Ioi 0) := integrableOn_phi_sinh_sin σ γ
  have hre_im := riemannXi_re_im_pastFuture_phi (1 / 2 + σ) γ
  have hsub : (1 / 2 + σ) - 1 / 2 = σ := by ring
  rw [hsub] at hre_im
  dsimp [xiNormSq]
  rw [norm_sq_eq_re_sq_add_im_sq, hre_im.1, hre_im.2]
  have hsq : (2 * ∫ u in Ioi (0 : ℝ), f u) ^ 2 + (2 * ∫ u in Ioi (0 : ℝ), g u) ^ 2 =
      4 * ((∫ u in Ioi (0 : ℝ), f u) * (∫ v in Ioi (0 : ℝ), f v) +
           (∫ u in Ioi (0 : ℝ), g u) * (∫ v in Ioi (0 : ℝ), g v)) := by ring
  change (2 * ∫ u in Ioi (0 : ℝ), f u) ^ 2 + (2 * ∫ u in Ioi (0 : ℝ), g u) ^ 2 = _
  rw [hsq]
  have hff : (∫ u in Ioi (0 : ℝ), f u) * (∫ v in Ioi (0 : ℝ), f v) =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), f u * f v := by
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [integral_const_mul]
  have hgg : (∫ u in Ioi (0 : ℝ), g u) * (∫ v in Ioi (0 : ℝ), g v) =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), g u * g v := by
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [integral_const_mul]
  have hint_ff_outer : IntegrableOn (fun u => ∫ v in Ioi (0 : ℝ), f u * f v) (Ioi 0) := by
    have : (fun u => ∫ v in Ioi (0 : ℝ), f u * f v) = fun u => f u * ∫ v in Ioi (0 : ℝ), f v :=
      funext fun u => integral_const_mul _ _
    rw [this]
    exact hf.mul_const _
  have hint_gg_outer : IntegrableOn (fun u => ∫ v in Ioi (0 : ℝ), g u * g v) (Ioi 0) := by
    have : (fun u => ∫ v in Ioi (0 : ℝ), g u * g v) = fun u => g u * ∫ v in Ioi (0 : ℝ), g v :=
      funext fun u => integral_const_mul _ _
    rw [this]
    exact hg.mul_const _
  rw [hff, hgg, ← integral_add hint_ff_outer hint_gg_outer]
  have hcombine : ∀ u : ℝ,
      (∫ v in Ioi (0 : ℝ), f u * f v) + (∫ v in Ioi (0 : ℝ), g u * g v) =
      ∫ v in Ioi (0 : ℝ), (f u * f v + g u * g v) :=
    fun u => (integral_add (hf.const_mul (f u)) (hg.const_mul (g u))).symm
  simp_rw [hcombine]
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  dsimp [f, g]
  have hid := lightcone_trig_hyp_identity σ γ u v
  calc 2 * (riemannPhi u * Real.cosh (σ * u) * Real.cos (γ * u) *
            (riemannPhi v * Real.cosh (σ * v) * Real.cos (γ * v)) +
            riemannPhi u * Real.sinh (σ * u) * Real.sin (γ * u) *
            (riemannPhi v * Real.sinh (σ * v) * Real.sin (γ * v)))
    _ = riemannPhi u * riemannPhi v *
        (2 * (Real.cosh (σ * u) * Real.cos (γ * u) * (Real.cosh (σ * v) * Real.cos (γ * v)) +
              Real.sinh (σ * u) * Real.sin (γ * u) * (Real.sinh (σ * v) * Real.sin (γ * v)))) := by ring
    _ = riemannPhi u * riemannPhi v *
        (Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v))) := by rw [hid]

-- ==============================================================================
-- PART IV: FOUR-LEVEL DIFFERENTIAL REDUCTION CHAIN DIRECTLY TO MATHLIB4
--          OFFICIAL `RiemannHypothesis`
-- ==============================================================================

/-- Level 0 Target (Sondow-Dumitrescu Strict Transverse Monotonicity):
    For every gamma in R, sigma ↦ ||xi(1/2 + sigma + i*gamma)||^2 is strictly
    increasing on [0, 1/2). -/
def XiModulusStrictMono : Prop :=
  ∀ γ : ℝ, StrictMonoOn (fun σ : ℝ => xiNormSq σ γ) (Ico 0 (1 / 2))

/-- Level -1 Target (Strict Positivity of the 1st Transverse Derivative / Force):
    d/dsigma ||xi(1/2 + sigma + i*gamma)||^2 > 0 for all sigma in (0, 1/2) and gamma in R. -/
def XiTransverseForcePos : Prop :=
  ∀ γ : ℝ, ∀ σ ∈ Ioo (0 : ℝ) (1 / 2), 0 < deriv (fun x : ℝ => xiNormSq x γ) σ

/-- Level -2 Target (Strict Positivity of the 2nd Transverse Derivative / Hessian):
    d^2/dsigma^2 ||xi(1/2 + sigma + i*gamma)||^2 > 0 for all sigma in (0, 1/2) and gamma in R. -/
def XiTransverseHessianPos : Prop :=
  ∀ γ : ℝ, ∀ σ ∈ Ioo (0 : ℝ) (1 / 2), 0 < deriv (deriv (fun x : ℝ => xiNormSq x γ)) σ

/-- Level -3 Target (Non-Negative Critical Laguerre Curvature + Positive Transverse Jerk):
    (d^2V/dsigma^2)|_{sigma=0} >= 0 and d^3V/dsigma^3 > 0 on (0, 1/2) x R. -/
def XiTransverseJerkPos : Prop :=
  ∀ γ : ℝ,
    0 ≤ deriv (deriv (fun x : ℝ => xiNormSq x γ)) 0 ∧
    ∀ σ ∈ Ioo (0 : ℝ) (1 / 2),
      0 < deriv (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t γ)) x) σ

/-- THEOREM IV.1 (Level -3 -> Level -2):
    Non-negative critical Laguerre curvature + positive 3rd transverse derivative
    implies strict positivity of the 2nd transverse Hessian on (0, 1/2). -/
theorem xiTransverseHessianPos_of_jerkPos (h : XiTransverseJerkPos) :
    XiTransverseHessianPos := by
  intro γ σ hσ
  have hdiff : Differentiable ℝ (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t γ)) x) :=
    differentiable_xiNormSq_deriv2_sigma γ
  have hmono : StrictMonoOn (fun x : ℝ => deriv (deriv (fun t : ℝ => xiNormSq t γ)) x) (Ico 0 (1 / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 (1 / 2)) hdiff.continuous.continuousOn ?_
    intro x hx
    rw [interior_Ico] at hx
    exact (h γ).2 x hx
  have hlt := hmono ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ.1, hσ.2⟩ hσ.1
  exact lt_of_le_of_lt (h γ).1 hlt

/-- THEOREM IV.2 (Level -2 -> Level -1):
    Strict positivity of the 2nd transverse Hessian on (0, 1/2) implies strict
    positivity of the 1st transverse force on (0, 1/2), using stationarity m1(0, gamma) = 0. -/
theorem xiTransverseForcePos_of_hessianPos (h : XiTransverseHessianPos) :
    XiTransverseForcePos := by
  intro γ σ hσ
  have hdiff : Differentiable ℝ (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t γ) x) :=
    fun x => (hasDerivAt_xiNormSq_deriv_sigma x γ).differentiableAt
  have hmono : StrictMonoOn (fun x : ℝ => deriv (fun t : ℝ => xiNormSq t γ) x) (Ico 0 (1 / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 (1 / 2)) hdiff.continuous.continuousOn ?_
    intro x hx
    rw [interior_Ico] at hx
    exact h γ x hx
  have hlt := hmono ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ.1, hσ.2⟩ hσ.1
  dsimp only at hlt
  rw [xiNormSq_deriv_sigma_zero γ] at hlt
  exact hlt

/-- THEOREM IV.3 (Level -1 -> Level 0):
    Strict positivity of the 1st transverse force on (0, 1/2) implies strict
    monotonicity of V(sigma, gamma) = ||xi(1/2 + sigma + i*gamma)||^2 on [0, 1/2). -/
theorem xiModulusStrictMono_of_forcePos (h : XiTransverseForcePos) :
    XiModulusStrictMono := by
  intro γ
  have hdiff : Differentiable ℝ (fun x : ℝ => xiNormSq x γ) :=
    fun x => (hasDerivAt_xiNormSq_sigma x γ).differentiableAt
  refine strictMonoOn_of_deriv_pos (convex_Ico 0 (1 / 2)) hdiff.continuous.continuousOn ?_
  intro x hx
  rw [interior_Ico] at hx
  exact h γ x hx

/-- THEOREM IV.4 (Level 0 -> MATHLIB4 OFFICIAL `RiemannHypothesis`):
    Strict transverse monotonicity of ||xi(1/2 + sigma + i*gamma)||^2 on [0, 1/2)
    unconditionally implies Mathlib4's official `RiemannHypothesis`! -/
theorem riemannHypothesis_of_xiModulusStrictMono (h : XiModulusStrictMono) :
    RiemannHypothesis := by
  intro s hz htriv hone
  have hnt := isNonTrivialZetaZero_of_mathlib_rh_hyp s hz htriv hone
  have h0 : 0 < s.re := hnt.1
  have h1 : s.re < 1 := hnt.2.1
  have hxi0 : riemannXi s = 0 := (riemannXi_eq_zero_iff_riemannZeta h0 h1).mpr hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Case s.re < 1/2: reflect to 1 - s with Re(1 - s) > 1/2
    let σ : ℝ := 1 / 2 - s.re
    have hσ0 : 0 < σ := by dsimp [σ]; linarith
    have hσ1 : σ < 1 / 2 := by dsimp [σ]; linarith
    have hmono := h (-s.im) ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ0, hσ1⟩ hσ0
    have h1s : (⟨1 / 2 + σ, -s.im⟩ : ℂ) = 1 - s := by
      apply Complex.ext
      · simp [σ]; ring
      · simp
    have hval0 : xiNormSq σ (-s.im) = 0 := by
      rw [xiNormSq_eq_zero_iff, h1s, riemannXi_one_sub, hxi0]
    linarith [xiNormSq_nonneg 0 (-s.im)]
  · -- Case 1/2 < s.re
    let σ : ℝ := s.re - 1 / 2
    have hσ0 : 0 < σ := by dsimp [σ]; linarith
    have hσ1 : σ < 1 / 2 := by dsimp [σ]; linarith
    have hmono := h s.im ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hσ0, hσ1⟩ hσ0
    have hs_eq : (⟨1 / 2 + σ, s.im⟩ : ℂ) = s := by
      apply Complex.ext
      · simp [σ]
      · simp
    have hval0 : xiNormSq σ s.im = 0 := by
      rw [xiNormSq_eq_zero_iff, hs_eq, hxi0]
    linarith [xiNormSq_nonneg 0 s.im]

/-- COROLLARY IV.5 (Direct Closure of `RiemannHypothesis`, `SpectralBridgeTarget`,
    and `AdelicDipolarWeilPositivity` from Any of the Differential Hierarchy Targets): -/
theorem riemannHypothesis_of_xiTransverseForcePos (h : XiTransverseForcePos) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiModulusStrictMono (xiModulusStrictMono_of_forcePos h)

theorem riemannHypothesis_of_xiTransverseHessianPos (h : XiTransverseHessianPos) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiTransverseForcePos (xiTransverseForcePos_of_hessianPos h)

theorem riemannHypothesis_of_xiTransverseJerkPos (h : XiTransverseJerkPos) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiTransverseHessianPos (xiTransverseHessianPos_of_jerkPos h)

theorem spectralBridge_and_adelicWeil_of_xiTransverseHessianPos (h : XiTransverseHessianPos) :
    RiemannHypothesis ∧
    SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight) ∧
    AdelicDipolarWeilPositivity := by
  have hRH := riemannHypothesis_of_xiTransverseHessianPos h
  have h3 := three_way_equivalence_rh_spectralBridge_adelicWeil
  have hSB := h3.1.mp hRH
  exact ⟨hRH, hSB, h3.2.mp hSB⟩

-- ==============================================================================
-- PART V: WEIERSTRASS MODULAR SURFACE H/SL_2(Z) SCATTERING MATRIX phi(s)
-- ==============================================================================

/-- The Lax-Phillips / Eisenstein scattering matrix of the modular surface
    H / SL_2(Z) (moduli space of complex Weierstrass tori C / Lambda):
      phi(s) = xi(2*s - 1) / xi(2*s). -/
noncomputable def modularScattering (s : ℂ) : ℂ :=
  riemannXi (2 * s - 1) / riemannXi (2 * s)

/-- THEOREM V.1 (Exact Unitarity of the Modular Scattering Matrix on Re(s) = 1/2):
    Along the continuous spectrum s = 1/2 + i*t of -Delta_H, ||phi(1/2 + i*t)|| = 1. -/
theorem modularScattering_norm_on_half (t : ℝ) :
    ‖modularScattering (⟨1 / 2, t⟩ : ℂ)‖ = 1 := by
  dsimp [modularScattering]
  have hden_re : 1 ≤ (2 * (⟨1 / 2, t⟩ : ℂ)).re := by
    simp
  have hden_ne : riemannXi (2 * (⟨1 / 2, t⟩ : ℂ)) ≠ 0 :=
    riemannXi_ne_zero_of_one_le_re hden_re
  have hnum_eq : 2 * (⟨1 / 2, t⟩ : ℂ) - 1 = 1 - conj (2 * (⟨1 / 2, t⟩ : ℂ)) := by
    apply Complex.ext <;> simp
  rw [norm_div, hnum_eq, riemannXi_one_sub, riemannXi_conj, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hden_ne)

/-- Predicate: the modular scattering matrix has no denominator zeros (poles) in the
    strip 1/4 < Re(w) < 1/2 (equivalently, no resonances off Re(w) = 1/4). -/
def ModularScatteringPoleFree : Prop :=
  ∀ w : ℂ, 1 / 4 < w.re → w.re < 1 / 2 → riemannXi (2 * w) ≠ 0

/-- THEOREM V.2 (EXACT EQUIVALENCE BETWEEN MODULAR SCATTERING POLE-EXCLUSION
    AND MATHLIB4 OFFICIAL `RiemannHypothesis`):
    The Lax-Phillips scattering matrix phi(w) = xi(2w - 1) / xi(2w) on H/SL_2(Z)
    is pole-free on the strip 1/4 < Re(w) < 1/2 IF AND ONLY IF Mathlib4's
    official `RiemannHypothesis` holds! Moreover, at any off-line zero, the
    numerator xi(2w - 1) is strictly non-zero while the denominator xi(2w) vanishes. -/
theorem modularScattering_numerator_ne_zero_in_strip {w : ℂ} (hw : w.re < 1 / 2) :
    riemannXi (2 * w - 1) ≠ 0 := by
  have h1 : 1 - (2 * w - 1) = 2 - 2 * w := by ring
  rw [← riemannXi_one_sub, h1]
  refine riemannXi_ne_zero_of_one_le_re ?_
  simp
  linarith

theorem modularScatteringPoleFree_iff_riemannHypothesis :
    ModularScatteringPoleFree ↔ RiemannHypothesis := by
  constructor
  · intro hPF s hz htriv hone
    have hnt := isNonTrivialZetaZero_of_mathlib_rh_hyp s hz htriv hone
    have hxi0 : riemannXi s = 0 := (riemannXi_eq_zero_iff_riemannZeta hnt.1 hnt.2.1).mpr hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let w : ℂ := (1 - s) / 2
      have hw1 : 1 / 4 < w.re := by dsimp [w]; simp; linarith
      have hw2 : w.re < 1 / 2 := by dsimp [w]; simp; linarith [hnt.1]
      have h2w : 2 * w = 1 - s := by dsimp [w]; ring
      exact hPF w hw1 hw2 (by rw [h2w, riemannXi_one_sub, hxi0])
    · let w : ℂ := s / 2
      have hw1 : 1 / 4 < w.re := by dsimp [w]; simp; linarith
      have hw2 : w.re < 1 / 2 := by dsimp [w]; simp; linarith [hnt.2.1]
      have h2w : 2 * w = s := by dsimp [w]; ring
      exact hPF w hw1 hw2 (by rw [h2w, hxi0])
  · intro hRH w hw1 hw2 hxi0
    let s : ℂ := 2 * w
    have hs_re0 : 0 < s.re := by dsimp [s]; simp; linarith
    have hs_re1 : s.re < 1 := by dsimp [s]; simp; linarith
    have hz : riemannZeta s = 0 := (riemannXi_eq_zero_iff_riemannZeta hs_re0 hs_re1).mp hxi0
    have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      linarith
    have hone : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hhalf : s.re = 1 / 2 := hRH s hz htriv hone
    have : s.re = 2 * w.re := by dsimp [s]; simp
    linarith

/-- THEOREM V.3 (FOUR-WAY MASTER EQUIVALENCE IN MATHLIB4):
    The following four global statements are 100% logically equivalent in Mathlib4:
      (1) Mathlib4 official `RiemannHypothesis`,
      (2) `SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)`,
      (3) `AdelicDipolarWeilPositivity`,
      (4) `ModularScatteringPoleFree` (pole-exclusion of phi(s) on H/SL_2(Z)). -/
theorem four_way_rh_equivalence :
    (RiemannHypothesis ↔ SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)) ∧
    (SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight) ↔ AdelicDipolarWeilPositivity) ∧
    (AdelicDipolarWeilPositivity ↔ ModularScatteringPoleFree) := by
  have h3 := three_way_equivalence_rh_spectralBridge_adelicWeil
  refine ⟨h3.1, h3.2, ?_⟩
  exact (h3.2.symm.trans h3.1.symm).trans modularScatteringPoleFree_iff_riemannHypothesis.symm

end XiConvexityLaguerre
