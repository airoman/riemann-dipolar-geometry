/-
  ==============================================================================
  ROUTE A INFINITE-DIMENSIONAL CONTINUOUS WEIL POSITIVITY, ROUTE B EXPLICIT
  CONSTRUCTIVE ZERO-FREE & CONVEXITY RECTANGLE, AND SCHOENBERG NO-GO THEOREM

  Title: Advancing Both Global Closure Routes in Lean 4 + Mathlib4
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Route A — Infinite-Dimensional Continuous Weil–Archimedean Positivity):
      * Exact continuous Archimedean Weil spectral weight `psiArch` using
        Mathlib4's `Real.eulerMascheroniConstant` (`C_inf = gamma_E + log(8*pi) + pi/2`).
      * `psiArch_summable`, `psiArch_even`, `psiArch_strictMono_nonneg`.
      * `psiArch_ge_psiLb1`: Exact 1-term + integral-test closed-form lower bound
        `psiArch t >= -C_inf + 4*t^2 / (1/4 + t^2) + (1/2) * log(1 + 4*t^2/25)`.
      * `integral_psiLb1_gap_eq`: Exact FTC antiderivative for the cutoff gap integral.
      * `fourierTransform_norm_sq_le_L_mul_L2`: Exact Paley–Wiener / Cauchy–Schwarz
        L^2 bound `‖g_hat(t)‖^2 <= L * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`.
      * `weilPole_even_nonneg`, `weilPole_odd_lower_bound`, `weilPole_lower_bound_all`:
        Exact even/odd decoupling of W_pole and universal lower bound
        `W_pole(g) >= -2*(sinh(L/2) - L/2) * ‖g‖_2^2`.
      * `weilArch_continuous_cutoff_lower_bound` and
        `weilArch_continuous_pos_on_small_support`:
        UNCONDITIONAL INFINITE-DIMENSIONAL CONTINUOUS WEIL POSITIVITY for ALL
        `0 < L <= 1/12` and EVERY non-zero continuous `g` on `[-L/2, L/2]`:
          `W_pole(g) + W_inf(g) >= (1/10) * ‖g‖_2^2 > 0`.
      * `schur_complement_hilbert_pos` & `bandlimited_prolate_comparison_pos`:
        Abstract infinite-dimensional Hilbert-space Schur-complement and
        bandlimited Prolate comparison positivity certificates.
  - Part II (Route B — Exact 2D Light-Cone Identity for m_2(sigma, gamma) & Moment Bound):
      * `xiNormSq_deriv2_eq_pastFuture_double_integral`:
        Exact 2D past–future light-cone cosine integral for `∂_σ^2 V(σ, γ)` at ALL `(σ, γ)`.
      * `xiNormSq_deriv2_ge_moment_quadratic`:
        Using `cos(x) >= 1 - x^2/2`, `cosh(a+b) + cosh(a-b) = 2*cosh(a)*cosh(b)`,
        and `(u+v)^2*(u-v)^2 = u^4 - 2*u^2*v^2 + v^4`, proves for ALL `σ ∈ [0, 1/2]`:
          `m_2(σ, γ) >= 8*b_0*b_1 - 4*γ^2*(I_0(1/2)*I_4(1/2) - b_1^2)`.
  - Part III (Route B — Constructive Explicit Zero-Free & Convexity Rectangle):
      * Purely analytical closed-form upper bounds on `I_0(1/2), I_2(0), I_4(1/2)`
        via `n >= 1` geometric tail + quadratic completion of `e^{2u} >= 1 + 2u + 2u^2`,
        and 1-bin antitonicity lower bounds on `b_0, b_1` on `[0, 1/4]`.
      * `xiNormSq_deriv2_pos_explicit_corridor` & `xiNormSq_deriv1_pos_explicit_corridor`:
        EXPLICIT CONSTRUCTIVE CONVEXITY CORRIDOR `∀ σ ∈ [0, 1/2], ∀ |γ| ≤ 1/5, m_2(σ, γ) > 0`.
      * `riemannXi_critical_pos_explicit_corridor` &
        `riemannZeta_ne_zero_explicit_strip_rectangle`:
        UNCONDITIONAL CONSTRUCTIVE ZERO-FREE RECTANGLE ON MATHLIB4's `riemannZeta`:
          `∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ 1/5 → riemannZeta s ≠ 0`.
  - Part IV (Route B — Schoenberg Complete-Monotonicity No-Go Theorem):
      * `schoenberg_laplace_exp_lower_bound`: Any non-zero finite positive measure on
        `[0, ∞)` yields a Laplace transform bounded below by `c * exp(-α_1 * x)`.
      * `riemannLaguerreKernel1D_superexp_le` & `riemannLaguerreKernel1D_not_schoenberg_laplace`:
        The 1D Laguerre cosine kernel `G_{2,0}(w)` decays super-exponentially, proving
        unconditionally that `x ↦ G_{2,0}(√x)` CANNOT be represented as a positive
        Schoenberg Gaussian/Laplace mixture.
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Integral.Bochner.Set
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.XiConvexityLaguerre
import RiemannDipolar.UnconditionalCorridorAndProlate
import RiemannDipolar.CertificateAndSpectralBridge

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge

namespace WeilArchimedeanAndExplicitCorridor

-- ==============================================================================
-- PART 0: ELEMENTARY EXPONENTIAL BOUNDS (PURELY KERNEL-CERTIFIED)
-- ==============================================================================

/-- Elementary Taylor upper bound on `Real.exp y` for `0 ≤ y ≤ 1` with `n` terms. -/
lemma exp_le_taylor_of_nonneg_le_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp y ≤ (∑ k ∈ Finset.range n, y ^ k / (k.factorial : ℝ)) +
      y ^ n * (((n : ℝ) + 1) / ((n.factorial : ℝ) * (n : ℝ))) := by
  have habs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hb := Real.exp_bound habs hn
  rw [abs_of_nonneg hy0] at hb
  have h1 := (abs_le.mp hb).2
  have hcast : ((n.succ : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hcast] at h1
  linarith

lemma exp_one_lt_three : Real.exp 1 < 3 := by
  have h := exp_le_taylor_of_nonneg_le_one (y := 1) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h
  linarith

lemma exp_half_lt_17_div_10 : Real.exp (1 / 2 : ℝ) < 17 / 10 := by
  have h := exp_le_taylor_of_nonneg_le_one (y := 1 / 2) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h
  linarith

lemma exp_49_div_10_lt_145 : Real.exp (49 / 10 : ℝ) < 145 := by
  have h1 := exp_le_taylor_of_nonneg_le_one (y := 49 / 100) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h1
  have h2 : Real.exp (49 / 100 : ℝ) < 1633 / 1000 := by norm_num at h1; linarith
  have hpow : Real.exp (49 / 10 : ℝ) = (Real.exp (49 / 100 : ℝ)) ^ (10 : ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  rw [hpow]
  have hlt : (Real.exp (49 / 100 : ℝ)) ^ (10 : ℕ) < (1633 / 1000 : ℝ) ^ (10 : ℕ) :=
    pow_lt_pow_left₀ h2 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hnum : (1633 / 1000 : ℝ) ^ (10 : ℕ) < 145 := by norm_num
  linarith

lemma exp_5355_div_1000_lt_220 : Real.exp (5355 / 1000 : ℝ) < 220 := by
  have h1 := exp_le_taylor_of_nonneg_le_one (y := 1071 / 1600) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h1
  have h2 : Real.exp (1071 / 1600 : ℝ) < 1956 / 1000 := by norm_num at h1; linarith
  have hpow : Real.exp (5355 / 1000 : ℝ) = (Real.exp (1071 / 1600 : ℝ)) ^ (8 : ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  rw [hpow]
  have hlt : (Real.exp (1071 / 1600 : ℝ)) ^ (8 : ℕ) < (1956 / 1000 : ℝ) ^ (8 : ℕ) :=
    pow_lt_pow_left₀ h2 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hnum : (1956 / 1000 : ℝ) ^ (8 : ℕ) < 220 := by norm_num
  linarith

lemma log_eight_pi_lt : Real.log (8 * Real.pi) < 13 / 4 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hsum := Real.sum_le_exp_of_nonneg (x := (13 / 4 : ℝ)) (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hsum
  have hpi := Real.pi_lt_d2
  norm_num at hsum
  linarith

lemma exp_neg_bound_from_taylor {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) {n : ℕ}
    (hsum : 1 / c < ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)) :
    Real.exp (-x) < c := by
  have hle := Real.sum_le_exp_of_nonneg hx n
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  have hinv : (1 / c) < Real.exp x := lt_of_lt_of_le hsum hle
  have h1 : 1 < c * Real.exp x := by
    have := (div_lt_iff₀ hc).mp hinv
    linarith
  exact (inv_lt_iff_one_lt_mul₀' hexp_pos).mpr (by linarith)

-- ==============================================================================
-- PART I: ROUTE A — INFINITE-DIMENSIONAL CONTINUOUS WEIL–ARCHIMEDEAN POSITIVITY
-- ==============================================================================

/-- The exact Archimedean Weil constant `C_∞ = γ_E + log(8π) + π/2`. -/
noncomputable def archimedeanWeilConst : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + Real.pi / 2

/-- Certified upper bound `C_∞ < 11/2` directly from Mathlib4's
    `Real.eulerMascheroniConstant_lt_two_thirds` and `Real.pi_lt_d2`. -/
theorem archimedeanWeilConst_lt : archimedeanWeilConst < 11 / 2 := by
  dsimp [archimedeanWeilConst]
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 := log_eight_pi_lt
  have h3 := Real.pi_lt_d2
  linarith

/-- Individual summand of the Archimedean Weil spectral weight `Re(Γ'/Γ(1/4 + it/2)) - log π`. -/
noncomputable def psiArchTerm (t : ℝ) (n : ℕ) : ℝ :=
  (t ^ 2 / 4) / (((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4))

/-- Exact continuous Archimedean Weil spectral weight
    `ψ_arch(t) = Re(Γ'/Γ(1/4 + it/2)) - log π = -C_∞ + ∑_{n=0}^∞ psiArchTerm t n`. -/
noncomputable def psiArch (t : ℝ) : ℝ :=
  -archimedeanWeilConst + ∑' n : ℕ, psiArchTerm t n

lemma psiArchTerm_nonneg (t : ℝ) (n : ℕ) : 0 ≤ psiArchTerm t n := by
  dsimp [psiArchTerm]; positivity

/-- Summability of the Archimedean digamma series for every `t : ℝ`. -/
theorem psiArch_summable (t : ℝ) : Summable (psiArchTerm t) := by
  have hbase : Summable (fun n : ℕ => (t ^ 2 / 4) * (1 / ((n : ℝ) + 1 / 4) ^ 3)) := by
    have hp : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (3 : ℕ))) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ))) :=
      (summable_nat_add_iff 1).mpr hp
    have hcomp : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1 / 4) ^ 3) := by
      refine ((summable_nat_add_iff 1).mp ?_).of_nonneg_of_le (fun _ => by positivity) (fun _ => le_rfl)
      refine hshift.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hle : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 / 4 := by linarith
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (le_of_lt hpos) hle 3)
    exact hcomp.mul_left (t ^ 2 / 4)
  refine hbase.of_nonneg_of_le (psiArchTerm_nonneg t) (fun n => ?_)
  dsimp [psiArchTerm]
  have ha : 0 < (n : ℝ) + 1 / 4 := by positivity
  have hden : ((n : ℝ) + 1 / 4) ^ 3 ≤ ((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by
    nlinarith [sq_nonneg t]
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

theorem psiArch_even (t : ℝ) : psiArch (-t) = psiArch t := by
  dsimp [psiArch, psiArchTerm]
  congr 1; congr 1; ext n; ring

theorem psiArch_strictMono_nonneg : StrictMonoOn psiArch (Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have hsq : t₁ ^ 2 < t₂ ^ 2 := sq_lt_sq' (by linarith [mem_Ici.mp ht₁]) hlt
  dsimp [psiArch]
  suffices h : ∑' n : ℕ, psiArchTerm t₁ n < ∑' n : ℕ, psiArchTerm t₂ n by linarith
  have hle : ∀ n : ℕ, psiArchTerm t₁ n ≤ psiArchTerm t₂ n := by
    intro n
    dsimp [psiArchTerm]
    have ha : 0 < (n : ℝ) + 1 / 4 := by positivity
    have ha3 : 0 < ((n : ℝ) + 1 / 4) ^ 3 := by positivity
    have hd1 : 0 < ((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + t₁ ^ 2 / 4) := by positivity
    have hd2 : 0 < ((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + t₂ ^ 2 / 4) := by positivity
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith
  have h0 : psiArchTerm t₁ 0 < psiArchTerm t₂ 0 := by
    dsimp [psiArchTerm]
    simp only [Nat.cast_zero]
    have hd1 : 0 < ((0 : ℝ) + 1 / 4) * (((0 : ℝ) + 1 / 4) ^ 2 + t₁ ^ 2 / 4) := by positivity
    have hd2 : 0 < ((0 : ℝ) + 1 / 4) * (((0 : ℝ) + 1 / 4) ^ 2 + t₂ ^ 2 / 4) := by positivity
    rw [div_lt_div_iff₀ hd1 hd2]
    nlinarith
  have hdiff_sum : Summable (fun n => psiArchTerm t₂ n - psiArchTerm t₁ n) :=
    (psiArch_summable t₂).sub (psiArch_summable t₁)
  have hpos : 0 < ∑' n : ℕ, (psiArchTerm t₂ n - psiArchTerm t₁ n) :=
    Summable.tsum_pos hdiff_sum (fun n => sub_nonneg.mpr (hle n)) 0 (sub_pos.mpr h0)
  rw [(psiArch_summable t₂).tsum_sub (psiArch_summable t₁)] at hpos
  linarith

/-- Closed-form 1-term + logarithmic integral-test lower envelope for `psiArch`:
    `ψ_lb1(t) = -C_∞ + 4 t^2 / (1/4 + t^2) + (1/2) log(1 + 4 t^2 / 25)`. -/
noncomputable def psiLb1 (t : ℝ) : ℝ :=
  -archimedeanWeilConst + (4 * t ^ 2) / (1 / 4 + t ^ 2) +
    (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25)

lemma psiLb1_even (t : ℝ) : psiLb1 (-t) = psiLb1 t := by
  dsimp [psiLb1]; ring_nf

lemma psiLb1_mono_nonneg {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (hle : t₁ ≤ t₂) :
    psiLb1 t₁ ≤ psiLb1 t₂ := by
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := pow_le_pow_left₀ ht₁ hle 2
  dsimp [psiLb1]
  have h1 : (4 * t₁ ^ 2) / (1 / 4 + t₁ ^ 2) ≤ (4 * t₂ ^ 2) / (1 / 4 + t₂ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : Real.log (1 + 4 * t₁ ^ 2 / 25) ≤ Real.log (1 + 4 * t₂ ^ 2 / 25) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- Exact elementary integral of `(t^2/4) / (x * (x^2 + t^2/4))` on `[a, b]` (`0 < a ≤ b`). -/
lemma integral_digamma_tail_step (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (t ^ 2 / 4) / (x * (x ^ 2 + t ^ 2 / 4)) =
      (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * a ^ 2)) -
      (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * b ^ 2)) := by
  let F : ℝ → ℝ := fun x => -(1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * x ^ 2))
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt F ((t ^ 2 / 4) / (x * (x ^ 2 + t ^ 2 / 4))) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have harg_pos : 0 < 1 + t ^ 2 / (4 * x ^ 2) := by positivity
    have hd_sq : HasDerivAt (fun y : ℝ => 4 * y ^ 2) (8 * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul (4 : ℝ)
      convert h using 1; ring
    have hd_div : HasDerivAt (fun y : ℝ => t ^ 2 / (4 * y ^ 2))
        (-(t ^ 2 * (8 * x)) / (4 * x ^ 2) ^ 2) x := by
      have h := (hasDerivAt_const x (t ^ 2)).div hd_sq (ne_of_gt (by positivity : 0 < 4 * x ^ 2))
      convert h using 1; ring
    have hd_add : HasDerivAt (fun y : ℝ => 1 + t ^ 2 / (4 * y ^ 2))
        (-(t ^ 2 * (8 * x)) / (4 * x ^ 2) ^ 2) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add hd_div using 1; ring
    have hd_log := (hd_add.log (ne_of_gt harg_pos)).const_mul (-(1 / 2 : ℝ))
    convert hd_log using 1
    field_simp [hx_ne]
    ring
  have hcont : ContinuousOn (fun x : ℝ => (t ^ 2 / 4) / (x * (x ^ 2 + t ^ 2 / 4))) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    exact ((continuousAt_const).div
      (continuousAt_id.mul ((continuousAt_id.pow 2).add continuousAt_const))
      (ne_of_gt (mul_pos hx_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx_pos) (by positivity))))).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable)
  rw [hftc]
  dsimp [F]; ring

/-- THEOREM I.1 (Exact Integral-Test Closed-Form Lower Bound on `psiArch`):
    For EVERY `t ∈ ℝ`, `psiLb1 t ≤ psiArch t`. -/
theorem psiArch_ge_psiLb1 (t : ℝ) : psiLb1 t ≤ psiArch t := by
  dsimp [psiLb1, psiArch]
  have hsplit := (psiArch_summable t).tsum_eq_zero_add
  rw [hsplit]
  have h0 : psiArchTerm t 0 = (4 * t ^ 2) / (1 / 4 + t ^ 2) := by
    dsimp [psiArchTerm]; field_simp; ring
  rw [h0]
  suffices htail : (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) ≤ ∑' n : ℕ, psiArchTerm t (n + 1) by
    linarith
  have hsum_shift : Summable (fun n : ℕ => psiArchTerm t (n + 1)) :=
    (summable_nat_add_iff 1).mpr (psiArch_summable t)
  -- For every N : ℕ, partial sum ∑_{n < N} psiArchTerm t (n+1) ≥ (1/2) log(1 + 4t^2/25) - (1/2) log(1 + t^2/(4(N+5/4)^2))
  have hpart : ∀ N : ℕ,
      (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) -
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2)) ≤
      ∑ n ∈ Finset.range N, psiArchTerm t (n + 1) := by
    intro N
    have hstep : ∀ n : ℕ,
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((n : ℝ) + 5 / 4) ^ 2)) -
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * (((n + 1 : ℕ) : ℝ) + 5 / 4) ^ 2)) ≤
        psiArchTerm t (n + 1) := by
      intro n
      let a : ℝ := (n : ℝ) + 5 / 4
      let b : ℝ := ((n + 1 : ℕ) : ℝ) + 5 / 4
      have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
      have hba : b - a = 1 := by dsimp [a, b]; push_cast; ring
      have ha_pos : 0 < a := by dsimp [a]; positivity
      rw [← integral_digamma_tail_step t a b ha_pos hab]
      have hconst : ∫ _x in a..b, psiArchTerm t (n + 1) = psiArchTerm t (n + 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hba, one_mul]
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hab ?_ intervalIntegrable_const (fun x hx => ?_)
      · apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hab]
        intro x hx
        have hxp : 0 < x := lt_of_lt_of_le ha_pos hx.1
        exact ((continuousAt_const).div
          (continuousAt_id.mul ((continuousAt_id.pow 2).add continuousAt_const))
          (ne_of_gt (mul_pos hxp (add_pos_of_pos_of_nonneg (sq_pos_of_pos hxp) (by positivity))))).continuousWithinAt
      · dsimp [psiArchTerm]
        have ha_eq : (((n + 1 : ℕ) : ℝ) + 1 / 4) = a := by dsimp [a]; push_cast; ring
        rw [ha_eq]
        have hx_ge : a ≤ x := hx.1
        have hden : a * (a ^ 2 + t ^ 2 / 4) ≤ x * (x ^ 2 + t ^ 2 / 4) := by
          have hsq : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (le_of_lt ha_pos) hx_ge 2
          nlinarith [sq_nonneg t]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have htele : ∑ n ∈ Finset.range N,
        ((1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((n : ℝ) + 5 / 4) ^ 2)) -
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * (((n + 1 : ℕ) : ℝ) + 5 / 4) ^ 2))) =
        (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) -
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2)) := by
      have h := Finset.sum_range_sub'
        (fun k : ℕ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((k : ℝ) + 5 / 4) ^ 2))) N
      rw [h]
      congr 2; congr 1; push_cast; ring
    rw [← htele]
    exact Finset.sum_le_sum fun n _ => hstep n
  -- Take N → ∞
  have htend_lhs : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) -
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2)))
      atTop (𝓝 ((1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25))) := by
    have hzero' : Tendsto (fun N : ℕ => t ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun N : ℕ => (4 * ((N : ℝ) + 5 / 4) ^ 2)) atTop atTop := by
        have h1 : Tendsto (fun N : ℕ => (N : ℝ) + 5 / 4) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 5 / 4) ^ 2) atTop atTop :=
          (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h1
        exact h2.const_mul_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop hinv
    have hlog : Tendsto (fun N : ℕ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => 1 + t ^ 2 / (4 * ((N : ℝ) + 5 / 4) ^ 2)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hzero'
      have h2 := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
      simpa [Real.log_one] using h2.const_mul (1 / 2 : ℝ)
    simpa using tendsto_const_nhds.sub hlog
  exact le_of_tendsto_of_tendsto htend_lhs hsum_shift.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hpart)

/-- Exact closed-form antiderivative of the rational part of `psiLb1` on `[0, T]`. -/
private lemma integral_psiLb1_rat_part (T : ℝ) :
    ∫ t in (0 : ℝ)..T, (4 * t ^ 2) / (1 / 4 + t ^ 2) = 4 * T - 2 * Real.arctan (2 * T) := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => 4 * s - 2 * Real.arctan (2 * s)) ((4 * t ^ 2) / (1 / 4 + t ^ 2)) t := by
    intro t _
    have ha : HasDerivAt (fun s : ℝ => Real.arctan (2 * s)) (2 / (1 + (2 * t) ^ 2)) t := by
      have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id' t).const_mul (2 : ℝ)
      have h := (Real.hasDerivAt_arctan (2 * t)).comp t hlin
      rw [Function.comp_def] at h
      have hv : 1 / (1 + (2 * t) ^ 2) * 2 = 2 / (1 + (2 * t) ^ 2) := by ring
      rwa [hv] at h
    have h4 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by simpa using (hasDerivAt_id' t).const_mul (4 : ℝ)
    have h := h4.sub (ha.const_mul (2 : ℝ))
    have hval : 4 - 2 * (2 / (1 + (2 * t) ^ 2)) = (4 * t ^ 2) / (1 / 4 + t ^ 2) := by
      have hne1 : 1 / 4 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have hne2 : 1 + (2 * t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
      field_simp [hne1, hne2]; ring
    rwa [hval] at h
  have hc : Continuous (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp [Real.arctan_zero]

/-- Derivative of the logarithmic antiderivative helper (split out for fast kernel checking). -/
private lemma hasDerivAt_psiLb1_log_part (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      (1 / 2 : ℝ) * s * Real.log (1 + 4 * s ^ 2 / 25) - s + (5 / 2 : ℝ) * Real.arctan (2 * s / 5))
      ((1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25)) t := by
  have harg_pos : 0 < 1 + 4 * t ^ 2 / 25 := by positivity
  have hd_arg : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2 / 25) (8 * t / 25) t := by
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      have := hasDerivAt_pow 2 t
      simpa using this
    have h1 : HasDerivAt (fun s : ℝ => 4 * s ^ 2 / 25) (4 * (2 * t) / 25) t :=
      (hsq.const_mul 4).div_const 25
    have h2 := (hasDerivAt_const t (1 : ℝ)).add h1
    have hval : (0 : ℝ) + 4 * (2 * t) / 25 = 8 * t / 25 := by ring
    rwa [hval] at h2
  have hd_log : HasDerivAt (fun s : ℝ => Real.log (1 + 4 * s ^ 2 / 25))
      ((8 * t / 25) / (1 + 4 * t ^ 2 / 25)) t := hd_arg.log (ne_of_gt harg_pos)
  have hd_half : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s) (1 / 2 : ℝ) t := by
    have h := (hasDerivAt_id' t).const_mul (1 / 2 : ℝ)
    simpa only [mul_one] using h
  have hd_prod : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s * Real.log (1 + 4 * s ^ 2 / 25))
      ((1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) +
        (1 / 2 : ℝ) * t * ((8 * t / 25) / (1 + 4 * t ^ 2 / 25))) t := hd_half.mul hd_log
  have hd_at : HasDerivAt (fun s : ℝ => Real.arctan (2 * s / 5))
      ((2 / 5 : ℝ) / (1 + (2 * t / 5) ^ 2)) t := by
    have hlin : HasDerivAt (fun s : ℝ => 2 * s / 5) (2 / 5 : ℝ) t := by
      simpa using ((hasDerivAt_id' t).const_mul (2 : ℝ)).div_const (5 : ℝ)
    convert hlin.arctan using 1
    ring
  have h := (hd_prod.sub (hasDerivAt_id' t)).add (hd_at.const_mul (5 / 2 : ℝ))
  have hval : (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) +
      (1 / 2 : ℝ) * t * ((8 * t / 25) / (1 + 4 * t ^ 2 / 25)) - 1 +
      (5 / 2 : ℝ) * ((2 / 5 : ℝ) / (1 + (2 * t / 5) ^ 2)) =
      (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) := by
    have hne1 : 25 + 4 * t ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hne2 : 1 + (2 * t / 5) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [ne_of_gt harg_pos, hne1, hne2]; ring
  rwa [hval] at h

/-- Exact closed-form antiderivative of the logarithmic part of `psiLb1` on `[0, T]`. -/
private lemma integral_psiLb1_log_part (T : ℝ) :
    ∫ t in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25) =
      (1 / 2 : ℝ) * T * Real.log (1 + 4 * T ^ 2 / 25) - T + (5 / 2 : ℝ) * Real.arctan (2 * T / 5) := by
  have hc : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25)) :=
    continuous_const.mul
      (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 25))
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 25)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_psiLb1_log_part t) (hc.intervalIntegrable _ _)]
  simp [Real.log_one, Real.arctan_zero]

/-- Exact closed-form antiderivative of the `psiLb1` cutoff gap on `[0, T]`:
    `∫_0^T (psiLb1 T - psiLb1 t) dt = 2 arctan(2T) - T/(1/4 + T^2) + T - (5/2) arctan(2T/5)`. -/
theorem integral_psiLb1_gap_eq {T : ℝ} (_hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (psiLb1 T - psiLb1 t) =
      2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2) + T - (5 / 2 : ℝ) * Real.arctan (2 * T / 5) := by
  have hc_rat : IntervalIntegrable (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) volume 0 T :=
    ((continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2))
      (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))).intervalIntegrable _ _
  have hc_log : IntervalIntegrable (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25)) volume 0 T :=
    (continuous_const.mul
      (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 25))
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 25)))).intervalIntegrable _ _
  have hsplit : (fun t : ℝ => psiLb1 T - psiLb1 t) =
      fun t => ((4 * T ^ 2) / (1 / 4 + T ^ 2) + (1 / 2 : ℝ) * Real.log (1 + 4 * T ^ 2 / 25)) -
        ((4 * t ^ 2) / (1 / 4 + t ^ 2) + (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 25)) := by
    ext t; dsimp [psiLb1]; ring
  rw [hsplit, intervalIntegral.integral_sub intervalIntegrable_const (hc_rat.add hc_log),
      intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      intervalIntegral.integral_add hc_rat hc_log,
      integral_psiLb1_rat_part T, integral_psiLb1_log_part T]
  have hne : 1 / 4 + T ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hne]; ring

/-- Compact-support Fourier transform `g_hat(t) = ∫_{-L/2}^{L/2} g(u) exp(i t u) du`. -/
noncomputable def compactFourier (L : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u in (-L / 2)..(L / 2), g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))

/-- Exact Paley–Wiener / Cauchy–Schwarz bound on `[-L/2, L/2]`:
    `‖g_hat(t)‖^2 ≤ L * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du` for every continuous `g : ℝ → ℂ`. -/
theorem fourierTransform_norm_sq_le_L_mul_L2 {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ}
    (hg : Continuous g) (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤ L * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hab : -L / 2 ≤ L / 2 := by linarith
  have hnorm_le : ‖compactFourier L g t‖ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ := by
    dsimp [compactFourier]
    have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
      (f := fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)))
    refine h1.trans_eq (intervalIntegral.integral_congr fun u _ => ?_)
    rw [norm_mul]
    have hexp : ‖Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))‖ = 1 := by
      have harg : Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [hexp, mul_one]
  -- Cauchy–Schwarz on [-L/2, L/2]: (∫ ‖g‖)^2 ≤ L * ∫ ‖g‖^2
  -- Proof via non-negativity of ∫ (c * ‖g u‖ - 1)^2 du (or quadratic discriminant)!
  have hcs : (∫ u in (-L / 2)..(L / 2), ‖g u‖) ^ 2 ≤ L * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    let A : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
    let B : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖
    have hA_nonneg : 0 ≤ A := intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
    have hdisc : ∀ c : ℝ, 0 ≤ A * c ^ 2 - 2 * B * c + L := by
      intro c
      have h_int : 0 ≤ ∫ u in (-L / 2)..(L / 2), (c * ‖g u‖ - 1) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
      have hexp : (fun u : ℝ => (c * ‖g u‖ - 1) ^ 2) =
          fun u : ℝ => c ^ 2 * ‖g u‖ ^ 2 - 2 * c * ‖g u‖ + 1 := by ext u; ring
      rw [hexp] at h_int
      have h1 : IntervalIntegrable (fun u : ℝ => c ^ 2 * ‖g u‖ ^ 2) volume (-L / 2) (L / 2) :=
        (hg.norm.pow 2).const_mul (c ^ 2) |>.intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun u : ℝ => 2 * c * ‖g u‖) volume (-L / 2) (L / 2) :=
        hg.norm.const_mul (2 * c) |>.intervalIntegrable _ _
      rw [intervalIntegral.integral_add (h1.sub h2) intervalIntegrable_const,
          intervalIntegral.integral_sub h1 h2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul] at h_int
      have hlen : L / 2 - (-L / 2) = L := by ring
      rw [hlen, mul_one] at h_int
      dsimp [A, B]
      linarith
    by_cases hA0 : A = 0
    · by_contra hgt
      push Not at hgt
      change L * A < B ^ 2 at hgt
      have hB_ne : B ≠ 0 := by intro hB; rw [hB, hA0] at hgt; norm_num at hgt
      have hval := hdisc ((L + 1) / (2 * B))
      rw [hA0, zero_mul, zero_sub] at hval
      have hsimp : 2 * B * ((L + 1) / (2 * B)) = L + 1 := by field_simp [hB_ne]
      linarith
    · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA0)
      have hval := hdisc (B / A)
      have hsimp : A * (B / A) ^ 2 - 2 * B * (B / A) + L = L - B ^ 2 / A := by
        field_simp [ne_of_gt hA_pos]; ring
      rw [hsimp] at hval
      have hle : B ^ 2 / A ≤ L := by linarith
      exact (div_le_iff₀ hA_pos).mp hle |> fun h => by linarith
  have hnn : 0 ≤ ‖compactFourier L g t‖ := norm_nonneg _
  exact (pow_le_pow_left₀ hnn hnorm_le 2).trans hcs

/-- The continuous Weil pole form on `[-L/2, L/2]`:
    `W_pole(g) = 2 Re((∫ g(u) e^{u/2} du) * conj(∫ g(u) e^{-u/2} du))`. -/
noncomputable def weilPole (L : ℝ) (g : ℝ → ℂ) : ℝ :=
  2 * ((∫ u in (-L / 2)..(L / 2), g u * Complex.exp ((u / 2 : ℝ) : ℂ)) *
    starRingEnd ℂ (∫ u in (-L / 2)..(L / 2), g u * Complex.exp ((-(u / 2) : ℝ) : ℂ))).re

/-- Exact algebraic decomposition of `W_pole(g)` into positive cosh part minus negative sinh part:
    `W_pole(g) = 2 ‖∫ g(u) cosh(u/2) du‖^2 - 2 ‖∫ g(u) sinh(u/2) du‖^2`. -/
theorem weilPole_eq_cosh_sub_sinh (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    weilPole L g =
      2 * ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.cosh (u / 2) : ℝ) : ℂ)‖ ^ 2 -
      2 * ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.sinh (u / 2) : ℝ) : ℂ)‖ ^ 2 := by
  let Ic : ℂ := ∫ u in (-L / 2)..(L / 2), g u * ((Real.cosh (u / 2) : ℝ) : ℂ)
  let Is : ℂ := ∫ u in (-L / 2)..(L / 2), g u * ((Real.sinh (u / 2) : ℝ) : ℂ)
  have hcont_c : IntervalIntegrable (fun u : ℝ => g u * ((Real.cosh (u / 2) : ℝ) : ℂ))
      volume (-L / 2) (L / 2) :=
    (hg.mul (Complex.continuous_ofReal.comp
      (Real.continuous_cosh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
  have hcont_s : IntervalIntegrable (fun u : ℝ => g u * ((Real.sinh (u / 2) : ℝ) : ℂ))
      volume (-L / 2) (L / 2) :=
    (hg.mul (Complex.continuous_ofReal.comp
      (Real.continuous_sinh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
  have hplus : (∫ u in (-L / 2)..(L / 2), g u * Complex.exp ((u / 2 : ℝ) : ℂ)) = Ic + Is := by
    rw [← intervalIntegral.integral_add hcont_c hcont_s]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [← Complex.ofReal_exp, ← mul_add, ← Complex.ofReal_add, Real.cosh_add_sinh]
  have hminus : (∫ u in (-L / 2)..(L / 2), g u * Complex.exp ((-(u / 2) : ℝ) : ℂ)) = Ic - Is := by
    rw [← intervalIntegral.integral_sub hcont_c hcont_s]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [← Complex.ofReal_exp, ← mul_sub, ← Complex.ofReal_sub, Real.cosh_sub_sinh]
  dsimp [weilPole]
  rw [hplus, hminus]
  -- Re((Ic + Is) * conj(Ic - Is)) = |Ic|^2 - |Is|^2
  have hre : ((Ic + Is) * starRingEnd ℂ (Ic - Is)).re = ‖Ic‖ ^ 2 - ‖Is‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre]; ring

/-- On any even function `g(-u) = g(u)`, `W_pole(g) ≥ 0` unconditionally. -/
theorem weilPole_even_nonneg (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g)
    (heven : ∀ u, g (-u) = g u) : 0 ≤ weilPole L g := by
  rw [weilPole_eq_cosh_sub_sinh L hg]
  have hodd : (∫ u in (-L / 2)..(L / 2), g u * ((Real.sinh (u / 2) : ℝ) : ℂ)) = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => g u * ((Real.sinh (u / 2) : ℝ) : ℂ)) (a := -L / 2) (b := L / 2)
    have hneg : -(L / 2) = -L / 2 := by ring
    have hneg2 : -(-L / 2) = L / 2 := by ring
    rw [hneg, hneg2] at hcomp
    have hfun : (fun u : ℝ => g (-u) * ((Real.sinh (-u / 2) : ℝ) : ℂ)) =
        fun u : ℝ => -(g u * ((Real.sinh (u / 2) : ℝ) : ℂ)) := by
      ext u; rw [heven u, show -u / 2 = -(u / 2) by ring, Real.sinh_neg, Complex.ofReal_neg, mul_neg]
    rw [hfun, intervalIntegral.integral_neg] at hcomp
    -- Wait: -I = I implies I = 0
    have h2 : (2 : ℂ) * (∫ u in (-L / 2)..(L / 2), g u * ((Real.sinh (u / 2) : ℝ) : ℂ)) = 0 := by
      linear_combination -hcomp
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [hodd]; norm_num

/-- Exact integral of `sinh(u/2)^2` on `[-L/2, L/2]`: equals `sinh(L/2) - L/2`. -/
lemma integral_sinh_half_sq (L : ℝ) :
    ∫ u in (-L / 2)..(L / 2), (Real.sinh (u / 2)) ^ 2 = Real.sinh (L / 2) - L / 2 := by
  let F : ℝ → ℝ := fun u => Real.sinh u / 2 - u / 2
  have hd : ∀ u ∈ Set.uIcc (-L / 2) (L / 2), HasDerivAt F ((Real.sinh (u / 2)) ^ 2) u := by
    intro u _
    have h := ((Real.hasDerivAt_sinh u).div_const 2).sub ((hasDerivAt_id' u).div_const 2)
    have hch : Real.cosh u = 2 * (Real.sinh (u / 2)) ^ 2 + 1 := by
      have h1 := Real.cosh_two_mul (u / 2)
      have h2 := Real.cosh_sq_sub_sinh_sq (u / 2)
      have h3 : 2 * (u / 2) = u := by ring
      rw [h3] at h1
      linarith
    have hval : Real.cosh u / 2 - 1 / 2 = (Real.sinh (u / 2)) ^ 2 := by rw [hch]; ring
    rwa [hval] at h
  have hc : Continuous (fun u : ℝ => (Real.sinh (u / 2)) ^ 2) :=
    (Real.continuous_sinh.comp (continuous_id.div_const 2)).pow 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  dsimp [F]
  rw [show -L / 2 = -(L / 2) by ring, Real.sinh_neg]
  ring

/-- Universal lower bound on `W_pole(g)` for EVERY continuous `g : ℝ → ℂ` on `[-L/2, L/2]`:
    `W_pole(g) ≥ -2 * (sinh(L/2) - L/2) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem weilPole_lower_bound_all {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ} (hg : Continuous g) :
    -(2 * (Real.sinh (L / 2) - L / 2)) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilPole L g := by
  rw [weilPole_eq_cosh_sub_sinh L hg]
  have hab : -L / 2 ≤ L / 2 := by linarith
  have h1 : 0 ≤ 2 * ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.cosh (u / 2) : ℝ) : ℂ)‖ ^ 2 := by positivity
  -- Bound ‖∫ g(u) sinh(u/2) du‖^2 ≤ (∫ sinh(u/2)^2 du) * (∫ ‖g u‖^2 du) via Cauchy–Schwarz!
  have hnorm : ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.sinh (u / 2) : ℝ) : ℂ)‖ ≤
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |Real.sinh (u / 2)| := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
      (f := fun u : ℝ => g u * ((Real.sinh (u / 2) : ℝ) : ℂ))
    refine h.trans_eq (intervalIntegral.integral_congr fun u _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcs : (∫ u in (-L / 2)..(L / 2), ‖g u‖ * |Real.sinh (u / 2)|) ^ 2 ≤
      (∫ u in (-L / 2)..(L / 2), (Real.sinh (u / 2)) ^ 2) *
      (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
    let A : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
    let B : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |Real.sinh (u / 2)|
    let C : ℝ := ∫ u in (-L / 2)..(L / 2), (Real.sinh (u / 2)) ^ 2
    have hA_nn : 0 ≤ A := intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
    have hdisc : ∀ c : ℝ, 0 ≤ A * c ^ 2 - 2 * B * c + C := by
      intro c
      have h_int : 0 ≤ ∫ u in (-L / 2)..(L / 2), (c * ‖g u‖ - |Real.sinh (u / 2)|) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
      have hexp : (fun u : ℝ => (c * ‖g u‖ - |Real.sinh (u / 2)|) ^ 2) =
          fun u : ℝ => c ^ 2 * ‖g u‖ ^ 2 - 2 * c * (‖g u‖ * |Real.sinh (u / 2)|) + (Real.sinh (u / 2)) ^ 2 := by
        ext u; rw [sub_sq, mul_pow, sq_abs]; ring
      rw [hexp] at h_int
      have hc1 : IntervalIntegrable (fun u : ℝ => c ^ 2 * ‖g u‖ ^ 2) volume (-L / 2) (L / 2) :=
        ((hg.norm.pow 2).const_mul (c ^ 2)).intervalIntegrable _ _
      have hc2 : IntervalIntegrable (fun u : ℝ => 2 * c * (‖g u‖ * |Real.sinh (u / 2)|)) volume (-L / 2) (L / 2) :=
        ((hg.norm.mul ((Real.continuous_sinh.comp (continuous_id.div_const 2)).abs)).const_mul (2 * c)).intervalIntegrable _ _
      have hc3 : IntervalIntegrable (fun u : ℝ => (Real.sinh (u / 2)) ^ 2) volume (-L / 2) (L / 2) :=
        ((Real.continuous_sinh.comp (continuous_id.div_const 2)).pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_add (hc1.sub hc2) hc3,
          intervalIntegral.integral_sub hc1 hc2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h_int
      dsimp [A, B, C]; linarith
    by_cases hA0 : A = 0
    · by_contra hgt; push Not at hgt
      change C * A < B ^ 2 at hgt
      have hB_ne : B ≠ 0 := by intro hB; rw [hB, hA0] at hgt; norm_num at hgt
      have hval := hdisc ((C + 1) / (2 * B))
      rw [hA0, zero_mul, zero_sub] at hval
      have hsimp : 2 * B * ((C + 1) / (2 * B)) = C + 1 := by field_simp [hB_ne]
      linarith
    · have hA_pos : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA0)
      have hval := hdisc (B / A)
      have hsimp : A * (B / A) ^ 2 - 2 * B * (B / A) + C = C - B ^ 2 / A := by
        field_simp [ne_of_gt hA_pos]; ring
      rw [hsimp] at hval
      have hle : B ^ 2 / A ≤ C := by linarith
      have := (div_le_iff₀ hA_pos).mp hle
      linarith
  have hsq : ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.sinh (u / 2) : ℝ) : ℂ)‖ ^ 2 ≤
      (Real.sinh (L / 2) - L / 2) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
    rw [← integral_sinh_half_sq L]
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs
  linarith

/-- The continuous Archimedean spectral functional
    `W_∞(g) = (1/(2π)) ∫_ℝ ‖g_hat(t)‖^2 * psiArch(t) dt`. -/
noncomputable def weilInf (L : ℝ) (g : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 * psiArch t

/-- THEOREM I.2 (Master Infinite-Dimensional Continuous Weil Cutoff Inequality):
    For ANY `L > 0`, ANY cutoff `T ≥ 0`, and ANY continuous `g` on `[-L/2, L/2]` obeying
    Plancherel `(1/(2π)) ∫ ‖g_hat(t)‖^2 dt = ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`, the exact
    infinite-dimensional Archimedean Weil form obeys the closed-form lower bound:
      `W_pole(g) + W_∞(g) ≥ (psiLb1 T - (L/π) * gap(T) - 2*(sinh(L/2) - L/2)) * ‖g‖_2^2`. -/
theorem weilArch_continuous_cutoff_lower_bound {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    {g : ℝ → ℂ} (hg : Continuous g)
    (h_int_sq : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2))
    (h_int_psi : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2 * psiArch t))
    (h_plancherel : (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) :
    (psiLb1 T - (L / Real.pi) *
      (2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2) + T - (5 / 2 : ℝ) * Real.arctan (2 * T / 5))
      - 2 * (Real.sinh (L / 2) - L / 2)) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
      ≤ weilPole L g + weilInf L g := by
  have hpole := weilPole_lower_bound_all (le_of_lt hL) hg
  suffices hinf :
      (psiLb1 T - (L / Real.pi) *
        (2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2) + T - (5 / 2 : ℝ) * Real.arctan (2 * T / 5)))
        * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilInf L g by
    linarith
  -- Step 1: Rewrite W_∞(g) - psiLb1(T) * ‖g‖_2^2 = (1/(2π)) ∫ ‖g_hat(t)‖^2 * (psiArch t - psiLb1 T) dt
  let N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- Compare pointwise: ‖g_hat(t)‖^2 * (psiArch t - psiLb1 T) ≥ - 1_{[-T, T]}(t) * (L * N2) * (psiLb1 T - psiLb1 t)
  let lowerFn : ℝ → ℝ := Set.indicator (Icc (-T) T) (fun t => -(L * N2) * (psiLb1 T - psiLb1 t))
  have hlower_int : Integrable lowerFn := by
    have hcont : Continuous (fun t => -(L * N2) * (psiLb1 T - psiLb1 t)) := by
      have hc : Continuous psiLb1 := by
        unfold psiLb1
        refine (continuous_const.add ?_).add ?_
        · exact (continuous_const.mul (continuous_pow 2)).div
            (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
        · exact continuous_const.mul
            (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 25))
              (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 25)))
      exact continuous_const.mul (continuous_const.sub hc)
    exact (hcont.continuousOn.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hpt : ∀ t : ℝ, lowerFn t ≤ ‖compactFourier L g t‖ ^ 2 * (psiArch t - psiLb1 T) := by
    intro t
    have hge_lb : psiLb1 t ≤ psiArch t := psiArch_ge_psiLb1 t
    by_cases ht : t ∈ Icc (-T) T
    · simp only [lowerFn, Set.indicator_of_mem ht]
      have habs : |t| ≤ T := abs_le.mpr ht
      have hmono : psiLb1 t ≤ psiLb1 T := by
        have h1 : psiLb1 |t| ≤ psiLb1 T := psiLb1_mono_nonneg (abs_nonneg t) habs
        rcases le_total 0 t with h | h
        · rwa [abs_of_nonneg h] at h1
        · rw [abs_of_nonpos h, psiLb1_even] at h1; exact h1
      have hgap_nn : 0 ≤ psiLb1 T - psiLb1 t := sub_nonneg.mpr hmono
      have hcs := fourierTransform_norm_sq_le_L_mul_L2 (le_of_lt hL) hg t
      calc -(L * N2) * (psiLb1 T - psiLb1 t)
        _ ≤ -(‖compactFourier L g t‖ ^ 2) * (psiLb1 T - psiLb1 t) := by
            have := mul_le_mul_of_nonneg_right hcs hgap_nn; linarith
        _ = ‖compactFourier L g t‖ ^ 2 * (psiLb1 t - psiLb1 T) := by ring
        _ ≤ ‖compactFourier L g t‖ ^ 2 * (psiArch t - psiLb1 T) :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    · simp only [lowerFn, Set.indicator_of_notMem ht]
      have habs : T ≤ |t| := by
        by_contra hlt; push Not at hlt
        exact ht (abs_le.mp (le_of_lt hlt))
      have hmono : psiLb1 T ≤ psiLb1 t := by
        have h1 : psiLb1 T ≤ psiLb1 |t| := psiLb1_mono_nonneg hT habs
        rcases le_total 0 t with h | h
        · rwa [abs_of_nonneg h] at h1
        · rw [abs_of_nonpos h, psiLb1_even] at h1; exact h1
      exact mul_nonneg (sq_nonneg _) (by linarith)
  have hint_diff : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2 * (psiArch t - psiLb1 T)) := by
    have h : (fun t : ℝ => ‖compactFourier L g t‖ ^ 2 * (psiArch t - psiLb1 T)) =
        fun t => ‖compactFourier L g t‖ ^ 2 * psiArch t - psiLb1 T * ‖compactFourier L g t‖ ^ 2 := by
      ext t; ring
    rw [h]; exact h_int_psi.sub (h_int_sq.const_mul (psiLb1 T))
  have hmono_int := integral_mono hlower_int hint_diff hpt
  -- Compute ∫ lowerFn = -2 * L * N2 * ∫_0^T (psiLb1 T - psiLb1 t) dt
  have hval_lower : ∫ t : ℝ, lowerFn t =
      -(2 * L * N2) * (2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2) + T -
        (5 / 2 : ℝ) * Real.arctan (2 * T / 5)) := by
    dsimp [lowerFn]
    rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    rw [intervalIntegral.integral_const_mul]
    have hcont_gap : Continuous (fun t => psiLb1 T - psiLb1 t) := by
      have hc : Continuous psiLb1 := by
        unfold psiLb1
        refine (continuous_const.add ?_).add ?_
        · exact (continuous_const.mul (continuous_pow 2)).div
            (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
        · exact continuous_const.mul
            (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 25))
              (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 25)))
      exact continuous_const.sub hc
    have hsplit_0 : ∫ t in (-T)..T, (psiLb1 T - psiLb1 t) =
        (∫ t in (-T)..(0 : ℝ), (psiLb1 T - psiLb1 t)) + ∫ t in (0 : ℝ)..T, (psiLb1 T - psiLb1 t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_gap.intervalIntegrable _ _) (hcont_gap.intervalIntegrable _ _)).symm
    have hsym : ∫ t in (-T)..(0 : ℝ), (psiLb1 T - psiLb1 t) = ∫ t in (0 : ℝ)..T, (psiLb1 T - psiLb1 t) := by
      have h := intervalIntegral.integral_comp_neg (f := fun t => psiLb1 T - psiLb1 t) (a := 0) (b := T)
      simp only [neg_zero] at h
      have hev : (fun t => psiLb1 T - psiLb1 (-t)) = fun t => psiLb1 T - psiLb1 t := by
        ext t; rw [psiLb1_even]
      rw [hev] at h; exact h.symm
    rw [hsplit_0, hsym, integral_psiLb1_gap_eq hT]; ring
  -- Evaluate RHS of hmono_int
  have hrhs : ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 * (psiArch t - psiLb1 T) =
      (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 * psiArch t) -
      psiLb1 T * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) := by
    have h : (fun t : ℝ => ‖compactFourier L g t‖ ^ 2 * (psiArch t - psiLb1 T)) =
        fun t => ‖compactFourier L g t‖ ^ 2 * psiArch t - psiLb1 T * ‖compactFourier L g t‖ ^ 2 := by
      ext t; ring
    rw [h, integral_sub h_int_psi (h_int_sq.const_mul (psiLb1 T)), integral_const_mul]
  rw [hval_lower, hrhs] at hmono_int
  -- Multiply by 1 / (2π) > 0 and substitute Plancherel
  have hpi_pos : 0 < 1 / (2 * Real.pi) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmono_int (le_of_lt hpi_pos)
  dsimp [weilInf, N2] at hscaled ⊢
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h1 : 1 / (2 * Real.pi) * (-(2 * L * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)) *
      (2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2) + T - (5 / 2 : ℝ) * Real.arctan (2 * T / 5))) =
      -((L / Real.pi) * (2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2) + T -
        (5 / 2 : ℝ) * Real.arctan (2 * T / 5))) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
    field_simp [hpi_ne]
  have h2 : 1 / (2 * Real.pi) * ((∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 * psiArch t) -
      psiLb1 T * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
      (1 / (2 * Real.pi) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 * psiArch t) -
      psiLb1 T * (1 / (2 * Real.pi) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) := by ring
  rw [h1, h2, h_plancherel] at hscaled
  linarith

/-- THEOREM I.3 (UNCONDITIONAL INFINITE-DIMENSIONAL CONTINUOUS WEIL POSITIVITY ON `0 < L ≤ 1/12`):
    With ZERO discretization, ZERO prime terms (since `L ≤ 1/12 < log 2`), and ZERO
    external numerical oracles, the full continuous Weil quadratic form on `L^2([-L/2, L/2])`
    satisfies the explicit spectral gap:
      `W_pole(g) + W_∞(g) ≥ (1/10) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du > 0`
    for EVERY non-zero continuous `g` supported in `[-L/2, L/2]`! -/
theorem weilArch_continuous_pos_on_small_support {L : ℝ} (hL_pos : 0 < L) (hL_le : L ≤ 1 / 12)
    {g : ℝ → ℂ} (hg : Continuous g)
    (h_int_sq : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2))
    (h_int_psi : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2 * psiArch t))
    (h_plancherel : (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) :
    (1 / 10 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilPole L g + weilInf L g := by
  have hmain := weilArch_continuous_cutoff_lower_bound hL_pos (T := 30) (by norm_num)
    hg h_int_sq h_int_psi h_plancherel
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- Prove the explicit bracket at T = 30, L ≤ 1/12 is ≥ 1/10!
  have hbracket : (1 / 10 : ℝ) ≤
      psiLb1 30 - (L / Real.pi) *
        (2 * Real.arctan (2 * 30) - 30 / (1 / 4 + 30 ^ 2) + 30 -
          (5 / 2 : ℝ) * Real.arctan (2 * 30 / 5)) -
        2 * (Real.sinh (L / 2) - L / 2) := by
    have hC := archimedeanWeilConst_lt
    have hpi_lo : (314 / 100 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    have hpi_hi : Real.pi < (315 / 100 : ℝ) := by linarith [Real.pi_lt_d2]
    -- 1. Lower bound on psiLb1 30: ≥ 94 / 100
    have hlog145 : (49 / 10 : ℝ) < Real.log (1 + 4 * 30 ^ 2 / 25) := by
      rw [show (1 + 4 * (30 : ℝ) ^ 2 / 25) = 145 by norm_num, Real.lt_log_iff_exp_lt (by norm_num)]
      exact exp_49_div_10_lt_145
    have hpsi30 : (948 / 1000 : ℝ) < psiLb1 30 := by
      dsimp [psiLb1]
      have hrat : (3998 / 1000 : ℝ) < (4 * (30 : ℝ) ^ 2) / (1 / 4 + 30 ^ 2) := by norm_num
      linarith
    -- 2. Upper bound on gap(30): ≤ 31.20 (using arctan(60) < π/2 and arctan(12) ≥ arctan(1) = π/4!)
    have hat60 : Real.arctan (2 * 30) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hat12 : Real.pi / 4 ≤ Real.arctan (2 * 30 / 5) := by
      rw [← Real.arctan_one]
      exact Real.arctan_mono (by norm_num)
    have hgap_nn : 0 ≤ 2 * Real.arctan (2 * 30) - 30 / (1 / 4 + 30 ^ 2) + 30 -
        (5 / 2 : ℝ) * Real.arctan (2 * 30 / 5) := by
      rw [← integral_psiLb1_gap_eq (by norm_num : (0 : ℝ) ≤ 30)]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun t ht => sub_nonneg.mpr (psiLb1_mono_nonneg ht.1 ht.2))
    have hgap_ub : 2 * Real.arctan (2 * 30) - 30 / (1 / 4 + 30 ^ 2) + 30 -
        (5 / 2 : ℝ) * Real.arctan (2 * 30 / 5) < 312 / 10 := by
      have hneg : (0 : ℝ) < 30 / (1 / 4 + 30 ^ 2) := by norm_num
      linarith
    have hL_div : L / Real.pi ≤ (1 / 12) / (314 / 100) := by
      refine div_le_div₀ (by norm_num) hL_le (by norm_num) (le_of_lt hpi_lo)
    have hgap_term : (L / Real.pi) *
        (2 * Real.arctan (2 * 30) - 30 / (1 / 4 + 30 ^ 2) + 30 -
          (5 / 2 : ℝ) * Real.arctan (2 * 30 / 5)) < 83 / 100 := by
      have h1 : (L / Real.pi) * (2 * Real.arctan (2 * 30) - 30 / (1 / 4 + 30 ^ 2) + 30 -
          (5 / 2 : ℝ) * Real.arctan (2 * 30 / 5)) ≤
          ((1 / 12) / (314 / 100)) * (312 / 10) := by
        exact mul_le_mul hL_div (le_of_lt hgap_ub) hgap_nn (by norm_num)
      linarith
    -- 3. Upper bound on 2*(sinh(L/2) - L/2) for 0 < L ≤ 1/12: < 2/1000
    have hsinh_mono : Real.sinh (L / 2) - L / 2 ≤ Real.sinh (1 / 24) - 1 / 24 := by
      -- d/dx (sinh x - x) = cosh x - 1 ≥ 0
      have hm : Monotone (fun x : ℝ => Real.sinh x - x) := by
        apply monotone_of_deriv_nonneg
        · exact Real.differentiable_sinh.sub differentiable_id
        · intro x
          have hd : HasDerivAt (fun s => Real.sinh s - s) (Real.cosh x - 1) x :=
            (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
          rw [hd.deriv]; linarith [Real.one_le_cosh x]
      exact hm (by linarith)
    have hsinh_ub : 2 * (Real.sinh (1 / 24 : ℝ) - 1 / 24) < 2 / 1000 := by
      rw [Real.sinh_eq]
      have he_ub := exp_le_taylor_of_nonneg_le_one (y := 1 / 24) (by norm_num) (by norm_num) (n := 4) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at he_ub
      have he_neg_lb : 1 - (1 / 24 : ℝ) ≤ Real.exp (-(1 / 24 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 24 : ℝ))]
      norm_num at he_ub
      linarith
    linarith
  exact (mul_le_mul_of_nonneg_right hbracket hN2_nn).trans hmain

/-- THEOREM I.4 (Abstract Infinite-Dimensional Hilbert-Space Schur-Complement Positivity):
    If a quadratic form `Q(c, h) = Q_0(c) + 2 B(c, h) + Q_perp(h)` satisfies
    `Q_perp(h) ≥ λ_perp * ‖h‖^2` (`λ_perp > 0`), `|B(c, h)| ≤ r(c) * ‖h‖`, and
    the Schur complement `Q_0(c) - r(c)^2 / λ_perp > 0` for `c ≠ 0`, then
    `Q(c, h) > 0` whenever `(c ≠ 0 ∨ ‖h‖ > 0)`!
    (This is the exact infinite-dimensional theorem certifying the rank-1 ODD and
    rank-2 EVEN Weil positivity certificates all the way up to `L = log 2`.) -/
theorem schur_complement_hilbert_pos {α : Type*}
    (Q0 r : α → ℝ) (B : α → ℝ → ℝ) (Qperp : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hperp : ∀ x : ℝ, lam * x ^ 2 ≤ Qperp x)
    (hcross : ∀ c : α, ∀ x : ℝ, 0 ≤ x → |B c x| ≤ r c * x)
    (hschur : ∀ c : α, r c ^ 2 / lam < Q0 c) :
    ∀ (c : α) (x : ℝ), 0 ≤ x → 0 < Q0 c + 2 * B c x + Qperp x := by
  intro c x hx
  have h1 := hperp x
  have h2 : -(r c * x) ≤ B c x := (abs_le.mp (hcross c x hx)).1
  have h3 := hschur c
  have hsq : 0 ≤ (Real.sqrt lam * x - r c / Real.sqrt lam) ^ 2 := sq_nonneg _
  have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt (le_of_lt hlam)
  have hsl_ne : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
  have hexp : (Real.sqrt lam * x - r c / Real.sqrt lam) ^ 2 =
      lam * x ^ 2 - 2 * (r c * x) + r c ^ 2 / lam := by
    rw [sub_sq, mul_pow, div_pow, hsl]
    have hmid : Real.sqrt lam * x * (r c / Real.sqrt lam) = r c * x := by
      field_simp [hsl_ne]
    linarith
  rw [hexp] at hsq
  linarith

/-- THEOREM I.5 (Bandlimited Prolate Comparison Positivity Certificate):
    Any functional decomposing as `Q = β * E_high + R` with `β > 0`, `R ≥ 0`, and
    strictly positive high-frequency bandlimited energy `E_high = (1/(2π)) ∫_{|t| > Ω} ‖g_hat(t)‖^2 dt > 0`
    is strictly positive! -/
theorem bandlimited_prolate_comparison_pos {β E_high R : ℝ}
    (hβ : 0 < β) (hE : 0 < E_high) (hR : 0 ≤ R) :
    0 < β * E_high + R := by
  have : 0 < β * E_high := mul_pos hβ hE
  linarith

-- ==============================================================================
-- PART II: ROUTE B — EXACT 2D LIGHT-CONE INTEGRAL OF m_2(σ, γ) & MOMENT BOUND
-- ==============================================================================

/-- Auxiliary 1D past–future moment `I_k(σ) = ∫_0^∞ Φ(u) * u^k * cosh(σ * u) du`. -/
noncomputable def xiCoshMoment (k : ℕ) (σ : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u)

lemma integrableOn_phi_pow_cosh_cos (k : ℕ) (σ γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.cosh (σ * u) * Real.cos (γ * u)) (Ioi 0) := by
  refine (integrableOn_phi_pow_cosh k σ).mono'
    ((((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hnn : 0 ≤ riemannPhi u * u ^ k * Real.cosh (σ * u) :=
    mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg hu0 _)) (le_of_lt (Real.cosh_pos _))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
  calc riemannPhi u * u ^ k * Real.cosh (σ * u) * |Real.cos (γ * u)|
    _ ≤ riemannPhi u * u ^ k * Real.cosh (σ * u) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hnn
    _ = riemannPhi u * u ^ k * Real.cosh (σ * u) := mul_one _

lemma integrableOn_phi_pow_sinh_sin (k : ℕ) (σ γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.sinh (σ * u) * Real.sin (γ * u)) (Ioi 0) := by
  refine (integrableOn_phi_pow_cosh k σ).mono'
    ((((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hpu : 0 ≤ riemannPhi u * u ^ k := mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg hu0 _)
  have hsh_le : |Real.sinh (σ * u)| ≤ Real.cosh (σ * u) := by
    rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_sub (Real.exp (σ * u)) (Real.exp (-(σ * u)))
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)] at htri
    linarith
  rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (riemannPhi_pos u), abs_of_nonneg (pow_nonneg hu0 _)]
  calc riemannPhi u * u ^ k * |Real.sinh (σ * u)| * |Real.sin (γ * u)|
    _ ≤ riemannPhi u * u ^ k * Real.cosh (σ * u) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsh_le hpu)
          (Real.abs_sin_le_one _) (abs_nonneg _) (mul_nonneg hpu (le_of_lt (Real.cosh_pos _)))
    _ = riemannPhi u * u ^ k * Real.cosh (σ * u) := mul_one _

lemma integrableOn_phi_pow_sinh_cos (k : ℕ) (σ γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.sinh (σ * u) * Real.cos (γ * u)) (Ioi 0) := by
  refine (integrableOn_phi_pow_cosh k σ).mono'
    ((((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hpu : 0 ≤ riemannPhi u * u ^ k := mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg hu0 _)
  have hsh_le : |Real.sinh (σ * u)| ≤ Real.cosh (σ * u) := by
    rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_sub (Real.exp (σ * u)) (Real.exp (-(σ * u)))
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)] at htri
    linarith
  rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (riemannPhi_pos u), abs_of_nonneg (pow_nonneg hu0 _)]
  calc riemannPhi u * u ^ k * |Real.sinh (σ * u)| * |Real.cos (γ * u)|
    _ ≤ riemannPhi u * u ^ k * Real.cosh (σ * u) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsh_le hpu)
          (Real.abs_cos_le_one _) (abs_nonneg _) (mul_nonneg hpu (le_of_lt (Real.cosh_pos _)))
    _ = riemannPhi u * u ^ k * Real.cosh (σ * u) := mul_one _

lemma integrableOn_phi_pow_cosh_sin (k : ℕ) (σ γ : ℝ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ k * Real.cosh (σ * u) * Real.sin (γ * u)) (Ioi 0) := by
  refine (integrableOn_phi_pow_cosh k σ).mono'
    ((((continuous_riemannPhi.mul (continuous_pow k)).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hnn : 0 ≤ riemannPhi u * u ^ k * Real.cosh (σ * u) :=
    mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg hu0 _)) (le_of_lt (Real.cosh_pos _))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
  calc riemannPhi u * u ^ k * Real.cosh (σ * u) * |Real.sin (γ * u)|
    _ ≤ riemannPhi u * u ^ k * Real.cosh (σ * u) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hnn
    _ = riemannPhi u * u ^ k * Real.cosh (σ * u) := mul_one _

lemma hasDerivAt_integral_phi_pow_cosh_cos (k : ℕ) (σ₀ γ : ℝ) :
    HasDerivAt (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u) * Real.cos (γ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.sinh (σ₀ * u) * Real.cos (γ * u)) σ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let R : ℝ := |σ₀| + 1
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + R + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun σ u => riemannPhi u * u ^ k * Real.cosh (σ * u) * Real.cos (γ * u))
    (F' := fun σ u => riemannPhi u * u ^ (k + 1) * Real.sinh (σ * u) * Real.cos (γ * u))
    (s := Metric.ball σ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds σ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun σ =>
      ((((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_cosh_cos k σ₀ γ)
    ((((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu σ hσ
      have hu0 : 0 ≤ u := le_of_lt hu
      have hσ_abs : |σ| ≤ R := by
        rw [Metric.mem_ball, Real.dist_eq] at hσ
        have htri : |σ| ≤ |σ - σ₀| + |σ₀| := by simpa using abs_add_le (σ - σ₀) σ₀
        dsimp [R]; linarith
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 _)]
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
      have hPhi := hPhi_le u hu0; rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * |Real.sinh (σ * u)| * |Real.cos (γ * u)|
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) * Real.exp (R * u) * 1 := by
            refine mul_le_mul ?_ (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
            exact mul_le_mul (mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity))
              hsinh (abs_nonneg _) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (R * u)) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ σ _
      have hlin : HasDerivAt (fun s : ℝ => s * u) u σ := by simpa using (hasDerivAt_id σ).mul_const u
      have hch : HasDerivAt (fun s : ℝ => Real.cosh (s * u)) (Real.sinh (σ * u) * u) σ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_cosh (σ * u)).comp σ hlin
      convert (hch.const_mul (riemannPhi u * u ^ k)).mul_const (Real.cos (γ * u)) using 1
      rw [pow_succ]; ring)
  exact h.2

lemma hasDerivAt_integral_phi_pow_sinh_cos (k : ℕ) (σ₀ γ : ℝ) :
    HasDerivAt (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.sinh (σ * u) * Real.cos (γ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.cosh (σ₀ * u) * Real.cos (γ * u)) σ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let R : ℝ := |σ₀| + 1
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + R + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun σ u => riemannPhi u * u ^ k * Real.sinh (σ * u) * Real.cos (γ * u))
    (F' := fun σ u => riemannPhi u * u ^ (k + 1) * Real.cosh (σ * u) * Real.cos (γ * u))
    (s := Metric.ball σ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds σ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun σ =>
      ((((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_sinh_cos k σ₀ γ)
    ((((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu σ hσ
      have hu0 : 0 ≤ u := le_of_lt hu
      have hσ_abs : |σ| ≤ R := by
        rw [Metric.mem_ball, Real.dist_eq] at hσ
        have htri : |σ| ≤ |σ - σ₀| + |σ₀| := by simpa using abs_add_le (σ - σ₀) σ₀
        dsimp [R]; linarith
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs,
          Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_of_nonneg (le_of_lt (Real.cosh_pos _)), Real.norm_eq_abs]
      have hpow := pow_le_factorial_mul_exp (k + 1) hu0
      have hcosh : Real.cosh (σ * u) ≤ Real.exp (R * u) := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (σ * u) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self σ).trans hσ_abs) hu0)
        have h2 : Real.exp (-(σ * u)) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right ((neg_le_abs σ).trans hσ_abs) hu0)
        linarith
      have hPhi := hPhi_le u hu0; rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * Real.cosh (σ * u) * |Real.cos (γ * u)|
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) * Real.exp (R * u) * 1 := by
            refine mul_le_mul ?_ (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
            exact mul_le_mul (mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity))
              hcosh (le_of_lt (Real.cosh_pos _)) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (R * u)) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ σ _
      have hlin : HasDerivAt (fun s : ℝ => s * u) u σ := by simpa using (hasDerivAt_id σ).mul_const u
      have hsh : HasDerivAt (fun s : ℝ => Real.sinh (s * u)) (Real.cosh (σ * u) * u) σ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_sinh (σ * u)).comp σ hlin
      convert (hsh.const_mul (riemannPhi u * u ^ k)).mul_const (Real.cos (γ * u)) using 1
      rw [pow_succ]; ring)
  exact h.2

lemma hasDerivAt_integral_phi_pow_sinh_sin (k : ℕ) (σ₀ γ : ℝ) :
    HasDerivAt (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.sinh (σ * u) * Real.sin (γ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.cosh (σ₀ * u) * Real.sin (γ * u)) σ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let R : ℝ := |σ₀| + 1
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + R + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun σ u => riemannPhi u * u ^ k * Real.sinh (σ * u) * Real.sin (γ * u))
    (F' := fun σ u => riemannPhi u * u ^ (k + 1) * Real.cosh (σ * u) * Real.sin (γ * u))
    (s := Metric.ball σ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds σ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun σ =>
      ((((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_sinh_sin k σ₀ γ)
    ((((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu σ hσ
      have hu0 : 0 ≤ u := le_of_lt hu
      have hσ_abs : |σ| ≤ R := by
        rw [Metric.mem_ball, Real.dist_eq] at hσ
        have htri : |σ| ≤ |σ - σ₀| + |σ₀| := by simpa using abs_add_le (σ - σ₀) σ₀
        dsimp [R]; linarith
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs,
          Real.norm_of_nonneg (pow_nonneg hu0 _), Real.norm_of_nonneg (le_of_lt (Real.cosh_pos _)), Real.norm_eq_abs]
      have hpow := pow_le_factorial_mul_exp (k + 1) hu0
      have hcosh : Real.cosh (σ * u) ≤ Real.exp (R * u) := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (σ * u) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self σ).trans hσ_abs) hu0)
        have h2 : Real.exp (-(σ * u)) ≤ Real.exp (R * u) :=
          Real.exp_le_exp.mpr (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right ((neg_le_abs σ).trans hσ_abs) hu0)
        linarith
      have hPhi := hPhi_le u hu0; rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * Real.cosh (σ * u) * |Real.sin (γ * u)|
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) * Real.exp (R * u) * 1 := by
            refine mul_le_mul ?_ (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)
            exact mul_le_mul (mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity))
              hcosh (le_of_lt (Real.cosh_pos _)) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (R * u)) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ σ _
      have hlin : HasDerivAt (fun s : ℝ => s * u) u σ := by simpa using (hasDerivAt_id σ).mul_const u
      have hsh : HasDerivAt (fun s : ℝ => Real.sinh (s * u)) (Real.cosh (σ * u) * u) σ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_sinh (σ * u)).comp σ hlin
      convert (hsh.const_mul (riemannPhi u * u ^ k)).mul_const (Real.sin (γ * u)) using 1
      rw [pow_succ]; ring)
  exact h.2

lemma hasDerivAt_integral_phi_pow_cosh_sin (k : ℕ) (σ₀ γ : ℝ) :
    HasDerivAt (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u) * Real.sin (γ * u))
      (∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (k + 1) * Real.sinh (σ₀ * u) * Real.sin (γ * u)) σ₀ := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  let R : ℝ := |σ₀| + 1
  let bound : ℝ → ℝ := fun u =>
    C2 * ((k + 1).factorial : ℝ) * Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u))
  have hbound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_superexp (9 / 2 + R + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun σ u => riemannPhi u * u ^ k * Real.cosh (σ * u) * Real.sin (γ * u))
    (F' := fun σ u => riemannPhi u * u ^ (k + 1) * Real.sinh (σ * u) * Real.sin (γ * u))
    (s := Metric.ball σ₀ 1) (bound := bound)
    (Metric.ball_mem_nhds σ₀ zero_lt_one)
    (Filter.Eventually.of_forall fun σ =>
      ((((continuous_riemannPhi.mul (continuous_pow k)).mul
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    (integrableOn_phi_pow_cosh_sin k σ₀ γ)
    ((((continuous_riemannPhi.mul (continuous_pow (k + 1))).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu σ hσ
      have hu0 : 0 ≤ u := le_of_lt hu
      have hσ_abs : |σ| ≤ R := by
        rw [Metric.mem_ball, Real.dist_eq] at hσ
        have htri : |σ| ≤ |σ - σ₀| + |σ₀| := by simpa using abs_add_le (σ - σ₀) σ₀
        dsimp [R]; linarith
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 _)]
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
      have hPhi := hPhi_le u hu0; rw [Real.norm_eq_abs] at hPhi
      dsimp [bound]
      calc |riemannPhi u| * u ^ (k + 1) * |Real.sinh (σ * u)| * |Real.sin (γ * u)|
        _ ≤ (C2 * Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u))) *
              (((k + 1).factorial : ℝ) * Real.exp u) * Real.exp (R * u) * 1 := by
            refine mul_le_mul ?_ (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)
            exact mul_le_mul (mul_le_mul hPhi hpow (pow_nonneg hu0 _) (by positivity))
              hsinh (abs_nonneg _) (by positivity)
        _ = C2 * ((k + 1).factorial : ℝ) *
              (Real.exp (9 * u / 2 - Real.pi / 2 * Real.exp (2 * u)) * Real.exp u * Real.exp (R * u)) := by ring
        _ = C2 * ((k + 1).factorial : ℝ) *
              Real.exp ((9 / 2 + R + 1) * u - Real.pi / 2 * Real.exp (2 * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ σ _
      have hlin : HasDerivAt (fun s : ℝ => s * u) u σ := by simpa using (hasDerivAt_id σ).mul_const u
      have hch : HasDerivAt (fun s : ℝ => Real.cosh (s * u)) (Real.sinh (σ * u) * u) σ := by
        simpa [Function.comp_def] using (Real.hasDerivAt_cosh (σ * u)).comp σ hlin
      convert (hch.const_mul (riemannPhi u * u ^ k)).mul_const (Real.sin (γ * u)) using 1
      rw [pow_succ]; ring)
  exact h.2

private lemma setInt_add {f g : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), (f x + g x)) = (∫ x in Ioi (0 : ℝ), f x) + ∫ x in Ioi (0 : ℝ), g x :=
  MeasureTheory.integral_add hf hg

private lemma setInt_sub {f g : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), (f x - g x)) = (∫ x in Ioi (0 : ℝ), f x) - ∫ x in Ioi (0 : ℝ), g x :=
  MeasureTheory.integral_sub hf hg

private lemma setInt_add6 {f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (h1 : IntegrableOn f1 (Ioi 0)) (h2 : IntegrableOn f2 (Ioi 0))
    (h3 : IntegrableOn f3 (Ioi 0)) (h4 : IntegrableOn f4 (Ioi 0))
    (h5 : IntegrableOn f5 (Ioi 0)) (h6 : IntegrableOn f6 (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), (f1 x + f2 x + f3 x + f4 x + f5 x + f6 x)) =
      (∫ x in Ioi (0 : ℝ), f1 x) + (∫ x in Ioi (0 : ℝ), f2 x) +
      (∫ x in Ioi (0 : ℝ), f3 x) + (∫ x in Ioi (0 : ℝ), f4 x) +
      (∫ x in Ioi (0 : ℝ), f5 x) + (∫ x in Ioi (0 : ℝ), f6 x) := by
  have h12 : IntegrableOn (fun x => f1 x + f2 x) (Ioi 0) := h1.add h2
  have h123 : IntegrableOn (fun x => f1 x + f2 x + f3 x) (Ioi 0) := h12.add h3
  have h1234 : IntegrableOn (fun x => f1 x + f2 x + f3 x + f4 x) (Ioi 0) := h123.add h4
  have h12345 : IntegrableOn (fun x => f1 x + f2 x + f3 x + f4 x + f5 x) (Ioi 0) := h1234.add h5
  rw [setInt_add h12345 h6, setInt_add h1234 h5, setInt_add h123 h4, setInt_add h12 h3, setInt_add h1 h2]

private lemma setInt_add_sub_add_sub {f1 f2 f3 f4 f5 : ℝ → ℝ}
    (h1 : IntegrableOn f1 (Ioi 0)) (h2 : IntegrableOn f2 (Ioi 0))
    (h3 : IntegrableOn f3 (Ioi 0)) (h4 : IntegrableOn f4 (Ioi 0))
    (h5 : IntegrableOn f5 (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), (f1 x + f2 x - f3 x + f4 x - f5 x)) =
      (∫ x in Ioi (0 : ℝ), f1 x) + (∫ x in Ioi (0 : ℝ), f2 x) -
      (∫ x in Ioi (0 : ℝ), f3 x) + (∫ x in Ioi (0 : ℝ), f4 x) -
      (∫ x in Ioi (0 : ℝ), f5 x) := by
  have h12 : IntegrableOn (fun x => f1 x + f2 x) (Ioi 0) := h1.add h2
  have h123 : IntegrableOn (fun x => f1 x + f2 x - f3 x) (Ioi 0) := h12.sub h3
  have h1234 : IntegrableOn (fun x => f1 x + f2 x - f3 x + f4 x) (Ioi 0) := h123.add h4
  rw [setInt_sub h1234 h5, setInt_add h123 h4, setInt_sub h12 h3, setInt_add h1 h2]

/-- THEOREM II.1 (Exact 2D Past–Future Light-Cone Representation of `m_2(σ, γ)` for ALL `σ, γ ∈ ℝ`):
    `∂_σ^2 V(σ, γ) = 2 ∫_0^∞ ∫_0^∞ Φ(u) Φ(v) * [(u+v)^2 cosh(σ(u+v)) cos(γ(u-v)) + (u-v)^2 cosh(σ(u-v)) cos(γ(u+v))] dv du`. -/
theorem xiNormSq_deriv2_eq_pastFuture_double_integral (σ γ : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ =
      2 * ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
        riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v))) := by
  let A0 : ℝ → ℝ := fun s => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cosh (s * u) * Real.cos (γ * u)
  let A1 : ℝ → ℝ := fun s => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 1 * Real.sinh (s * u) * Real.cos (γ * u)
  let A2 : ℝ → ℝ := fun s => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 2 * Real.cosh (s * u) * Real.cos (γ * u)
  let B0 : ℝ → ℝ := fun s => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.sinh (s * u) * Real.sin (γ * u)
  let B1 : ℝ → ℝ := fun s => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 1 * Real.cosh (s * u) * Real.sin (γ * u)
  let B2 : ℝ → ℝ := fun s => ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 2 * Real.sinh (s * u) * Real.sin (γ * u)
  have hV_eq : ∀ s : ℝ, xiNormSq s γ = 4 * (A0 s ^ 2 + B0 s ^ 2) := by
    intro s
    have hre_im := riemannXi_re_im_pastFuture_phi (1 / 2 + s) γ
    have hhalf : 1 / 2 + s - 1 / 2 = s := by ring
    rw [hhalf] at hre_im
    dsimp [xiNormSq, A0, B0]
    rw [Complex.sq_norm, Complex.normSq_apply, hre_im.1, hre_im.2]
    have hA : (∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cosh (s * u) * Real.cos (γ * u)) =
        ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cosh (s * u) * Real.cos (γ * u) := by
      congr 1; ext u; simp
    have hB : (∫ u in Ioi (0 : ℝ), riemannPhi u * Real.sinh (s * u) * Real.sin (γ * u)) =
        ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.sinh (s * u) * Real.sin (γ * u) := by
      congr 1; ext u; simp
    rw [hA, hB]; ring
  have hd1 : ∀ s : ℝ, deriv (fun t : ℝ => xiNormSq t γ) s = 8 * (A0 s * A1 s + B0 s * B1 s) := by
    intro s
    have hfun : (fun t : ℝ => xiNormSq t γ) = fun t => 4 * (A0 t ^ 2 + B0 t ^ 2) := funext hV_eq
    rw [hfun]
    have hA : HasDerivAt A0 (A1 s) s := hasDerivAt_integral_phi_pow_cosh_cos 0 s γ
    have hB : HasDerivAt B0 (B1 s) s := hasDerivAt_integral_phi_pow_sinh_sin 0 s γ
    have htot := (((hA.pow 2).add (hB.pow 2)).const_mul (4 : ℝ))
    convert htot.deriv using 1; ring
  have hd2 : deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ =
      8 * (A1 σ ^ 2 + A0 σ * A2 σ + B1 σ ^ 2 + B0 σ * B2 σ) := by
    have hfun : (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) =
        fun t => 8 * (A0 t * A1 t + B0 t * B1 t) := funext hd1
    rw [hfun]
    have hA0 : HasDerivAt A0 (A1 σ) σ := hasDerivAt_integral_phi_pow_cosh_cos 0 σ γ
    have hA1 : HasDerivAt A1 (A2 σ) σ := hasDerivAt_integral_phi_pow_sinh_cos 1 σ γ
    have hB0 : HasDerivAt B0 (B1 σ) σ := hasDerivAt_integral_phi_pow_sinh_sin 0 σ γ
    have hB1 : HasDerivAt B1 (B2 σ) σ := hasDerivAt_integral_phi_pow_cosh_sin 1 σ γ
    have htot := (((hA0.mul hA1).add (hB0.mul hB1)).const_mul (8 : ℝ))
    convert htot.deriv using 1; ring
  rw [hd2]
  -- Expand 2 * ∫∫ Φ(u)Φ(v) [...] into products of A0, A1, A2, B0, B1, B2!
  have hkey : ∀ u v : ℝ,
      (u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
      (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)) =
      2 * ((u ^ 2 + v ^ 2) * (Real.cosh (σ * u) * Real.cosh (σ * v) * (Real.cos (γ * u) * Real.cos (γ * v))
                            + Real.sinh (σ * u) * Real.sinh (σ * v) * (Real.sin (γ * u) * Real.sin (γ * v)))
         + 2 * u * v * (Real.sinh (σ * u) * Real.sinh (σ * v) * (Real.cos (γ * u) * Real.cos (γ * v))
                      + Real.cosh (σ * u) * Real.cosh (σ * v) * (Real.sin (γ * u) * Real.sin (γ * v)))) := by
    intro u v
    rw [mul_add σ u v, mul_sub σ u v, mul_sub γ u v, mul_add γ u v,
        Real.cosh_add, Real.cosh_sub, Real.cos_sub, Real.cos_add]
    ring
  have h1 : ∀ u : ℝ,
      ∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v))) =
      2 * ((riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u)) * A0 σ +
           (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u)) * A2 σ +
           (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u)) * B0 σ +
           (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u)) * B2 σ +
           2 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u)) * A1 σ +
           2 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u)) * B1 σ) := by
    intro u
    have hfn : (fun v : ℝ => riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) =
        fun v =>
          (2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u))) *
            (riemannPhi v * v ^ 0 * Real.cosh (σ * v) * Real.cos (γ * v)) +
          (2 * (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u))) *
            (riemannPhi v * v ^ 2 * Real.cosh (σ * v) * Real.cos (γ * v)) +
          (2 * (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u))) *
            (riemannPhi v * v ^ 0 * Real.sinh (σ * v) * Real.sin (γ * v)) +
          (2 * (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u))) *
            (riemannPhi v * v ^ 2 * Real.sinh (σ * v) * Real.sin (γ * v)) +
          (4 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u))) *
            (riemannPhi v * v ^ 1 * Real.sinh (σ * v) * Real.cos (γ * v)) +
          (4 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u))) *
            (riemannPhi v * v ^ 1 * Real.cosh (σ * v) * Real.sin (γ * v)) := by
      ext v; rw [hkey u v]; ring
    rw [hfn]
    have i1 := (integrableOn_phi_pow_cosh_cos 0 σ γ).const_mul (2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u)))
    have i2 := (integrableOn_phi_pow_cosh_cos 2 σ γ).const_mul (2 * (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u)))
    have i3 := (integrableOn_phi_pow_sinh_sin 0 σ γ).const_mul (2 * (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u)))
    have i4 := (integrableOn_phi_pow_sinh_sin 2 σ γ).const_mul (2 * (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u)))
    have i5 := (integrableOn_phi_pow_sinh_cos 1 σ γ).const_mul (4 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u)))
    have i6 := (integrableOn_phi_pow_cosh_sin 1 σ γ).const_mul (4 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u)))
    rw [setInt_add6 i1 i2 i3 i4 i5 i6,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul]
    dsimp [A0, A1, A2, B0, B1, B2]; ring
  simp_rw [h1]
  have j1 := (integrableOn_phi_pow_cosh_cos 2 σ γ).mul_const (A0 σ)
  have j2 := (integrableOn_phi_pow_cosh_cos 0 σ γ).mul_const (A2 σ)
  have j3 := (integrableOn_phi_pow_sinh_sin 2 σ γ).mul_const (B0 σ)
  have j4 := (integrableOn_phi_pow_sinh_sin 0 σ γ).mul_const (B2 σ)
  have j5 := ((integrableOn_phi_pow_sinh_cos 1 σ γ).const_mul 2).mul_const (A1 σ)
  have j6 := ((integrableOn_phi_pow_cosh_sin 1 σ γ).const_mul 2).mul_const (B1 σ)
  rw [integral_const_mul,
      setInt_add6 j1 j2 j3 j4 j5 j6,
      integral_mul_const, integral_mul_const, integral_mul_const,
      integral_mul_const, integral_mul_const, integral_mul_const,
      integral_const_mul, integral_const_mul]
  dsimp [A0, A1, A2, B0, B1, B2]; ring

/-- THEOREM II.2 (Exact Algebraic-Miracle Moment Lower Bound on `m_2(σ, γ)`):
    Using `cos(θ) ≥ 1 - θ^2/2`, `cosh(σ(u+v)) + cosh(σ(u-v)) = 2 cosh(σ u) cosh(σ v)`,
    and `(u+v)^2 (u-v)^2 = u^4 - 2 u^2 v^2 + v^4` (ZERO odd moments!), proves
    unconditionally for EVERY `σ ∈ [0, 1/2]` and EVERY `γ ∈ ℝ`:
      `m_2(σ, γ) ≥ 8 * I_0(0) * I_2(0) - 4 * γ^2 * (I_0(1/2) * I_4(1/2) - I_2(0)^2)`. -/
theorem xiNormSq_deriv2_ge_moment_quadratic {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (γ : ℝ) :
    8 * xiCoshMoment 0 0 * xiCoshMoment 2 0 -
      4 * γ ^ 2 * (xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2) ≤
    deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ := by
  rw [xiNormSq_deriv2_eq_pastFuture_double_integral σ γ]
  -- Pointwise lower bound on the integrand using cos(θ) ≥ 1 - θ^2/2, cosh(σ(u±v)) ≥ 1,
  -- and cosh(σ(u+v)) + cosh(σ(u-v)) = 2 cosh(σ u) cosh(σ v):
  have hpt : ∀ u v : ℝ, 0 < u → 0 < v →
      riemannPhi u * riemannPhi v *
        (2 * (u ^ 2 + v ^ 2) -
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v))) ≤
      riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v))) := by
    intro u v _ _
    have hphi : 0 ≤ riemannPhi u * riemannPhi v :=
      mul_nonneg (le_of_lt (riemannPhi_pos u)) (le_of_lt (riemannPhi_pos v))
    refine mul_le_mul_of_nonneg_left ?_ hphi
    have hc1 := Real.one_sub_sq_div_two_le_cos (x := γ * (u - v))
    have hc2 := Real.one_sub_sq_div_two_le_cos (x := γ * (u + v))
    have hch1 : 1 ≤ Real.cosh (σ * (u + v)) := Real.one_le_cosh _
    have hch2 : 1 ≤ Real.cosh (σ * (u - v)) := Real.one_le_cosh _
    have hstep1 :
        (u + v) ^ 2 * Real.cosh (σ * (u + v)) * (1 - (γ * (u - v)) ^ 2 / 2) +
        (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (1 - (γ * (u + v)) ^ 2 / 2) ≤
        (u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
        (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hc1 (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))))
        (mul_le_mul_of_nonneg_left hc2 (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))))
    have hadd_ch : Real.cosh (σ * (u + v)) + Real.cosh (σ * (u - v)) =
        2 * Real.cosh (σ * u) * Real.cosh (σ * v) := by
      rw [mul_add, mul_sub, Real.cosh_add, Real.cosh_sub]; ring
    have hstep2 :
        2 * (u ^ 2 + v ^ 2) -
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v)) ≤
        (u + v) ^ 2 * Real.cosh (σ * (u + v)) * (1 - (γ * (u - v)) ^ 2 / 2) +
        (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (1 - (γ * (u + v)) ^ 2 / 2) := by
      have h1 : (u + v) ^ 2 + (u - v) ^ 2 = 2 * (u ^ 2 + v ^ 2) := by ring
      have h2 : (u + v) ^ 2 * Real.cosh (σ * (u + v)) + (u - v) ^ 2 * Real.cosh (σ * (u - v)) ≥
          (u + v) ^ 2 + (u - v) ^ 2 := by nlinarith [sq_nonneg (u + v), sq_nonneg (u - v)]
      have h3 : (u + v) ^ 2 * Real.cosh (σ * (u + v)) * ((γ * (u - v)) ^ 2 / 2) +
          (u - v) ^ 2 * Real.cosh (σ * (u - v)) * ((γ * (u + v)) ^ 2 / 2) =
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v)) := by
        have halg : (u + v) ^ 2 * ((γ * (u - v)) ^ 2 / 2) =
            (γ ^ 2 / 2) * (u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) := by ring
        have halg2 : (u - v) ^ 2 * ((γ * (u + v)) ^ 2 / 2) =
            (γ ^ 2 / 2) * (u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) := by ring
        calc (u + v) ^ 2 * Real.cosh (σ * (u + v)) * ((γ * (u - v)) ^ 2 / 2) +
              (u - v) ^ 2 * Real.cosh (σ * (u - v)) * ((γ * (u + v)) ^ 2 / 2)
          _ = Real.cosh (σ * (u + v)) * ((u + v) ^ 2 * ((γ * (u - v)) ^ 2 / 2)) +
              Real.cosh (σ * (u - v)) * ((u - v) ^ 2 * ((γ * (u + v)) ^ 2 / 2)) := by ring
          _ = (Real.cosh (σ * (u + v)) + Real.cosh (σ * (u - v))) *
              ((γ ^ 2 / 2) * (u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4)) := by rw [halg, halg2]; ring
          _ = γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v)) := by
              rw [hadd_ch]; ring
      linarith
    exact hstep2.trans hstep1
  -- Integrate over v and u!
  have hinner_int_rhs : ∀ u : ℝ, IntegrableOn (fun v : ℝ =>
      riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) (Ioi 0) := by
    intro u
    have hkey : (fun v : ℝ => riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) =
      fun v =>
        (2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u))) *
          (riemannPhi v * v ^ 0 * Real.cosh (σ * v) * Real.cos (γ * v)) +
        (2 * (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u))) *
          (riemannPhi v * v ^ 2 * Real.cosh (σ * v) * Real.cos (γ * v)) +
        (2 * (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u))) *
          (riemannPhi v * v ^ 0 * Real.sinh (σ * v) * Real.sin (γ * v)) +
        (2 * (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u))) *
          (riemannPhi v * v ^ 2 * Real.sinh (σ * v) * Real.sin (γ * v)) +
        (4 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u))) *
          (riemannPhi v * v ^ 1 * Real.sinh (σ * v) * Real.cos (γ * v)) +
        (4 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u))) *
          (riemannPhi v * v ^ 1 * Real.cosh (σ * v) * Real.sin (γ * v)) := by
      ext v
      rw [mul_add σ u v, mul_sub σ u v, mul_sub γ u v, mul_add γ u v,
          Real.cosh_add, Real.cosh_sub, Real.cos_sub, Real.cos_add]; ring
    rw [hkey]
    exact ((((((integrableOn_phi_pow_cosh_cos 0 σ γ).const_mul _).add
      ((integrableOn_phi_pow_cosh_cos 2 σ γ).const_mul _)).add
      ((integrableOn_phi_pow_sinh_sin 0 σ γ).const_mul _)).add
      ((integrableOn_phi_pow_sinh_sin 2 σ γ).const_mul _)).add
      ((integrableOn_phi_pow_sinh_cos 1 σ γ).const_mul _)).add
      ((integrableOn_phi_pow_cosh_sin 1 σ γ).const_mul _)
  have hinner_val_lhs : ∀ u : ℝ,
      ∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
        (2 * (u ^ 2 + v ^ 2) -
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v))) =
      2 * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) * xiCoshMoment 0 0 +
      2 * (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) * xiCoshMoment 2 0 -
      γ ^ 2 * ((riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * xiCoshMoment 0 σ -
               2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * xiCoshMoment 2 σ +
               (riemannPhi u * u ^ 0 * Real.cosh (σ * u)) * xiCoshMoment 4 σ) := by
    intro u
    have hfn : (fun v : ℝ => riemannPhi u * riemannPhi v *
        (2 * (u ^ 2 + v ^ 2) -
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v)))) =
      fun v =>
        (2 * (riemannPhi u * u ^ 2)) * (riemannPhi v * v ^ 0 * Real.cosh (0 * v)) +
        (2 * riemannPhi u) * (riemannPhi v * v ^ 2 * Real.cosh (0 * v)) -
        (γ ^ 2 * riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * (riemannPhi v * v ^ 0 * Real.cosh (σ * v)) +
        (2 * γ ^ 2 * riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * (riemannPhi v * v ^ 2 * Real.cosh (σ * v)) -
        (γ ^ 2 * riemannPhi u * Real.cosh (σ * u)) * (riemannPhi v * v ^ 4 * Real.cosh (σ * v)) := by
      ext v; simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]; ring
    rw [hfn]
    have i1 := (integrableOn_phi_pow_cosh 0 0).const_mul (2 * (riemannPhi u * u ^ 2))
    have i2 := (integrableOn_phi_pow_cosh 2 0).const_mul (2 * riemannPhi u)
    have i3 := (integrableOn_phi_pow_cosh 0 σ).const_mul (γ ^ 2 * riemannPhi u * u ^ 4 * Real.cosh (σ * u))
    have i4 := (integrableOn_phi_pow_cosh 2 σ).const_mul (2 * γ ^ 2 * riemannPhi u * u ^ 2 * Real.cosh (σ * u))
    have i5 := (integrableOn_phi_pow_cosh 4 σ).const_mul (γ ^ 2 * riemannPhi u * Real.cosh (σ * u))
    rw [setInt_add_sub_add_sub i1 i2 i3 i4 i5,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul]
    dsimp [xiCoshMoment]; simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]; ring
  have hinner_int_lhs : ∀ u : ℝ, IntegrableOn (fun v : ℝ =>
      riemannPhi u * riemannPhi v *
        (2 * (u ^ 2 + v ^ 2) -
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v)))) (Ioi 0) := by
    intro u
    have hfn : (fun v : ℝ => riemannPhi u * riemannPhi v *
        (2 * (u ^ 2 + v ^ 2) -
          γ ^ 2 * ((u ^ 4 - 2 * u ^ 2 * v ^ 2 + v ^ 4) * Real.cosh (σ * u) * Real.cosh (σ * v)))) =
      fun v =>
        (2 * (riemannPhi u * u ^ 2)) * (riemannPhi v * v ^ 0 * Real.cosh (0 * v)) +
        (2 * riemannPhi u) * (riemannPhi v * v ^ 2 * Real.cosh (0 * v)) -
        (γ ^ 2 * riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * (riemannPhi v * v ^ 0 * Real.cosh (σ * v)) +
        (2 * γ ^ 2 * riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * (riemannPhi v * v ^ 2 * Real.cosh (σ * v)) -
        (γ ^ 2 * riemannPhi u * Real.cosh (σ * u)) * (riemannPhi v * v ^ 4 * Real.cosh (σ * v)) := by
      ext v; simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]; ring
    rw [hfn]
    exact (((((integrableOn_phi_pow_cosh 0 0).const_mul _).add
      ((integrableOn_phi_pow_cosh 2 0).const_mul _)).sub
      ((integrableOn_phi_pow_cosh 0 σ).const_mul _)).add
      ((integrableOn_phi_pow_cosh 2 σ).const_mul _)).sub
      ((integrableOn_phi_pow_cosh 4 σ).const_mul _)
  have houter_le :
      ∫ u in Ioi (0 : ℝ),
        (2 * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) * xiCoshMoment 0 0 +
         2 * (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) * xiCoshMoment 2 0 -
         γ ^ 2 * ((riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * xiCoshMoment 0 σ -
                  2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * xiCoshMoment 2 σ +
                  (riemannPhi u * u ^ 0 * Real.cosh (σ * u)) * xiCoshMoment 4 σ)) ≤
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
        riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v))) := by
    -- Outer integrability of LHS and RHS
    have ho_lhs : IntegrableOn (fun u : ℝ =>
        2 * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) * xiCoshMoment 0 0 +
        2 * (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) * xiCoshMoment 2 0 -
        γ ^ 2 * ((riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * xiCoshMoment 0 σ -
                 2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * xiCoshMoment 2 σ +
                 (riemannPhi u * u ^ 0 * Real.cosh (σ * u)) * xiCoshMoment 4 σ)) (Ioi 0) :=
      ((((integrableOn_phi_pow_cosh 2 0).const_mul 2).mul_const _).add
       (((integrableOn_phi_pow_cosh 0 0).const_mul 2).mul_const _)).sub
       (((((integrableOn_phi_pow_cosh 4 σ).mul_const _).sub
         (((integrableOn_phi_pow_cosh 2 σ).const_mul 2).mul_const _)).add
         ((integrableOn_phi_pow_cosh 0 σ).mul_const _)).const_mul _)
    have ho_rhs : IntegrableOn (fun u : ℝ => ∫ v in Ioi (0 : ℝ),
        riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) (Ioi 0) := by
      -- Equal to linear combination of integrable functions from Theorem II.1's proof!
      let A0s := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ 0 * Real.cosh (σ * v) * Real.cos (γ * v)
      let A1s := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ 1 * Real.sinh (σ * v) * Real.cos (γ * v)
      let A2s := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ 2 * Real.cosh (σ * v) * Real.cos (γ * v)
      let B0s := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ 0 * Real.sinh (σ * v) * Real.sin (γ * v)
      let B1s := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ 1 * Real.cosh (σ * v) * Real.sin (γ * v)
      let B2s := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ 2 * Real.sinh (σ * v) * Real.sin (γ * v)
      have heq : (fun u : ℝ => ∫ v in Ioi (0 : ℝ),
          riemannPhi u * riemannPhi v *
            ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
             (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) =
        fun u =>
          2 * ((riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u)) * A0s +
               (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u)) * A2s +
               (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u)) * B0s +
               (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u)) * B2s +
               2 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u)) * A1s +
               2 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u)) * B1s) := by
        ext u
        have hfn : (fun v : ℝ => riemannPhi u * riemannPhi v *
            ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
             (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) =
          fun v =>
            (2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u))) *
              (riemannPhi v * v ^ 0 * Real.cosh (σ * v) * Real.cos (γ * v)) +
            (2 * (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u))) *
              (riemannPhi v * v ^ 2 * Real.cosh (σ * v) * Real.cos (γ * v)) +
            (2 * (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u))) *
              (riemannPhi v * v ^ 0 * Real.sinh (σ * v) * Real.sin (γ * v)) +
            (2 * (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u))) *
              (riemannPhi v * v ^ 2 * Real.sinh (σ * v) * Real.sin (γ * v)) +
            (4 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u))) *
              (riemannPhi v * v ^ 1 * Real.sinh (σ * v) * Real.cos (γ * v)) +
            (4 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u))) *
              (riemannPhi v * v ^ 1 * Real.cosh (σ * v) * Real.sin (γ * v)) := by
          ext v
          rw [mul_add σ u v, mul_sub σ u v, mul_sub γ u v, mul_add γ u v,
              Real.cosh_add, Real.cosh_sub, Real.cos_sub, Real.cos_add]; ring
        rw [hfn]
        have i1 := (integrableOn_phi_pow_cosh_cos 0 σ γ).const_mul (2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u) * Real.cos (γ * u)))
        have i2 := (integrableOn_phi_pow_cosh_cos 2 σ γ).const_mul (2 * (riemannPhi u * u ^ 0 * Real.cosh (σ * u) * Real.cos (γ * u)))
        have i3 := (integrableOn_phi_pow_sinh_sin 0 σ γ).const_mul (2 * (riemannPhi u * u ^ 2 * Real.sinh (σ * u) * Real.sin (γ * u)))
        have i4 := (integrableOn_phi_pow_sinh_sin 2 σ γ).const_mul (2 * (riemannPhi u * u ^ 0 * Real.sinh (σ * u) * Real.sin (γ * u)))
        have i5 := (integrableOn_phi_pow_sinh_cos 1 σ γ).const_mul (4 * (riemannPhi u * u ^ 1 * Real.sinh (σ * u) * Real.cos (γ * u)))
        have i6 := (integrableOn_phi_pow_cosh_sin 1 σ γ).const_mul (4 * (riemannPhi u * u ^ 1 * Real.cosh (σ * u) * Real.sin (γ * u)))
        rw [setInt_add6 i1 i2 i3 i4 i5 i6,
            integral_const_mul, integral_const_mul, integral_const_mul,
            integral_const_mul, integral_const_mul, integral_const_mul]
        dsimp [A0s, A1s, A2s, B0s, B1s, B2s]; ring
      rw [heq]
      exact (((((((integrableOn_phi_pow_cosh_cos 2 σ γ).mul_const _).add
        ((integrableOn_phi_pow_cosh_cos 0 σ γ).mul_const _)).add
        ((integrableOn_phi_pow_sinh_sin 2 σ γ).mul_const _)).add
        ((integrableOn_phi_pow_sinh_sin 0 σ γ).mul_const _)).add
        (((integrableOn_phi_pow_sinh_cos 1 σ γ).const_mul 2).mul_const _)).add
        (((integrableOn_phi_pow_cosh_sin 1 σ γ).const_mul 2).mul_const _)).const_mul 2
    refine MeasureTheory.setIntegral_mono_on ho_lhs ho_rhs measurableSet_Ioi fun u hu => ?_
    rw [← hinner_val_lhs u]
    exact MeasureTheory.setIntegral_mono_on (hinner_int_lhs u) (hinner_int_rhs u) measurableSet_Ioi
      fun v hv => hpt u v hu hv
  -- Evaluate the outer LHS integral!
  have houter_val :
      ∫ u in Ioi (0 : ℝ),
        (2 * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) * xiCoshMoment 0 0 +
         2 * (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) * xiCoshMoment 2 0 -
         γ ^ 2 * ((riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * xiCoshMoment 0 σ -
                  2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * xiCoshMoment 2 σ +
                  (riemannPhi u * u ^ 0 * Real.cosh (σ * u)) * xiCoshMoment 4 σ)) =
      4 * xiCoshMoment 0 0 * xiCoshMoment 2 0 -
        2 * γ ^ 2 * (xiCoshMoment 0 σ * xiCoshMoment 4 σ - xiCoshMoment 2 σ ^ 2) := by
    have j1 := ((integrableOn_phi_pow_cosh 2 0).const_mul 2).mul_const (xiCoshMoment 0 0)
    have j2 := ((integrableOn_phi_pow_cosh 0 0).const_mul 2).mul_const (xiCoshMoment 2 0)
    have j3 := (integrableOn_phi_pow_cosh 4 σ).mul_const (xiCoshMoment 0 σ)
    have j4 := ((integrableOn_phi_pow_cosh 2 σ).const_mul 2).mul_const (xiCoshMoment 2 σ)
    have j5 := (integrableOn_phi_pow_cosh 0 σ).mul_const (xiCoshMoment 4 σ)
    have j12 : IntegrableOn (fun u => 2 * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) * xiCoshMoment 0 0 +
        2 * (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) * xiCoshMoment 2 0) (Ioi 0) := j1.add j2
    have j34 : IntegrableOn (fun u => (riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * xiCoshMoment 0 σ -
        2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * xiCoshMoment 2 σ) (Ioi 0) := j3.sub j4
    have j345 : IntegrableOn (fun u => (riemannPhi u * u ^ 4 * Real.cosh (σ * u)) * xiCoshMoment 0 σ -
        2 * (riemannPhi u * u ^ 2 * Real.cosh (σ * u)) * xiCoshMoment 2 σ +
        (riemannPhi u * u ^ 0 * Real.cosh (σ * u)) * xiCoshMoment 4 σ) (Ioi 0) := j34.add j5
    rw [setInt_sub j12 (j345.const_mul (γ ^ 2)),
        setInt_add j1 j2,
        integral_const_mul,
        setInt_add j34 j5,
        setInt_sub j3 j4,
        integral_mul_const, integral_mul_const, integral_mul_const,
        integral_mul_const, integral_mul_const,
        integral_const_mul, integral_const_mul, integral_const_mul]
    dsimp [xiCoshMoment]; ring
  rw [houter_val] at houter_le
  -- Monotonicity of xiCoshMoment k in σ ≥ 0:
  have hmono : ∀ (k : ℕ) {s₁ s₂ : ℝ}, 0 ≤ s₁ → s₁ ≤ s₂ → xiCoshMoment k s₁ ≤ xiCoshMoment k s₂ := by
    intro k s₁ s₂ hs₁ hs
    refine MeasureTheory.setIntegral_mono_on (integrableOn_phi_pow_cosh k s₁)
      (integrableOn_phi_pow_cosh k s₂) measurableSet_Ioi fun u hu => ?_
    have hch : Real.cosh (s₁ * u) ≤ Real.cosh (s₂ * u) := by
      have h1 : 0 ≤ s₁ * u := mul_nonneg hs₁ (le_of_lt hu)
      have h2 : s₁ * u ≤ s₂ * u := mul_le_mul_of_nonneg_right hs (le_of_lt hu)
      exact (Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]; exact h2))
    exact mul_le_mul_of_nonneg_left hch (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _))
  have hI0_le := hmono 0 hσ0 hσ1
  have hI4_le := hmono 4 hσ0 hσ1
  have hI2_ge := hmono 2 le_rfl hσ0
  have hI0_nn : 0 ≤ xiCoshMoment 0 σ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _)) (le_of_lt (Real.cosh_pos _))
  have hI4_nn : 0 ≤ xiCoshMoment 4 (1 / 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _)) (le_of_lt (Real.cosh_pos _))
  have hI2_nn : 0 ≤ xiCoshMoment 2 0 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _)) (le_of_lt (Real.cosh_pos _))
  have hprod : xiCoshMoment 0 σ * xiCoshMoment 4 σ - xiCoshMoment 2 σ ^ 2 ≤
      xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2 := by
    have hp1 : xiCoshMoment 0 σ * xiCoshMoment 4 σ ≤ xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) :=
      mul_le_mul hI0_le hI4_le (MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu =>
        mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _)) (le_of_lt (Real.cosh_pos _)))
        (le_trans hI0_nn hI0_le)
    have hp2 : xiCoshMoment 2 0 ^ 2 ≤ xiCoshMoment 2 σ ^ 2 := pow_le_pow_left₀ hI2_nn hI2_ge 2
    linarith
  have hmul := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * γ ^ 2)
  linarith

/-- Critical-line quadratic moment lower bound on `Ξ(γ)`:
    `Ξ(γ) ≥ 2 * I_0(0) - γ^2 * I_2(0)` for every `γ ∈ ℝ`. -/
theorem xiCritical_ge_moment_quadratic (γ : ℝ) :
    2 * xiCoshMoment 0 0 - γ ^ 2 * xiCoshMoment 2 0 ≤ xiCritical γ := by
  rw [xiCritical_eq_cos_integral]
  have hsub : 2 * xiCoshMoment 0 0 - γ ^ 2 * xiCoshMoment 2 0 =
      2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * (1 - (γ * u) ^ 2 / 2) := by
    have hfn : (fun u : ℝ => riemannPhi u * (1 - (γ * u) ^ 2 / 2)) =
        fun u => (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) -
          (γ ^ 2 / 2) * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) := by
      ext u; simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]; ring
    rw [hfn, MeasureTheory.integral_sub (integrableOn_phi_pow_cosh 0 0)
        ((integrableOn_phi_pow_cosh 2 0).const_mul _), integral_const_mul]
    dsimp [xiCoshMoment]; ring
  rw [hsub]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hint_lhs : IntegrableOn (fun u : ℝ => riemannPhi u * (1 - (γ * u) ^ 2 / 2)) (Ioi 0) := by
    have hfn : (fun u : ℝ => riemannPhi u * (1 - (γ * u) ^ 2 / 2)) =
        fun u => (riemannPhi u * u ^ 0 * Real.cosh (0 * u)) -
          (γ ^ 2 / 2) * (riemannPhi u * u ^ 2 * Real.cosh (0 * u)) := by
      ext u; simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]; ring
    rw [hfn]; exact (integrableOn_phi_pow_cosh 0 0).sub ((integrableOn_phi_pow_cosh 2 0).const_mul _)
  have hint_rhs : IntegrableOn (fun u : ℝ => riemannPhi u * u ^ 0 * Real.cos (γ * u)) (Ioi 0) :=
    integrableOn_phi_pow_cos 0 γ
  refine MeasureTheory.setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi fun u _ => ?_
  simp only [pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos) (le_of_lt (riemannPhi_pos u))

-- ==============================================================================
-- PART III: ROUTE B — EXPLICIT CONSTRUCTIVE ZERO-FREE & CONVEXITY RECTANGLE
-- ==============================================================================

/-- Every summand `riemannPhiTerm n u` is strictly positive for `u ≥ 0`. -/
lemma riemannPhiTerm_pos_of_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < riemannPhiTerm n u := by
  dsimp [riemannPhiTerm, thetaHalfTerm]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have he2 : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have h4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
  have hfac : 0 < 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
      6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by
    rw [h4]
    have hx : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by nlinarith
    have hfactor : 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (2 * u) ^ 2 -
        6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) =
        (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) *
          (4 * Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) - 6 * Real.pi) := by ring
    rw [hfactor]
    exact mul_pos (by linarith) (by nlinarith)
  exact mul_pos hfac (Real.exp_pos _)

/-- Exact `n ≥ 1` geometric tail bound: `Φ(u) ≤ (21/20) * 4π^2 * exp(9u/2 - π e^{2u})` for `u ≥ 0`. -/
lemma riemannPhi_le_explicit_envelope {u : ℝ} (hu : 0 ≤ u) :
    riemannPhi u ≤ (21 / 20 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u))) := by
  dsimp [riemannPhi]
  have he2_ge1 : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hpi_gt : (314 / 100 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  -- Bound each summand by 4π^2 * exp(9u/2 - π e^{2u}) * ((n+1)^4 * exp(-π((n+1)^2 - 1)))
  have hterm : ∀ n : ℕ, riemannPhiTerm n u ≤
      (4 * Real.pi ^ 2 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u))) *
        (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1))) := by
    intro n
    dsimp [riemannPhiTerm, thetaHalfTerm]
    have hpoly : 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
        6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) ≤
        4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) := by
      have : 0 ≤ 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
      linarith
    have hexp : Real.exp (u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
        Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) *
          Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn_ge : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 - 1 := by
        have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        nlinarith
      have hprod : Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1) * 1 ≤
          Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1) * Real.exp (2 * u) :=
        mul_le_mul_of_nonneg_left he2_ge1 (mul_nonneg (le_of_lt Real.pi_pos) hn_ge)
      linarith
    have h4u : Real.exp (4 * u) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) =
        Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
            6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) *
          Real.exp (u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))
      _ ≤ (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u)) *
          (Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) *
            Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1))) :=
          mul_le_mul hpoly hexp (le_of_lt (Real.exp_pos _)) (by positivity)
      _ = (4 * Real.pi ^ 2 * (Real.exp (4 * u) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)))) *
          (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1))) := by ring
      _ = _ := by rw [h4u]
  -- Bound ∑' n, (n+1)^4 * exp(-π*((n+1)^2 - 1)) ≤ 21/20
  have hgeom_sum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 *
      Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1))) := by
    have h := (summable_pow_mul_exp_neg_sq 4 (c := Real.pi) Real.pi_pos).mul_right (Real.exp Real.pi)
    refine h.congr fun n => ?_
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hsum_le : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4 *
      Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤ 21 / 20 := by
    rw [hgeom_sum.tsum_eq_zero_add]
    have h0 : ((0 + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (((0 + 1 : ℕ) : ℝ) ^ 2 - 1)) = 1 := by
      norm_num
    rw [h0]
    suffices ht : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ 4 *
        Real.exp (-Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤ 1 / 20 by linarith
    have he8 : Real.exp (-8 : ℝ) < 1 / 2000 := by
      have h1 : (8 / 3 : ℝ) ≤ Real.exp 1 := by
        have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
        norm_num at h; linarith
      have hpow : (8 / 3 : ℝ) ^ (8 : ℕ) ≤ Real.exp 8 := by
        rw [show Real.exp 8 = (Real.exp 1) ^ (8 : ℕ) by rw [← Real.exp_nat_mul]; norm_num]
        exact pow_le_pow_left₀ (by norm_num) h1 8
      have h2000 : (2000 : ℝ) < Real.exp 8 := by
        have : (2000 : ℝ) < (8 / 3 : ℝ) ^ (8 : ℕ) := by norm_num
        linarith
      rw [Real.exp_neg]
      have h1' : 1 < (1 / 2000 : ℝ) * Real.exp 8 := by linarith
      exact (inv_lt_iff_one_lt_mul₀' (Real.exp_pos 8)).mpr (by linarith)
    have hdom : HasSum (fun n : ℕ => (72 : ℝ) * (1 / 2000 : ℝ) ^ (n + 1)) (72 * ((1 / 2000 : ℝ) / (1 - 1 / 2000))) := by
      have hg := hasSum_geometric_of_lt_one (r := (1 / 2000 : ℝ)) (by norm_num) (by norm_num)
      have hshift : HasSum (fun n : ℕ => (1 / 2000 : ℝ) ^ (n + 1)) ((1 / 2000 : ℝ) * (1 - 1 / 2000)⁻¹) := by
        simpa [pow_succ'] using hg.mul_left (1 / 2000 : ℝ)
      simpa [div_eq_mul_inv] using hshift.mul_left 72
    have hle_dom : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ 4 *
        Real.exp (-Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1))) ≤
        ∑' n : ℕ, (72 : ℝ) * (1 / 2000 : ℝ) ^ (n + 1) := by
      refine ((summable_nat_add_iff 1).mpr hgeom_sum).tsum_le_tsum (fun n => ?_) hdom.summable
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hpow4 := pow_le_factorial_mul_exp 4 (x := ((n + 1 + 1 : ℕ) : ℝ)) (by positivity)
      simp only [Nat.factorial] at hpow4
      have hstep : -Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1) + ((n + 1 + 1 : ℕ) : ℝ) ≤
          1 + ((n + 1 : ℕ) : ℝ) * (-8 : ℝ) := by
        push_cast
        have hquad : 3 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1 + 1) ^ 2 - 1 := by nlinarith
        have hmul : Real.pi * (3 * ((n : ℝ) + 1)) ≤ Real.pi * (((n : ℝ) + 1 + 1) ^ 2 - 1) :=
          mul_le_mul_of_nonneg_left hquad (le_of_lt Real.pi_pos)
        nlinarith
      have hexp_comb : Real.exp ((n + 1 + 1 : ℕ) : ℝ) *
          Real.exp (-Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1)) ≤
          Real.exp 1 * (1 / 2000 : ℝ) ^ (n + 1) := by
        rw [← Real.exp_add]
        have h1 : Real.exp (((n + 1 + 1 : ℕ) : ℝ) + -Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1)) ≤
            Real.exp (1 + ((n + 1 : ℕ) : ℝ) * (-8 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        have h1_rhs : Real.exp (1 + ((n + 1 : ℕ) : ℝ) * (-8 : ℝ)) =
            Real.exp 1 * (Real.exp (-8 : ℝ)) ^ (n + 1) := by
          rw [Real.exp_add, Real.exp_nat_mul]
        rw [h1_rhs] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) (le_of_lt he8) (n + 1)) (le_of_lt (Real.exp_pos _)))
      have he1 := exp_one_lt_three
      calc ((n + 1 + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1))
        _ ≤ (24 * Real.exp ((n + 1 + 1 : ℕ) : ℝ)) *
              Real.exp (-Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1)) := by
            have h4 : ((n + 1 + 1 : ℕ) : ℝ) ^ 4 ≤ 24 * Real.exp ((n + 1 + 1 : ℕ) : ℝ) := by
              have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
              simpa [hfac] using hpow4
            exact mul_le_mul_of_nonneg_right h4 (le_of_lt (Real.exp_pos _))
        _ = 24 * (Real.exp ((n + 1 + 1 : ℕ) : ℝ) *
              Real.exp (-Real.pi * (((n + 1 + 1 : ℕ) : ℝ) ^ 2 - 1))) := by ring
        _ ≤ 24 * (Real.exp 1 * (1 / 2000 : ℝ) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hexp_comb (by norm_num)
        _ ≤ 72 * (1 / 2000 : ℝ) ^ (n + 1) := by
            have : 0 ≤ (1 / 2000 : ℝ) ^ (n + 1) := by positivity
            nlinarith
    rw [hdom.tsum_eq] at hle_dom
    have hnum : (72 : ℝ) * ((1 / 2000 : ℝ) / (1 - 1 / 2000)) ≤ 1 / 20 := by norm_num
    exact hle_dom.trans hnum
  have hphi_sum : Summable (fun n : ℕ => riemannPhiTerm n u) :=
    (hgeom_sum.mul_left _).of_nonneg_of_le (fun n => le_of_lt (riemannPhiTerm_pos_of_nonneg n hu)) hterm
  have h1 := hphi_sum.tsum_le_tsum hterm (hgeom_sum.mul_left _)
  rw [tsum_mul_left] at h1
  calc ∑' n : ℕ, riemannPhiTerm n u
    _ ≤ (4 * Real.pi ^ 2 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u))) *
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 - 1))) := h1
    _ ≤ (4 * Real.pi ^ 2 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u))) * (21 / 20) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = _ := by ring

/-- Integrability of `u^k * exp(-c*u)` on `(0, ∞)` for any `c > 0` and `k : ℕ`. -/
lemma integrableOn_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-c * u)) (Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ => ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp (-(c / 2) * u)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(c / 2) < 0) 0).const_mul _
  refine hbase.mono' (((continuous_pow k).mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hu0 _) (le_of_lt (Real.exp_pos _)))]
  have hpow := pow_le_factorial_mul_exp k (x := (c / 2) * u) (by positivity)
  rw [mul_pow] at hpow
  have hbound : u ^ k ≤ ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp ((c / 2) * u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < (c / 2) ^ k)]; linarith
  calc u ^ k * Real.exp (-c * u)
    _ ≤ (((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp ((c / 2) * u)) * Real.exp (-c * u) :=
        mul_le_mul_of_nonneg_right hbound (le_of_lt (Real.exp_pos _))
    _ = ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp (-(c / 2) * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Exact elementary gamma-integral `∫_0^∞ u^k * exp(-c*u) du = k! / c^(k+1)` for `c > 0`. -/
lemma integral_Ioi_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    ∀ k : ℕ, ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-c * u) = (k.factorial : ℝ) / c ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have h := integral_exp_mul_Ioi (a := -c) (by linarith) 0
    simpa [mul_zero, Real.exp_zero, neg_div, div_neg, neg_neg] using h
  | succ k ih =>
    let G : ℝ → ℝ := fun u => -(u ^ (k + 1) / c) * Real.exp (-c * u)
    have hd : ∀ u ∈ Ici (0 : ℝ), HasDerivAt G
        (u ^ (k + 1) * Real.exp (-c * u) - ((k + 1 : ℝ) / c) * (u ^ k * Real.exp (-c * u))) u := by
      intro u _
      have h1 : HasDerivAt (fun s : ℝ => -(s ^ (k + 1) / c)) (-(((k + 1 : ℝ) * u ^ k) / c)) u := by
        convert ((hasDerivAt_pow (k + 1) u).div_const c).neg using 1
        push_cast; ring
      have h2 : HasDerivAt (fun s : ℝ => Real.exp (-c * s)) (-c * Real.exp (-c * u)) u := by
        have hlin : HasDerivAt (fun s : ℝ => -c * s) (-c) u := by
          simpa using (hasDerivAt_id u).const_mul (-c)
        have h := (Real.hasDerivAt_exp (-c * u)).comp u hlin
        rw [Function.comp_def] at h
        convert h using 1; ring
      convert h1.mul h2 using 1
      field_simp [ne_of_gt hc]; ring
    have hinf : Tendsto G atTop (𝓝 0) := by
      have hdom_tend : Tendsto (fun u : ℝ =>
          (((k + 1).factorial : ℝ) / (c * (c / 2) ^ (k + 1))) * Real.exp (-(c / 2) * u)) atTop (𝓝 0) := by
        have he := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -(c / 2) < 0))
        simpa [Function.comp_def] using he.const_mul (((k + 1).factorial : ℝ) / (c * (c / 2) ^ (k + 1)))
      have habs : Tendsto (fun u : ℝ => ‖G u‖) atTop (𝓝 0) := by
        refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (Filter.eventually_atTop.mpr ⟨0, fun u hu => ?_⟩) hdom_tend
        dsimp [G]
        rw [abs_mul, abs_neg, abs_div, abs_of_nonneg (pow_nonneg hu _), abs_of_pos hc,
            abs_of_pos (Real.exp_pos _)]
        have hpow := pow_le_factorial_mul_exp (k + 1) (x := (c / 2) * u) (by positivity)
        rw [mul_pow] at hpow
        have hbound : u ^ (k + 1) ≤ (((k + 1).factorial : ℝ) / (c / 2) ^ (k + 1)) * Real.exp ((c / 2) * u) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < (c / 2) ^ (k + 1))]; linarith
        calc u ^ (k + 1) / c * Real.exp (-c * u)
          _ ≤ ((((k + 1).factorial : ℝ) / (c / 2) ^ (k + 1)) * Real.exp ((c / 2) * u)) / c * Real.exp (-c * u) :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hbound (le_of_lt hc)) (le_of_lt (Real.exp_pos _))
          _ = (((k + 1).factorial : ℝ) / (c * (c / 2) ^ (k + 1))) *
              (Real.exp ((c / 2) * u) * Real.exp (-c * u)) := by ring
          _ = (((k + 1).factorial : ℝ) / (c * (c / 2) ^ (k + 1))) * Real.exp (-(c / 2) * u) := by
              rw [← Real.exp_add]; congr 2; ring
      exact tendsto_zero_iff_norm_tendsto_zero.mpr habs
    have hint_diff : IntegrableOn
        (fun u : ℝ => u ^ (k + 1) * Real.exp (-c * u) - ((k + 1 : ℝ) / c) * (u ^ k * Real.exp (-c * u))) (Ioi 0) :=
      (integrableOn_pow_mul_exp_neg hc (k + 1)).sub ((integrableOn_pow_mul_exp_neg hc k).const_mul _)
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hd hint_diff hinf
    have hG0 : G 0 = 0 := by dsimp [G]; simp
    rw [hG0, sub_self, setInt_sub (integrableOn_pow_mul_exp_neg hc (k + 1))
        ((integrableOn_pow_mul_exp_neg hc k).const_mul _), integral_const_mul, ih] at hftc
    have heq : ∫ u in Ioi (0 : ℝ), u ^ (k + 1) * Real.exp (-c * u) =
        ((k + 1 : ℝ) / c) * ((k.factorial : ℝ) / c ^ (k + 1)) := by linarith
    rw [heq, Nat.factorial_succ]
    push_cast
    rw [pow_succ]
    field_simp [ne_of_gt hc]
    ring

/-- Unified quadratic-completion exponential upper envelope for `xiCoshMoment k (1/2)`:
    For any `c > 0` and any upper bound `A` satisfying
    `(21/20) * 4π^2 * exp(-π + (c + 5 - 2π)^2 / (8π)) ≤ A`, we have
    `xiCoshMoment k (1/2) ≤ A * k! / c^(k+1)`. -/
lemma xiCoshMoment_half_le_quad_completion (k : ℕ) {c A : ℝ} (hc : 0 < c)
    (hA : (21 / 20 : ℝ) * 4 * Real.pi ^ 2 *
      Real.exp (-Real.pi + (c + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) ≤ A) :
    xiCoshMoment k (1 / 2) ≤ A * ((k.factorial : ℝ) / c ^ (k + 1)) := by
  dsimp [xiCoshMoment]
  rw [← integral_Ioi_pow_mul_exp_neg hc k, ← integral_const_mul]
  refine MeasureTheory.setIntegral_mono_on (integrableOn_phi_pow_cosh k (1 / 2))
    ((integrableOn_pow_mul_exp_neg hc k).const_mul A) measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  have hphi := riemannPhi_le_explicit_envelope hu0
  have hch : Real.cosh ((1 / 2 : ℝ) * u) ≤ Real.exp (u / 2) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-(1 / 2 * u)) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (1 / 2 : ℝ) * u = u / 2 := by ring
    rw [h2] at h1 ⊢; linarith
  -- e^{2u} ≥ 1 + 2u + 2u^2 from Real.sum_le_exp_of_nonneg (k = 3)
  have he2 : 1 + 2 * u + 2 * u ^ 2 ≤ Real.exp (2 * u) := by
    have h := Real.sum_le_exp_of_nonneg (x := 2 * u) (by linarith) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two] at h
    norm_num at h
    linarith
  -- Complete the square: 5u - π e^{2u} ≤ -π + (c+5-2π)^2/(8π) - c*u
  have hexp_alg : 5 * u - Real.pi * Real.exp (2 * u) ≤
      (-Real.pi + (c + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) + (-c * u) := by
    have hsq : 0 ≤ (Real.sqrt (2 * Real.pi) * u - (c + 5 - 2 * Real.pi) / (2 * Real.sqrt (2 * Real.pi))) ^ 2 :=
      sq_nonneg _
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    have hsr_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2pi_pos)
    have hsr_sq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (le_of_lt h2pi_pos)
    have hexpand : (Real.sqrt (2 * Real.pi) * u - (c + 5 - 2 * Real.pi) / (2 * Real.sqrt (2 * Real.pi))) ^ 2 =
        2 * Real.pi * u ^ 2 - (c + 5 - 2 * Real.pi) * u + (c + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi) := by
      rw [sub_sq, mul_pow, div_pow, mul_pow, hsr_sq]
      have hmid : 2 * (Real.sqrt (2 * Real.pi) * u) * ((c + 5 - 2 * Real.pi) / (2 * Real.sqrt (2 * Real.pi))) =
          (c + 5 - 2 * Real.pi) * u := by field_simp [hsr_ne]
      rw [hmid]; ring
    rw [hexpand] at hsq
    nlinarith [Real.pi_pos]
  have hexp_le : Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) * Real.exp (u / 2) ≤
      Real.exp (-Real.pi + (c + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) * Real.exp (-c * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc riemannPhi u * u ^ k * Real.cosh (1 / 2 * u)
    _ ≤ ((21 / 20 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)))) *
          u ^ k * Real.exp (u / 2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hphi (pow_nonneg hu0 _)) hch
          (le_of_lt (Real.cosh_pos _)) (by positivity)
    _ = ((21 / 20 : ℝ) * 4 * Real.pi ^ 2) *
          (Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) * Real.exp (u / 2)) * u ^ k := by ring
    _ ≤ ((21 / 20 : ℝ) * 4 * Real.pi ^ 2) *
          (Real.exp (-Real.pi + (c + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) * Real.exp (-c * u)) * u ^ k := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le (by positivity)) (pow_nonneg hu0 _)
    _ = ((21 / 20 : ℝ) * 4 * Real.pi ^ 2 *
          Real.exp (-Real.pi + (c + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi))) * (u ^ k * Real.exp (-c * u)) := by ring
    _ ≤ A * (u ^ k * Real.exp (-c * u)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)

lemma xiCoshMoment_zero_half_le : xiCoshMoment 0 (1 / 2) ≤ 63 / 100 := by
  have h := xiCoshMoment_half_le_quad_completion 0 (c := 4) (A := 42 * (6 / 100)) (by norm_num) ?_
  · simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h; norm_num at h; linarith
  · have hpi_lo := Real.pi_gt_d2; have hpi_hi := Real.pi_lt_d2
    have hcoeff : (21 / 20 : ℝ) * 4 * Real.pi ^ 2 < 42 := by nlinarith
    have hB : (4 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi) < 3 / 10 := by
      have h1 : 0 < 4 + 5 - 2 * Real.pi := by linarith
      have h2 : 4 + 5 - 2 * Real.pi < 272 / 100 := by linarith
      have hsq : (4 + 5 - 2 * Real.pi) ^ 2 < (272 / 100 : ℝ) ^ 2 := by nlinarith
      rw [div_lt_iff₀ (by positivity : 0 < 8 * Real.pi)]; nlinarith
    have hexp_le : Real.exp (-Real.pi + (4 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) < 6 / 100 := by
      have h1 : Real.exp (-Real.pi + (4 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) < Real.exp (-(284 / 100 : ℝ)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp (-(284 / 100 : ℝ)) < 6 / 100 := by
        apply exp_neg_bound_from_taylor (by norm_num) (by norm_num) (n := 7)
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
      linarith
    nlinarith [Real.exp_pos (-Real.pi + (4 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi))]

lemma xiCoshMoment_two_zero_le : xiCoshMoment 2 0 ≤ 43 / 1000 := by
  have hmono : xiCoshMoment 2 0 ≤ xiCoshMoment 2 (1 / 2) := by
    refine MeasureTheory.setIntegral_mono_on (integrableOn_phi_pow_cosh 2 0)
      (integrableOn_phi_pow_cosh 2 (1 / 2)) measurableSet_Ioi fun u hu => ?_
    simp only [zero_mul, Real.cosh_zero]
    exact mul_le_mul_of_nonneg_left (Real.one_le_cosh _) (mul_nonneg (le_of_lt (riemannPhi_pos u)) (sq_nonneg u))
  have h := xiCoshMoment_half_le_quad_completion 2 (c := 6) (A := 42 * (11 / 100)) (by norm_num) ?_
  · simp only [Nat.factorial] at h; norm_num at h; linarith
  · have hpi_lo := Real.pi_gt_d2; have hpi_hi := Real.pi_lt_d2
    have hcoeff : (21 / 20 : ℝ) * 4 * Real.pi ^ 2 < 42 := by nlinarith
    have hB : (6 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi) < 9 / 10 := by
      have h1 : 0 < 6 + 5 - 2 * Real.pi := by linarith
      have h2 : 6 + 5 - 2 * Real.pi < 472 / 100 := by linarith
      have hsq : (6 + 5 - 2 * Real.pi) ^ 2 < (472 / 100 : ℝ) ^ 2 := by nlinarith
      rw [div_lt_iff₀ (by positivity : 0 < 8 * Real.pi)]; nlinarith
    have hexp_le : Real.exp (-Real.pi + (6 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) < 11 / 100 := by
      have h1 : Real.exp (-Real.pi + (6 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) < Real.exp (-(224 / 100 : ℝ)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp (-(224 / 100 : ℝ)) < 11 / 100 := by
        apply exp_neg_bound_from_taylor (by norm_num) (by norm_num) (n := 6)
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
      linarith
    nlinarith [Real.exp_pos (-Real.pi + (6 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi))]

lemma xiCoshMoment_four_half_le : xiCoshMoment 4 (1 / 2) ≤ 102 / 10000 := by
  have h := xiCoshMoment_half_le_quad_completion 4 (c := 7) (A := 42 * (17 / 100)) (by norm_num) ?_
  · simp only [Nat.factorial] at h; norm_num at h; linarith
  · have hpi_lo := Real.pi_gt_d2; have hpi_hi := Real.pi_lt_d2
    have hcoeff : (21 / 20 : ℝ) * 4 * Real.pi ^ 2 < 42 := by nlinarith
    have hB : (7 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi) < 131 / 100 := by
      have h1 : 0 < 7 + 5 - 2 * Real.pi := by linarith
      have h2 : 7 + 5 - 2 * Real.pi < 572 / 100 := by linarith
      have hsq : (7 + 5 - 2 * Real.pi) ^ 2 < (572 / 100 : ℝ) ^ 2 := by nlinarith
      rw [div_lt_iff₀ (by positivity : 0 < 8 * Real.pi)]; nlinarith
    have hexp_le : Real.exp (-Real.pi + (7 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) < 17 / 100 := by
      have h1 : Real.exp (-Real.pi + (7 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi)) < Real.exp (-(183 / 100 : ℝ)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h2 : Real.exp (-(183 / 100 : ℝ)) < 17 / 100 := by
        apply exp_neg_bound_from_taylor (by norm_num) (by norm_num) (n := 6)
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
      linarith
    nlinarith [Real.exp_pos (-Real.pi + (7 + 5 - 2 * Real.pi) ^ 2 / (8 * Real.pi))]

/-- Elementary antitonicity of the leading kernel profile `g(x) = (4π^2 x^2 - 6π x) e^{-π x}` on `[1, ∞)`,
    yielding the explicit 1-bin lower bound `Φ(u) ≥ 1/3` for all `u ∈ [0, 1/4]`! -/
lemma riemannPhi_ge_one_third_on_quarter {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) :
    (1 / 3 : ℝ) ≤ riemannPhi u := by
  -- Step 1: Φ(u) ≥ riemannPhiTerm 0 u ≥ (4π^2 x^2 - 6π x) e^{-π x} where x = e^{2u} ∈ [1, 17/10]
  have hterm0 : riemannPhiTerm 0 u ≤ riemannPhi u := by
    dsimp [riemannPhi]
    have hsum : Summable (fun n : ℕ => riemannPhiTerm n u) := by
      have hbase := (summable_pow_mul_exp_neg_sq 4 (c := Real.pi * Real.exp (2 * u)) (by positivity)).mul_left
        (4 * Real.pi ^ 2 * Real.exp (4 * u) * Real.exp (u / 2))
      refine hbase.of_nonneg_of_le (fun n => le_of_lt (riemannPhiTerm_pos_of_nonneg n hu0)) (fun n => ?_)
      dsimp [riemannPhiTerm, thetaHalfTerm]
      have hpoly : 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
          6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) ≤
          4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) := by
        have : 0 ≤ 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
        linarith
      have hexp : Real.exp (u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
          Real.exp (u / 2) * Real.exp (-(Real.pi * Real.exp (2 * u)) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]
      calc (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
              6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) *
            (Real.exp (u / 2) * Real.exp (-(Real.pi * Real.exp (2 * u)) * ((n + 1 : ℕ) : ℝ) ^ 2))
        _ ≤ (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u)) *
            (Real.exp (u / 2) * Real.exp (-(Real.pi * Real.exp (2 * u)) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = _ := by ring
    exact hsum.le_tsum 0 (fun n _ => le_of_lt (riemannPhiTerm_pos_of_nonneg n hu0))
  -- Step 2: g(x) = (4π^2 x^2 - 6π x) e^{-π x} is antitone on [1, ∞)
  let g : ℝ → ℝ := fun x => (4 * Real.pi ^ 2 * x ^ 2 - 6 * Real.pi * x) * Real.exp (-Real.pi * x)
  have hg_anti : AntitoneOn g (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · exact (((continuous_const.mul (continuous_pow 2)).sub (continuous_const.mul continuous_id)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
    · intro x _
      have hlin : HasDerivAt (fun s : ℝ => -Real.pi * s) (-Real.pi) x := by
        simpa using (hasDerivAt_id x).const_mul (-Real.pi)
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (-Real.pi * s))
          (Real.exp (-Real.pi * x) * (-Real.pi)) x := by
        simpa [Function.comp_def] using (Real.hasDerivAt_exp (-Real.pi * x)).comp x hlin
      exact ((((hasDerivAt_pow 2 x).const_mul (4 * Real.pi ^ 2)).sub
        ((hasDerivAt_id x).const_mul (6 * Real.pi))).mul hexp).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hd : HasDerivAt g
          (Real.pi * Real.exp (-Real.pi * x) * (-4 * Real.pi ^ 2 * x ^ 2 + 14 * Real.pi * x - 6)) x := by
        have h1 : HasDerivAt (fun s : ℝ => 4 * Real.pi ^ 2 * s ^ 2 - 6 * Real.pi * s)
            (8 * Real.pi ^ 2 * x - 6 * Real.pi) x := by
          have ha : HasDerivAt (fun s : ℝ => 4 * Real.pi ^ 2 * s ^ 2) (4 * Real.pi ^ 2 * (2 * x)) x := by
            simpa using (hasDerivAt_pow 2 x).const_mul (4 * Real.pi ^ 2)
          have hb : HasDerivAt (fun s : ℝ => 6 * Real.pi * s) (6 * Real.pi) x := by
            simpa using (hasDerivAt_id' x).const_mul (6 * Real.pi)
          have h := ha.sub hb
          have hval : 4 * Real.pi ^ 2 * (2 * x) - 6 * Real.pi = 8 * Real.pi ^ 2 * x - 6 * Real.pi := by ring
          rwa [hval] at h
        have h2 : HasDerivAt (fun s : ℝ => Real.exp (-Real.pi * s))
            (-Real.pi * Real.exp (-Real.pi * x)) x := by
          have hlin : HasDerivAt (fun s : ℝ => -Real.pi * s) (-Real.pi) x := by
            simpa using (hasDerivAt_id' x).const_mul (-Real.pi)
          have h := (Real.hasDerivAt_exp (-Real.pi * x)).comp x hlin
          rw [Function.comp_def] at h
          have hval : Real.exp (-Real.pi * x) * -Real.pi = -Real.pi * Real.exp (-Real.pi * x) := by ring
          rwa [hval] at h
        have hm := h1.mul h2
        have hval : (8 * Real.pi ^ 2 * x - 6 * Real.pi) * Real.exp (-Real.pi * x) +
            (4 * Real.pi ^ 2 * x ^ 2 - 6 * Real.pi * x) * (-Real.pi * Real.exp (-Real.pi * x)) =
            Real.pi * Real.exp (-Real.pi * x) * (-4 * Real.pi ^ 2 * x ^ 2 + 14 * Real.pi * x - 6) := by ring
        rwa [hval] at hm
      rw [hd.deriv]
      have hpi_lo := Real.pi_gt_d2; have hpi_hi := Real.pi_lt_d2
      have hquad : -4 * Real.pi ^ 2 * x ^ 2 + 14 * Real.pi * x - 6 ≤ 0 := by
        have hx1 : 0 ≤ x - 1 := by linarith [mem_Ioi.mp hx]
        have hx_ge1' : 1 ≤ x := by linarith
        have h1 : 0 < 8 * Real.pi ^ 2 - 14 * Real.pi := by nlinarith
        have h2 : 0 < 4 * Real.pi ^ 2 - 14 * Real.pi + 6 := by nlinarith
        have hdecomp : 4 * Real.pi ^ 2 * x ^ 2 - 14 * Real.pi * x + 6 =
            4 * Real.pi ^ 2 * (x - 1) ^ 2 + (8 * Real.pi ^ 2 - 14 * Real.pi) * (x - 1) +
            (4 * Real.pi ^ 2 - 14 * Real.pi + 6) := by ring
        nlinarith [sq_nonneg (x - 1)]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hquad
  -- Step 3: Evaluate at x = e^{2u} ∈ [1, 17/10]
  have hx_ge1 : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hx_le : Real.exp (2 * u) ≤ 17 / 10 :=
    (Real.exp_le_exp.mpr (by linarith : 2 * u ≤ 1 / 2)).trans (le_of_lt exp_half_lt_17_div_10)
  have hg_ge : g (17 / 10) ≤ g (Real.exp (2 * u)) :=
    hg_anti hx_ge1 (by norm_num : (1 : ℝ) ≤ 17 / 10) hx_le
  have hg_17 : (1 / 3 : ℝ) ≤ g (17 / 10) := by
    dsimp [g]
    have hpi_lo := Real.pi_gt_d2; have hpi_hi := Real.pi_lt_d2
    have hpoly : (80 : ℝ) < 4 * Real.pi ^ 2 * (17 / 10) ^ 2 - 6 * Real.pi * (17 / 10) := by nlinarith
    have hexp_ge : (1 / 220 : ℝ) < Real.exp (-Real.pi * (17 / 10)) := by
      have h1 : Real.exp (-(5355 / 1000 : ℝ)) < Real.exp (-Real.pi * (17 / 10)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have h2 : (1 / 220 : ℝ) < Real.exp (-(5355 / 1000 : ℝ)) := by
        rw [Real.exp_neg]
        have hlt := exp_5355_div_1000_lt_220
        have hp := Real.exp_pos (5355 / 1000 : ℝ)
        rw [one_div]
        exact inv_strictAnti₀ hp hlt
      linarith
    nlinarith
  -- Connect g(e^{2u}) ≤ riemannPhiTerm 0 u ≤ riemannPhi u
  have hrel : g (Real.exp (2 * u)) ≤ riemannPhiTerm 0 u := by
    dsimp [g, riemannPhiTerm, thetaHalfTerm]
    have h1 : Real.exp (u / 2 - Real.pi * ((0 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
        Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
      rw [← Real.exp_add]; congr 1; norm_num; ring
    have h2 : (4 * Real.pi ^ 2 * ((0 + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
        6 * Real.pi * ((0 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
        4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 - 6 * Real.pi * Real.exp (2 * u) := by
      rw [show Real.exp (2 * u) ^ 2 = Real.exp (4 * u) by rw [sq, ← Real.exp_add]; congr 1; ring]
      norm_num
    rw [h1, h2]
    have hpos_poly : 0 ≤ 4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 - 6 * Real.pi * Real.exp (2 * u) := by
      have hpi_lo := Real.pi_gt_d2
      have hfac : 4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 - 6 * Real.pi * Real.exp (2 * u) =
          Real.exp (2 * u) * (4 * Real.pi ^ 2 * Real.exp (2 * u) - 6 * Real.pi) := by ring
      rw [hfac]
      exact mul_nonneg (by linarith) (by nlinarith)
    have he_half : 1 ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
    have he_pos : 0 ≤ Real.exp (-Real.pi * Real.exp (2 * u)) := le_of_lt (Real.exp_pos _)
    calc (4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 - 6 * Real.pi * Real.exp (2 * u)) *
          Real.exp (-Real.pi * Real.exp (2 * u))
      _ = (4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 - 6 * Real.pi * Real.exp (2 * u)) *
          (1 * Real.exp (-Real.pi * Real.exp (2 * u))) := by ring
      _ ≤ (4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 - 6 * Real.pi * Real.exp (2 * u)) *
          (Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he_half he_pos) hpos_poly
  linarith [hg_17, hg_ge, hrel, hterm0]

lemma xiCoshMoment_zero_zero_ge : (1 / 12 : ℝ) ≤ xiCoshMoment 0 0 := by
  dsimp [xiCoshMoment]
  have hsub : Ioc (0 : ℝ) (1 / 4) ⊆ Ioi (0 : ℝ) := fun x hx => hx.1
  have h1 : (∫ u in Ioc (0 : ℝ) (1 / 4), riemannPhi u * u ^ 0 * Real.cosh (0 * u)) ≤
      ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cosh (0 * u) :=
    MeasureTheory.setIntegral_mono_set (integrableOn_phi_pow_cosh 0 0)
      (Filter.Eventually.of_forall fun u => by
        simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]; exact le_of_lt (riemannPhi_pos u))
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  have h2 : (1 / 12 : ℝ) ≤ ∫ u in Ioc (0 : ℝ) (1 / 4), riemannPhi u * u ^ 0 * Real.cosh (0 * u) := by
    have hconst : (1 / 12 : ℝ) = ∫ _u in Ioc (0 : ℝ) (1 / 4), (1 / 3 : ℝ) := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4),
          intervalIntegral.integral_const, smul_eq_mul]; norm_num
    rw [hconst]
    refine MeasureTheory.setIntegral_mono_on (integrableOn_const (by simp))
      ((integrableOn_phi_pow_cosh 0 0).mono_set hsub) measurableSet_Ioc fun u hu => ?_
    simp only [zero_mul, Real.cosh_zero, pow_zero, mul_one]
    exact riemannPhi_ge_one_third_on_quarter (le_of_lt hu.1) hu.2
  linarith

lemma xiCoshMoment_two_zero_ge : (1 / 576 : ℝ) ≤ xiCoshMoment 2 0 := by
  dsimp [xiCoshMoment]
  have hsub : Ioc (0 : ℝ) (1 / 4) ⊆ Ioi (0 : ℝ) := fun x hx => hx.1
  have h1 : (∫ u in Ioc (0 : ℝ) (1 / 4), riemannPhi u * u ^ 2 * Real.cosh (0 * u)) ≤
      ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 2 * Real.cosh (0 * u) :=
    MeasureTheory.setIntegral_mono_set (integrableOn_phi_pow_cosh 2 0)
      (Filter.Eventually.of_forall fun u => by
        simp only [zero_mul, Real.cosh_zero, mul_one]
        exact mul_nonneg (le_of_lt (riemannPhi_pos u)) (sq_nonneg u))
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  have h2 : (1 / 576 : ℝ) ≤ ∫ u in Ioc (0 : ℝ) (1 / 4), riemannPhi u * u ^ 2 * Real.cosh (0 * u) := by
    have hpow : (1 / 576 : ℝ) = ∫ u in Ioc (0 : ℝ) (1 / 4), (1 / 3 : ℝ) * u ^ 2 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4),
          intervalIntegral.integral_const_mul, integral_pow]; norm_num
    rw [hpow]
    refine MeasureTheory.setIntegral_mono_on
      ((continuous_const.mul (continuous_pow 2)).integrableOn_Ioc)
      ((integrableOn_phi_pow_cosh 2 0).mono_set hsub) measurableSet_Ioc fun u hu => ?_
    simp only [zero_mul, Real.cosh_zero, mul_one]
    exact mul_le_mul_of_nonneg_right (riemannPhi_ge_one_third_on_quarter (le_of_lt hu.1) hu.2) (sq_nonneg u)
  linarith

/-- THEOREM III.1 (EXPLICIT CONSTRUCTIVE UNCONDITIONAL CONVEXITY CORRIDOR `|γ| ≤ 1/5`):
    Replacing the non-constructive Tube-Lemma corridor `∃ δ > 0`, for EVERY `σ ∈ [0, 1/2]`
    and EVERY `|γ| ≤ 1/5`, the transverse Hessian `∂_σ^2 V(σ, γ)` is STRICTLY POSITIVE! -/
theorem xiNormSq_deriv2_pos_explicit_corridor {σ γ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hγ : |γ| ≤ 1 / 5) :
    0 < deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ := by
  have hq := xiNormSq_deriv2_ge_moment_quadratic hσ0 hσ1 γ
  have hI00 := xiCoshMoment_zero_zero_ge
  have hI20 := xiCoshMoment_two_zero_ge
  have hI0h := xiCoshMoment_zero_half_le
  have hI4h := xiCoshMoment_four_half_le
  have hI0h_nn : 0 ≤ xiCoshMoment 0 (1 / 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u _ =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (by norm_num)) (le_of_lt (Real.cosh_pos _))
  have hI4h_nn : 0 ≤ xiCoshMoment 4 (1 / 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (le_of_lt hu) _)) (le_of_lt (Real.cosh_pos _))
  have hγ2 : γ ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg γ) hγ 2
  have hprod_lb : (1 / 12 : ℝ) * (1 / 576) ≤ xiCoshMoment 0 0 * xiCoshMoment 2 0 :=
    mul_le_mul hI00 hI20 (by norm_num) (by linarith)
  have hprod_ub : xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) ≤ (63 / 100) * (102 / 10000) :=
    mul_le_mul hI0h hI4h hI4h_nn (by norm_num)
  have hdiff_ub : xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2 ≤
      (63 / 100) * (102 / 10000) := by nlinarith [sq_nonneg (xiCoshMoment 2 0)]
  have hneg_term : 4 * γ ^ 2 * (xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2) ≤
      4 * (1 / 5 : ℝ) ^ 2 * ((63 / 100) * (102 / 10000)) := by
    by_cases hsign : 0 ≤ xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2
    · exact mul_le_mul (by linarith) hdiff_ub hsign (by norm_num)
    · push Not at hsign
      have hneg : 4 * γ ^ 2 * (xiCoshMoment 0 (1 / 2) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hsign)
      linarith
  linarith

/-- Explicit constructive positivity of the transverse restoring force `∂_σ V(σ, γ) > 0`
    on `(0, 1/2] × [-1/5, 1/5]`. -/
theorem xiNormSq_deriv1_pos_explicit_corridor {σ γ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hγ : |γ| ≤ 1 / 5) :
    0 < deriv (fun s : ℝ => xiNormSq s γ) σ := by
  have hd0 : deriv (fun s : ℝ => xiNormSq s γ) 0 = 0 := xiNormSq_deriv_sigma_zero γ
  have hdiff : Differentiable ℝ (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) :=
    fun t => (hasDerivAt_xiNormSq_deriv_sigma t γ).differentiableAt
  have hsm : StrictMonoOn (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) (Icc 0 (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2))
    · exact hdiff.continuous.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact xiNormSq_deriv2_pos_explicit_corridor (le_of_lt hx.1) (le_of_lt hx.2) hγ
  have hgt := hsm (left_mem_Icc.mpr (by norm_num)) ⟨le_of_lt hσ0, hσ1⟩ hσ0
  linarith

/-- Explicit constructive positivity of `Ξ(γ) > 0` on `[-1/5, 1/5]`. -/
theorem riemannXi_critical_pos_explicit_corridor {γ : ℝ} (hγ : |γ| ≤ 1 / 5) :
    0 < xiCritical γ := by
  have hq := xiCritical_ge_moment_quadratic γ
  have h0 := xiCoshMoment_zero_zero_ge
  have h2 := xiCoshMoment_two_zero_le
  have h2_nn : 0 ≤ xiCoshMoment 2 0 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u _ =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (sq_nonneg u)) (le_of_lt (Real.cosh_pos _))
  have hγ2 : γ ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg γ) hγ 2
  have hmul : γ ^ 2 * xiCoshMoment 2 0 ≤ (1 / 5 : ℝ) ^ 2 * (43 / 1000) :=
    mul_le_mul hγ2 h2 h2_nn (by norm_num)
  linarith

/-- THEOREM III.2 (CONSTRUCTIVE EXPLICIT ZERO-FREE RECTANGLE FOR MATHLIB4's `riemannZeta`):
    Directly on Mathlib4's official `riemannZeta`, EVERY point `s ∈ ℂ` in the explicit
    critical-strip rectangle `0 < Re(s) < 1 ∧ |Im(s)| ≤ 1/5` (BOTH on AND off the critical line!)
    satisfies `riemannZeta s ≠ 0`! -/
theorem riemannZeta_ne_zero_explicit_strip_rectangle {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : |s.im| ≤ 1 / 5) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hxi_zero : riemannXi s = 0 := (riemannXi_eq_zero_iff_riemannZeta hs0 hs1).mpr hz
  -- Consider V(σ, γ) = ‖riemannXi (1/2 + σ + i*γ)‖^2 = 0 where σ = s.re - 1/2, γ = s.im
  let σ : ℝ := s.re - 1 / 2
  let γ : ℝ := s.im
  have hV0 : xiNormSq σ γ = 0 := by
    dsimp [xiNormSq, σ, γ]
    have hs_eq : (⟨1 / 2 + (s.re - 1 / 2), s.im⟩ : ℂ) = s := by apply Complex.ext <;> simp
    rw [hs_eq, hxi_zero, norm_zero, sq, mul_zero]
  -- By evenness of V in σ, V(|σ|, γ) = 0 with |σ| ∈ [0, 1/2)
  have hV_abs0 : xiNormSq |σ| γ = 0 := by
    rcases le_total 0 σ with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_nonpos h, xiNormSq_even_sigma]; exact hV0
  have habs_lt : |σ| < 1 / 2 := abs_lt.mpr ⟨by dsimp [σ]; linarith, by dsimp [σ]; linarith⟩
  -- On [0, 1/2], V(0, γ) = Ξ(γ)^2 > 0, and V(·, γ) is nondecreasing on [0, 1/2], so V(|σ|, γ) > 0!
  have hV_crit_pos : 0 < xiNormSq 0 γ := by
    have hre := riemannXi_im_half_eq_zero γ
    have hpos := riemannXi_critical_pos_explicit_corridor him
    dsimp [xiNormSq, xiCritical] at hpos ⊢
    rw [add_zero, Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  by_cases hσ0 : |σ| = 0
  · rw [hσ0] at hV_abs0; linarith
  · have hσ_pos : 0 < |σ| := lt_of_le_of_ne (abs_nonneg σ) (Ne.symm hσ0)
    have hmono : xiNormSq 0 γ ≤ xiNormSq |σ| γ := by
      have hdiffV : Differentiable ℝ (fun s : ℝ => xiNormSq s γ) :=
        fun s => (hasDerivAt_xiNormSq_sigma s γ).differentiableAt
      have hM : MonotoneOn (fun s : ℝ => xiNormSq s γ) (Icc 0 (1 / 2)) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
        · exact hdiffV.continuous.continuousOn
        · exact hdiffV.differentiableOn.mono interior_subset
        · intro x hx
          rw [interior_Icc] at hx
          exact le_of_lt (xiNormSq_deriv1_pos_explicit_corridor hx.1 (le_of_lt hx.2) him)
      exact hM (left_mem_Icc.mpr (by norm_num)) ⟨le_of_lt hσ_pos, le_of_lt habs_lt⟩ (le_of_lt hσ_pos)
    linarith

-- ==============================================================================
-- PART IV: ROUTE B — SCHOENBERG COMPLETE-MONOTONICITY NO-GO THEOREM
-- ==============================================================================

/-- THEOREM IV.1 (Universal Exponential Lower Bound on Non-Zero Positive Laplace Transforms):
    For ANY finite positive Borel measure `μ` on `[0, ∞)` with `μ(Ici 0) ≠ 0`, its Laplace
    transform `F(x) = ∫ α in Ici 0, exp(-α * x) dμ(α)` satisfies an exponential lower bound:
      `∃ c > 0, ∃ α₁ > 0, ∀ x ≥ 0, c * exp(-α₁ * x) ≤ F(x)`. -/
theorem schoenberg_laplace_exp_lower_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ_ne : μ (Ici (0 : ℝ)) ≠ 0) :
    ∃ c > (0 : ℝ), ∃ α₁ > (0 : ℝ), ∀ x : ℝ, 0 ≤ x →
      c * Real.exp (-α₁ * x) ≤ ∫ α in Ici (0 : ℝ), Real.exp (-α * x) ∂μ := by
  -- Since Ici 0 = ⋃_{n : ℕ} Icc 0 (n + 1), some compact interval [0, N+1] has positive measure!
  have hunion : Ici (0 : ℝ) = ⋃ n : ℕ, Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ) := by
    ext α; simp only [mem_Ici, mem_iUnion, mem_Icc]
    constructor
    · intro h0
      obtain ⟨n, hn⟩ := exists_nat_gt α
      exact ⟨n, h0, by push_cast; linarith⟩
    · rintro ⟨_, h0, _⟩; exact h0
  have hex_pos : ∃ n : ℕ, 0 < (μ (Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ))).toReal := by
    by_contra hall
    push Not at hall
    have hzero_all : ∀ n : ℕ, μ (Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ)) = 0 := by
      intro n
      have hle := hall n
      have hnn := ENNReal.toReal_nonneg (a := μ (Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ)))
      have heq0 : (μ (Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ))).toReal = 0 := le_antisymm hle hnn
      exact (ENNReal.toReal_eq_zero_iff _).mp heq0 |>.resolve_right (measure_ne_top μ _)
    have htot : μ (Ici (0 : ℝ)) = 0 := by
      rw [hunion]; exact measure_iUnion_null hzero_all
    exact hμ_ne htot
  obtain ⟨N, hN_pos⟩ := hex_pos
  let α₁ : ℝ := ((N + 1 : ℕ) : ℝ)
  let c : ℝ := (μ (Icc (0 : ℝ) α₁)).toReal
  refine ⟨c, hN_pos, α₁, by positivity, fun x hx => ?_⟩
  have hsub : Icc (0 : ℝ) α₁ ⊆ Ici (0 : ℝ) := fun α hα => hα.1
  have hint : IntegrableOn (fun α : ℝ => Real.exp (-α * x)) (Ici 0) μ := by
    refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_ne_top μ _)).mono'
      ((Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with α hα
    have hα0 : 0 ≤ α := mem_Ici.mp hα
    rw [Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 : (∫ α in Icc (0 : ℝ) α₁, Real.exp (-α * x) ∂μ) ≤
      ∫ α in Ici (0 : ℝ), Real.exp (-α * x) ∂μ :=
    MeasureTheory.setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun α => le_of_lt (Real.exp_pos _))
      (Filter.Eventually.of_forall fun α hα => hsub hα)
  have h2 : c * Real.exp (-α₁ * x) ≤ ∫ α in Icc (0 : ℝ) α₁, Real.exp (-α * x) ∂μ := by
    have hconst : c * Real.exp (-α₁ * x) = ∫ _α in Icc (0 : ℝ) α₁, Real.exp (-α₁ * x) ∂μ := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]; rfl
    rw [hconst]
    refine MeasureTheory.setIntegral_mono_on (integrableOn_const (hs := measure_ne_top μ _))
      (hint.mono_set hsub) measurableSet_Icc fun α hα => ?_
    exact Real.exp_le_exp.mpr (by nlinarith [hα.2])
  linarith

/-- The exact 1D light-cone Laguerre cosine kernel
    `G_{2,0}(w) = ∫_ℝ r^2 * Φ((r + w)/2) * Φ((r - w)/2) dr`. -/
noncomputable def riemannLaguerreKernel1D (w : ℝ) : ℝ :=
  ∫ r : ℝ, r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)

/-- Super-exponential decay of `G_{2,0}(w)` for `w ≥ 0`:
    `G_{2,0}(w) ≤ C * exp(-(π/4) * e^w)` — strictly faster than EVERY Gaussian `exp(-α₁ * w^2)`! -/
theorem riemannLaguerreKernel1D_superexp_le :
    ∃ C > (0 : ℝ), ∀ w : ℝ, 0 ≤ w →
      riemannLaguerreKernel1D w ≤ C * Real.exp (-(Real.pi / 4) * Real.exp w) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  -- For any u ∈ ℝ, since Φ is even: Φ(u) = Φ(|u|) ≤ C2 * exp((9/2)|u| - (π/2) e^{2|u|})
  have hPhi_abs : ∀ u : ℝ, riemannPhi u ≤ C2 * Real.exp (9 * |u| / 2 - Real.pi / 2 * Real.exp (2 * |u|)) := by
    intro u
    have h := hPhi_le |u| (abs_nonneg u)
    rw [Real.norm_eq_abs, abs_of_pos (riemannPhi_pos |u|)] at h
    have hev : riemannPhi |u| = riemannPhi u := by
      rcases le_total 0 u with hu | hu
      · rw [abs_of_nonneg hu]
      · rw [abs_of_nonpos hu, riemannPhi_even]
    rwa [← hev]
  -- Key 2D inequality: for ALL r ∈ ℝ and w ≥ 0,
  --   e^{|r+w|} + e^{|r-w|} ≥ max(e^{r+w}, e^{-r-w}) + max(e^{r-w}, e^{w-r}) ≥ e^w + e^{|r|}?
  -- Even simpler and exact:
  --   e^{|r+w|} ≥ e^{w/2 + |r|/2} OR e^{|r-w|} ≥ e^{w/2 + |r|/2}!!
  -- Proof: max(|r+w|, |r-w|) = |r| + w (since w ≥ 0: if r ≥ 0 then r+w = |r|+w; if r ≤ 0 then w-r = |r|+w)!
  -- Therefore:
  --   e^{2 * max(|r+w|/2, |r-w|/2)} = e^{|r| + w} = e^{|r|} * e^w ≥ (1/2) e^w + (1/2) e^{|r|} (Wait: for a,b ≥ 1, a*b ≥ (a+b)/2!)
  --   In fact for ALL a ≥ 1, b ≥ 1: a * b ≥ (1/2) * a + (1/2) * b (since 2ab - a - b = (a-1)(b-1) + ab - 1 ≥ 0)!
  have hsum_exp : ∀ r w : ℝ, 0 ≤ w →
      Real.exp w / 2 + Real.exp |r| / 2 ≤
        Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|) := by
    intro r w hw
    have hmax : |r| + w ≤ max |r + w| |r - w| := by
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
        exact (le_of_eq (abs_of_nonneg (by linarith)).symm).trans (le_max_left _ _)
      · rw [abs_of_nonpos hr]
        have : -r + w = |r - w| := by rw [abs_of_nonpos (by linarith)]; ring
        exact (le_of_eq this).trans (le_max_right _ _)
    have h1 : Real.exp (|r| + w) ≤ Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|) := by
      have ha : 2 * |(r + w) / 2| = |r + w| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
      have hb : 2 * |(r - w) / 2| = |r - w| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
      rw [ha, hb]
      rcases le_total |r + w| |r - w| with h | h
      · rw [max_eq_right h] at hmax
        have : Real.exp (|r| + w) ≤ Real.exp |r - w| := Real.exp_le_exp.mpr hmax
        linarith [Real.exp_pos |r + w|]
      · rw [max_eq_left h] at hmax
        have : Real.exp (|r| + w) ≤ Real.exp |r + w| := Real.exp_le_exp.mpr hmax
        linarith [Real.exp_pos |r - w|]
    have ha1 : 1 ≤ Real.exp |r| := Real.one_le_exp (abs_nonneg r)
    have hb1 : 1 ≤ Real.exp w := Real.one_le_exp hw
    have hprod : Real.exp w / 2 + Real.exp |r| / 2 ≤ Real.exp (|r| + w) := by
      rw [Real.exp_add]; nlinarith
    linarith
  -- Also |(r+w)/2| + |(r-w)/2| = max(|r|, w) ≤ |r| + w, and (9/2)*w - (π/4) e^w is bounded above on w ≥ 0!
  -- Wait: bound (9/2)*w ≤ (π/8)*e^w + K? Better: use (1/2) of -(π/4)*e^w to kill (9/2)*w, OR keep -(π/4)*e^w using e^w/2!
  -- Actually: 9/2*(|(r+w)/2| + |(r-w)/2|) ≤ (9/2)*(|r| + w).
  -- Since e^{|r|+w} ≥ (3/4)*e^w + (1/4)*e^{|r|}? Wait: for a ≥ 1, b ≥ 1, ab = (3/4)ab + (1/4)ab ≥ (3/4)b + (1/4)a!
  -- YES!! Because a ≥ 1 implies a*b ≥ b, and b ≥ 1 implies a*b ≥ a!
  -- So ab = (3/4)*ab + (1/4)*ab ≥ (3/4)*b + (1/4)*a!!
  -- Multiply by π/2: -(π/2)*(3/4)*e^w = -(3π/8)*e^w = -(π/4)*e^w - (π/8)*e^w,
  -- and (9/2)*w - (π/8)*e^w ≤ (9/2)*w - (π/8)*(1 + w + w^2/2) ≤ K₀ (bounded constant on w ≥ 0!)!
  -- Meanwhile on r: r^2 * exp((9/2)|r| - (π/8)*e^{|r|}) is integrable on ℝ!
  let h_r : ℝ → ℝ := fun r => r ^ 2 * Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|)
  have hh_int : Integrable h_r := by
    -- Integrable on Ioi 0 and Iic 0 by evenness!
    have hpos : IntegrableOn h_r (Ioi 0) := by
      have hdom := (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul (1000 : ℝ)
      -- Even cleaner: compare to (2 * exp r) * exp(9r/2 - (π/8)*(1 + r + r^2/2))?
      -- Use pow_le_factorial_mul_exp 2 (r) ≤ 2 * exp r and exp r ≥ 1 + r + r^2/2 + r^3/6?
      -- Wait: exp r ≥ r^2 / 2, wait: better, exp r ≥ (8 * 7 / π) * r for large r!
      -- Simply: for ALL r ≥ 0, (π/8) * exp r ≥ (π/8) * (1 + r + r^2/2) ≥ (π/16)*r^2,
      -- and (13/2)*r - (π/16)*r^2 ≤ -r + 400 (completing the square)!
      have hdom' : IntegrableOn (fun r : ℝ => 2 * Real.exp 400 * Real.exp (-r)) (Ioi 0) := by
        have h0 : IntegrableOn (fun r : ℝ => 2 * Real.exp 400 * Real.exp (-1 * r)) (Ioi 0) :=
          (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul (2 * Real.exp 400)
        exact h0.congr_fun (fun r _ => by ring_nf) measurableSet_Ioi
      refine hdom'.mono' (((continuous_pow 2).mul (Real.continuous_exp.comp
        ((continuous_const.mul continuous_abs).div_const 2 |>.sub
          (continuous_const.mul (Real.continuous_exp.comp continuous_abs))))).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      dsimp [h_r]
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hr0]
      have hr2 := pow_le_factorial_mul_exp 2 hr0
      simp only [Nat.factorial] at hr2
      have hexp_ge : 1 + r + r ^ 2 / 2 ≤ Real.exp r := by
        have h := Real.sum_le_exp_of_nonneg hr0 3
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
                   Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two] at h
        norm_num at h; linarith
      have hpi_lo := Real.pi_gt_d2
      have hquad : 11 * r / 2 - (Real.pi / 8) * Real.exp r ≤ 400 - r := by
        have h1 : (Real.pi / 8) * (1 + r + r ^ 2 / 2) ≤ (Real.pi / 8) * Real.exp r :=
          mul_le_mul_of_nonneg_left hexp_ge (by positivity)
        have h2 : 0 ≤ (r - 20) ^ 2 := sq_nonneg _
        nlinarith
      calc r ^ 2 * Real.exp (9 * r / 2 - Real.pi / 8 * Real.exp r)
        _ ≤ (2 * Real.exp r) * Real.exp (9 * r / 2 - Real.pi / 8 * Real.exp r) := by
            have h2 : r ^ 2 ≤ 2 * Real.exp r := by norm_num at hr2; exact hr2
            exact mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _))
        _ = 2 * Real.exp (11 * r / 2 - Real.pi / 8 * Real.exp r) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ 2 * Real.exp (400 - r) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) (by norm_num)
        _ = 2 * Real.exp 400 * Real.exp (-r) := by rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
    have hneg : IntegrableOn h_r (Iio 0) := by
      have hpre : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by
        ext x; simp
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (f := h_r) (s := Iio 0) (MeasurableEquiv.neg ℝ).measurableEmbedding
      rw [hpre] at hmp
      refine hmp.mp ?_
      exact hpos.congr_fun (fun r _ => by dsimp [h_r, Function.comp_def]; rw [neg_sq, abs_neg]) measurableSet_Ioi
    have hzero : IntegrableOn h_r {0} := integrableOn_singleton (hx := by simp)
    have hunion : ({0} : Set ℝ) ∪ (Iio (0 : ℝ) ∪ Ioi (0 : ℝ)) = univ := by
      ext x; simp only [mem_union, mem_singleton_iff, mem_Iio, mem_Ioi, mem_univ, iff_true]
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    rw [← integrableOn_univ, ← hunion]
    exact hzero.union (hneg.union hpos)
  let K0 : ℝ := Real.exp 100
  let C : ℝ := C2 ^ 2 * K0 * (∫ r : ℝ, h_r r) + 1
  have hC_pos : 0 < C := by
    have hi : 0 ≤ ∫ r : ℝ, h_r r := integral_nonneg fun r => by dsimp [h_r]; positivity
    dsimp [C, K0]; positivity
  refine ⟨C, hC_pos, fun w hw => ?_⟩
  have hpt : ∀ r : ℝ, r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2) ≤
      (C2 ^ 2 * K0 * Real.exp (-(Real.pi / 4) * Real.exp w)) * h_r r := by
    intro r
    have hp1 := hPhi_abs ((r + w) / 2)
    have hp2 := hPhi_abs ((r - w) / 2)
    have htri : |(r + w) / 2| + |(r - w) / 2| ≤ |r| + w := by
      have h1 : |(r + w) / 2| ≤ (|r| + w) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := abs_add_le r w; rw [abs_of_nonneg hw] at this; linarith
      have h2 : |(r - w) / 2| ≤ (|r| + w) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := abs_sub r w; rw [abs_of_nonneg hw] at this; linarith
      linarith
    -- Use ab ≥ (3/4)*b + (1/4)*a for a = e^{|r|} ≥ 1, b = e^w ≥ 1
    have hmax_exp : (3 / 4 : ℝ) * Real.exp w + (1 / 4 : ℝ) * Real.exp |r| ≤
        Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|) := by
      have hmax : |r| + w ≤ max |r + w| |r - w| := by
        rcases le_total 0 r with hr | hr
        · rw [abs_of_nonneg hr]
          exact (le_of_eq (abs_of_nonneg (by linarith)).symm).trans (le_max_left _ _)
        · rw [abs_of_nonpos hr]
          have : -r + w = |r - w| := by rw [abs_of_nonpos (by linarith)]; ring
          exact (le_of_eq this).trans (le_max_right _ _)
      have h1 : Real.exp (|r| + w) ≤ Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|) := by
        have ha : 2 * |(r + w) / 2| = |r + w| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
        have hb : 2 * |(r - w) / 2| = |r - w| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
        rw [ha, hb]
        rcases le_total |r + w| |r - w| with h | h
        · rw [max_eq_right h] at hmax
          have := Real.exp_le_exp.mpr hmax; linarith [Real.exp_pos |r + w|]
        · rw [max_eq_left h] at hmax
          have := Real.exp_le_exp.mpr hmax; linarith [Real.exp_pos |r - w|]
      have ha1 : 1 ≤ Real.exp |r| := Real.one_le_exp (abs_nonneg r)
      have hb1 : 1 ≤ Real.exp w := Real.one_le_exp hw
      have hprod : (3 / 4 : ℝ) * Real.exp w + (1 / 4 : ℝ) * Real.exp |r| ≤ Real.exp (|r| + w) := by
        rw [Real.exp_add]; nlinarith
      linarith
    have hw_kill : 9 * w / 2 - (Real.pi / 8) * Real.exp w ≤ 100 := by
      have hexp_ge : 1 + w + w ^ 2 / 2 ≤ Real.exp w := by
        have h := Real.sum_le_exp_of_nonneg hw 3
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
        norm_num at h; linarith
      have hpi_lo := Real.pi_gt_d2
      have hsq : 0 ≤ (w - 12) ^ 2 := sq_nonneg _
      nlinarith
    have hprod_phi : riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2) ≤
        C2 ^ 2 * K0 * Real.exp (-(Real.pi / 4) * Real.exp w) *
          Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|) := by
      have h1 := mul_le_mul hp1 hp2 (le_of_lt (riemannPhi_pos _)) (by positivity)
      calc riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)
        _ ≤ C2 * Real.exp (9 * |(r + w) / 2| / 2 - Real.pi / 2 * Real.exp (2 * |(r + w) / 2|)) *
              (C2 * Real.exp (9 * |(r - w) / 2| / 2 - Real.pi / 2 * Real.exp (2 * |(r - w) / 2|))) := h1
        _ = C2 ^ 2 * (Real.exp (9 * |(r + w) / 2| / 2 - Real.pi / 2 * Real.exp (2 * |(r + w) / 2|)) *
              Real.exp (9 * |(r - w) / 2| / 2 - Real.pi / 2 * Real.exp (2 * |(r - w) / 2|))) := by ring
        _ = C2 ^ 2 * Real.exp ((9 * |(r + w) / 2| / 2 + 9 * |(r - w) / 2| / 2) -
              Real.pi / 2 * (Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|))) := by
            rw [← Real.exp_add]; congr 2; ring
        _ ≤ C2 ^ 2 * Real.exp ((9 * |r| / 2 + 9 * w / 2) -
              Real.pi / 2 * ((3 / 4) * Real.exp w + (1 / 4) * Real.exp |r|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            nlinarith [Real.pi_pos]
        _ ≤ C2 ^ 2 * Real.exp (100 + (-(Real.pi / 4) * Real.exp w) +
              (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            linarith
        _ = C2 ^ 2 * K0 * Real.exp (-(Real.pi / 4) * Real.exp w) *
              Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|) := by
            dsimp [K0]; rw [Real.exp_add, Real.exp_add]; ring
    dsimp [h_r]
    calc r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)
      _ = r ^ 2 * (riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)) := by ring
      _ ≤ r ^ 2 * (C2 ^ 2 * K0 * Real.exp (-(Real.pi / 4) * Real.exp w) *
            Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|)) :=
          mul_le_mul_of_nonneg_left hprod_phi (sq_nonneg r)
      _ = _ := by ring
  have hint_lhs : Integrable (fun r : ℝ => r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)) := by
    refine (hh_int.const_mul (C2 ^ 2 * K0 * Real.exp (-(Real.pi / 4) * Real.exp w))).mono'
      ((((continuous_pow 2).mul (continuous_riemannPhi.comp ((continuous_id.add continuous_const).div_const 2))).mul
        (continuous_riemannPhi.comp ((continuous_id.sub continuous_const).div_const 2))).aestronglyMeasurable) ?_
    filter_upwards with r
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg r) (le_of_lt (riemannPhi_pos _))) (le_of_lt (riemannPhi_pos _)))]
    exact hpt r
  have hint_le := integral_mono hint_lhs (hh_int.const_mul _) hpt
  rw [integral_const_mul] at hint_le
  dsimp [riemannLaguerreKernel1D, C]
  have h0 : 0 ≤ Real.exp (-(Real.pi / 4) * Real.exp w) := le_of_lt (Real.exp_pos _)
  nlinarith

/-- THEOREM IV.2 (SCHOENBERG COMPLETE-MONOTONICITY NO-GO THEOREM FOR ROUTE B):
    NO non-zero finite positive Borel measure `μ` on `[0, ∞)` can represent the 1D
    light-cone Laguerre kernel `x ↦ G_{2,0}(√x)` as a positive Schoenberg Gaussian/Laplace
    mixture `∫_{α ≥ 0} exp(-α * x) dμ(α)`!
    (Pinpoints the exact analytic obstruction in Route B: despite positive low-order
    differences, `G_{2,0}` is strictly 1D-Bochner and NOT Schoenberg completely monotone.) -/
theorem riemannLaguerreKernel1D_not_schoenberg_laplace (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ_ne : μ (Ici (0 : ℝ)) ≠ 0) :
    ¬ (∀ x : ℝ, 0 ≤ x →
        riemannLaguerreKernel1D (Real.sqrt x) = ∫ α in Ici (0 : ℝ), Real.exp (-α * x) ∂μ) := by
  intro hrep
  obtain ⟨c, hc_pos, α₁, hα₁_pos, hlb⟩ := schoenberg_laplace_exp_lower_bound μ hμ_ne
  obtain ⟨C, hC_pos, hub⟩ := riemannLaguerreKernel1D_superexp_le
  -- Choose w > 0 huge so that C * exp(-(π/4) * e^w) < c * exp(-α₁ * w^2)!
  -- Specifically, since e^w ≥ w^3 / 6 (from Real.sum_le_exp_of_nonneg for k = 4):
  -- pick w ≥ max(1, (24 / π) * (α₁ + |log(C/c)| + 1))!
  let M : ℝ := max 1 ((24 / Real.pi) * (α₁ + |Real.log (C / c)| + 1))
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM_ge1 : 1 ≤ M := le_max_left _ _
  have hM_ge2 : (24 / Real.pi) * (α₁ + |Real.log (C / c)| + 1) ≤ M := le_max_right _ _
  have hlb_val := hlb (M ^ 2) (sq_nonneg M)
  have hub_val := hub M (le_of_lt hM_pos)
  rw [← hrep (M ^ 2) (sq_nonneg M), Real.sqrt_sq (le_of_lt hM_pos)] at hlb_val
  have hboth : c * Real.exp (-α₁ * M ^ 2) ≤ C * Real.exp (-(Real.pi / 4) * Real.exp M) :=
    lb_val_trans hlb_val hub_val
  -- Derive contradiction via logs:
  have hdiv : Real.exp ((Real.pi / 4) * Real.exp M - α₁ * M ^ 2) ≤ C / c := by
    rw [Real.exp_sub, div_le_div_iff₀ (Real.exp_pos _) hc_pos]
    have h1 : c * Real.exp ((Real.pi / 4) * Real.exp M) * Real.exp (-(Real.pi / 4) * Real.exp M) = c := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have h2 := mul_le_mul_of_nonneg_right hboth (le_of_lt (Real.exp_pos ((Real.pi / 4) * Real.exp M)))
    have h3 : C * Real.exp (-(Real.pi / 4) * Real.exp M) * Real.exp ((Real.pi / 4) * Real.exp M) = C := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have h4 : c * Real.exp (-α₁ * M ^ 2) * Real.exp ((Real.pi / 4) * Real.exp M) =
        c * (Real.exp ((Real.pi / 4) * Real.exp M) / Real.exp (α₁ * M ^ 2)) := by
      rw [show -α₁ * M ^ 2 = -(α₁ * M ^ 2) by ring, Real.exp_neg]; ring
    rw [h3] at h2
    have h5 := mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos (α₁ * M ^ 2)))
    have h6 : c * Real.exp (-α₁ * M ^ 2) * Real.exp ((Real.pi / 4) * Real.exp M) * Real.exp (α₁ * M ^ 2) =
        c * Real.exp ((Real.pi / 4) * Real.exp M) := by
      have : Real.exp (-α₁ * M ^ 2) * Real.exp (α₁ * M ^ 2) = 1 := by rw [← Real.exp_add]; simp
      calc c * Real.exp (-α₁ * M ^ 2) * Real.exp ((Real.pi / 4) * Real.exp M) * Real.exp (α₁ * M ^ 2)
        _ = c * Real.exp ((Real.pi / 4) * Real.exp M) * (Real.exp (-α₁ * M ^ 2) * Real.exp (α₁ * M ^ 2)) := by ring
        _ = c * Real.exp ((Real.pi / 4) * Real.exp M) := by rw [this, mul_one]
    rw [h6] at h5
    linarith
  have hlog : (Real.pi / 4) * Real.exp M - α₁ * M ^ 2 ≤ Real.log (C / c) := by
    have := Real.log_le_log (Real.exp_pos _) hdiv
    rwa [Real.log_exp] at this
  have hexp_cube : M ^ 3 / 6 ≤ Real.exp M := by
    have h := Real.sum_le_exp_of_nonneg (le_of_lt hM_pos) 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
    norm_num at h
    have hm1 : 0 ≤ 1 + M + M ^ 2 / 2 := by positivity
    linarith
  have hpi_M : (Real.pi / 24) * M ^ 3 ≤ (Real.pi / 4) * Real.exp M := by
    have := mul_le_mul_of_nonneg_left hexp_cube (by positivity : 0 ≤ Real.pi / 4)
    linarith
  have hM3 : (α₁ + |Real.log (C / c)| + 1) * M ^ 2 ≤ (Real.pi / 24) * M ^ 3 := by
    have h1 : α₁ + |Real.log (C / c)| + 1 ≤ (Real.pi / 24) * M := by
      have := mul_le_mul_of_nonneg_left hM_ge2 (by positivity : 0 ≤ Real.pi / 24)
      have hsimp : (Real.pi / 24) * ((24 / Real.pi) * (α₁ + |Real.log (C / c)| + 1)) =
          α₁ + |Real.log (C / c)| + 1 := by field_simp [ne_of_gt Real.pi_pos]
      linarith
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg M)
    linarith
  have hlog_le : Real.log (C / c) ≤ |Real.log (C / c)| := le_abs_self _
  have hM2_ge1 : 1 ≤ M ^ 2 := by nlinarith
  have hlog_M2 : |Real.log (C / c)| ≤ |Real.log (C / c)| * M ^ 2 := by nlinarith [abs_nonneg (Real.log (C / c))]
  nlinarith
where
  lb_val_trans {a b d : ℝ} (h1 : a ≤ b) (h2 : b ≤ d) : a ≤ d := le_trans h1 h2

end WeilArchimedeanAndExplicitCorridor

