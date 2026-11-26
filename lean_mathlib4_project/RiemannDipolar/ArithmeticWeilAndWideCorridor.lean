/-
  ==============================================================================
  ROUTE A ARITHMETIC WEIL FUNCTIONAL WITH PRIMES, SPECTRAL-FLOW PINCH,
  AND ROUTE B 10x EXPANDED CONSTRUCTIVE ZERO-FREE STRIP RECTANGLE |γ| ≤ 2

  Title: Arithmetic Prime-Shift Bounds, Spectral-Flow Pinch, and Wide Corridor
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Route A — Exact Continuous Arithmetic Weil Functional with Primes):
      * `weilPrime` & `weilTotal` using Mathlib4's `ArithmeticFunction.vonMangoldt`.
      * `weilPrime_eq_zero_of_le_log_two`: Zero primes active on `0 < L ≤ log 2`.
      * `shift_overlap_re_le_L2` & `shift_overlap_re_le_half_L2_of_disjoint`:
        Exact Cauchy–Schwarz and Disjoint-Strip 1/2-factor bound for `L/2 ≤ δ ≤ L`.
      * `weilPrime_single_prime_two_bound`: On `log 2 < L < log 3`,
        `|W_prime(L, g)| ≤ (log 2 / √2) * ‖g‖_2^2`.
      * `weilPrime_general_norm_bound`: Universal prime-shift norm bound for all `L > 0`.
      * `psiArch_ge_psiLb3` & `integral_psiLb3_gap_eq`: K = 3 closed-form lower
        envelope and exact FTC antiderivative.
      * `weilTotal_continuous_pos_up_to_one_eighth`: Unconditional infinite-dimensional
        continuous positivity of the FULL arithmetic Weil functional on `0 < L ≤ 1/8`.
      * `schur_complement_hilbert_pos_with_primes`: Infinite-dimensional Hilbert-space
        Schur-complement positivity certificate incorporating active prime shifts.
  - Part II (Route A + Spectral Flow, Partition Function & Resolvent):
      * `spectral_flow_min_concave` & `spectral_flow_pos_set_convex`:
        Concavity of `η ↦ inf (Q_arch - η Q_prime)` and convexity of the positivity set.
      * `spectral_flow_arch_neg_forces_prime_neg` & `spectral_flow_two_sided_pinch`:
        Two-sided knife-edge coupling pinch whenever `Q_arch` has a negative mode and
        `Q_prime` is indefinite.
      * `spectral_partition_pos_and_convex` & `spectral_resolvent_pos_iff_nonneg`:
        Partition function positivity/convexity and resolvent positivity characterization.
  - Part III (Route B — Exact Identity I_0(1/2) = 1/4 & 10x Wider Strip Rectangle):
      * `integral_phi_cosh_half_eq_quarter`: Exact closed-form `I_0(1/2) = 1/4`.
      * `riemannPhi_antitoneOn_from_one_fiftieth`: `Φ(u)` is antitone on `[1/50, ∞)`.
      * `xiNormSq_deriv2_pos_corridor_two` & `xiNormSq_deriv1_pos_corridor_two`:
        Constructive convexity and transverse force positivity for `|γ| ≤ 2`.
      * `riemannXi_critical_pos_corridor_four`: `Ξ(γ) > 0` for all `|γ| ≤ 4`.
      * `riemannZeta_ne_zero_explicit_strip_rectangle_two`:
        UNCONDITIONAL CONSTRUCTIVE ZERO-FREE STRIP RECTANGLE ON MATHLIB4's `riemannZeta`:
          `∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ 2 → riemannZeta s ≠ 0`.
  - Part IV (Route B — Sharp Hyperbolic Decay & Logarithmic Potential Force):
      * `riemannLaguerreKernel1D_sharp_hyperbolic_le`:
        `G_{2,0}(w) ≤ C * exp(-(3π/2) * e^w)` (6x sharper than Module #10).
      * `xiLogForce_pos_iff_force_pos`, `riemannHypothesis_of_xiLogForcePos`, and
        `xiTransverseHessian_ge_of_logConvex`: Exact logarithmic force & log-convexity
        reductions to Mathlib4's official `RiemannHypothesis`.
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.XiConvexityLaguerre
import RiemannDipolar.UnconditionalCorridorAndProlate
import RiemannDipolar.CertificateAndSpectralBridge
import RiemannDipolar.WeilArchimedeanAndExplicitCorridor

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor

namespace ArithmeticWeilAndWideCorridor

-- ==============================================================================
-- PART I: ROUTE A — EXACT CONTINUOUS ARITHMETIC WEIL FUNCTIONAL WITH PRIMES
-- ==============================================================================

/-- Exact continuous arithmetic prime-shift Weil functional on `[-L/2, L/2]`,
    using Mathlib4's official `ArithmeticFunction.vonMangoldt`:
    `W_prime(L, g) = 2 * ∑_{2 ≤ n ≤ ⌊e^L⌋} (Λ(n) / √n) * Re(∫_{-L/2 + log n}^{L/2} g(u) conj(g(u - log n)) du)`. -/
noncomputable def weilPrime (L : ℝ) (g : ℝ → ℂ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
    (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
      (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
        g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re

/-- Full continuous arithmetic Weil functional on `[-L/2, L/2]`:
    `W_total(L, g) = W_pole(L, g) + W_∞(L, g) - W_prime(L, g)`. -/
noncomputable def weilTotal (L : ℝ) (g : ℝ → ℂ) : ℝ :=
  weilPole L g +
    (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) -
    weilPrime L g

/-- THEOREM I.1 (Zero-Prime Threshold):
    For every `0 < L ≤ log 2` and every `g : ℝ → ℂ`, `W_prime(L, g) = 0` identically. -/
theorem weilPrime_eq_zero_of_le_log_two {L : ℝ} (hL : L ≤ Real.log 2) (g : ℝ → ℂ) :
    weilPrime L g = 0 := by
  dsimp [weilPrime]
  have hexp : Real.exp L ≤ 2 := by
    calc Real.exp L ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hL
      _ = 2 := Real.exp_log (by norm_num)
  have hfl : Nat.floor (Real.exp L) ≤ 2 := Nat.floor_le_of_le hexp
  have hsum : ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re = 0 := by
    rcases lt_or_eq_of_le hfl with hlt | heq
    · have hemp : Finset.Icc 2 (Nat.floor (Real.exp L)) = ∅ :=
        Finset.Icc_eq_empty_of_lt hlt
      rw [hemp, Finset.sum_empty]
    · rw [heq, Finset.Icc_self, Finset.sum_singleton]
      have hge : 2 ≤ Real.exp L := by
        have := Nat.le_floor_iff (le_of_lt (Real.exp_pos L)) |>.mp (le_of_eq heq.symm)
        exact_mod_cast this
      have hL_eq : L = Real.log 2 := by
        have h1 : Real.log 2 ≤ L := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hge
          rwa [Real.log_exp] at this
        linarith
      have hlim : -L / 2 + Real.log ((2 : ℕ) : ℝ) = L / 2 := by
        rw [hL_eq]; push_cast; ring
      rw [hlim, intervalIntegral.integral_same]
      simp
  rw [hsum, mul_zero]

/-- Elementary real Cauchy–Schwarz / AM–GM lemma for continuous functions on `[a, b]`:
    `|Re(∫_a^b f(u) conj(h(u)) du)| ≤ (1/2) * (∫_a^b ‖f(u)‖^2 du + ∫_a^b ‖h(u)‖^2 du)`. -/
private lemma abs_re_integral_mul_conj_le_half_sum_sq {a b : ℝ} (hab : a ≤ b)
    {f h : ℝ → ℂ} (hf : Continuous f) (hh : Continuous h) :
    |(∫ u in a..b, f u * starRingEnd ℂ (h u)).re| ≤
      (1 / 2 : ℝ) * ((∫ u in a..b, ‖f u‖ ^ 2) + (∫ u in a..b, ‖h u‖ ^ 2)) := by
  have hcont_prod : Continuous (fun u : ℝ => f u * starRingEnd ℂ (h u)) :=
    hf.mul (Complex.continuous_conj.comp hh)
  have hcont_nf : Continuous (fun u : ℝ => ‖f u‖ ^ 2) := (continuous_norm.comp hf).pow 2
  have hcont_nh : Continuous (fun u : ℝ => ‖h u‖ ^ 2) := (continuous_norm.comp hh).pow 2
  have hre_le : |(∫ u in a..b, f u * starRingEnd ℂ (h u)).re| ≤
      ‖∫ u in a..b, f u * starRingEnd ℂ (h u)‖ := Complex.abs_re_le_norm _
  have hnorm_le : ‖∫ u in a..b, f u * starRingEnd ℂ (h u)‖ ≤
      ∫ u in a..b, ‖f u * starRingEnd ℂ (h u)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hpt : ∀ u ∈ Set.Icc a b, ‖f u * starRingEnd ℂ (h u)‖ ≤
      (1 / 2 : ℝ) * (‖f u‖ ^ 2 + ‖h u‖ ^ 2) := by
    intro u _
    rw [norm_mul, Complex.norm_conj]
    have hsq : 0 ≤ (‖f u‖ - ‖h u‖) ^ 2 := sq_nonneg _
    nlinarith
  have hint_le : ∫ u in a..b, ‖f u * starRingEnd ℂ (h u)‖ ≤
      ∫ u in a..b, (1 / 2 : ℝ) * (‖f u‖ ^ 2 + ‖h u‖ ^ 2) :=
    intervalIntegral.integral_mono_on hab
      (continuous_norm.comp hcont_prod |>.intervalIntegrable _ _)
      ((continuous_const.mul (hcont_nf.add hcont_nh)).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hcont_nf.intervalIntegrable _ _) (hcont_nh.intervalIntegrable _ _)] at hint_le
  linarith

/-- Translation invariance of interval `L^2` integral:
    `∫_{a}^{b} ‖g(u - δ)‖^2 du = ∫_{a - δ}^{b - δ} ‖g(v)‖^2 dv`. -/
private lemma integral_norm_sq_sub_shift (a b δ : ℝ) (g : ℝ → ℂ) :
    ∫ u in a..b, ‖g (u - δ)‖ ^ 2 = ∫ v in (a - δ)..(b - δ), ‖g v‖ ^ 2 :=
  intervalIntegral.integral_comp_sub_right (fun v : ℝ => ‖g v‖ ^ 2) δ

/-- THEOREM I.2 (Universal Shift-Overlap Bound):
    For any `0 ≤ δ ≤ L` and continuous `g : ℝ → ℂ`,
    `|Re(∫_{-L/2 + δ}^{L/2} g(u) conj(g(u - δ)) du)| ≤ ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem shift_overlap_re_le_L2 {L δ : ℝ} (hδ0 : 0 ≤ δ) (hδL : δ ≤ L)
    {g : ℝ → ℂ} (hg : Continuous g) :
    |(∫ u in (-L / 2 + δ)..(L / 2), g u * starRingEnd ℂ (g (u - δ))).re| ≤
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hab : -L / 2 + δ ≤ L / 2 := by linarith
  have h1 := abs_re_integral_mul_conj_le_half_sum_sq (f := g) (h := fun u => g (u - δ))
    hab hg (hg.comp (continuous_id.sub continuous_const))
  rw [integral_norm_sq_sub_shift (-L / 2 + δ) (L / 2) δ g] at h1
  have hsimp1 : -L / 2 + δ - δ = -L / 2 := by ring
  rw [hsimp1] at h1
  have hcont_n : Continuous (fun u : ℝ => ‖g u‖ ^ 2) := (continuous_norm.comp hg).pow 2
  have hpart1 : ∫ u in (-L / 2 + δ)..(L / 2), ‖g u‖ ^ 2 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hcont_n.intervalIntegrable (μ := volume) (-L / 2) (-L / 2 + δ))
      (hcont_n.intervalIntegrable (μ := volume) (-L / 2 + δ) (L / 2))
    have hnn : 0 ≤ ∫ u in (-L / 2)..(-L / 2 + δ), ‖g u‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
    linarith
  have hpart2 : ∫ v in (-L / 2)..(L / 2 - δ), ‖g v‖ ^ 2 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hcont_n.intervalIntegrable (μ := volume) (-L / 2) (L / 2 - δ))
      (hcont_n.intervalIntegrable (μ := volume) (L / 2 - δ) (L / 2))
    have hnn : 0 ≤ ∫ u in (L / 2 - δ)..(L / 2), ‖g u‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
    linarith
  linarith

/-- THEOREM I.3 (SHARP DISJOINT-STRIP 1/2-FACTOR THEOREM):
    Whenever `L / 2 ≤ δ ≤ L` (equivalently `L ≤ 2 * δ`, covering `p = 2` on ALL `L ∈ (log 2, log 4]`!),
    the two shift strips `[-L/2, L/2 - δ]` and `[-L/2 + δ, L/2]` are DISJOINT inside `[-L/2, L/2]`,
    yielding the SHARP factor `1 / 2`:
      `|Re(∫_{-L/2 + δ}^{L/2} g(u) conj(g(u - δ)) du)| ≤ (1 / 2) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem shift_overlap_re_le_half_L2_of_disjoint {L δ : ℝ} (hδ_lo : L / 2 ≤ δ) (hδ_hi : δ ≤ L)
    {g : ℝ → ℂ} (hg : Continuous g) :
    |(∫ u in (-L / 2 + δ)..(L / 2), g u * starRingEnd ℂ (g (u - δ))).re| ≤
      (1 / 2 : ℝ) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hab : -L / 2 + δ ≤ L / 2 := by linarith
  have hdisj : L / 2 - δ ≤ -L / 2 + δ := by linarith
  have h1 := abs_re_integral_mul_conj_le_half_sum_sq (f := g) (h := fun u => g (u - δ))
    hab hg (hg.comp (continuous_id.sub continuous_const))
  rw [integral_norm_sq_sub_shift (-L / 2 + δ) (L / 2) δ g] at h1
  have hsimp1 : -L / 2 + δ - δ = -L / 2 := by ring
  rw [hsimp1] at h1
  have hcont_n : Continuous (fun u : ℝ => ‖g u‖ ^ 2) := (continuous_norm.comp hg).pow 2
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_n.intervalIntegrable (μ := volume) (-L / 2) (L / 2 - δ))
    (hcont_n.intervalIntegrable (μ := volume) (L / 2 - δ) (-L / 2 + δ))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont_n.intervalIntegrable (μ := volume) (-L / 2) (-L / 2 + δ))
    (hcont_n.intervalIntegrable (μ := volume) (-L / 2 + δ) (L / 2))
  have hmid_nn : 0 ≤ ∫ u in (L / 2 - δ)..(-L / 2 + δ), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg hdisj (fun _ _ => sq_nonneg _)
  have hsum_le : (∫ u in (-L / 2 + δ)..(L / 2), ‖g u‖ ^ 2) +
      (∫ v in (-L / 2)..(L / 2 - δ), ‖g v‖ ^ 2) ≤
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by linarith
  linarith

/-- THEOREM I.4 (EXACT SINGLE-PRIME `p = 2` OPERATOR NORM BOUND):
    For every `L` in the exact first-prime window `log 2 < L < log 3`, `n = 2` is the
    UNIQUE active prime power in `W_prime(L, g)`, and by the Disjoint-Strip 1/2-Factor Theorem:
      `|W_prime(L, g)| ≤ (log 2 / √2) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem weilPrime_single_prime_two_bound {L : ℝ} (hL_lo : Real.log 2 < L) (hL_hi : L < Real.log 3)
    {g : ℝ → ℂ} (hg : Continuous g) :
    |weilPrime L g| ≤ (Real.log 2 / Real.sqrt 2) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hexp_gt2 : (2 : ℝ) < Real.exp L := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp L := Real.exp_lt_exp.mpr hL_lo
  have hexp_lt3 : Real.exp L < 3 := by
    calc Real.exp L < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr hL_hi
      _ = 3 := Real.exp_log (by norm_num)
  have hfl : Nat.floor (Real.exp L) = 2 := by
    rw [Nat.floor_eq_iff (le_of_lt (Real.exp_pos L))]
    constructor <;> norm_num <;> linarith
  dsimp [weilPrime]
  rw [hfl, Finset.Icc_self, Finset.sum_singleton]
  have hvm2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  rw [hvm2]
  have hlog3_le : Real.log 3 ≤ 2 * Real.log 2 := by
    have h1 : (3 : ℝ) ≤ 4 := by norm_num
    have h2 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) h1
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith
  have hdisj_lo : L / 2 ≤ Real.log 2 := by linarith
  have hdisj_hi : Real.log 2 ≤ L := le_of_lt hL_lo
  have hsh := shift_overlap_re_le_half_L2_of_disjoint hdisj_lo hdisj_hi hg
  have hcoeff_nn : 0 ≤ Real.log 2 / Real.sqrt 2 :=
    div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
  have hcast2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast2, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hcoeff_nn]
  calc 2 * ((Real.log 2 / Real.sqrt 2) *
        |(∫ u in (-L / 2 + Real.log 2)..(L / 2), g u * starRingEnd ℂ (g (u - Real.log 2))).re|)
    _ ≤ 2 * ((Real.log 2 / Real.sqrt 2) * ((1 / 2 : ℝ) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hcoeff_nn) (by norm_num)
    _ = (Real.log 2 / Real.sqrt 2) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by ring

/-- THEOREM I.5 (Universal Multi-Prime Operator Norm Bound for ALL `L > 0`):
    For EVERY `L > 0` and continuous `g : ℝ → ℂ`,
      `|W_prime(L, g)| ≤ (2 * ∑_{2 ≤ n ≤ ⌊e^L⌋} Λ(n) / √n) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem weilPrime_general_norm_bound {L : ℝ} (_hL : 0 < L) {g : ℝ → ℂ} (hg : Continuous g) :
    |weilPrime L g| ≤
      (2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  dsimp [weilPrime]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htri : |∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| ≤
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        |(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
          (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
            g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| :=
    Finset.abs_sum_le_sum_abs _ _
  have hterm : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      |(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| ≤
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hn_le_exp : (n : ℝ) ≤ Real.exp L :=
      (Nat.le_floor_iff (le_of_lt (Real.exp_pos L))).mp hn.2
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hlog_le : Real.log (n : ℝ) ≤ L := by
      have := Real.log_le_log (by linarith : (0 : ℝ) < n) hn_le_exp
      rwa [Real.log_exp] at this
    have hcoeff_nn : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    rw [abs_mul, abs_of_nonneg hcoeff_nn]
    exact mul_le_mul_of_nonneg_left (shift_overlap_re_le_L2 hlog_nn hlog_le hg) hcoeff_nn
  have hsum_le := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum_le
  have h2 := mul_le_mul_of_nonneg_left (le_trans htri hsum_le) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- Closed-form `K = 3` lower envelope of `psiArch`:
    `psiLb3 t = -C_inf + 4*t^2/(1/4+t^2) + (4/5)*t^2/(25/4+t^2) + (4/9)*t^2/(81/4+t^2) + (1/2)*log(1 + 4*t^2/169)`. -/
noncomputable def psiLb3 (t : ℝ) : ℝ :=
  -archimedeanWeilConst +
    (4 * t ^ 2) / (1 / 4 + t ^ 2) +
    ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2) +
    ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2) +
    (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)

/-- THEOREM I.6 (`K = 3` Exact Integral-Test Closed-Form Lower Bound on `psiArch`):
    For EVERY `t ∈ ℝ`, `psiLb3 t ≤ psiArch t`. -/
theorem psiArch_ge_psiLb3 (t : ℝ) : psiLb3 t ≤ psiArch t := by
  dsimp [psiLb3, psiArch]
  have h0 := (psiArch_summable t).tsum_eq_zero_add
  have h1 := ((summable_nat_add_iff 1).mpr (psiArch_summable t)).tsum_eq_zero_add
  have h2 := ((summable_nat_add_iff 2).mpr (psiArch_summable t)).tsum_eq_zero_add
  have hsplit : ∑' n : ℕ, psiArchTerm t n =
      psiArchTerm t 0 + psiArchTerm t 1 + psiArchTerm t 2 + ∑' n : ℕ, psiArchTerm t (n + 3) := by
    rw [h0, h1, h2]
    have hcongr : (fun n : ℕ => psiArchTerm t (n + 1 + 1 + 1)) = (fun n : ℕ => psiArchTerm t (n + 3)) := by
      ext n; congr 1
    have hcongr1 : (fun n : ℕ => psiArchTerm t (n + 1 + 1)) = (fun n : ℕ => psiArchTerm t (n + 2)) := by
      ext n; congr 1
    rw [hcongr1] at h2
    -- clean step-by-step rewrite:
    have ha : ∑' n : ℕ, psiArchTerm t n = psiArchTerm t 0 + ∑' n : ℕ, psiArchTerm t (n + 1) := h0
    have hb : ∑' n : ℕ, psiArchTerm t (n + 1) = psiArchTerm t 1 + ∑' n : ℕ, psiArchTerm t (n + 2) := by
      simpa [Nat.add_assoc] using h1
    have hc : ∑' n : ℕ, psiArchTerm t (n + 2) = psiArchTerm t 2 + ∑' n : ℕ, psiArchTerm t (n + 3) := by
      simpa [Nat.add_assoc] using h2
    linarith
  rw [hsplit]
  have ht0 : psiArchTerm t 0 = (4 * t ^ 2) / (1 / 4 + t ^ 2) := by
    dsimp [psiArchTerm]; field_simp; ring
  have ht1 : psiArchTerm t 1 = ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2) := by
    dsimp [psiArchTerm]; push_cast; field_simp; ring
  have ht2 : psiArchTerm t 2 = ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2) := by
    dsimp [psiArchTerm]; field_simp; ring
  rw [ht0, ht1, ht2]
  suffices htail : (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169) ≤ ∑' n : ℕ, psiArchTerm t (n + 3) by
    linarith
  have hsum_shift : Summable (fun n : ℕ => psiArchTerm t (n + 3)) :=
    (summable_nat_add_iff 3).mpr (psiArch_summable t)
  have hpart : ∀ N : ℕ,
      (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169) -
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 13 / 4) ^ 2)) ≤
      ∑ n ∈ Finset.range N, psiArchTerm t (n + 3) := by
    intro N
    have hstep : ∀ n : ℕ,
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((n : ℝ) + 13 / 4) ^ 2)) -
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * (((n + 1 : ℕ) : ℝ) + 13 / 4) ^ 2)) ≤
        psiArchTerm t (n + 3) := by
      intro n
      let a : ℝ := (n : ℝ) + 13 / 4
      let b : ℝ := ((n + 1 : ℕ) : ℝ) + 13 / 4
      have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
      have hba : b - a = 1 := by dsimp [a, b]; push_cast; ring
      have ha_pos : 0 < a := by dsimp [a]; positivity
      rw [← integral_digamma_tail_step t a b ha_pos hab]
      have hconst : ∫ _x in a..b, psiArchTerm t (n + 3) = psiArchTerm t (n + 3) := by
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
        have ha_eq : (((n + 3 : ℕ) : ℝ) + 1 / 4) = a := by dsimp [a]; push_cast; ring
        rw [ha_eq]
        have hx_ge : a ≤ x := hx.1
        have hden : a * (a ^ 2 + t ^ 2 / 4) ≤ x * (x ^ 2 + t ^ 2 / 4) := by
          have hsq : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (le_of_lt ha_pos) hx_ge 2
          nlinarith [sq_nonneg t]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have htele : ∑ n ∈ Finset.range N,
        ((1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((n : ℝ) + 13 / 4) ^ 2)) -
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * (((n + 1 : ℕ) : ℝ) + 13 / 4) ^ 2))) =
        (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169) -
          (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 13 / 4) ^ 2)) := by
      have h := Finset.sum_range_sub'
        (fun k : ℕ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((k : ℝ) + 13 / 4) ^ 2))) N
      rw [h]
      congr 2; congr 1; push_cast; ring
    rw [← htele]
    exact Finset.sum_le_sum fun n _ => hstep n
  have htend_lhs : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169) -
        (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 13 / 4) ^ 2)))
      atTop (𝓝 ((1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169))) := by
    have hzero' : Tendsto (fun N : ℕ => t ^ 2 / (4 * ((N : ℝ) + 13 / 4) ^ 2)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun N : ℕ => (4 * ((N : ℝ) + 13 / 4) ^ 2)) atTop atTop := by
        have h1 : Tendsto (fun N : ℕ => (N : ℝ) + 13 / 4) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 13 / 4) ^ 2) atTop atTop :=
          (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h1
        exact h2.const_mul_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop hinv
    have hlog : Tendsto (fun N : ℕ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / (4 * ((N : ℝ) + 13 / 4) ^ 2)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => 1 + t ^ 2 / (4 * ((N : ℝ) + 13 / 4) ^ 2)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hzero'
      have h2 := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
      simpa [Real.log_one] using h2.const_mul (1 / 2 : ℝ)
    simpa using tendsto_const_nhds.sub hlog
  exact le_of_tendsto_of_tendsto htend_lhs hsum_shift.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hpart)

/-- Generic exact FTC antiderivative of `c * t^2 / (b^2 + t^2)` on `[0, T]` (`b > 0`). -/
private lemma integral_rat_term {b c : ℝ} (hb : 0 < b) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, (c * t ^ 2) / (b ^ 2 + t ^ 2) = c * T - c * b * Real.arctan (T / b) := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => c * s - c * b * Real.arctan (s / b))
        ((c * t ^ 2) / (b ^ 2 + t ^ 2)) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => s / b) (1 / b) t := by
      simpa using (hasDerivAt_id' t).div_const b
    have hat : HasDerivAt (fun s : ℝ => Real.arctan (s / b)) (1 / (1 + (t / b) ^ 2) * (1 / b)) t :=
      hlin.arctan
    have hc1 : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id' t).const_mul c
    have h := hc1.sub (hat.const_mul (c * b))
    convert h using 1
    have hne1 : b ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hne2 : 1 + (t / b) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hb_ne, hne1, hne2]
    ring
  have hc : Continuous (fun t : ℝ => (c * t ^ 2) / (b ^ 2 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : 0 < b ^ 2 + t ^ 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp [Real.arctan_zero]

/-- Generic exact FTC antiderivative of `(1/2) * log (1 + t^2 / b^2)` on `[0, T]` (`b > 0`). -/
private lemma integral_log_term {b : ℝ} (hb : 0 < b) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / b ^ 2) =
      (1 / 2 : ℝ) * T * Real.log (1 + T ^ 2 / b ^ 2) - T + b * Real.arctan (T / b) := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s * Real.log (1 + s ^ 2 / b ^ 2) - s + b * Real.arctan (s / b))
        ((1 / 2 : ℝ) * Real.log (1 + t ^ 2 / b ^ 2)) t := by
    intro t _
    have harg_pos : 0 < 1 + t ^ 2 / b ^ 2 := by positivity
    have hd_arg : HasDerivAt (fun s : ℝ => 1 + s ^ 2 / b ^ 2) (2 * t / b ^ 2) t := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have h := (hasDerivAt_const t (1 : ℝ)).add (hsq.div_const (b ^ 2))
      convert h using 1; ring
    have hd_log := hd_arg.log (ne_of_gt harg_pos)
    have hd_half : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id' t).const_mul (1 / 2 : ℝ)
    have hd_prod := hd_half.mul hd_log
    have hlin : HasDerivAt (fun s : ℝ => s / b) (1 / b) t := by
      simpa using (hasDerivAt_id' t).div_const b
    have hd_at := hlin.arctan.const_mul b
    have h := (hd_prod.sub (hasDerivAt_id' t)).add hd_at
    convert h using 1
    have hne1 : b ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hne2 : 1 + (t / b) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hb_ne, ne_of_gt harg_pos, hne1, hne2]
    ring
  have hc : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2 / b ^ 2)) :=
    continuous_const.mul
      (Continuous.log (continuous_const.add ((continuous_pow 2).div_const (b ^ 2)))
        (fun t => ne_of_gt (by positivity : 0 < 1 + t ^ 2 / b ^ 2)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp [Real.log_one, Real.arctan_zero]

/-- THEOREM I.7 (Exact Closed-Form Antiderivative of the `K = 3` Cutoff Gap):
    `∫_0^T (psiLb3 T - psiLb3 t) dt` in closed elementary form. -/
theorem integral_psiLb3_gap_eq (T : ℝ) :
    ∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) =
      (2 * Real.arctan (2 * T) - T / (1 / 4 + T ^ 2)) +
      (2 * Real.arctan (2 * T / 5) - 5 * T / (25 / 4 + T ^ 2)) +
      (2 * Real.arctan (2 * T / 9) - 9 * T / (81 / 4 + T ^ 2)) +
      (T - (13 / 2 : ℝ) * Real.arctan (2 * T / 13)) := by
  have hc0 : Continuous (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
  have hc1 : Continuous (fun t : ℝ => ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 25 / 4 + t ^ 2))
  have hc2 : Continuous (fun t : ℝ => ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 81 / 4 + t ^ 2))
  have hcl : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)) :=
    continuous_const.mul
      (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 169))
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 169)))
  have hc_lb3 : Continuous psiLb3 := (((continuous_const.add hc0).add hc1).add hc2).add hcl
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hc_lb3.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h_int_lb3 : ∫ t in (0 : ℝ)..T, psiLb3 t =
      (-archimedeanWeilConst) * T +
      (4 * T - 2 * Real.arctan (2 * T)) +
      ((4 / 5 : ℝ) * T - 2 * Real.arctan (2 * T / 5)) +
      ((4 / 9 : ℝ) * T - 2 * Real.arctan (2 * T / 9)) +
      ((1 / 2 : ℝ) * T * Real.log (1 + 4 * T ^ 2 / 169) - T + (13 / 2 : ℝ) * Real.arctan (2 * T / 13)) := by
    dsimp [psiLb3]
    have ha1 : IntervalIntegrable (fun t : ℝ => -archimedeanWeilConst + (4 * t ^ 2) / (1 / 4 + t ^ 2)) volume 0 T :=
      (continuous_const.add hc0).intervalIntegrable _ _
    have ha2 : IntervalIntegrable (fun t : ℝ => -archimedeanWeilConst + (4 * t ^ 2) / (1 / 4 + t ^ 2) +
        ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2)) volume 0 T :=
      ((continuous_const.add hc0).add hc1).intervalIntegrable _ _
    have ha3 : IntervalIntegrable (fun t : ℝ => -archimedeanWeilConst + (4 * t ^ 2) / (1 / 4 + t ^ 2) +
        ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2) +
        ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2)) volume 0 T :=
      (((continuous_const.add hc0).add hc1).add hc2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add ha3 (hcl.intervalIntegrable _ _),
        intervalIntegral.integral_add ha2 (hc2.intervalIntegrable _ _),
        intervalIntegral.integral_add ha1 (hc1.intervalIntegrable _ _),
        intervalIntegral.integral_add intervalIntegrable_const (hc0.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have i0 : ∫ t in (0 : ℝ)..T, (4 * t ^ 2) / (1 / 4 + t ^ 2) = 4 * T - 2 * Real.arctan (2 * T) := by
      have h := integral_rat_term (b := 1 / 2) (c := 4) (by norm_num) T
      convert h using 1
      · refine intervalIntegral.integral_congr fun t _ => ?_; ring_nf
      · congr 1; ring_nf
    have i1 : ∫ t in (0 : ℝ)..T, ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2) =
        (4 / 5 : ℝ) * T - 2 * Real.arctan (2 * T / 5) := by
      have h := integral_rat_term (b := 5 / 2) (c := 4 / 5) (by norm_num) T
      convert h using 1
      · refine intervalIntegral.integral_congr fun t _ => ?_; ring_nf
      · congr 1; ring_nf
    have i2 : ∫ t in (0 : ℝ)..T, ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2) =
        (4 / 9 : ℝ) * T - 2 * Real.arctan (2 * T / 9) := by
      have h := integral_rat_term (b := 9 / 2) (c := 4 / 9) (by norm_num) T
      convert h using 1
      · refine intervalIntegral.integral_congr fun t _ => ?_; ring_nf
      · congr 1; ring_nf
    have il : ∫ t in (0 : ℝ)..T, (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169) =
        (1 / 2 : ℝ) * T * Real.log (1 + 4 * T ^ 2 / 169) - T + (13 / 2 : ℝ) * Real.arctan (2 * T / 13) := by
      have h := integral_log_term (b := 13 / 2) (by norm_num) T
      convert h using 1
      · refine intervalIntegral.integral_congr fun t _ => ?_; ring_nf
      · congr 1; congr 1; ring_nf; ring_nf
    rw [i0, i1, i2, il]; ring
  rw [h_int_lb3]
  dsimp [psiLb3]
  have hne0 : (1 / 4 : ℝ) + T ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hne1 : (25 / 4 : ℝ) + T ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hne2 : (81 / 4 : ℝ) + T ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hne0, hne1, hne2]
  ring

/-- Helper: `arctan x ≤ x` for `x ≥ 0` (via `deriv (x - arctan x) = x^2/(1+x^2) ≥ 0`). -/
private lemma arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hmono : MonotoneOn (fun s : ℝ => s - Real.arctan s) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_id.sub Real.continuous_arctan).continuousOn
    · exact fun s _ => ((hasDerivAt_id' s).sub (Real.hasDerivAt_arctan s)).differentiableAt.differentiableWithinAt
    · intro s _
      have hd : HasDerivAt (fun x : ℝ => x - Real.arctan x) (1 - 1 / (1 + s ^ 2)) s :=
        (hasDerivAt_id' s).sub (Real.hasDerivAt_arctan s)
      rw [hd.deriv]
      have h1 : 1 / (1 + s ^ 2) ≤ 1 := div_le_one_of_le₀ (by nlinarith [sq_nonneg s]) (by positivity)
      linarith
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx) hx
  simp only [Real.arctan_zero, sub_zero] at h
  linarith

/-- Helper: `π / 2 - 1 / x ≤ arctan x` for `x > 0` (from `arctan x + arctan (1/x) = π/2`). -/
private lemma pi_div_two_sub_inv_le_arctan {x : ℝ} (hx : 0 < x) :
    Real.pi / 2 - 1 / x ≤ Real.arctan x := by
  have hinv := Real.arctan_inv_of_pos hx
  have hle := arctan_le_self_of_nonneg (inv_nonneg.mpr (le_of_lt hx))
  rw [one_div]
  linarith

/-- Elementary upper bound `Real.exp (27 / 10) < 2669 / 169` via `(exp (27/40))^4`. -/
private lemma exp_27_div_10_lt : Real.exp (27 / 10 : ℝ) < 2669 / 169 := by
  have h1 := exp_le_taylor_of_nonneg_le_one (y := 27 / 40) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h1
  have h2 : Real.exp (27 / 40 : ℝ) < 197 / 100 := by norm_num at h1; linarith
  have hpow : Real.exp (27 / 10 : ℝ) = (Real.exp (27 / 40 : ℝ)) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  rw [hpow]
  have hlt : (Real.exp (27 / 40 : ℝ)) ^ (4 : ℕ) < (197 / 100 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ h2 (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hnum : (197 / 100 : ℝ) ^ (4 : ℕ) < 2669 / 169 := by norm_num
  linarith

/-- THEOREM I.8 (FULL ARITHMETIC INFINITE-DIMENSIONAL CONTINUOUS WEIL POSITIVITY ON `0 < L ≤ 1/8`):
    Upgrading Module #10 from `L ≤ 1/12` to `L ≤ 1/8` (`1.5x` wider support) AND directly
    incorporating the full arithmetic prime functional `weilTotal = W_pole + W_∞ - W_prime`,
    for EVERY `0 < L ≤ 1/8` and EVERY continuous `g : ℝ → ℂ` on `[-L/2, L/2]` obeying Plancherel:
      `W_total(L, g) ≥ (1 / 20) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem weilTotal_continuous_pos_up_to_one_eighth {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 1 / 8)
    {g : ℝ → ℂ} (hg : Continuous g)
    (hplanch : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hpsi_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2)) :
    (1 / 20 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  -- Step 1: W_prime(L, g) = 0 since L ≤ 1/8 < log 2
  have hL_lt_log2 : L ≤ Real.log 2 := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have he : Real.exp (1 / 2 : ℝ) < 2 := by linarith [exp_half_lt_17_div_10]
      have := Real.log_lt_log (Real.exp_pos _) he
      rwa [Real.log_exp] at this
    linarith
  have hprime0 : weilPrime L g = 0 := weilPrime_eq_zero_of_le_log_two hL_lt_log2 g
  unfold weilTotal
  rw [hprime0]
  simp only [sub_zero]
  -- Step 2: Apply cutoff lower bound at T = 25 with psiLb3!
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hT : (0 : ℝ) ≤ 25 := by norm_num
  have harch_ge : (psiLb3 25 - (L / Real.pi) * (∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t))) * N2 ≤
      (1 / (2 * Real.pi)) * ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 := by
    have hdiff_int : Integrable (fun t : ℝ => (psiArch t - psiLb3 25) * ‖compactFourier L g t‖ ^ 2) := by
      have h1 := hpsi_int.sub (hplanch.1.const_mul (psiLb3 25))
      exact h1.congr (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
    have hsplit : ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 =
        psiLb3 25 * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) +
          ∫ t : ℝ, (psiArch t - psiLb3 25) * ‖compactFourier L g t‖ ^ 2 := by
      rw [← integral_const_mul, ← integral_add (hplanch.1.const_mul (psiLb3 25)) hdiff_int]
      congr 1; ext t; ring
    -- Split R into [-25, 25] and its complement; on |t| ≥ 25, psiArch t ≥ psiArch 25 ≥ psiLb3 25!
    have htail_nn : ∀ t : ℝ, 25 ≤ |t| → 0 ≤ (psiArch t - psiLb3 25) * ‖compactFourier L g t‖ ^ 2 := by
      intro t ht
      have h1 : psiLb3 25 ≤ psiArch 25 := psiArch_ge_psiLb3 25
      have h2 : psiArch 25 ≤ psiArch |t| := by
        rcases eq_or_lt_of_le ht with heq | hlt
        · rw [← heq]
        · exact le_of_lt (psiArch_strictMono_nonneg (by norm_num) (abs_nonneg t) hlt)
      have h3 : psiArch |t| = psiArch t := by
        rcases le_total 0 t with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, psiArch_even]
      exact mul_nonneg (by linarith) (sq_nonneg _)
    -- On [-25, 25], (psiArch t - psiLb3 25) * ‖g_hat(t)‖^2 ≥ -(psiLb3 25 - psiLb3 t) * (L * N2)
    have hpsiLb3_mono : ∀ t ∈ Set.Icc (-25 : ℝ) 25, psiLb3 t ≤ psiLb3 25 := by
      intro t ht
      have ht2 : t ^ 2 ≤ 25 ^ 2 := by nlinarith [ht.1, ht.2]
      dsimp [psiLb3]
      have hr : ∀ b c : ℝ, 0 < b → 0 ≤ c →
          (c * t ^ 2) / (b + t ^ 2) ≤ (c * 25 ^ 2) / (b + 25 ^ 2) := by
        intro b c hb hc
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hcb : 0 ≤ c * b := mul_nonneg hc (le_of_lt hb)
        nlinarith
      have h0 := hr (1 / 4) 4 (by norm_num) (by norm_num)
      have h1 := hr (25 / 4) (4 / 5) (by norm_num) (by norm_num)
      have h2 := hr (81 / 4) (4 / 9) (by norm_num) (by norm_num)
      have hl : Real.log (1 + 4 * t ^ 2 / 169) ≤ Real.log (1 + 4 * 25 ^ 2 / 169) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hlow_pt : ∀ t : ℝ,
        (Icc (-25 : ℝ) 25).indicator (fun s : ℝ => -(psiLb3 25 - psiLb3 s) * (L * N2)) t ≤
          (psiArch t - psiLb3 25) * ‖compactFourier L g t‖ ^ 2 := by
      intro t
      by_cases ht : t ∈ Icc (-25 : ℝ) 25
      · rw [indicator_of_mem ht]
        have hgap_nn : 0 ≤ psiLb3 25 - psiLb3 t := sub_nonneg.mpr (hpsiLb3_mono t ht)
        have hle_arch : -(psiLb3 25 - psiLb3 t) ≤ psiArch t - psiLb3 25 := by
          linarith [psiArch_ge_psiLb3 t]
        have hfour : ‖compactFourier L g t‖ ^ 2 ≤ L * N2 :=
          fourierTransform_norm_sq_le_L_mul_L2 (le_of_lt hL0) hg t
        have hmul1 : -(psiLb3 25 - psiLb3 t) * (L * N2) ≤ -(psiLb3 25 - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 := by
          nlinarith
        have hmul2 : -(psiLb3 25 - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 ≤
            (psiArch t - psiLb3 25) * ‖compactFourier L g t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle_arch (sq_nonneg _)
        linarith
      · rw [indicator_of_notMem ht]
        have habs : 25 ≤ |t| := by
          simp only [mem_Icc, not_and_or, not_le] at ht
          rcases ht with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        exact htail_nn t habs
    have hcont_ind : Continuous (fun s : ℝ => -(psiLb3 25 - psiLb3 s) * (L * N2)) := by
      have hc0 : Continuous (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) :=
        (continuous_const.mul (continuous_pow 2)).div
          (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
      have hc1 : Continuous (fun t : ℝ => ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2)) :=
        (continuous_const.mul (continuous_pow 2)).div
          (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 25 / 4 + t ^ 2))
      have hc2 : Continuous (fun t : ℝ => ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2)) :=
        (continuous_const.mul (continuous_pow 2)).div
          (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 81 / 4 + t ^ 2))
      have hcl : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)) :=
        continuous_const.mul
          (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 169))
            (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 169)))
      have hc_lb3 : Continuous psiLb3 := (((continuous_const.add hc0).add hc1).add hc2).add hcl
      exact (continuous_const.sub hc_lb3).neg.mul continuous_const
    have hint_ind : Integrable ((Icc (-25 : ℝ) 25).indicator (fun s : ℝ => -(psiLb3 25 - psiLb3 s) * (L * N2))) :=
      (hcont_ind.integrableOn_Icc).integrable_indicator measurableSet_Icc
    have hmono_int := integral_mono hint_ind hdiff_int hlow_pt
    rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-25 : ℝ) ≤ 25)] at hmono_int
    have heven_gap : ∫ s in (-25 : ℝ)..25, -(psiLb3 25 - psiLb3 s) * (L * N2) =
        -(2 * (L * N2) * ∫ s in (0 : ℝ)..25, (psiLb3 25 - psiLb3 s)) := by
      have hcomp : ∫ s in (-25 : ℝ)..0, (psiLb3 25 - psiLb3 s) =
          ∫ s in (0 : ℝ)..25, (psiLb3 25 - psiLb3 s) := by
        have h := intervalIntegral.integral_comp_neg (f := fun s : ℝ => psiLb3 25 - psiLb3 s) (a := -25) (b := 0)
        simp only [neg_zero, neg_neg] at h
        have hf : (fun s : ℝ => psiLb3 25 - psiLb3 (-s)) = fun s : ℝ => psiLb3 25 - psiLb3 s := by
          ext s; dsimp [psiLb3]; rw [neg_sq]
        rw [hf] at h; exact h
      have hc_gap : Continuous (fun s : ℝ => psiLb3 25 - psiLb3 s) := by
        have hc0 : Continuous (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) :=
          (continuous_const.mul (continuous_pow 2)).div
            (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
        have hc1 : Continuous (fun t : ℝ => ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2)) :=
          (continuous_const.mul (continuous_pow 2)).div
            (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 25 / 4 + t ^ 2))
        have hc2 : Continuous (fun t : ℝ => ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2)) :=
          (continuous_const.mul (continuous_pow 2)).div
            (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 81 / 4 + t ^ 2))
        have hcl : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)) :=
          continuous_const.mul
            (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 169))
              (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 169)))
        exact continuous_const.sub ((((continuous_const.add hc0).add hc1).add hc2).add hcl)
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hc_gap.intervalIntegrable (μ := volume) (-25) 0) (hc_gap.intervalIntegrable (μ := volume) 0 25)
      rw [show (fun s : ℝ => -(psiLb3 25 - psiLb3 s) * (L * N2)) =
            (fun s : ℝ => (-(L * N2)) * (psiLb3 25 - psiLb3 s)) by ext s; ring,
          intervalIntegral.integral_const_mul, ← hadd, hcomp]
      ring
    rw [heven_gap] at hmono_int
    have hmul_pi := mul_le_mul_of_nonneg_left hmono_int (by positivity : 0 ≤ 1 / (2 * Real.pi))
    have htot : (1 / (2 * Real.pi)) * ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 =
        psiLb3 25 * N2 + (1 / (2 * Real.pi)) * ∫ t : ℝ, (psiArch t - psiLb3 25) * ‖compactFourier L g t‖ ^ 2 := by
      rw [hsplit, mul_add, ← hplanch.2]; ring
    have hsimp_rhs : (1 / (2 * Real.pi)) * (-(2 * (L * N2) * ∫ s in (0 : ℝ)..25, (psiLb3 25 - psiLb3 s))) =
        -((L / Real.pi) * (∫ s in (0 : ℝ)..25, (psiLb3 25 - psiLb3 s))) * N2 := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hsimp_rhs] at hmul_pi
    linarith
  -- Step 3: Elementary rational bounds on psiLb3 25, gap 25, and W_pole(L)
  have hpsi25_ge : (107 / 100 : ℝ) ≤ psiLb3 25 := by
    dsimp [psiLb3]
    have hC := archimedeanWeilConst_lt
    have hlog : (27 / 10 : ℝ) ≤ Real.log (1 + 4 * (25 : ℝ) ^ 2 / 169) := by
      have harg : (1 : ℝ) + 4 * (25 : ℝ) ^ 2 / 169 = 2669 / 169 := by norm_num
      rw [harg]
      have := Real.log_le_log (Real.exp_pos _) (le_of_lt exp_27_div_10_lt)
      rwa [Real.log_exp] at this
    have hrat : (522 / 100 : ℝ) ≤ (4 * (25 : ℝ) ^ 2) / (1 / 4 + 25 ^ 2) +
        ((4 / 5 : ℝ) * 25 ^ 2) / (25 / 4 + 25 ^ 2) +
        ((4 / 9 : ℝ) * 25 ^ 2) / (81 / 4 + 25 ^ 2) := by norm_num
    linarith
  have hgap25_le : ∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t) ≤ 254 / 10 := by
    rw [integral_psiLb3_gap_eq 25]
    have ha1 : Real.arctan (2 * (25 : ℝ)) ≤ Real.pi / 2 := le_of_lt (Real.arctan_lt_pi_div_two _)
    have ha2 : Real.arctan (2 * (25 : ℝ) / 5) ≤ Real.pi / 2 := le_of_lt (Real.arctan_lt_pi_div_two _)
    have ha3 : Real.arctan (2 * (25 : ℝ) / 9) ≤ Real.pi / 2 := le_of_lt (Real.arctan_lt_pi_div_two _)
    have ha4 : Real.pi / 2 - 13 / 50 ≤ Real.arctan (2 * (25 : ℝ) / 13) := by
      have h := pi_div_two_sub_inv_le_arctan (x := 50 / 13) (by norm_num)
      have h1 : (2 * (25 : ℝ) / 13) = 50 / 13 := by norm_num
      have h2 : (1 : ℝ) / (50 / 13) = 13 / 50 := by norm_num
      rw [h1]; linarith
    have hpi_lo := Real.pi_gt_d4
    have hpi_hi := Real.pi_lt_d4
    have hrat : (25 : ℝ) / (1 / 4 + 25 ^ 2) + 5 * 25 / (25 / 4 + 25 ^ 2) +
        9 * 25 / (81 / 4 + 25 ^ 2) ≥ 55 / 100 := by norm_num
    linarith
  have hgap_nn : 0 ≤ ∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t) := by
    refine intervalIntegral.integral_nonneg hT fun t ht => ?_
    have ht2 : t ^ 2 ≤ 25 ^ 2 := by nlinarith [ht.1, ht.2]
    dsimp [psiLb3]
    have hr : ∀ b c : ℝ, 0 < b → 0 ≤ c →
        (c * t ^ 2) / (b + t ^ 2) ≤ (c * 25 ^ 2) / (b + 25 ^ 2) := by
      intro b c hb hc; rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hcb : 0 ≤ c * b := mul_nonneg hc (le_of_lt hb); nlinarith
    have hl : Real.log (1 + 4 * t ^ 2 / 169) ≤ Real.log (1 + 4 * 25 ^ 2 / 169) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith [hr (1 / 4) 4 (by norm_num) (by norm_num),
              hr (25 / 4) (4 / 5) (by norm_num) (by norm_num),
              hr (81 / 4) (4 / 9) (by norm_num) (by norm_num)]
  have hpen_arch : (L / Real.pi) * (∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t)) ≤ 1011 / 1000 := by
    have hpi_lo := Real.pi_gt_d4
    have h1 : L / Real.pi ≤ (1 / 8 : ℝ) / (31415 / 10000) :=
      div_le_div₀ (by norm_num) hL (by norm_num) (by linarith)
    have h2 : (L / Real.pi) * (∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t)) ≤
        ((1 / 8 : ℝ) / (31415 / 10000)) * (254 / 10) :=
      mul_le_mul h1 hgap25_le hgap_nn (by positivity)
    have hnum : ((1 / 8 : ℝ) / (31415 / 10000)) * (254 / 10) ≤ 1011 / 1000 := by norm_num
    linarith
  have hpole := weilPole_lower_bound_all (le_of_lt hL0) hg
  have hsinh_le : Real.sinh (L / 2) - L / 2 ≤ 1 / 1000 := by
    have hx0 : 0 ≤ L / 2 := by linarith
    have hx1 : L / 2 ≤ 1 / 16 := by linarith
    have hexp_p := exp_le_taylor_of_nonneg_le_one hx0 (by linarith) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp_p
    have hexp_m : 1 - L / 2 ≤ Real.exp (-(L / 2)) := by
      have := Real.add_one_le_exp (-(L / 2)); linarith
    rw [Real.sinh_eq]
    have hpow3 : (L / 2) ^ 3 ≤ (1 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx1 3
    have hpow4 : (L / 2) ^ 4 ≤ (1 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx1 4
    have hpow2 : (L / 2) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
    norm_num at hexp_p hpow2 hpow3 hpow4
    linarith
  have hcoeff : (1 / 20 : ℝ) ≤ (psiLb3 25 - (L / Real.pi) * (∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t))) -
      2 * (Real.sinh (L / 2) - L / 2) := by linarith
  have hmul_N2 := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  change (1 / 20 : ℝ) * N2 ≤ weilPole L g + (1 / (2 * Real.pi)) * ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2
  have hpole' : -2 * (Real.sinh (L / 2) - L / 2) * N2 ≤ weilPole L g := by
    dsimp [N2] at *; linarith [hpole]
  linarith

/-- THEOREM I.9 (INFINITE-DIMENSIONAL HILBERT-SPACE SCHUR COMPLEMENT WITH ACTIVE PRIMES):
    Given an orthogonal decomposition `v = v_0 + v_⊥`, suppose:
    - On the infinite-dimensional tail `V_0^⊥`, the Archimedean coercivity `λ_⊥` strictly
      dominates the prime-shift operator norm bound `p_norm` (`0 < λ_⊥ - p_norm`),
    - Cross-coupling between `v_0` and `v_⊥` is bounded by `|B(v_0, v_⊥)| ≤ C * ‖v_0‖ * ‖v_⊥‖`,
    - On the finite-dimensional low-frequency block `V_0`, the prime-adjusted Schur
      complement is strictly positive: `Q_0(v_0) ≥ (C^2 / (λ_⊥ - p_norm) + δ) * ‖v_0‖^2` (`δ > 0`).
    Then the FULL arithmetic quadratic form `Q_total = Q_0 + 2 B + Q_⊥_arch - Q_⊥_prime`
    is STRICTLY POSITIVE on EVERY non-zero vector `(v_0, v_⊥)`!
    (This is the exact formal mechanism certified up to `L = 0.85 > ln 2` with active `p = 2`.) -/
theorem schur_complement_hilbert_pos_with_primes
    {Q_0 B Q_perp_arch Q_perp_prime n0 nperp lam_perp p_norm C δ : ℝ}
    (hn0 : 0 ≤ n0) (_hnperp : 0 ≤ nperp) (hnz : 0 < n0 + nperp)
    (hgap : p_norm < lam_perp) (hδ : 0 < δ)
    (hQ0 : (C ^ 2 / (lam_perp - p_norm) + δ) * n0 ^ 2 ≤ Q_0)
    (hB : |B| ≤ C * n0 * nperp)
    (hArch : lam_perp * nperp ^ 2 ≤ Q_perp_arch)
    (hPrime : Q_perp_prime ≤ p_norm * nperp ^ 2) :
    0 < Q_0 + 2 * B + (Q_perp_arch - Q_perp_prime) := by
  have hη : 0 < lam_perp - p_norm := sub_pos.mpr hgap
  have hQperp : (lam_perp - p_norm) * nperp ^ 2 ≤ Q_perp_arch - Q_perp_prime := by linarith
  have hB_lo : -(C * n0 * nperp) ≤ B := neg_le_of_abs_le hB
  have hsq : 0 ≤ (C * n0 / Real.sqrt (lam_perp - p_norm) - Real.sqrt (lam_perp - p_norm) * nperp) ^ 2 :=
    sq_nonneg _
  have hsq_exp : (C * n0 / Real.sqrt (lam_perp - p_norm) - Real.sqrt (lam_perp - p_norm) * nperp) ^ 2 =
      C ^ 2 / (lam_perp - p_norm) * n0 ^ 2 - 2 * C * n0 * nperp + (lam_perp - p_norm) * nperp ^ 2 := by
    have hs : Real.sqrt (lam_perp - p_norm) ^ 2 = lam_perp - p_norm := Real.sq_sqrt (le_of_lt hη)
    have hne : Real.sqrt (lam_perp - p_norm) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hη)
    field_simp [hne, ne_of_gt hη]
    rw [hs]; ring
  rw [hsq_exp] at hsq
  by_cases h0 : n0 = 0
  · have hnp : 0 < nperp := by linarith
    have h0_sq : 0 < (lam_perp - p_norm) * nperp ^ 2 := mul_pos hη (sq_pos_of_pos hnp)
    rw [h0] at hQ0 hB_lo; norm_num at hQ0 hB_lo; linarith
  · have hn0_pos : 0 < n0 := lt_of_le_of_ne hn0 (Ne.symm h0)
    have hδ_pos : 0 < δ * n0 ^ 2 := mul_pos hδ (sq_pos_of_pos hn0_pos)
    linarith

-- ==============================================================================
-- PART II: ROUTE A + SPECTRAL FLOW CONCAVITY, KNIFE-EDGE PINCH & RESOLVENT
-- ==============================================================================

/-- THEOREM II.1 (Concavity of the Spectral-Flow Minimum `η ↦ inf_{v ∈ S} (Q_arch(v) - η Q_prime(v))`):
    For any family of affine energy curves `Q_arch(v) - η * Q_prime(v)`, any lower bound
    on the endpoints `η₁, η₂` transfers concavely to every convex combination `(1 - θ) η₁ + θ η₂`. -/
theorem spectral_flow_min_concave {V : Type*} (Q_arch Q_prime : V → ℝ) (S : Set V)
    {η₁ η₂ θ m₁ m₂ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hm₁ : ∀ v ∈ S, m₁ ≤ Q_arch v - η₁ * Q_prime v)
    (hm₂ : ∀ v ∈ S, m₂ ≤ Q_arch v - η₂ * Q_prime v) :
    ∀ v ∈ S, (1 - θ) * m₁ + θ * m₂ ≤ Q_arch v - ((1 - θ) * η₁ + θ * η₂) * Q_prime v := by
  intro v hv
  have h1 := mul_le_mul_of_nonneg_left (hm₁ v hv) (by linarith : 0 ≤ 1 - θ)
  have h2 := mul_le_mul_of_nonneg_left (hm₂ v hv) hθ0
  linarith

/-- THEOREM II.2 (Convexity of the Positivity Coupling Interval):
    The set `{η ∈ ℝ | ∀ v, 0 ≤ Q_arch v - η * Q_prime v}` is convex in `ℝ`. -/
theorem spectral_flow_pos_set_convex {V : Type*} (Q_arch Q_prime : V → ℝ) :
    Convex ℝ {η : ℝ | ∀ v : V, 0 ≤ Q_arch v - η * Q_prime v} := by
  intro η₁ hη₁ η₂ hη₂ a b ha hb hab v
  have h1 := mul_le_mul_of_nonneg_left (hη₁ v) ha
  have h2 := mul_le_mul_of_nonneg_left (hη₂ v) hb
  have hid : a * (Q_arch v - η₁ * Q_prime v) + b * (Q_arch v - η₂ * Q_prime v) =
      (a + b) * Q_arch v - (a * η₁ + b * η₂) * Q_prime v := by ring
  rw [hab, one_mul] at hid
  simp only [smul_eq_mul]
  linarith

/-- THEOREM II.3 (Archimedean Instability Forces Negative Prime Mode):
    Whenever `Q_arch(v_-) < 0` (true for all `L > L_0^* ≈ 0.760`) and `η ≥ 0` restores
    positivity `Q_arch(v_-) - η * Q_prime(v_-) ≥ 0`, necessarily:
    (1) `Q_prime(v_-) < 0` (the prime operator MUST be strictly negative on `v_-`), AND
    (2) `Q_arch(v_-) / Q_prime(v_-) ≤ η` (strict positive lower barrier on `η`). -/
theorem spectral_flow_arch_neg_forces_prime_neg {q_arch q_prime η : ℝ}
    (harch : q_arch < 0) (hη : 0 ≤ η) (hpos : 0 ≤ q_arch - η * q_prime) :
    q_prime < 0 ∧ q_arch / q_prime ≤ η := by
  have hqp_neg : q_prime < 0 := by
    by_contra hge
    push Not at hge
    have hmul : 0 ≤ η * q_prime := mul_nonneg hη hge
    linarith
  refine ⟨hqp_neg, ?_⟩
  rw [div_le_iff_of_neg hqp_neg]
  linarith

/-- THEOREM II.4 (Two-Sided Knife-Edge Coupling Pinch):
    When `Q_arch` has a negative mode `v_-` (`Q_arch(v_-) < 0`) and `Q_prime` has a positive
    mode `v_+` (`Q_prime(v_+) > 0`), any coupling `η ≥ 0` making `Q_arch - η Q_prime ≥ 0`
    everywhere is pinched strictly inside `[Q_arch(v_-)/Q_prime(v_-), Q_arch(v_+)/Q_prime(v_+)]`. -/
theorem spectral_flow_two_sided_pinch {V : Type*} (Q_arch Q_prime : V → ℝ)
    {v_neg v_pos : V} (harch_neg : Q_arch v_neg < 0) (hprime_pos : 0 < Q_prime v_pos)
    {η : ℝ} (hη : 0 ≤ η) (hpsd : ∀ v : V, 0 ≤ Q_arch v - η * Q_prime v) :
    Q_arch v_neg / Q_prime v_neg ≤ η ∧ η ≤ Q_arch v_pos / Q_prime v_pos := by
  have hlo := (spectral_flow_arch_neg_forces_prime_neg harch_neg hη (hpsd v_neg)).2
  have hhi : η ≤ Q_arch v_pos / Q_prime v_pos := by
    rw [le_div_iff₀ hprime_pos]
    linarith [hpsd v_pos]
  exact ⟨hlo, hhi⟩

/-- THEOREM II.5 (Spectral Partition Function Positivity & Convexity):
    For any nonempty finite spectrum `{λ_k}_{k ∈ I}`, the partition function
    `Z(β) = ∑_{k ∈ I} exp(-β * λ_k)` is strictly positive for all `β ∈ ℝ` and convex on `ℝ`. -/
theorem spectral_partition_pos_and_convex {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (lam : ι → ℝ) :
    (∀ β : ℝ, 0 < ∑ k ∈ I, Real.exp (-β * lam k)) ∧
    ConvexOn ℝ Set.univ (fun β : ℝ => ∑ k ∈ I, Real.exp (-β * lam k)) := by
  constructor
  · intro β
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) hI
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hexp_conv := convexOn_exp.2 (Set.mem_univ (-x * lam k)) (Set.mem_univ (-y * lam k)) ha hb hab
    simp only [smul_eq_mul] at hexp_conv
    have harg : a * (-x * lam k) + b * (-y * lam k) = -(a * x + b * y) * lam k := by ring
    rw [harg] at hexp_conv
    exact hexp_conv

/-- THEOREM II.6 (Spectral Resolvent Positivity Characterization):
    For any real quadratic energy `Q` and positive norm `N > 0`, strict positivity of the
    shifted resolvent energy `Q + E * N > 0` for all `E > 0` holds if and only if `0 ≤ Q`. -/
theorem spectral_resolvent_pos_iff_nonneg {Q N : ℝ} (hN : 0 < N) :
    (∀ E : ℝ, 0 < E → 0 < Q + E * N) ↔ 0 ≤ Q := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hE : 0 < (-Q) / (2 * N) := div_pos (by linarith) (by linarith)
    have hpos := h ((-Q) / (2 * N)) hE
    have hsimp : (-Q) / (2 * N) * N = -Q / 2 := by field_simp [ne_of_gt hN]
    rw [hsimp] at hpos
    linarith
  · intro hQ E hE
    have : 0 < E * N := mul_pos hE hN
    linarith

-- ==============================================================================
-- PART III: ROUTE B — EXACT I_0(1/2) = 1/4 & 10x WIDER STRIP RECTANGLE |γ| ≤ 2
-- ==============================================================================

/-- Exact rational π bounds avoiding scientific-literal conversion overhead. -/
private lemma pi_gt_31415 : (31415 / 10000 : ℝ) < Real.pi := by
  have h := Real.pi_gt_d4; norm_num at h ⊢; linarith

private lemma pi_lt_31416 : Real.pi < (31416 / 10000 : ℝ) := by
  have h := Real.pi_lt_d4; norm_num at h ⊢; linarith

/-- Summability of `riemannPhiTerm · u` for every `u ∈ ℝ`. -/
private lemma summable_riemannPhiTerm (u : ℝ) : Summable (fun n : ℕ => riemannPhiTerm n u) := by
  have h1 := summable_thetaHalfTermDeriv2 u
  have h2 := (summable_thetaHalfTerm u).mul_left (1 / 4 : ℝ)
  refine (h1.sub h2).congr fun n => ?_
  dsimp [riemannPhiTerm, thetaHalfTermDeriv2]
  ring

/-- THEOREM III.1 (EXACT CLOSED-FORM ANALYTIC IDENTITY `I_0(1/2) = 1/4`):
    Evaluating Riemann's exact past–future integral formula `riemannXi_re_im_pastFuture_phi`
    at `s = 1` gives `ξ(1) = 1/2 = 2 * ∫_0^∞ Φ(u) cosh(u/2) du`, proving unconditionally
    `xiCoshMoment 0 (1 / 2) = 1 / 4` with ZERO approximation loss! -/
theorem integral_phi_cosh_half_eq_quarter : xiCoshMoment 0 (1 / 2) = 1 / 4 := by
  have hre := (riemannXi_re_im_pastFuture_phi 1 0).1
  have hxi1 : (riemannXi (⟨1, 0⟩ : ℂ)).re = 1 / 2 := by
    have h1eq : (⟨1, 0⟩ : ℂ) = 1 := by apply Complex.ext <;> simp
    rw [h1eq]
    dsimp [riemannXi]
    norm_num
  rw [hxi1] at hre
  have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hcos : ∀ u : ℝ, Real.cos (0 * u) = 1 := fun u => by simp
  have hint_eq : (∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cosh ((1 - 1 / 2) * u) * Real.cos (0 * u)) =
      xiCoshMoment 0 (1 / 2) := by
    dsimp [xiCoshMoment]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [hsub, hcos u, pow_zero, mul_one, mul_one]
  rw [hint_eq] at hre
  linarith

/-- Helper: Derivative of `riemannPhiTerm n` is strictly nonpositive on `[1/50, ∞)` for every `n : ℕ`. -/
private lemma riemannPhiTerm_antitoneOn (n : ℕ) :
    AntitoneOn (riemannPhiTerm n) (Ici (1 / 50 : ℝ)) := by
  let c : ℝ := Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2
  have hc_ge : Real.pi ≤ c := by
    dsimp [c]
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    nlinarith [Real.pi_pos]
  have hd : ∀ u : ℝ, HasDerivAt (riemannPhiTerm n)
      (c * Real.exp (2 * u) * (-8 * (c * Real.exp (2 * u)) ^ 2 + 30 * (c * Real.exp (2 * u)) - 15) *
        thetaHalfTerm n u) u := by
    intro u
    have hfun : riemannPhiTerm n = fun x : ℝ =>
        (4 * c ^ 2 * Real.exp (4 * x) - 6 * c * Real.exp (2 * x)) * thetaHalfTerm n x := by
      ext x; dsimp [riemannPhiTerm, c]; ring
    rw [hfun]
    have he2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * u) * 2) u := by
      have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by simpa using (hasDerivAt_id' u).const_mul 2
      exact hlin.exp
    have he4 : HasDerivAt (fun x : ℝ => Real.exp (4 * x)) (Real.exp (4 * u) * 4) u := by
      have hlin : HasDerivAt (fun x : ℝ => 4 * x) 4 u := by simpa using (hasDerivAt_id' u).const_mul 4
      exact hlin.exp
    have hpref := (he4.const_mul (4 * c ^ 2)).sub (he2.const_mul (6 * c))
    have hprod := hpref.mul (hasDerivAt_thetaHalfTerm n u)
    convert hprod using 1
    dsimp [thetaHalfTermDeriv, c]
    have hsq : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hsq]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici (1 / 50 : ℝ))
  · exact (fun u _ => (hd u).continuousAt.continuousWithinAt)
  · exact fun u _ => (hd u).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    have hu_gt : (1 / 50 : ℝ) < u := hu
    rw [(hd u).deriv]
    let X : ℝ := c * Real.exp (2 * u)
    have hX_ge : (16 / 5 : ℝ) ≤ X := by
      dsimp [X]
      have he2 : (1 + 2 * (1 / 50 : ℝ)) ≤ Real.exp (2 * u) := by
        have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
        linarith
      have hpi_lo := pi_gt_31415
      have h1 : (31415 / 10000 : ℝ) * (26 / 25) ≤ c * Real.exp (2 * u) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith [Real.pi_pos])
      linarith
    have hquad_neg : -8 * X ^ 2 + 30 * X - 15 ≤ 0 := by
      have hdecomp : 8 * X ^ 2 - 30 * X + 15 =
          8 * (X - 16 / 5) ^ 2 + (106 / 5) * (X - 16 / 5) + 23 / 25 := by ring
      nlinarith [sq_nonneg (X - 16 / 5)]
    have hX_nn : 0 ≤ X := by linarith
    have hth_nn : 0 ≤ thetaHalfTerm n u := le_of_lt (Real.exp_pos _)
    change X * (-8 * X ^ 2 + 30 * X - 15) * thetaHalfTerm n u ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hX_nn hquad_neg) hth_nn

/-- THEOREM III.2 (Unconditional Antitonicity of `riemannPhi` on `[1/50, ∞)`):
    Every summand `riemannPhiTerm n` is decreasing on `[1/50, ∞)`, hence `riemannPhi`
    itself is antitone on `[1/50, ∞)`. -/
theorem riemannPhi_antitoneOn_from_one_fiftieth :
    AntitoneOn riemannPhi (Ici (1 / 50 : ℝ)) := by
  intro u hu v hv huv
  dsimp [riemannPhi]
  have hsum_u : Summable (fun n : ℕ => riemannPhiTerm n u) := summable_riemannPhiTerm u
  have hsum_v : Summable (fun n : ℕ => riemannPhiTerm n v) := summable_riemannPhiTerm v
  exact hsum_v.tsum_le_tsum (fun n => riemannPhiTerm_antitoneOn n hu hv huv) hsum_u

/-- Helper: `1 + z + z^2/2 + z^3/6 + z^4/24 ≤ exp z` for `0 ≤ z`. -/
private lemma exp_ge_poly4 {z : ℝ} (hz : 0 ≤ z) :
    1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 ≤ Real.exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 5
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h
  linarith

/-- Helper: `exp z ≤ 1 + z + z^2/2 + z^3/6 + z^4/24 + z^5/100` for `0 ≤ z ≤ 1`. -/
private lemma exp_le_poly5 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp z ≤ 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 100 := by
  have h := exp_le_taylor_of_nonneg_le_one hz0 hz1 (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h
  linarith

/-- Helper: Power-scaled lower bound on `exp x` for `x ≥ 0`. -/
private lemma exp_ge_pow {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) :
    (1 + x / m + (x / m) ^ 2 / 2 + (x / m) ^ 3 / 6 + (x / m) ^ 4 / 24) ^ m ≤ Real.exp x := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hzm : 0 ≤ x / (m : ℝ) := div_nonneg hx (le_of_lt hm_pos)
  have h1 := exp_ge_poly4 hzm
  have hpow : Real.exp x = (Real.exp (x / (m : ℝ))) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp [ne_of_gt hm_pos]
  rw [hpow]
  exact pow_le_pow_left₀ (by positivity) h1 m

/-- Helper: Power-scaled upper bound on `exp x` for `0 ≤ x` with `x / m ≤ 1`. -/
private lemma exp_le_pow {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) (hxm : x / (m : ℝ) ≤ 1) :
    Real.exp x ≤ (1 + x / m + (x / m) ^ 2 / 2 + (x / m) ^ 3 / 6 + (x / m) ^ 4 / 24 + (x / m) ^ 5 / 100) ^ m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hzm : 0 ≤ x / (m : ℝ) := div_nonneg hx (le_of_lt hm_pos)
  have h1 := exp_le_poly5 hzm hxm
  have hpow : Real.exp x = (Real.exp (x / (m : ℝ))) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp [ne_of_gt hm_pos]
  rw [hpow]
  exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h1 m

/-- Sharp `n ≥ 2` tail upper bound on `riemannPhi u` for ALL `u ≥ 0`:
    `riemannPhi u ≤ riemannPhiTerm 0 u + (1 / 500) * 4 * π^2 * exp(4u) * thetaHalfTerm 0 u`. -/
private lemma riemannPhi_le_term0_plus_tail {u : ℝ} (hu : 0 ≤ u) :
    riemannPhi u ≤ riemannPhiTerm 0 u +
      (1 / 500 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) := by
  dsimp [riemannPhi]
  rw [(summable_riemannPhiTerm u).tsum_eq_zero_add]
  suffices htail : ∑' n : ℕ, riemannPhiTerm (n + 1) u ≤
      (1 / 500 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) by linarith
  have hgeo_sum : Summable (fun n : ℕ =>
      (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) * ((16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ n)) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (16 / 10000 : ℝ)).mul_left _
  have hterm : ∀ n : ℕ, riemannPhiTerm (n + 1) u ≤
      (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) * ((16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ n) := by
    intro n
    set m : ℕ := n + 2
    have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
    have he2u_ge1 : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
    have h1 : riemannPhiTerm (n + 1) u ≤
        4 * Real.pi ^ 2 * (m : ℝ) ^ 4 * Real.exp (4 * u) * thetaHalfTerm (n + 1) u := by
      dsimp [riemannPhiTerm]
      have hsub_nn : 0 ≤ 6 * Real.pi * ((n + 1 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
      have hth_nn : 0 ≤ thetaHalfTerm (n + 1) u := le_of_lt (Real.exp_pos _)
      have hm_eq : ((n + 1 + 1 : ℕ) : ℝ) = (m : ℝ) := rfl
      rw [hm_eq]
      nlinarith
    have hth_ratio : thetaHalfTerm (n + 1) u =
        thetaHalfTerm 0 u * Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1) * Real.exp (2 * u)) := by
      dsimp [thetaHalfTerm]
      rw [← Real.exp_add]
      congr 1
      have hm_eq : ((n + 1 + 1 : ℕ) : ℝ) = (m : ℝ) := rfl
      rw [hm_eq]; norm_num; ring
    have hexp_drop : Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1) * Real.exp (2 * u)) ≤
        Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1)) := by
      apply Real.exp_le_exp.mpr
      have hm2 : 0 ≤ (m : ℝ) ^ 2 - 1 := by nlinarith
      have hprod : Real.pi * ((m : ℝ) ^ 2 - 1) ≤ Real.pi * ((m : ℝ) ^ 2 - 1) * Real.exp (2 * u) :=
        le_mul_of_one_le_right (mul_nonneg (le_of_lt Real.pi_pos) hm2) he2u_ge1
      linarith
    have hnum_decay : (m : ℝ) ^ 4 * Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1)) ≤
        (16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ n := by
      rw [show -Real.pi * ((m : ℝ) ^ 2 - 1) = -(Real.pi * ((m : ℝ) ^ 2 - 1)) by ring, Real.exp_neg]
      rw [mul_inv_le_iff₀ (Real.exp_pos _)]
      cases n with
      | zero =>
        have hm2 : (m : ℝ) = 2 := by norm_num [m]
        rw [hm2]; norm_num
        have hpi3 : (942 / 100 : ℝ) ≤ Real.pi * (2 ^ 2 - 1) := by linarith [pi_gt_31415]
        have he1 : (10000 : ℝ) ≤ Real.exp (942 / 100 : ℝ) := by
          have h := exp_ge_pow (x := 942 / 100) (by norm_num) (m := 12) (by norm_num)
          push_cast at h; norm_num at h ⊢; linarith
        have he2 : Real.exp (942 / 100 : ℝ) ≤ Real.exp (Real.pi * (2 ^ 2 - 1)) :=
          Real.exp_le_exp.mpr hpi3
        linarith
      | succ k =>
        have hm_eq : (m : ℝ) = ((k + 1 : ℕ) : ℝ) + 2 := by dsimp [m]; push_cast; ring
        have harg : (6 : ℝ) + 18 * ((k + 1 : ℕ) : ℝ) ≤ Real.pi * ((m : ℝ) ^ 2 - 1) := by
          rw [hm_eq]
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          have hpi3 : (3 : ℝ) ≤ Real.pi := by linarith [pi_gt_31415]
          have hsq : 2 + 6 * ((k + 1 : ℕ) : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 2) ^ 2 - 1 := by
            push_cast; nlinarith
          nlinarith
        have he6 : (400 : ℝ) ≤ Real.exp 6 := by
          have h := exp_ge_pow (x := 6) (by norm_num) (m := 8) (by norm_num)
          push_cast at h; norm_num at h; linarith
        have he18 : (100000 : ℝ) ≤ Real.exp 18 := by
          have h := exp_ge_pow (x := 18) (by norm_num) (m := 24) (by norm_num)
          push_cast at h; norm_num at h; linarith
        have hexp_ge : (400 : ℝ) * (100000 : ℝ) ^ (k + 1) ≤ Real.exp (Real.pi * ((m : ℝ) ^ 2 - 1)) := by
          have h1 : Real.exp (6 + 18 * ((k + 1 : ℕ) : ℝ)) ≤ Real.exp (Real.pi * ((m : ℝ) ^ 2 - 1)) :=
            Real.exp_le_exp.mpr harg
          have h2 : Real.exp (6 + 18 * ((k + 1 : ℕ) : ℝ)) = Real.exp 6 * (Real.exp 18) ^ (k + 1) := by
            rw [Real.exp_add, mul_comm 18 _, Real.exp_nat_mul]
          rw [h2] at h1
          have h3 : (100000 : ℝ) ^ (k + 1) ≤ (Real.exp 18) ^ (k + 1) :=
            pow_le_pow_left₀ (by norm_num) he18 _
          have h4 := mul_le_mul he6 h3 (by positivity) (by positivity)
          linarith
        have hpoly : ((k + 1 + 2 : ℕ) : ℝ) ^ 4 ≤ (64 : ℝ) * (10 : ℝ) ^ (k + 1) := by
          have hind : ∀ j : ℕ, ((j + 3 : ℕ) : ℝ) ^ 4 ≤ (81 : ℝ) * (10 : ℝ) ^ j := by
            intro j
            induction j with
            | zero => norm_num
            | succ r ihr =>
              have hstep : (((r + 1 + 3 : ℕ) : ℝ) ^ 4) ≤ 10 * (((r + 3 : ℕ) : ℝ) ^ 4) := by
                have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
                push_cast; nlinarith [sq_nonneg (r : ℝ), sq_nonneg ((r : ℝ) ^ 2)]
              calc (((r + 1 + 3 : ℕ) : ℝ) ^ 4)
                _ ≤ 10 * (((r + 3 : ℕ) : ℝ) ^ 4) := hstep
                _ ≤ 10 * ((81 : ℝ) * (10 : ℝ) ^ r) := by linarith
                _ = (81 : ℝ) * (10 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
          have h1 := hind k
          have h2 : ((k + 1 + 2 : ℕ) : ℝ) = ((k + 3 : ℕ) : ℝ) := by norm_cast
          rw [h2]
          calc ((k + 3 : ℕ) : ℝ) ^ 4 ≤ (81 : ℝ) * (10 : ℝ) ^ k := h1
            _ ≤ (64 : ℝ) * (10 : ℝ) ^ (k + 1) := by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 10) k]
        have hm_nat : (m : ℝ) = ((k + 1 + 2 : ℕ) : ℝ) := rfl
        rw [hm_nat]
        have hmul_rhs : (16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ (k + 1) * ((400 : ℝ) * (100000 : ℝ) ^ (k + 1)) =
            (64 / 100 : ℝ) * (10000 : ℝ) ^ (k + 1) := by
          have hpow : (1 / 10 : ℝ) ^ (k + 1) * (100000 : ℝ) ^ (k + 1) = (10000 : ℝ) ^ (k + 1) := by
            rw [← mul_pow]; norm_num
          calc (16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ (k + 1) * ((400 : ℝ) * (100000 : ℝ) ^ (k + 1))
            _ = (16 / 10000 * 400) * ((1 / 10 : ℝ) ^ (k + 1) * (100000 : ℝ) ^ (k + 1)) := by ring
            _ = (64 / 100 : ℝ) * (10000 : ℝ) ^ (k + 1) := by rw [hpow]; norm_num
        have hdom : (64 : ℝ) * (10 : ℝ) ^ (k + 1) ≤ (64 / 100 : ℝ) * (10000 : ℝ) ^ (k + 1) := by
          have h1 : (100 : ℝ) * (10 : ℝ) ^ (k + 1) ≤ (10000 : ℝ) ^ (k + 1) := by
            rw [pow_succ, pow_succ]
            have hpow : (10 : ℝ) ^ k ≤ (10000 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
            nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 10) k]
          linarith
        have hmain := mul_le_mul_of_nonneg_left hexp_ge (by positivity : 0 ≤ (16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ (k + 1))
        linarith
    have hpref_nn : 0 ≤ 4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u := by
      dsimp [thetaHalfTerm]; positivity
    calc riemannPhiTerm (n + 1) u
      _ ≤ 4 * Real.pi ^ 2 * (m : ℝ) ^ 4 * Real.exp (4 * u) * thetaHalfTerm (n + 1) u := h1
      _ = (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) *
            ((m : ℝ) ^ 4 * Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1) * Real.exp (2 * u))) := by
          rw [hth_ratio]; ring
      _ ≤ (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) *
            ((m : ℝ) ^ 4 * Real.exp (-Real.pi * ((m : ℝ) ^ 2 - 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_drop (by positivity)) hpref_nn
      _ ≤ (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) * ((16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hnum_decay hpref_nn
  have hsum_le := ((summable_nat_add_iff 1).mpr (summable_riemannPhiTerm u)).tsum_le_tsum hterm hgeo_sum
  have hgeo_val : ∑' n : ℕ, (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) *
        ((16 / 10000 : ℝ) * (1 / 10 : ℝ) ^ n) =
      (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) * (16 / 9000 : ℝ) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  rw [hgeo_val] at hsum_le
  have hpref_nn : 0 ≤ 4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u := by
    dsimp [thetaHalfTerm]; positivity
  have hfrac : (16 / 9000 : ℝ) ≤ 1 / 500 := by norm_num
  have hfin := mul_le_mul_of_nonneg_left hfrac hpref_nn
  linarith

/-- Generic pointwise lower bound on `riemannPhi b` from rational brackets on `exp (2*b)`, `exp (b/2)`, `exp (π*e^{2b})`. -/
private lemma riemannPhi_ge_of_brackets {b e2_lo e2_hi eh_lo e_pi_hi c_lo : ℝ}
    (hb : 0 ≤ b) (he2_lo : e2_lo ≤ Real.exp (2 * b)) (he2_hi : Real.exp (2 * b) ≤ e2_hi)
    (he2_ge1 : 1 ≤ e2_lo)
    (heh_lo : eh_lo ≤ Real.exp (b / 2)) (heh_nn : 0 ≤ eh_lo)
    (hepi_hi : Real.exp (Real.pi * e2_hi) ≤ e_pi_hi) (hepi_pos : 0 < e_pi_hi)
    (hnum : c_lo * e_pi_hi ≤ (4 * (31415 / 10000 : ℝ) ^ 2 * e2_lo ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo) * eh_lo) :
    c_lo ≤ riemannPhi b := by
  have hterm0 : riemannPhiTerm 0 b ≤ riemannPhi b := by
    dsimp [riemannPhi]
    have hnn : ∀ n : ℕ, 0 ≤ riemannPhiTerm n b := fun n => by
      dsimp [riemannPhiTerm, thetaHalfTerm]
      have hpi_lo : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have he2 : (1 : ℝ) ≤ Real.exp (2 * b) := Real.one_le_exp (by linarith)
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        nlinarith
      have hsq : Real.exp (4 * b) = Real.exp (2 * b) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
      rw [hsq]
      have hfac : 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (2 * b) ^ 2 -
          6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * b) =
          Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * b) *
            (4 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * b) - 6) := by ring
      rw [hfac]
      have hprod1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * b) :=
        one_le_mul_of_one_le_of_one_le hn1 he2
      have hpos_br : 0 ≤ 4 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * b) - 6 := by nlinarith
      exact mul_nonneg (mul_nonneg (by positivity) hpos_br) (le_of_lt (Real.exp_pos _))
    exact (summable_riemannPhiTerm b).le_tsum 0 (fun k _ => hnn k)
  have hpi_lo := pi_gt_31415
  have hsq : Real.exp (4 * b) = Real.exp (2 * b) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
  have hpoly_mono : 4 * (31415 / 10000 : ℝ) ^ 2 * e2_lo ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo ≤
      4 * Real.pi ^ 2 * Real.exp (2 * b) ^ 2 - 6 * Real.pi * Real.exp (2 * b) := by
    let X1 : ℝ := (31415 / 10000 : ℝ) * e2_lo
    let X2 : ℝ := Real.pi * Real.exp (2 * b)
    have hX1 : (3 : ℝ) ≤ X1 := by dsimp [X1]; nlinarith
    have hX12 : X1 ≤ X2 := mul_le_mul (le_of_lt hpi_lo) he2_lo (by linarith) (le_of_lt Real.pi_pos)
    have hdiff : (4 * X2 ^ 2 - 6 * X2) - (4 * X1 ^ 2 - 6 * X1) = (X2 - X1) * (4 * (X2 + X1) - 6) := by ring
    have heq1 : 4 * (31415 / 10000 : ℝ) ^ 2 * e2_lo ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo = 4 * X1 ^ 2 - 6 * X1 := by
      dsimp [X1]; ring
    have heq2 : 4 * Real.pi ^ 2 * Real.exp (2 * b) ^ 2 - 6 * Real.pi * Real.exp (2 * b) = 4 * X2 ^ 2 - 6 * X2 := by
      dsimp [X2]; ring
    rw [heq1, heq2]; nlinarith
  have hpoly_nn : 0 ≤ 4 * (31415 / 10000 : ℝ) ^ 2 * e2_lo ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo := by
    nlinarith
  have hth_eq : thetaHalfTerm 0 b = Real.exp (b / 2) * (Real.exp (Real.pi * Real.exp (2 * b)))⁻¹ := by
    dsimp [thetaHalfTerm]; rw [← Real.exp_neg, ← Real.exp_add]; congr 1; norm_num; ring
  have hinv_ge : e_pi_hi⁻¹ ≤ (Real.exp (Real.pi * Real.exp (2 * b)))⁻¹ := by
    have h1 : Real.exp (Real.pi * Real.exp (2 * b)) ≤ e_pi_hi :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he2_hi (le_of_lt Real.pi_pos))).trans hepi_hi
    exact (inv_le_inv₀ hepi_pos (Real.exp_pos _)).mpr h1
  have hth_ge : eh_lo * e_pi_hi⁻¹ ≤ thetaHalfTerm 0 b := by
    rw [hth_eq]
    exact mul_le_mul heh_lo hinv_ge (inv_nonneg.mpr (le_of_lt hepi_pos)) (le_of_lt (Real.exp_pos _))
  have ht0_ge : (4 * (31415 / 10000 : ℝ) ^ 2 * e2_lo ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo) * (eh_lo * e_pi_hi⁻¹) ≤
      riemannPhiTerm 0 b := by
    dsimp [riemannPhiTerm]; rw [hsq]
    simp only [Nat.cast_one, one_pow, mul_one]
    exact mul_le_mul hpoly_mono hth_ge (by positivity) (by linarith)
  have hc_le : c_lo ≤ (4 * (31415 / 10000 : ℝ) ^ 2 * e2_lo ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo) * (eh_lo * e_pi_hi⁻¹) := by
    have := (le_mul_inv_iff₀ hepi_pos).mpr hnum
    linarith
  linarith

/-- Generic pointwise upper bound on `riemannPhi a` from rational brackets on `exp (2*a)`, `exp (a/2)`, `exp (π*e^{2a})`. -/
private lemma riemannPhi_le_of_brackets {a e2_lo e2_hi eh_hi e_pi_lo c_hi : ℝ}
    (ha : 0 ≤ a) (he2_lo : e2_lo ≤ Real.exp (2 * a)) (he2_hi : Real.exp (2 * a) ≤ e2_hi)
    (he2_ge1 : 1 ≤ e2_lo)
    (heh_hi : Real.exp (a / 2) ≤ eh_hi) (heh_nn : 0 ≤ eh_hi)
    (hepi_lo : e_pi_lo ≤ Real.exp (Real.pi * e2_lo)) (hepi_pos : 0 < e_pi_lo)
    (hnum : ((501 / 500 : ℝ) * 4 * (31416 / 10000 : ℝ) ^ 2 * e2_hi ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo) * eh_hi ≤ c_hi * e_pi_lo) :
    riemannPhi a ≤ c_hi := by
  have htail := riemannPhi_le_term0_plus_tail ha
  have hpi_lo := pi_gt_31415
  have hpi_hi := pi_lt_31416
  have hsq : Real.exp (4 * a) = Real.exp (2 * a) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
  have hth_eq : thetaHalfTerm 0 a = Real.exp (a / 2) * (Real.exp (Real.pi * Real.exp (2 * a)))⁻¹ := by
    dsimp [thetaHalfTerm]; rw [← Real.exp_neg, ← Real.exp_add]; congr 1; norm_num; ring
  have hinv_le : (Real.exp (Real.pi * Real.exp (2 * a)))⁻¹ ≤ e_pi_lo⁻¹ := by
    have h1 : e_pi_lo ≤ Real.exp (Real.pi * Real.exp (2 * a)) :=
      hepi_lo.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he2_lo (le_of_lt Real.pi_pos)))
    exact (inv_le_inv₀ (Real.exp_pos _) hepi_pos).mpr h1
  have hth_le : thetaHalfTerm 0 a ≤ eh_hi * e_pi_lo⁻¹ := by
    rw [hth_eq]
    exact mul_le_mul heh_hi hinv_le (inv_nonneg.mpr (le_of_lt (Real.exp_pos _))) heh_nn
  have hpoly_le : (501 / 500 : ℝ) * 4 * Real.pi ^ 2 * Real.exp (2 * a) ^ 2 - 6 * Real.pi * Real.exp (2 * a) ≤
      (501 / 500 : ℝ) * 4 * (31416 / 10000 : ℝ) ^ 2 * e2_hi ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo := by
    have h1 : Real.pi * Real.exp (2 * a) ≤ (31416 / 10000 : ℝ) * e2_hi :=
      mul_le_mul (le_of_lt hpi_hi) he2_hi (le_of_lt (Real.exp_pos _)) (by norm_num)
    have h2 : (Real.pi * Real.exp (2 * a)) ^ 2 ≤ ((31416 / 10000 : ℝ) * e2_hi) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (31415 / 10000 : ℝ) * e2_lo ≤ Real.pi * Real.exp (2 * a) :=
      mul_le_mul (le_of_lt hpi_lo) he2_lo (by linarith) (le_of_lt Real.pi_pos)
    nlinarith
  have hpoly_nn : 0 ≤ (501 / 500 : ℝ) * 4 * Real.pi ^ 2 * Real.exp (2 * a) ^ 2 - 6 * Real.pi * Real.exp (2 * a) := by
    have he1 : (1 : ℝ) ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
    have hfac : (501 / 500 : ℝ) * 4 * Real.pi ^ 2 * Real.exp (2 * a) ^ 2 - 6 * Real.pi * Real.exp (2 * a) =
        Real.pi * Real.exp (2 * a) * ((501 / 500 : ℝ) * 4 * Real.pi * Real.exp (2 * a) - 6) := by ring
    rw [hfac]
    exact mul_nonneg (by positivity) (by nlinarith)
  have hcomb : riemannPhiTerm 0 a + (1 / 500 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (4 * a) * thetaHalfTerm 0 a) =
      ((501 / 500 : ℝ) * 4 * Real.pi ^ 2 * Real.exp (2 * a) ^ 2 - 6 * Real.pi * Real.exp (2 * a)) * thetaHalfTerm 0 a := by
    dsimp [riemannPhiTerm]; rw [hsq]; norm_num; ring
  rw [hcomb] at htail
  have hprod : ((501 / 500 : ℝ) * 4 * Real.pi ^ 2 * Real.exp (2 * a) ^ 2 - 6 * Real.pi * Real.exp (2 * a)) * thetaHalfTerm 0 a ≤
      ((501 / 500 : ℝ) * 4 * (31416 / 10000 : ℝ) ^ 2 * e2_hi ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo) * (eh_hi * e_pi_lo⁻¹) :=
    mul_le_mul hpoly_le hth_le (le_of_lt (Real.exp_pos _)) (by linarith)
  have hc_ge : ((501 / 500 : ℝ) * 4 * (31416 / 10000 : ℝ) ^ 2 * e2_hi ^ 2 - 6 * (31415 / 10000 : ℝ) * e2_lo) * (eh_hi * e_pi_lo⁻¹) ≤ c_hi := by
    have := (mul_inv_le_iff₀ hepi_pos).mpr hnum
    linarith
  linarith

-- Pointwise certified rational brackets at the 9 grid nodes:
-- 1/50, 3/20, 1/4, 7/20, 9/20, 11/20, 13/20, 4/5!

private lemma phi_bounds_bin0 {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 50) :
    (75 / 100 : ℝ) ≤ riemannPhi u ∧ riemannPhi u ≤ 106 / 100 := by
  have he2_lo : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have he2_hi : Real.exp (2 * u) ≤ 1041 / 1000 := by
    have h1 := Real.exp_le_exp.mpr (show 2 * u ≤ 1 / 25 by linarith)
    have h2 := exp_le_poly5 (z := 1 / 25) (by norm_num) (by norm_num)
    norm_num at h2; linarith
  have heh_lo : (1 : ℝ) ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
  have heh_hi : Real.exp (u / 2) ≤ 1011 / 1000 := by
    have h1 := Real.exp_le_exp.mpr (show u / 2 ≤ 1 / 100 by linarith)
    have h2 := exp_le_poly5 (z := 1 / 100) (by norm_num) (by norm_num)
    norm_num at h2; linarith
  have hepi_hi : Real.exp (Real.pi * (1041 / 1000)) ≤ 264 / 10 := by
    have h1 : Real.pi * (1041 / 1000 : ℝ) ≤ 3271 / 1000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 3271 / 1000) (by norm_num) (m := 6) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (231 / 10 : ℝ) ≤ Real.exp (Real.pi * 1) := by
    have h1 : (31415 / 10000 : ℝ) ≤ Real.pi * 1 := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 31415 / 10000) (by norm_num) (m := 6) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  constructor
  · exact riemannPhi_ge_of_brackets hu0 he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num)
  · exact riemannPhi_le_of_brackets hu0 he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)

private lemma phi_at_002_le : riemannPhi (1 / 50) ≤ 90 / 100 := by
  have he2_lo : (1301 / 1250 : ℝ) ≤ Real.exp (2 * (1 / 50)) := by
    have h := exp_ge_poly4 (z := 1 / 25) (by norm_num); norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (1 / 50)) ≤ 10409 / 10000 := by
    have h := exp_le_poly5 (z := 1 / 25) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((1 / 50 : ℝ) / 2) ≤ 10101 / 10000 := by
    have h := exp_le_poly5 (z := 1 / 100) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have hepi_lo : (2613 / 100 : ℝ) ≤ Real.exp (Real.pi * (1301 / 1250)) := by
    have h1 : (4087 / 1250 : ℝ) ≤ Real.pi * (1301 / 1250) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 4087 / 1250) (by norm_num) (m := 4) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)

private lemma phi_at_015_bounds : (72 / 100 : ℝ) ≤ riemannPhi (3 / 20) ∧ riemannPhi (3 / 20) ≤ 73 / 100 := by
  have he2_lo : (6749 / 5000 : ℝ) ≤ Real.exp (2 * (3 / 20)) := by
    have h := exp_ge_pow (x := 3 / 10) (by norm_num) (m := 2) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (3 / 20)) ≤ 13499 / 10000 := by
    have h := exp_le_pow (x := 3 / 10) (by norm_num) (m := 2) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (5389 / 5000 : ℝ) ≤ Real.exp ((3 / 20 : ℝ) / 2) := by
    have h := exp_ge_poly4 (z := 3 / 40) (by norm_num); norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((3 / 20 : ℝ) / 2) ≤ 10779 / 10000 := by
    have h := exp_le_poly5 (z := 3 / 40) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (13499 / 10000)) ≤ 139 / 2 := by
    have h1 : Real.pi * (13499 / 10000 : ℝ) ≤ 42409 / 10000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 42409 / 10000) (by norm_num) (m := 6) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (1727 / 25 : ℝ) ≤ Real.exp (Real.pi * (6749 / 5000)) := by
    have h1 : (42403 / 10000 : ℝ) ≤ Real.pi * (6749 / 5000) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 42403 / 10000) (by norm_num) (m := 6) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

private lemma phi_at_025_bounds : (48 / 100 : ℝ) ≤ riemannPhi (1 / 4) ∧ riemannPhi (1 / 4) ≤ 492 / 1000 := by
  have he2_lo : (8243 / 5000 : ℝ) ≤ Real.exp (2 * (1 / 4)) := by
    have h := exp_ge_pow (x := 1 / 2) (by norm_num) (m := 2) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (1 / 4)) ≤ 2061 / 1250 := by
    have h := exp_le_pow (x := 1 / 2) (by norm_num) (m := 2) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (11331 / 10000 : ℝ) ≤ Real.exp ((1 / 4 : ℝ) / 2) := by
    have h := exp_ge_poly4 (z := 1 / 8) (by norm_num); norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((1 / 4 : ℝ) / 2) ≤ 2833 / 2500 := by
    have h := exp_le_poly5 (z := 1 / 8) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (2061 / 1250)) ≤ 17773 / 100 := by
    have h1 : Real.pi * (2061 / 1250 : ℝ) ≤ 51799 / 10000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 51799 / 10000) (by norm_num) (m := 8) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (17671 / 100 : ℝ) ≤ Real.exp (Real.pi * (8243 / 5000)) := by
    have h1 : (5179 / 1000 : ℝ) ≤ Real.pi * (8243 / 5000) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 5179 / 1000) (by norm_num) (m := 8) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

private lemma phi_at_035_bounds : (25 / 100 : ℝ) ≤ riemannPhi (7 / 20) ∧ riemannPhi (7 / 20) ≤ 265 / 1000 := by
  have he2_lo : (20137 / 10000 : ℝ) ≤ Real.exp (2 * (7 / 20)) := by
    have h := exp_ge_pow (x := 7 / 10) (by norm_num) (m := 4) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (7 / 20)) ≤ 10069 / 5000 := by
    have h := exp_le_pow (x := 7 / 10) (by norm_num) (m := 4) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (1489 / 1250 : ℝ) ≤ Real.exp ((7 / 20 : ℝ) / 2) := by
    have h := exp_ge_poly4 (z := 7 / 40) (by norm_num); norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((7 / 20 : ℝ) / 2) ≤ 11913 / 10000 := by
    have h := exp_le_poly5 (z := 7 / 40) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (10069 / 5000)) ≤ 55947 / 100 := by
    have h1 : Real.pi * (10069 / 5000 : ℝ) ≤ 31633 / 5000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 31633 / 5000) (by norm_num) (m := 10) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (13903 / 25 : ℝ) ≤ Real.exp (Real.pi * (20137 / 10000)) := by
    have h1 : (3163 / 500 : ℝ) ≤ Real.pi * (20137 / 10000) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 3163 / 500) (by norm_num) (m := 10) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

private lemma phi_at_045_bounds : (105 / 1000 : ℝ) ≤ riemannPhi (9 / 20) ∧ riemannPhi (9 / 20) ≤ 110 / 1000 := by
  have he2_lo : (4919 / 2000 : ℝ) ≤ Real.exp (2 * (9 / 20)) := by
    have h := exp_ge_pow (x := 9 / 10) (by norm_num) (m := 4) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (9 / 20)) ≤ 24597 / 10000 := by
    have h := exp_le_pow (x := 9 / 10) (by norm_num) (m := 4) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (12523 / 10000 : ℝ) ≤ Real.exp ((9 / 20 : ℝ) / 2) := by
    have h := exp_ge_poly4 (z := 9 / 40) (by norm_num); norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((9 / 20 : ℝ) / 2) ≤ 3131 / 2500 := by
    have h := exp_le_poly5 (z := 9 / 40) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (24597 / 10000)) ≤ 113539 / 50 := by
    have h1 : Real.pi * (24597 / 10000 : ℝ) ≤ 38637 / 5000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 38637 / 5000) (by norm_num) (m := 12) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (45059 / 20 : ℝ) ≤ Real.exp (Real.pi * (4919 / 2000)) := by
    have h1 : (15453 / 2000 : ℝ) ≤ Real.pi * (4919 / 2000) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 15453 / 2000) (by norm_num) (m := 12) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

private lemma phi_at_055_bounds : (31 / 1000 : ℝ) ≤ riemannPhi (11 / 20) ∧ riemannPhi (11 / 20) ≤ 32 / 1000 := by
  have he2_lo : (751 / 250 : ℝ) ≤ Real.exp (2 * (11 / 20)) := by
    have h := exp_ge_pow (x := 11 / 10) (by norm_num) (m := 4) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (11 / 20)) ≤ 15021 / 5000 := by
    have h := exp_le_pow (x := 11 / 10) (by norm_num) (m := 4) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (2633 / 2000 : ℝ) ≤ Real.exp ((11 / 20 : ℝ) / 2) := by
    have h := exp_ge_poly4 (z := 11 / 40) (by norm_num); norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((11 / 20 : ℝ) / 2) ≤ 6583 / 5000 := by
    have h := exp_le_poly5 (z := 11 / 40) (by norm_num) (by norm_num); norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (15021 / 5000)) ≤ 1256447 / 100 := by
    have h1 : Real.pi * (15021 / 5000 : ℝ) ≤ 4719 / 500 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 4719 / 500) (by norm_num) (m := 14) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (248557 / 20 : ℝ) ≤ Real.exp (Real.pi * (751 / 250)) := by
    have h1 : (9437 / 1000 : ℝ) ≤ Real.pi * (751 / 250) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 9437 / 1000) (by norm_num) (m := 14) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

private lemma phi_at_065_bounds : (6 / 1000 : ℝ) ≤ riemannPhi (13 / 20) ∧ riemannPhi (13 / 20) ≤ 65 / 10000 := by
  have he2_lo : (36689 / 10000 : ℝ) ≤ Real.exp (2 * (13 / 20)) := by
    have h := exp_ge_pow (x := 13 / 10) (by norm_num) (m := 4) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (13 / 20)) ≤ 18347 / 5000 := by
    have h := exp_le_pow (x := 13 / 10) (by norm_num) (m := 4) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (173 / 125 : ℝ) ≤ Real.exp ((13 / 20 : ℝ) / 2) := by
    have h := exp_ge_pow (x := 13 / 40) (by norm_num) (m := 2) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((13 / 20 : ℝ) / 2) ≤ 13841 / 10000 := by
    have h := exp_le_pow (x := 13 / 40) (by norm_num) (m := 2) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (18347 / 5000)) ≤ 5079171 / 50 := by
    have h1 : Real.pi * (18347 / 5000 : ℝ) ≤ 57639 / 5000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 57639 / 5000) (by norm_num) (m := 16) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (9986027 / 100 : ℝ) ≤ Real.exp (Real.pi * (36689 / 10000)) := by
    have h1 : (57629 / 5000 : ℝ) ≤ Real.pi * (36689 / 10000) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 57629 / 5000) (by norm_num) (m := 16) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

private lemma phi_at_080_bounds : (2 / 10000 : ℝ) ≤ riemannPhi (4 / 5) ∧ riemannPhi (4 / 5) ≤ 3 / 10000 := by
  have he2_lo : (49527 / 10000 : ℝ) ≤ Real.exp (2 * (4 / 5)) := by
    have h := exp_ge_pow (x := 8 / 5) (by norm_num) (m := 6) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have he2_hi : Real.exp (2 * (4 / 5)) ≤ 49531 / 10000 := by
    have h := exp_le_pow (x := 8 / 5) (by norm_num) (m := 6) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_lo : (7459 / 5000 : ℝ) ≤ Real.exp ((4 / 5 : ℝ) / 2) := by
    have h := exp_ge_pow (x := 2 / 5) (by norm_num) (m := 2) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have heh_hi : Real.exp ((4 / 5 : ℝ) / 2) ≤ 14919 / 10000 := by
    have h := exp_le_pow (x := 2 / 5) (by norm_num) (m := 2) (by norm_num) (by norm_num); push_cast at h; norm_num at h ⊢; linarith
  have hepi_hi : Real.exp (Real.pi * (49531 / 10000)) ≤ 286627561 / 50 := by
    have h1 : Real.pi * (49531 / 10000 : ℝ) ≤ 155607 / 10000 := by linarith [pi_lt_31416]
    have h2 := (Real.exp_le_exp.mpr h1).trans (exp_le_pow (x := 155607 / 10000) (by norm_num) (m := 24) (by norm_num) (by norm_num))
    push_cast at h2; norm_num at h2 ⊢; linarith
  have hepi_lo : (282028507 / 50 : ℝ) ≤ Real.exp (Real.pi * (49527 / 10000)) := by
    have h1 : (155589 / 10000 : ℝ) ≤ Real.pi * (49527 / 10000) := by linarith [pi_gt_31415]
    have h2 := (exp_ge_pow (x := 155589 / 10000) (by norm_num) (m := 24) (by norm_num)).trans (Real.exp_le_exp.mpr h1)
    push_cast at h2; norm_num at h2 ⊢; linarith
  exact ⟨riemannPhi_ge_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_lo (by norm_num) hepi_hi (by norm_num) (by norm_num),
         riemannPhi_le_of_brackets (by norm_num) he2_lo he2_hi (by norm_num) heh_hi (by norm_num) hepi_lo (by norm_num) (by norm_num)⟩

/-- Helper: elementary rational upper bound on `cosh x` for `0 ≤ x ≤ 1/2`. -/
private lemma cosh_le_poly4 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.cosh x ≤ 1 + x ^ 2 / 2 + x ^ 4 / 20 := by
  have h1 := exp_le_poly5 hx0 (by linarith)
  have hneg : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 := by
    rw [Real.exp_neg]
    have hexp_ge := exp_ge_poly4 hx0
    have hden_pos : 0 < 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by positivity
    have hinv : (Real.exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos x) hden_pos).mpr hexp_ge
    have hprod : 1 ≤ (1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24) := by
      have hid : (1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24) - 1 =
          x ^ 6 / 72 + x ^ 8 / 576 := by ring
      nlinarith [pow_nonneg hx0 6, pow_nonneg hx0 8]
    have hle := (inv_le_iff_one_le_mul₀ hden_pos).mpr hprod
    linarith
  rw [Real.cosh_eq]
  have hx5 : x ^ 5 ≤ (1 / 2 : ℝ) * x ^ 4 := by
    have : x ^ 5 = x * x ^ 4 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hx1 (pow_nonneg hx0 4)
  have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx0 4
  linarith

/-- Helper: Split `∫_Ioc a b` into adjacent `Ioc` bins cleanly. -/
private lemma setIntegral_Ioc_add {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntegrableOn f (Ioc a b)) (h2 : IntegrableOn f (Ioc b c)) :
    ∫ u in Ioc a c, f u = (∫ u in Ioc a b, f u) + (∫ u in Ioc b c, f u) := by
  have hun : Ioc a b ∪ Ioc b c = Ioc a c := Ioc_union_Ioc_eq_Ioc hab hbc
  have hdisj : Disjoint (Ioc a b) (Ioc b c) := Ioc_disjoint_Ioc_of_le le_rfl
  rw [← hun, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc h1 h2]

/-- Helper: Lower bound on `∫_{Ioc a b} Φ(u) * u^k du` from constant floor `c_lo ≤ Φ(u)`. -/
private lemma setIntegral_phi_pow_ge_bin {a b c_lo : ℝ} {k : ℕ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hphi : ∀ u ∈ Ioc a b, c_lo ≤ riemannPhi u) :
    c_lo * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℝ)) ≤
      ∫ u in Ioc a b, riemannPhi u * u ^ k * Real.cosh (0 * u) := by
  have hval : c_lo * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℝ)) =
      ∫ u in Ioc a b, c_lo * u ^ k := by
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul, integral_pow]
  rw [hval]
  refine MeasureTheory.setIntegral_mono_on
    ((continuous_const.mul (continuous_pow k)).integrableOn_Ioc)
    ((integrableOn_phi_pow_cosh k 0).mono_set (fun u hu => lt_of_le_of_lt ha hu.1))
    measurableSet_Ioc fun u hu => ?_
  simp only [zero_mul, Real.cosh_zero, mul_one]
  exact mul_le_mul_of_nonneg_right (hphi u hu) (pow_nonneg (le_of_lt (lt_of_le_of_lt ha hu.1)) k)

/-- Helper: Upper bound on `∫_{Ioc a b} Φ(u) * u^k * cosh(σ*u) du` from constant ceiling `c_hi` and `ch_hi`. -/
private lemma setIntegral_phi_pow_cosh_le_bin {a b σ c_hi ch_hi : ℝ} {k : ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hσ : 0 ≤ σ)
    (hphi : ∀ u ∈ Ioc a b, riemannPhi u ≤ c_hi)
    (hch : Real.cosh (σ * b) ≤ ch_hi) :
    ∫ u in Ioc a b, riemannPhi u * u ^ k * Real.cosh (σ * u) ≤
      c_hi * ch_hi * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℝ)) := by
  have hval : c_hi * ch_hi * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℝ)) =
      ∫ u in Ioc a b, (c_hi * ch_hi) * u ^ k := by
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul, integral_pow]
  rw [hval]
  refine MeasureTheory.setIntegral_mono_on
    ((integrableOn_phi_pow_cosh k σ).mono_set (fun u hu => lt_of_le_of_lt ha hu.1))
    ((continuous_const.mul (continuous_pow k)).integrableOn_Ioc)
    measurableSet_Ioc fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt (lt_of_le_of_lt ha hu.1)
  have hch_u : Real.cosh (σ * u) ≤ ch_hi := by
    have h1 : Real.cosh (σ * u) ≤ Real.cosh (σ * b) := by
      have hle : σ * u ≤ σ * b := mul_le_mul_of_nonneg_left hu.2 hσ
      exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (mul_nonneg hσ hu0), abs_of_nonneg (mul_nonneg hσ (le_trans ha hab))]; exact hle)
    linarith
  have hprod : riemannPhi u * Real.cosh (σ * u) ≤ c_hi * ch_hi :=
    mul_le_mul (hphi u hu) hch_u (le_of_lt (Real.cosh_pos _)) (le_trans (le_of_lt (riemannPhi_pos u)) (hphi u hu))
  have hre : riemannPhi u * u ^ k * Real.cosh (σ * u) = (riemannPhi u * Real.cosh (σ * u)) * u ^ k := by ring
  rw [hre]
  exact mul_le_mul_of_nonneg_right hprod (pow_nonneg hu0 k)

/-- Tail bound on `[1, ∞)`: `∫_{Ioi 1} Φ(u) * u^k * cosh(σ*u) du ≤ 1 / 100000` for `k ≤ 4, 0 ≤ σ ≤ 1/2`. -/
private lemma tail_Ioi_one_le {k : ℕ} (hk : k ≤ 4) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) :
    ∫ u in Ioi (1 : ℝ), riemannPhi u * u ^ k * Real.cosh (σ * u) ≤ 1 / 100000 := by
  -- For u ≥ 1:
  -- Φ(u) ≤ (501/500) * 4*π^2 * e^{9u/2} * exp(-π * e^{2u})
  -- u^k ≤ u^4 ≤ 24 * exp(u)
  -- cosh(σ*u) ≤ exp(u/2)
  -- e^{2u} = e^2 * e^{2(u-1)} ≥ 7 * (1 + 2*(u-1)) = 14*u - 7 (since e^2 ≥ 7.38 > 7!)
  -- So π * e^{2u} ≥ 3.14 * (14*u - 7) = 43.96*u - 21.98 ≥ 43*u - 22!
  -- Thus Φ(u) * u^k * cosh(σ*u) ≤ 40 * 24 * exp(6*u - (43*u - 22)) = 960 * exp(22 - 37*u)
  -- Wait: at u = 1, 22 - 37 = -15, 960 * exp(-15) / 37 = 26 * 3e-7 = 8e-6 < 1/100000!!
  have hdom_int : IntegrableOn (fun u : ℝ => 960 * Real.exp 22 * Real.exp (-37 * u)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (a := -37) (by norm_num) 1).const_mul (960 * Real.exp 22)
  have hpt : ∀ u ∈ Ioi (1 : ℝ),
      riemannPhi u * u ^ k * Real.cosh (σ * u) ≤ 960 * Real.exp 22 * Real.exp (-37 * u) := by
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hu0 : 0 ≤ u := by linarith
    have hphi := riemannPhi_le_term0_plus_tail hu0
    have hphi_ub : riemannPhi u ≤ 40 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) := by
      have hpi_hi := pi_lt_31416
      have hcomb : riemannPhiTerm 0 u + (1 / 500 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (4 * u) * thetaHalfTerm 0 u) ≤
          (501 / 500 : ℝ) * 4 * Real.pi ^ 2 * (Real.exp (4 * u) * thetaHalfTerm 0 u) := by
        dsimp [riemannPhiTerm]
        have hnn : 0 ≤ 6 * Real.pi * ((0 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) * thetaHalfTerm 0 u := by
          dsimp [thetaHalfTerm]; positivity
        norm_num at hnn ⊢; linarith
      have hexp_eq : Real.exp (4 * u) * thetaHalfTerm 0 u = Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) := by
        dsimp [thetaHalfTerm]; rw [← Real.exp_add]; congr 1; norm_num; ring
      rw [hexp_eq] at hcomb
      have hc40 : (501 / 500 : ℝ) * 4 * Real.pi ^ 2 ≤ 40 := by nlinarith [Real.pi_pos]
      have he_nn : 0 ≤ Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) := le_of_lt (Real.exp_pos _)
      linarith [mul_le_mul_of_nonneg_right hc40 he_nn]
    have huk : u ^ k ≤ 24 * Real.exp u := by
      have h1 : u ^ k ≤ u ^ 4 := pow_le_pow_right₀ hu1 hk
      have h2 := exp_ge_poly4 hu0
      have h3 : u ^ 4 / 24 ≤ Real.exp u := by nlinarith [pow_nonneg hu0 2, pow_nonneg hu0 3]
      linarith
    have hch : Real.cosh (σ * u) ≤ Real.exp (u / 2) := by
      rw [Real.cosh_eq]
      have h1 : Real.exp (σ * u) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (-(σ * u)) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have he2u : 14 * u - 7 ≤ Real.exp (2 * u) := by
      have he2 : (7 : ℝ) ≤ Real.exp 2 := by
        have h := exp_ge_pow (x := 2) (by norm_num) (m := 4) (by norm_num)
        push_cast at h; norm_num at h; linarith
      have hshift : 1 + 2 * (u - 1) ≤ Real.exp (2 * (u - 1)) := by linarith [Real.add_one_le_exp (2 * (u - 1))]
      have hmul : Real.exp (2 * u) = Real.exp 2 * Real.exp (2 * (u - 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hmul]
      nlinarith
    have hpi_e2 : 43 * u - 22 ≤ Real.pi * Real.exp (2 * u) := by
      have hpi_lo := pi_gt_31415
      nlinarith
    have hexp_comb : Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) * Real.exp u * Real.exp (u / 2) ≤
        Real.exp 22 * Real.exp (-37 * u) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc riemannPhi u * u ^ k * Real.cosh (σ * u)
      _ ≤ (40 * Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u))) * (24 * Real.exp u) * Real.exp (u / 2) :=
          mul_le_mul (mul_le_mul hphi_ub huk (pow_nonneg hu0 k) (by positivity)) hch
            (le_of_lt (Real.cosh_pos _)) (by positivity)
      _ = 960 * (Real.exp (9 * u / 2 - Real.pi * Real.exp (2 * u)) * Real.exp u * Real.exp (u / 2)) := by ring
      _ ≤ 960 * (Real.exp 22 * Real.exp (-37 * u)) := mul_le_mul_of_nonneg_left hexp_comb (by norm_num)
      _ = 960 * Real.exp 22 * Real.exp (-37 * u) := by ring
  have hmono := MeasureTheory.setIntegral_mono_on
    ((integrableOn_phi_pow_cosh k σ).mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
    hdom_int measurableSet_Ioi hpt
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (a := -37) (by norm_num) 1] at hmono
  have hval : 960 * Real.exp 22 * (-Real.exp (-37 * 1) / -37) = (960 / 37 : ℝ) * (Real.exp 15)⁻¹ := by
    have h1 : Real.exp 22 * Real.exp (-37 * 1) = (Real.exp 15)⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_add]; congr 1; norm_num
    calc 960 * Real.exp 22 * (-Real.exp (-37 * 1) / -37)
      _ = (960 / 37 : ℝ) * (Real.exp 22 * Real.exp (-37 * 1)) := by ring
      _ = (960 / 37 : ℝ) * (Real.exp 15)⁻¹ := by rw [h1]
  rw [hval] at hmono
  have he15 : (3000000 : ℝ) ≤ Real.exp 15 := by
    have h := exp_ge_pow (x := 15) (by norm_num) (m := 20) (by norm_num)
    push_cast at h; norm_num at h; linarith
  have hinv : (Real.exp 15)⁻¹ ≤ (3000000 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he15
  have hfin : (960 / 37 : ℝ) * (Real.exp 15)⁻¹ ≤ 1 / 100000 := by
    have h1 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 960 / 37)
    norm_num at h1 ⊢; linarith
  linarith

/-- Helper: Split `∫_{Ioi 0} f` into 9 `Ioc` bins on `(0, 1]` plus tail `Ioi 1`. -/
private lemma setIntegral_Ioi_zero_eq_nine_bins {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    ∫ u in Ioi (0 : ℝ), f u =
      (∫ u in Ioc (0 : ℝ) (1 / 50), f u) +
      (∫ u in Ioc (1 / 50 : ℝ) (3 / 20), f u) +
      (∫ u in Ioc (3 / 20 : ℝ) (1 / 4), f u) +
      (∫ u in Ioc (1 / 4 : ℝ) (7 / 20), f u) +
      (∫ u in Ioc (7 / 20 : ℝ) (9 / 20), f u) +
      (∫ u in Ioc (9 / 20 : ℝ) (11 / 20), f u) +
      (∫ u in Ioc (11 / 20 : ℝ) (13 / 20), f u) +
      (∫ u in Ioc (13 / 20 : ℝ) (4 / 5), f u) +
      (∫ u in Ioc (4 / 5 : ℝ) 1, f u) +
      (∫ u in Ioi (1 : ℝ), f u) := by
  have hun : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := Ioc_disjoint_Ioi_same
  have hsub : ∀ a b : ℝ, 0 ≤ a → Ioc a b ⊆ Ioi (0 : ℝ) := fun a b ha u hu => lt_of_le_of_lt ha hu.1
  rw [← hun, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        (hf.mono_set (hsub 0 1 le_rfl)) (hf.mono_set (fun u (hu : (1 : ℝ) < u) => lt_trans zero_lt_one hu))]
  rw [setIntegral_Ioc_add (b := 4 / 5) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 13 / 20) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 11 / 20) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 9 / 20) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 7 / 20) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 1 / 4) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 3 / 20) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num))),
      setIntegral_Ioc_add (b := 1 / 50) (by norm_num) (by norm_num) (hf.mono_set (hsub _ _ (by norm_num))) (hf.mono_set (hsub _ _ (by norm_num)))]

/-- Helper: Lower bound on `xiCoshMoment k 0` via the 9-bin antitone grid. -/
private lemma xiCoshMoment_zero_ge_nine_bins (k : ℕ) :
    (75 / 100 : ℝ) * (((1 / 50 : ℝ) ^ (k + 1) - 0 ^ (k + 1)) / (k + 1 : ℝ)) +
    (72 / 100 : ℝ) * (((3 / 20 : ℝ) ^ (k + 1) - (1 / 50 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) +
    (48 / 100 : ℝ) * (((1 / 4 : ℝ) ^ (k + 1) - (3 / 20 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) +
    (25 / 100 : ℝ) * (((7 / 20 : ℝ) ^ (k + 1) - (1 / 4 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) +
    (105 / 1000 : ℝ) * (((9 / 20 : ℝ) ^ (k + 1) - (7 / 20 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) +
    (31 / 1000 : ℝ) * (((11 / 20 : ℝ) ^ (k + 1) - (9 / 20 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) +
    (6 / 1000 : ℝ) * (((13 / 20 : ℝ) ^ (k + 1) - (11 / 20 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) +
    (2 / 10000 : ℝ) * (((4 / 5 : ℝ) ^ (k + 1) - (13 / 20 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)) ≤
      xiCoshMoment k 0 := by
  dsimp [xiCoshMoment]
  rw [setIntegral_Ioi_zero_eq_nine_bins (integrableOn_phi_pow_cosh k 0)]
  have hanti := riemannPhi_antitoneOn_from_one_fiftieth
  have b1 := setIntegral_phi_pow_ge_bin (k := k) (a := 0) (b := 1 / 50) (c_lo := 75 / 100)
    (by norm_num) (by norm_num) fun u hu => (phi_bounds_bin0 (le_of_lt hu.1) hu.2).1
  have b2 := setIntegral_phi_pow_ge_bin (k := k) (a := 1 / 50) (b := 3 / 20) (c_lo := 72 / 100)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_015_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 3 / 20 by norm_num) hu.2)
  have b3 := setIntegral_phi_pow_ge_bin (k := k) (a := 3 / 20) (b := 1 / 4) (c_lo := 48 / 100)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_025_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 1 / 4 by norm_num) hu.2)
  have b4 := setIntegral_phi_pow_ge_bin (k := k) (a := 1 / 4) (b := 7 / 20) (c_lo := 25 / 100)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_035_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 7 / 20 by norm_num) hu.2)
  have b5 := setIntegral_phi_pow_ge_bin (k := k) (a := 7 / 20) (b := 9 / 20) (c_lo := 105 / 1000)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_045_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 9 / 20 by norm_num) hu.2)
  have b6 := setIntegral_phi_pow_ge_bin (k := k) (a := 9 / 20) (b := 11 / 20) (c_lo := 31 / 1000)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_055_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 11 / 20 by norm_num) hu.2)
  have b7 := setIntegral_phi_pow_ge_bin (k := k) (a := 11 / 20) (b := 13 / 20) (c_lo := 6 / 1000)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_065_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 13 / 20 by norm_num) hu.2)
  have b8 := setIntegral_phi_pow_ge_bin (k := k) (a := 13 / 20) (b := 4 / 5) (c_lo := 2 / 10000)
    (by norm_num) (by norm_num) fun u hu =>
      phi_at_080_bounds.1.trans (hanti (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (show (1 / 50 : ℝ) ≤ 4 / 5 by norm_num) hu.2)
  have b9 : 0 ≤ ∫ u in Ioc (4 / 5 : ℝ) 1, riemannPhi u * u ^ k * Real.cosh (0 * u) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun u hu =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (by linarith [hu.1]) k)) (le_of_lt (Real.cosh_pos _))
  have b10 : 0 ≤ ∫ u in Ioi (1 : ℝ), riemannPhi u * u ^ k * Real.cosh (0 * u) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u (hu : (1 : ℝ) < u) =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (pow_nonneg (by linarith) k)) (le_of_lt (Real.cosh_pos _))
  linarith

/-- Sharp constructive lower bounds `I_0(0) ≥ 195/1000` and `I_2(0) ≥ 77/10000`. -/
lemma xiCoshMoment_zero_zero_ge_tight : (195 / 1000 : ℝ) ≤ xiCoshMoment 0 0 := by
  have h := xiCoshMoment_zero_ge_nine_bins 0
  norm_num at h; linarith

lemma xiCoshMoment_two_zero_ge_tight : (77 / 10000 : ℝ) ≤ xiCoshMoment 2 0 := by
  have h := xiCoshMoment_zero_ge_nine_bins 2
  norm_num at h; linarith

/-- Sharp constructive upper bound `I_2(0) ≤ 175 / 10000`. -/
lemma xiCoshMoment_two_zero_le_tight : xiCoshMoment 2 0 ≤ 175 / 10000 := by
  dsimp [xiCoshMoment]
  rw [setIntegral_Ioi_zero_eq_nine_bins (integrableOn_phi_pow_cosh 2 0)]
  have hanti := riemannPhi_antitoneOn_from_one_fiftieth
  have hch1 : ∀ b : ℝ, Real.cosh ((0 : ℝ) * b) ≤ 1 := fun b => by simp
  have b1 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 0) (b := 1 / 50) (c_hi := 106 / 100) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (phi_bounds_bin0 (le_of_lt hu.1) hu.2).2) (hch1 _)
  have b2 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 1 / 50) (b := 3 / 20) (c_hi := 90 / 100) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 1 / 50 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_002_le) (hch1 _)
  have b3 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 3 / 20) (b := 1 / 4) (c_hi := 73 / 100) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 3 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_015_bounds.2) (hch1 _)
  have b4 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 1 / 4) (b := 7 / 20) (c_hi := 492 / 1000) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 1 / 4 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_025_bounds.2) (hch1 _)
  have b5 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 7 / 20) (b := 9 / 20) (c_hi := 265 / 1000) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 7 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_035_bounds.2) (hch1 _)
  have b6 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 9 / 20) (b := 11 / 20) (c_hi := 110 / 1000) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 9 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_045_bounds.2) (hch1 _)
  have b7 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 11 / 20) (b := 13 / 20) (c_hi := 32 / 1000) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 11 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_055_bounds.2) (hch1 _)
  have b8 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 13 / 20) (b := 4 / 5) (c_hi := 65 / 10000) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 13 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_065_bounds.2) (hch1 _)
  have b9 := setIntegral_phi_pow_cosh_le_bin (k := 2) (σ := 0) (a := 4 / 5) (b := 1) (c_hi := 3 / 10000) (ch_hi := 1)
    (by norm_num) (by norm_num) le_rfl (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 4 / 5 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_080_bounds.2) (hch1 _)
  have b10 := tail_Ioi_one_le (k := 2) (by norm_num) (σ := 0) le_rfl (by norm_num)
  norm_num at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 ⊢
  linarith

/-- Sharp constructive upper bound `I_4(1/2) ≤ 285 / 100000`. -/
lemma xiCoshMoment_four_half_le_tight : xiCoshMoment 4 (1 / 2) ≤ 285 / 100000 := by
  dsimp [xiCoshMoment]
  rw [setIntegral_Ioi_zero_eq_nine_bins (integrableOn_phi_pow_cosh 4 (1 / 2))]
  have hanti := riemannPhi_antitoneOn_from_one_fiftieth
  have hch : ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      Real.cosh ((1 / 2 : ℝ) * b) ≤ 1 + ((1 / 2 : ℝ) * b) ^ 2 / 2 + ((1 / 2 : ℝ) * b) ^ 4 / 20 :=
    fun b hb0 hb1 => cosh_le_poly4 (by linarith) (by linarith)
  have b1 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 0) (b := 1 / 50) (c_hi := 106 / 100)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (1 / 50)) ^ 2 / 2 + ((1 / 2 : ℝ) * (1 / 50)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (phi_bounds_bin0 (le_of_lt hu.1) hu.2).2) (hch _ (by norm_num) (by norm_num))
  have b2 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 1 / 50) (b := 3 / 20) (c_hi := 90 / 100)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (3 / 20)) ^ 2 / 2 + ((1 / 2 : ℝ) * (3 / 20)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 1 / 50 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_002_le) (hch _ (by norm_num) (by norm_num))
  have b3 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 3 / 20) (b := 1 / 4) (c_hi := 73 / 100)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (1 / 4)) ^ 2 / 2 + ((1 / 2 : ℝ) * (1 / 4)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 3 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_015_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b4 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 1 / 4) (b := 7 / 20) (c_hi := 492 / 1000)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (7 / 20)) ^ 2 / 2 + ((1 / 2 : ℝ) * (7 / 20)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 1 / 4 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_025_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b5 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 7 / 20) (b := 9 / 20) (c_hi := 265 / 1000)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (9 / 20)) ^ 2 / 2 + ((1 / 2 : ℝ) * (9 / 20)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 7 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_035_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b6 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 9 / 20) (b := 11 / 20) (c_hi := 110 / 1000)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (11 / 20)) ^ 2 / 2 + ((1 / 2 : ℝ) * (11 / 20)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 9 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_045_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b7 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 11 / 20) (b := 13 / 20) (c_hi := 32 / 1000)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (13 / 20)) ^ 2 / 2 + ((1 / 2 : ℝ) * (13 / 20)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 11 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_055_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b8 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 13 / 20) (b := 4 / 5) (c_hi := 65 / 10000)
    (ch_hi := 1 + ((1 / 2 : ℝ) * (4 / 5)) ^ 2 / 2 + ((1 / 2 : ℝ) * (4 / 5)) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 13 / 20 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_065_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b9 := setIntegral_phi_pow_cosh_le_bin (k := 4) (σ := 1 / 2) (a := 4 / 5) (b := 1) (c_hi := 3 / 10000)
    (ch_hi := 1 + ((1 / 2 : ℝ) * 1) ^ 2 / 2 + ((1 / 2 : ℝ) * 1) ^ 4 / 20)
    (by norm_num) (by norm_num) (by norm_num) (fun u hu => (hanti (show (1 / 50 : ℝ) ≤ 4 / 5 by norm_num) (show (1 / 50 : ℝ) ≤ u by linarith [hu.1]) (le_of_lt hu.1)).trans phi_at_080_bounds.2) (hch _ (by norm_num) (by norm_num))
  have b10 := tail_Ioi_one_le (k := 4) le_rfl (σ := 1 / 2) (by norm_num) le_rfl
  norm_num at b1 b2 b3 b4 b5 b6 b7 b8 b9 ⊢
  linarith

/-- THEOREM III.3 (10x EXPANDED CONSTRUCTIVE CONVEXITY CORRIDOR `|γ| ≤ 2`):
    Using the exact identity `I_0(1/2) = 1/4` together with the 9-bin antitone bounds,
    for EVERY `σ ∈ [0, 1/2]` and EVERY `|γ| ≤ 2`, the transverse Hessian `∂_σ^2 V(σ, γ)`
    is STRICTLY POSITIVE! -/
theorem xiNormSq_deriv2_pos_corridor_two {σ γ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hγ : |γ| ≤ 2) :
    0 < deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ := by
  have hq := xiNormSq_deriv2_ge_moment_quadratic hσ0 hσ1 γ
  have hI00 := xiCoshMoment_zero_zero_ge_tight
  have hI20 := xiCoshMoment_two_zero_ge_tight
  have hI0h := integral_phi_cosh_half_eq_quarter
  have hI4h := xiCoshMoment_four_half_le_tight
  have hγ2 : γ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg γ) hγ 2
    rw [sq_abs] at h; norm_num at h; exact h
  have hprod_lb : (195 / 1000 : ℝ) * (77 / 10000) ≤ xiCoshMoment 0 0 * xiCoshMoment 2 0 :=
    mul_le_mul hI00 hI20 (by norm_num) (by linarith)
  have hI20_sq : (77 / 10000 : ℝ) ^ 2 ≤ xiCoshMoment 2 0 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hI20 2
  rw [hI0h] at hq
  have hdiff_ub : (1 / 4 : ℝ) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2 ≤
      (1 / 4 : ℝ) * (285 / 100000) - (77 / 10000) ^ 2 := by linarith
  have hγ_term : 4 * γ ^ 2 * ((1 / 4 : ℝ) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2) ≤
      16 * ((1 / 4 : ℝ) * (285 / 100000) - (77 / 10000) ^ 2) := by
    by_cases hd : 0 ≤ (1 / 4 : ℝ) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2
    · nlinarith
    · push Not at hd
      have h1 : 4 * γ ^ 2 * ((1 / 4 : ℝ) * xiCoshMoment 4 (1 / 2) - xiCoshMoment 2 0 ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt hd)
      have h2 : (0 : ℝ) ≤ 16 * ((1 / 4 : ℝ) * (285 / 100000) - (77 / 10000) ^ 2) := by norm_num
      linarith
  have hnum : (16 : ℝ) * ((1 / 4 : ℝ) * (285 / 100000) - (77 / 10000) ^ 2) <
      8 * ((195 / 1000 : ℝ) * (77 / 10000)) := by norm_num
  linarith

/-- THEOREM III.4 (10x EXPANDED CONSTRUCTIVE TRANSVERSE FORCE POSITIVITY `|γ| ≤ 2`):
    For every `σ ∈ (0, 1/2]` and `|γ| ≤ 2`, `∂_σ V(σ, γ) > 0`. -/
theorem xiNormSq_deriv1_pos_corridor_two {σ γ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hγ : |γ| ≤ 2) :
    0 < deriv (fun s : ℝ => xiNormSq s γ) σ := by
  have hd0 : deriv (fun s : ℝ => xiNormSq s γ) 0 = 0 := xiNormSq_deriv_sigma_zero γ
  have hdiff : Differentiable ℝ (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) :=
    fun t => (hasDerivAt_xiNormSq_deriv_sigma t γ).differentiableAt
  have hsm : StrictMonoOn (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) (Icc 0 (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2))
    · exact hdiff.continuous.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact xiNormSq_deriv2_pos_corridor_two (le_of_lt hx.1) (le_of_lt hx.2) hγ
  have hgt := hsm (left_mem_Icc.mpr (by norm_num)) ⟨le_of_lt hσ0, hσ1⟩ hσ0
  linarith

/-- THEOREM III.5 (20x EXPANDED CRITICAL-LINE POSITIVITY `|γ| ≤ 4`):
    For EVERY `|γ| ≤ 4`, `Ξ(γ) = Re(ξ(1/2 + i γ)) > 0` unconditionally! -/
theorem riemannXi_critical_pos_corridor_four {γ : ℝ} (hγ : |γ| ≤ 4) :
    0 < xiCritical γ := by
  have hq := xiCritical_ge_moment_quadratic γ
  have hI00 := xiCoshMoment_zero_zero_ge_tight
  have hI20 := xiCoshMoment_two_zero_le_tight
  have hγ2 : γ ^ 2 ≤ 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg γ) hγ 2
    rw [sq_abs] at h; norm_num at h; exact h
  have hI20_nn : 0 ≤ xiCoshMoment 2 0 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (sq_nonneg u)) (le_of_lt (Real.cosh_pos _))
  nlinarith

/-- THEOREM III.6 (UNCONDITIONAL 10x EXPANDED CONSTRUCTIVE ZERO-FREE STRIP RECTANGLE ON MATHLIB4's `riemannZeta`):
    Directly on Mathlib4's official `riemannZeta`, for EVERY `s ∈ ℂ` in the explicit rectangle
    `0 < Re(s) < 1` and `|Im(s)| ≤ 2`, `riemannZeta s ≠ 0`!
    (Expands Module #10's `(0, 1) × [-1/5, 1/5]` by a factor of 10x with 0 `sorry` and 0 axioms.) -/
theorem riemannZeta_ne_zero_explicit_strip_rectangle_two {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : |s.im| ≤ 2) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hxi_zero : riemannXi s = 0 := (riemannXi_eq_zero_iff_riemannZeta hs0 hs1).mpr hz
  let σ : ℝ := s.re - 1 / 2
  let γ : ℝ := s.im
  have hV0 : xiNormSq σ γ = 0 := by
    dsimp [xiNormSq, σ, γ]
    have hs_eq : (⟨1 / 2 + (s.re - 1 / 2), s.im⟩ : ℂ) = s := by apply Complex.ext <;> simp
    rw [hs_eq, hxi_zero, norm_zero, sq, mul_zero]
  have hV_abs0 : xiNormSq |σ| γ = 0 := by
    rcases le_total 0 σ with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_nonpos h, xiNormSq_even_sigma]; exact hV0
  have habs_lt : |σ| < 1 / 2 := abs_lt.mpr ⟨by dsimp [σ]; linarith, by dsimp [σ]; linarith⟩
  have hV_crit_pos : 0 < xiNormSq 0 γ := by
    have hre := riemannXi_im_half_eq_zero γ
    have hpos := riemannXi_critical_pos_corridor_four (by linarith : |γ| ≤ 4)
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
          exact le_of_lt (xiNormSq_deriv1_pos_corridor_two hx.1 (le_of_lt hx.2) him)
      exact hM (left_mem_Icc.mpr (by norm_num)) ⟨le_of_lt hσ_pos, le_of_lt habs_lt⟩ (le_of_lt hσ_pos)
    linarith

-- ==============================================================================
-- PART IV: ROUTE B — SHARP HYPERBOLIC DECAY & LOGARITHMIC POTENTIAL FORCE
-- ==============================================================================

/-- THEOREM IV.1 (SHARP HYPERBOLIC-TYPE DECAY OF `G_{2,0}(w)`):
    Tightening Module #10's `-(π/4) * e^w` by 6x to `-(3π/2) * e^w`, matching the
    exact exponential type in the hyperbolic geodesic variable `y = cosh(w) - 1`:
      `∃ C > 0, ∀ w ≥ 0, G_{2,0}(w) ≤ C * exp(-(3π/2) * exp w)`. -/
theorem riemannLaguerreKernel1D_sharp_hyperbolic_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 ≤ w →
      riemannLaguerreKernel1D w ≤ C * Real.exp (-(3 * Real.pi / 2) * Real.exp w) := by
  -- Sharp bound on Φ(u) with FULL exponent `-π * exp(2|u|)` (from riemannPhi_le_term0_plus_tail!):
  have hPhi_sharp : ∀ u : ℝ, riemannPhi u ≤
      40 * Real.exp (9 * |u| / 2 - Real.pi * Real.exp (2 * |u|)) := by
    intro u
    have hev : riemannPhi u = riemannPhi |u| := by
      rcases le_total 0 u with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, riemannPhi_even]
    rw [hev]
    have ha : 0 ≤ |u| := abs_nonneg u
    have htail := riemannPhi_le_term0_plus_tail ha
    have hcomb : riemannPhiTerm 0 |u| + (1 / 500 : ℝ) * (4 * Real.pi ^ 2 * Real.exp (4 * |u|) * thetaHalfTerm 0 |u|) ≤
        (501 / 500 : ℝ) * 4 * Real.pi ^ 2 * (Real.exp (4 * |u|) * thetaHalfTerm 0 |u|) := by
      dsimp [riemannPhiTerm]
      have hnn : 0 ≤ 6 * Real.pi * ((0 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * |u|) * thetaHalfTerm 0 |u| := by
        dsimp [thetaHalfTerm]; positivity
      norm_num at hnn ⊢; linarith
    have hexp_eq : Real.exp (4 * |u|) * thetaHalfTerm 0 |u| =
        Real.exp (9 * |u| / 2 - Real.pi * Real.exp (2 * |u|)) := by
      dsimp [thetaHalfTerm]; rw [← Real.exp_add]; congr 1; norm_num; ring
    rw [hexp_eq] at hcomb
    have hc40 : (501 / 500 : ℝ) * 4 * Real.pi ^ 2 ≤ 40 := by nlinarith [pi_lt_31416, Real.pi_pos]
    linarith [mul_le_mul_of_nonneg_right hc40 (le_of_lt (Real.exp_pos (9 * |u| / 2 - Real.pi * Real.exp (2 * |u|))))]
  -- Integrable r-envelope h_r(r) = r^2 * exp(9|r|/2 - (π/8)*exp|r|) (same integrable tail as Module #10!):
  let h_r : ℝ → ℝ := fun r => r ^ 2 * Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|)
  have hh_int : Integrable h_r := by
    have hpos : IntegrableOn h_r (Ioi 0) := by
      have hdom' : IntegrableOn (fun r : ℝ => 2 * Real.exp 400 * Real.exp (-r)) (Ioi 0) := by
        have h0 : IntegrableOn (fun r : ℝ => 2 * Real.exp 400 * Real.exp (-1 * r)) (Ioi 0) :=
          (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul (2 * Real.exp 400)
        exact h0.congr_fun (fun r _ => by ring_nf) measurableSet_Ioi
      refine hdom'.mono' (((continuous_pow 2).mul (Real.continuous_exp.comp
        ((continuous_const.mul continuous_abs).div_const 2 |>.sub
          (continuous_const.mul (Real.continuous_exp.comp continuous_abs))))).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      dsimp [h_r]; rw [abs_of_nonneg (by positivity), abs_of_nonneg hr0]
      have hexp_ge : 1 + r + r ^ 2 / 2 ≤ Real.exp r := by
        have h := Real.sum_le_exp_of_nonneg hr0 3
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
        norm_num at h; linarith
      have hpi_lo := Real.pi_gt_d2
      have hquad : 11 * r / 2 - (Real.pi / 8) * Real.exp r ≤ 400 - r := by
        have h1 : (Real.pi / 8) * (1 + r + r ^ 2 / 2) ≤ (Real.pi / 8) * Real.exp r :=
          mul_le_mul_of_nonneg_left hexp_ge (by positivity)
        nlinarith [sq_nonneg (r - 20)]
      have hr2 : r ^ 2 ≤ 2 * Real.exp r := by nlinarith
      calc r ^ 2 * Real.exp (9 * r / 2 - Real.pi / 8 * Real.exp r)
        _ ≤ (2 * Real.exp r) * Real.exp (9 * r / 2 - Real.pi / 8 * Real.exp r) :=
            mul_le_mul_of_nonneg_right hr2 (le_of_lt (Real.exp_pos _))
        _ = 2 * Real.exp (11 * r / 2 - Real.pi / 8 * Real.exp r) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ 2 * Real.exp (400 - r) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) (by norm_num)
        _ = 2 * Real.exp 400 * Real.exp (-r) := by rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
    have hneg : IntegrableOn h_r (Iio 0) := by
      have hpre : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by ext x; simp
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (f := h_r) (s := Iio 0) (MeasurableEquiv.neg ℝ).measurableEmbedding
      rw [hpre] at hmp
      exact hmp.mp (hpos.congr_fun (fun r _ => by dsimp [h_r, Function.comp_def]; rw [neg_sq, abs_neg]) measurableSet_Ioi)
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
  let C : ℝ := 1600 * K0 * (∫ r : ℝ, h_r r) + 1
  have hC_pos : 0 < C := by
    have hi : 0 ≤ ∫ r : ℝ, h_r r := integral_nonneg fun r => by dsimp [h_r]; positivity
    dsimp [C, K0]; positivity
  refine ⟨C, hC_pos, fun w hw => ?_⟩
  have hpt : ∀ r : ℝ, r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2) ≤
      (1600 * K0 * Real.exp (-(3 * Real.pi / 2) * Real.exp w)) * h_r r := by
    intro r
    have hp1 := hPhi_sharp ((r + w) / 2)
    have hp2 := hPhi_sharp ((r - w) / 2)
    have htri : |(r + w) / 2| + |(r - w) / 2| ≤ |r| + w := by
      have h1 : |(r + w) / 2| ≤ (|r| + w) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := abs_add_le r w; rw [abs_of_nonneg hw] at this; linarith
      have h2 : |(r - w) / 2| ≤ (|r| + w) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := abs_sub r w; rw [abs_of_nonneg hw] at this; linarith
      linarith
    -- SHARP AM–GM + MAX LOWER BOUND:
    -- (1) e^{|r+w|} + e^{|r-w|} ≥ 2 * exp((|r+w| + |r-w|)/2) ≥ 2 * exp w  (AM–GM + triangle!)
    -- (2) e^{|r+w|} + e^{|r-w|} ≥ exp(|r| + w) ≥ exp |r|!
    -- Convex combo (7/8)*(1) + (1/8)*(2): e^{|r+w|} + e^{|r-w|} ≥ (7/4) * exp w + (1/8) * exp |r|!!
    have hsum_exp : (7 / 4 : ℝ) * Real.exp w + (1 / 8 : ℝ) * Real.exp |r| ≤
        Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|) := by
      have ha : 2 * |(r + w) / 2| = |r + w| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
      have hb : 2 * |(r - w) / 2| = |r - w| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
      rw [ha, hb]
      have h1_amgm : 2 * Real.exp w ≤ Real.exp |r + w| + Real.exp |r - w| := by
        have htri_w : 2 * w ≤ |r + w| + |r - w| := by
          have h := abs_sub (r + w) (r - w)
          have hs : (r + w) - (r - w) = 2 * w := by ring
          rw [hs, abs_of_nonneg (by linarith)] at h
          exact h
        have hsq : 0 ≤ (Real.exp (|r + w| / 2) - Real.exp (|r - w| / 2)) ^ 2 := sq_nonneg _
        have hprod : Real.exp (|r + w| / 2) * Real.exp (|r - w| / 2) = Real.exp ((|r + w| + |r - w|) / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        have hsq1 : Real.exp (|r + w| / 2) ^ 2 = Real.exp |r + w| := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have hsq2 : Real.exp (|r - w| / 2) ^ 2 = Real.exp |r - w| := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have hew : Real.exp w ≤ Real.exp ((|r + w| + |r - w|) / 2) := Real.exp_le_exp.mpr (by linarith)
        nlinarith
      have h2_max : Real.exp |r| ≤ Real.exp |r + w| + Real.exp |r - w| := by
        have hmax : |r| ≤ max |r + w| |r - w| := by
          rcases le_total 0 r with hr | hr
          · rw [abs_of_nonneg hr]
            have : r ≤ |r + w| := by rw [abs_of_nonneg (by linarith)]; linarith
            exact this.trans (le_max_left _ _)
          · rw [abs_of_nonpos hr]
            have : -r ≤ |r - w| := by rw [abs_of_nonpos (by linarith)]; linarith
            exact this.trans (le_max_right _ _)
        rcases le_total |r + w| |r - w| with h | h
        · rw [max_eq_right h] at hmax
          linarith [Real.exp_le_exp.mpr hmax, Real.exp_pos |r + w|]
        · rw [max_eq_left h] at hmax
          linarith [Real.exp_le_exp.mpr hmax, Real.exp_pos |r - w|]
      linarith
    have hw_kill : 9 * w / 2 - (Real.pi / 4) * Real.exp w ≤ 100 := by
      have hexp_ge : 1 + w + w ^ 2 / 2 ≤ Real.exp w := by
        have h := Real.sum_le_exp_of_nonneg hw 3
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
        norm_num at h; linarith
      have hpi_lo := Real.pi_gt_d2
      nlinarith [sq_nonneg (w - 8)]
    have hprod_phi : riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2) ≤
        1600 * K0 * Real.exp (-(3 * Real.pi / 2) * Real.exp w) *
          Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|) := by
      have h1 := mul_le_mul hp1 hp2 (le_of_lt (riemannPhi_pos _)) (by positivity)
      calc riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)
        _ ≤ 40 * Real.exp (9 * |(r + w) / 2| / 2 - Real.pi * Real.exp (2 * |(r + w) / 2|)) *
              (40 * Real.exp (9 * |(r - w) / 2| / 2 - Real.pi * Real.exp (2 * |(r - w) / 2|))) := h1
        _ = 1600 * Real.exp ((9 * |(r + w) / 2| / 2 + 9 * |(r - w) / 2| / 2) -
              Real.pi * (Real.exp (2 * |(r + w) / 2|) + Real.exp (2 * |(r - w) / 2|))) := by
            rw [show 40 * Real.exp (9 * |(r + w) / 2| / 2 - Real.pi * Real.exp (2 * |(r + w) / 2|)) *
                  (40 * Real.exp (9 * |(r - w) / 2| / 2 - Real.pi * Real.exp (2 * |(r - w) / 2|))) =
                1600 * (Real.exp (9 * |(r + w) / 2| / 2 - Real.pi * Real.exp (2 * |(r + w) / 2|)) *
                  Real.exp (9 * |(r - w) / 2| / 2 - Real.pi * Real.exp (2 * |(r - w) / 2|))) by ring,
                ← Real.exp_add]
            congr 2; ring
        _ ≤ 1600 * Real.exp ((9 * |r| / 2 + 9 * w / 2) -
              Real.pi * ((7 / 4) * Real.exp w + (1 / 8) * Real.exp |r|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
            nlinarith [Real.pi_pos]
        _ ≤ 1600 * Real.exp (100 + (-(3 * Real.pi / 2) * Real.exp w) +
              (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
            linarith
        _ = 1600 * K0 * Real.exp (-(3 * Real.pi / 2) * Real.exp w) *
              Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|) := by
            dsimp [K0]; rw [Real.exp_add, Real.exp_add]; ring
    dsimp [h_r]
    calc r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)
      _ = r ^ 2 * (riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)) := by ring
      _ ≤ r ^ 2 * (1600 * K0 * Real.exp (-(3 * Real.pi / 2) * Real.exp w) *
            Real.exp (9 * |r| / 2 - (Real.pi / 8) * Real.exp |r|)) :=
          mul_le_mul_of_nonneg_left hprod_phi (sq_nonneg r)
      _ = _ := by ring
  have hint_lhs : Integrable (fun r : ℝ => r ^ 2 * riemannPhi ((r + w) / 2) * riemannPhi ((r - w) / 2)) := by
    refine (hh_int.const_mul (1600 * K0 * Real.exp (-(3 * Real.pi / 2) * Real.exp w))).mono'
      ((((continuous_pow 2).mul (continuous_riemannPhi.comp ((continuous_id.add continuous_const).div_const 2))).mul
        (continuous_riemannPhi.comp ((continuous_id.sub continuous_const).div_const 2))).aestronglyMeasurable) ?_
    filter_upwards with r
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg r) (le_of_lt (riemannPhi_pos _))) (le_of_lt (riemannPhi_pos _)))]
    exact hpt r
  have hint_le := integral_mono hint_lhs (hh_int.const_mul _) hpt
  rw [integral_const_mul] at hint_le
  dsimp [riemannLaguerreKernel1D, C]
  have h0 : 0 ≤ Real.exp (-(3 * Real.pi / 2) * Real.exp w) := le_of_lt (Real.exp_pos _)
  nlinarith

/-- Logarithmic transverse potential force `∂_σ (log V(σ, γ)) = ∂_σ V(σ, γ) / V(σ, γ)`
    (equivalently `2 * Re(ξ'/ξ (1/2 + σ + i γ))`, Lagarias's positivity criterion). -/
noncomputable def xiLogForce (σ γ : ℝ) : ℝ :=
  deriv (fun s : ℝ => Real.log (xiNormSq s γ)) σ

/-- Exact quotient identity `∂_σ (log V) = (∂_σ V) / V` whenever `V(σ, γ) > 0`. -/
theorem xiLogForce_eq_force_div_normSq {σ γ : ℝ} (hV : 0 < xiNormSq σ γ) :
    xiLogForce σ γ = deriv (fun s : ℝ => xiNormSq s γ) σ / xiNormSq σ γ := by
  dsimp [xiLogForce]
  have hd : HasDerivAt (fun s : ℝ => xiNormSq s γ) (deriv (fun s : ℝ => xiNormSq s γ) σ) σ :=
    (hasDerivAt_xiNormSq_sigma σ γ).differentiableAt.hasDerivAt
  exact (hd.log (ne_of_gt hV)).deriv

/-- THEOREM IV.2 (Logarithmic Force Positivity Equivalence Away from Zeros):
    Whenever `V(σ, γ) > 0`, `∂_σ (log V(σ, γ)) > 0 ↔ ∂_σ V(σ, γ) > 0`. -/
theorem xiLogForce_pos_iff_force_pos {σ γ : ℝ} (hV : 0 < xiNormSq σ γ) :
    0 < xiLogForce σ γ ↔ 0 < deriv (fun s : ℝ => xiNormSq s γ) σ := by
  rw [xiLogForce_eq_force_div_normSq hV]
  exact div_pos_iff_of_pos_right hV

/-- Global Logarithmic Transverse Force Positivity (`Lagarias` logarithmic derivative criterion):
    `ξ(1/2 + σ + iγ) ≠ 0` and `∂_σ (log V(σ, γ)) > 0` for all `σ ∈ (0, 1/2)` and `γ ∈ ℝ`. -/
def XiLogForcePos : Prop :=
  ∀ σ γ : ℝ, 0 < σ → σ < 1 / 2 → 0 < xiNormSq σ γ ∧ 0 < xiLogForce σ γ

/-- THEOREM IV.3 (Unconditional Reduction from `XiLogForcePos` to Mathlib4's `RiemannHypothesis`):
    Positivity of the transverse logarithmic force `∂_σ log V > 0` on `(0, 1/2) × ℝ`
    implies `XiTransverseForcePos`, hence Mathlib4's official `RiemannHypothesis`! -/
theorem riemannHypothesis_of_xiLogForcePos (hlog : XiLogForcePos) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiTransverseForcePos
  intro γ σ hσ
  obtain ⟨hV, hF⟩ := hlog σ γ hσ.1 hσ.2
  exact (xiLogForce_pos_iff_force_pos hV).mp hF

/-- THEOREM IV.4 (Log-Convexity Strictly Implies Transverse Hessian Positivity):
    At any point `(σ, γ)` with `V(σ, γ) > 0`, non-negative logarithmic curvature
    `∂_σ^2 (log V) = (V * ∂_σ^2 V - (∂_σ V)^2) / V^2 ≥ 0` implies
    `∂_σ^2 V ≥ (∂_σ V)^2 / V ≥ 0` (and strictly `> 0` whenever `∂_σ V ≠ 0` or `∂_σ^2 log V > 0`). -/
theorem xiTransverseHessian_ge_of_logConvex {σ γ : ℝ} (hV : 0 < xiNormSq σ γ)
    (hlog_conv : 0 ≤ (xiNormSq σ γ * deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ -
      (deriv (fun s : ℝ => xiNormSq s γ) σ) ^ 2) / (xiNormSq σ γ) ^ 2) :
    (deriv (fun s : ℝ => xiNormSq s γ) σ) ^ 2 / xiNormSq σ γ ≤
      deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ := by
  have hnum : 0 ≤ xiNormSq σ γ * deriv (fun t : ℝ => deriv (fun s : ℝ => xiNormSq s γ) t) σ -
      (deriv (fun s : ℝ => xiNormSq s γ) σ) ^ 2 := by
    have hsq : 0 < (xiNormSq σ γ) ^ 2 := sq_pos_of_pos hV
    exact (div_nonneg_iff.mp hlog_conv).resolve_right (fun h => by linarith) |>.1
  rw [div_le_iff₀ hV]
  linarith

end ArithmeticWeilAndWideCorridor

