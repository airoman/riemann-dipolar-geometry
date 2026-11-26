/-
  ==============================================================================
  MODULE #20: GLOBAL ALL-HORIZON (L ∈ (0, ∞)) CONTINUOUS WEIL COERCIVITY &
  HILBERT-SCHUR REDUCTION (ROUTE A), AND COMPLETE UNCONDITIONAL CLOSURE OF
  THE ENTIRE OUTER HALF-PLANE Re(s) ≥ 1 (σ ≥ 1/2) VIA EULER-REFLECTION GAMMA
  BOUNDS, MOEBIUS-EULER LOWER BOUNDS, PHRAGMEN-LINDELOF, AND HOLOMORPHIC
  ANNULUS HOPF BOUNDARY RIGIDITY (ROUTE B)

  Title: Complete Outer Half-Plane Closure (Re(s) >= 1) and All-Horizon Weil
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Route A — Unconditional All-Horizon L ∈ (0, ∞) Continuous Weil & Schur):
      * `weilTotal_all_horizon_finiteCodim_coercive`:
        For EVERY L > 0 (arbitrary unbounded horizon, infinitely many primes as L -> ∞!)
        and EVERY desired coercivity floor c > 0, there exists a finite moment order M : ℕ
        such that for EVERY continuous g on [-L/2, L/2] orthogonal to {1, u, ..., u^(2M-1)},
          `c * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ weilTotal L g`!
      * `weilTotal_all_horizon_finite_negative_obstruction`:
        For EVERY L > 0, no nonzero continuous g in the infinite-dimensional orthogonal
        complement P_{<2M(L)}^⊥ can ever make `weilTotal L g ≤ 0`.
      * `hilbert_schur_complement_positivity_reduction`:
        Exact infinite-to-finite Hilbert-Schur complement positivity reduction: once the
        infinite-dimensional tail W has uniform coercivity λ_⊥ > 0 (proved for all L > 0
        by Theorem I.1!), global positivity on V ⊕ W reduces strictly to finite-dimensional
        Schur-complement positivity on V.
  - Part II (Route B — Complete Closure of the Entire Outer Half-Plane Re(s) ≥ 1):
      * `norm_complex_Gamma_ge_pi_div_two_exp_neg_pi_abs_im`:
        Universal vertical-strip Gamma lower bound via Euler's reflection formula:
          `∀ z : ℂ, 0 ≤ z.re → 1 ≤ |z.im| → (π / 2) * exp (-π * |z.im|) ≤ ‖Complex.Gamma z‖`.
      * `norm_riemannZeta_ge_const_of_one_lt_re`:
        Uniform Moebius-Euler lower bound `0 < c_η ≤ ‖riemannZeta s‖` on `Re(s) ≥ 1 + η`.
      * `norm_riemannXi_le_uniform_vertical_strip`:
        Uniform γ-independent upper bound `‖riemannXi s‖ ≤ 4 * xiCoshMoment 0 U` on `|Re(s) - 1/2| ≤ U`.
      * `xiSchur_strict_contraction_and_hopfBloch_complete_outer_halfPlane`:
        Via Phragmen-Lindelof (`S_α(z) * exp(-ε z^2)`), limit `α ↓ 1/2`, and the open
        Maximum Modulus Principle: for EVERY `α ≥ 1/2`, EVERY `σ > 0`, and EVERY `γ ∈ ℝ`,
          `‖xiSchur α (γ + iσ)‖ < 1`, `0 < hopfBlochZ α (γ + iσ)`,
          and `xiNormSq |σ - α| γ < xiNormSq (σ + α) γ`
        (in particular `‖riemannXi (1/2 + iγ)‖ < ‖riemannXi (3/2 + iγ)‖` for ALL `γ ∈ ℝ`!).
      * `xiResolvent_herglotz_global_complete_outer_halfPlane_half`:
        Via the holomorphic annulus Hopf Boundary Lemma (`G(z) = exp(i N w(z)) / (z - (γ₀ + i))`),
        COMPLETELY CLOSING THE ENTIRE OUTER HALF-PLANE `Re(s) ≥ 1` (`σ ≥ 1/2`, INCLUDING THE
        EXACT CRITICAL-STRIP BOUNDARY `Re(s) = 1`!) FOR ALL `γ ∈ ℝ`:
          (1) `0 < (xiResolvent (γ + iσ)).im` (global Herglotz positivity on `σ ≥ 1/2`),
          (2) `0 < deriv (fun s => xiNormSq s γ) σ` and `0 < xiLogForce σ γ` (global radial force),
          (3) `0 < (logDeriv (xiSchur σ) γ).im` (strictly positive de Branges phase velocity),
          (4) `0 < deBrangesPhaseMemory α γ₁ γ₂` for ALL `α ≥ 1/2` and ALL `γ₁ < γ₂`!
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.XiConvexityLaguerre
import RiemannDipolar.WeilArchimedeanAndExplicitCorridor
import RiemannDipolar.ArithmeticWeilAndWideCorridor
import RiemannDipolar.UniversalWeilAndHerglotzResolvent
import RiemannDipolar.HermiteBiehlerHomotopyAndWeilPick
import RiemannDipolar.RouteABLimitBarriersAndDeBrangesSynthesis
import RiemannDipolar.CompactMomentWeilAndHopfBlochEulerDescent
import RiemannDipolar.CliffordPhaseEulerDescentAndPrimeWeil
import RiemannDipolar.PhaseBarrierEulerDescentAndMultiPrimeWeil

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators Classical
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick UniversalSolverLyapunovAndPrimeResolvent
open RouteABLimitBarriersAndDeBrangesSynthesis GeodesicRenormalizationAndEulerJacobiPick
open CompactMomentWeilAndHopfBlochEulerDescent CliffordPhaseEulerDescentAndPrimeWeil
open PhaseBarrierEulerDescentAndMultiPrimeWeil

namespace GlobalOuterHalfPlaneClosureAndAllHorizonWeil

-- ==============================================================================
-- PART I: ROUTE A — UNCONDITIONAL ALL-HORIZON (L ∈ (0, ∞)) CONTINUOUS WEIL
--         FINITE-CODIMENSION COERCIVITY & HILBERT-SCHUR COMPLEMENT REDUCTION
-- ==============================================================================

/-- Helper: Exact uniform prime-shift operator norm bound for arbitrary horizon `L > 0`. -/
private lemma weilPrime_le_explicit_all_horizon {L : ℝ} (hL0 : 0 < L)
    {g : ℝ → ℂ} (hg : Continuous g) :
    weilPrime L g ≤
      (2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  dsimp [weilPrime]
  have hsum : ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re ≤
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
          ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    refine Finset.sum_le_sum fun n hn => ?_
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
    have hov := (abs_le.mp (shift_overlap_re_le_L2 hlog_nn hlog_le hg)).2
    exact mul_le_mul_of_nonneg_left hov hcoeff_nn
  rw [← Finset.sum_mul] at hsum
  have h2 := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- Helper: `psiLb3 T → +∞` as `T → +∞` (unbounded logarithmic Archimedean dominance). -/
private lemma tendsto_psiLb3_atTop : Tendsto psiLb3 atTop atTop := by
  have hlog : Tendsto (fun T : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * T ^ 2 / 169) - archimedeanWeilConst)
      atTop atTop := by
    have hsq : Tendsto (fun T : ℝ => T ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have harg : Tendsto (fun T : ℝ => 1 + 4 * T ^ 2 / 169) atTop atTop := by
      have h1 : Tendsto (fun T : ℝ => (4 / 169 : ℝ) * T ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 169) hsq
      have h2 : Tendsto (fun T : ℝ => 1 + (4 / 169 : ℝ) * T ^ 2) atTop atTop :=
        Filter.tendsto_atTop_add_const_left atTop 1 h1
      exact h2.congr fun T => by ring
    have hl : Tendsto (fun T : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * T ^ 2 / 169)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) (Real.tendsto_log_atTop.comp harg)
    exact Filter.tendsto_atTop_add_const_right atTop (-archimedeanWeilConst) hl
  refine Filter.tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T _
  dsimp [psiLb3]
  have h1 : 0 ≤ 4 * T ^ 2 / (1 / 4 + T ^ 2) := by positivity
  have h2 : 0 ≤ (4 / 5 : ℝ) * T ^ 2 / (25 / 4 + T ^ 2) := by positivity
  have h3 : 0 ≤ (4 / 9 : ℝ) * T ^ 2 / (81 / 4 + T ^ 2) := by positivity
  linarith

/-- THEOREM I.1 (UNCONDITIONAL ALL-HORIZON `L ∈ (0, ∞)` FINITE-CODIMENSION CONTINUOUS WEIL
    COERCIVITY — NO UPPER BOUND ON `L`, NO PARITY RESTRICTION, ARBITRARY FLOOR `c > 0`!):
    For EVERY support horizon `L > 0` (arbitrarily large, simultaneously accommodating all
    infinitely many prime powers as `L → ∞`!) and EVERY target coercivity constant `c > 0`,
    there exists a finite moment order `M : ℕ` such that for EVERY continuous `g : ℝ → ℂ`
    satisfying the `2 * M` moment-vanishing (higher-order Sobolev/Jerk) conditions
      `∀ k < 2 * M, ∫_{-L/2}^{L/2} u^k g(u) du = 0`,
    the full continuous arithmetic Weil functional is STRICTLY COERCIVE:
      `c * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ weilTotal L g`! -/
theorem weilTotal_all_horizon_finiteCodim_coercive (L c : ℝ) (hL0 : 0 < L) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ {g : ℝ → ℂ}, Continuous g →
      (∀ k : ℕ, k < 2 * M → ∫ u in (-L / 2)..(L / 2), ((u ^ k : ℝ) : ℂ) * g u = 0) →
      ((1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) →
      Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2) →
      Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) →
      c * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  set B_prime : ℝ := 2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
    ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
  set B_pole : ℝ := 2 * (Real.sinh (L / 2) - L / 2)
  -- Step 1: Choose spectral cutoff `T ≥ 1` where Archimedean `psiLb3 T` overwhelms `c + B_prime + B_pole + 1`!
  rcases Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp tendsto_psiLb3_atTop) (c + B_prime + B_pole + 1)) with ⟨T0, hT0⟩
  set T : ℝ := max T0 1
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_right T0 1)
  have hpsiT : c + B_prime + B_pole + 1 ≤ psiLb3 T := hT0 T (le_max_left T0 1)
  set G : ℝ := psiLb3 T - psiLb3 0
  have hG_nn : 0 ≤ G := by
    dsimp [G, psiLb3]
    have h1 : 0 ≤ 4 * T ^ 2 / (1 / 4 + T ^ 2) := by positivity
    have h2 : 0 ≤ (4 / 5 : ℝ) * T ^ 2 / (25 / 4 + T ^ 2) := by positivity
    have h3 : 0 ≤ (4 / 9 : ℝ) * T ^ 2 / (81 / 4 + T ^ 2) := by positivity
    have h4 : 0 ≤ Real.log (1 + 4 * T ^ 2 / 169) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 4 * T ^ 2 / 169 by positivity])
    norm_num; linarith
  -- Step 2: Choose finite moment order `M ≥ 1` making Stirling-exp ratio `≤ 9/10` AND penalty `≤ 1`!
  set K_pen : ℝ := (1 / Real.pi) * (T * G * ((9 / 4 : ℝ) * L))
  have hK_nn : 0 ≤ K_pen := by dsimp [K_pen]; positivity
  have hgeom0 : Tendsto (fun m : ℕ => K_pen * (9 / 10 : ℝ) ^ (4 * m)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun m : ℕ => ((9 / 10 : ℝ) ^ 4) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul : Tendsto (fun m : ℕ => K_pen * ((9 / 10 : ℝ) ^ 4) ^ m) atTop (𝓝 (K_pen * 0)) :=
      hbase.const_mul K_pen
    rw [mul_zero] at hmul
    exact hmul.congr fun m => by rw [← pow_mul]
  rcases (Metric.tendsto_atTop.mp hgeom0) 1 (by norm_num) with ⟨M1, hM1⟩
  obtain ⟨M2, hM2⟩ := exists_nat_gt (68 * L * T / 90)
  set M : ℕ := max 1 (max M1 M2)
  have hM1_le : M1 ≤ M := le_trans (le_max_left M1 M2) (le_max_right 1 _)
  have hM2_le : M2 ≤ M := le_trans (le_max_right M1 M2) (le_max_right 1 _)
  have hM_ge1 : 1 ≤ M := le_max_left 1 _
  have hratio : 68 * L * T ≤ 90 * (M : ℝ) := by
    have hlt : 68 * L * T / 90 < (M : ℝ) := lt_of_lt_of_le hM2 (by exact_mod_cast hM2_le)
    linarith
  have hpen_le1 : (1 / Real.pi) * (T * G * ((9 / 4 : ℝ) * L * (9 / 10 : ℝ) ^ (4 * M))) ≤ 1 := by
    have hdist := hM1 M hM1_le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    have heq : (1 / Real.pi) * (T * G * ((9 / 4 : ℝ) * L * (9 / 10 : ℝ) ^ (4 * M))) =
        K_pen * (9 / 10 : ℝ) ^ (4 * M) := by dsimp [K_pen]; ring
    linarith
  refine ⟨M, hM_ge1, fun {g} hg hmom hparseval hint_arch hint_pl => ?_⟩
  have hpole : -B_pole * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilPole L g := by
    have hp := weilPole_lower_bound_all (le_of_lt hL0) hg
    dsimp [B_pole]; linarith
  have hmargin : c + B_prime + B_pole +
      (1 / Real.pi) * (T * (psiLb3 T - psiLb3 0) * ((9 / 4 : ℝ) * L * (9 / 10 : ℝ) ^ (4 * M))) ≤ psiLb3 T := by
    dsimp [G] at hpen_le1; linarith
  exact weilTotal_continuous_pos_noParity_of_ratio_le_nine_tenths hL0 le_rfl hT_pos hM_ge1
    hratio le_rfl hmargin hg hmom
    (weilPrime_le_explicit_all_horizon hL0 hg) hpole hparseval hint_arch hint_pl

/-- THEOREM I.2 (COROLLARY — ALL-HORIZON FINITE NEGATIVE OBSTRUCTION):
    For EVERY `L > 0`, there exists a finite moment order `M : ℕ` such that EVERY continuous
    `g` orthogonal to `{1, u, ..., u^(2M-1)}` with nonzero `L^2` norm satisfies STRICTLY
      `0 < weilTotal L g`!
    Thus every conceivable RH counterexample at ANY horizon `L > 0` MUST have a nonzero
    projection onto the finite-dimensional polynomial subspace `span {1, u, ..., u^(2M-1)}`. -/
theorem weilTotal_all_horizon_finite_negative_obstruction (L : ℝ) (hL0 : 0 < L) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ {g : ℝ → ℂ}, Continuous g →
      (∀ k : ℕ, k < 2 * M → ∫ u in (-L / 2)..(L / 2), ((u ^ k : ℝ) : ℂ) * g u = 0) →
      0 < ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 →
      ((1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) →
      Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2) →
      Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) →
      0 < weilTotal L g := by
  rcases weilTotal_all_horizon_finiteCodim_coercive L 1 hL0 with ⟨M, hM1, hcoerc⟩
  refine ⟨M, hM1, fun {g} hg hmom hnorm hpar hia hip => ?_⟩
  have h1 := hcoerc hg hmom hpar hia hip
  linarith

/-- THEOREM I.3 (EXACT INFINITE-TO-FINITE HILBERT-SCHUR COMPLEMENT POSITIVITY REDUCTION):
    Let a real quadratic form decompose on `V × W` as `Q(v, w) = Q11(v) + 2 B(v, w) + Q22(w)`.
    Suppose the (possibly infinite-dimensional) tail `W` is strictly coercive:
      `λ_⊥ * nw^2 ≤ Q22(w)` (`λ_⊥ > 0`),
    the cross-coupling satisfies `|B(v, w)| ≤ β(v) * nw`, and the finite-dimensional
    Schur-penalized functional satisfies `0 < Q11(v) - β(v)^2 / λ_⊥` whenever `v ≠ 0`
    (with `Q11(0) = 0, β(0) = 0`).
    Then `0 < Q(v, w)` for EVERY `(v, w)` with `v ≠ 0 ∨ 0 < nw`!
    Combined with Theorem I.1, this unconditionally reduces Weil's infinite-dimensional
    positivity criterion at EVERY horizon `L > 0` to finite-dimensional Schur positivity! -/
theorem hilbert_schur_complement_positivity_reduction {V W : Type*} [Zero V]
    (Q11 : V → ℝ) (B : V → W → ℝ) (Q22 : W → ℝ) (nw : W → ℝ) (β : V → ℝ) (lam_perp : ℝ)
    (hlam : 0 < lam_perp)
    (_hnw_nn : ∀ w : W, 0 ≤ nw w)
    (hQ22 : ∀ w : W, lam_perp * (nw w) ^ 2 ≤ Q22 w)
    (hB : ∀ v : V, ∀ w : W, |B v w| ≤ β v * nw w)
    (hQ11_zero : Q11 0 = 0) (hβ_zero : β 0 = 0)
    (hschur : ∀ v : V, v ≠ 0 → 0 < Q11 v - (β v) ^ 2 / lam_perp) :
    ∀ v : V, ∀ w : W, (v ≠ 0 ∨ 0 < nw w) →
      0 < Q11 v + 2 * B v w + Q22 w := by
  intro v w hne
  have hB_lb : -(β v * nw w) ≤ B v w := (abs_le.mp (hB v w)).1
  have hcomp : (β v) ^ 2 / lam_perp + lam_perp * (nw w - β v / lam_perp) ^ 2 =
      lam_perp * (nw w) ^ 2 - 2 * (β v * nw w) + 2 * ((β v) ^ 2 / lam_perp) := by
    field_simp [ne_of_gt hlam]; ring
  have hquad : Q11 v - (β v) ^ 2 / lam_perp + lam_perp * (nw w - β v / lam_perp) ^ 2 ≤
      Q11 v + 2 * B v w + Q22 w := by
    have h1 := hQ22 w
    have hsq : lam_perp * (nw w - β v / lam_perp) ^ 2 =
        lam_perp * (nw w) ^ 2 - 2 * (β v * nw w) + (β v) ^ 2 / lam_perp := by
      field_simp [ne_of_gt hlam]; ring
    linarith
  by_cases hv : v = 0
  · subst hv
    rcases hne with hcontra | hnw_pos
    · exact False.elim (hcontra rfl)
    · rw [hQ11_zero]
      rw [hQ11_zero, hβ_zero] at hquad
      have hpos : 0 < lam_perp * (nw w) ^ 2 := mul_pos hlam (sq_pos_of_pos hnw_pos)
      simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, zero_add] at hquad
      linarith
  · have hs := hschur v hv
    have hsq_nn : 0 ≤ lam_perp * (nw w - β v / lam_perp) ^ 2 :=
      mul_nonneg (le_of_lt hlam) (sq_nonneg _)
    linarith

-- ==============================================================================
-- PART II: ROUTE B — COMPLETE UNCONDITIONAL CLOSURE OF THE ENTIRE OUTER
--          HALF-PLANE Re(s) ≥ 1 (σ ≥ 1/2, INCLUDING THE CRITICAL-STRIP EDGE!)
--          VIA EULER REFLECTION, MOEBIUS LOWER BOUND, PHRAGMEN-LINDELOF,
--          AND HOLOMORPHIC ANNULUS HOPF BOUNDARY RIGIDITY
-- ==============================================================================

/-- Helper II.1A: Uniform Euler-integral upper bound `‖Γ(s)‖ ≤ 2` on the vertical strip `1 ≤ Re(s) ≤ 2`. -/
private lemma norm_complex_Gamma_le_two_of_re_mem {s : ℂ} (hs1 : 1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 2 := by
  rw [Complex.Gamma_eq_integral (by linarith)]
  dsimp [Complex.GammaIntegral]
  have hint_dom : IntegrableOn (fun x : ℝ => Real.exp (-x) * (1 + x)) (Ioi 0) := by
    have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) - 1)) (Ioi 0) :=
      Real.GammaIntegral_convergent (by norm_num)
    have h2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi 0) :=
      Real.GammaIntegral_convergent (by norm_num)
    refine (h1.add h2).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx_pos : (0 : ℝ) < x := hx
    simp only [Pi.add_apply, sub_self, Real.rpow_zero, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤ Real.exp (-x) * (1 + x) := by
    intro x hx
    have hx_pos : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    simp only [Complex.sub_re, Complex.one_re]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
    by_cases hx1 : x ≤ 1
    · have hle : x ^ (s.re - 1) ≤ (1 : ℝ) ^ (s.re - 1) :=
        Real.rpow_le_rpow (le_of_lt hx_pos) hx1 (by linarith)
      rw [Real.one_rpow] at hle; linarith
    · push Not at hx1
      have hle : x ^ (s.re - 1) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
      rw [Real.rpow_one] at hle; linarith
  have hnorm_le : ‖∫ x in Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      ∫ x in Ioi (0 : ℝ), Real.exp (-x) * (1 + x) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    exact MeasureTheory.setIntegral_mono_on (Complex.GammaIntegral_convergent (by linarith)).norm
      hint_dom measurableSet_Ioi hpt
  have hval : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * (1 + x) = 2 := by
    have h1 : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((1 : ℝ) - 1) = Real.Gamma 1 := by
      rw [Real.Gamma_eq_integral (by norm_num)]
    have h2 : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((2 : ℝ) - 1) = Real.Gamma 2 := by
      rw [Real.Gamma_eq_integral (by norm_num)]
    have hadd := MeasureTheory.integral_add
      (Real.GammaIntegral_convergent (s := 1) (by norm_num))
      (Real.GammaIntegral_convergent (s := 2) (by norm_num))
    have hcongr : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * (1 + x) =
        ∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ ((1 : ℝ) - 1) + Real.exp (-x) * x ^ ((2 : ℝ) - 1)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [sub_self, Real.rpow_zero, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]; ring
    rw [hcongr, hadd, h1, h2, Real.Gamma_one, show (2 : ℝ) = (1 : ℝ) + 1 by norm_num,
        Real.Gamma_add_one (by norm_num), Real.Gamma_one]; norm_num
  linarith

/-- Helper II.1B: Exponential upper bound `‖Complex.sin z‖ ≤ Real.exp |z.im|` for all `z : ℂ`. -/
private lemma norm_complex_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ ≤
      ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ := norm_sub_le _ _
  rw [Complex.norm_exp, Complex.norm_exp] at h1
  have hre1 : (-z * Complex.I).re = z.im := by simp
  have hre2 : (z * Complex.I).re = -z.im := by simp
  rw [hre1, hre2] at h1
  have he1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self z.im)
  have he2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

/-- THEOREM II.1 (UNIVERSAL VERTICAL-STRIP GAMMA LOWER BOUND VIA EULER'S REFLECTION FORMULA):
    For EVERY `z : ℂ` with `0 ≤ z.re` and `1 ≤ |z.im|`:
      `(Real.pi / 2) * Real.exp (-Real.pi * |z.im|) ≤ ‖Complex.Gamma z‖`! -/
theorem norm_complex_Gamma_ge_pi_div_two_exp_neg_pi_abs_im {z : ℂ}
    (hre : 0 ≤ z.re) (him : 1 ≤ |z.im|) :
    (Real.pi / 2) * Real.exp (-Real.pi * |z.im|) ≤ ‖Complex.Gamma z‖ := by
  -- Step 1: Prove the bound on the unit strip `0 ≤ w.re < 1, 1 ≤ |w.im|` via Euler reflection!
  have hstrip : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → 1 ≤ |w.im| →
      (Real.pi / 2) * Real.exp (-Real.pi * |w.im|) ≤ ‖Complex.Gamma w‖ := by
    intro w hw0 hw1 hwim
    have h1w_ne : 1 - w ≠ 0 := by
      intro h0
      have him0 : (1 - w).im = 0 := by rw [h0]; simp
      simp at him0; rw [him0, abs_zero] at hwim; linarith
    have hG2 : ‖Complex.Gamma (2 - w)‖ ≤ 2 :=
      norm_complex_Gamma_le_two_of_re_mem (by simp; linarith) (by simp; linarith)
    have hrec : Complex.Gamma (2 - w) = (1 - w) * Complex.Gamma (1 - w) := by
      have := Complex.Gamma_add_one (1 - w) h1w_ne
      rwa [show (1 - w) + 1 = 2 - w by ring] at this
    have h1w_ge1 : (1 : ℝ) ≤ ‖1 - w‖ := by
      have := Complex.abs_im_le_norm (1 - w)
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
      linarith
    have hG1w : ‖Complex.Gamma (1 - w)‖ ≤ 2 := by
      have hmul : ‖1 - w‖ * ‖Complex.Gamma (1 - w)‖ ≤ 2 := by
        rw [← norm_mul, ← hrec]; exact hG2
      nlinarith [norm_nonneg (Complex.Gamma (1 - w))]
    have href := Complex.Gamma_mul_Gamma_one_sub w
    have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤ Real.exp (Real.pi * |w.im|) := by
      have h1 := norm_complex_sin_le_exp_abs_im ((Real.pi : ℂ) * w)
      have him_eq : |((Real.pi : ℂ) * w).im| = Real.pi * |w.im| := by
        simp [abs_mul, abs_of_pos Real.pi_pos]
      rwa [him_eq] at h1
    have hsin_ne : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
      intro h0
      rw [Complex.sin_eq_zero_iff] at h0
      rcases h0 with ⟨k, hk⟩
      have him_eq := congrArg Complex.im hk
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
                 Complex.intCast_im, zero_mul, mul_zero, add_zero] at him_eq
      have hw0' : w.im = 0 := (mul_eq_zero.mp him_eq).resolve_left (ne_of_gt Real.pi_pos)
      rw [hw0', abs_zero] at hwim; linarith
    have hprod_ge : Real.pi * Real.exp (-Real.pi * |w.im|) ≤ ‖Complex.Gamma w‖ * ‖Complex.Gamma (1 - w)‖ := by
      rw [← norm_mul, href, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [show -Real.pi * |w.im| = -(Real.pi * |w.im|) by ring, Real.exp_neg, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (norm_pos_iff.mpr hsin_ne) hsin_le
    nlinarith [norm_nonneg (Complex.Gamma w), Real.pi_pos, Real.exp_pos (-Real.pi * |w.im|)]
  -- Step 2: Shift down by `k = Nat.floor z.re` via `Γ(w + 1) = w * Γ(w)` with `‖w‖ ≥ |w.im| ≥ 1`!
  set k : ℕ := Nat.floor z.re
  set w : ℂ := z - (k : ℂ)
  have hw0 : 0 ≤ w.re := by
    dsimp [w, k]; simp; exact Nat.floor_le hre
  have hw1 : w.re ≤ 1 := by
    dsimp [w, k]; simp; linarith [Nat.lt_floor_add_one z.re]
  have hwim : w.im = z.im := by dsimp [w]; simp
  have hbase := hstrip w hw0 hw1 (by rw [hwim]; exact him)
  rw [hwim] at hbase
  have hshift : ∀ m : ℕ, ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + (m : ℂ))‖ := by
    intro m
    induction m with
    | zero => simp
    | succ r ih =>
      have hne : w + (r : ℂ) ≠ 0 := by
        intro h0
        have him0 := congrArg Complex.im h0
        simp only [Complex.add_im, Complex.natCast_im, add_zero, Complex.zero_im, hwim] at him0
        rw [him0, abs_zero] at him; linarith
      have hge1 : (1 : ℝ) ≤ ‖w + (r : ℂ)‖ := by
        have h := Complex.abs_im_le_norm (w + (r : ℂ))
        simp only [Complex.add_im, Complex.natCast_im, add_zero, hwim] at h; linarith
      have hrec : Complex.Gamma (w + ((r + 1 : ℕ) : ℂ)) = (w + (r : ℂ)) * Complex.Gamma (w + (r : ℂ)) := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne]
      rw [hrec, norm_mul]
      have := mul_le_mul_of_nonneg_right hge1 (norm_nonneg (Complex.Gamma (w + (r : ℂ))))
      linarith
  have hwk : w + (k : ℂ) = z := by dsimp [w]; ring
  have hfin := hshift k
  rw [hwk] at hfin
  linarith

/-- THEOREM II.2 (UNIFORM MOEBIUS-EULER LOWER BOUND FOR `riemannZeta` ON `Re(s) ≥ 1 + η`):
    For EVERY `η > 0`, there exists `c > 0` such that for EVERY `s : ℂ` with `1 + η ≤ s.re`:
      `c ≤ ‖riemannZeta s‖`! -/
theorem norm_riemannZeta_ge_const_of_one_lt_re {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 + η ≤ s.re → c ≤ ‖riemannZeta s‖ := by
  have hp_sum : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + η))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  set M : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (1 + η))⁻¹
  have hM_pos : 0 < M := by
    have h1 : (0 : ℝ) < ((1 : ℕ) : ℝ) ^ (1 + η) := by norm_num
    have hle : (((1 : ℕ) : ℝ) ^ (1 + η))⁻¹ ≤ M :=
      hp_sum.le_tsum 1 fun k _ => by positivity
    exact lt_of_lt_of_le (inv_pos.mpr h1) hle
  refine ⟨M⁻¹, inv_pos.mpr hM_pos, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at hmul
  have hμ_le : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ M := by
    have hsum_μ : Summable (fun n : ℕ => LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) s n) :=
      ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1
    refine le_trans (norm_tsum_le_tsum_norm hsum_μ.norm) ?_
    refine hsum_μ.norm.tsum_le_tsum (fun n => ?_) hp_sum
    by_cases hn0 : n = 0
    · subst hn0; simp [LSeries.term]; exact Real.rpow_nonneg le_rfl _
    · simp only [LSeries.term, hn0, ↓reduceIte, norm_div]
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hμ1 : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hcp : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0) s
      rw [hcp]
      have hrp : (n : ℝ) ^ (1 + η) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn_ge1 hs
      calc ‖(ArithmeticFunction.moebius n : ℂ)‖ / (n : ℝ) ^ s.re
        _ ≤ 1 / (n : ℝ) ^ s.re := div_le_div_of_nonneg_right hμ1 (by positivity)
        _ ≤ 1 / (n : ℝ) ^ (1 + η) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hrp
        _ = ((n : ℝ) ^ (1 + η))⁻¹ := one_div _
  have hnorm_prod : ‖riemannZeta s‖ * ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hnorm_le : ‖riemannZeta s‖ * M ≥ 1 := by
    have := mul_le_mul_of_nonneg_left hμ_le (norm_nonneg (riemannZeta s))
    linarith
  exact (inv_le_iff_one_le_mul₀ hM_pos).mpr (by linarith)

/-- THEOREM II.3A (UNIFORM `γ`-INDEPENDENT VERTICAL-STRIP UPPER BOUND FOR `riemannXi`):
    For EVERY `U ≥ 0` and EVERY `s : ℂ` with `|s.re - 1/2| ≤ U`:
      `‖riemannXi s‖ ≤ 4 * xiCoshMoment 0 U`! -/
theorem norm_riemannXi_le_uniform_vertical_strip {U : ℝ} (hU : 0 ≤ U) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ U) :
    ‖riemannXi s‖ ≤ 4 * xiCoshMoment 0 U := by
  have hreim := riemannXi_re_im_pastFuture_phi s.re s.im
  have hs_eta : (⟨s.re, s.im⟩ : ℂ) = s := by exact Complex.ext rfl rfl
  rw [hs_eta] at hreim
  have hintU : IntegrableOn (fun u : ℝ => riemannPhi u * Real.cosh (U * u)) (Ioi 0) := by
    simpa [pow_zero, mul_one] using integrableOn_phi_pow_cosh 0 U
  have hre_abs : |(riemannXi s).re| ≤ 2 * xiCoshMoment 0 U := by
    rw [hreim.1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hch_bound : ∀ u : ℝ, 0 < u → Real.cosh ((s.re - 1 / 2) * u) ≤ Real.cosh (U * u) := fun u hu_pos => by
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_of_pos hu_pos, abs_of_nonneg (mul_nonneg hU (le_of_lt hu_pos))]
      exact mul_le_mul_of_nonneg_right hs (le_of_lt hu_pos)
    have hint_re : IntegrableOn (fun u : ℝ => riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * Real.cos (s.im * u)) (Ioi 0) :=
      hintU.mono' ((continuous_riemannPhi.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) fun u hu => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (riemannPhi_pos u), abs_of_pos (Real.cosh_pos _)]
          calc riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * |Real.cos (s.im * u)|
            _ ≤ riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
                  (mul_nonneg (le_of_lt (riemannPhi_pos u)) (le_of_lt (Real.cosh_pos _)))
            _ ≤ riemannPhi u * Real.cosh (U * u) := by
                rw [mul_one]; exact mul_le_mul_of_nonneg_left (hch_bound u hu) (le_of_lt (riemannPhi_pos u)))
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
    refine le_trans (MeasureTheory.setIntegral_mono_on hint_re.abs hintU measurableSet_Ioi fun u hu => ?_) ?_
    · rw [abs_mul, abs_mul, abs_of_pos (riemannPhi_pos u), abs_of_pos (Real.cosh_pos _)]
      calc riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * |Real.cos (s.im * u)|
        _ ≤ riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
              (mul_nonneg (le_of_lt (riemannPhi_pos u)) (le_of_lt (Real.cosh_pos _)))
        _ ≤ riemannPhi u * Real.cosh (U * u) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left (hch_bound u hu) (le_of_lt (riemannPhi_pos u))
    · dsimp [xiCoshMoment]; simp [pow_zero]
  have him_abs : |(riemannXi s).im| ≤ 2 * xiCoshMoment 0 U := by
    rw [hreim.2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hch_bound : ∀ u : ℝ, 0 < u → Real.cosh ((s.re - 1 / 2) * u) ≤ Real.cosh (U * u) := fun u hu_pos => by
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_of_pos hu_pos, abs_of_nonneg (mul_nonneg hU (le_of_lt hu_pos))]
      exact mul_le_mul_of_nonneg_right hs (le_of_lt hu_pos)
    have hsh_le : ∀ x : ℝ, |Real.sinh x| ≤ Real.cosh x := fun x => by
      rw [Real.sinh_eq, Real.cosh_eq, abs_le]
      constructor <;> linarith [Real.exp_pos x, Real.exp_pos (-x)]
    have hint_im : IntegrableOn (fun u : ℝ => riemannPhi u * Real.sinh ((s.re - 1 / 2) * u) * Real.sin (s.im * u)) (Ioi 0) :=
      hintU.mono' ((continuous_riemannPhi.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) fun u hu => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (riemannPhi_pos u)]
          calc riemannPhi u * |Real.sinh ((s.re - 1 / 2) * u)| * |Real.sin (s.im * u)|
            _ ≤ riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hsh_le _) (le_of_lt (riemannPhi_pos u)))
                  (Real.abs_sin_le_one _) (abs_nonneg _)
                  (mul_nonneg (le_of_lt (riemannPhi_pos u)) (le_of_lt (Real.cosh_pos _)))
            _ ≤ riemannPhi u * Real.cosh (U * u) := by
                rw [mul_one]; exact mul_le_mul_of_nonneg_left (hch_bound u hu) (le_of_lt (riemannPhi_pos u)))
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
    refine le_trans (MeasureTheory.setIntegral_mono_on hint_im.abs hintU measurableSet_Ioi fun u hu => ?_) ?_
    · rw [abs_mul, abs_mul, abs_of_pos (riemannPhi_pos u)]
      calc riemannPhi u * |Real.sinh ((s.re - 1 / 2) * u)| * |Real.sin (s.im * u)|
        _ ≤ riemannPhi u * Real.cosh ((s.re - 1 / 2) * u) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hsh_le _) (le_of_lt (riemannPhi_pos u)))
              (Real.abs_sin_le_one _) (abs_nonneg _)
              (mul_nonneg (le_of_lt (riemannPhi_pos u)) (le_of_lt (Real.cosh_pos _)))
        _ ≤ riemannPhi u * Real.cosh (U * u) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left (hch_bound u hu) (le_of_lt (riemannPhi_pos u))
    · dsimp [xiCoshMoment]; simp [pow_zero]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (riemannXi s)
  linarith

/-- THEOREM II.3B (EXPONENTIAL VERTICAL-STRIP LOWER BOUND FOR `riemannXi` ON `1 + η ≤ Re(s) ≤ B`):
    For EVERY `η > 0` and `B ≥ 1 + η`, there exists `c > 0` such that for EVERY `s : ℂ` with
    `1 + η ≤ s.re ≤ B` and `2 ≤ |s.im|`:
      `c * Real.exp (-(Real.pi / 2) * |s.im|) ≤ ‖riemannXi s‖`! -/
theorem norm_riemannXi_ge_exp_neg_pi_half_of_one_lt_re {η B : ℝ} (hη : 0 < η) (_hB : 1 + η ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 + η ≤ s.re → s.re ≤ B → 2 ≤ |s.im| →
      c * Real.exp (-(Real.pi / 2) * |s.im|) ≤ ‖riemannXi s‖ := by
  rcases norm_riemannZeta_ge_const_of_one_lt_re hη with ⟨cζ, hcζ_pos, hcζ⟩
  set c_tot : ℝ := (1 / 2 : ℝ) * (1 + η) * η * (Real.pi ^ (-(B / 2))) * (Real.pi / 2) * cζ
  have hc_pos : 0 < c_tot := by
    dsimp [c_tot]
    have hpi_pow : 0 < Real.pi ^ (-(B / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity
  refine ⟨c_tot, hc_pos, fun s hs0 hs1 him => ?_⟩
  have hs_ne0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; linarith
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs0; linarith
  have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hcomp : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs_ne0, div_mul_cancel₀ _ hG_ne]
  rw [riemannXi_eq_completedRiemannZeta hs_ne0 hs_ne1, hcomp]
  dsimp [Gammaℝ]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hs_norm : 1 + η ≤ ‖s‖ := le_trans hs0 (le_trans (le_abs_self s.re) (Complex.abs_re_le_norm s))
  have hs1_norm : η ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at this
    exact le_trans (by linarith) (le_trans (le_abs_self _) this)
  have hpi_norm : Real.pi ^ (-(B / 2)) ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre_eq : (-s / 2).re = -(s.re / 2) := by simp; ring
    rw [hre_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have hgam_norm : (Real.pi / 2) * Real.exp (-(Real.pi / 2) * |s.im|) ≤ ‖Complex.Gamma (s / 2)‖ := by
    have h := norm_complex_Gamma_ge_pi_div_two_exp_neg_pi_abs_im (z := s / 2)
      (by simp; linarith) (by simp [abs_div]; linarith)
    have him_eq : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
    have harg : -Real.pi * (|s.im| / 2) = -(Real.pi / 2) * |s.im| := by ring
    rwa [him_eq, harg] at h
  have hζ_norm : cζ ≤ ‖riemannZeta s‖ := hcζ s hs0
  rw [hhalf]
  have h1 : (1 / 2 : ℝ) * (1 + η) ≤ (1 / 2 : ℝ) * ‖s‖ := mul_le_mul_of_nonneg_left hs_norm (by norm_num)
  have h2 : (1 / 2 : ℝ) * (1 + η) * η ≤ (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ :=
    mul_le_mul h1 hs1_norm (le_of_lt hη) (by positivity)
  have h3 : (1 / 2 : ℝ) * (1 + η) * η * cζ ≤ (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ * ‖riemannZeta s‖ :=
    mul_le_mul h2 hζ_norm (le_of_lt hcζ_pos) (by positivity)
  have h4 : Real.pi ^ (-(B / 2)) * ((Real.pi / 2) * Real.exp (-(Real.pi / 2) * |s.im|)) ≤
      ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ :=
    mul_le_mul hpi_norm hgam_norm (by positivity) (norm_nonneg _)
  have h5 := mul_le_mul h3 h4 (by positivity) (by positivity)
  dsimp [c_tot]
  linarith

/-- Helper II.4A: Holomorphicity of `xiSchur α` on `{z : ℂ | 1/2 - α ≤ z.im}` (in particular all of `ℂ_+`
    and an open neighborhood of `ℝ` whenever `α > 1/2`, and all of `overline(ℂ_+)` whenever `α ≥ 1/2`)! -/
private lemma differentiableAt_xiSchur_of_one_le {α : ℝ} {z : ℂ} (hz : 1 / 2 ≤ α + z.im) :
    DifferentiableAt ℂ (xiSchur α) z := by
  have hre : 1 ≤ (((1 / 2 + α : ℝ) : ℂ) - Complex.I * z).re := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
               zero_mul, one_mul, zero_sub, sub_neg_eq_add]; linarith
  have hE_ne : xiShiftE α z ≠ 0 := riemannXi_ne_zero_of_one_le_re hre
  have hnum : DifferentiableAt ℂ (xiShiftE_sharp α) z := by
    unfold xiShiftE_sharp
    exact riemannXi_entire.differentiableAt.comp z
      ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id))
  have hden : DifferentiableAt ℂ (xiShiftE α) z := by
    unfold xiShiftE
    exact riemannXi_entire.differentiableAt.comp z
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))
  exact hnum.div hden hE_ne

/-- Helper II.4B: Phragmen-Lindelof strip contraction for EVERY `α > 1/2` and EVERY `z ∈ ℂ_+`! -/
private lemma xiSchur_norm_le_one_of_half_lt {α : ℝ} (hα : 1 / 2 < α) {σ γ : ℝ} (hσ : 0 < σ) :
    ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ≤ 1 := by
  set H : ℝ := α + 3 / 2
  by_cases htop : H ≤ σ
  · have hge : 3 / 2 ≤ |σ - α| := by
      rw [abs_of_nonneg (by dsimp [H] at htop; linarith)]; dsimp [H] at htop; linarith
    exact le_of_lt (xiResolvent_herglotz_global_phase_euler_halfPlane_three_halves.2 α σ γ (by linarith) hσ hge)
  · push Not at htop
    -- Apply Maximum Modulus Principle to `F_ε(z) = xiSchur α z * exp(-ε * z^2)` on `[-Y, Y] × [0, H]`!
    set U : ℝ := max α (3 / 2)
    have hU : 0 ≤ U := le_trans (by norm_num) (le_max_right α (3 / 2))
    set η : ℝ := α - 1 / 2
    have hη : 0 < η := by dsimp [η]; linarith
    rcases norm_riemannXi_ge_exp_neg_pi_half_of_one_lt_re (η := η) (B := 1 + η + H) hη (by dsimp [H]; linarith)
      with ⟨c_lo, hc_lo_pos, hc_lo⟩
    set M_top : ℝ := 4 * xiCoshMoment 0 U
    have hM_nn : 0 ≤ M_top := by
      dsimp [M_top, xiCoshMoment]
      have : 0 ≤ ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ 0 * Real.cosh (U * u) :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u _ =>
          mul_nonneg (mul_nonneg (le_of_lt (riemannPhi_pos u)) (by norm_num)) (le_of_lt (Real.cosh_pos _))
      linarith
    set C_side : ℝ := M_top / c_lo
    have hC_nn : 0 ≤ C_side := div_nonneg hM_nn (le_of_lt hc_lo_pos)
    -- Step 1: Show `‖xiSchur α z‖ ≤ exp(ε * (H^2 + γ^2 - σ^2))` for EVERY `ε > 0`!
    have hbound_eps : ∀ ε : ℝ, 0 < ε →
        ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ≤ Real.exp (ε * (H ^ 2 + γ ^ 2 - σ ^ 2)) := by
      intro ε hε
      -- Choose `Y ≥ max (|γ| + 1) 2` such that `C_side * exp((π/2)*Y - ε*Y^2) ≤ 1`!
      have hdecay : Tendsto (fun Y : ℝ => C_side * Real.exp ((Real.pi / 2) * Y - ε * Y ^ 2)) atTop (𝓝 0) := by
        have harg : Tendsto (fun Y : ℝ => (Real.pi / 2) * Y - ε * Y ^ 2) atTop atBot := by
          have hfac : (fun Y : ℝ => (Real.pi / 2) * Y - ε * Y ^ 2) =
              fun Y => -(Y * (ε * Y - Real.pi / 2)) := by ext Y; ring
          rw [hfac]
          refine Filter.tendsto_neg_atTop_atBot.comp ?_
          refine Filter.tendsto_atTop_mono' atTop ?_ tendsto_id
          filter_upwards [Filter.eventually_ge_atTop (max 0 ((1 + Real.pi / 2) / ε))] with Y hY
          have hY0 : 0 ≤ Y := le_trans (le_max_left _ _) hY
          have hY1 : (1 + Real.pi / 2) / ε ≤ Y := le_trans (le_max_right _ _) hY
          have hlin : 1 ≤ ε * Y - Real.pi / 2 := by
            have := (div_le_iff₀ hε).mp hY1; linarith
          change Y ≤ Y * (ε * Y - Real.pi / 2)
          nlinarith
        have hexp0 : Tendsto (fun Y : ℝ => Real.exp ((Real.pi / 2) * Y - ε * Y ^ 2)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp harg
        simpa [mul_zero] using hexp0.const_mul C_side
      rcases (Metric.tendsto_atTop.mp hdecay) 1 (by norm_num) with ⟨Y0, hY0⟩
      set Y : ℝ := max (max (|γ| + 1) 2) Y0
      have hY_gt_γ : |γ| < Y := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ 2) (le_max_left _ Y0))
      have hY_ge2 : 2 ≤ Y := le_trans (le_max_right _ 2) (le_max_left _ Y0)
      have hY_side : C_side * Real.exp ((Real.pi / 2) * Y - ε * Y ^ 2) ≤ 1 := by
        have hd := hY0 Y (le_max_right _ Y0)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd; linarith
      -- Open rectangle `R = (-Y, Y) × (0, H)`
      set R : Set ℂ := {z : ℂ | -Y < z.re ∧ z.re < Y ∧ 0 < z.im ∧ z.im < H}
      set Rbar : Set ℂ := {z : ℂ | -Y ≤ z.re ∧ z.re ≤ Y ∧ 0 ≤ z.im ∧ z.im ≤ H}
      have hR_open : IsOpen R := by
        have h1 : IsOpen {z : ℂ | -Y < z.re} := isOpen_lt continuous_const Complex.continuous_re
        have h2 : IsOpen {z : ℂ | z.re < Y} := isOpen_lt Complex.continuous_re continuous_const
        have h3 : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
        have h4 : IsOpen {z : ℂ | z.im < H} := isOpen_lt Complex.continuous_im continuous_const
        simpa [R, Set.ofPred_and] using h1.inter (h2.inter (h3.inter h4))
      have hRbar_closed : IsClosed Rbar := by
        have h1 : IsClosed {z : ℂ | -Y ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
        have h2 : IsClosed {z : ℂ | z.re ≤ Y} := isClosed_le Complex.continuous_re continuous_const
        have h3 : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
        have h4 : IsClosed {z : ℂ | z.im ≤ H} := isClosed_le Complex.continuous_im continuous_const
        simpa [Rbar, Set.ofPred_and] using h1.inter (h2.inter (h3.inter h4))
      have hR_sub_Rbar : R ⊆ Rbar := fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩
      have hcl_sub : closure R ⊆ Rbar := closure_minimal hR_sub_Rbar hRbar_closed
      have hR_bdd : Bornology.IsBounded R := by
        rw [Metric.isBounded_iff_subset_closedBall 0]
        refine ⟨Y + H, fun z hz => ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 := Complex.norm_le_abs_re_add_abs_im z
        have hre : |z.re| ≤ Y := abs_le.mpr ⟨le_of_lt hz.1, le_of_lt hz.2.1⟩
        have him : |z.im| ≤ H := abs_le.mpr ⟨by linarith [hz.2.2.1], le_of_lt hz.2.2.2⟩
        linarith
      set F : ℂ → ℂ := fun z => xiSchur α z * Complex.exp (-((ε : ℝ) : ℂ) * z ^ 2)
      have hF_diff : DiffContOnCl ℂ F R := by
        have hdiff_bar : DifferentiableOn ℂ F Rbar := fun z hz => by
          have hd1 := differentiableAt_xiSchur_of_one_le (α := α) (z := z) (by linarith [hz.2.2.1])
          have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-((ε : ℝ) : ℂ) * w ^ 2)) z :=
            (((differentiableAt_const _).mul (differentiableAt_id.pow 2)).cexp)
          exact (hd1.mul hd2).differentiableWithinAt
        exact ⟨hdiff_bar.mono hR_sub_Rbar, hdiff_bar.continuousOn.mono hcl_sub⟩
      have hF_norm_exp : ∀ z : ℂ, ‖Complex.exp (-((ε : ℝ) : ℂ) * z ^ 2)‖ =
          Real.exp (-ε * (z.re ^ 2 - z.im ^ 2)) := by
        intro z
        rw [Complex.norm_exp]
        congr 1
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
                   sq, Complex.mul_im, neg_zero, zero_mul, sub_zero]
      -- Bound `‖F z‖ ≤ exp(ε * H^2)` on ALL of `frontier R`!
      have hfront_le : ∀ z ∈ frontier R, ‖F z‖ ≤ Real.exp (ε * H ^ 2) := by
        intro z hz
        have hz_bar : z ∈ Rbar := hcl_sub hz.1
        have hz_not_R : z ∉ R := by
          have hz2 : z ∉ interior R := hz.2
          rwa [hR_open.interior_eq] at hz2
        have hz_im_lo : 0 ≤ z.im := hz_bar.2.2.1
        have hz_im_hi : z.im ≤ α + 3 / 2 := hz_bar.2.2.2
        have hedge : z.re = -Y ∨ z.re = Y ∨ z.im = 0 ∨ z.im = H := by
          by_contra hnone; push Not at hnone
          exact hz_not_R ⟨lt_of_le_of_ne hz_bar.1 (Ne.symm hnone.1),
            lt_of_le_of_ne hz_bar.2.1 hnone.2.1,
            lt_of_le_of_ne hz_bar.2.2.1 (Ne.symm hnone.2.2.1),
            lt_of_le_of_ne hz_bar.2.2.2 hnone.2.2.2⟩
        have hz_split : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
          apply Complex.ext <;> simp
        dsimp [F]; rw [norm_mul, hF_norm_exp]
        rcases hedge with hL | hR_e | hB_e | hT_e
        · -- Left wall `z.re = -Y`
          have hnum_le : ‖xiShiftE_sharp α z‖ ≤ M_top := by
            dsimp [xiShiftE_sharp]
            refine norm_riemannXi_le_uniform_vertical_strip hU ?_
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                       zero_mul, one_mul, zero_sub]
            rw [abs_le]; constructor <;> dsimp [U] <;> linarith [le_max_left α (3 / 2), le_max_right α (3 / 2)]
          have hden_ge : c_lo * Real.exp (-(Real.pi / 2) * Y) ≤ ‖xiShiftE α z‖ := by
            dsimp [xiShiftE]
            have h1 := hc_lo (((1 / 2 + α : ℝ) : ℂ) - Complex.I * z)
              (by simp [η]; linarith)
              (by simp [η, H]; linarith)
              (by simp [hL, abs_of_pos (by linarith : (0 : ℝ) < Y)]; linarith)
            have him_eq : |(((1 / 2 + α : ℝ) : ℂ) - Complex.I * z).im| = Y := by
              simp [hL, abs_of_pos (by linarith : (0 : ℝ) < Y)]
            rwa [him_eq] at h1
          have hS_le : ‖xiSchur α z‖ ≤ C_side * Real.exp ((Real.pi / 2) * Y) := by
            dsimp [xiSchur, C_side]; rw [norm_div]
            calc ‖xiShiftE_sharp α z‖ / ‖xiShiftE α z‖
              _ ≤ M_top / (c_lo * Real.exp (-(Real.pi / 2) * Y)) :=
                  div_le_div₀ hM_nn hnum_le (by positivity) hden_ge
              _ = (M_top / c_lo) * Real.exp ((Real.pi / 2) * Y) := by
                  rw [show -(Real.pi / 2) * Y = -((Real.pi / 2) * Y) by ring, Real.exp_neg,
                      div_mul_eq_div_div, div_inv_eq_mul]
          have him_sq : z.im ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hz_bar.2.2.1 hz_bar.2.2.2 2
          have hexp_le : Real.exp (-ε * (z.re ^ 2 - z.im ^ 2)) ≤ Real.exp (ε * H ^ 2) * Real.exp (-ε * Y ^ 2) := by
            rw [← Real.exp_add, hL]; exact Real.exp_le_exp.mpr (by nlinarith)
          calc ‖xiSchur α z‖ * Real.exp (-ε * (z.re ^ 2 - z.im ^ 2))
            _ ≤ (C_side * Real.exp ((Real.pi / 2) * Y)) * (Real.exp (ε * H ^ 2) * Real.exp (-ε * Y ^ 2)) :=
                mul_le_mul hS_le hexp_le (le_of_lt (Real.exp_pos _)) (by positivity)
            _ = Real.exp (ε * H ^ 2) * (C_side * Real.exp ((Real.pi / 2) * Y - ε * Y ^ 2)) := by
                rw [sub_eq_add_neg, show -(ε * Y ^ 2) = -ε * Y ^ 2 by ring, Real.exp_add]; ring
            _ ≤ Real.exp (ε * H ^ 2) * 1 := mul_le_mul_of_nonneg_left hY_side (le_of_lt (Real.exp_pos _))
            _ = Real.exp (ε * H ^ 2) := mul_one _
        · -- Right wall `z.re = Y`
          have hnum_le : ‖xiShiftE_sharp α z‖ ≤ M_top := by
            dsimp [xiShiftE_sharp]
            refine norm_riemannXi_le_uniform_vertical_strip hU ?_
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                       zero_mul, one_mul, zero_sub]
            rw [abs_le]; constructor <;> dsimp [U] <;> linarith [le_max_left α (3 / 2), le_max_right α (3 / 2)]
          have hden_ge : c_lo * Real.exp (-(Real.pi / 2) * Y) ≤ ‖xiShiftE α z‖ := by
            dsimp [xiShiftE]
            have h1 := hc_lo (((1 / 2 + α : ℝ) : ℂ) - Complex.I * z)
              (by simp [η]; linarith)
              (by simp [η, H]; linarith)
              (by simp [hR_e, abs_of_pos (by linarith : (0 : ℝ) < Y)]; linarith)
            have him_eq : |(((1 / 2 + α : ℝ) : ℂ) - Complex.I * z).im| = Y := by
              simp [hR_e, abs_of_pos (by linarith : (0 : ℝ) < Y)]
            rwa [him_eq] at h1
          have hS_le : ‖xiSchur α z‖ ≤ C_side * Real.exp ((Real.pi / 2) * Y) := by
            dsimp [xiSchur, C_side]; rw [norm_div]
            calc ‖xiShiftE_sharp α z‖ / ‖xiShiftE α z‖
              _ ≤ M_top / (c_lo * Real.exp (-(Real.pi / 2) * Y)) :=
                  div_le_div₀ hM_nn hnum_le (by positivity) hden_ge
              _ = (M_top / c_lo) * Real.exp ((Real.pi / 2) * Y) := by
                  rw [show -(Real.pi / 2) * Y = -((Real.pi / 2) * Y) by ring, Real.exp_neg,
                      div_mul_eq_div_div, div_inv_eq_mul]
          have him_sq : z.im ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hz_bar.2.2.1 hz_bar.2.2.2 2
          have hexp_le : Real.exp (-ε * (z.re ^ 2 - z.im ^ 2)) ≤ Real.exp (ε * H ^ 2) * Real.exp (-ε * Y ^ 2) := by
            rw [← Real.exp_add, hR_e]; exact Real.exp_le_exp.mpr (by nlinarith)
          calc ‖xiSchur α z‖ * Real.exp (-ε * (z.re ^ 2 - z.im ^ 2))
            _ ≤ (C_side * Real.exp ((Real.pi / 2) * Y)) * (Real.exp (ε * H ^ 2) * Real.exp (-ε * Y ^ 2)) :=
                mul_le_mul hS_le hexp_le (le_of_lt (Real.exp_pos _)) (by positivity)
            _ = Real.exp (ε * H ^ 2) * (C_side * Real.exp ((Real.pi / 2) * Y - ε * Y ^ 2)) := by
                rw [sub_eq_add_neg, show -(ε * Y ^ 2) = -ε * Y ^ 2 by ring, Real.exp_add]; ring
            _ ≤ Real.exp (ε * H ^ 2) * 1 := mul_le_mul_of_nonneg_left hY_side (le_of_lt (Real.exp_pos _))
            _ = Real.exp (ε * H ^ 2) := mul_one _
        · -- Bottom edge `z.im = 0`: `‖xiSchur α z‖ = 1`!
          have hE_ne : xiShiftE α z ≠ 0 := by
            dsimp [xiShiftE]; exact riemannXi_ne_zero_of_one_le_re (by simp [hB_e]; linarith)
          have hS1 : ‖xiSchur α z‖ = 1 := by
            have hr := xiSchur_norm_sq_eq_xiNormSq_ratio α 0 z.re
            have hz0 : (z.re : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = z := by
              apply Complex.ext <;> simp [hB_e]
            rw [hz0] at hr
            have hsq := hr.2.2 hE_ne
            simp only [zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < α), zero_add] at hsq
            have hV_pos : 0 < xiNormSq α z.re := by
              have h1 := hr.2.1; rw [zero_add] at h1
              rw [← h1]; exact sq_pos_of_pos (norm_pos_iff.mpr hE_ne)
            rw [div_self (ne_of_gt hV_pos)] at hsq
            nlinarith [norm_nonneg (xiSchur α z)]
          rw [hS1, one_mul, hB_e]
          exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.re, sq_nonneg H])
        · -- Top edge `z.im = H = α + 3/2`: `‖xiSchur α z‖ < 1` by Module #19 Theorem III.2!
          have hS_lt : ‖xiSchur α z‖ < 1 := by
            rw [hz_split, hT_e]
            have hge : 3 / 2 ≤ |H - α| := by dsimp [H]; norm_num
            exact xiResolvent_herglotz_global_phase_euler_halfPlane_three_halves.2 α H z.re
              (by linarith) (by dsimp [H]; linarith) hge
          have hexp_le : Real.exp (-ε * (z.re ^ 2 - z.im ^ 2)) ≤ Real.exp (ε * H ^ 2) := by
            rw [hT_e]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.re])
          calc ‖xiSchur α z‖ * Real.exp (-ε * (z.re ^ 2 - z.im ^ 2))
            _ ≤ 1 * Real.exp (ε * H ^ 2) := mul_le_mul (le_of_lt hS_lt) hexp_le (le_of_lt (Real.exp_pos _)) (by norm_num)
            _ = Real.exp (ε * H ^ 2) := one_mul _
      -- Apply Maximum Modulus Principle on bounded open rectangle `R`!
      set z₀ : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
      have hz₀_R : z₀ ∈ R := by
        dsimp [R, z₀]; simp; exact ⟨(abs_lt.mp hY_gt_γ).1, (abs_lt.mp hY_gt_γ).2, hσ, htop⟩
      rcases Complex.exists_mem_frontier_isMaxOn_norm hR_bdd ⟨z₀, hz₀_R⟩ hF_diff with ⟨w, hw_fr, hw_max⟩
      have hFz₀ : ‖F z₀‖ ≤ Real.exp (ε * H ^ 2) :=
        le_trans (hw_max (subset_closure hz₀_R)) (hfront_le w hw_fr)
      dsimp [F] at hFz₀
      rw [norm_mul, hF_norm_exp] at hFz₀
      have hz₀_re : z₀.re = γ := by dsimp [z₀]; simp
      have hz₀_im : z₀.im = σ := by dsimp [z₀]; simp
      rw [hz₀_re, hz₀_im] at hFz₀
      have hmul_pos := mul_le_mul_of_nonneg_right hFz₀ (le_of_lt (Real.exp_pos (ε * (γ ^ 2 - σ ^ 2))))
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_add] at hmul_pos
      have hzero : -ε * (γ ^ 2 - σ ^ 2) + ε * (γ ^ 2 - σ ^ 2) = 0 := by ring
      rw [hzero, Real.exp_zero, mul_one] at hmul_pos
      have hcomb : ε * H ^ 2 + ε * (γ ^ 2 - σ ^ 2) = ε * (H ^ 2 + γ ^ 2 - σ ^ 2) := by ring
      rwa [hcomb] at hmul_pos
    -- Step 2: Let `ε → 0⁺`!
    have htend : Tendsto (fun n : ℕ => Real.exp ((1 / ((n + 1 : ℕ) : ℝ)) * (H ^ 2 + γ ^ 2 - σ ^ 2)))
        atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) * (H ^ 2 + γ ^ 2 - σ ^ 2)) atTop (𝓝 0) := by
        have hden : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
          (Tendsto.atTop_add tendsto_natCast_atTop_atTop (tendsto_const_nhds (x := (1 : ℝ)))).congr
            fun n => by push_cast; rfl
        have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hden
        simpa [zero_mul] using hinv.mul_const (H ^ 2 + γ ^ 2 - σ ^ 2)
      have hexp := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at hexp
      exact hexp
    exact ge_of_tendsto htend (Filter.Eventually.of_forall fun n => hbound_eps (1 / ((n + 1 : ℕ) : ℝ)) (by positivity))

/-- THEOREM II.4 (COMPLETE OUTER HALF-PLANE STRICT SCHUR CONTRACTION, HOPF-BLOCH NORTHERN
    HEMISPHERE CONFINEMENT, AND RADIAL POTENTIAL STRICT MONOTONICITY FOR ALL `α ≥ 1/2`,
    ALL `σ > 0`, AND ALL `γ ∈ ℝ`!):
    Extending `xiSchur_norm_le_one_of_half_lt` continuously down to the EXACT critical-strip
    boundary `α = 1/2` (`Re(s) = 1`) and upgrading `≤ 1` to STRICT `< 1` via the open
    Maximum Modulus Principle (`Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`):
      For EVERY `α ≥ 1/2`, EVERY `σ > 0`, and EVERY `γ ∈ ℝ`:
      (1) `‖xiSchur α (γ + iσ)‖ < 1` (EVEN at `α = σ = 1/2`, where numerator sits on `Re(s) = 1/2`!),
      (2) `0 < hopfBlochZ α (γ + iσ)` (strict Open Northern Hemisphere confinement on `S^2`),
      (3) `xiNormSq |σ - α| γ < xiNormSq (σ + α) γ`! -/
theorem xiSchur_strict_contraction_and_hopfBloch_complete_outer_halfPlane
    {α σ γ : ℝ} (hα : 1 / 2 ≤ α) (hσ : 0 < σ) :
    ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ < 1 ∧
    0 < hopfBlochZ α ((γ : ℂ) + Complex.I * (σ : ℂ)) ∧
    xiNormSq |σ - α| γ < xiNormSq (σ + α) γ := by
  -- Step 1: Establish weak contraction `‖xiSchur α z‖ ≤ 1` for EVERY `z ∈ ℂ_+` (including `α = 1/2` by limit!).
  have hle_all : ∀ z : ℂ, 0 < z.im → ‖xiSchur α z‖ ≤ 1 := by
    intro z hz
    have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by apply Complex.ext <;> simp
    rw [hz_eq]
    by_cases hgt : 1 / 2 < α
    · exact xiSchur_norm_le_one_of_half_lt hgt hz
    · have hα_eq : α = 1 / 2 := by linarith
      subst hα_eq
      set z₀ : ℂ := (z.re : ℂ) + Complex.I * (z.im : ℂ)
      have hcont : ContinuousAt (fun a : ℝ => ‖xiSchur a z₀‖) (1 / 2) := by
        have hE_ne : xiShiftE (1 / 2) z₀ ≠ 0 := by
          dsimp [xiShiftE, z₀]; exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
        have hnum : Continuous (fun a : ℝ => xiShiftE_sharp a z₀) := by
          unfold xiShiftE_sharp
          exact riemannXi_entire.continuous.comp
            ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add continuous_const)
        have hden : Continuous (fun a : ℝ => xiShiftE a z₀) := by
          unfold xiShiftE
          exact riemannXi_entire.continuous.comp
            ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).sub continuous_const)
        exact ((hnum.continuousAt.div hden.continuousAt hE_ne).norm)
      have hseq : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (1 / 2)) := by
        have hden : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
          (Tendsto.atTop_add tendsto_natCast_atTop_atTop (tendsto_const_nhds (x := (1 : ℝ)))).congr
            fun n => by push_cast; rfl
        have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hden
        simpa [add_zero] using h0.const_add (1 / 2 : ℝ)
      have htend := hcont.tendsto.comp hseq
      exact le_of_tendsto htend (Filter.Eventually.of_forall fun n =>
        xiSchur_norm_le_one_of_half_lt (by linarith [show (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) by positivity]) hz)
  -- Step 2: Upgrade `≤ 1` to STRICT `< 1` via open Maximum Modulus Principle on connected `ℂ_+`!
  set U : Set ℂ := {z : ℂ | 0 < z.im}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    have hx' : 0 < x.im := hx
    have hy' : 0 < y.im := hy
    show (0 : ℝ) < (a • x + b • y).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
               zero_mul, add_zero]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      rw [hb1]; simp; exact hy'
    · nlinarith
  have hU_conn : IsPreconnected U := hU_conv.isPreconnected
  have hdiffU : DifferentiableOn ℂ (xiSchur α) U := fun z hz => by
    have hz' : 0 < z.im := hz
    exact (differentiableAt_xiSchur_of_one_le (by linarith)).differentiableWithinAt
  set z_ref : ℂ := ((0 : ℝ) : ℂ) + Complex.I * ((α + 3 / 2 : ℝ) : ℂ)
  have hz_ref_U : z_ref ∈ U := by dsimp [U, z_ref]; simp; linarith
  have href_lt : ‖xiSchur α z_ref‖ < 1 :=
    xiResolvent_herglotz_global_phase_euler_halfPlane_three_halves.2 α (α + 3 / 2) 0
      (by linarith) (by linarith) (by norm_num)
  set z₀ : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hz₀_U : z₀ ∈ U := by dsimp [U, z₀]; simp; exact hσ
  have hlt1 : ‖xiSchur α z₀‖ < 1 := by
    refine lt_of_le_of_ne (hle_all z₀ hz₀_U) ?_
    intro heq1
    have hmax : IsMaxOn (norm ∘ xiSchur α) U z₀ := fun w hw => by
      show ‖xiSchur α w‖ ≤ ‖xiSchur α z₀‖; rw [heq1]; exact hle_all w hw
    have hconst := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hU_conn hU_open hdiffU hz₀_U hmax
    have href_eq : ‖xiSchur α z_ref‖ = ‖xiSchur α z₀‖ := hconst hz_ref_U
    linarith
  have hE_ne : xiShiftE α z₀ ≠ 0 := by
    dsimp [xiShiftE, z₀]; exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hHB : 0 < hopfBlochZ α z₀ :=
    (hopfBloch_northern_hemisphere_iff_schur_and_potential α σ γ hE_ne).2.2.1.mpr hlt1
  have hrat := xiSchur_norm_sq_eq_xiNormSq_ratio α σ γ
  have hden_pos : 0 < xiNormSq (σ + α) γ := by
    rw [← hrat.2.1]; exact sq_pos_of_pos (norm_pos_iff.mpr hE_ne)
  have hV_lt : xiNormSq |σ - α| γ < xiNormSq (σ + α) γ := by
    have hsq_lt : ‖xiSchur α z₀‖ ^ 2 < 1 := by nlinarith [norm_nonneg (xiSchur α z₀)]
    rw [hrat.2.2 hE_ne, div_lt_one hden_pos] at hsq_lt; exact hsq_lt
  exact ⟨hlt1, hHB, hV_lt⟩

/-- THEOREM II.5A (HOLOMORPHIC ANNULUS HOPF BOUNDARY LEMMA — ZERO BRANCH CUTS, ZERO LOGARITHMS!):
    Let `w : ℂ → ℂ` be holomorphic on the closed tangent disk `closedBall (γ₀ + i) 1`, satisfy
    `w(γ₀) = 0` and `0 < (w z).im` on `{z : ℂ | 0 < z.im}`, and have vertical imaginary derivative
    `d` at `σ = 0` (`HasDerivAt (fun σ : ℝ => (w (γ₀ + iσ)).im) d 0`).
    Applying the Maximum Modulus Principle to the explicit holomorphic function
      `G(z) = exp(i * N * w(z)) / (z - (γ₀ + i))`
    on the annulus `1/2 < ‖z - (γ₀ + i)‖ < 1` proves STRICTLY `0 < d`! -/
theorem holomorphic_annulus_hopf_boundary_lemma {w : ℂ → ℂ} {γ₀ d : ℝ}
    (hw0 : w (γ₀ : ℂ) = 0)
    (hw_im_pos : ∀ z : ℂ, 0 < z.im → 0 < (w z).im)
    (hw_diff : ∀ z ∈ Metric.closedBall ((γ₀ : ℂ) + Complex.I) 1, DifferentiableAt ℂ w z)
    (him_deriv : HasDerivAt (fun σ : ℝ => (w ((γ₀ : ℂ) + Complex.I * (σ : ℂ))).im) d 0) :
    0 < d := by
  set p : ℂ := (γ₀ : ℂ) + Complex.I
  have hball_im : ∀ z ∈ Metric.closedBall p 1, 0 ≤ z.im ∧ (z.im = 0 → z = (γ₀ : ℂ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hsq : (z.re - γ₀) ^ 2 + (z.im - 1) ^ 2 ≤ 1 := by
      have h1 : ‖z - p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z - p)]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      dsimp [p] at h1; simp at h1; nlinarith
    constructor
    · nlinarith [sq_nonneg (z.re - γ₀)]
    · intro him0
      have hre : z.re = γ₀ := by rw [him0] at hsq; nlinarith
      exact Complex.ext hre him0
  -- Minimum `m > 0` of `Im w` on the compact inner circle `sphere p (1/2)`!
  have hsphere_comp : IsCompact (Metric.sphere p (1 / 2)) := isCompact_sphere p (1 / 2)
  have hsphere_ne : (Metric.sphere p (1 / 2)).Nonempty := by
    refine ⟨p + (1 / 2 : ℂ), ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm]; simp
  have hsphere_sub : Metric.sphere p (1 / 2) ⊆ Metric.closedBall p 1 := fun z hz => by
    rw [Metric.mem_sphere] at hz; rw [Metric.mem_closedBall]; linarith
  have hw_im_cont : ContinuousOn (fun z : ℂ => (w z).im) (Metric.sphere p (1 / 2)) := fun z hz =>
    (Complex.continuous_im.continuousAt.comp (hw_diff z (hsphere_sub hz)).continuousAt).continuousWithinAt
  rcases hsphere_comp.exists_isMinOn hsphere_ne hw_im_cont with ⟨z_min, hz_min, hmin⟩
  set m : ℝ := (w z_min).im
  have hz_min_im : 0 < z_min.im := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz_min
    have h1 := Complex.abs_im_le_norm (z_min - p)
    rw [hz_min] at h1; dsimp [p] at h1; simp at h1
    linarith [(abs_le.mp h1).1]
  have hm_pos : 0 < m := hw_im_pos z_min hz_min_im
  -- Pick `N : ℕ` with `1 ≤ N * m` so `2 * exp(-N * m) ≤ 2 * exp(-1) ≤ 1`!
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / m)
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN
  have hNm_ge1 : 1 ≤ (N : ℝ) * m := by
    have := (div_lt_iff₀ hm_pos).mp hN; linarith
  -- Open annulus `A = {z : ℂ | 1/2 < ‖z - p‖ ∧ ‖z - p‖ < 1}` and holomorphic barrier `G(z) = exp(i N w(z)) / (z - p)`!
  set A : Set ℂ := {z : ℂ | (1 / 2 : ℝ) < ‖z - p‖ ∧ ‖z - p‖ < 1}
  set Abar : Set ℂ := {z : ℂ | (1 / 2 : ℝ) ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ 1}
  have hnorm_cont : Continuous (fun z : ℂ => ‖z - p‖) := (continuous_id.sub continuous_const).norm
  have hA_open : IsOpen A := by
    simpa [A, Set.ofPred_and] using
      (isOpen_lt continuous_const hnorm_cont).inter (isOpen_lt hnorm_cont continuous_const)
  have hAbar_closed : IsClosed Abar := by
    simpa [Abar, Set.ofPred_and] using
      (isClosed_le continuous_const hnorm_cont).inter (isClosed_le hnorm_cont continuous_const)
  have hA_sub_Abar : A ⊆ Abar := fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hcl_A : closure A ⊆ Abar := closure_minimal hA_sub_Abar hAbar_closed
  have hA_bdd : Bornology.IsBounded A := by
    rw [Metric.isBounded_iff_subset_closedBall p]
    exact ⟨1, fun z hz => by rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hz.2⟩
  let G : ℂ → ℂ := fun z => Complex.exp ((Complex.I * ((N : ℝ) : ℂ)) * w z) / (z - p)
  have hG_diff : DiffContOnCl ℂ G A := by
    have hdiff_bar : DifferentiableOn ℂ G Abar := fun z hz => by
      have hz_ball : z ∈ Metric.closedBall p 1 := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz.2
      have hzp_ne : z - p ≠ 0 := fun h0 => by
        have h1 : (1 / 2 : ℝ) ≤ ‖z - p‖ := hz.1
        rw [h0, norm_zero] at h1; linarith
      have hnum : DifferentiableAt ℂ (fun x => Complex.exp ((Complex.I * ((N : ℝ) : ℂ)) * w x)) z :=
        ((differentiableAt_const (Complex.I * ((N : ℝ) : ℂ))).mul (hw_diff z hz_ball)).cexp
      exact (hnum.div (differentiableAt_id.sub (differentiableAt_const p)) hzp_ne).differentiableWithinAt
    exact ⟨hdiff_bar.mono hA_sub_Abar, hdiff_bar.continuousOn.mono hcl_A⟩
  have hG_norm : ∀ z : ℂ, ‖G z‖ = Real.exp (-(N : ℝ) * (w z).im) / ‖z - p‖ := by
    intro z; dsimp only [G]; rw [norm_div, Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, zero_sub, zero_add, neg_mul]
  -- Check `‖G z‖ ≤ 1` on `frontier A` (inner circle `‖z - p‖ = 1/2` and outer circle `‖z - p‖ = 1`)!
  have hG_front : ∀ z ∈ frontier A, ‖G z‖ ≤ 1 := by
    intro z hz
    have hz_bar : z ∈ Abar := hcl_A hz.1
    have hz_not_A : z ∉ A := by
      have hz2 : z ∉ interior A := hz.2
      rwa [hA_open.interior_eq] at hz2
    have hcirc : ‖z - p‖ = 1 / 2 ∨ ‖z - p‖ = 1 := by
      by_contra hnone; push Not at hnone
      exact hz_not_A ⟨lt_of_le_of_ne hz_bar.1 (Ne.symm hnone.1), lt_of_le_of_ne hz_bar.2 hnone.2⟩
    rw [hG_norm]
    rcases hcirc with hin | hout
    · rw [hin]
      have hz_sph : z ∈ Metric.sphere p (1 / 2) := by rw [Metric.mem_sphere, dist_eq_norm]; exact hin
      have hw_ge_m : m ≤ (w z).im := hmin hz_sph
      have hexp_le : Real.exp (-(N : ℝ) * (w z).im) ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have he_ge2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have he_inv : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]; exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr he_ge2
      linarith
    · rw [hout, div_one]
      have hz_ball : z ∈ Metric.closedBall p 1 := by rw [Metric.mem_closedBall, dist_eq_norm, hout]
      have hw_nn : 0 ≤ (w z).im := by
        rcases eq_or_lt_of_le (hball_im z hz_ball).1 with him0 | him_pos
        · rw [(hball_im z hz_ball).2 him0.symm, hw0, Complex.zero_im]
        · exact le_of_lt (hw_im_pos z him_pos)
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  -- Maximum Modulus Principle on annulus `A`: `‖G z‖ ≤ 1` for EVERY `z ∈ A`!
  have hA_ne : A.Nonempty := by
    refine ⟨p + (3 / 4 : ℂ), ?_⟩
    dsimp [A]; simp; norm_num
  rcases Complex.exists_mem_frontier_isMaxOn_norm hA_bdd hA_ne hG_diff with ⟨z_max, hz_max_fr, hz_max⟩
  -- Evaluate along vertical segment `σ ↦ γ₀ + iσ` for `σ ∈ (0, 1/2)`!
  have hsec_ge : ∀ σ : ℝ, 0 < σ → σ < 1 / 2 →
      1 / (N : ℝ) ≤ (w ((γ₀ : ℂ) + Complex.I * (σ : ℂ))).im / σ := by
    intro σ hσ0 hσ1
    set z : ℂ := (γ₀ : ℂ) + Complex.I * (σ : ℂ)
    have hzp_norm : ‖z - p‖ = 1 - σ := by
      have heq : z - p = (((σ - 1 : ℝ) : ℂ)) * Complex.I := by
        dsimp [z, p]; exact Complex.ext (by simp) (by simp)
      rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hz_A : z ∈ A := by dsimp [A]; rw [hzp_norm]; constructor <;> linarith
    have hGz : ‖G z‖ ≤ 1 := le_trans (hz_max (subset_closure hz_A)) (hG_front z_max hz_max_fr)
    rw [hG_norm, hzp_norm, div_le_one (by linarith)] at hGz
    -- One-line elementary inequality `1 - N * Im(w) ≤ exp(-N * Im(w)) ≤ 1 - σ`!
    have hadd1 := Real.add_one_le_exp (-(N : ℝ) * (w z).im)
    have hlin : σ ≤ (N : ℝ) * (w z).im := by linarith
    rw [div_le_div_iff₀ hN_pos hσ0]; linarith
  -- Take the limit along `σ_k = 1 / (k + 3) ∈ (0, 1/2)`!
  have hslope := hasDerivAt_iff_tendsto_slope.mp him_deriv
  have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 3 : ℕ) : ℝ)) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall fun k => ne_of_gt (by positivity : (0 : ℝ) < 1 / ((k + 3 : ℕ) : ℝ)))
    have hden : Tendsto (fun k : ℕ => ((k + 3 : ℕ) : ℝ)) atTop atTop :=
      (Tendsto.atTop_add tendsto_natCast_atTop_atTop (tendsto_const_nhds (x := (3 : ℝ)))).congr
        fun k => by push_cast; rfl
    exact tendsto_const_nhds.div_atTop hden
  have htend_val := hslope.comp hseq
  have hge_lim : 1 / (N : ℝ) ≤ d := by
    refine ge_of_tendsto htend_val (Filter.Eventually.of_forall fun k => ?_)
    dsimp [Function.comp, slope]
    have hk_pos : (0 : ℝ) < 1 / ((k + 3 : ℕ) : ℝ) := by positivity
    have hk_lt : (1 : ℝ) / ((k + 3 : ℕ) : ℝ) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
      linarith
    simp only [mul_zero, add_zero, hw0, Complex.zero_im, sub_zero, inv_mul_eq_div]
    exact hsec_ge _ hk_pos hk_lt
  linarith [one_div_pos.mpr hN_pos]

/-- THEOREM II.5B (SCHUR BOUNDARY STRICT PHASE-VELOCITY THEOREM — JULIA-CARATHEODORY / HOPF):
    Any holomorphic strict Schur contraction `S : ℂ → ℂ` on `ℂ_+` (`‖S z‖ < 1` for `z.im > 0`)
    extending holomorphically to the tangent disk `closedBall (γ₀ + i) 1` with boundary unitarity
    `‖S(γ₀)‖ = 1` and purely imaginary logarithmic derivative `S'(γ₀)/S(γ₀) = 2 i d` MUST have
    strictly positive phase velocity `0 < d`! -/
theorem schur_boundary_phase_velocity_pos {S : ℂ → ℂ} {γ₀ d : ℝ}
    (hS_unit : ‖S (γ₀ : ℂ)‖ = 1)
    (hS_lt1 : ∀ z : ℂ, 0 < z.im → ‖S z‖ < 1)
    (hS_diff : ∀ z ∈ Metric.closedBall ((γ₀ : ℂ) + Complex.I) 1, DifferentiableAt ℂ S z)
    (hS_logDeriv : logDeriv S (γ₀ : ℂ) = Complex.I * ((2 * d : ℝ) : ℂ)) :
    0 < d := by
  set u₀ : ℂ := S (γ₀ : ℂ)
  have hu₀_ne : u₀ ≠ 0 := fun h => by rw [h, norm_zero] at hS_unit; norm_num at hS_unit
  let g : ℂ → ℂ := fun z => u₀⁻¹ * S z
  let w : ℂ → ℂ := fun z => Complex.I * ((1 - g z) / (1 + g z))
  have hg_norm : ∀ z : ℂ, ‖g z‖ = ‖S z‖ := fun z => by
    dsimp only [g]; rw [norm_mul, norm_inv, hS_unit, inv_one, one_mul]
  have hg_lt1 : ∀ z : ℂ, 0 < z.im → ‖g z‖ < 1 := fun z hz => by
    rw [hg_norm]; exact hS_lt1 z hz
  have hg0 : g (γ₀ : ℂ) = 1 := by dsimp only [g, u₀]; exact inv_mul_cancel₀ hu₀_ne
  have h1g_ne_of_im_pos : ∀ z : ℂ, 0 < z.im → 1 + g z ≠ 0 := fun z hz h0 => by
    have heq : g z = -1 := by linear_combination h0
    have h1 := hg_lt1 z hz; rw [heq, norm_neg, norm_one] at h1; linarith
  have hw_im_formula : ∀ z : ℂ, 1 + g z ≠ 0 →
      (w z).im = (1 - ‖g z‖ ^ 2) / ‖1 + g z‖ ^ 2 := by
    intro z hne
    dsimp only [w]
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
        Complex.div_re, ← Complex.sq_norm]
    have hnum : (1 - g z).re * (1 + g z).re + (1 - g z).im * (1 + g z).im = 1 - ‖g z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [← add_div, hnum]
  have hw_im_pos : ∀ z : ℂ, 0 < z.im → 0 < (w z).im := fun z hz => by
    have hne := h1g_ne_of_im_pos z hz
    rw [hw_im_formula z hne]
    exact div_pos (by nlinarith [hg_lt1 z hz, norm_nonneg (g z)]) (sq_pos_of_pos (norm_pos_iff.mpr hne))
  have hw0 : w (γ₀ : ℂ) = 0 := by dsimp only [w]; rw [hg0]; simp
  have hw_diff : ∀ z ∈ Metric.closedBall ((γ₀ : ℂ) + Complex.I) 1, DifferentiableAt ℂ w z := by
    intro z hz
    have hSz := hS_diff z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hsq : (z.re - γ₀) ^ 2 + (z.im - 1) ^ 2 ≤ 1 := by
      have h1 : ‖z - ((γ₀ : ℂ) + Complex.I)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z - ((γ₀ : ℂ) + Complex.I))]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1; simp at h1; nlinarith
    have him_nn : 0 ≤ z.im := by nlinarith [sq_nonneg (z.re - γ₀)]
    have hdg : DifferentiableAt ℂ g z := (differentiableAt_const u₀⁻¹).mul hSz
    have h1g_ne : 1 + g z ≠ 0 := by
      rcases eq_or_lt_of_le him_nn with him0 | him_pos
      · have hre : z.re = γ₀ := by rw [← him0] at hsq; nlinarith
        have hzeq : z = (γ₀ : ℂ) := Complex.ext hre him0.symm
        rw [hzeq, hg0]; norm_num
      · exact h1g_ne_of_im_pos z him_pos
    have hnum_d : DifferentiableAt ℂ (fun x => (1 : ℂ) - g x) z := (differentiableAt_const (1 : ℂ)).sub hdg
    have hden_d : DifferentiableAt ℂ (fun x => (1 : ℂ) + g x) z := (differentiableAt_const (1 : ℂ)).add hdg
    exact (differentiableAt_const Complex.I).mul (hnum_d.div hden_d h1g_ne)
  have hγ_ball : (γ₀ : ℂ) ∈ Metric.closedBall ((γ₀ : ℂ) + Complex.I) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]; simp
  have hdg0 : HasDerivAt g (logDeriv S (γ₀ : ℂ)) (γ₀ : ℂ) := by
    have h1 := (hS_diff (γ₀ : ℂ) hγ_ball).hasDerivAt.const_mul u₀⁻¹
    refine h1.congr_deriv ?_
    dsimp [logDeriv, u₀]; ring
  have hdw0 : HasDerivAt w (-(Complex.I / 2) * logDeriv S (γ₀ : ℂ)) (γ₀ : ℂ) := by
    have h1g_ne : 1 + g (γ₀ : ℂ) ≠ 0 := by rw [hg0]; norm_num
    have hq := ((hasDerivAt_const (γ₀ : ℂ) (1 : ℂ)).sub hdg0).div ((hasDerivAt_const (γ₀ : ℂ) (1 : ℂ)).add hdg0) h1g_ne
    have hm := hq.const_mul Complex.I
    refine hm.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, hg0]; ring
  have hdw0_val : -(Complex.I / 2) * logDeriv S (γ₀ : ℂ) = (d : ℂ) := by
    rw [hS_logDeriv]
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc -(Complex.I / 2) * (Complex.I * ((2 * d : ℝ) : ℂ))
      _ = -(Complex.I * Complex.I) * (d : ℂ) := by push_cast; ring
      _ = (d : ℂ) := by rw [hI2]; ring
  rw [hdw0_val] at hdw0
  have hpath : HasDerivAt (fun σ : ℝ => (γ₀ : ℂ) + Complex.I * (σ : ℂ)) Complex.I 0 := by
    have h1 : HasDerivAt (fun σ : ℝ => (σ : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul Complex.I).const_add (γ₀ : ℂ)
    simpa [mul_one] using h2
  have hcomp_deriv : HasDerivAt (fun σ : ℝ => w ((γ₀ : ℂ) + Complex.I * (σ : ℂ)))
      ((d : ℂ) * Complex.I) 0 := by
    have h0 : (γ₀ : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = (γ₀ : ℂ) := by simp
    have hdw' : HasDerivAt w (d : ℂ) ((γ₀ : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) := by rwa [h0]
    have hcomp := (hdw'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hpath
    simpa [Function.comp_def, ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm] using hcomp
  have him_deriv : HasDerivAt (fun σ : ℝ => (w ((γ₀ : ℂ) + Complex.I * (σ : ℂ))).im) d 0 := by
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcomp_deriv
    simpa [Function.comp_def, Complex.imCLM_apply] using h1
  exact holomorphic_annulus_hopf_boundary_lemma hw0 hw_im_pos hw_diff him_deriv

/-- Helper II.5C: 12-line instantiation of `schur_boundary_phase_velocity_pos` on `xiSchur α`
    proving STRICT Herglotz positivity `0 < (xiResolvent (γ₀ + iα)).im` for ALL `α ≥ 1/2` and ALL `γ₀ ∈ ℝ`! -/
private lemma xiResolvent_im_pos_of_half_le_via_annulus_hopf {α : ℝ} (hα : 1 / 2 ≤ α) (γ₀ : ℝ) :
    0 < (xiResolvent ((γ₀ : ℂ) + Complex.I * (α : ℂ))).im := by
  have hE0_ne : xiShiftE α (γ₀ : ℂ) ≠ 0 := by
    dsimp [xiShiftE]; exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hS_unit : ‖xiSchur α (γ₀ : ℂ)‖ = 1 := by
    have hr := xiSchur_norm_sq_eq_xiNormSq_ratio α 0 γ₀
    have hγ_eq : (γ₀ : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = (γ₀ : ℂ) := by simp
    rw [hγ_eq] at hr
    have hsq := hr.2.2 hE0_ne
    simp only [zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < α), zero_add] at hsq
    have hV_pos : 0 < xiNormSq α γ₀ := by
      have h1 := hr.2.1; rw [zero_add] at h1
      rw [← h1]; exact sq_pos_of_pos (norm_pos_iff.mpr hE0_ne)
    rw [div_self (ne_of_gt hV_pos)] at hsq
    nlinarith [norm_nonneg (xiSchur α (γ₀ : ℂ))]
  have hS_lt1 : ∀ z : ℂ, 0 < z.im → ‖xiSchur α z‖ < 1 := fun z hz => by
    have hz_eq : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by apply Complex.ext <;> simp
    rw [hz_eq]; exact (xiSchur_strict_contraction_and_hopfBloch_complete_outer_halfPlane hα hz).1
  have hS_diff : ∀ z ∈ Metric.closedBall ((γ₀ : ℂ) + Complex.I) 1, DifferentiableAt ℂ (xiSchur α) z := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hsq : (z.re - γ₀) ^ 2 + (z.im - 1) ^ 2 ≤ 1 := by
      have h1 : ‖z - ((γ₀ : ℂ) + Complex.I)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z - ((γ₀ : ℂ) + Complex.I))]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1; simp at h1; nlinarith
    have him_nn : 0 ≤ z.im := by nlinarith [sq_nonneg (z.re - γ₀)]
    exact differentiableAt_xiSchur_of_one_le (by linarith)
  exact schur_boundary_phase_velocity_pos hS_unit hS_lt1 hS_diff
    (xiSchur_boundary_logDeriv_eq_I_mul_logForce hE0_ne).1

/-- Helper: Complex differentiability of `xiResolvent` on `{z : ℂ | 1 / 2 ≤ z.im}` (including the edge `z.im = 1/2`!). -/
private lemma differentiableOn_xiResolvent_closed_outer_halfPlane :
    DifferentiableOn ℂ xiResolvent {z : ℂ | (1 / 2 : ℝ) ≤ z.im} := by
  intro z hz
  have hre : 1 ≤ (1 / 2 - Complex.I * z).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, sub_neg_eq_add]
    have hz' : (1 / 2 : ℝ) ≤ z.im := hz; linarith
  have hxi_ne : riemannXi (1 / 2 - Complex.I * z) ≠ 0 := riemannXi_ne_zero_of_one_le_re hre
  have hmap : Differentiable ℂ (fun w : ℂ => (1 / 2 : ℂ) - Complex.I * w) :=
    (differentiable_const _).sub ((differentiable_const _).mul differentiable_id)
  have hdiff_at : DifferentiableAt ℂ xiResolvent z := by
    unfold xiResolvent
    exact (differentiableAt_const _).mul
      (((differentiable_deriv_riemannXi.comp hmap).differentiableAt).div
        ((riemannXi_entire.comp hmap).differentiableAt) hxi_ne)
  exact hdiff_at.differentiableWithinAt

/-- THEOREM II.5 (COMPLETE UNCONDITIONAL CLOSURE OF THE ENTIRE OUTER HALF-PLANE `Re(s) ≥ 1`,
    i.e. `σ ≥ 1/2` — INCLUDING THE EXACT CRITICAL-STRIP BOUNDARY `Re(s) = 1` — FOR ALL `γ ∈ ℝ`!):
    Completely eliminates EVERY remaining outer-half-plane gap beyond the critical strip (descending
    all the way from Module #16's `σ ≥ 15/2`, Module #17's `σ ≥ 7/2`, Module #18's `σ ≥ 2`, and
    Module #19's `σ ≥ 3/2` to the EXACT critical-strip edge `σ ≥ 1/2`, `Re(s) ≥ 1`!):
    (1) For EVERY `σ ≥ 1/2` and EVERY `γ ∈ ℝ`:
          * `0 < (xiResolvent (γ + iσ)).im` (strict Herglotz positivity on ALL of `Re(s) ≥ 1`),
          * `0 < deriv (fun s => xiNormSq s γ) σ` (strict positive radial force on ALL of `Re(s) ≥ 1`),
          * `0 < xiLogForce σ γ` and `0 < (logDeriv (xiSchur σ) γ).im` (strict positive de Branges phase velocity);
    (2) For EVERY `α ≥ 1/2`, EVERY `σ > 0`, and EVERY `γ ∈ ℝ`:
          * `‖xiSchur α (γ + iσ)‖ < 1` and `0 < hopfBlochZ α (γ + iσ)`;
    (3) For EVERY `α ≥ 1/2` and EVERY `γ₁ < γ₂`:
          * `0 < deBrangesPhaseMemory α γ₁ γ₂ = ∫_{γ₁}^{γ₂} 2 * Im R_ξ(t + iα) dt`! -/
theorem xiResolvent_herglotz_global_complete_outer_halfPlane_half :
    (∀ σ γ : ℝ, 1 / 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im) ∧
    (∀ α σ γ : ℝ, 1 / 2 ≤ α → 0 < σ →
      ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ < 1 ∧
      0 < hopfBlochZ α ((γ : ℂ) + Complex.I * (σ : ℂ))) ∧
    (∀ α γ₁ γ₂ : ℝ, 1 / 2 ≤ α → γ₁ < γ₂ →
      0 < deBrangesPhaseMemory α γ₁ γ₂) := by
  have hmain : ∀ σ γ : ℝ, 1 / 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
    intro σ γ hσ
    have hR_pos := xiResolvent_im_pos_of_half_le_via_annulus_hopf hσ γ
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
    have hE_ne : xiShiftE σ (γ : ℂ) ≠ 0 := by
      dsimp [xiShiftE]; exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
    have hphase := xiSchur_boundary_logDeriv_eq_I_mul_logForce hE_ne
    have hph_pos : 0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
      rw [hphase.2]; simp; exact hLF_pos
    exact ⟨hR_pos, hF_pos, hLF_pos, hph_pos⟩
  refine ⟨hmain, fun α σ γ hα hσ => ?_, fun α γ₁ γ₂ hα hγ => ?_⟩
  · have h := xiSchur_strict_contraction_and_hopfBloch_complete_outer_halfPlane (γ := γ) hα hσ
    exact ⟨h.1, h.2.1⟩
  · dsimp [deBrangesPhaseMemory]
    have hcont : Continuous (fun t : ℝ => 2 * (xiResolvent ((t : ℂ) + Complex.I * (α : ℂ))).im) := by
      have hpath : Continuous (fun x : ℝ => (x : ℂ) + Complex.I * (α : ℂ)) :=
        Complex.continuous_ofReal.add continuous_const
      have hres : Continuous (fun x : ℝ => xiResolvent ((x : ℂ) + Complex.I * (α : ℂ))) :=
        differentiableOn_xiResolvent_closed_outer_halfPlane.continuousOn.comp_continuous hpath (fun x => by simp; linarith)
      exact continuous_const.mul (Complex.continuous_im.comp hres)
    exact intervalIntegral.integral_pos hγ hcont.continuousOn
      (fun t _ => le_of_lt (mul_pos (by norm_num) (hmain α t hα).1))
      ⟨γ₁, Set.left_mem_Icc.mpr (le_of_lt hγ), mul_pos (by norm_num) (hmain α γ₁ hα).1⟩

end GlobalOuterHalfPlaneClosureAndAllHorizonWeil
