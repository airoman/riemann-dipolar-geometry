/-
  ==============================================================================
  MODULE #18: CLIFFORD-TORUS PRIME-PHASE EULER DESCENT TO σ ≥ 2 (Re(s) ≥ 5/2),
  HARMONIC MINIMUM PRINCIPLE, 3-4-1 PHASE POSITIVITY, BOHR ERGODIC KURAMOTO
  DECOHERENCE, EXPANDED CONTINUOUS WEIL POSITIVITY (UNRESTRICTED L ≤ 3/20,
  ODD L ≤ 2/5, EVEN ZERO-MEAN L ≤ 11/20), AND TWO-PRIME-ACTIVE (p = 2, 3)
  CONTINUOUS POSITIVITY BEYOND ln 3 (L ≤ 6/5)

  Title: Clifford-Torus Prime-Phase Euler Descent and Two-Prime Continuous Weil
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part 0 (Tight Certified Analytic Constants):
      * `eulerMascheroniConstant_lt_5813_div_10000`: γ_E < 5813 / 10000 via H_128 - 7 log 2.
      * `archimedeanWeilConst_lt_5377_div_1000`: C_∞ < 5377 / 1000 (tightening 11/2).
  - Part I (Route A — Expanded Continuous Weil Positivity & Two-Prime-Active L ≤ 6/5):
      * `weilTotal_continuous_pos_all_unrestricted_up_to_three_twentieths`:
        COMPLETELY UNRESTRICTED (no parity, no zero-mean, no moments, zero discretization)
        continuous Weil positivity on `0 < L ≤ 3/20` (+20% over Module #11's `1/8`).
      * `weilTotal_continuous_pos_odd_up_to_two_fifths`:
        UNRESTRICTED ODD continuous Weil positivity on `0 < L ≤ 2/5` (+33% over Module #13's `3/10`).
      * `weilTotal_continuous_pos_even_zeroMean_up_to_eleven_twentieths`:
        ZERO-MEAN EVEN continuous Weil positivity on `0 < L ≤ 11/20` (+24% over Module #13's `4/9`).
      * `weilTotal_continuous_pos_primes_two_three_active_up_to_six_fifths`:
        FIRST TWO-PRIME-ACTIVE (p = 2 AND p = 3 BOTH LIVE, L ≤ 6/5 > ln 3) ZERO-DISCRETIZATION
        CONTINUOUS WEIL POSITIVITY (nearly doubling Module #17's `L ≤ 3/4`).
  - Part II (Route A — Clifford-Torus / Bohr Ergodic Kuramoto Decoherence):
      * `primeKuramotoOrder_bohr_mean_square_identity`:
        Exact finite-horizon Bohr mean-square integral identity for `‖K_L(t)‖^2`.
      * `primeKuramotoCoherence_bohr_ergodic_limit_and_decay`:
        Exact Bohr ergodic limit `lim_{T→∞} (1/(2T)) ∫_{-T}^T r_L(t)^2 dt = (∑ Λ(n)^2/n)/B_0(L)^2`
        and unconditional universal decay bound `≤ (2 / exp 1) / B_0(L) < 3 / (4 * B_0(L))`.
  - Part III (Route B — Harmonic Minimum Principle, Log Digamma Tail, & 3-4-1 Phase Law):
      * `xiResolvent_im_pos_of_rectangle_boundary`:
        Harmonic Minimum Principle for `Im(R_ξ)` on any compact rectangle inside `Im z > 1/2`
        via Mathlib4's Maximum Modulus Principle `Complex.exists_mem_frontier_isMaxOn_norm`.
      * `complex_digamma_re_ge_real_add_finset_add_log_tail`:
        Exact finite-term + logarithmic tail lower bound for `Re ψ(x + iy) - ψ(x)` for ALL
        `x > 0`, `y ∈ ℝ`, and `K : ℕ`.
      * `cliffordTorus_341_zeta_logDeriv_nonneg`:
        Hadamard–de la Vallée Poussin 3-4-1 Clifford-torus harmonic positivity law for ALL
        `β > 1` and `γ ∈ ℝ`.
  - Part IV (Route B — Clifford-Torus Prime-Phase Euler Splitting & Unconditional Global
    All-γ Descent to σ ≥ 2, Re(s) ≥ 5/2):
      * `cliffordTorus_primePhase_euler_split_2357`:
        Exact Clifford-torus prime-phase Euler splitting separating `{2, 3, 5, 7}` from the
        `6k ± 1` residual tail (`≤ 235/10000` at `β = 5/2`).
      * `xiResolvent_herglotz_global_phase_euler_halfPlane_two`:
        UNCONDITIONAL GLOBAL ALL-γ HERGLOTZ, RADIAL FORCE, DE BRANGES PHASE VELOCITY, AND
        STRICT SCHUR CONTRACTION FOR EVERY `σ ≥ 2` (`Re(s) ≥ 5/2`) AND EVERY `γ ∈ ℝ`
        (smashing +1.05 units past the naive triangle-inequality wall at σ ≈ 3.05, and a
        3.75x total descent from Module #16's σ ≥ 15/2!).
      * `hopfBloch_northern_hemisphere_and_phaseMemory_unconditional_euler_two`:
        UNCONDITIONAL ALL-γ HOPF–BLOCH S^2 NORTHERN HEMISPHERE CONFINEMENT (`0 < Z_α`) AND
        POSITIVE ACCUMULATED DE BRANGES PHASE MEMORY (`0 < ΔΦ_α`) DOWN TO `σ, α ≥ 2`.
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RiemannDipolar.WeilArchimedeanAndExplicitCorridor
import RiemannDipolar.ArithmeticWeilAndWideCorridor
import RiemannDipolar.UniversalWeilAndHerglotzResolvent
import RiemannDipolar.HermiteBiehlerHomotopyAndWeilPick
import RiemannDipolar.GeodesicRenormalizationAndEulerJacobiPick
import RiemannDipolar.CompactMomentWeilAndHopfBlochEulerDescent

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators Classical
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick UniversalSolverLyapunovAndPrimeResolvent
open RouteABLimitBarriersAndDeBrangesSynthesis GeodesicRenormalizationAndEulerJacobiPick
open CompactMomentWeilAndHopfBlochEulerDescent

namespace CliffordPhaseEulerDescentAndPrimeWeil

-- ==============================================================================
-- PART 0: TIGHT CERTIFIED ANALYTIC CONSTANTS (H_128, γ_E, C_∞, log p, p^{-5/2})
-- ==============================================================================

/-- Elementary Taylor upper bound on `Real.exp y` for `0 ≤ y ≤ 1` with `n` terms. -/
private lemma exp_le_taylor_small {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp y ≤ (∑ k ∈ Finset.range n, y ^ k / (k.factorial : ℝ)) +
      y ^ n * (((n : ℝ) + 1) / ((n.factorial : ℝ) * (n : ℝ))) := by
  have habs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  have hb := Real.exp_bound habs hn
  rw [abs_of_nonneg hy0] at hb
  have h1 := (abs_le.mp hb).2
  have hcast : ((n.succ : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hcast] at h1
  linarith

/-- Helper: Rational upper bound on `Real.exp y` for `0 ≤ y ≤ 2` via `exp(y) = (exp(y/2))^2`. -/
private lemma exp_le_sq_taylor_of_le_two {y B : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (_hB0 : 0 ≤ B)
    (htay : (∑ k ∈ Finset.range 7, (y / 2) ^ k / (k.factorial : ℝ)) +
        (y / 2) ^ 7 * (((7 : ℝ) + 1) / (((7 : ℕ).factorial : ℝ) * 7)) ≤ B) :
    Real.exp y ≤ B ^ 2 := by
  have hhalf := exp_le_taylor_small (y := y / 2) (by linarith) (by linarith) (n := 7) (by norm_num)
  have hle : Real.exp (y / 2) ≤ B := le_trans hhalf htay
  have hsq : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hsq]
  exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hle 2

/-- Helper: Rational upper bound on `Real.exp y` for `0 ≤ y ≤ 3` via `exp(y) = (exp(y/3))^3`. -/
private lemma exp_le_cube_taylor_of_le_three {y B : ℝ} (hy0 : 0 ≤ y) (hy3 : y ≤ 3) (_hB0 : 0 ≤ B)
    (htay : (∑ k ∈ Finset.range 7, (y / 3) ^ k / (k.factorial : ℝ)) +
        (y / 3) ^ 7 * (((7 : ℝ) + 1) / (((7 : ℕ).factorial : ℝ) * 7)) ≤ B) :
    Real.exp y ≤ B ^ 3 := by
  have hthird := exp_le_taylor_small (y := y / 3) (by linarith) (by linarith) (n := 7) (by norm_num)
  have hle : Real.exp (y / 3) ≤ B := le_trans hthird htay
  have hcb : Real.exp y = (Real.exp (y / 3)) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hcb]
  exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hle 3

/-- Certified bounds on `log 2, log 3, log 5, log 7, π, log π, log(8π)`. -/
private lemma log_two_ge_69314 : (69314 / 100000 : ℝ) ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := exp_le_taylor_small (y := 69314 / 100000) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h; linarith

private lemma log_two_le_6932 : Real.log 2 ≤ 6932 / 10000 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 6932 / 10000 by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h; linarith

private lemma log_two_ge_6931 : (6931 / 10000 : ℝ) ≤ Real.log 2 := by linarith [log_two_ge_69314]

private lemma log_three_ge_10986 : (10986 / 10000 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := exp_le_sq_taylor_of_le_two (y := 10986 / 10000) (B := 173205 / 100000)
    (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
      norm_num)
  norm_num at h; linarith

private lemma log_three_le_10987 : Real.log 3 ≤ 10987 / 10000 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 10987 / 10000 by norm_num) 9
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h; linarith

private lemma log_five_ge_16094 : (16094 / 10000 : ℝ) ≤ Real.log 5 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := exp_le_sq_taylor_of_le_two (y := 16094 / 10000) (B := 223605 / 100000)
    (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
      norm_num)
  norm_num at h; linarith

private lemma log_five_le_16095 : Real.log 5 ≤ 16095 / 10000 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 16095 / 10000 by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h; linarith

private lemma log_seven_ge_19459 : (19459 / 10000 : ℝ) ≤ Real.log 7 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := exp_le_sq_taylor_of_le_two (y := 19459 / 10000) (B := 264575 / 100000)
    (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
      norm_num)
  norm_num at h; linarith

private lemma log_seven_le_19460 : Real.log 7 ≤ 19460 / 10000 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 19460 / 10000 by norm_num) 11
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  norm_num at h; linarith

private lemma pi_gt_31415 : (31415 / 10000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
private lemma pi_lt_31416 : Real.pi < 31416 / 10000 := by linarith [Real.pi_lt_d4]

private lemma log_pi_le_11448 : Real.log Real.pi ≤ 11448 / 10000 := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11448 / 10000 by norm_num) 9
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  have hpi := pi_lt_31416
  norm_num at h; linarith

private lemma log_eight_pi_le_32242 : Real.log (8 * Real.pi) ≤ 32242 / 10000 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hhalf : (501332 / 100000 : ℝ) ≤ Real.exp (16121 / 10000) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 16121 / 10000 by norm_num) 11
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hsum
    norm_num at hsum; linarith
  have hsq : Real.exp (32242 / 10000) = (Real.exp (16121 / 10000)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num
  rw [hsq]
  have hpow : (501332 / 100000 : ℝ) ^ 2 ≤ (Real.exp (16121 / 10000)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hhalf 2
  have hpi := pi_lt_31416
  norm_num at hpow; linarith

/-- Helper: Upper bound `harmonic 128 ≤ 543318 / 100000` in 8 fast 16-term chunks. -/
private lemma harmonic_128_le : ((harmonic 128 : ℚ) : ℝ) ≤ 543318 / 100000 := by
  have hrat : harmonic 128 ≤ (543318 / 100000 : ℚ) := by
    have hsplit : harmonic 128 =
        (∑ i ∈ Finset.range 16, ((i + 1 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 17 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 33 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 49 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 65 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 81 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 97 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 113 : ℚ)⁻¹)) := by
      unfold harmonic
      rw [show (128 : ℕ) = 112 + 16 by rfl, Finset.sum_range_add,
          show (112 : ℕ) = 96 + 16 by rfl, Finset.sum_range_add,
          show (96 : ℕ) = 80 + 16 by rfl, Finset.sum_range_add,
          show (80 : ℕ) = 64 + 16 by rfl, Finset.sum_range_add,
          show (64 : ℕ) = 48 + 16 by rfl, Finset.sum_range_add,
          show (48 : ℕ) = 32 + 16 by rfl, Finset.sum_range_add,
          show (32 : ℕ) = 16 + 16 by rfl, Finset.sum_range_add]
      congr 1
      · congr 1
        · congr 1
          · congr 1
            · congr 1
              · congr 1
                · congr 1
                  · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
                  · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
                · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
              · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
            · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
          · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
        · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
      · refine Finset.sum_congr rfl fun i _ => by push_cast; ring
    have hc1 : (∑ i ∈ Finset.range 16, ((i + 1 : ℚ)⁻¹)) ≤ 338073 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc2 : (∑ i ∈ Finset.range 16, ((i + 17 : ℚ)⁻¹)) ≤ 67777 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc3 : (∑ i ∈ Finset.range 16, ((i + 33 : ℚ)⁻¹)) ≤ 40031 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc4 : (∑ i ∈ Finset.range 16, ((i + 49 : ℚ)⁻¹)) ≤ 28510 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc5 : (∑ i ∈ Finset.range 16, ((i + 65 : ℚ)⁻¹)) ≤ 22159 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc6 : (∑ i ∈ Finset.range 16, ((i + 81 : ℚ)⁻¹)) ≤ 18129 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc7 : (∑ i ∈ Finset.range 16, ((i + 97 : ℚ)⁻¹)) ≤ 15341 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc8 : (∑ i ∈ Finset.range 16, ((i + 113 : ℚ)⁻¹)) ≤ 13298 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    rw [hsplit]; linarith
  have hcast : ((harmonic 128 : ℚ) : ℝ) ≤ ((543318 / 100000 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  push_cast at hcast
  exact hcast

/-- THEOREM 0.1 (SHARP CERTIFIED EULER-MASCHERONI UPPER BOUND `γ_E < 5813 / 10000`):
    Tightening Module #17's `586 / 1000` via `eulerMascheroniSeq' 128 = H_128 - 7 log 2`. -/
theorem eulerMascheroniConstant_lt_5813_div_10000 :
    Real.eulerMascheroniConstant < 5813 / 10000 := by
  have hlt : Real.eulerMascheroniConstant < Real.eulerMascheroniSeq' 128 :=
    Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have hseq : Real.eulerMascheroniSeq' 128 = ((harmonic 128 : ℚ) : ℝ) - Real.log ((128 : ℕ) : ℝ) := by
    dsimp [Real.eulerMascheroniSeq']
  rw [hseq] at hlt
  have hlog128 : Real.log ((128 : ℕ) : ℝ) = 7 * Real.log 2 := by
    rw [show ((128 : ℕ) : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hlog128] at hlt
  linarith [harmonic_128_le, log_two_ge_69314]

/-- THEOREM 0.2 (SHARP CERTIFIED ARCHIMEDEAN WEIL CONSTANT `C_∞ < 5377 / 1000`):
    Tightening Module #10's `11 / 2` (= 5.50) to `5377 / 1000` (= 5.377; exact `5.37218...`). -/
theorem archimedeanWeilConst_lt_5377_div_1000 :
    archimedeanWeilConst < 5377 / 1000 := by
  dsimp [archimedeanWeilConst]
  linarith [eulerMascheroniConstant_lt_5813_div_10000, log_eight_pi_le_32242, pi_lt_31416]

-- ==============================================================================
-- PART I: ROUTE A — EXPANDED UNRESTRICTED / ODD / ZERO-MEAN EVEN POSITIVITY AND
--         FIRST TWO-PRIME-ACTIVE (p = 2, 3) CONTINUOUS POSITIVITY BEYOND ln 3
-- ==============================================================================

/-- Elementary 5-term arctan envelope for ALL `y ≥ 0`:
    `y - y^3 / 3 ≤ Real.arctan y ≤ y - y^3 / 3 + y^5 / 5`. -/
private lemma arctan_bounds_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 3 ≤ Real.arctan y ∧ Real.arctan y ≤ y - y ^ 3 / 3 + y ^ 5 / 5 := by
  constructor
  · have hmono : MonotoneOn (fun s : ℝ => Real.arctan s - (s - s ^ 3 / 3)) (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (Real.continuous_arctan.sub (continuous_id.sub ((continuous_pow 3).div_const 3))).continuousOn
      · intro s _
        exact ((Real.hasDerivAt_arctan s).sub
          ((hasDerivAt_id' s).sub ((hasDerivAt_pow 3 s).div_const 3))).differentiableAt.differentiableWithinAt
      · intro s _
        have hd : HasDerivAt (fun x : ℝ => Real.arctan x - (x - x ^ 3 / 3))
            (1 / (1 + s ^ 2) - (1 - 3 * s ^ 2 / 3)) s :=
          (Real.hasDerivAt_arctan s).sub ((hasDerivAt_id' s).sub ((hasDerivAt_pow 3 s).div_const 3))
        rw [hd.deriv]
        have hpos : 0 < 1 + s ^ 2 := by positivity
        have heq : 1 / (1 + s ^ 2) - (1 - 3 * s ^ 2 / 3) = s ^ 4 / (1 + s ^ 2) := by
          field_simp [ne_of_gt hpos]; ring
        rw [heq]; positivity
    have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) hy hy
    simp only [Real.arctan_zero] at h; norm_num at h; linarith
  · have hmono : MonotoneOn (fun s : ℝ => (s - s ^ 3 / 3 + s ^ 5 / 5) - Real.arctan s) (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact (((continuous_id.sub ((continuous_pow 3).div_const 3)).add
          ((continuous_pow 5).div_const 5)).sub Real.continuous_arctan).continuousOn
      · intro s _
        exact ((((hasDerivAt_id' s).sub ((hasDerivAt_pow 3 s).div_const 3)).add
          ((hasDerivAt_pow 5 s).div_const 5)).sub (Real.hasDerivAt_arctan s)).differentiableAt.differentiableWithinAt
      · intro s _
        have hd : HasDerivAt (fun x : ℝ => (x - x ^ 3 / 3 + x ^ 5 / 5) - Real.arctan x)
            ((1 - 3 * s ^ 2 / 3 + 5 * s ^ 4 / 5) - 1 / (1 + s ^ 2)) s :=
          (((hasDerivAt_id' s).sub ((hasDerivAt_pow 3 s).div_const 3)).add
            ((hasDerivAt_pow 5 s).div_const 5)).sub (Real.hasDerivAt_arctan s)
        rw [hd.deriv]
        have hpos : 0 < 1 + s ^ 2 := by positivity
        have heq : (1 - 3 * s ^ 2 / 3 + 5 * s ^ 4 / 5) - 1 / (1 + s ^ 2) = s ^ 6 / (1 + s ^ 2) := by
          field_simp [ne_of_gt hpos]; ring
        rw [heq]; positivity
    have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) hy hy
    simp only [Real.arctan_zero] at h; norm_num at h; linarith

/-- Tight arctan bounds for `x > 0` via `arctan x = π/2 - arctan(1/x)`. -/
private lemma arctan_large_bounds {x : ℝ} (hx : 0 < x) :
    Real.pi / 2 - 1 / x + 1 / (3 * x ^ 3) - 1 / (5 * x ^ 5) ≤ Real.arctan x ∧
    Real.arctan x ≤ Real.pi / 2 - 1 / x + 1 / (3 * x ^ 3) := by
  have hinv := Real.arctan_inv_of_pos hx
  have hb := arctan_bounds_of_nonneg (inv_nonneg.mpr (le_of_lt hx))
  have h1 : x⁻¹ = 1 / x := (one_div x).symm
  have h3 : (x⁻¹) ^ 3 / 3 = 1 / (3 * x ^ 3) := by field_simp [ne_of_gt hx]
  have h5 : (x⁻¹) ^ 5 / 5 = 1 / (5 * x ^ 5) := by field_simp [ne_of_gt hx]
  rw [h3, h5, h1] at hb
  rw [h1] at hinv
  constructor <;> linarith

private lemma psiLb3_mono_nonneg {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (hle : t₁ ≤ t₂) :
    psiLb3 t₁ ≤ psiLb3 t₂ := by
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := pow_le_pow_left₀ ht₁ hle 2
  dsimp [psiLb3]
  have h0 : (4 * t₁ ^ 2) / (1 / 4 + t₁ ^ 2) ≤ (4 * t₂ ^ 2) / (1 / 4 + t₂ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h1 : ((4 / 5 : ℝ) * t₁ ^ 2) / (25 / 4 + t₁ ^ 2) ≤ ((4 / 5 : ℝ) * t₂ ^ 2) / (25 / 4 + t₂ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : ((4 / 9 : ℝ) * t₁ ^ 2) / (81 / 4 + t₁ ^ 2) ≤ ((4 / 9 : ℝ) * t₂ ^ 2) / (81 / 4 + t₂ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hl : Real.log (1 + 4 * t₁ ^ 2 / 169) ≤ Real.log (1 + 4 * t₂ ^ 2 / 169) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

private lemma psiLb3_cont : Continuous psiLb3 := by
  unfold psiLb3
  have h0 : Continuous (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div (continuous_const.add (continuous_pow 2))
      (fun t => ne_of_gt (by show (0 : ℝ) < 1 / 4 + t ^ 2; positivity))
  have h1 : Continuous (fun t : ℝ => ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div (continuous_const.add (continuous_pow 2))
      (fun t => ne_of_gt (by show (0 : ℝ) < 25 / 4 + t ^ 2; positivity))
  have h2 : Continuous (fun t : ℝ => ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div (continuous_const.add (continuous_pow 2))
      (fun t => ne_of_gt (by show (0 : ℝ) < 81 / 4 + t ^ 2; positivity))
  have h3 : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)) :=
    continuous_const.mul (Continuous.log
      (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 169))
      (fun t => ne_of_gt (by show (0 : ℝ) < 1 + 4 * t ^ 2 / 169; positivity)))
  exact (((continuous_const.add h0).add h1).add h2).add h3

private lemma psiLb3_even (t : ℝ) : psiLb3 (-t) = psiLb3 t := by
  unfold psiLb3; ring_nf

/-- Master continuous Archimedean cutoff bound using `psiLb3` and any symmetric Fourier envelope `K(t)`. -/
private lemma weilArch_psiLb3_envelope_lower {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    {g : ℝ → ℂ} {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_even : ∀ t, K (-t) = K t)
    (hK_bound : ∀ t : ℝ, ‖compactFourier L g t‖ ^ 2 ≤ K t * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hparseval : (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hint_arch : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    (hint_pl : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2)) :
    (psiLb3 T - (1 / Real.pi) * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t)) *
        (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤
      (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) := by
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Step 1: Subtract `psiLb3 T * ‖ĝ(t)‖^2`:
  -- `(psiLb3 T - psiArch t) * ‖ĝ(t)‖^2 ≤ indicator_{[-T,T]} * (psiLb3 T - psiLb3 t) * K(t) * N2`!
  let rhs : ℝ → ℝ := Set.indicator (Icc (-T) T) (fun t => (psiLb3 T - psiLb3 t) * K t * N2)
  have hrhs_int : Integrable rhs := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.integrable_indicator measurableSet_Icc
    exact (((continuous_const.sub psiLb3_cont).mul hK_cont).mul continuous_const).continuousOn
  have hdiff_int : Integrable (fun t : ℝ => (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2) := by
    have hrew : (fun t : ℝ => (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2) =
        fun t => psiLb3 T * ‖compactFourier L g t‖ ^ 2 - psiArch t * ‖compactFourier L g t‖ ^ 2 := by
      ext t; ring
    rw [hrew]; exact (hint_pl.const_mul (psiLb3 T)).sub hint_arch
  have hpt : ∀ t : ℝ, (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2 ≤ rhs t := by
    intro t
    dsimp [rhs]
    by_cases ht : t ∈ Icc (-T) T
    · rw [Set.indicator_of_mem ht]
      have habs : |t| ≤ T := abs_le.mpr ht
      have hge1 : psiLb3 t ≤ psiArch t := psiArch_ge_psiLb3 t
      have hgap_nn : 0 ≤ psiLb3 T - psiLb3 t := by
        have h1 : psiLb3 |t| ≤ psiLb3 T := psiLb3_mono_nonneg (abs_nonneg t) habs
        have h2 : psiLb3 |t| = psiLb3 t := by
          rcases le_or_gt 0 t with h | h
          · rw [abs_of_nonneg h]
          · rw [abs_of_neg h, psiLb3_even]
        linarith
      calc (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2
        _ ≤ (psiLb3 T - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        _ ≤ (psiLb3 T - psiLb3 t) * (K t * N2) := mul_le_mul_of_nonneg_left (hK_bound t) hgap_nn
        _ = (psiLb3 T - psiLb3 t) * K t * N2 := by ring
    · rw [Set.indicator_of_notMem ht]
      have hgt : T < |t| := by
        by_contra hle; push Not at hle; exact ht (abs_le.mp hle)
      have h1 : psiLb3 T ≤ psiLb3 |t| := psiLb3_mono_nonneg hT (le_of_lt hgt)
      have h2 : psiLb3 |t| = psiLb3 t := by
        rcases le_or_gt 0 t with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h, psiLb3_even]
      have h3 : psiLb3 T ≤ psiArch t := le_trans (by linarith) (psiArch_ge_psiLb3 t)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hint_le : ∫ t : ℝ, (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2 ≤ ∫ t : ℝ, rhs t :=
    MeasureTheory.integral_mono hdiff_int hrhs_int hpt
  have hrhs_eq : ∫ t : ℝ, rhs t = 2 * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t) * N2 := by
    dsimp [rhs]
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show -T ≤ T by linarith),
        intervalIntegral.integral_mul_const]
    have hsplit : ∫ t in (-T)..T, (psiLb3 T - psiLb3 t) * K t =
        (∫ t in (-T)..(0 : ℝ), (psiLb3 T - psiLb3 t) * K t) +
        (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (((continuous_const.sub psiLb3_cont).mul hK_cont).intervalIntegrable _ _)
        (((continuous_const.sub psiLb3_cont).mul hK_cont).intervalIntegrable _ _)).symm
    have hneg : ∫ t in (-T)..(0 : ℝ), (psiLb3 T - psiLb3 t) * K t =
        ∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t := by
      have hcomp := intervalIntegral.integral_comp_neg
        (f := fun t : ℝ => (psiLb3 T - psiLb3 t) * K t) (a := 0) (b := T)
      simp only [neg_zero] at hcomp
      have hev : (fun t : ℝ => (psiLb3 T - psiLb3 (-t)) * K (-t)) =
          fun t => (psiLb3 T - psiLb3 t) * K t := by
        ext t; rw [psiLb3_even, hK_even]
      rw [hev] at hcomp; exact hcomp.symm
    rw [hsplit, hneg]; ring
  have hlhs_eq : ∫ t : ℝ, (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2 =
      psiLb3 T * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) -
        ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 := by
    have hrew : (fun t : ℝ => (psiLb3 T - psiArch t) * ‖compactFourier L g t‖ ^ 2) =
        fun t => psiLb3 T * ‖compactFourier L g t‖ ^ 2 - psiArch t * ‖compactFourier L g t‖ ^ 2 := by
      ext t; ring
    rw [hrew, MeasureTheory.integral_sub (hint_pl.const_mul _) hint_arch,
        MeasureTheory.integral_const_mul]
  rw [hlhs_eq, hrhs_eq] at hint_le
  have hdiv := mul_le_mul_of_nonneg_left hint_le (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  have h2pi : (1 / (2 * Real.pi)) * (2 * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t) * N2) =
      (1 / Real.pi) * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t) * N2 := by
    field_simp [ne_of_gt hpi]
  have hmul_p : (1 / (2 * Real.pi)) * (psiLb3 T * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2)) =
      psiLb3 T * N2 := by
    have h1 : (1 / (2 * Real.pi)) * (psiLb3 T * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2)) =
        psiLb3 T * ((1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2)) := by ring
    rw [h1, hparseval]
  linarith [hdiv, h2pi, hmul_p]

/-- THEOREM I.1 (COMPLETELY UNRESTRICTED CONTINUOUS WEIL POSITIVITY ON `0 < L ≤ 3/20` —
    +20% OVER MODULE #11's `L ≤ 1/8`, ZERO PARITY, ZERO MOMENTS, ZERO DISCRETIZATION!):
    For EVERY `0 < L ≤ 3 / 20` and EVERY continuous `g : ℝ → ℂ`:
      `(1 / 20) * ∫ u in (-L/2)..(L/2), ‖g u‖^2 ≤ weilTotal L g`. -/
theorem weilTotal_continuous_pos_all_unrestricted_up_to_three_twentieths {L : ℝ}
    (hL0 : 0 < L) (hL : L ≤ 3 / 20) {g : ℝ → ℂ} (hg : Continuous g)
    (hparseval : (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hint_arch : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    (hint_pl : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2)) :
    (1 / 20 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hprime0 : weilPrime L g = 0 :=
    weilPrime_eq_zero_of_le_log_two (by linarith [log_two_ge_6931]) g
  have harch := weilArch_psiLb3_envelope_lower hL0 (T := 20) (by norm_num) (K := fun _ => L)
    continuous_const (fun _ => rfl) (fun t => fourierTransform_norm_sq_le_L_mul_L2 (le_of_lt hL0) hg t)
    hparseval hint_arch hint_pl
  have hpole := weilPole_lower_bound_all (le_of_lt hL0) hg
  -- Bound `psiLb3 20 ≥ 1003 / 1000`
  have hpsi20 : (1003 / 1000 : ℝ) ≤ psiLb3 20 := by
    unfold psiLb3
    have hC := archimedeanWeilConst_lt_5377_div_1000
    have hlog : (2345 / 1000 : ℝ) ≤ Real.log (1 + 4 * (20 : ℝ) ^ 2 / 169) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h := exp_le_cube_taylor_of_le_three (y := 2345 / 1000) (B := 2186 / 1000)
        (by norm_num) (by norm_num) (by norm_num) (by
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
          norm_num)
      norm_num at h ⊢; linarith
    have harg : 1 + 4 * (20 : ℝ) ^ 2 / 169 = 1769 / 169 := by norm_num
    rw [harg] at hlog ⊢
    norm_num at hlog ⊢; linarith
  -- Bound `∫ t in 0..20, (psiLb3 20 - psiLb3 t) ≤ 198 / 10`
  have hgap20 : ∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t) ≤ 198 / 10 := by
    rw [integral_psiLb3_gap_eq 20]
    have ha1 := (arctan_large_bounds (x := 40) (by norm_num)).2
    have ha2 := (arctan_large_bounds (x := 8) (by norm_num)).2
    have ha3 := (arctan_large_bounds (x := 40 / 9) (by norm_num)).2
    have ha4 := (arctan_large_bounds (x := 40 / 13) (by norm_num)).1
    have hpi := pi_gt_31415
    norm_num at ha1 ha2 ha3 ha4 ⊢; linarith
  have hint_eq : ∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t) * L =
      (∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t)) * L :=
    intervalIntegral.integral_mul_const L _
  have hpen : (1 / Real.pi) * (∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t) * L) ≤ 946 / 1000 := by
    rw [hint_eq]
    have hpi := pi_gt_31415
    have hg0 : 0 ≤ ∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t) :=
      intervalIntegral.integral_nonneg (by norm_num) fun t ht =>
        sub_nonneg.mpr (psiLb3_mono_nonneg ht.1 ht.2)
    have hmul : (∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t)) * L ≤ (198 / 10 : ℝ) * (3 / 20) :=
      mul_le_mul hgap20 hL (le_of_lt hL0) (by norm_num)
    have hdiv : (1 / Real.pi) * ((∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t)) * L) ≤
        (1 / (31415 / 10000 : ℝ)) * ((198 / 10 : ℝ) * (3 / 20)) :=
      mul_le_mul (one_div_le_one_div_of_le (by norm_num) (le_of_lt hpi)) hmul
        (mul_nonneg hg0 (le_of_lt hL0)) (by norm_num)
    refine le_trans hdiv (by norm_num)
  -- Bound `2 * (sinh(L/2) - L/2) ≤ 1 / 500` for `0 < L ≤ 3/20`
  have hpole_pen : 2 * (Real.sinh (L / 2) - L / 2) ≤ 1 / 500 := by
    have hy0 : 0 ≤ L / 2 := by linarith
    have hy1 : L / 2 ≤ 3 / 40 := by linarith
    have hpos := exp_le_taylor_small hy0 (by linarith) (n := 4) (by norm_num)
    have habs_n : |-(L / 2)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hy0]; linarith
    have hneg := Real.exp_bound habs_n (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hpos hneg
    rw [abs_neg, abs_of_nonneg hy0] at hneg
    have hlo := (abs_le.mp hneg).1
    rw [Real.sinh_eq]
    have h3 : (L / 2) ^ 3 ≤ (3 / 40 : ℝ) ^ 3 := pow_le_pow_left₀ hy0 hy1 3
    have h4 : (L / 2) ^ 4 ≤ (3 / 40 : ℝ) ^ 4 := pow_le_pow_left₀ hy0 hy1 4
    norm_num at hpos hlo h3 h4; linarith
  have hcoeff : (1 / 20 : ℝ) ≤ (psiLb3 20 - (1 / Real.pi) * (∫ t in (0 : ℝ)..20, (psiLb3 20 - psiLb3 t) * L)) -
      2 * (Real.sinh (L / 2) - L / 2) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal; rw [hprime0, sub_zero]
  linarith [harch, hpole, hmul]

/-- Helper: Panel bound for `∫ t in a..b, (psiLb3 T - psiLb3 t) * min c (d * t^k) dt`. -/
private lemma panel_integral_pow_le {T a b G c d : ℝ} (k : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hG : psiLb3 T - psiLb3 a ≤ G) :
    ∫ t in a..b, (psiLb3 T - psiLb3 t) * min c (d * t ^ k) ≤
      G * min (c * (b - a)) (d * ((b ^ (k + 1) - a ^ (k + 1)) / ((k + 1 : ℕ) : ℝ))) := by
  have hG_nn : 0 ≤ G := le_trans (sub_nonneg.mpr (psiLb3_mono_nonneg ha (le_trans hab hbT))) hG
  have hcont_lhs : Continuous (fun t : ℝ => (psiLb3 T - psiLb3 t) * min c (d * t ^ k)) :=
    (continuous_const.sub psiLb3_cont).mul (continuous_const.min (continuous_const.mul (continuous_pow k)))
  rw [mul_min_of_nonneg _ _ hG_nn]
  refine le_min ?_ ?_
  · have h1 : ∫ t in a..b, (psiLb3 T - psiLb3 t) * min c (d * t ^ k) ≤ ∫ _t in a..b, G * c := by
      refine intervalIntegral.integral_mono_on hab (hcont_lhs.intervalIntegrable _ _)
        intervalIntegrable_const fun t ht => ?_
      have hgap : psiLb3 T - psiLb3 t ≤ G :=
        le_trans (sub_le_sub_left (psiLb3_mono_nonneg ha ht.1) _) hG
      exact mul_le_mul hgap (min_le_left _ _)
        (le_min hc (mul_nonneg hd (pow_nonneg (le_trans ha ht.1) k))) hG_nn
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1; linarith
  · have h1 : ∫ t in a..b, (psiLb3 T - psiLb3 t) * min c (d * t ^ k) ≤ ∫ t in a..b, (G * d) * t ^ k := by
      refine intervalIntegral.integral_mono_on hab (hcont_lhs.intervalIntegrable _ _)
        ((continuous_const.mul (continuous_pow k)).intervalIntegrable _ _) fun t ht => ?_
      have hgap : psiLb3 T - psiLb3 t ≤ G :=
        le_trans (sub_le_sub_left (psiLb3_mono_nonneg ha ht.1) _) hG
      have hmul : (psiLb3 T - psiLb3 t) * min c (d * t ^ k) ≤ G * (d * t ^ k) :=
        mul_le_mul hgap (min_le_right _ _)
          (le_min hc (mul_nonneg hd (pow_nonneg (le_trans ha ht.1) k))) hG_nn
      linarith
    rw [intervalIntegral.integral_const_mul, integral_pow] at h1
    push_cast; linarith

private lemma psiLb3_ten_ge : (341 / 1000 : ℝ) ≤ psiLb3 10 := by
  unfold psiLb3
  have hC := archimedeanWeilConst_lt_5377_div_1000
  have hlog : (1212 / 1000 : ℝ) ≤ Real.log (1 + 4 * (10 : ℝ) ^ 2 / 169) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := exp_le_sq_taylor_of_le_two (y := 1212 / 1000) (B := 1834 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
        norm_num)
    norm_num at h ⊢; linarith
  have harg : 1 + 4 * (10 : ℝ) ^ 2 / 169 = 569 / 169 := by norm_num
  rw [harg] at hlog ⊢
  norm_num at hlog ⊢; linarith

private lemma psiLb3_gap_ten_le_of_log_le {a B : ℝ}
    (hlog : Real.log ((1 + 4 * (10 : ℝ) ^ 2 / 169) / (1 + 4 * a ^ 2 / 169)) ≤ B) :
    psiLb3 10 - psiLb3 a ≤
      ((4 * (10 : ℝ) ^ 2) / (1 / 4 + 10 ^ 2) + ((4 / 5 : ℝ) * 10 ^ 2) / (25 / 4 + 10 ^ 2) +
        ((4 / 9 : ℝ) * 10 ^ 2) / (81 / 4 + 10 ^ 2)) -
      ((4 * a ^ 2) / (1 / 4 + a ^ 2) + ((4 / 5 : ℝ) * a ^ 2) / (25 / 4 + a ^ 2) +
        ((4 / 9 : ℝ) * a ^ 2) / (81 / 4 + a ^ 2)) + (1 / 2 : ℝ) * B := by
  dsimp [psiLb3]
  have hsub : Real.log (1 + 4 * (10 : ℝ) ^ 2 / 169) - Real.log (1 + 4 * a ^ 2 / 169) =
      Real.log ((1 + 4 * (10 : ℝ) ^ 2 / 169) / (1 + 4 * a ^ 2 / 169)) :=
    (Real.log_div (by positivity) (by positivity)).symm
  linarith

private lemma log_le_of_sum_ge {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hsum : r ≤ ∑ k ∈ Finset.range 10, B ^ k / (k.factorial : ℝ)) :
    Real.log r ≤ B := by
  rw [Real.log_le_iff_le_exp hr]
  exact le_trans hsum (Real.sum_le_exp_of_nonneg hB 10)

private lemma psiLb3_gap_ten_0 : psiLb3 10 - psiLb3 0 ≤ 573 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 0) (B := 1215 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_1 : psiLb3 10 - psiLb3 1 ≤ 238 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 1) (B := 1192 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_2 : psiLb3 10 - psiLb3 2 ≤ 153 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 2) (B := 1125 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_3 : psiLb3 10 - psiLb3 3 ≤ 113 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 3) (B := 1022 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_4 : psiLb3 10 - psiLb3 4 ≤ 85 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 4) (B := 894 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_5 : psiLb3 10 - psiLb3 5 ≤ 65 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 5) (B := 750 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_6 : psiLb3 10 - psiLb3 6 ≤ 48 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 6) (B := 599 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

private lemma psiLb3_gap_ten_8 : psiLb3 10 - psiLb3 8 ≤ 21 / 100 := by
  have h := psiLb3_gap_ten_le_of_log_le (a := 8) (B := 293 / 1000)
    (log_le_of_sum_ge (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
  norm_num at h; linarith

/-- Elementary Cauchy–Schwarz bound for continuous ODD functions on `[-L/2, L/2]`
    (ZERO moment assumptions!): `‖compactFourier L g t‖^2 ≤ min L (L^3 t^2 / 12) * ‖g‖_2^2`. -/
private lemma compactFourier_odd_norm_sq_le {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ}
    (hg : Continuous g) (hodd : ∀ u, g (-u) = -g u) (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤
      min L (L ^ 3 * t ^ 2 / 12) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hab : -L / 2 ≤ L / 2 := by linarith
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
  rw [min_mul_of_nonneg _ _ hN2_nn]
  refine le_min (fourierTransform_norm_sq_le_L_mul_L2 hL hg t) ?_
  have hcos_zero : ∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) : ℝ) : ℂ)) = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => g u * (((Real.cos (t * u) : ℝ) : ℂ))) (a := -L / 2) (b := L / 2)
    have harg : (fun u : ℝ => g (-u) * (((Real.cos (t * -u) : ℝ) : ℂ))) =
        fun u => -(g u * (((Real.cos (t * u) : ℝ) : ℂ))) := by
      ext u; rw [hodd u, mul_neg, Real.cos_neg]; ring
    rw [harg, intervalIntegral.integral_neg] at hcomp
    have h1 : -(-L / 2) = L / 2 := by ring
    have h2 : -(L / 2) = -L / 2 := by ring
    rw [h1, h2] at hcomp
    have h2z : (2 : ℂ) * ∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) : ℝ) : ℂ)) = 0 := by
      linear_combination -hcomp
    exact (mul_eq_zero.mp h2z).resolve_left (by norm_num)
  have hsin_eq : compactFourier L g t =
      Complex.I * ∫ u in (-L / 2)..(L / 2), g u * (((Real.sin (t * u) : ℝ) : ℂ)) := by
    dsimp [compactFourier]
    have hsplit : (fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        fun u => g u * (((Real.cos (t * u) : ℝ) : ℂ)) +
          Complex.I * (g u * (((Real.sin (t * u) : ℝ) : ℂ))) := by
      ext u
      have harg : Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
    have hc : Continuous (fun u : ℝ => g u * (((Real.cos (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hs : Continuous (fun u : ℝ => g u * (((Real.sin (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
    have his : Continuous (fun u : ℝ => Complex.I * (g u * (((Real.sin (t * u) : ℝ) : ℂ)))) :=
      continuous_const.mul hs
    rw [hsplit, intervalIntegral.integral_add (hc.intervalIntegrable _ _) (his.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, hcos_zero, zero_add]
  have hnorm_le : ‖compactFourier L g t‖ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u| := by
    rw [hsin_eq, norm_mul, Complex.norm_I, one_mul]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    have hcl : Continuous (fun u : ℝ => ‖g u * (((Real.sin (t * u) : ℝ) : ℂ))‖) :=
      (hg.mul (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id)))).norm
    have hcr : Continuous (fun u : ℝ => ‖g u‖ * |t * u|) :=
      hg.norm.mul (continuous_abs.comp (continuous_const.mul continuous_id))
    refine intervalIntegral.integral_mono_on hab (hcl.intervalIntegrable _ _) (hcr.intervalIntegrable _ _) fun u _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (norm_nonneg _)
  have hw_int : ∫ u in (-L / 2)..(L / 2), (|t * u|) ^ 2 = L ^ 3 * t ^ 2 / 12 := by
    have hrew : (fun u : ℝ => (|t * u|) ^ 2) = fun u => t ^ 2 * u ^ 2 := by
      ext u; rw [sq_abs]; ring
    rw [hrew, intervalIntegral.integral_const_mul, integral_pow]; ring
  let A : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  let B : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u|
  let W : ℝ := ∫ u in (-L / 2)..(L / 2), (|t * u|) ^ 2
  have hdisc : ∀ c : ℝ, 0 ≤ A * c ^ 2 - 2 * B * c + W := by
    intro c
    have hint : 0 ≤ ∫ u in (-L / 2)..(L / 2), (c * ‖g u‖ - |t * u|) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
    have hexp : (fun u : ℝ => (c * ‖g u‖ - |t * u|) ^ 2) =
        fun u => c ^ 2 * ‖g u‖ ^ 2 - 2 * c * (‖g u‖ * |t * u|) + (|t * u|) ^ 2 := by ext u; ring
    rw [hexp] at hint
    have hi1 : IntervalIntegrable (fun u : ℝ => c ^ 2 * ‖g u‖ ^ 2) volume (-L / 2) (L / 2) :=
      ((hg.norm.pow 2).const_mul _).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => 2 * c * (‖g u‖ * |t * u|)) volume (-L / 2) (L / 2) :=
      ((hg.norm.mul (continuous_abs.comp (continuous_const.mul continuous_id))).const_mul _).intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun u : ℝ => (|t * u|) ^ 2) volume (-L / 2) (L / 2) :=
      ((continuous_abs.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
    dsimp [A, B, W]; linarith
  have hcs : B ^ 2 ≤ W * A := by
    by_cases hA0 : A = 0
    · by_contra hgt; push Not at hgt
      have hB_ne : B ≠ 0 := by intro hB; rw [hB, hA0] at hgt; norm_num at hgt
      have hval := hdisc ((W + 1) / (2 * B))
      rw [hA0, zero_mul, zero_sub] at hval
      have hs : 2 * B * ((W + 1) / (2 * B)) = W + 1 := by field_simp [hB_ne]
      linarith
    · have hA_pos : 0 < A := lt_of_le_of_ne hN2_nn (Ne.symm hA0)
      have hval := hdisc (B / A)
      have hs : A * (B / A) ^ 2 - 2 * B * (B / A) + W = W - B ^ 2 / A := by
        field_simp [ne_of_gt hA_pos]; ring
      rw [hs] at hval
      have hle : B ^ 2 / A ≤ W := by linarith
      exact (div_le_iff₀ hA_pos).mp hle |> fun h => by linarith
  dsimp [A, B, W] at hcs
  rw [hw_int] at hcs
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2) hcs

/-- THEOREM I.2 (EXPANDED UNRESTRICTED ODD CONTINUOUS WEIL POSITIVITY ON `0 < L ≤ 2/5` —
    +33% OVER MODULE #13's `L ≤ 3/10`, ZERO MOMENT ASSUMPTIONS, ZERO DISCRETIZATION!):
    For EVERY `0 < L ≤ 2 / 5` and EVERY continuous odd `g : ℝ → ℂ`:
      `(1 / 20) * ∫ u in (-L/2)..(L/2), ‖g u‖^2 ≤ weilTotal L g`. -/
theorem weilTotal_continuous_pos_odd_up_to_two_fifths {L : ℝ}
    (hL0 : 0 < L) (hL : L ≤ 2 / 5) {g : ℝ → ℂ} (hg : Continuous g)
    (hodd : ∀ u, g (-u) = -g u)
    (hparseval : (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hint_arch : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    (hint_pl : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2)) :
    (1 / 20 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hprime0 : weilPrime L g = 0 :=
    weilPrime_eq_zero_of_le_log_two (by linarith [log_two_ge_6931]) g
  let K : ℝ → ℝ := fun t => min (2 / 5 : ℝ) (((2 / 5 : ℝ) ^ 3 / 12) * t ^ 2)
  have hK_cont : Continuous K :=
    continuous_const.min (continuous_const.mul (continuous_pow 2))
  have hK_even : ∀ t, K (-t) = K t := fun t => by dsimp [K]; ring_nf
  have hK_bound : ∀ t : ℝ, ‖compactFourier L g t‖ ^ 2 ≤ K t * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    intro t
    refine le_trans (compactFourier_odd_norm_sq_le (le_of_lt hL0) hg hodd t)
      (mul_le_mul_of_nonneg_right ?_ hN2_nn)
    dsimp [K]
    have hL3 : L ^ 3 ≤ (2 / 5 : ℝ) ^ 3 := pow_le_pow_left₀ (le_of_lt hL0) hL 3
    refine le_min (le_trans (min_le_left _ _) hL) (le_trans (min_le_right _ _) ?_)
    have : L ^ 3 * t ^ 2 / 12 = (L ^ 3 / 12) * t ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg t]
  have harch := weilArch_psiLb3_envelope_lower hL0 (T := 10) (by norm_num) hK_cont hK_even hK_bound
    hparseval hint_arch hint_pl
  have hpole := weilPole_lower_bound_all (le_of_lt hL0) hg
  -- Bound `∫_0^10 (psiLb3 10 - psiLb3 t) * K t dt` over 8 panels `[0, 1, 2, 3, 4, 5, 6, 8, 10]`!
  have hcont_f : Continuous (fun t : ℝ => (psiLb3 10 - psiLb3 t) * K t) :=
    (continuous_const.sub psiLb3_cont).mul hK_cont
  have hsplit : ∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t =
      (∫ t in (0 : ℝ)..1, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (1 : ℝ)..2, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (2 : ℝ)..3, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (3 : ℝ)..4, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (4 : ℝ)..5, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (5 : ℝ)..6, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (6 : ℝ)..8, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (8 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t) := by
    have h := fun a b c : ℝ =>
      (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont_f.intervalIntegrable a b) (hcont_f.intervalIntegrable b c)).symm
    rw [h 0 8 10, h 0 6 8, h 0 5 6, h 0 4 5, h 0 3 4, h 0 2 3, h 0 1 2]
  have hp1 := panel_integral_pow_le (T := 10) (a := 0) (b := 1) (G := 573 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_0
  have hp2 := panel_integral_pow_le (T := 10) (a := 1) (b := 2) (G := 238 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_1
  have hp3 := panel_integral_pow_le (T := 10) (a := 2) (b := 3) (G := 153 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_2
  have hp4 := panel_integral_pow_le (T := 10) (a := 3) (b := 4) (G := 113 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_3
  have hp5 := panel_integral_pow_le (T := 10) (a := 4) (b := 5) (G := 85 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_4
  have hp6 := panel_integral_pow_le (T := 10) (a := 5) (b := 6) (G := 65 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_5
  have hp7 := panel_integral_pow_le (T := 10) (a := 6) (b := 8) (G := 48 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_6
  have hp8 := panel_integral_pow_le (T := 10) (a := 8) (b := 10) (G := 21 / 100) (c := 2 / 5)
    (d := (2 / 5 : ℝ) ^ 3 / 12) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_8
  norm_num at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8
  have hint_ub : ∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t ≤ 79 / 100 := by
    rw [hsplit]; dsimp [K]; linarith
  have hpen : (1 / Real.pi) * (∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t) ≤ 252 / 1000 := by
    have hpi := pi_gt_31415
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t :=
      intervalIntegral.integral_nonneg (by norm_num) fun t ht =>
        mul_nonneg (sub_nonneg.mpr (psiLb3_mono_nonneg ht.1 ht.2))
          (le_min (by norm_num) (by positivity))
    have hdiv := mul_le_mul (one_div_le_one_div_of_le (by norm_num) (le_of_lt hpi)) hint_ub hnn (by norm_num)
    refine le_trans hdiv (by norm_num)
  have hpole_pen : 2 * (Real.sinh (L / 2) - L / 2) ≤ 1 / 250 := by
    have hy0 : 0 ≤ L / 2 := by linarith
    have hy1 : L / 2 ≤ 1 / 5 := by linarith
    have hpos := exp_le_taylor_small hy0 (by linarith) (n := 4) (by norm_num)
    have habs_n : |-(L / 2)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hy0]; linarith
    have hneg := Real.exp_bound habs_n (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hpos hneg
    rw [abs_neg, abs_of_nonneg hy0] at hneg
    have hlo := (abs_le.mp hneg).1
    rw [Real.sinh_eq]
    have h3 : (L / 2) ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := pow_le_pow_left₀ hy0 hy1 3
    have h4 : (L / 2) ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hy0 hy1 4
    norm_num at hpos hlo h3 h4; linarith
  have hcoeff : (1 / 20 : ℝ) ≤ (psiLb3 10 - (1 / Real.pi) * (∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t)) -
      2 * (Real.sinh (L / 2) - L / 2) := by linarith [psiLb3_ten_ge]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal; rw [hprime0, sub_zero]
  linarith [harch, hpole, hmul]

/-- THEOREM I.3 (EXPANDED ZERO-MEAN EVEN CONTINUOUS WEIL POSITIVITY ON `0 < L ≤ 11/20` —
    +24% OVER MODULE #13's `L ≤ 4/9`, REACHING 79% OF `ln 2` WITH ZERO DISCRETIZATION!):
    For EVERY `0 < L ≤ 11 / 20` and EVERY continuous even zero-mean `g : ℝ → ℂ`:
      `(1 / 20) * ∫ u in (-L/2)..(L/2), ‖g u‖^2 ≤ weilTotal L g`. -/
theorem weilTotal_continuous_pos_even_zeroMean_up_to_eleven_twentieths {L : ℝ}
    (hL0 : 0 < L) (hL : L ≤ 11 / 20) {g : ℝ → ℂ} (hg : Continuous g)
    (heven : ∀ u, g (-u) = g u) (hmean : ∫ u in (-L / 2)..(L / 2), g u = 0)
    (hparseval : (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hint_arch : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    (hint_pl : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2)) :
    (1 / 20 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hprime0 : weilPrime L g = 0 :=
    weilPrime_eq_zero_of_le_log_two (by linarith [log_two_ge_6931]) g
  have hpole_nn : 0 ≤ weilPole L g := weilPole_even_nonneg L hg heven
  let K : ℝ → ℝ := fun t => min (11 / 20 : ℝ) (((11 / 20 : ℝ) ^ 5 / 320) * t ^ 4)
  have hK_cont : Continuous K :=
    continuous_const.min (continuous_const.mul (continuous_pow 4))
  have hK_even : ∀ t, K (-t) = K t := fun t => by dsimp [K]; ring_nf
  have hK_bound : ∀ t : ℝ, ‖compactFourier L g t‖ ^ 2 ≤ K t * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    intro t
    have hmom : ∀ k : ℕ, k < 1 → ∫ u in (-L / 2)..(L / 2), ((u ^ (2 * k) : ℝ) : ℂ) * g u = 0 := by
      intro k hk
      have hk0 : k = 0 := by omega
      rw [hk0]
      simpa using hmean
    have h1 := compactFourier_even_moments_norm_sq_le (le_of_lt hL0) 1 hg heven hmom t
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hN2_nn)
    dsimp [K]
    have hL5 : L ^ 5 ≤ (11 / 20 : ℝ) ^ 5 := pow_le_pow_left₀ (le_of_lt hL0) hL 5
    refine le_min (le_trans (min_le_left _ _) hL) (le_trans (min_le_right _ _) ?_)
    norm_num [Nat.factorial]
    have ht4 : 0 ≤ t ^ 4 := by positivity
    nlinarith
  have harch := weilArch_psiLb3_envelope_lower hL0 (T := 10) (by norm_num) hK_cont hK_even hK_bound
    hparseval hint_arch hint_pl
  have hcont_f : Continuous (fun t : ℝ => (psiLb3 10 - psiLb3 t) * K t) :=
    (continuous_const.sub psiLb3_cont).mul hK_cont
  have hsplit : ∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t =
      (∫ t in (0 : ℝ)..2, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (2 : ℝ)..3, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (3 : ℝ)..4, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (4 : ℝ)..5, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (5 : ℝ)..6, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (6 : ℝ)..8, (psiLb3 10 - psiLb3 t) * K t) +
      (∫ t in (8 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t) := by
    have h := fun a b c : ℝ =>
      (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont_f.intervalIntegrable a b) (hcont_f.intervalIntegrable b c)).symm
    rw [h 0 8 10, h 0 6 8, h 0 5 6, h 0 4 5, h 0 3 4, h 0 2 3]
  have hp1 := panel_integral_pow_le (T := 10) (a := 0) (b := 2) (G := 573 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_0
  have hp2 := panel_integral_pow_le (T := 10) (a := 2) (b := 3) (G := 153 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_2
  have hp3 := panel_integral_pow_le (T := 10) (a := 3) (b := 4) (G := 113 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_3
  have hp4 := panel_integral_pow_le (T := 10) (a := 4) (b := 5) (G := 85 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_4
  have hp5 := panel_integral_pow_le (T := 10) (a := 5) (b := 6) (G := 65 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_5
  have hp6 := panel_integral_pow_le (T := 10) (a := 6) (b := 8) (G := 48 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_6
  have hp7 := panel_integral_pow_le (T := 10) (a := 8) (b := 10) (G := 21 / 100) (c := 11 / 20)
    (d := (11 / 20 : ℝ) ^ 5 / 320) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) psiLb3_gap_ten_8
  norm_num at hp1 hp2 hp3 hp4 hp5 hp6 hp7
  have hint_ub : ∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t ≤ 82 / 100 := by
    rw [hsplit]; dsimp [K]; linarith
  have hpen : (1 / Real.pi) * (∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t) ≤ 262 / 1000 := by
    have hpi := pi_gt_31415
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t :=
      intervalIntegral.integral_nonneg (by norm_num) fun t ht =>
        mul_nonneg (sub_nonneg.mpr (psiLb3_mono_nonneg ht.1 ht.2))
          (le_min (by norm_num) (by positivity))
    have hdiv := mul_le_mul (one_div_le_one_div_of_le (by norm_num) (le_of_lt hpi)) hint_ub hnn (by norm_num)
    refine le_trans hdiv (by norm_num)
  have hcoeff : (1 / 20 : ℝ) ≤ psiLb3 10 - (1 / Real.pi) * (∫ t in (0 : ℝ)..10, (psiLb3 10 - psiLb3 t) * K t) := by
    linarith [psiLb3_ten_ge]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal; rw [hprime0, sub_zero]
  linarith [harch, hpole_nn, hmul]

/-- Helper: Exact two-prime (`p = 2, 3`) prime-shift norm bound for `0 < L ≤ 6 / 5`:
    `|weilPrime L g| ≤ (log 2 / √2 + log 3 / √3) * ∫ ‖g‖^2` (using the disjoint-half 1/2 factor!). -/
private lemma weilPrime_two_three_bound {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 6 / 5)
    {g : ℝ → ℂ} (hg : Continuous g) :
    |weilPrime L g| ≤ (Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3) *
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hexp_lt4 : Real.exp L < 4 := by
    have h1 : Real.exp L ≤ Real.exp (6 / 5) := Real.exp_le_exp.mpr hL
    have h2 := exp_le_sq_taylor_of_le_two (y := 6 / 5) (B := 183 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
        norm_num)
    norm_num at h2; linarith
  have hfl : Nat.floor (Real.exp L) ≤ 3 := by
    have hlt4 : Nat.floor (Real.exp L) < 4 := (Nat.floor_lt (le_of_lt (Real.exp_pos L))).mpr hexp_lt4
    omega
  have hlog2_ge : L / 2 ≤ Real.log 2 := by linarith [log_two_ge_6931]
  have hlog3_ge : L / 2 ≤ Real.log 3 := by linarith [log_three_ge_10986]
  have hvm2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hvm3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  dsimp [weilPrime]
  have hcase : Nat.floor (Real.exp L) ≤ 1 ∨ Nat.floor (Real.exp L) = 2 ∨ Nat.floor (Real.exp L) = 3 := by omega
  rcases hcase with hle1 | h2 | h3
  · have hemp : Finset.Icc 2 (Nat.floor (Real.exp L)) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hemp, Finset.sum_empty, mul_zero, abs_zero]
    exact mul_nonneg (add_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _))
      (div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _))) hN2_nn
  · rw [h2, Finset.Icc_self, Finset.sum_singleton, hvm2]
    have hge2 : Real.log 2 ≤ L := by
      have h1 : (2 : ℝ) ≤ Real.exp L := by
        have := (Nat.le_floor_iff (le_of_lt (Real.exp_pos L))).mp (le_of_eq h2.symm)
        exact_mod_cast this
      have := Real.log_le_log (by norm_num) h1; rwa [Real.log_exp] at this
    have hov2 := shift_overlap_re_le_half_L2_of_disjoint hlog2_ge hge2 hg
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _))]
    have h2' : 2 * (Real.log 2 / Real.sqrt 2 *
        |(∫ u in (-L / 2 + Real.log 2)..(L / 2), g u * starRingEnd ℂ (g (u - Real.log 2))).re|) ≤
        Real.log 2 / Real.sqrt 2 * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
      have hnn : 0 ≤ Real.log 2 / Real.sqrt 2 := div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hov2 hnn
      linarith
    have h3_nn : 0 ≤ Real.log 3 / Real.sqrt 3 * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
      mul_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)) hN2_nn
    push_cast at h2' ⊢; linarith
  · rw [h3, show Finset.Icc 2 3 = {2, 3} by decide, Finset.sum_pair (by decide), hvm2, hvm3]
    have hge3 : Real.log 3 ≤ L := by
      have h1 : (3 : ℝ) ≤ Real.exp L := by
        have := (Nat.le_floor_iff (le_of_lt (Real.exp_pos L))).mp (le_of_eq h3.symm)
        exact_mod_cast this
      have := Real.log_le_log (by norm_num) h1; rwa [Real.log_exp] at this
    have hge2 : Real.log 2 ≤ L := le_trans (Real.log_le_log (by norm_num) (by norm_num)) hge3
    have hov2 := shift_overlap_re_le_half_L2_of_disjoint hlog2_ge hge2 hg
    have hov3 := shift_overlap_re_le_half_L2_of_disjoint hlog3_ge hge3 hg
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_add_le
      (Real.log 2 / Real.sqrt 2 * (∫ u in (-L / 2 + Real.log ((2 : ℕ) : ℝ))..(L / 2), g u * starRingEnd ℂ (g (u - Real.log ((2 : ℕ) : ℝ)))).re)
      (Real.log 3 / Real.sqrt 3 * (∫ u in (-L / 2 + Real.log ((3 : ℕ) : ℝ))..(L / 2), g u * starRingEnd ℂ (g (u - Real.log ((3 : ℕ) : ℝ)))).re)
    rw [abs_mul, abs_mul,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)),
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _))] at htri
    have hn2 : 0 ≤ Real.log 2 / Real.sqrt 2 := div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
    have hn3 : 0 ≤ Real.log 3 / Real.sqrt 3 := div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
    push_cast at htri ⊢
    have hm2 := mul_le_mul_of_nonneg_left hov2 hn2
    have hm3 := mul_le_mul_of_nonneg_left hov3 hn3
    linarith

/-- THEOREM I.4 (FIRST TWO-PRIME-ACTIVE `p = 2, 3` ZERO-DISCRETIZATION CONTINUOUS WEIL
    POSITIVITY BEYOND `ln 3`, ALL THE WAY TO `0 < L ≤ 6/5`!):
    Nearly DOUBLING Module #17's single-prime threshold (`3/4 → 6/5`) and crossing the SECOND
    prime threshold `ln 3 ≈ 1.0986 < 6/5 = 1.20` with BOTH `vonMangoldt 2` AND `vonMangoldt 3`
    live and ZERO discretization: for EVERY `0 < L ≤ 6/5` and EVERY continuous even `g` with
    `m = 20` vanishing even moments:
      `(1 / 20) * ∫ u in (-L/2)..(L/2), ‖g u‖^2 ≤ weilTotal L g`. -/
theorem weilTotal_continuous_pos_primes_two_three_active_up_to_six_fifths {L : ℝ}
    (hL0 : 0 < L) (hL : L ≤ 6 / 5) {g : ℝ → ℂ} (hg : Continuous g)
    (heven : ∀ u, g (-u) = g u)
    (hmom : ∀ k : ℕ, k < 20 → ∫ u in (-L / 2)..(L / 2), ((u ^ (2 * k) : ℝ) : ℂ) * g u = 0)
    (hparseval : (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) =
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hint_arch : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    (hint_pl : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2)) :
    (1 / 20 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  have hN2_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hpole_nn : 0 ≤ weilPole L g := weilPole_even_nonneg L hg heven
  have hprime := (abs_le.mp (weilPrime_two_three_bound hL0 hL hg)).2
  -- Prime penalty constant `log 2 / √2 + log 3 / √3 ≤ 1125 / 1000`
  have hBprime : Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3 ≤ 1125 / 1000 := by
    have hsq2 : (1414 / 1000 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hsq3 : (1732 / 1000 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.log 2 / Real.sqrt 2 ≤ (6932 / 10000 : ℝ) / (1414 / 1000) :=
      div_le_div₀ (by norm_num) log_two_le_6932 (by norm_num) hsq2
    have h3 : Real.log 3 / Real.sqrt 3 ≤ (10987 / 10000 : ℝ) / (1732 / 1000) :=
      div_le_div₀ (by norm_num) log_three_le_10987 (by norm_num) hsq3
    norm_num at h2 h3; linarith
  -- Single-panel `m = 20` Taylor envelope on `[0, 25]` using `40! ≥ 8 * 10^47`!
  have hfac40_sq : (64 * (10 : ℝ) ^ 94) ≤ (((40 : ℕ).factorial : ℝ) ^ 2) := by
    have hstep10 : ∀ n : ℕ, Nat.factorial (n + 10) =
        (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) *
        (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * Nat.factorial n := fun n => by
      simp only [Nat.factorial_succ]; ring
    have hf10 : Nat.factorial 10 = 3628800 := by
      rw [show (10 : ℕ) = 0 + 10 by rfl, hstep10]; norm_num [Nat.factorial]
    have hf20 : Nat.factorial 20 = 2432902008176640000 := by
      rw [show (20 : ℕ) = 10 + 10 by rfl, hstep10, hf10]
    have hf30 : Nat.factorial 30 = 265252859812191058636308480000000 := by
      rw [show (30 : ℕ) = 20 + 10 by rfl, hstep10, hf20]
    have hf40_nat : (8 * 10 ^ 47 : ℕ) ≤ Nat.factorial 40 := by
      rw [show (40 : ℕ) = 30 + 10 by rfl, hstep10, hf30]; norm_num
    have hf40 : (8 * (10 : ℝ) ^ 47) ≤ ((40 : ℕ).factorial : ℝ) := by exact_mod_cast hf40_nat
    have hsq := pow_le_pow_left₀ (by positivity) hf40 2
    norm_num at hsq ⊢
  let c20 : ℝ := (1 / 10000000000 : ℝ) ^ 11 / 20000
  let K : ℝ → ℝ := fun t => min (6 / 5 : ℝ) (c20 * t ^ 80)
  have hK_cont : Continuous K :=
    (fun (a b : ℝ) => (continuous_const : Continuous (fun _ : ℝ => a)).min
      (continuous_const.mul (continuous_pow 80))) (6 / 5) c20
  have hK_even : ∀ t, K (-t) = K t := fun t => by dsimp [K]; ring_nf
  have hK_bound : ∀ t : ℝ, ‖compactFourier L g t‖ ^ 2 ≤ K t * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    intro t
    have h1 := compactFourier_even_moments_norm_sq_le (le_of_lt hL0) 20 hg heven hmom t
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hN2_nn)
    dsimp [K]
    have hL81 : L ^ 81 ≤ (6 / 5 : ℝ) ^ 81 := pow_le_pow_left₀ (le_of_lt hL0) hL 81
    refine le_min (le_trans (min_le_left _ _) hL) (le_trans (min_le_right _ _) ?_)
    have ht80 : 0 ≤ t ^ 80 := by positivity
    have hden_ge : (81 : ℝ) * (2 : ℝ) ^ 80 * (64 * (10 : ℝ) ^ 94) ≤
        (81 : ℝ) * (2 : ℝ) ^ 80 * (((40 : ℕ).factorial : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hfac40_sq (by positivity)
    have hc20_ge : (6 / 5 : ℝ) ^ 81 / ((81 : ℝ) * (2 : ℝ) ^ 80 * (64 * (10 : ℝ) ^ 94)) ≤ c20 := by
      dsimp [c20]; norm_num
    calc L ^ 81 * t ^ 80 / ((81 : ℝ) * (2 : ℝ) ^ 80 * (((40 : ℕ).factorial : ℝ) ^ 2))
      _ ≤ (6 / 5 : ℝ) ^ 81 * t ^ 80 / ((81 : ℝ) * (2 : ℝ) ^ 80 * (64 * (10 : ℝ) ^ 94)) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hL81 ht80) (by positivity) hden_ge
      _ = (6 / 5 : ℝ) ^ 81 / ((81 : ℝ) * (2 : ℝ) ^ 80 * (64 * (10 : ℝ) ^ 94)) * t ^ 80 := by ring
      _ ≤ c20 * t ^ 80 := mul_le_mul_of_nonneg_right hc20_ge ht80
  have harch := weilArch_psiLb3_envelope_lower hL0 (T := 25) (by norm_num) hK_cont hK_even hK_bound
    hparseval hint_arch hint_pl
  -- Lower bound `psiLb3 25 ≥ 1222 / 1000`
  have hpsi25 : (1222 / 1000 : ℝ) ≤ psiLb3 25 := by
    unfold psiLb3
    have hC := archimedeanWeilConst_lt_5377_div_1000
    have hlog : (2758 / 1000 : ℝ) ≤ Real.log (1 + 4 * (25 : ℝ) ^ 2 / 169) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h := exp_le_cube_taylor_of_le_three (y := 2758 / 1000) (B := 2508 / 1000)
        (by norm_num) (by norm_num) (by norm_num) (by
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
          norm_num)
      norm_num at h ⊢; linarith
    have harg : 1 + 4 * (25 : ℝ) ^ 2 / 169 = 2669 / 169 := by norm_num
    rw [harg] at hlog ⊢
    norm_num at hlog ⊢; linarith
  -- Upper bound `psiLb3 25 - psiLb3 0 ≤ 67 / 10`
  have hgap25 : psiLb3 25 - psiLb3 0 ≤ 67 / 10 := by
    unfold psiLb3
    have hlog : Real.log (1 + 4 * (25 : ℝ) ^ 2 / 169) ≤ 14 / 5 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 7 / 5 by norm_num) 10
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
      have hsq : Real.exp (14 / 5) = (Real.exp (7 / 5)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num
      rw [hsq]
      have hle : (405 / 100 : ℝ) ≤ Real.exp (7 / 5) := by norm_num at h; linarith
      have hp := pow_le_pow_left₀ (by norm_num) hle 2
      norm_num at hp ⊢; linarith
    have harg : 1 + 4 * (25 : ℝ) ^ 2 / 169 = 2669 / 169 := by norm_num
    rw [harg] at hlog ⊢
    norm_num at hlog ⊢; linarith
  -- Single-panel bound on `[0, 25]`: `∫_0^25 (psiLb3 25 - psiLb3 t) * K t dt ≤ (67/10) * c20 * 25^81 / 81 ≤ 1 / 100`!
  have hp_single := panel_integral_pow_le (T := 25) (a := 0) (b := 25) (G := 67 / 10)
    (c := 6 / 5) (d := c20) 80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp [c20]; positivity) hgap25
  have hc20_eval : (67 / 10 : ℝ) * (c20 * ((25 ^ (80 + 1) - 0 ^ (80 + 1)) / ((80 + 1 : ℕ) : ℝ))) ≤ 1 / 100 := by
    dsimp [c20]; norm_num
  have hint_ub : ∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t) * K t ≤ 1 / 100 := by
    refine le_trans hp_single (le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) hc20_eval)
  have hpen : (1 / Real.pi) * (∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t) * K t) ≤ 1 / 100 := by
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t) * K t :=
      intervalIntegral.integral_nonneg (by norm_num) fun t ht =>
        mul_nonneg (sub_nonneg.mpr (psiLb3_mono_nonneg ht.1 ht.2)) (le_min (by norm_num) (by dsimp [c20]; positivity))
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [pi_gt_31415]
    have h1 := mul_le_mul (one_div_le_one_div_of_le (by norm_num) hpi) hint_ub hnn (by norm_num)
    rw [one_div]; norm_num at h1; linarith
  have hcoeff : (1 / 20 : ℝ) ≤ (psiLb3 25 - (1 / Real.pi) * (∫ t in (0 : ℝ)..25, (psiLb3 25 - psiLb3 t) * K t)) -
      (Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal
  linarith [harch, hpole_nn, hprime, hmul]

-- ==============================================================================
-- PART II: ROUTE A — EXACT CLIFFORD-TORUS / BOHR ERGODIC KURAMOTO DECOHERENCE
-- ==============================================================================

/-- Exact diagonal Bohr mean-square weight `D(L) = ∑_{2 ≤ n ≤ ⌊e^L⌋} Λ(n)^2 / n`. -/
noncomputable def primeKuramotoDiagEnergy (L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
    (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ)

/-- Helper: Exact integral of `Real.cos (ω * t)` on `[-T, T]` equals `2 * sin(ω T) / ω` for `ω ≠ 0`. -/
private lemma integral_cos_symm_eq {ω T : ℝ} (hω : ω ≠ 0) :
    ∫ t in (-T)..T, Real.cos (ω * t) = 2 * Real.sin (ω * T) / ω := by
  let F : ℝ → ℝ := fun t => Real.sin (ω * t) / ω
  have hd : ∀ t ∈ Set.uIcc (-T) T, HasDerivAt F (Real.cos (ω * t)) t := by
    intro t _
    have h1 := ((Real.hasDerivAt_sin (ω * t)).comp t ((hasDerivAt_id' t).const_mul ω)).div_const ω
    refine h1.congr_deriv ?_; field_simp [hω]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  dsimp [F]
  rw [show ω * -T = -(ω * T) by ring, Real.sin_neg]; ring

/-- Helper: Continuity of a finite sum of continuous real functions. -/
private lemma continuous_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [continuous_const]
  | insert y t hy ih =>
    have hrew : (fun z => ∑ i ∈ insert y t, f i z) = fun z => f y z + ∑ i ∈ t, f i z := by
      ext z; exact Finset.sum_insert hy
    rw [hrew]
    exact (hf y (Finset.mem_insert_self y t)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Helper: Finite-sum interval integral (explicit `Finset.induction_on`). -/
private lemma intervalIntegral_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    ∫ t in a..b, (∑ i ∈ s, f i t) = ∑ i ∈ s, ∫ t in a..b, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hcx : Continuous (f x) := hf x (Finset.mem_insert_self x s)
    have hcs : Continuous (fun t => ∑ i ∈ s, f i t) :=
      continuous_sum_real s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hrew : (fun t => ∑ i ∈ insert x s, f i t) = fun t => f x t + ∑ i ∈ s, f i t := by
      ext t; exact Finset.sum_insert hx
    rw [hrew, intervalIntegral.integral_add (hcx.intervalIntegrable _ _) (hcs.intervalIntegrable _ _),
        Finset.sum_insert hx, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- THEOREM II.1 (EXACT FINITE-HORIZON BOHR MEAN-SQUARE IDENTITY FOR THE PRIME KURAMOTO ORDER):
    For EVERY `L : ℝ` and EVERY `T > 0`:
      `(1 / (2 * T)) * ∫ t in (-T)..T, ‖primeKuramotoOrder L t‖^2 =
        primeKuramotoDiagEnergy L +
          (1 / T) * ∑ m ∈ Icc 2 ⌊e^L⌋, ∑ n ∈ (Icc 2 ⌊e^L⌋).erase m,
            (Λ(m) / √m) * (Λ(n) / √n) * (sin(T * log(m/n)) / log(m/n))`. -/
theorem primeKuramotoOrder_bohr_mean_square_identity (L : ℝ) {T : ℝ} (hT : 0 < T) :
    (1 / (2 * T)) * (∫ t in (-T)..T, ‖primeKuramotoOrder L t‖ ^ 2) =
      primeKuramotoDiagEnergy L +
        (1 / T) * ∑ m ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
          ∑ n ∈ (Finset.Icc 2 (Nat.floor (Real.exp L))).erase m,
            (ArithmeticFunction.vonMangoldt m / Real.sqrt (m : ℝ)) *
            (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
            (Real.sin (T * Real.log ((m : ℝ) / (n : ℝ))) / Real.log ((m : ℝ) / (n : ℝ))) := by
  classical
  set S : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp L))
  let w : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
  -- Step 1: Pointwise expansion `‖K_L(t)‖^2 = ∑ m ∈ S, ∑ n ∈ S, w m * w n * cos(t * log(m/n))`!
  have hnorm_sq : ∀ t : ℝ, ‖primeKuramotoOrder L t‖ ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S, w m * w n * Real.cos (Real.log ((m : ℝ) / (n : ℝ)) * t) := by
    intro t
    have hmul : (‖primeKuramotoOrder L t‖ ^ 2 : ℝ) =
        (primeKuramotoOrder L t * starRingEnd ℂ (primeKuramotoOrder L t)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    rw [hmul]
    dsimp [primeKuramotoOrder]
    rw [map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (by omega : 0 < m)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (by omega : 0 < n)
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hconj_arg : (starRingEnd ℂ) (-Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ))) =
        Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ)) := by
      rw [map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]; ring
    rw [hconj_arg]
    have hprod : ((w m : ℂ) * Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ)))) *
        ((w n : ℂ) * Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ)))) =
        ((w m * w n : ℝ) : ℂ) *
          Complex.exp (((-(Real.log ((m : ℝ) / (n : ℝ)) * t) : ℝ) : ℂ) * Complex.I) := by
      have hexp : Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ))) =
          Complex.exp (((-(Real.log ((m : ℝ) / (n : ℝ)) * t) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add, Real.log_div (ne_of_gt hm_pos) (ne_of_gt hn_pos)]
        congr 1; push_cast; ring
      calc ((w m : ℂ) * Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ)))) *
            ((w n : ℂ) * Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ))))
        _ = ((w m : ℂ) * (w n : ℂ)) * (Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ))) *
            Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ)))) := by ring
        _ = ((w m * w n : ℝ) : ℂ) *
            Complex.exp (((-(Real.log ((m : ℝ) / (n : ℝ)) * t) : ℝ) : ℂ) * Complex.I) := by
            rw [hexp]; push_cast; ring
    change (((w m : ℂ) * Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ)))) *
        ((w n : ℂ) * Complex.exp (Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ))))).re = _
    rw [hprod, Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
               Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.I_re, Complex.I_im,
               Complex.sin_ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [Real.cos_neg]
  -- Step 2: Integrate term-by-term on `[-T, T]`!
  simp_rw [hnorm_sq]
  rw [intervalIntegral_sum_real S (fun m t => ∑ n ∈ S, w m * w n * Real.cos (Real.log ((m : ℝ) / (n : ℝ)) * t))
      (-T) T (fun m _ => continuous_sum_real S (fun n t => w m * w n * Real.cos (Real.log ((m : ℝ) / (n : ℝ)) * t))
        (fun n _ => continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))))]
  -- Split each inner sum `n ∈ S` into `n = m` (diagonal) and `n ∈ S.erase m` (off-diagonal)!
  have hinner : ∀ m ∈ S,
      ∫ t in (-T)..T, (∑ n ∈ S, w m * w n * Real.cos (Real.log ((m : ℝ) / (n : ℝ)) * t)) =
        (2 * T) * ((ArithmeticFunction.vonMangoldt m) ^ 2 / (m : ℝ)) +
          2 * ∑ n ∈ S.erase m,
            w m * w n * (Real.sin (T * Real.log ((m : ℝ) / (n : ℝ))) / Real.log ((m : ℝ) / (n : ℝ))) := by
    intro m hm
    rw [intervalIntegral_sum_real S (fun n t => w m * w n * Real.cos (Real.log ((m : ℝ) / (n : ℝ)) * t))
        (-T) T (fun n _ => continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))]
    rw [← Finset.add_sum_erase S _ hm]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (by omega : 0 < m)
    have hdiag : ∫ t in (-T)..T, w m * w m * Real.cos (Real.log ((m : ℝ) / (m : ℝ)) * t) =
        (2 * T) * ((ArithmeticFunction.vonMangoldt m) ^ 2 / (m : ℝ)) := by
      rw [div_self (ne_of_gt hm_pos), Real.log_one]
      simp only [zero_mul, Real.cos_zero, mul_one, intervalIntegral.integral_const, smul_eq_mul]
      dsimp [w]
      have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt (le_of_lt hm_pos)
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hm_pos), ne_of_gt hm_pos]
      rw [show (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) from Real.sq_sqrt (le_of_lt hm_pos)]
      ring
    have hoff : ∑ n ∈ S.erase m, ∫ t in (-T)..T, w m * w n * Real.cos (Real.log ((m : ℝ) / (n : ℝ)) * t) =
        2 * ∑ n ∈ S.erase m,
          w m * w n * (Real.sin (T * Real.log ((m : ℝ) / (n : ℝ))) / Real.log ((m : ℝ) / (n : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hne : n ≠ m := Finset.ne_of_mem_erase hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by
        have := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hn)).1; exact_mod_cast (by omega : 0 < n)
      have hω_ne : Real.log ((m : ℝ) / (n : ℝ)) ≠ 0 := by
        intro h0
        have hdiv1 : (m : ℝ) / (n : ℝ) = 1 := by
          have := congrArg Real.exp h0
          rw [Real.exp_log (div_pos hm_pos hn_pos), Real.exp_zero] at this; exact this
        have heq : (m : ℝ) = (n : ℝ) := by rwa [div_eq_one_iff_eq (ne_of_gt hn_pos)] at hdiv1
        exact hne ((Nat.cast_injective heq).symm)
      rw [intervalIntegral.integral_const_mul, integral_cos_symm_eq hω_ne]
      rw [mul_comm (Real.log ((m : ℝ) / (n : ℝ))) T]; ring
    rw [hdiag, hoff]
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  dsimp [primeKuramotoDiagEnergy, w, S]
  have hT_ne : T ≠ 0 := ne_of_gt hT
  field_simp [hT_ne]

/-- THEOREM II.2 (CLIFFORD-TORUS / BOHR ERGODIC LIMIT AND EXPONENTIAL RMS COLLAPSE OF THE
    PRIME KURAMOTO COHERENCE PARAMETER):
    For EVERY `L ≥ Real.log 2`:
    (1) Exact Bohr ergodic mean-square limit on the prime Clifford torus as `T → ∞`:
        `Tendsto (fun T => (1 / (2 * T)) * ∫ t in (-T)..T, (primeKuramotoCoherence L t)^2) atTop
          (𝓝 (primeKuramotoDiagEnergy L / (primeKuramotoWeight L)^2))`,
    (2) Universal unconditional coherence decay bound (via `Λ(n) / √n ≤ 2 / e < 3/4` for all `n`):
        `primeKuramotoDiagEnergy L / (primeKuramotoWeight L)^2 ≤ (2 / Real.exp 1) / primeKuramotoWeight L`
        and `< 3 / (4 * primeKuramotoWeight L)`, proving rigorously that while `r_L(0) = 1`,
        the ergodic mean-square prime coherence decays as `O(1 / B_0(L)) = O(e^{-L/2})`! -/
theorem primeKuramotoCoherence_bohr_ergodic_limit_and_decay {L : ℝ} (hL : Real.log 2 ≤ L) :
    Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T)..T, (primeKuramotoCoherence L t) ^ 2)
      atTop (𝓝 (primeKuramotoDiagEnergy L / (primeKuramotoWeight L) ^ 2)) ∧
    primeKuramotoDiagEnergy L / (primeKuramotoWeight L) ^ 2 ≤
      (2 / Real.exp 1) / primeKuramotoWeight L ∧
    primeKuramotoDiagEnergy L / (primeKuramotoWeight L) ^ 2 <
      3 / (4 * primeKuramotoWeight L) := by
  classical
  have hB0_pos : 0 < primeKuramotoWeight L := (primeKuramotoOrder_bounds_and_sync_zero hL).1
  have hB0_ne : primeKuramotoWeight L ≠ 0 := ne_of_gt hB0_pos
  set S : Finset ℕ := Finset.Icc 2 (Nat.floor (Real.exp L))
  -- Part 1: Bohr ergodic limit via `primeKuramotoOrder_bohr_mean_square_identity` + `|sin x| ≤ 1`!
  let C_off : ℝ := ∑ m ∈ S, ∑ n ∈ S.erase m,
    (ArithmeticFunction.vonMangoldt m / Real.sqrt (m : ℝ)) *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
    (1 / |Real.log ((m : ℝ) / (n : ℝ))|)
  have htend : Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T)..T, (primeKuramotoCoherence L t) ^ 2)
      atTop (𝓝 (primeKuramotoDiagEnergy L / (primeKuramotoWeight L) ^ 2)) := by
    -- Express `r_L(t)^2 = ‖K_L(t)‖^2 / B_0(L)^2`
    have hrew : (fun T : ℝ => (1 / (2 * T)) * ∫ t in (-T)..T, (primeKuramotoCoherence L t) ^ 2) =
        fun T => ((1 / (2 * T)) * ∫ t in (-T)..T, ‖primeKuramotoOrder L t‖ ^ 2) /
          (primeKuramotoWeight L) ^ 2 := by
      ext T
      have hsq : (fun t : ℝ => (primeKuramotoCoherence L t) ^ 2) =
          fun t => ‖primeKuramotoOrder L t‖ ^ 2 / (primeKuramotoWeight L) ^ 2 := by
        ext t; dsimp [primeKuramotoCoherence]; rw [div_pow]
      rw [hsq, intervalIntegral.integral_div]; ring
    rw [hrew]
    refine Tendsto.div_const ?_ ((primeKuramotoWeight L) ^ 2)
    -- Show `(1 / (2 * T)) * ∫_{-T}^T ‖K_L(t)‖^2 → primeKuramotoDiagEnergy L` via squeeze theorem!
    have hbound : ∀ᶠ T : ℝ in atTop,
        |(1 / (2 * T)) * (∫ t in (-T)..T, ‖primeKuramotoOrder L t‖ ^ 2) -
          primeKuramotoDiagEnergy L| ≤ C_off / T := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
      rw [primeKuramotoOrder_bohr_mean_square_identity L hT, add_sub_cancel_left,
          abs_mul, abs_of_pos (one_div_pos.mpr hT), one_div_mul_eq_div]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hT)
      dsimp [C_off]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m _ => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n _ => ?_)
      rw [abs_mul, abs_mul,
          abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)),
          abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)),
          abs_div]
      have hsin : |Real.sin (T * Real.log ((m : ℝ) / (n : ℝ)))| ≤ 1 := Real.abs_sin_le_one _
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsin (abs_nonneg _))
        (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)))
    have hlim0 : Tendsto (fun T : ℝ => C_off / T) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (a := C_off) tendsto_id
    rw [Metric.tendsto_atTop] at hlim0 ⊢
    intro ε hε
    rcases hlim0 ε hε with ⟨M1, hM1⟩
    rcases Filter.eventually_atTop.mp hbound with ⟨M2, hM2⟩
    refine ⟨max M1 (max M2 1), fun T hT => ?_⟩
    rw [Real.dist_eq]
    have hT1 : M1 ≤ T := le_trans (le_max_left _ _) hT
    have hT2 : M2 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT)
    have hC_nn : 0 ≤ C_off := Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ =>
      mul_nonneg (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))) (by positivity)
    have h1 := hM1 T hT1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hC_nn (le_of_lt hTpos))] at h1
    exact lt_of_le_of_lt (hM2 T hT2) h1
  -- Part 2: Universal decay `Λ(n) / √n ≤ 2 / e` for all `n ≥ 1`!
  have hterm_max : ∀ n : ℕ, 1 ≤ n → ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) ≤ 2 / Real.exp 1 := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hlog_le : Real.log (n : ℝ) ≤ (2 / Real.exp 1) * Real.sqrt (n : ℝ) := by
      have h1 : Real.log (Real.sqrt (n : ℝ) / Real.exp 1) ≤ Real.sqrt (n : ℝ) / Real.exp 1 - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hsq_pos (Real.exp_pos 1))
      rw [Real.log_div (ne_of_gt hsq_pos) (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at h1
      have h2 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
        rw [Real.log_sqrt (le_of_lt hn_pos)]; ring
      have h3 : (2 / Real.exp 1) * Real.sqrt (n : ℝ) = 2 * (Real.sqrt (n : ℝ) / Real.exp 1) := by ring
      linarith
    have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    rw [div_le_iff₀ hsq_pos]
    exact le_trans hvm hlog_le
  have hdiag_le : primeKuramotoDiagEnergy L ≤ (2 / Real.exp 1) * primeKuramotoWeight L := by
    dsimp [primeKuramotoDiagEnergy, primeKuramotoWeight]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (by omega : 0 < n)
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hn_pos)
    have heq : (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) =
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) := by
      rw [div_mul_div_comm, hsq, sq]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hterm_max n (by have := (Finset.mem_Icc.mp hn).1; omega))
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  have hdecay1 : primeKuramotoDiagEnergy L / (primeKuramotoWeight L) ^ 2 ≤
      (2 / Real.exp 1) / primeKuramotoWeight L := by
    have hdiv := div_le_div_of_nonneg_right hdiag_le (sq_nonneg (primeKuramotoWeight L))
    have hsimp : (2 / Real.exp 1) * primeKuramotoWeight L / (primeKuramotoWeight L) ^ 2 =
        (2 / Real.exp 1) / primeKuramotoWeight L := by field_simp [hB0_ne]
    rwa [hsimp] at hdiv
  have h2e_lt : 2 / Real.exp 1 < 3 / 4 := by
    have he : (27 / 10 : ℝ) < Real.exp 1 := by
      have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 5
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
      norm_num at h; linarith
    rw [div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have hdecay2 : primeKuramotoDiagEnergy L / (primeKuramotoWeight L) ^ 2 <
      3 / (4 * primeKuramotoWeight L) := by
    refine lt_of_le_of_lt hdecay1 ?_
    have h1 := div_lt_div_of_pos_right h2e_lt hB0_pos
    have h2 : (3 / 4 : ℝ) / primeKuramotoWeight L = 3 / (4 * primeKuramotoWeight L) := by ring
    rwa [h2] at h1
  exact ⟨htend, hdecay1, hdecay2⟩

-- ==============================================================================
-- PART III: ROUTE B — HARMONIC MINIMUM PRINCIPLE ON COMPACT RECTANGLES,
--           LOGARITHMIC DIGAMMA TAIL, AND 3-4-1 CLIFFORD-TORUS PHASE POSITIVITY
-- ==============================================================================

/-- Helper: `xiResolvent` is complex-differentiable everywhere on `{z : ℂ | 1 / 2 < z.im}`. -/
private lemma differentiableOn_xiResolvent_halfPlane :
    DifferentiableOn ℂ xiResolvent {z : ℂ | (1 / 2 : ℝ) < z.im} := by
  intro z hz
  have hre : 1 ≤ (1 / 2 - Complex.I * z).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, sub_neg_eq_add]
    have hz' : (1 / 2 : ℝ) < z.im := hz
    linarith
  have hxi_ne : riemannXi (1 / 2 - Complex.I * z) ≠ 0 := riemannXi_ne_zero_of_one_le_re hre
  have hmap : Differentiable ℂ (fun w : ℂ => (1 / 2 : ℂ) - Complex.I * w) :=
    (differentiable_const _).sub ((differentiable_const _).mul differentiable_id)
  have hdiff_at : DifferentiableAt ℂ xiResolvent z := by
    unfold xiResolvent
    exact (differentiableAt_const _).mul
      (((differentiable_deriv_riemannXi.comp hmap).differentiableAt).div
        ((riemannXi_entire.comp hmap).differentiableAt) hxi_ne)
  exact hdiff_at.differentiableWithinAt

/-- THEOREM III.1 (HARMONIC MINIMUM PRINCIPLE FOR `Im(xiResolvent)` ON COMPACT RECTANGLES):
    Applying Mathlib4's Maximum Modulus Principle (`Complex.exists_mem_frontier_isMaxOn_norm`)
    to the holomorphic function `z ↦ Complex.exp (Complex.I * xiResolvent z)` on the open
    rectangle `U = {z : ℂ | -Y < z.re < Y ∧ σ₀ < z.im < σ₁}` (`1/2 < σ₀ < σ₁, 0 < Y`):
    if `0 < (xiResolvent z).im` on all four boundary edges of `[-Y, Y] × [σ₀, σ₁]`, then
    `0 < (xiResolvent z).im` throughout the ENTIRE closed rectangle `[-Y, Y] × [σ₀, σ₁]`! -/
theorem xiResolvent_im_pos_of_rectangle_boundary {σ₀ σ₁ Y : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (hσ01 : σ₀ < σ₁) (hY : 0 < Y)
    (hbot : ∀ γ ∈ Icc (-Y) Y, 0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ₀ : ℂ))).im)
    (htop : ∀ γ ∈ Icc (-Y) Y, 0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ₁ : ℂ))).im)
    (hleft : ∀ σ ∈ Icc σ₀ σ₁, 0 < (xiResolvent (((-Y : ℝ) : ℂ) + Complex.I * (σ : ℂ))).im)
    (hright : ∀ σ ∈ Icc σ₀ σ₁, 0 < (xiResolvent ((Y : ℂ) + Complex.I * (σ : ℂ))).im) :
    ∀ σ ∈ Icc σ₀ σ₁, ∀ γ ∈ Icc (-Y) Y,
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  let U : Set ℂ := {z : ℂ | -Y < z.re ∧ z.re < Y ∧ σ₀ < z.im ∧ z.im < σ₁}
  let K : Set ℂ := {z : ℂ | -Y ≤ z.re ∧ z.re ≤ Y ∧ σ₀ ≤ z.im ∧ z.im ≤ σ₁}
  have hU_sub_K : U ⊆ K := fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩
  have hK_closed : IsClosed K := by
    have h1 : IsClosed {z : ℂ | -Y ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {z : ℂ | z.re ≤ Y} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {z : ℂ | σ₀ ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    have h4 : IsClosed {z : ℂ | z.im ≤ σ₁} := isClosed_le Complex.continuous_im continuous_const
    exact ((h1.inter h2).inter h3).inter h4 |> fun h => by
      convert h using 1; ext z; simp [K, and_assoc]
  have hU_open : IsOpen U := by
    have h1 : IsOpen {z : ℂ | -Y < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z.re < Y} := isOpen_lt Complex.continuous_re continuous_const
    have h3 : IsOpen {z : ℂ | σ₀ < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have h4 : IsOpen {z : ℂ | z.im < σ₁} := isOpen_lt Complex.continuous_im continuous_const
    exact ((h1.inter h2).inter h3).inter h4 |> fun h => by
      convert h using 1; ext z; simp [U, and_assoc]
  have hcl_sub : closure U ⊆ K := closure_minimal hU_sub_K hK_closed
  -- Show `K ⊆ closure U` by explicit radial contraction toward the center `c = ⟨0, (σ₀ + σ₁)/2⟩ ∈ U`!
  have hK_sub_cl : K ⊆ closure U := by
    intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    let c : ℂ := ⟨0, (σ₀ + σ₁) / 2⟩
    let δ : ℝ := min (1 / 2) (ε / (2 * (‖z - c‖ + 1)))
    have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    let w : ℂ := ((1 - δ : ℝ) : ℂ) * z + (δ : ℂ) * c
    refine ⟨w, ?_, ?_⟩
    · have hw_re : w.re = (1 - δ) * z.re := by dsimp [w, c]; simp
      have hw_im : w.im = (1 - δ) * z.im + δ * ((σ₀ + σ₁) / 2) := by dsimp [w, c]; simp
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hw_re]; nlinarith [hz.1]
      · rw [hw_re]; nlinarith [hz.2.1]
      · rw [hw_im]; nlinarith [hz.2.2.1]
      · rw [hw_im]; nlinarith [hz.2.2.2]
    · rw [dist_eq_norm]
      have hsub : z - w = (δ : ℂ) * (z - c) := by dsimp [w]; push_cast; ring
      rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
      have hδ_le : δ ≤ ε / (2 * (‖z - c‖ + 1)) := min_le_right _ _
      calc δ * ‖z - c‖ ≤ (ε / (2 * (‖z - c‖ + 1))) * ‖z - c‖ :=
            mul_le_mul_of_nonneg_right hδ_le (norm_nonneg _)
        _ < (ε / (2 * (‖z - c‖ + 1))) * (‖z - c‖ + 1) :=
            mul_lt_mul_of_pos_left (by linarith) (div_pos hε (by positivity))
        _ = ε / 2 := by field_simp [ne_of_gt (by positivity : 0 < ‖z - c‖ + 1)]
        _ < ε := by linarith
  have hcl_eq : closure U = K := Set.Subset.antisymm hcl_sub hK_sub_cl
  have hU_bdd : Bornology.IsBounded U := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨Y + |σ₀| + |σ₁| + 1, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ Y := abs_le.mpr ⟨le_of_lt hz.1, le_of_lt hz.2.1⟩
    have him : |z.im| ≤ |σ₀| + |σ₁| := by
      have h1 : z.im ≤ |σ₁| := le_trans (le_of_lt hz.2.2.2) (le_abs_self σ₁)
      have h2 : -|σ₀| ≤ z.im := le_trans (neg_abs_le σ₀) (le_of_lt hz.2.2.1)
      exact abs_le.mpr ⟨by linarith [abs_nonneg σ₁], by linarith [abs_nonneg σ₀]⟩
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    linarith
  have hU_ne : U.Nonempty :=
    ⟨⟨0, (σ₀ + σ₁) / 2⟩, ⟨by simp; linarith, by simp; linarith, by simp; linarith, by simp; linarith⟩⟩
  let f : ℂ → ℂ := fun z => Complex.exp (Complex.I * xiResolvent z)
  have hf_diff : DiffContOnCl ℂ f U := by
    have hopen_half : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hK_half : K ⊆ {z : ℂ | (1 / 2 : ℝ) < z.im} := fun z hz => lt_of_lt_of_le hσ₀ hz.2.2.1
    have hf_on_half : DifferentiableOn ℂ f {z : ℂ | (1 / 2 : ℝ) < z.im} :=
      Complex.differentiable_exp.comp_differentiableOn
        ((differentiableOn_const Complex.I).mul differentiableOn_xiResolvent_halfPlane)
    refine ⟨hf_on_half.mono (Set.Subset.trans hU_sub_K hK_half), ?_⟩
    rw [hcl_eq]
    exact (hf_on_half.continuousOn).mono hK_half
  -- Apply Mathlib4's Maximum Modulus Principle!
  rcases Complex.exists_mem_frontier_isMaxOn_norm hU_bdd hU_ne hf_diff with ⟨z₀, hz₀_fr, hmax⟩
  -- Since `z₀ ∈ frontier U = closure U \ interior U = K \ U`, `z₀` lies on one of the 4 boundary edges!
  have hz₀_K : z₀ ∈ K := by rw [← hcl_eq]; exact hz₀_fr.1
  have hz₀_notU : z₀ ∉ U := by
    have := hz₀_fr.2
    rwa [hU_open.interior_eq] at this
  have hmk : ∀ w : ℂ, ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := fun w => by
    apply Complex.ext <;> simp
  have hz₀_pos : 0 < (xiResolvent z₀).im := by
    have hedge : z₀.re = -Y ∨ z₀.re = Y ∨ z₀.im = σ₀ ∨ z₀.im = σ₁ := by
      by_contra hall; push Not at hall
      exact hz₀_notU ⟨lt_of_le_of_ne hz₀_K.1 (Ne.symm hall.1), lt_of_le_of_ne hz₀_K.2.1 hall.2.1,
        lt_of_le_of_ne hz₀_K.2.2.1 (Ne.symm hall.2.2.1), lt_of_le_of_ne hz₀_K.2.2.2 hall.2.2.2⟩
    rcases hedge with hreL | hreR | himB | himT
    · have := hleft z₀.im ⟨hz₀_K.2.2.1, hz₀_K.2.2.2⟩
      rwa [← hreL, hmk z₀] at this
    · have := hright z₀.im ⟨hz₀_K.2.2.1, hz₀_K.2.2.2⟩
      rwa [← hreR, hmk z₀] at this
    · have := hbot z₀.re ⟨hz₀_K.1, hz₀_K.2.1⟩
      rwa [← himB, hmk z₀] at this
    · have := htop z₀.re ⟨hz₀_K.1, hz₀_K.2.1⟩
      rwa [← himT, hmk z₀] at this
  -- Every `z ∈ K = closure U` satisfies `‖f z‖ ≤ ‖f z₀‖`, i.e., `exp(-(xiResolvent z).im) ≤ exp(-(xiResolvent z₀).im)`!
  intro σ hσ γ hγ
  set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hz_cl : z ∈ closure U := by
    rw [hcl_eq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [z, hγ.1, hγ.2, hσ.1, hσ.2]
  have hle : ‖f z‖ ≤ ‖f z₀‖ := hmax hz_cl
  have hnorm_f : ∀ w : ℂ, ‖f w‖ = Real.exp (-(xiResolvent w).im) := fun w => by
    dsimp [f]; rw [Complex.norm_exp]; simp
  rw [hnorm_f, hnorm_f, Real.exp_le_exp] at hle
  linarith

/-- Helper: Exact digamma tail integral step on `[a, b]` (`0 < a ≤ b`) for `y : ℝ`:
    `∫ u in a..b, y^2 / (u * (u^2 + y^2)) = (1/2) * log(1 + y^2 / a^2) - (1/2) * log(1 + y^2 / b^2)`. -/
private lemma integral_digamma_y_tail_step (y a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, y ^ 2 / (u * (u ^ 2 + y ^ 2)) =
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / a ^ 2) -
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / b ^ 2) := by
  let F : ℝ → ℝ := fun u => -(1 / 2 : ℝ) * Real.log (1 + y ^ 2 / u ^ 2)
  have hd : ∀ u ∈ Set.uIcc a b, HasDerivAt F (y ^ 2 / (u * (u ^ 2 + y ^ 2))) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu_pos : 0 < u := lt_of_lt_of_le ha hu.1
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have harg_pos : 0 < 1 + y ^ 2 / u ^ 2 := by positivity
    have hd_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      convert hasDerivAt_pow 2 u using 1; ring
    have hd_div : HasDerivAt (fun x : ℝ => y ^ 2 / x ^ 2) (-(y ^ 2 * (2 * u)) / (u ^ 2) ^ 2) u := by
      have h := (hasDerivAt_const u (y ^ 2)).div hd_sq (pow_ne_zero 2 hu_ne)
      convert h using 1; ring
    have hd_add : HasDerivAt (fun x : ℝ => 1 + y ^ 2 / x ^ 2) (-(y ^ 2 * (2 * u)) / (u ^ 2) ^ 2) u := by
      convert (hasDerivAt_const u (1 : ℝ)).add hd_div using 1; ring
    have hd_log := (hd_add.log (ne_of_gt harg_pos)).const_mul (-(1 / 2 : ℝ))
    refine hd_log.congr_deriv ?_
    field_simp [hu_ne]
  have hcont : ContinuousOn (fun u : ℝ => y ^ 2 / (u * (u ^ 2 + y ^ 2))) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]; intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le ha hu.1
    exact ((continuousAt_const).div
      (continuousAt_id.mul ((continuousAt_id.pow 2).add continuousAt_const))
      (ne_of_gt (mul_pos hu_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu_pos) (sq_nonneg y))))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  dsimp [F]; ring

/-- THEOREM III.2 (EXACT FINITE-TERM + LOGARITHMIC TAIL LOWER BOUND ON `Re ψ(x + iy)`):
    Combining Module #16's `complex_digamma_re_ge_real_add_finset` with the integral test on the
    tail `k ≥ K`, for EVERY `x > 0`, EVERY `y : ℝ`, and EVERY `K : ℕ`:
      `(Complex.digamma x).re + ∑ k ∈ Finset.range K, y^2 / ((x + k) * ((x + k)^2 + y^2))
        + (1 / 2) * Real.log (1 + y^2 / (x + K)^2) ≤ (Complex.digamma ⟨x, y⟩).re`. -/
theorem complex_digamma_re_ge_real_add_finset_add_log_tail {x : ℝ} (hx : 0 < x) (y : ℝ) (K : ℕ) :
    (Complex.digamma (x : ℂ)).re +
      (∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2))) +
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + (K : ℝ)) ^ 2) ≤
      (Complex.digamma (⟨x, y⟩ : ℂ)).re := by
  -- For every N : ℕ, compare tail `∑_{j < N} term (K + j)` with telescoping integral!
  have hN : ∀ N : ℕ,
      (Complex.digamma (x : ℂ)).re +
        (∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2))) +
        (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + (K : ℝ)) ^ 2) -
        (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2) ≤
      (Complex.digamma (⟨x, y⟩ : ℂ)).re := by
    intro N
    have hbase := complex_digamma_re_ge_real_add_finset hx y (K + N)
    rw [Finset.sum_range_add] at hbase
    have htail : (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + (K : ℝ)) ^ 2) -
        (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2) ≤
        ∑ j ∈ Finset.range N, y ^ 2 / ((x + ((K + j : ℕ) : ℝ)) * ((x + ((K + j : ℕ) : ℝ)) ^ 2 + y ^ 2)) := by
      have hstep : ∀ j : ℕ,
          (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + j : ℕ) : ℝ)) ^ 2) -
          (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + (j + 1) : ℕ) : ℝ)) ^ 2) ≤
          y ^ 2 / ((x + ((K + j : ℕ) : ℝ)) * ((x + ((K + j : ℕ) : ℝ)) ^ 2 + y ^ 2)) := by
        intro j
        let a : ℝ := x + ((K + j : ℕ) : ℝ)
        let b : ℝ := x + ((K + (j + 1) : ℕ) : ℝ)
        have ha : 0 < a := by dsimp [a]; positivity
        have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
        have hba : b - a = 1 := by dsimp [a, b]; push_cast; ring
        rw [← integral_digamma_y_tail_step y a b ha hab]
        have hconst : ∫ _u in a..b, y ^ 2 / (a * (a ^ 2 + y ^ 2)) = y ^ 2 / (a * (a ^ 2 + y ^ 2)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hba, one_mul]
        rw [← hconst]
        refine intervalIntegral.integral_mono_on hab ?_ intervalIntegrable_const fun u hu => ?_
        · apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hab]; intro u hu
          have hup : 0 < u := lt_of_lt_of_le ha hu.1
          exact ((continuousAt_const).div
            (continuousAt_id.mul ((continuousAt_id.pow 2).add continuousAt_const))
            (ne_of_gt (mul_pos hup (add_pos_of_pos_of_nonneg (sq_pos_of_pos hup) (sq_nonneg y))))).continuousWithinAt
        · have hden : a * (a ^ 2 + y ^ 2) ≤ u * (u ^ 2 + y ^ 2) := by
            have hsq : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (le_of_lt ha) hu.1 2
            nlinarith [sq_nonneg y, hu.1]
          exact div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) hden
      have htele := Finset.sum_range_sub'
        (fun j : ℕ => (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + j : ℕ) : ℝ)) ^ 2)) N
      simp only [Nat.add_zero] at htele
      rw [← htele]
      exact Finset.sum_le_sum fun j _ => hstep j
    linarith
  -- Pass `N → ∞`: `(1/2) * log (1 + y^2 / (x + K + N)^2) → 0`!
  have hlim_zero : Tendsto (fun N : ℕ => (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2))
      atTop (𝓝 0) := by
    have hden_top : Tendsto (fun N : ℕ => (x + ((K + N : ℕ) : ℝ)) ^ 2) atTop atTop := by
      have hlin : Tendsto (fun N : ℕ => x + ((K + N : ℕ) : ℝ)) atTop atTop := by
        have h1 : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun N : ℕ => (x + (K : ℝ)) + (N : ℝ)) atTop atTop :=
          Filter.tendsto_atTop_add_const_left atTop (x + (K : ℝ)) h1
        exact h2.congr fun N => by push_cast; ring
      exact (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hlin
    have hinv : Tendsto (fun N : ℕ => y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden_top
    have h1 : Tendsto (fun N : ℕ => 1 + y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at h1
    have hlog : Tendsto (fun N : ℕ => Real.log (1 + y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2)) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp h1
    rw [Real.log_one] at hlog
    simpa using hlog.const_mul (1 / 2 : ℝ)
  set Lval : ℝ := (Complex.digamma (x : ℂ)).re +
      (∑ k ∈ Finset.range K, y ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + y ^ 2))) +
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + (K : ℝ)) ^ 2)
  have hlim_lhs : Tendsto (fun N : ℕ => Lval - (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / (x + ((K + N : ℕ) : ℝ)) ^ 2))
      atTop (𝓝 (Lval - 0)) := tendsto_const_nhds.sub hlim_zero
  rw [sub_zero] at hlim_lhs
  exact le_of_tendsto hlim_lhs (Filter.Eventually.of_forall hN)

/-- THEOREM III.3 (HADAMARD–DE LA VALLÉE POUSSIN 3-4-1 CLIFFORD-TORUS PHASE POSITIVITY LAW):
    Using the trigonometric square identity `3 + 4 cos θ + cos(2θ) = 2(1 + cos θ)^2 ≥ 0` on
    the prime Clifford torus `θ_n = γ log n`, for EVERY `β > 1` and EVERY `γ : ℝ`:
      `0 ≤ (3 * L(Λ, β) + 4 * L(Λ, ⟨β, γ⟩) + L(Λ, ⟨β, 2γ⟩)).re`
    and equivalently in terms of Mathlib4's `riemannZeta`:
      `0 ≤ (-3 * (deriv riemannZeta β / riemannZeta β) -
            4 * (deriv riemannZeta ⟨β, γ⟩ / riemannZeta ⟨β, γ⟩) -
            (deriv riemannZeta ⟨β, 2γ⟩ / riemannZeta ⟨β, 2γ⟩)).re`. -/
theorem cliffordTorus_341_zeta_logDeriv_nonneg {β : ℝ} (hβ : 1 < β) (γ : ℝ) :
    0 ≤ (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (β : ℂ) +
         4 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, γ⟩ : ℂ) +
         LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 2 * γ⟩ : ℂ)).re ∧
    0 ≤ (-3 * (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) -
         4 * (deriv riemannZeta (⟨β, γ⟩ : ℂ) / riemannZeta (⟨β, γ⟩ : ℂ)) -
         (deriv riemannZeta (⟨β, 2 * γ⟩ : ℂ) / riemannZeta (⟨β, 2 * γ⟩ : ℂ))).re := by
  have hs0 : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (β : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hβ)
  have hs1 : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, γ⟩ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hβ
  have hs2 : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 2 * γ⟩ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hβ
  -- Term-by-term real part of `LSeries.term Λ ⟨β, t⟩ n` equals `Λ(n) / n^β * cos(t * log n)`!
  have hterm_re : ∀ (t : ℝ) (n : ℕ),
      (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (⟨β, t⟩ : ℂ) n).re =
        if n = 0 then 0 else (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β) * Real.cos (t * Real.log (n : ℝ)) := by
    intro t n
    cases n with
    | zero => simp [LSeries.term]
    | succ m =>
      simp only [LSeries.term, Nat.succ_ne_zero, ↓reduceIte]
      have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hcpow : (((m + 1 : ℕ) : ℂ) ^ (⟨β, t⟩ : ℂ))⁻¹ =
          (((((m + 1 : ℕ) : ℝ) ^ β)⁻¹ : ℝ) : ℂ) *
            Complex.exp (((-(t * Real.log ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero m)]
        have hlog : Complex.log ((m + 1 : ℕ) : ℂ) = ((Real.log ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_natCast, Complex.ofReal_log (le_of_lt hm_pos)]
        rw [hlog]
        have hmul : ((Real.log ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * -(⟨β, t⟩ : ℂ) =
            ((-(β * Real.log ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) +
              ((-(t * Real.log ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp <;> ring
        rw [hmul, Complex.exp_add, ← Complex.ofReal_exp]
        congr 1
        have hrp : (((m + 1 : ℕ) : ℝ) ^ β)⁻¹ = Real.exp (-(β * Real.log ((m + 1 : ℕ) : ℝ))) := by
          rw [Real.rpow_def_of_pos hm_pos, ← Real.exp_neg]; congr 1; ring
        rw [hrp]
      rw [div_eq_mul_inv, hcpow]
      have hprod : ((ArithmeticFunction.vonMangoldt (m + 1) : ℝ) : ℂ) *
          ((((((m + 1 : ℕ) : ℝ) ^ β)⁻¹ : ℝ) : ℂ) *
            Complex.exp (((-(t * Real.log ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) =
          ((ArithmeticFunction.vonMangoldt (m + 1) / ((m + 1 : ℕ) : ℝ) ^ β : ℝ) : ℂ) *
            Complex.exp (((-(t * Real.log ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
        push_cast; rw [div_eq_mul_inv]; ring
      rw [hprod, Complex.exp_mul_I]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
                 Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
                 Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [Real.cos_neg]
  have hre_hasSum : ∀ (t : ℝ), LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, t⟩ : ℂ) →
      HasSum (fun n : ℕ => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (⟨β, t⟩ : ℂ) n).re)
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, t⟩ : ℂ)).re := by
    intro t hst
    exact (hst.hasSum.map Complex.reCLM Complex.reCLM.continuous)
  have hβ_mk : (β : ℂ) = (⟨β, 0⟩ : ℂ) := by apply Complex.ext <;> simp
  have h1 : 0 ≤ (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (β : ℂ) +
       4 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, γ⟩ : ℂ) +
       LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 2 * γ⟩ : ℂ)).re := by
    have hre_comb : (3 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (β : ℂ) +
         4 * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, γ⟩ : ℂ) +
         LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 2 * γ⟩ : ℂ)).re =
        3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 0⟩ : ℂ)).re +
        4 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, γ⟩ : ℂ)).re +
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 2 * γ⟩ : ℂ)).re := by
      rw [hβ_mk]; simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    rw [hre_comb]
    have hs0' : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, 0⟩ : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hβ
    have hh0 := (hre_hasSum 0 hs0').mul_left 3
    have hh1 := (hre_hasSum γ hs1).mul_left 4
    have hh2 := hre_hasSum (2 * γ) hs2
    have hcomb := (hh0.add hh1).add hh2
    rw [← hcomb.tsum_eq]
    refine tsum_nonneg fun n => ?_
    rw [hterm_re 0 n, hterm_re γ n, hterm_re (2 * γ) n]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte, zero_mul, Real.cos_zero, mul_one]
      have hθ : 2 * γ * Real.log (n : ℝ) = 2 * (γ * Real.log (n : ℝ)) := by ring
      rw [hθ, Real.cos_two_mul]
      have hfac : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) β)
      have hsq : 0 ≤ 2 * (1 + Real.cos (γ * Real.log (n : ℝ))) ^ 2 := by positivity
      have halg : 3 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β) +
          4 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β * Real.cos (γ * Real.log (n : ℝ))) +
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β * (2 * Real.cos (γ * Real.log (n : ℝ)) ^ 2 - 1) =
          (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β) * (2 * (1 + Real.cos (γ * Real.log (n : ℝ))) ^ 2) := by
        ring
      rw [halg]
      exact mul_nonneg hfac hsq
  refine ⟨h1, ?_⟩
  have hz0 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hβ : 1 < (β : ℂ).re)
  have hz1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hβ : 1 < (⟨β, γ⟩ : ℂ).re)
  have hz2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hβ : 1 < (⟨β, 2 * γ⟩ : ℂ).re)
  rw [hz0, hz1, hz2] at h1
  have heq : 3 * (-deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) +
      4 * (-deriv riemannZeta (⟨β, γ⟩ : ℂ) / riemannZeta (⟨β, γ⟩ : ℂ)) +
      -deriv riemannZeta (⟨β, 2 * γ⟩ : ℂ) / riemannZeta (⟨β, 2 * γ⟩ : ℂ) =
      -3 * (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) -
      4 * (deriv riemannZeta (⟨β, γ⟩ : ℂ) / riemannZeta (⟨β, γ⟩ : ℂ)) -
      (deriv riemannZeta (⟨β, 2 * γ⟩ : ℂ) / riemannZeta (⟨β, 2 * γ⟩ : ℂ)) := by ring
  rwa [heq] at h1


-- ==============================================================================
-- PART IV: ROUTE B — CLIFFORD-TORUS PRIME-PHASE EULER SPLITTING ({2, 3, 5, 7} +
--          6k ± 1 TAIL), 34-SEGMENT PHASE-PRESERVING BOUNDARY CERTIFICATE AT
--          β = 5/2 (σ = 2), AND UNCONDITIONAL GLOBAL ALL-γ DESCENT TO σ ≥ 2
--          (Re(s) ≥ 5/2) INCLUDING HOPF-BLOCH S^2 & ACCUMULATED PHASE MEMORY!
-- ==============================================================================

/-- Predicate identifying prime powers of the four Clifford-torus phase-preserved primes `{2, 3, 5, 7}`. -/
def isSmallPrimePow (n : ℕ) : Prop :=
  (∃ k : ℕ, n = 2 ^ (k + 1)) ∨ (∃ k : ℕ, n = 3 ^ (k + 1)) ∨
  (∃ k : ℕ, n = 5 ^ (k + 1)) ∨ (∃ k : ℕ, n = 7 ^ (k + 1))

/-- Exact real part of a single Clifford-torus prime Euler factor `Re((log p) * p^{-s} / (1 - p^{-s}))`
    at `s = β - iγ` (where `r = p^{-β}` and `θ = γ log p`):
      `primePhaseFactor p β γ = (log p) * (r cos θ - r^2) / (1 - 2 r cos θ + r^2)`. -/
noncomputable def primePhaseFactor (p : ℕ) (β γ : ℝ) : ℝ :=
  Real.log (p : ℝ) *
    (((p : ℝ) ^ (-β) * Real.cos (γ * Real.log (p : ℝ)) - ((p : ℝ) ^ (-β)) ^ 2) /
      (1 - 2 * (p : ℝ) ^ (-β) * Real.cos (γ * Real.log (p : ℝ)) + ((p : ℝ) ^ (-β)) ^ 2))

/-- Helper: Exact real part of `z / (1 - z)` for `z = r * exp(i θ)` (`0 < r < 1`). -/
private lemma re_div_one_sub_polar {r θ : ℝ} (_hr0 : 0 ≤ r) (_hr1 : r < 1) :
    ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) /
      (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re =
      (r * Real.cos θ - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2) := by
  set z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hz_re : z.re = r * Real.cos θ := by
    dsimp [z]; rw [Complex.exp_mul_I]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have hz_im : z.im = r * Real.sin θ := by
    dsimp [z]; rw [Complex.exp_mul_I]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  have hns : Complex.normSq (1 - z) = 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [Complex.normSq_apply]; simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hz_re, hz_im]
    have hcs := Real.cos_sq_add_sin_sq θ
    nlinarith
  rw [Complex.div_re, hns]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hz_re, hz_im]
  have hcs := Real.cos_sq_add_sin_sq θ
  have hnum : (r * Real.cos θ) * (1 - r * Real.cos θ) + (r * Real.sin θ) * (0 - r * Real.sin θ) =
      r * Real.cos θ - r ^ 2 := by nlinarith [hcs]
  rw [← add_div, hnum]

/-- Helper: Exact geometric series for a single prime `p` in `LSeries Λ ⟨β, -γ⟩`. -/
private lemma prime_pow_indicator_hasSum {p : ℕ} (hp : p.Prime) {β : ℝ} (hβ : 1 < β) (γ : ℝ) :
    HasSum
      (fun n : ℕ => if ∃ k : ℕ, n = p ^ (k + 1) then
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨β, -γ⟩ : ℂ) n else 0)
      (((Real.log (p : ℝ) : ℝ) : ℂ) *
        ((((p : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (((γ * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) /
          (1 - (((p : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (((γ * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)))) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  set z : ℂ := (((p : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (((γ * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)
  have hz_norm : ‖z‖ < 1 := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp_pos _),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hlt : (p : ℝ) ^ (-β) < (p : ℝ) ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    simpa using hlt
  have hgeom : HasSum (fun k : ℕ => z ^ (k + 1)) (z / (1 - z)) := by
    have h0 := (hasSum_geometric_of_norm_lt_one hz_norm).mul_left z
    have heq : (fun k : ℕ => z * z ^ k) = fun k => z ^ (k + 1) := by ext k; rw [pow_succ']
    have hval : z * (1 - z)⁻¹ = z / (1 - z) := by rw [div_eq_mul_inv]
    rwa [heq, hval] at h0
  have hmul := hgeom.mul_left ((Real.log (p : ℝ) : ℝ) : ℂ)
  -- Map via the injection `k ↦ p ^ (k + 1)`!
  have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) := fun a b hab => by
    have h := Nat.pow_right_injective hp.two_le hab; omega
  have hcomp : ∀ k : ℕ,
      (if ∃ j : ℕ, p ^ (k + 1) = p ^ (j + 1) then
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨β, -γ⟩ : ℂ) (p ^ (k + 1)) else 0) =
      ((Real.log (p : ℝ) : ℝ) : ℂ) * z ^ (k + 1) := by
    intro k
    have hexk : ∃ j : ℕ, p ^ (k + 1) = p ^ (j + 1) := ⟨k, rfl⟩
    simp only [hexk, ↓reduceIte]
    have hne : p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hp.ne_zero
    simp only [LSeries.term, hne, ↓reduceIte]
    have hvm : ArithmeticFunction.vonMangoldt (p ^ (k + 1)) = Real.log (p : ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    rw [hvm, div_eq_mul_inv]
    congr 1
    have hcp : (((p ^ (k + 1) : ℕ) : ℂ) ^ (⟨β, -γ⟩ : ℂ))⁻¹ = z ^ (k + 1) := by
      rw [← Complex.cpow_neg, Nat.cast_pow,
          Complex.cpow_def_of_ne_zero (pow_ne_zero (k + 1) (by exact_mod_cast hp.ne_zero))]
      have hlog : Complex.log (((p : ℂ)) ^ (k + 1)) = (((k + 1 : ℕ) : ℂ)) * ((Real.log (p : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_log (by positivity),
            Real.log_pow]; push_cast; ring
      rw [hlog]
      have hz_exp : z = Complex.exp (((-β * Real.log (p : ℝ) : ℝ) : ℂ) +
          ((γ * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
        dsimp [z]
        rw [Complex.exp_add, ← Complex.ofReal_exp, Real.rpow_def_of_pos hp_pos]
        congr 3; ring
      rw [hz_exp, ← Complex.exp_nat_mul]
      congr 1; apply Complex.ext <;> simp <;> ring
    exact hcp
  have hmul' : HasSum (fun k : ℕ =>
      if ∃ j : ℕ, p ^ (k + 1) = p ^ (j + 1) then
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨β, -γ⟩ : ℂ) (p ^ (k + 1)) else 0)
      (((Real.log (p : ℝ) : ℝ) : ℂ) * (z / (1 - z))) := by
    have heq : (fun k : ℕ =>
        if ∃ j : ℕ, p ^ (k + 1) = p ^ (j + 1) then
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨β, -γ⟩ : ℂ) (p ^ (k + 1)) else 0) =
        fun k : ℕ => ((Real.log (p : ℝ) : ℝ) : ℂ) * z ^ (k + 1) := funext hcomp
    rwa [heq]
  exact (hinj.hasSum_iff fun n hn => by
    simp only [Set.mem_range] at hn
    exact ite_eq_right_iff.mpr fun ⟨k, hk⟩ => False.elim (hn ⟨k, hk.symm⟩)).mp hmul'

/-- Helper: Pairwise disjointness of `p ^ (k + 1)` for distinct primes `p ≠ q`. -/
private lemma prime_pow_disjoint {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {n : ℕ} (h1 : ∃ k : ℕ, n = p ^ (k + 1)) (h2 : ∃ j : ℕ, n = q ^ (j + 1)) : False := by
  rcases h1 with ⟨k, rfl⟩
  rcases h2 with ⟨j, heq⟩
  have hdvd : p ∣ q ^ (j + 1) := by rw [← heq]; exact dvd_pow_self p (Nat.succ_ne_zero k)
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hdvd
  exact hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one)

/-- Helper: `x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x` for `x ≥ 0`. -/
private lemma rpow_five_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with rfl | hpos
  · norm_num
  · rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_two, ← Real.sqrt_eq_rpow]

/-- Certified rational enclosures for `p ^ (-5/2)` (`p = 2, 3, 5, 7`). -/
private lemma rpow_neg_five_halves_2 :
    (1767 / 10000 : ℝ) ≤ (2 : ℝ) ^ (-(5 / 2 : ℝ)) ∧ (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 1768 / 10000 := by
  rw [Real.rpow_neg (by norm_num), rpow_five_halves_eq (by norm_num)]
  have hs1 : (14142 / 10000 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · rw [← one_div, le_div_iff₀ (by positivity)]; nlinarith
  · rw [← one_div, div_le_iff₀ (by positivity)]; nlinarith

private lemma rpow_neg_five_halves_3 :
    (641 / 10000 : ℝ) ≤ (3 : ℝ) ^ (-(5 / 2 : ℝ)) ∧ (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 642 / 10000 := by
  rw [Real.rpow_neg (by norm_num), rpow_five_halves_eq (by norm_num)]
  have hs1 : (17320 / 10000 : ℝ) ≤ Real.sqrt 3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.sqrt 3 ≤ 17321 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · rw [← one_div, le_div_iff₀ (by positivity)]; nlinarith
  · rw [← one_div, div_le_iff₀ (by positivity)]; nlinarith

private lemma rpow_neg_five_halves_5 :
    (178 / 10000 : ℝ) ≤ (5 : ℝ) ^ (-(5 / 2 : ℝ)) ∧ (5 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 179 / 10000 := by
  rw [Real.rpow_neg (by norm_num), rpow_five_halves_eq (by norm_num)]
  have hs1 : (22360 / 10000 : ℝ) ≤ Real.sqrt 5 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.sqrt 5 ≤ 22361 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · rw [← one_div, le_div_iff₀ (by positivity)]; nlinarith
  · rw [← one_div, div_le_iff₀ (by positivity)]; nlinarith

private lemma rpow_neg_five_halves_7 :
    (77 / 10000 : ℝ) ≤ (7 : ℝ) ^ (-(5 / 2 : ℝ)) ∧ (7 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ 78 / 10000 := by
  rw [Real.rpow_neg (by norm_num), rpow_five_halves_eq (by norm_num)]
  have hs1 : (26457 / 10000 : ℝ) ≤ Real.sqrt 7 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.sqrt 7 ≤ 26458 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · rw [← one_div, le_div_iff₀ (by positivity)]; nlinarith
  · rw [← one_div, div_le_iff₀ (by positivity)]; nlinarith

/-- Helper: Any prime power `n` NOT in `isSmallPrimePow` with `2 ∣ n` or `3 ∣ n` is impossible! -/
private lemma vonMangoldt_eq_zero_of_dvd_two_or_three_not_small {n : ℕ}
    (hns : ¬ isSmallPrimePow n) (hd : 2 ∣ n ∨ 3 ∣ n) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  by_contra hne
  have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
  rw [isPrimePow_nat_iff] at hpp
  rcases hpp with ⟨p, k, hp, hk, rfl⟩
  rcases hd with h2 | h3
  · have hp2 : p = 2 := ((hp.eq_one_or_self_of_dvd 2 (Nat.prime_two.dvd_of_dvd_pow h2)).resolve_left (by decide)).symm
    subst hp2
    exact hns (Or.inl ⟨k - 1, by rw [Nat.sub_add_cancel hk]⟩)
  · have hp3 : p = 3 := ((hp.eq_one_or_self_of_dvd 3 (Nat.prime_three.dvd_of_dvd_pow h3)).resolve_left (by decide)).symm
    subst hp3
    exact hns (Or.inr (Or.inl ⟨k - 1, by rw [Nat.sub_add_cancel hk]⟩))

/-- Helper: Telescoping majorant `F(x) = (2/3) x^{-3/2} (log x + 2/3)` has `F(a) - F(a+6) ≥ 6 * log(a+6) * (a+6)^{-5/2}` for `a ≥ 25`. -/
private lemma tail_step_six_le {a : ℝ} (ha : 25 ≤ a) :
    6 * (Real.log (a + 6) / (a + 6) ^ (5 / 2 : ℝ)) ≤
      (2 / 3 : ℝ) * a ^ (-(3 / 2 : ℝ)) * (Real.log a + 2 / 3) -
      (2 / 3 : ℝ) * (a + 6) ^ (-(3 / 2 : ℝ)) * (Real.log (a + 6) + 2 / 3) := by
  let F : ℝ → ℝ := fun x => -(2 / 3 : ℝ) * x ^ (-(3 / 2 : ℝ)) * (Real.log x + 2 / 3)
  let g : ℝ → ℝ := fun x => Real.log x / x ^ (5 / 2 : ℝ)
  have hdF : ∀ x ∈ Set.uIcc a (a + 6), HasDerivAt F (g x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have h1 : HasDerivAt (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) ((-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx_ne)
    have h2 : HasDerivAt (fun t : ℝ => Real.log t + 2 / 3) (x⁻¹) x :=
      (Real.hasDerivAt_log hx_ne).add_const _
    have h3 : HasDerivAt F
        ((-(2 / 3 : ℝ) * ((-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ) - 1))) * (Real.log x + 2 / 3) +
          (-(2 / 3 : ℝ) * x ^ (-(3 / 2 : ℝ))) * x⁻¹) x :=
      (h1.const_mul (-(2 / 3 : ℝ))).mul h2
    refine h3.congr_deriv ?_
    dsimp [g]
    have hexp1 : x ^ (-(3 / 2 : ℝ) - 1) = (x ^ (5 / 2 : ℝ))⁻¹ := by
      rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx_pos)]
    have hexp2 : x ^ (-(3 / 2 : ℝ)) * x⁻¹ = (x ^ (5 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_add hx_pos,
          show -(3 / 2 : ℝ) + (-1 : ℝ) = -(5 / 2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx_pos)]
    rw [hexp1, mul_assoc (-(2 / 3 : ℝ)) (x ^ (-(3 / 2 : ℝ))) x⁻¹, hexp2, div_eq_mul_inv]; ring
  have hg_cont : ContinuousOn g (Set.uIcc a (a + 6)) := by
    rw [Set.uIcc_of_le (by linarith)]; intro x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    exact ((Real.continuousAt_log (ne_of_gt hx_pos)).div
      (Real.continuousAt_rpow_const x (5 / 2) (Or.inl (ne_of_gt hx_pos)))
      (ne_of_gt (Real.rpow_pos_of_pos hx_pos _))).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hdF hg_cont.intervalIntegrable
  -- Show `g` is antitone on `[25, ∞)` via `g'(x) = (1 - (5/2) log x) / x^(7/2) ≤ 0`!
  have hg_anti : AntitoneOn g (Ici 25) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 25)
    · intro x hx; have hx_pos : 0 < x := by linarith [mem_Ici.mp hx]
      exact ((Real.continuousAt_log (ne_of_gt hx_pos)).div
        (Real.continuousAt_rpow_const x (5 / 2) (Or.inl (ne_of_gt hx_pos)))
        (ne_of_gt (Real.rpow_pos_of_pos hx_pos _))).continuousWithinAt
    · intro x hx; have hx_pos : 0 < x := by linarith [mem_Ici.mp (interior_subset hx)]
      exact ((Real.hasDerivAt_log (ne_of_gt hx_pos)).div
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx_pos)))
        (ne_of_gt (Real.rpow_pos_of_pos hx_pos _))).differentiableAt.differentiableWithinAt
    · intro x hx; have hx25 : 25 ≤ x := interior_subset hx
      have hx_pos : 0 < x := by linarith
      have hd : HasDerivAt g ((x⁻¹ * x ^ (5 / 2 : ℝ) - Real.log x * ((5 / 2 : ℝ) * x ^ ((5 / 2 : ℝ) - 1))) /
          (x ^ (5 / 2 : ℝ)) ^ 2) x :=
        (Real.hasDerivAt_log (ne_of_gt hx_pos)).div
          (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx_pos)))
          (ne_of_gt (Real.rpow_pos_of_pos hx_pos _))
      rw [hd.deriv]
      refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
      have hxp : x⁻¹ * x ^ (5 / 2 : ℝ) = x ^ ((5 / 2 : ℝ) - 1) := by
        rw [← Real.rpow_neg_one x, ← Real.rpow_add hx_pos]; congr 1; ring
      rw [hxp]
      have hlog_ge : (1 : ℝ) ≤ Real.log x := by
        have h1 : (2 : ℝ) ≤ x := by linarith
        have h2 := Real.log_le_log (by norm_num) (show (3 : ℝ) ≤ x by linarith)
        linarith [log_three_ge_10986]
      have hrp_nn : 0 ≤ x ^ ((5 / 2 : ℝ) - 1) := Real.rpow_nonneg (le_of_lt hx_pos) _
      nlinarith
  have hconst : ∫ _x in a..(a + 6), g (a + 6) = 6 * g (a + 6) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hmono : ∫ _x in a..(a + 6), g (a + 6) ≤ ∫ x in a..(a + 6), g x :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hg_cont.intervalIntegrable
      fun x hx => hg_anti (show (25 : ℝ) ≤ x by linarith [hx.1]) (show (25 : ℝ) ≤ a + 6 by linarith) hx.2
  rw [hconst, hftc] at hmono
  dsimp [F, g] at hmono ⊢; linarith

/-- Helper: Upper bounds on `log p` for the 6 explicit tail primes `{11, 13, 17, 19, 23, 29}` via `(exp(y/2))^2`. -/
private lemma log_le_of_half_sum {p : ℝ} {B : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (h1 : 0 ≤ B / 2)
    (hsq : p ≤ (∑ k ∈ Finset.range 9, (B / 2) ^ k / (k.factorial : ℝ)) ^ 2) :
    Real.log p ≤ B := by
  rw [Real.log_le_iff_le_exp hp]
  have hhalf := Real.sum_le_exp_of_nonneg h1 9
  have hpow := pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => by positivity) hhalf 2
  have hexp : Real.exp B = (Real.exp (B / 2)) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp]; exact le_trans hsq hpow

/-- Helper: Certified `6k ± 1` residual tail bound at `β = 5 / 2`:
    `∑' n, (if isSmallPrimePow n then 0 else Λ(n) / n^(5/2)) ≤ 235 / 10000`. -/
private lemma residual_vonMangoldt_five_halves_le :
    Summable (fun n : ℕ => if isSmallPrimePow n then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)) ∧
    (∑' n : ℕ, if isSmallPrimePow n then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)) ≤
      235 / 10000 := by
  classical
  have hfull_sum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)) :=
    (vonMangoldt_lseries_norm_le_tsum (by norm_num : (1 : ℝ) < 5 / 2) 0).1
  let f : ℕ → ℝ := fun n => if isSmallPrimePow n then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ)
  have hf_sum : Summable f := hfull_sum.of_nonneg_of_le (fun n => by
      dsimp [f]; split_ifs
      · exact le_rfl
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => by
      dsimp [f]; split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · exact le_rfl)
  refine ⟨hf_sum, ?_⟩
  -- Split `∑' n, f n = (∑ n ∈ range 30, f n) + ∑' m, f (m + 30)`!
  rw [← hf_sum.sum_add_tsum_nat_add 30]
  -- Bound the head `n < 30`: ONLY `{11, 13, 17, 19, 23, 29}` are nonzero!
  have hf_zero_head : ∀ n ∈ Finset.range 30,
      n ∉ ({11, 13, 17, 19, 23, 29} : Finset ℕ) → f n = 0 := by
    intro n hn hnot
    rw [Finset.mem_range] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    dsimp [f]
    by_cases hs : isSmallPrimePow n
    · simp only [hs, ↓reduceIte]
    · simp only [hs, ↓reduceIte]
      have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
        by_cases h01 : n ≤ 1
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h01 with rfl | rfl <;>
            simp [ArithmeticFunction.vonMangoldt_apply_one]
        · by_cases hd : 2 ∣ n ∨ 3 ∣ n
          · exact vonMangoldt_eq_zero_of_dvd_two_or_three_not_small hs hd
          · -- Remaining `n < 30` with `n ≥ 2` and `¬(2 ∣ n)` and `¬(3 ∣ n)` are `{5, 7, 11, 13, 17, 19, 23, 25, 29}`!
            -- `{5, 7, 25}` are in `isSmallPrimePow`!
            have hcases : n = 5 ∨ n = 7 ∨ n = 25 := by omega
            rcases hcases with rfl | rfl | rfl
            · exact absurd (Or.inr (Or.inr (Or.inl ⟨0, by norm_num⟩))) hs
            · exact absurd (Or.inr (Or.inr (Or.inr ⟨0, by norm_num⟩))) hs
            · exact absurd (Or.inr (Or.inr (Or.inl ⟨1, by norm_num⟩))) hs
      rw [h0, zero_div]
  have hhead_eq : ∑ n ∈ Finset.range 30, f n =
      f 11 + f 13 + f 17 + f 19 + f 23 + f 29 := by
    have hsub : ({11, 13, 17, 19, 23, 29} : Finset ℕ) ⊆ Finset.range 30 := by decide
    rw [← Finset.sum_subset hsub hf_zero_head]
    simp [Finset.sum_insert, Finset.sum_singleton]; ring
  have hterm_ub : ∀ (p : ℕ) (lp_ub sp_lb B : ℝ),
      0 < (p : ℝ) → 0 < sp_lb → Real.log (p : ℝ) ≤ lp_ub → sp_lb ≤ Real.sqrt (p : ℝ) →
      lp_ub / ((p : ℝ) ^ 2 * sp_lb) ≤ B → f p ≤ B := by
    intro p lp_ub sp_lb B hp_pos hsp_pos hlp hsp hB
    dsimp [f]; split_ifs
    · have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        have hpn : 0 < p := by exact_mod_cast hp_pos
        exact_mod_cast (by omega : 1 ≤ p)
      exact le_trans (div_nonneg (le_trans (Real.log_nonneg hp1) hlp) (by positivity)) hB
    · rw [rpow_five_halves_eq (le_of_lt hp_pos)]
      have hvm : ArithmeticFunction.vonMangoldt p ≤ lp_ub :=
        le_trans ArithmeticFunction.vonMangoldt_le_log hlp
      have hden : (p : ℝ) ^ 2 * sp_lb ≤ (p : ℝ) ^ 2 * Real.sqrt (p : ℝ) :=
        mul_le_mul_of_nonneg_left hsp (sq_nonneg _)
      exact le_trans (div_le_div₀ (le_trans ArithmeticFunction.vonMangoldt_nonneg hvm) hvm (by positivity) hden) hB
  have h11 : f 11 ≤ 600 / 100000 := hterm_ub 11 (240 / 100) (3316 / 1000) _ (by norm_num) (by norm_num)
    (log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
    (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
  have h13 : f 13 ≤ 422 / 100000 := hterm_ub 13 (257 / 100) (3605 / 1000) _ (by norm_num) (by norm_num)
    (log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
    (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
  have h17 : f 17 ≤ 239 / 100000 := hterm_ub 17 (284 / 100) (4123 / 1000) _ (by norm_num) (by norm_num)
    (log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
    (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
  have h19 : f 19 ≤ 188 / 100000 := hterm_ub 19 (295 / 100) (4358 / 1000) _ (by norm_num) (by norm_num)
    (log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
    (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
  have h23 : f 23 ≤ 124 / 100000 := hterm_ub 23 (314 / 100) (4795 / 1000) _ (by norm_num) (by norm_num)
    (log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
    (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
  have h29 : f 29 ≤ 75 / 100000 := hterm_ub 29 (337 / 100) (5385 / 1000) _ (by norm_num) (by norm_num)
    (log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
    (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
  have hhead_le : ∑ n ∈ Finset.range 30, f n ≤ 1648 / 100000 := by rw [hhead_eq]; linarith
  -- Bound the tail `∑' m, f (m + 30)` by telescoping `F(x) = (2/3) x^{-3/2} (log x + 2/3)`!
  -- Group `m + 30` into blocks of 6: `[30 + 6k, ..., 35 + 6k]` where ONLY `31 + 6k` and `35 + 6k` can be nonzero!
  let Φ : ℝ → ℝ := fun x => (2 / 3 : ℝ) * x ^ (-(3 / 2 : ℝ)) * (Real.log x + 2 / 3)
  have hΦ_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ Φ x := fun x hx =>
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
      (add_nonneg (Real.log_nonneg hx) (by norm_num))
  have htail_part : ∀ M : ℕ, ∑ m ∈ Finset.range (6 * M), f (m + 30) ≤ (1 / 3 : ℝ) * Φ 25 := by
    intro M
    have hblock : ∀ k : ℕ,
        ∑ r ∈ Finset.range 6, f (6 * k + r + 30) ≤
          (1 / 6 : ℝ) * (Φ ((6 * k + 25 : ℕ) : ℝ) - Φ ((6 * (k + 1) + 25 : ℕ) : ℝ)) +
          (1 / 6 : ℝ) * (Φ ((6 * k + 29 : ℕ) : ℝ) - Φ ((6 * (k + 1) + 29 : ℕ) : ℝ)) := by
      intro k
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      have hz0 : f (6 * k + 0 + 30) = 0 := by
        dsimp [f]; split_ifs with hs
        · rfl
        · rw [vonMangoldt_eq_zero_of_dvd_two_or_three_not_small hs (Or.inl ⟨3 * k + 15, by omega⟩), zero_div]
      have hz2 : f (6 * k + 2 + 30) = 0 := by
        dsimp [f]; split_ifs with hs
        · rfl
        · rw [vonMangoldt_eq_zero_of_dvd_two_or_three_not_small hs (Or.inl ⟨3 * k + 16, by omega⟩), zero_div]
      have hz3 : f (6 * k + 3 + 30) = 0 := by
        dsimp [f]; split_ifs with hs
        · rfl
        · rw [vonMangoldt_eq_zero_of_dvd_two_or_three_not_small hs (Or.inr ⟨2 * k + 11, by omega⟩), zero_div]
      have hz4 : f (6 * k + 4 + 30) = 0 := by
        dsimp [f]; split_ifs with hs
        · rfl
        · rw [vonMangoldt_eq_zero_of_dvd_two_or_three_not_small hs (Or.inl ⟨3 * k + 17, by omega⟩), zero_div]
      have hf1 : f (6 * k + 1 + 30) ≤ (1 / 6 : ℝ) * (Φ ((6 * k + 25 : ℕ) : ℝ) - Φ ((6 * (k + 1) + 25 : ℕ) : ℝ)) := by
        have hge25 : (25 : ℝ) ≤ ((6 * k + 25 : ℕ) : ℝ) := by exact_mod_cast (by omega : 25 ≤ 6 * k + 25)
        have hstep := tail_step_six_le (a := ((6 * k + 25 : ℕ) : ℝ)) hge25
        have hcast1 : ((6 * k + 25 : ℕ) : ℝ) + 6 = ((6 * k + 1 + 30 : ℕ) : ℝ) := by push_cast; ring
        have hcast2 : ((6 * k + 25 : ℕ) : ℝ) + 6 = ((6 * (k + 1) + 25 : ℕ) : ℝ) := by push_cast; ring
        dsimp [f]; split_ifs
        · dsimp [Φ]; rw [← hcast2]
          have hnn : 0 ≤ Real.log (((6 * k + 25 : ℕ) : ℝ) + 6) / (((6 * k + 25 : ℕ) : ℝ) + 6) ^ (5 / 2 : ℝ) :=
            div_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg (by linarith) _)
          linarith
        · have hvm : ArithmeticFunction.vonMangoldt (6 * k + 1 + 30) ≤ Real.log ((6 * k + 1 + 30 : ℕ) : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log
          have hle1 : ArithmeticFunction.vonMangoldt (6 * k + 1 + 30) / ((6 * k + 1 + 30 : ℕ) : ℝ) ^ (5 / 2 : ℝ) ≤
              Real.log ((6 * k + 1 + 30 : ℕ) : ℝ) / ((6 * k + 1 + 30 : ℕ) : ℝ) ^ (5 / 2 : ℝ) :=
            div_le_div_of_nonneg_right hvm (Real.rpow_nonneg (by positivity) _)
          rw [← hcast1] at hle1 ⊢; dsimp [Φ]; rw [← hcast2]; linarith
      have hf5 : f (6 * k + 5 + 30) ≤ (1 / 6 : ℝ) * (Φ ((6 * k + 29 : ℕ) : ℝ) - Φ ((6 * (k + 1) + 29 : ℕ) : ℝ)) := by
        have hge25 : (25 : ℝ) ≤ ((6 * k + 29 : ℕ) : ℝ) := by exact_mod_cast (by omega : 25 ≤ 6 * k + 29)
        have hstep := tail_step_six_le (a := ((6 * k + 29 : ℕ) : ℝ)) hge25
        have hcast1 : ((6 * k + 29 : ℕ) : ℝ) + 6 = ((6 * k + 5 + 30 : ℕ) : ℝ) := by push_cast; ring
        have hcast2 : ((6 * k + 29 : ℕ) : ℝ) + 6 = ((6 * (k + 1) + 29 : ℕ) : ℝ) := by push_cast; ring
        dsimp [f]; split_ifs
        · dsimp [Φ]; rw [← hcast2]
          have hnn : 0 ≤ Real.log (((6 * k + 29 : ℕ) : ℝ) + 6) / (((6 * k + 29 : ℕ) : ℝ) + 6) ^ (5 / 2 : ℝ) :=
            div_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg (by linarith) _)
          linarith
        · have hvm : ArithmeticFunction.vonMangoldt (6 * k + 5 + 30) ≤ Real.log ((6 * k + 5 + 30 : ℕ) : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log
          have hle1 : ArithmeticFunction.vonMangoldt (6 * k + 5 + 30) / ((6 * k + 5 + 30 : ℕ) : ℝ) ^ (5 / 2 : ℝ) ≤
              Real.log ((6 * k + 5 + 30 : ℕ) : ℝ) / ((6 * k + 5 + 30 : ℕ) : ℝ) ^ (5 / 2 : ℝ) :=
            div_le_div_of_nonneg_right hvm (Real.rpow_nonneg (by positivity) _)
          rw [← hcast1] at hle1 ⊢; dsimp [Φ]; rw [← hcast2]; linarith
      rw [hz0, hz2, hz3, hz4]; linarith
    -- Induction on `M`!
    have hsum_blocks : ∑ m ∈ Finset.range (6 * M), f (m + 30) =
        ∑ k ∈ Finset.range M, ∑ r ∈ Finset.range 6, f (6 * k + r + 30) := by
      induction M with
      | zero => simp
      | succ M ih =>
        rw [show 6 * (M + 1) = 6 * M + 6 by ring, Finset.sum_range_add, ih,
            Finset.sum_range_succ (fun k => ∑ r ∈ Finset.range 6, f (6 * k + r + 30)) M]
    rw [hsum_blocks]
    have hle := Finset.sum_le_sum fun k (_ : k ∈ Finset.range M) => hblock k
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_range_sub' (fun k => Φ ((6 * k + 25 : ℕ) : ℝ)) M,
        Finset.sum_range_sub' (fun k => Φ ((6 * k + 29 : ℕ) : ℝ)) M] at hle
    have hΦ29_le_25 : Φ 29 ≤ Φ 25 := by
      -- Since `Φ` has derivative `-(log x)/x^(5/2) ≤ 0` on `[25, 29]`, or direct: `29^(-3/2) < 25^(-3/2)`?
      -- Even simpler: direct numeric `Φ 29 ≤ Φ 25` via `29^(3/2) = 29*√29 ≥ 29*5.385 = 156.165` vs `25^(3/2) = 125`!
      dsimp [Φ]
      have h25 : (25 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 125 := by
        rw [Real.rpow_neg (by norm_num), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
            Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow,
            show Real.sqrt 25 = 5 by rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num]
        norm_num
      have h29_pow : (29 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 / 156 := by
        rw [Real.rpow_neg (by norm_num), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
            Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
        have hs : (5385 / 1000 : ℝ) ≤ Real.sqrt 29 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        rw [← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have hl25 : (32 / 10 : ℝ) ≤ Real.log 25 := by
        rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num; linarith [log_five_ge_16094]
      have hl29 : Real.log 29 ≤ 337 / 100 :=
        log_le_of_half_sum (by norm_num) (by norm_num) (by norm_num) (by
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num)
      rw [h25]
      have hmul := mul_le_mul h29_pow (show Real.log 29 + 2 / 3 ≤ 337 / 100 + 2 / 3 by linarith)
        (add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)) (by norm_num)
      norm_num at hmul ⊢; linarith
    have hnn1 : 0 ≤ Φ ((6 * M + 25 : ℕ) : ℝ) := hΦ_nonneg _ (by exact_mod_cast (by omega : 1 ≤ 6 * M + 25))
    have hnn2 : 0 ≤ Φ ((6 * M + 29 : ℕ) : ℝ) := hΦ_nonneg _ (by exact_mod_cast (by omega : 1 ≤ 6 * M + 29))
    push_cast at hnn1 hnn2
    norm_num at hle
    linarith
  have htail_tsum : ∑' m : ℕ, f (m + 30) ≤ (1 / 3 : ℝ) * Φ 25 := by
    have hsum_shift : Summable (fun m : ℕ => f (m + 30)) := (summable_nat_add_iff 30).mpr hf_sum
    have htend : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range (6 * M), f (m + 30)) atTop (𝓝 (∑' m : ℕ, f (m + 30))) :=
      hsum_shift.hasSum.tendsto_sum_nat.comp (Filter.tendsto_atTop_mono (fun M => show M ≤ 6 * M by omega) tendsto_id)
    exact le_of_tendsto htend (Filter.Eventually.of_forall htail_part)
  have hΦ25_ub : (1 / 3 : ℝ) * Φ 25 ≤ 691 / 100000 := by
    dsimp [Φ]
    have h25 : (25 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 125 := by
      rw [Real.rpow_neg (by norm_num), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow,
          show Real.sqrt 25 = 5 by rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num]
      norm_num
    have hl25 : Real.log 25 ≤ 3219 / 1000 := by
      rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num; linarith [log_five_le_16095]
    rw [h25]; linarith
  linarith

/-- THEOREM IV.1 (EXACT CLIFFORD-TORUS PRIME-PHASE EULER SPLITTING FOR `{2, 3, 5, 7}` +
    CERTIFIED `6k ± 1` TAIL BOUND AT `β = 5 / 2`):
    For EVERY `β > 1` and EVERY `γ : ℝ`, the real part of the von Mangoldt L-series decomposes
    EXACTLY into the four Clifford-torus prime-phase factors `p ∈ {2, 3, 5, 7}` plus a residual
    bounded by the non-`{2,3,5,7}` prime-power series; and at `β = 5 / 2`, this entire residual
    over ALL primes `p ≥ 11` combined is bounded by `235 / 10000` (`0.0235`)! -/
theorem cliffordTorus_primePhase_euler_split_2357 {β : ℝ} (hβ : 1 < β) (γ : ℝ) :
    ∃ rem : ℝ,
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)).re =
        primePhaseFactor 2 β γ + primePhaseFactor 3 β γ +
        primePhaseFactor 5 β γ + primePhaseFactor 7 β γ + rem ∧
      |rem| ≤ ∑' n : ℕ, if isSmallPrimePow n then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β := by
  classical
  have hsumm : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hβ
  let term : ℕ → ℂ := LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨β, -γ⟩ : ℂ)
  let tP : ℕ → ℕ → ℂ := fun p n => if ∃ k : ℕ, n = p ^ (k + 1) then term n else 0
  let tRem : ℕ → ℂ := fun n => if isSmallPrimePow n then 0 else term n
  have hsplit_pt : ∀ n : ℕ, term n = tP 2 n + tP 3 n + tP 5 n + tP 7 n + tRem n := by
    intro n
    dsimp [tP, tRem, isSmallPrimePow]
    by_cases h2 : ∃ k : ℕ, n = 2 ^ (k + 1)
    · have h3 : ¬ ∃ k : ℕ, n = 3 ^ (k + 1) := fun h => prime_pow_disjoint Nat.prime_two Nat.prime_three (by decide) h2 h
      have h5 : ¬ ∃ k : ℕ, n = 5 ^ (k + 1) := fun h => prime_pow_disjoint Nat.prime_two Nat.prime_five (by decide) h2 h
      have h7 : ¬ ∃ k : ℕ, n = 7 ^ (k + 1) := fun h => prime_pow_disjoint Nat.prime_two Nat.prime_seven (by decide) h2 h
      simp [h2, h3, h5, h7]
    · by_cases h3 : ∃ k : ℕ, n = 3 ^ (k + 1)
      · have h5 : ¬ ∃ k : ℕ, n = 5 ^ (k + 1) := fun h => prime_pow_disjoint Nat.prime_three Nat.prime_five (by decide) h3 h
        have h7 : ¬ ∃ k : ℕ, n = 7 ^ (k + 1) := fun h => prime_pow_disjoint Nat.prime_three Nat.prime_seven (by decide) h3 h
        simp [h2, h3, h5, h7]
      · by_cases h5 : ∃ k : ℕ, n = 5 ^ (k + 1)
        · have h7 : ¬ ∃ k : ℕ, n = 7 ^ (k + 1) := fun h => prime_pow_disjoint Nat.prime_five Nat.prime_seven (by decide) h5 h
          simp [h2, h3, h5, h7]
        · by_cases h7 : ∃ k : ℕ, n = 7 ^ (k + 1)
          · simp [h2, h3, h5, h7]
          · simp [h2, h3, h5, h7]
  have hs2 := prime_pow_indicator_hasSum Nat.prime_two hβ γ
  have hs3 := prime_pow_indicator_hasSum Nat.prime_three hβ γ
  have hs5 := prime_pow_indicator_hasSum Nat.prime_five hβ γ
  have hs7 := prime_pow_indicator_hasSum Nat.prime_seven hβ γ
  have hrem_norm : ∀ n : ℕ, ‖tRem n‖ = if isSmallPrimePow n then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β := by
    intro n; dsimp [tRem, term]; split_ifs
    · simp
    · cases n with
      | zero => simp [LSeries.term]
      | succ m =>
        simp only [LSeries.term, Nat.succ_ne_zero, ↓reduceIte, norm_div, Complex.norm_real,
                   Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m)]
  have hsRem_norm : Summable (fun n : ℕ => ‖tRem n‖) := by
    refine hsumm.norm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    dsimp [tRem]; split_ifs
    · simp
    · exact le_refl _
  have hsRem : Summable tRem := hsRem_norm.of_norm
  have hsum_all := (((hs2.add hs3).add hs5).add hs7).add hsRem.hasSum
  have heq_fn : (fun n => tP 2 n + tP 3 n + tP 5 n + tP 7 n + tRem n) = term := by
    ext n; exact (hsplit_pt n).symm
  rw [heq_fn] at hsum_all
  have hlser_eq : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ) = _ :=
    hsumm.hasSum.unique hsum_all
  have hre_p : ∀ (p : ℕ), p.Prime →
      ((((Real.log (p : ℝ) : ℝ) : ℂ) *
        ((((p : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (((γ * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) /
          (1 - (((p : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (((γ * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I))))).re =
        primePhaseFactor p β γ := by
    intro p hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hr0 : 0 ≤ (p : ℝ) ^ (-β) := Real.rpow_nonneg (le_of_lt hp_pos) _
    have hr1 : (p : ℝ) ^ (-β) < 1 := by
      have hlt : (p : ℝ) ^ (-β) < (p : ℝ) ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
      simpa using hlt
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        re_div_one_sub_polar hr0 hr1]
    rfl
  refine ⟨(∑' n : ℕ, tRem n).re, ?_, ?_⟩
  · have hre := congrArg Complex.re hlser_eq
    simp only [Complex.add_re] at hre
    rw [hre_p 2 Nat.prime_two, hre_p 3 Nat.prime_three, hre_p 5 Nat.prime_five, hre_p 7 Nat.prime_seven] at hre
    exact hre
  · calc |(∑' n : ℕ, tRem n).re| ≤ ‖∑' n : ℕ, tRem n‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' n : ℕ, ‖tRem n‖ := norm_tsum_le_tsum_norm hsRem_norm
      _ = ∑' n : ℕ, if isSmallPrimePow n then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β := by
          simp_rw [hrem_norm]

/-- Helper: Tight lower bound `(Complex.digamma ((5/4 : ℝ) : ℂ)).re ≥ -233 / 1000`
    via `complex_digamma_real_diff_ge_finset (K = 16 + N)` + pure rational telescoping `1/69`! -/
private lemma digamma_five_fourths_ge : (-233 / 1000 : ℝ) ≤ (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re := by
  have h1 : (Complex.digamma ((1 : ℝ) : ℂ)).re = -Real.eulerMascheroniConstant := by
    have h0 := Complex.digamma_nat_add_one 0
    simp only [Nat.cast_zero, zero_add, harmonic_zero, Rat.cast_zero, zero_sub] at h0
    have h1c : ((1 : ℝ) : ℂ) = 1 := by norm_num
    rw [h1c, h0]; simp
  -- For EVERY `N : ℕ`, `psi(5/4) ≥ -γ_E + ∑_{k < 16} (1/4)/((1+k)(5/4+k)) + (1/69 - (1/4)/(17+N+1/4))`!
  have hN : ∀ N : ℕ,
      -Real.eulerMascheroniConstant +
        (∑ k ∈ Finset.range 16, (1 / 4 : ℝ) / ((1 + (k : ℝ)) * (5 / 4 + (k : ℝ)))) +
        ((1 / 69 : ℝ) - (1 / 4 : ℝ) / ((17 : ℝ) + (N : ℝ) + 1 / 4)) ≤
      (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re := by
    intro N
    have hbase := complex_digamma_real_diff_ge_finset (a := 1) (b := 5 / 4) (by norm_num) (by norm_num) (16 + N)
    rw [h1, Finset.sum_range_add] at hbase
    have htail : (1 / 69 : ℝ) - (1 / 4 : ℝ) / ((17 : ℝ) + (N : ℝ) + 1 / 4) ≤
        ∑ j ∈ Finset.range N, (5 / 4 - 1 : ℝ) / ((1 + ((16 + j : ℕ) : ℝ)) * (5 / 4 + ((16 + j : ℕ) : ℝ))) := by
      have hstep : ∀ j : ℕ,
          (1 / 4 : ℝ) / ((17 : ℝ) + (j : ℝ) + 1 / 4) - (1 / 4 : ℝ) / ((17 : ℝ) + ((j + 1 : ℕ) : ℝ) + 1 / 4) ≤
          (5 / 4 - 1 : ℝ) / ((1 + ((16 + j : ℕ) : ℝ)) * (5 / 4 + ((16 + j : ℕ) : ℝ))) := by
        intro j
        have hdiff : (1 / 4 : ℝ) / ((17 : ℝ) + (j : ℝ) + 1 / 4) - (1 / 4 : ℝ) / ((17 : ℝ) + ((j + 1 : ℕ) : ℝ) + 1 / 4) =
            (1 / 4 : ℝ) / (((17 : ℝ) + (j : ℝ) + 1 / 4) * ((17 : ℝ) + (j : ℝ) + 5 / 4)) := by
          push_cast; field_simp [ne_of_gt (by positivity : (0 : ℝ) < 17 + (j : ℝ) + 1 / 4),
            ne_of_gt (by positivity : (0 : ℝ) < 17 + ((j : ℝ) + 1) + 1 / 4)]; ring
        rw [hdiff]
        have heq1 : (5 / 4 - 1 : ℝ) = 1 / 4 := by norm_num
        have heq2 : (1 + ((16 + j : ℕ) : ℝ)) * (5 / 4 + ((16 + j : ℕ) : ℝ)) =
            ((17 : ℝ) + (j : ℝ)) * ((17 : ℝ) + (j : ℝ) + 1 / 4) := by push_cast; ring
        rw [heq1, heq2]
        refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
        have h17 : 0 ≤ (17 : ℝ) + (j : ℝ) := by positivity
        nlinarith
      have htele := Finset.sum_range_sub' (fun j : ℕ => (1 / 4 : ℝ) / ((17 : ℝ) + (j : ℝ) + 1 / 4)) N
      have h0 : (1 / 4 : ℝ) / ((17 : ℝ) + ((0 : ℕ) : ℝ) + 1 / 4) = 1 / 69 := by norm_num
      rw [h0] at htele
      rw [← htele]
      exact Finset.sum_le_sum fun j _ => hstep j
    have h16eq : ∑ k ∈ Finset.range 16, (5 / 4 - 1 : ℝ) / ((1 + (k : ℝ)) * (5 / 4 + (k : ℝ))) =
        ∑ k ∈ Finset.range 16, (1 / 4 : ℝ) / ((1 + (k : ℝ)) * (5 / 4 + (k : ℝ))) := by
      refine Finset.sum_congr rfl fun k _ => by norm_num
    linarith
  have hlim0 : Tendsto (fun N : ℕ => (1 / 4 : ℝ) / ((17 : ℝ) + (N : ℝ) + 1 / 4)) atTop (𝓝 0) := by
    have hden : Tendsto (fun N : ℕ => (17 : ℝ) + (N : ℝ) + 1 / 4) atTop atTop := by
      have h1 := Filter.tendsto_atTop_add_const_left atTop (69 / 4 : ℝ) tendsto_natCast_atTop_atTop
      exact h1.congr fun N => by ring
    exact tendsto_const_nhds.div_atTop hden
  set C0 : ℝ := -Real.eulerMascheroniConstant +
      (∑ k ∈ Finset.range 16, (1 / 4 : ℝ) / ((1 + (k : ℝ)) * (5 / 4 + (k : ℝ)))) + (1 / 69 : ℝ)
  have hlim_lhs : Tendsto (fun N : ℕ => C0 - (1 / 4 : ℝ) / ((17 : ℝ) + (N : ℝ) + 1 / 4)) atTop (𝓝 (C0 - 0)) :=
    tendsto_const_nhds.sub hlim0
  rw [sub_zero] at hlim_lhs
  have hC0_le : C0 ≤ (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re :=
    le_of_tendsto hlim_lhs (Filter.Eventually.of_forall fun N => by dsimp [C0]; linarith [hN N])
  have hs16 : (33472 / 100000 : ℝ) ≤ ∑ k ∈ Finset.range 16, (1 / 4 : ℝ) / ((1 + (k : ℝ)) * (5 / 4 + (k : ℝ))) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
  have hγ := eulerMascheroniConstant_lt_5813_div_10000
  dsimp [C0] at hC0_le; linarith

/-- Helper: Monotonicity of `x ↦ (r * x - r^2) / (1 - 2 * r * x + r^2)` on `[-1, 1]` for `0 < r < 1`. -/
private lemma phase_rational_mono {r x c : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hx1 : x ≤ 1) (hc1 : c ≤ 1) (hxc : x ≤ c) :
    (r * x - r ^ 2) / (1 - 2 * r * x + r ^ 2) ≤ (r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2) := by
  have hd1 : 0 < 1 - 2 * r * x + r ^ 2 := by
    have : (1 - r) ^ 2 ≤ 1 - 2 * r * x + r ^ 2 := by nlinarith
    nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]
  have hd2 : 0 < 1 - 2 * r * c + r ^ 2 := by
    have : (1 - r) ^ 2 ≤ 1 - 2 * r * c + r ^ 2 := by nlinarith
    nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]
  rw [div_le_div_iff₀ hd1 hd2]
  have hid : (r * c - r ^ 2) * (1 - 2 * r * x + r ^ 2) - (r * x - r ^ 2) * (1 - 2 * r * c + r ^ 2) =
      r * (1 - r ^ 2) * (c - x) := by ring
  have h1r : 0 < 1 - r ^ 2 := by nlinarith
  have hpos : 0 ≤ r * (1 - r ^ 2) * (c - x) := mul_nonneg (mul_nonneg (le_of_lt hr0) (le_of_lt h1r)) (sub_nonneg.mpr hxc)
  linarith

/-- Helper: Conservative rational upper bound on `primePhaseFactor p (5/2) γ` given `cos(γ log p) ≤ c`
    and enclosures `lp_lo ≤ log p ≤ lp_hi`, `r_lo ≤ p^(-5/2) ≤ r_hi` (`r_hi < 1/2`). -/
private lemma primePhaseFactor_upper {p : ℕ} {γ c lp_lo lp_hi r_lo r_hi : ℝ}
    (hlp_lo : lp_lo ≤ Real.log (p : ℝ)) (hlp_hi : Real.log (p : ℝ) ≤ lp_hi) (hlp_nn : 0 ≤ lp_lo)
    (hr_lo : r_lo ≤ (p : ℝ) ^ (-(5 / 2 : ℝ))) (hr_hi : (p : ℝ) ^ (-(5 / 2 : ℝ)) ≤ r_hi)
    (hr0 : 0 < r_lo) (hr1 : r_hi < 1 / 2) (hc1 : c ≤ 1)
    (hcos : Real.cos (γ * Real.log (p : ℝ)) ≤ c) :
    primePhaseFactor p (5 / 2) γ ≤
      if 0 ≤ c then
        if 0 ≤ r_hi * c - r_lo ^ 2 then
          lp_hi * ((r_hi * c - r_lo ^ 2) / (1 - 2 * r_hi * c + r_lo ^ 2))
        else
          lp_lo * ((r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2))
      else
        -(lp_lo * ((r_lo * (-c) + r_lo ^ 2) / (1 + 2 * r_hi * (-c) + r_hi ^ 2))) := by
  set r : ℝ := (p : ℝ) ^ (-(5 / 2 : ℝ))
  have hr_pos : 0 < r := lt_of_lt_of_le hr0 hr_lo
  have hr_lt1 : r < 1 := by linarith
  have hlog_nn : 0 ≤ Real.log (p : ℝ) := le_trans hlp_nn hlp_lo
  have hstep1 : primePhaseFactor p (5 / 2) γ ≤
      Real.log (p : ℝ) * ((r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2)) := by
    dsimp [primePhaseFactor]
    exact mul_le_mul_of_nonneg_left (phase_rational_mono hr_pos hr_lt1 (Real.cos_le_one _) hc1 hcos) hlog_nn
  refine le_trans hstep1 ?_
  have hd_r : 0 < 1 - 2 * r * c + r ^ 2 := by
    have : (1 - r) ^ 2 ≤ 1 - 2 * r * c + r ^ 2 := by nlinarith
    nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]
  split_ifs with hc0 hnum0
  · have hd_ub : 0 < 1 - 2 * r_hi * c + r_lo ^ 2 := by nlinarith [sq_nonneg r_lo]
    have hfrac : (r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2) ≤ (r_hi * c - r_lo ^ 2) / (1 - 2 * r_hi * c + r_lo ^ 2) := by
      have hnum : r * c - r ^ 2 ≤ r_hi * c - r_lo ^ 2 := by nlinarith
      have hden : 1 - 2 * r_hi * c + r_lo ^ 2 ≤ 1 - 2 * r * c + r ^ 2 := by nlinarith
      exact div_le_div₀ hnum0 hnum hd_ub hden
    exact le_trans (mul_le_mul_of_nonneg_left hfrac hlog_nn)
      (mul_le_mul_of_nonneg_right hlp_hi (div_nonneg hnum0 (le_of_lt hd_ub)))
  · push Not at hnum0
    have hd_hi : 0 < 1 - 2 * r_lo * c + r_hi ^ 2 := by nlinarith [sq_nonneg r_hi]
    have hnum_neg : r * c - r ^ 2 ≤ r_hi * c - r_lo ^ 2 := by nlinarith
    have hden_le : 1 - 2 * r * c + r ^ 2 ≤ 1 - 2 * r_lo * c + r_hi ^ 2 := by nlinarith
    have hpos_ge : (-(r_hi * c - r_lo ^ 2)) / (1 - 2 * r_lo * c + r_hi ^ 2) ≤
        (-(r * c - r ^ 2)) / (1 - 2 * r * c + r ^ 2) :=
      div_le_div₀ (by linarith) (by linarith) hd_r hden_le
    have hfrac : (r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2) ≤
        (r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2) := by
      rw [neg_div, neg_div] at hpos_ge; linarith
    have hfrac_neg : (r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_lt hnum0) (le_of_lt hd_hi)
    have hstep2 : Real.log (p : ℝ) * ((r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2)) ≤
        Real.log (p : ℝ) * ((r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2)) :=
      mul_le_mul_of_nonneg_left hfrac hlog_nn
    refine le_trans hstep2 ?_
    have hstep3 : lp_lo * (-((r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2))) ≤
        Real.log (p : ℝ) * (-((r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2))) :=
      mul_le_mul_of_nonneg_right hlp_lo (by linarith)
    linarith
  · push Not at hc0
    have hnum_pos : 0 < r_lo * (-c) + r_lo ^ 2 := by nlinarith
    have hden_pos : 0 < 1 + 2 * r_hi * (-c) + r_hi ^ 2 := by nlinarith
    have hnum_ge : r_lo * (-c) + r_lo ^ 2 ≤ r * (-c) + r ^ 2 := by nlinarith
    have hden_le : 1 + 2 * r * (-c) + r ^ 2 ≤ 1 + 2 * r_hi * (-c) + r_hi ^ 2 := by nlinarith
    have hpos_le : (r_lo * (-c) + r_lo ^ 2) / (1 + 2 * r_hi * (-c) + r_hi ^ 2) ≤
        (r * (-c) + r ^ 2) / (1 + 2 * r * (-c) + r ^ 2) :=
      div_le_div₀ (by nlinarith) hnum_ge (by nlinarith) hden_le
    have hneg_eq : (r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2) =
        -((r * (-c) + r ^ 2) / (1 + 2 * r * (-c) + r ^ 2)) := by
      have h1 : r * c - r ^ 2 = -(r * (-c) + r ^ 2) := by ring
      have h2 : 1 - 2 * r * c + r ^ 2 = 1 + 2 * r * (-c) + r ^ 2 := by ring
      rw [h1, h2, neg_div]
    rw [hneg_eq, mul_neg]
    have hmul : lp_lo * ((r_lo * (-c) + r_lo ^ 2) / (1 + 2 * r_hi * (-c) + r_hi ^ 2)) ≤
        Real.log (p : ℝ) * ((r * (-c) + r ^ 2) / (1 + 2 * r * (-c) + r ^ 2)) :=
      mul_le_mul hlp_lo hpos_le (div_nonneg (le_of_lt hnum_pos) (le_of_lt hden_pos)) hlog_nn
    linarith

/-- Helper: Rational lower bound on `Real.log (1 + x)` via 6-term `exp` Taylor upper bound (`0 ≤ lg ≤ 1`). -/
private lemma log_lb_of_tay6 {lg x : ℝ} (hlg0 : 0 ≤ lg) (hlg1 : lg ≤ 1)
    (htay : (∑ k ∈ Finset.range 6, lg ^ k / (k.factorial : ℝ)) +
      lg ^ 6 * (((6 : ℝ) + 1) / (((6 : ℕ).factorial : ℝ) * 6)) ≤ 1 + x) :
    lg ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := lt_of_lt_of_le (Real.exp_pos lg) (le_trans (exp_le_taylor_small hlg0 hlg1 (by norm_num)) htay)
  rw [Real.le_log_iff_exp_le hpos]
  exact le_trans (exp_le_taylor_small hlg0 hlg1 (by norm_num)) htay

/-- Helper: Degree-8 Taylor upper bound on `Real.cos x` (`∀ x, cos x ≤ 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320`),
    directly from Module #17's `cos_sin_sub_taylor_abs_le` (`m = 4`). -/
private lemma cos_le_taylor8 (x : ℝ) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have h := (abs_le.mp ((cos_sin_sub_taylor_abs_le 4).1 x)).2
  dsimp [cosTaylorPoly] at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  have h8 : |x| ^ 8 = x ^ 8 := by rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sq_abs, ← pow_mul]
  norm_num at h; rw [h8] at h; linarith

/-- Helper: Degree-6 Taylor lower bound on `Real.cos x` (`∀ x, 1 - x^2/2 + x^4/24 - x^6/720 ≤ cos x`),
    directly from Module #17's `cos_sin_sub_taylor_abs_le` (`m = 3`). -/
private lemma cos_ge_taylor6 (x : ℝ) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have h := (abs_le.mp ((cos_sin_sub_taylor_abs_le 3).1 x)).1
  dsimp [cosTaylorPoly] at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
  have h6 : |x| ^ 6 = x ^ 6 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]
  norm_num at h; rw [h6] at h; linarith

/-- Helper (Case L): Upper bound on `cos(γ * log p)` for `γ ∈ [g0, g1]` when `γ * log p - 2πk ∈ [a, π] ⊆ [0, π]`. -/
private lemma cos_le_on_Icc_L {p : ℕ} {g0 g1 lp_lo lp_hi a c : ℝ} {k : ℕ}
    (hlp_lo : lp_lo ≤ Real.log (p : ℝ)) (hlp_hi : Real.log (p : ℝ) ≤ lp_hi)
    (hg0 : 0 ≤ g0) (hlp0 : 0 ≤ lp_lo)
    (ha0 : 0 ≤ a) (ha_le : a ≤ g0 * lp_lo - 2 * (k : ℝ) * (31416 / 10000))
    (hb_le : g1 * lp_hi - 2 * (k : ℝ) * (31415 / 10000) ≤ 31415 / 10000)
    (htay : 1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 ≤ c) :
    ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (p : ℝ)) ≤ c := by
  intro γ hγ
  have hpi1 := pi_gt_31415
  have hpi2 := pi_lt_31416
  have hγ_nn : 0 ≤ γ := le_trans hg0 hγ.1
  have hlog_nn : 0 ≤ Real.log (p : ℝ) := le_trans hlp0 hlp_lo
  set θ : ℝ := γ * Real.log (p : ℝ) - 2 * (k : ℝ) * Real.pi
  have hcos_eq : Real.cos (γ * Real.log (p : ℝ)) = Real.cos θ := by
    have h := Real.cos_sub_int_mul_two_pi (γ * Real.log (p : ℝ)) (k : ℤ)
    have harg : γ * Real.log (p : ℝ) - (k : ℤ) * (2 * Real.pi) = θ := by dsimp [θ]; push_cast; ring
    rw [← h, harg]
  rw [hcos_eq]
  have hθ_ge : a ≤ θ := by
    dsimp [θ]
    have hprod : g0 * lp_lo ≤ γ * Real.log (p : ℝ) := mul_le_mul hγ.1 hlp_lo hlp0 hγ_nn
    have h2k : 2 * (k : ℝ) * Real.pi ≤ 2 * (k : ℝ) * (31416 / 10000) :=
      mul_le_mul_of_nonneg_left (le_of_lt hpi2) (by positivity)
    linarith
  have hθ_le : θ ≤ Real.pi := by
    dsimp [θ]
    have hprod : γ * Real.log (p : ℝ) ≤ g1 * lp_hi :=
      mul_le_mul hγ.2 hlp_hi hlog_nn (le_trans hγ_nn hγ.2)
    have h2k : 2 * (k : ℝ) * (31415 / 10000) ≤ 2 * (k : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_left (le_of_lt hpi1) (by positivity)
    linarith
  have hanti : Real.cos θ ≤ Real.cos a :=
    Real.antitoneOn_cos ⟨ha0, le_trans hθ_ge hθ_le⟩ ⟨le_trans ha0 hθ_ge, hθ_le⟩ hθ_ge
  exact le_trans hanti (le_trans (cos_le_taylor8 a) htay)

/-- Helper (Case R): Upper bound on `cos(γ * log p)` for `γ ∈ [g0, g1]` when `γ * log p - 2πk ∈ [-π, b] ⊆ [-π, 0]`. -/
private lemma cos_le_on_Icc_R {p : ℕ} {g0 g1 lp_lo lp_hi b c : ℝ} {k : ℕ}
    (hlp_lo : lp_lo ≤ Real.log (p : ℝ)) (hlp_hi : Real.log (p : ℝ) ≤ lp_hi)
    (hg0 : 0 ≤ g0) (hlp0 : 0 ≤ lp_lo)
    (hb0 : b ≤ 0) (ha_ge : -(31415 / 10000) ≤ g0 * lp_lo - 2 * (k : ℝ) * (31416 / 10000))
    (hb_ge : g1 * lp_hi - 2 * (k : ℝ) * (31415 / 10000) ≤ b)
    (htay : 1 - b ^ 2 / 2 + b ^ 4 / 24 - b ^ 6 / 720 + b ^ 8 / 40320 ≤ c) :
    ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (p : ℝ)) ≤ c := by
  intro γ hγ
  have hpi1 := pi_gt_31415
  have hpi2 := pi_lt_31416
  have hγ_nn : 0 ≤ γ := le_trans hg0 hγ.1
  have hlog_nn : 0 ≤ Real.log (p : ℝ) := le_trans hlp0 hlp_lo
  set θ : ℝ := γ * Real.log (p : ℝ) - 2 * (k : ℝ) * Real.pi
  have hcos_eq : Real.cos (γ * Real.log (p : ℝ)) = Real.cos (-θ) := by
    have h := Real.cos_sub_int_mul_two_pi (γ * Real.log (p : ℝ)) (k : ℤ)
    have harg : γ * Real.log (p : ℝ) - (k : ℤ) * (2 * Real.pi) = θ := by dsimp [θ]; push_cast; ring
    rw [Real.cos_neg, ← h, harg]
  rw [hcos_eq]
  have hθ_ge : -Real.pi ≤ θ := by
    dsimp [θ]
    have hprod : g0 * lp_lo ≤ γ * Real.log (p : ℝ) := mul_le_mul hγ.1 hlp_lo hlp0 hγ_nn
    have h2k : 2 * (k : ℝ) * Real.pi ≤ 2 * (k : ℝ) * (31416 / 10000) :=
      mul_le_mul_of_nonneg_left (le_of_lt hpi2) (by positivity)
    linarith
  have hθ_le : θ ≤ b := by
    dsimp [θ]
    have hprod : γ * Real.log (p : ℝ) ≤ g1 * lp_hi :=
      mul_le_mul hγ.2 hlp_hi hlog_nn (le_trans hγ_nn hγ.2)
    have h2k : 2 * (k : ℝ) * (31415 / 10000) ≤ 2 * (k : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_left (le_of_lt hpi1) (by positivity)
    linarith
  have hmb_ge : 0 ≤ -b := neg_nonneg.mpr hb0
  have hmt_le : -θ ≤ Real.pi := neg_le.mp hθ_ge
  have hmb_le_mt : -b ≤ -θ := neg_le_neg hθ_le
  have hanti : Real.cos (-θ) ≤ Real.cos (-b) :=
    Real.antitoneOn_cos ⟨hmb_ge, le_trans hmb_le_mt hmt_le⟩ ⟨le_trans hmb_ge hmb_le_mt, hmt_le⟩ hmb_le_mt
  rw [Real.cos_neg b] at hanti
  exact le_trans hanti (le_trans (cos_le_taylor8 b) htay)

/-- Helper (Case P): Upper bound on `cos(γ * log p)` for `γ ∈ [g0, g1]` straddling `(2m+1)π`,
    where `|γ * log p - (2m+1)π| ≤ M ≤ π/2`, so `cos(γ * log p) = -cos(δ) ≤ -cos(M)`. -/
private lemma cos_le_on_Icc_P {p : ℕ} {g0 g1 lp_lo lp_hi M c : ℝ} {m : ℕ}
    (hlp_lo : lp_lo ≤ Real.log (p : ℝ)) (hlp_hi : Real.log (p : ℝ) ≤ lp_hi)
    (hg0 : 0 ≤ g0) (hlp0 : 0 ≤ lp_lo)
    (hM0 : 0 ≤ M) (hM_pi : M ≤ 31415 / 20000)
    (ha_ge : -M ≤ g0 * lp_lo - (2 * (m : ℝ) + 1) * (31416 / 10000))
    (hb_le : g1 * lp_hi - (2 * (m : ℝ) + 1) * (31415 / 10000) ≤ M)
    (htay : -(1 - M ^ 2 / 2 + M ^ 4 / 24 - M ^ 6 / 720) ≤ c) :
    ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (p : ℝ)) ≤ c := by
  intro γ hγ
  have hpi1 := pi_gt_31415
  have hpi2 := pi_lt_31416
  have hγ_nn : 0 ≤ γ := le_trans hg0 hγ.1
  have hlog_nn : 0 ≤ Real.log (p : ℝ) := le_trans hlp0 hlp_lo
  set δ : ℝ := γ * Real.log (p : ℝ) - (2 * (m : ℝ) + 1) * Real.pi
  have hcos_eq : Real.cos (γ * Real.log (p : ℝ)) = -Real.cos |δ| := by
    have h1 := Real.cos_sub_int_mul_two_pi (γ * Real.log (p : ℝ)) (m : ℤ)
    have h2 : γ * Real.log (p : ℝ) - (m : ℤ) * (2 * Real.pi) = δ + Real.pi := by
      dsimp [δ]; push_cast; ring
    rw [← h1, h2, Real.cos_add_pi]
    rcases le_or_gt 0 δ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.cos_neg]
  rw [hcos_eq]
  have hδ_abs : |δ| ≤ M := by
    rw [abs_le]
    have hprod_lo : g0 * lp_lo ≤ γ * Real.log (p : ℝ) := mul_le_mul hγ.1 hlp_lo hlp0 hγ_nn
    have hprod_hi : γ * Real.log (p : ℝ) ≤ g1 * lp_hi :=
      mul_le_mul hγ.2 hlp_hi hlog_nn (le_trans hγ_nn hγ.2)
    have hm_nn : 0 ≤ 2 * (m : ℝ) + 1 := by positivity
    have hpi_hi : (2 * (m : ℝ) + 1) * Real.pi ≤ (2 * (m : ℝ) + 1) * (31416 / 10000) :=
      mul_le_mul_of_nonneg_left (le_of_lt hpi2) hm_nn
    have hpi_lo : (2 * (m : ℝ) + 1) * (31415 / 10000) ≤ (2 * (m : ℝ) + 1) * Real.pi :=
      mul_le_mul_of_nonneg_left (le_of_lt hpi1) hm_nn
    dsimp [δ]; constructor <;> linarith
  have hM_lt_pi : M ≤ Real.pi := by linarith
  have hanti : Real.cos M ≤ Real.cos |δ| :=
    Real.antitoneOn_cos ⟨abs_nonneg δ, le_trans hδ_abs hM_lt_pi⟩ ⟨hM0, hM_lt_pi⟩ hδ_abs
  linarith [cos_ge_taylor6 M]

/-- Helper: Conservative rational upper bound function matching `primePhaseFactor_upper`. -/
private noncomputable def phaseBoundVal (lp_lo lp_hi r_lo r_hi c : ℝ) : ℝ :=
  if 0 ≤ c then
    if 0 ≤ r_hi * c - r_lo ^ 2 then
      lp_hi * ((r_hi * c - r_lo ^ 2) / (1 - 2 * r_hi * c + r_lo ^ 2))
    else
      lp_lo * ((r_hi * c - r_lo ^ 2) / (1 - 2 * r_lo * c + r_hi ^ 2))
  else
    -(lp_lo * ((r_lo * (-c) + r_lo ^ 2) / (1 + 2 * r_hi * (-c) + r_hi ^ 2)))

/-- Master 1D segment positivity engine at `β = 5 / 2` (`σ = 2`, fixed vertical left boundary!). -/
private lemma beta_five_halves_seg_pos {g0 g1 lg c2 c3 c5 c7 : ℝ}
    (hg0 : 0 ≤ g0) (_hg01 : g0 ≤ g1)
    (hc2_1 : c2 ≤ 1) (hc3_1 : c3 ≤ 1) (hc5_1 : c5 ≤ 1) (hc7_1 : c7 ≤ 1)
    (hlg : lg ≤ Real.log (1 + (g0 / 2) ^ 2 / (5 / 4 + 4) ^ 2))
    (hcos2 : ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (2 : ℕ)) ≤ c2)
    (hcos3 : ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (3 : ℕ)) ≤ c3)
    (hcos5 : ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (5 : ℕ)) ≤ c5)
    (hcos7 : ∀ γ ∈ Icc g0 g1, Real.cos (γ * Real.log (7 : ℕ)) ≤ c7)
    (hcheck : 0 < (5 / 2 : ℝ) / ((5 / 2) ^ 2 + g1 ^ 2) + (3 / 2 : ℝ) / ((3 / 2) ^ 2 + g1 ^ 2) +
      (1 / 2 : ℝ) * ((-233 / 1000 : ℝ) +
        (g0 / 2) ^ 2 / ((5 / 4 : ℝ) * ((5 / 4) ^ 2 + (g0 / 2) ^ 2)) +
        (g0 / 2) ^ 2 / ((9 / 4 : ℝ) * ((9 / 4) ^ 2 + (g0 / 2) ^ 2)) +
        (g0 / 2) ^ 2 / ((13 / 4 : ℝ) * ((13 / 4) ^ 2 + (g0 / 2) ^ 2)) +
        (g0 / 2) ^ 2 / ((17 / 4 : ℝ) * ((17 / 4) ^ 2 + (g0 / 2) ^ 2)) +
        (1 / 2 : ℝ) * lg) - (1 / 2 : ℝ) * (11448 / 10000) -
      phaseBoundVal (6931 / 10000) (6932 / 10000) (1767 / 10000) (1768 / 10000) c2 -
      phaseBoundVal (10986 / 10000) (10987 / 10000) (641 / 10000) (642 / 10000) c3 -
      phaseBoundVal (16094 / 10000) (16095 / 10000) (178 / 10000) (179 / 10000) c5 -
      phaseBoundVal (19459 / 10000) (19460 / 10000) (77 / 10000) (78 / 10000) c7 -
      (235 / 10000 : ℝ)) :
    ∀ γ ∈ Icc g0 g1, 0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  intro γ hγ
  set z : ℂ := (γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ)
  have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; norm_num
  have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
  dsimp only at hexp
  set s : ℂ := 1 / 2 - Complex.I * z
  have hs_eq : s = (⟨5 / 2, -γ⟩ : ℂ) := by dsimp [s, z]; exact Complex.ext (by simp; norm_num) (by simp)
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
  -- 1. Poles lower bound (using `γ ≤ g1`)
  have hγ_nn : 0 ≤ γ := le_trans hg0 hγ.1
  have hγsq_le : γ ^ 2 ≤ g1 ^ 2 := pow_le_pow_left₀ hγ_nn hγ.2 2
  have hp1 : (5 / 2 : ℝ) / ((5 / 2) ^ 2 + g1 ^ 2) ≤ (1 / s).re := by
    rw [hs_eq, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [neg_mul, mul_neg, neg_neg]
    have heq : (5 / 2 : ℝ) * (5 / 2) + γ * γ = (5 / 2) ^ 2 + γ ^ 2 := by ring
    rw [heq]; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hp2 : (3 / 2 : ℝ) / ((3 / 2) ^ 2 + g1 ^ 2) ≤ (1 / (s - 1)).re := by
    have hs1 : s - 1 = (⟨3 / 2, -γ⟩ : ℂ) := by rw [hs_eq]; exact Complex.ext (by simp; norm_num) (by simp)
    rw [hs1, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [neg_mul, mul_neg, neg_neg]
    have heq : (3 / 2 : ℝ) * (3 / 2) + γ * γ = (3 / 2) ^ 2 + γ ^ 2 := by ring
    rw [heq]; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  -- 2. Digamma lower bound (`K = 4` + log tail, monotone in `γ^2 ≥ g0^2`!)
  have hdig : (-233 / 1000 : ℝ) +
      (g0 / 2) ^ 2 / ((5 / 4 : ℝ) * ((5 / 4) ^ 2 + (g0 / 2) ^ 2)) +
      (g0 / 2) ^ 2 / ((9 / 4 : ℝ) * ((9 / 4) ^ 2 + (g0 / 2) ^ 2)) +
      (g0 / 2) ^ 2 / ((13 / 4 : ℝ) * ((13 / 4) ^ 2 + (g0 / 2) ^ 2)) +
      (g0 / 2) ^ 2 / ((17 / 4 : ℝ) * ((17 / 4) ^ 2 + (g0 / 2) ^ 2)) +
      (1 / 2 : ℝ) * lg ≤ (Complex.digamma (s / 2)).re := by
    have hs2 : s / 2 = (⟨5 / 4, -γ / 2⟩ : ℂ) := by rw [hs_eq]; exact Complex.ext (by simp; norm_num) (by simp)
    rw [hs2]
    have hd0 := complex_digamma_re_ge_real_add_finset_add_log_tail (x := 5 / 4) (by norm_num) (-γ / 2) 4
    have hsq_eq : (-γ / 2) ^ 2 = (γ / 2) ^ 2 := by ring
    have hsq_ge : (g0 / 2) ^ 2 ≤ (γ / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [hγ.1]) 2
    have hterm_mono : ∀ a : ℝ, 0 < a →
        (g0 / 2) ^ 2 / (a * (a ^ 2 + (g0 / 2) ^ 2)) ≤ (γ / 2) ^ 2 / (a * (a ^ 2 + (γ / 2) ^ 2)) := by
      intro a ha
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha (sq_pos_of_pos ha)]
    have hsum4 : ∑ k ∈ Finset.range 4, (-γ / 2) ^ 2 / ((5 / 4 + (k : ℝ)) * ((5 / 4 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) =
        (γ / 2) ^ 2 / ((5 / 4 : ℝ) * ((5 / 4) ^ 2 + (γ / 2) ^ 2)) +
        (γ / 2) ^ 2 / ((9 / 4 : ℝ) * ((9 / 4) ^ 2 + (γ / 2) ^ 2)) +
        (γ / 2) ^ 2 / ((13 / 4 : ℝ) * ((13 / 4) ^ 2 + (γ / 2) ^ 2)) +
        (γ / 2) ^ 2 / ((17 / 4 : ℝ) * ((17 / 4) ^ 2 + (γ / 2) ^ 2)) := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      rw [hsq_eq]; norm_num
    have hlog_ge : lg ≤ Real.log (1 + (-γ / 2) ^ 2 / (5 / 4 + ((4 : ℕ) : ℝ)) ^ 2) := by
      refine le_trans hlg ?_
      rw [hsq_eq]; push_cast
      exact Real.log_le_log (by positivity) (by
        have : (g0 / 2) ^ 2 / (5 / 4 + 4) ^ 2 ≤ (γ / 2) ^ 2 / (5 / 4 + 4) ^ 2 :=
          div_le_div_of_nonneg_right hsq_ge (by positivity)
        linarith)
    rw [hsum4] at hd0
    linarith [digamma_five_fourths_ge, hterm_mono (5 / 4) (by norm_num), hterm_mono (9 / 4) (by norm_num),
      hterm_mono (13 / 4) (by norm_num), hterm_mono (17 / 4) (by norm_num)]
  -- 3. Clifford-torus prime-phase Euler splitting (`p = 2, 3, 5, 7` + residual `≤ 235/10000`)!
  rcases cliffordTorus_primePhase_euler_split_2357 (by norm_num : (1 : ℝ) < 5 / 2) γ with ⟨rem, hre_eq, hrem_le⟩
  have hrem_ub : rem ≤ 235 / 10000 :=
    le_trans (le_abs_self rem) (le_trans hrem_le residual_vonMangoldt_five_halves_le.2)
  have hp2_ub : primePhaseFactor 2 (5 / 2) γ ≤ phaseBoundVal (6931 / 10000) (6932 / 10000) (1767 / 10000) (1768 / 10000) c2 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_2.1) (by push_cast; exact rpow_neg_five_halves_2.2)
      (by norm_num) (by norm_num) hc2_1 (hcos2 γ hγ)
  have hp3_ub : primePhaseFactor 3 (5 / 2) γ ≤ phaseBoundVal (10986 / 10000) (10987 / 10000) (641 / 10000) (642 / 10000) c3 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_3.1) (by push_cast; exact rpow_neg_five_halves_3.2)
      (by norm_num) (by norm_num) hc3_1 (hcos3 γ hγ)
  have hp5_ub : primePhaseFactor 5 (5 / 2) γ ≤ phaseBoundVal (16094 / 10000) (16095 / 10000) (178 / 10000) (179 / 10000) c5 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_5.1) (by push_cast; exact rpow_neg_five_halves_5.2)
      (by norm_num) (by norm_num) hc5_1 (hcos5 γ hγ)
  have hp7_ub : primePhaseFactor 7 (5 / 2) γ ≤ phaseBoundVal (19459 / 10000) (19460 / 10000) (77 / 10000) (78 / 10000) c7 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_7.1) (by push_cast; exact rpow_neg_five_halves_7.2)
      (by norm_num) (by norm_num) hc7_1 (hcos7 γ hγ)
  rw [← hs_eq] at hre_eq
  rw [him_eq, hre_eq]
  linarith [log_pi_le_11448]



private lemma xiResolvent_im_pos_beta52_chunk1 {γ : ℝ} (hγ0 : (0 : ℝ) ≤ γ) (hγ1 : γ ≤ (3 / 2 : ℝ)) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  by_cases h1 : γ ≤ (1 / 2 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (0 : ℝ)) (g1 := (1 / 2 : ℝ)) (lg := (0 : ℝ))
      (c2 := (1 : ℝ)) (c3 := (1 : ℝ)) (c5 := (1 : ℝ)) (c7 := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (fun _ _ => Real.cos_le_one _)
      (fun _ _ => Real.cos_le_one _)
      (fun _ _ => Real.cos_le_one _)
      (fun _ _ => Real.cos_le_one _)
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h1⟩
  push Not at h1
  by_cases h2 : γ ≤ (5 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (1 / 2 : ℝ)) (g1 := (5 / 8 : ℝ)) (lg := (1 / 500 : ℝ))
      (c2 := (941 / 1000 : ℝ)) (c3 := (853 / 1000 : ℝ)) (c5 := (347 / 500 : ℝ)) (c7 := (563 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (6931 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (5493 / 10000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (8047 / 10000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (19459 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h2⟩
  push Not at h2
  by_cases h3 : γ ≤ (3 / 4 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (5 / 8 : ℝ)) (g1 := (3 / 4 : ℝ)) (lg := (3 / 1000 : ℝ))
      (c2 := (227 / 250 : ℝ)) (c3 := (387 / 500 : ℝ)) (c5 := (67 / 125 : ℝ)) (c7 := (87 / 250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (6931 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (5493 / 8000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (8047 / 8000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (19459 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h3⟩
  push Not at h3
  by_cases h4 : γ ≤ (7 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (3 / 4 : ℝ)) (g1 := (7 / 8 : ℝ)) (lg := (1 / 200 : ℝ))
      (c2 := (217 / 250 : ℝ)) (c3 := (17 / 25 : ℝ)) (c5 := (89 / 250 : ℝ)) (c7 := (14 / 125 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (20793 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (16479 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (24141 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (58377 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h4⟩
  push Not at h4
  by_cases h5 : γ ≤ (1 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (7 / 8 : ℝ)) (g1 := (1 : ℝ)) (lg := (3 / 500 : ℝ))
      (c2 := (411 / 500 : ℝ)) (c3 := (573 / 1000 : ℝ)) (c5 := (81 / 500 : ℝ)) (c7 := (-131 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (48517 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (38451 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (56329 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (136213 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h5⟩
  push Not at h5
  by_cases h6 : γ ≤ (9 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (1 : ℝ)) (g1 := (9 / 8 : ℝ)) (lg := (9 / 1000 : ℝ))
      (c2 := (77 / 100 : ℝ)) (c3 := (91 / 200 : ℝ)) (c5 := (-19 / 500 : ℝ)) (c7 := (-183 / 500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (6931 / 10000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (5493 / 5000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (8047 / 5000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (19459 / 10000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h6⟩
  push Not at h6
  by_cases h7 : γ ≤ (5 / 4 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (9 / 8 : ℝ)) (g1 := (5 / 4 : ℝ)) (lg := (11 / 1000 : ℝ))
      (c2 := (89 / 125 : ℝ)) (c3 := (329 / 1000 : ℝ)) (c5 := (-237 / 1000 : ℝ)) (c7 := (-579 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (62379 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (49437 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (72423 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (175131 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h7⟩
  push Not at h7
  by_cases h8 : γ ≤ (11 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (5 / 4 : ℝ)) (g1 := (11 / 8 : ℝ)) (lg := (7 / 500 : ℝ))
      (c2 := (81 / 125 : ℝ)) (c3 := (197 / 1000 : ℝ)) (c5 := (-213 / 500 : ℝ)) (c7 := (-189 / 250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (6931 / 8000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (5493 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (8047 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (19459 / 8000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h8⟩
  push Not at h8
  exact beta_five_halves_seg_pos (g0 := (11 / 8 : ℝ)) (g1 := (3 / 2 : ℝ)) (lg := (17 / 1000 : ℝ))
      (c2 := (29 / 50 : ℝ)) (c3 := (61 / 1000 : ℝ)) (c5 := (-299 / 500 : ℝ)) (c7 := (-111 / 125 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (76241 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (60423 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (88517 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 0) (a := (214049 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, hγ1⟩

private lemma xiResolvent_im_pos_beta52_chunk2 {γ : ℝ} (hγ0 : (3 / 2 : ℝ) ≤ γ) (hγ1 : γ ≤ (27 / 8 : ℝ)) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  by_cases h1 : γ ≤ (13 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (3 / 2 : ℝ)) (g1 := (13 / 8 : ℝ)) (lg := (1 / 50 : ℝ))
      (c2 := (507 / 1000 : ℝ)) (c3 := (-19 / 250 : ℝ)) (c5 := (-149 / 200 : ℝ)) (c7 := (-39 / 40 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (20793 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (16479 / 10000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (24141 / 10000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (m := 0) (M := (891 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h1⟩
  push Not at h1
  by_cases h2 : γ ≤ (7 / 4 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (13 / 8 : ℝ)) (g1 := (7 / 4 : ℝ)) (lg := (23 / 1000 : ℝ))
      (c2 := (431 / 1000 : ℝ)) (c3 := (-53 / 250 : ℝ)) (c5 := (-43 / 50 : ℝ)) (c7 := (-191 / 200 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (90103 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (71409 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (104611 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-1151 / 400 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h2⟩
  push Not at h2
  by_cases h3 : γ ≤ (15 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (7 / 4 : ℝ)) (g1 := (15 / 8 : ℝ)) (lg := (27 / 1000 : ℝ))
      (c2 := (351 / 1000 : ℝ)) (c3 := (-43 / 125 : ℝ)) (c5 := (-939 / 1000 : ℝ)) (c7 := (-869 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (48517 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (38451 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 0) (a := (56329 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-10537 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h3⟩
  push Not at h3
  by_cases h4 : γ ≤ (17 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (15 / 8 : ℝ)) (g1 := (17 / 8 : ℝ)) (lg := (31 / 1000 : ℝ))
      (c2 := (67 / 250 : ℝ)) (c3 := (-469 / 1000 : ℝ)) (c5 := (-961 / 1000 : ℝ)) (c7 := (-68 / 125 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (20793 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (16479 / 8000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (m := 0) (M := (4459 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-8591 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h4⟩
  push Not at h4
  by_cases h5 : γ ≤ (19 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (17 / 8 : ℝ)) (g1 := (19 / 8 : ℝ)) (lg := (1 / 25 : ℝ))
      (c2 := (49 / 500 : ℝ)) (c3 := (-69 / 100 : ℝ)) (c5 := (-387 / 500 : ℝ)) (c7 := (-9 / 100 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (117827 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (93381 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-39367 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-1329 / 800 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h5⟩
  push Not at h5
  by_cases h6 : γ ≤ (21 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (19 / 8 : ℝ)) (g1 := (21 / 8 : ℝ)) (lg := (49 / 1000 : ℝ))
      (c2 := (-3 / 40 : ℝ)) (c3 := (-857 / 1000 : ℝ)) (c5 := (-467 / 1000 : ℝ)) (c7 := (193 / 500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (131689 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 0) (a := (104367 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-32929 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-4699 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h6⟩
  push Not at h6
  by_cases h7 : γ ≤ (23 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (21 / 8 : ℝ)) (g1 := (23 / 8 : ℝ)) (lg := (3 / 50 : ℝ))
      (c2 := (-49 / 200 : ℝ)) (c3 := (-483 / 500 : ℝ)) (c5 := (-21 / 250 : ℝ)) (c7 := (773 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (145551 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (m := 0) (M := (10311 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-26491 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-2753 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h7⟩
  push Not at h7
  by_cases h8 : γ ≤ (25 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (23 / 8 : ℝ)) (g1 := (25 / 8 : ℝ)) (lg := (9 / 125 : ℝ))
      (c2 := (-409 / 1000 : ℝ)) (c3 := (-237 / 250 : ℝ)) (c5 := (313 / 1000 : ℝ)) (c7 := (49 / 50 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (159413 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-45593 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-20053 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (b := (-807 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h8⟩
  push Not at h8
  exact beta_five_halves_seg_pos (g0 := (25 / 8 : ℝ)) (g1 := (27 / 8 : ℝ)) (lg := (21 / 250 : ℝ))
      (c2 := (-14 / 25 : ℝ)) (c3 := (-21 / 25 : ℝ)) (c5 := (33 / 50 : ℝ)) (c7 := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (6931 / 3200 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-205991 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-2723 / 3200 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, hγ1⟩

private lemma xiResolvent_im_pos_beta52_chunk3 {γ : ℝ} (hγ0 : (27 / 8 : ℝ) ≤ γ) (hγ1 : γ ≤ (49 / 8 : ℝ)) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  by_cases h1 : γ ≤ (29 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (27 / 8 : ℝ)) (g1 := (29 / 8 : ℝ)) (lg := (49 / 500 : ℝ))
      (c2 := (-693 / 1000 : ℝ)) (c3 := (-133 / 200 : ℝ)) (c5 := (451 / 500 : ℝ)) (c7 := (24 / 25 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (187137 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-184017 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-7177 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (a := (22737 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h1⟩
  push Not at h1
  by_cases h2 : γ ≤ (31 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (29 / 8 : ℝ)) (g1 := (31 / 8 : ℝ)) (lg := (14 / 125 : ℝ))
      (c2 := (-161 / 200 : ℝ)) (c3 := (-219 / 500 : ℝ)) (c5 := (999 / 1000 : ℝ)) (c7 := (359 / 500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (200999 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-162043 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (b := (-739 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (a := (12331 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h2⟩
  push Not at h2
  by_cases h3 : γ ≤ (33 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (31 / 8 : ℝ)) (g1 := (33 / 8 : ℝ)) (lg := (127 / 1000 : ℝ))
      (c2 := (-223 / 250 : ℝ)) (c3 := (-179 / 1000 : ℝ)) (c5 := (1 : ℝ)) (c7 := (309 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (214861 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-140069 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (a := (100573 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h3⟩
  push Not at h3
  by_cases h4 : γ ≤ (35 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (33 / 8 : ℝ)) (g1 := (35 / 8 : ℝ)) (lg := (143 / 1000 : ℝ))
      (c2 := (-19 / 20 : ℝ)) (c3 := (19 / 200 : ℝ)) (c5 := (469 / 500 : ℝ)) (c7 := (-171 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 0) (a := (228723 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-23619 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (a := (14223 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (a := (139491 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h4⟩
  push Not at h4
  by_cases h5 : γ ≤ (37 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (35 / 8 : ℝ)) (g1 := (37 / 8 : ℝ)) (lg := (4 / 25 : ℝ))
      (c2 := (-497 / 500 : ℝ)) (c3 := (361 / 1000 : ℝ)) (c5 := (727 / 1000 : ℝ)) (c7 := (-611 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_P (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (m := 0) (M := (8743 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-96121 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (a := (30317 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 1) (a := (178409 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h5⟩
  push Not at h5
  by_cases h6 : γ ≤ (41 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (37 / 8 : ℝ)) (g1 := (41 / 8 : ℝ)) (lg := (177 / 1000 : ℝ))
      (c2 := (-91 / 100 : ℝ)) (c3 := (159 / 200 : ℝ)) (c5 := (2 / 5 : ℝ)) (c7 := (-853 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-54607 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-52173 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (a := (46411 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (m := 1) (M := (439 / 800 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h6⟩
  push Not at h6
  by_cases h7 : γ ≤ (45 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (41 / 8 : ℝ)) (g1 := (45 / 8 : ℝ)) (lg := (213 / 1000 : ℝ))
      (c2 := (-181 / 250 : ℝ)) (c3 := (199 / 200 : ℝ)) (c5 := (-383 / 1000 : ℝ)) (c7 := (-6 / 125 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-1907 / 800 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (b := (-329 / 3200 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 1) (a := (78599 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 2) (b := (-6479 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h7⟩
  push Not at h7
  exact beta_five_halves_seg_pos (g0 := (45 / 8 : ℝ)) (g1 := (49 / 8 : ℝ)) (lg := (63 / 250 : ℝ))
      (c2 := (-449 / 1000 : ℝ)) (c3 := (1 : ℝ)) (c5 := (-907 / 1000 : ℝ)) (c7 := (799 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-40743 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (cos_le_on_Icc_P (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (m := 1) (M := (6939 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 2) (b := (-2587 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, hγ1⟩

private lemma xiResolvent_im_pos_beta52_chunk4 {γ : ℝ} (hγ0 : (49 / 8 : ℝ) ≤ γ) (hγ1 : γ ≤ (25 / 2 : ℝ)) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  by_cases h1 : γ ≤ (53 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (49 / 8 : ℝ)) (g1 := (53 / 8 : ℝ)) (lg := (73 / 250 : ℝ))
      (c2 := (-119 / 1000 : ℝ)) (c3 := (903 / 1000 : ℝ)) (c5 := (-163 / 500 : ℝ)) (c7 := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-33811 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (a := (17829 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 2) (b := (-30449 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h1⟩
  push Not at h1
  by_cases h2 : γ ≤ (55 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (53 / 8 : ℝ)) (g1 := (55 / 8 : ℝ)) (lg := (67 / 200 : ℝ))
      (c2 := (27 / 500 : ℝ)) (c3 := (109 / 200 : ℝ)) (c5 := (71 / 1000 : ℝ)) (c7 := (237 / 250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-6069 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (a := (39801 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 2) (b := (-24011 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 2) (a := (5203 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h2⟩
  push Not at h2
  by_cases h3 : γ ≤ (59 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (55 / 8 : ℝ)) (g1 := (59 / 8 : ℝ)) (lg := (89 / 250 : ℝ))
      (c2 := (39 / 100 : ℝ)) (c3 := (297 / 1000 : ℝ)) (c5 := (96 / 125 : ℝ)) (c7 := (689 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-23413 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (a := (50787 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 2) (b := (-2227 / 3200 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 2) (a := (64933 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h3⟩
  push Not at h3
  by_cases h4 : γ ≤ (63 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (59 / 8 : ℝ)) (g1 := (63 / 8 : ℝ)) (lg := (401 / 1000 : ℝ))
      (c2 := (17 / 25 : ℝ)) (c3 := (-49 / 200 : ℝ)) (c5 := (1 : ℝ)) (c7 := (-53 / 250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-16481 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 1) (a := (72759 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (cos_le_on_Icc_L (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 2) (a := (142769 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h4⟩
  push Not at h4
  by_cases h5 : γ ≤ (69 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (63 / 8 : ℝ)) (g1 := (69 / 8 : ℝ)) (lg := (223 / 500 : ℝ))
      (c2 := (191 / 200 : ℝ)) (c3 := (-143 / 200 : ℝ)) (c5 := (199 / 200 : ℝ)) (c7 := (-237 / 500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_R (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (b := (-6083 / 20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (m := 1) (M := (30933 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 2) (a := (861 / 8000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (m := 2) (M := (4307 / 4000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h5⟩
  push Not at h5
  by_cases h6 : γ ≤ (77 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (69 / 8 : ℝ)) (g1 := (77 / 8 : ℝ)) (lg := (103 / 200 : ℝ))
      (c2 := (1 : ℝ)) (c3 := (-407 / 1000 : ℝ)) (c5 := (127 / 500 : ℝ)) (c7 := (993 / 1000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (fun _ _ => Real.cos_le_one _)
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 2) (b := (-159281 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_L (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (k := 2) (a := (52587 / 40000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460) (k := 3) (b := (-19 / 160 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h6⟩
  push Not at h6
  by_cases h7 : γ ≤ (85 / 8 : ℝ)
  · exact beta_five_halves_seg_pos (g0 := (77 / 8 : ℝ)) (g1 := (85 / 8 : ℝ)) (lg := (609 / 1000 : ℝ))
      (c2 := (463 / 500 : ℝ)) (c3 := (157 / 250 : ℝ)) (c5 := (-22 / 125 : ℝ)) (c7 := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (a := (31031 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_R (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987) (k := 2) (b := (-14277 / 16000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (cos_le_on_Icc_P (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095) (m := 2) (M := (4459 / 3200 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, h7⟩
  push Not at h7
  exact beta_five_halves_seg_pos (g0 := (85 / 8 : ℝ)) (g1 := (25 / 2 : ℝ)) (lg := (141 / 200 : ℝ))
      (c2 := (471 / 1000 : ℝ)) (c3 := (1 : ℝ)) (c5 := (1 : ℝ)) (c7 := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_lb_of_tay6 (by norm_num) (by norm_num) (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num))
      (cos_le_on_Icc_L (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932) (k := 1) (a := (86479 / 80000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (fun _ _ => Real.cos_le_one _)
      (fun _ _ => Real.cos_le_one _)
      (fun _ _ => Real.cos_le_one _)
      (by unfold phaseBoundVal; norm_num) γ ⟨by linarith, hγ1⟩

private lemma xiResolvent_im_pos_beta_five_halves_on_zero_to_25_div_2 {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 25 / 2) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  by_cases hc1 : γ ≤ (3 / 2 : ℝ)
  · exact xiResolvent_im_pos_beta52_chunk1 (by linarith) hc1
  push Not at hc1
  by_cases hc2 : γ ≤ (27 / 8 : ℝ)
  · exact xiResolvent_im_pos_beta52_chunk2 (by linarith) hc2
  push Not at hc2
  by_cases hc3 : γ ≤ (49 / 8 : ℝ)
  · exact xiResolvent_im_pos_beta52_chunk3 (by linarith) hc3
  push Not at hc3
  exact xiResolvent_im_pos_beta52_chunk4 (by linarith) hγ1

private lemma xiResolvent_im_neg_gamma {σ : ℝ} (hσ : 1 / 2 < σ) (γ : ℝ) :
    (xiResolvent (((-γ : ℝ) : ℂ) + Complex.I * (σ : ℂ))).im =
    (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  have hxi1 : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 :=
    riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hxi2 : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * ((-γ : ℝ) : ℂ)) ≠ 0 :=
    riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hV1 : 0 < xiNormSq σ γ := by
    dsimp [xiNormSq]
    have harg : (⟨1 / 2 + σ, γ⟩ : ℂ) = ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
      apply Complex.ext <;> simp
    rw [harg]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxi1)
  have hV2 : 0 < xiNormSq σ (-γ) := by rw [xiNormSq_even_gamma]; exact hV1
  have h1 := (xiResolvent_im_eq_logForce_half hxi1).2
  have h2 := (xiResolvent_im_eq_logForce_half hxi2).2
  rw [xiLogForce_eq_force_div_normSq hV1] at h1
  rw [xiLogForce_eq_force_div_normSq hV2] at h2
  have hfn : (fun s : ℝ => xiNormSq s (-γ)) = fun s : ℝ => xiNormSq s γ := by
    ext s; exact xiNormSq_even_gamma s γ
  rw [hfn, xiNormSq_even_gamma] at h2
  exact h2.trans h1.symm

/-- Helper: Uniform upper bound `(LSeries Λ ⟨β, -γ⟩).re ≤ 2925 / 10000` for ALL `β ≥ 5 / 2` and ALL `γ : ℝ`,
    via termwise monotonicity `Λ(n) / n^β ≤ Λ(n) / n^{5/2}` and Clifford-torus `{2,3,5,7} + 6k ± 1` splitting! -/
private lemma LSeries_vonMangoldt_re_le_of_five_halves_le {β : ℝ} (hβ : 5 / 2 ≤ β) (γ : ℝ) :
    (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)).re ≤ 2925 / 10000 := by
  have hs1 : Summable (fun n : ℕ => LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨β, -γ⟩ : ℂ) n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
  have hs0 : Summable (fun n : ℕ => LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (⟨5 / 2, 0⟩ : ℂ) n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; norm_num)
  have hre_le : (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)).re ≤
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨5 / 2, 0⟩ : ℂ)).re := by
    dsimp [LSeries]
    rw [Complex.re_tsum hs1, Complex.re_tsum hs0]
    refine Summable.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hs1) (Complex.reCLM.summable hs0)
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
      have hterm0 : (((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (⟨5 / 2, 0⟩ : ℂ))).re) =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 2 : ℝ) := by
        have hcp : (n : ℂ) ^ (⟨5 / 2, 0⟩ : ℂ) = (((n : ℝ) ^ (5 / 2 : ℝ) : ℝ) : ℂ) := by
          have h52 : (⟨5 / 2, 0⟩ : ℂ) = ((5 / 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp
          rw [h52, ← Complex.ofReal_natCast, Complex.ofReal_cpow (le_of_lt hn_pos)]
        rw [hcp, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [hterm0]
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only
      exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_pos_of_pos hn_pos _) (Real.rpow_le_rpow_of_exponent_le hn1 hβ)
  -- Now bound `(LSeries Λ ⟨5/2, 0⟩).re` via `cliffordTorus_primePhase_euler_split_2357` at `γ = 0`!
  rcases cliffordTorus_primePhase_euler_split_2357 (by norm_num : (1 : ℝ) < 5 / 2) 0 with ⟨rem, hre_eq, hrem_le⟩
  have hneg0 : (⟨5 / 2, -(0 : ℝ)⟩ : ℂ) = (⟨5 / 2, 0⟩ : ℂ) := by apply Complex.ext <;> simp
  rw [hneg0] at hre_eq
  have hrem_ub : rem ≤ 235 / 10000 :=
    le_trans (le_abs_self rem) (le_trans hrem_le residual_vonMangoldt_five_halves_le.2)
  have hp2 : primePhaseFactor 2 (5 / 2) 0 ≤ phaseBoundVal (6931 / 10000) (6932 / 10000) (1767 / 10000) (1768 / 10000) 1 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 2) (by push_cast; exact log_two_ge_6931) (by push_cast; exact log_two_le_6932)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_2.1) (by push_cast; exact rpow_neg_five_halves_2.2)
      (by norm_num) (by norm_num) (le_refl 1) (Real.cos_le_one _)
  have hp3 : primePhaseFactor 3 (5 / 2) 0 ≤ phaseBoundVal (10986 / 10000) (10987 / 10000) (641 / 10000) (642 / 10000) 1 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 3) (by push_cast; exact log_three_ge_10986) (by push_cast; exact log_three_le_10987)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_3.1) (by push_cast; exact rpow_neg_five_halves_3.2)
      (by norm_num) (by norm_num) (le_refl 1) (Real.cos_le_one _)
  have hp5 : primePhaseFactor 5 (5 / 2) 0 ≤ phaseBoundVal (16094 / 10000) (16095 / 10000) (178 / 10000) (179 / 10000) 1 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 5) (by push_cast; exact log_five_ge_16094) (by push_cast; exact log_five_le_16095)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_5.1) (by push_cast; exact rpow_neg_five_halves_5.2)
      (by norm_num) (by norm_num) (le_refl 1) (Real.cos_le_one _)
  have hp7 : primePhaseFactor 7 (5 / 2) 0 ≤ phaseBoundVal (19459 / 10000) (19460 / 10000) (77 / 10000) (78 / 10000) 1 := by
    dsimp [phaseBoundVal]
    exact primePhaseFactor_upper (p := 7) (by push_cast; exact log_seven_ge_19459) (by push_cast; exact log_seven_le_19460)
      (by norm_num) (by push_cast; exact rpow_neg_five_halves_7.1) (by push_cast; exact rpow_neg_five_halves_7.2)
      (by norm_num) (by norm_num) (le_refl 1) (Real.cos_le_one _)
  have hnum : phaseBoundVal (6931 / 10000) (6932 / 10000) (1767 / 10000) (1768 / 10000) 1 +
      phaseBoundVal (10986 / 10000) (10987 / 10000) (641 / 10000) (642 / 10000) 1 +
      phaseBoundVal (16094 / 10000) (16095 / 10000) (178 / 10000) (179 / 10000) 1 +
      phaseBoundVal (19459 / 10000) (19460 / 10000) (77 / 10000) (78 / 10000) 1 +
      (235 / 10000 : ℝ) ≤ 2925 / 10000 := by
    unfold phaseBoundVal; norm_num
  linarith

/-- Helper: Unconditional Herglotz positivity on the vertical line `σ = 2` (`β = 5/2`)
    for ALL `γ ≥ 25 / 2` (margin `+0.0215 > 0`). -/
private lemma xiResolvent_im_pos_beta_five_halves_large_gamma {γ : ℝ} (hγ : 25 / 2 ≤ γ) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  set z : ℂ := (γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ)
  have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; norm_num
  have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
  dsimp only at hexp
  set s : ℂ := 1 / 2 - Complex.I * z
  have hs_eq : s = (⟨5 / 2, -γ⟩ : ℂ) := by dsimp [s, z]; exact Complex.ext (by simp; norm_num) (by simp)
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
  have hp1 : 0 ≤ (1 / s).re := by
    rw [hs_eq, one_div, Complex.inv_re]; exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hp2 : 0 ≤ (1 / (s - 1)).re := by
    have hs1 : s - 1 = (⟨3 / 2, -γ⟩ : ℂ) := by rw [hs_eq]; exact Complex.ext (by simp; norm_num) (by simp)
    rw [hs1, one_div, Complex.inv_re]; exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hdig : (-233 / 1000 : ℝ) +
      (25 / 4 : ℝ) ^ 2 / ((5 / 4 : ℝ) * ((5 / 4) ^ 2 + (25 / 4) ^ 2)) +
      (25 / 4 : ℝ) ^ 2 / ((9 / 4 : ℝ) * ((9 / 4) ^ 2 + (25 / 4) ^ 2)) +
      (25 / 4 : ℝ) ^ 2 / ((13 / 4 : ℝ) * ((13 / 4) ^ 2 + (25 / 4) ^ 2)) +
      (25 / 4 : ℝ) ^ 2 / ((17 / 4 : ℝ) * ((17 / 4) ^ 2 + (25 / 4) ^ 2)) +
      (1 / 2 : ℝ) * (88 / 100) ≤ (Complex.digamma (s / 2)).re := by
    have hs2 : s / 2 = (⟨5 / 4, -γ / 2⟩ : ℂ) := by rw [hs_eq]; exact Complex.ext (by simp; norm_num) (by simp)
    rw [hs2]
    have hd0 := complex_digamma_re_ge_real_add_finset_add_log_tail (x := 5 / 4) (by norm_num) (-γ / 2) 4
    have hsq_eq : (-γ / 2) ^ 2 = (γ / 2) ^ 2 := by ring
    have hsq_ge : (25 / 4 : ℝ) ^ 2 ≤ (γ / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hterm_mono : ∀ a : ℝ, 0 < a →
        (25 / 4 : ℝ) ^ 2 / (a * (a ^ 2 + (25 / 4) ^ 2)) ≤ (γ / 2) ^ 2 / (a * (a ^ 2 + (γ / 2) ^ 2)) := by
      intro a ha; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [mul_pos ha (sq_pos_of_pos ha)]
    have hsum4 : ∑ k ∈ Finset.range 4, (-γ / 2) ^ 2 / ((5 / 4 + (k : ℝ)) * ((5 / 4 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) =
        (γ / 2) ^ 2 / ((5 / 4 : ℝ) * ((5 / 4) ^ 2 + (γ / 2) ^ 2)) +
        (γ / 2) ^ 2 / ((9 / 4 : ℝ) * ((9 / 4) ^ 2 + (γ / 2) ^ 2)) +
        (γ / 2) ^ 2 / ((13 / 4 : ℝ) * ((13 / 4) ^ 2 + (γ / 2) ^ 2)) +
        (γ / 2) ^ 2 / ((17 / 4 : ℝ) * ((17 / 4) ^ 2 + (γ / 2) ^ 2)) := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      rw [hsq_eq]; norm_num
    have hlog88 : (88 / 100 : ℝ) ≤ Real.log (1 + (-γ / 2) ^ 2 / (5 / 4 + ((4 : ℕ) : ℝ)) ^ 2) := by
      have h1 : (88 / 100 : ℝ) ≤ Real.log (1 + (25 / 4 : ℝ) ^ 2 / (21 / 4 : ℝ) ^ 2) :=
        log_lb_of_tay6 (by norm_num) (by norm_num)
          (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num)
      refine le_trans h1 ?_
      rw [hsq_eq]; push_cast
      refine Real.log_le_log (by positivity) ?_
      have h21 : (5 / 4 + (4 : ℝ)) ^ 2 = (21 / 4 : ℝ) ^ 2 := by norm_num
      rw [h21]
      have : (25 / 4 : ℝ) ^ 2 / (21 / 4 : ℝ) ^ 2 ≤ (γ / 2) ^ 2 / (21 / 4 : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsq_ge (by positivity)
      linarith
    rw [hsum4] at hd0
    linarith [digamma_five_fourths_ge, hterm_mono (5 / 4) (by norm_num), hterm_mono (9 / 4) (by norm_num),
      hterm_mono (13 / 4) (by norm_num), hterm_mono (17 / 4) (by norm_num)]
  have hL_ub := LSeries_vonMangoldt_re_le_of_five_halves_le (le_refl (5 / 2)) γ
  rw [← hs_eq] at hL_ub
  rw [him_eq]
  have hnum : (0 : ℝ) < -(1 / 2 : ℝ) * (11448 / 10000) +
      (1 / 2 : ℝ) * ((-233 / 1000 : ℝ) +
        (25 / 4 : ℝ) ^ 2 / ((5 / 4 : ℝ) * ((5 / 4) ^ 2 + (25 / 4) ^ 2)) +
        (25 / 4 : ℝ) ^ 2 / ((9 / 4 : ℝ) * ((9 / 4) ^ 2 + (25 / 4) ^ 2)) +
        (25 / 4 : ℝ) ^ 2 / ((13 / 4 : ℝ) * ((13 / 4) ^ 2 + (25 / 4) ^ 2)) +
        (25 / 4 : ℝ) ^ 2 / ((17 / 4 : ℝ) * ((17 / 4) ^ 2 + (25 / 4) ^ 2)) +
        (1 / 2 : ℝ) * (88 / 100)) - (2925 / 10000 : ℝ) := by norm_num
  linarith [log_pi_le_11448]

/-- Helper: Unconditional Herglotz positivity on the ENTIRE vertical line `σ = 2` (`β = 5/2`)
    for EVERY `γ : ℝ`! -/
private lemma xiResolvent_im_pos_beta_five_halves_all (γ : ℝ) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
  have hnonneg : ∀ t : ℝ, 0 ≤ t → 0 < (xiResolvent ((t : ℂ) + Complex.I * ((2 : ℝ) : ℂ))).im := by
    intro t ht
    by_cases hcut : t ≤ 25 / 2
    · exact xiResolvent_im_pos_beta_five_halves_on_zero_to_25_div_2 ht hcut
    · push Not at hcut
      exact xiResolvent_im_pos_beta_five_halves_large_gamma (le_of_lt hcut)
  rcases le_total 0 γ with hγ | hγ
  · exact hnonneg γ hγ
  · rw [← xiResolvent_im_neg_gamma (by norm_num : (1 / 2 : ℝ) < 2) γ]
    exact hnonneg (-γ) (by linarith)

/-- Helper: Uniform Herglotz positivity throughout the large-`|γ|` strip `σ ∈ [2, 7/2], |γ| ≥ 24`,
    using exact `1 + 12^2 / (2 + 4)^2 = 5` (`log 5 ≥ 16094 / 10000`, margin `+0.0188 > 0`). -/
private lemma xiResolvent_im_pos_strip_large_gamma_24 {σ γ : ℝ}
    (hσ0 : 2 ≤ σ) (hσ1 : σ ≤ 7 / 2) (hγ : 24 ≤ |γ|) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; linarith
  have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
  dsimp only at hexp
  set β : ℝ := 1 / 2 + σ
  have hβ0 : 5 / 2 ≤ β := by dsimp [β]; linarith
  have hβ1 : β ≤ 4 := by dsimp [β]; linarith
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
  have hp1 : 0 ≤ (1 / s).re := by
    rw [hs_eq, one_div, Complex.inv_re]; exact div_nonneg (by linarith) (Complex.normSq_nonneg _)
  have hp2 : 0 ≤ (1 / (s - 1)).re := by
    have hs1 : s - 1 = (⟨β - 1, -γ⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs1, one_div, Complex.inv_re]; exact div_nonneg (by linarith) (Complex.normSq_nonneg _)
  -- Digamma bound for `x = β / 2 ∈ [5 / 4, 2]` and `|y| = |γ| / 2 ≥ 12`!
  set x : ℝ := β / 2
  have hx0 : 5 / 4 ≤ x := by dsimp [x]; linarith
  have hx1 : x ≤ 2 := by dsimp [x]; linarith
  have hψ_real : (-233 / 1000 : ℝ) ≤ (Complex.digamma ((x : ℝ) : ℂ)).re := by
    have hmono := complex_digamma_real_diff_ge_finset (a := 5 / 4) (b := x) (by norm_num) hx0 0
    simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hmono
    exact le_trans digamma_five_fourths_ge hmono
  have hdig : (-233 / 1000 : ℝ) +
      (144 : ℝ) / ((2 : ℝ) * (2 ^ 2 + 144)) +
      (144 : ℝ) / ((3 : ℝ) * (3 ^ 2 + 144)) +
      (144 : ℝ) / ((4 : ℝ) * (4 ^ 2 + 144)) +
      (144 : ℝ) / ((5 : ℝ) * (5 ^ 2 + 144)) +
      (1 / 2 : ℝ) * (16094 / 10000) ≤ (Complex.digamma (s / 2)).re := by
    have hs2 : s / 2 = (⟨x, -γ / 2⟩ : ℂ) := by rw [hs_eq]; dsimp [x]; apply Complex.ext <;> simp
    rw [hs2]
    have hd0 := complex_digamma_re_ge_real_add_finset_add_log_tail (x := x) (by linarith) (-γ / 2) 4
    have hy2_ge : (144 : ℝ) ≤ (-γ / 2) ^ 2 := by
      have h12 : (12 : ℝ) ≤ |γ| / 2 := by linarith
      have hsq : (12 : ℝ) ^ 2 ≤ (|γ| / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h12 2
      have heq : (|γ| / 2) ^ 2 = (-γ / 2) ^ 2 := by rw [div_pow, sq_abs]; ring
      linarith
    have hterm_mono : ∀ k : ℕ,
        (144 : ℝ) / (((2 + (k : ℝ))) * ((2 + (k : ℝ)) ^ 2 + 144)) ≤
        (-γ / 2) ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
      intro k
      have ha_pos : 0 < x + (k : ℝ) := by positivity
      have hb_pos : 0 < 2 + (k : ℝ) := by positivity
      have hab : x + (k : ℝ) ≤ 2 + (k : ℝ) := by linarith
      have h1 : (144 : ℝ) / ((2 + (k : ℝ)) * ((2 + (k : ℝ)) ^ 2 + 144)) ≤
          (144 : ℝ) / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + 144)) := by
        refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
        have hsq_le : (x + (k : ℝ)) ^ 2 ≤ (2 + (k : ℝ)) ^ 2 := pow_le_pow_left₀ (le_of_lt ha_pos) hab 2
        nlinarith
      have h2 : (144 : ℝ) / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + 144)) ≤
          (-γ / 2) ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos ha_pos (sq_pos_of_pos ha_pos)]
      exact le_trans h1 h2
    have hsum_le : (144 : ℝ) / ((2 : ℝ) * (2 ^ 2 + 144)) +
        (144 : ℝ) / ((3 : ℝ) * (3 ^ 2 + 144)) +
        (144 : ℝ) / ((4 : ℝ) * (4 ^ 2 + 144)) +
        (144 : ℝ) / ((5 : ℝ) * (5 ^ 2 + 144)) ≤
        ∑ k ∈ Finset.range 4, (-γ / 2) ^ 2 / ((x + (k : ℝ)) * ((x + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
      have h4 := Finset.sum_le_sum (s := Finset.range 4) fun k _ => hterm_mono k
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h4 ⊢
      norm_num at h4 ⊢; linarith
    have hlog5 : (16094 / 10000 : ℝ) ≤ Real.log (1 + (-γ / 2) ^ 2 / (x + ((4 : ℕ) : ℝ)) ^ 2) := by
      refine le_trans log_five_ge_16094 ?_
      refine Real.log_le_log (by norm_num) ?_
      have hden_le : (x + ((4 : ℕ) : ℝ)) ^ 2 ≤ 36 := by
        have hx4 : x + ((4 : ℕ) : ℝ) ≤ 6 := by push_cast; linarith
        have hsq := pow_le_pow_left₀ (by positivity) hx4 2
        norm_num at hsq; exact hsq
      have hfrac : (4 : ℝ) ≤ (-γ / 2) ^ 2 / (x + ((4 : ℕ) : ℝ)) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        calc (4 : ℝ) * (x + ((4 : ℕ) : ℝ)) ^ 2 ≤ 4 * 36 := by linarith [hden_le]
          _ = 144 := by norm_num
          _ ≤ (-γ / 2) ^ 2 := hy2_ge
      linarith
    linarith
  have hL_ub := LSeries_vonMangoldt_re_le_of_five_halves_le hβ0 γ
  rw [← hs_eq] at hL_ub
  rw [him_eq]
  have hnum : (0 : ℝ) < -(1 / 2 : ℝ) * (11448 / 10000) +
      (1 / 2 : ℝ) * ((-233 / 1000 : ℝ) +
        (144 : ℝ) / ((2 : ℝ) * (2 ^ 2 + 144)) +
        (144 : ℝ) / ((3 : ℝ) * (3 ^ 2 + 144)) +
        (144 : ℝ) / ((4 : ℝ) * (4 ^ 2 + 144)) +
        (144 : ℝ) / ((5 : ℝ) * (5 ^ 2 + 144)) +
        (1 / 2 : ℝ) * (16094 / 10000)) - (2925 / 10000 : ℝ) := by norm_num
  linarith [log_pi_le_11448]

/-- THEOREM IV.1 (UNCONDITIONAL GLOBAL ALL-`γ` HERGLOTZ POSITIVITY, RADIAL FORCE, DE BRANGES
    EQUATORIAL PHASE VELOCITY, AND STRICT SCHUR CONTRACTION ON THE PHASE-DESCENDED EULER
    HALF-PLANE `σ ≥ 2`, i.e. `Re(s) ≥ 5 / 2`!):
    Smashing +1.05 units PAST the naive triangle-inequality Euler wall (`σ ≈ 3.05`), and achieving
    a 3.75x total descent from Module #16's `σ ≥ 15/2` (and 1.75x below Module #17's `σ ≥ 7/2`),
    via Clifford-torus `{2, 3, 5, 7}` prime-phase preservation + `6k ± 1` telescoping tail +
    34-segment boundary certificate at `σ = 2` + Harmonic Minimum Principle on `[-24, 24] × [2, 7/2]`:
    For EVERY `σ ≥ 2` and EVERY `γ : ℝ`:
      (1) `0 < (xiResolvent (γ + iσ)).im` (global Herglotz positivity on `Im z ≥ 2`),
      (2) `0 < deriv (fun s => xiNormSq s γ) σ` and `0 < xiLogForce σ γ` (global radial force),
      (3) `0 < (logDeriv (xiSchur σ) γ).im` (strictly positive de Branges equatorial phase velocity),
      (4) `‖xiSchur α (γ + iσ)‖ < 1` whenever `0 < α, 0 < σ, 2 ≤ |σ - α|`. -/
theorem xiResolvent_herglotz_global_phase_euler_halfPlane_two :
    (∀ σ γ : ℝ, 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im) ∧
    (∀ α σ γ : ℝ, 0 < α → 0 < σ → 2 ≤ |σ - α| →
      ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ < 1) := by
  have hmain : ∀ σ γ : ℝ, 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
    intro σ γ hσ
    have hR_pos : 0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
      by_cases htop : 7 / 2 ≤ σ
      · exact (xiResolvent_herglotz_global_euler_halfPlane_seven_halves.1 σ γ htop).1
      · push Not at htop
        by_cases hbig : 24 ≤ |γ|
        · exact xiResolvent_im_pos_strip_large_gamma_24 hσ (le_of_lt htop) hbig
        · push Not at hbig
          have hγ_mem : γ ∈ Icc (-24 : ℝ) 24 := by
            have hab := abs_lt.mp hbig; exact ⟨le_of_lt hab.1, le_of_lt hab.2⟩
          exact xiResolvent_im_pos_of_rectangle_boundary (σ₀ := 2) (σ₁ := 7 / 2) (Y := 24)
            (by norm_num) (by norm_num) (by norm_num)
            (fun t _ => xiResolvent_im_pos_beta_five_halves_all t)
            (fun t _ => (xiResolvent_herglotz_global_euler_halfPlane_seven_halves.1 (7 / 2) t (le_refl _)).1)
            (fun s hs => xiResolvent_im_pos_strip_large_gamma_24 hs.1 hs.2 (by norm_num))
            (fun s hs => xiResolvent_im_pos_strip_large_gamma_24 hs.1 hs.2 (by norm_num))
            σ ⟨hσ, le_of_lt htop⟩ γ hγ_mem
    have hxi_ne : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 :=
      riemannXi_ne_zero_of_one_le_re (by simp; linarith)
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
  have hmono : StrictMonoOn (fun s : ℝ => xiNormSq s γ) (Set.Ici (2 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (2 : ℝ))
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

/-- THEOREM IV.2 (UNCONDITIONAL HOPF-BLOCH `S^2` NORTHERN HEMISPHERE CONFINEMENT AND
    STRICTLY POSITIVE ACCUMULATED DE BRANGES PHASE MEMORY DOWN TO `σ, α ≥ 2` FOR ALL `γ ∈ ℝ`!):
    (1) For EVERY `α > 0`, `σ > 0`, and `γ : ℝ` with `2 ≤ |σ - α|`:
          `0 < hopfBlochZ α (γ + iσ)` (strict confinement to the Open Northern Hemisphere of `S^2`).
    (2) For EVERY `α ≥ 2` and EVERY `γ₁ < γ₂`:
          `0 < deBrangesPhaseMemory α γ₁ γ₂ = ∫_{γ₁}^{γ₂} 2 * Im R_ξ(t + iα) dt`
        (strictly monotone forward equatorial phase accumulation with zero retrograde phase slips). -/
theorem hopfBloch_northern_hemisphere_and_phaseMemory_unconditional_euler_two :
    (∀ α σ γ : ℝ, 0 < α → 0 < σ → 2 ≤ |σ - α| →
      0 < hopfBlochZ α ((γ : ℂ) + Complex.I * (σ : ℂ))) ∧
    (∀ α γ₁ γ₂ : ℝ, 2 ≤ α → γ₁ < γ₂ →
      0 < deBrangesPhaseMemory α γ₁ γ₂) := by
  refine ⟨fun α σ γ hα hσ hge => ?_, fun α γ₁ γ₂ hα hγ => ?_⟩
  · have hE : xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0 := by
      dsimp [xiShiftE]
      have hsum : 2 ≤ σ + α := by
        rcases le_total α σ with h | h
        · rw [abs_of_nonneg (by linarith)] at hge; linarith
        · rw [abs_of_nonpos (by linarith)] at hge; linarith
      exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
    have hschur := xiResolvent_herglotz_global_phase_euler_halfPlane_two.2 α σ γ hα hσ hge
    exact (hopfBloch_northern_hemisphere_iff_schur_and_potential α σ γ hE).2.2.1.mpr hschur
  · dsimp [deBrangesPhaseMemory]
    have hcont : Continuous (fun t : ℝ => 2 * (xiResolvent ((t : ℂ) + Complex.I * (α : ℂ))).im) := by
      have hpath : Continuous (fun x : ℝ => (x : ℂ) + Complex.I * (α : ℂ)) :=
        Complex.continuous_ofReal.add continuous_const
      have hres : Continuous (fun x : ℝ => xiResolvent ((x : ℂ) + Complex.I * (α : ℂ))) :=
        differentiableOn_xiResolvent_halfPlane.continuousOn.comp_continuous hpath (fun x => by simp; linarith)
      exact continuous_const.mul (Complex.continuous_im.comp hres)
    exact intervalIntegral.integral_pos hγ hcont.continuousOn
      (fun t _ => le_of_lt (mul_pos (by norm_num) (xiResolvent_herglotz_global_phase_euler_halfPlane_two.1 α t hα).1))
      ⟨γ₁, Set.left_mem_Icc.mpr (le_of_lt hγ),
        mul_pos (by norm_num) (xiResolvent_herglotz_global_phase_euler_halfPlane_two.1 α γ₁ hα).1⟩

end CliffordPhaseEulerDescentAndPrimeWeil
