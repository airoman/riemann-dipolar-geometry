/-
  ==============================================================================
  MODULE #21: ROUTE A POLYNOMIAL SCHUR-GRAM REDUCTION & EXACT GRAM FACTORIZATION;
  ROUTE B ALL-ORDER ALTERNATING-COSINE CONVEXITY ENGINE, UNCONDITIONAL OPEN
  CRITICAL-STRIP COLLAR FOR EVERY HEIGHT T > 0, & EXACT RH EQUIVALENCE

  Title: Critical-Strip Collar, All-Order Convexity, and Polynomial Schur-Gram
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Route A — Exact Gram Factorization & All-Horizon Polynomial Schur):
      * `real_symmetric_psd_iff_gram_factorization`:
        For any real symmetric `n × n` matrix `W`, `W ⪰ 0` iff `∃ A, W = Aᵀ * A`
        (exact global Gram factorization equivalence via Mathlib4 spectral theorem).
      * `weilTotal_all_horizon_reduces_to_finite_polynomial_schur`:
        Combining Module #20's All-Horizon Coercivity with Hilbert-Schur reduction:
        for EVERY horizon `L > 0`, positivity of `weilTotal L` on all continuous
        functions `g = v + w` (`v ∈ P_{<2M(L)}`, `w ∈ P_{<2M(L)}^⊥`) reduces strictly
        to finite-dimensional Schur-complement positivity on `P_{<2M(L)}`.
  - Part II (Route B — All-Order Alternating-Cosine Convexity & Open Strip Collar):
      * `cos_ge_even_taylor_all_order`:
        For EVERY `m : ℕ` and EVERY `x : ℝ`,
          `∑ k ∈ Finset.range (2 * m + 2), (-1 : ℝ)^k * x^(2*k) / ((2*k).factorial : ℝ) ≤ Real.cos x`.
      * `xiNormSq_deriv2_ge_all_order_moment_poly`:
        For EVERY `m : ℕ`, `σ γ : ℝ`,
          `2 * ∑ k ∈ Finset.range (2 * m + 2), ((-1 : ℝ)^k * γ^(2*k) / ((2*k).factorial : ℝ)) * lightConeMoment2D k σ ≤ ∂_σ^2 V(σ, γ)`!
        (Formalizes the exact all-order engine behind the 220-digit 20-zero certificate!)
      * `riemannHypothesis_local_and_simple_of_all_order_poly_pos`:
        Positivity of the degree-`(4m+2)` moment polynomial on `[0, 1/2] × [-Γ, Γ]`
        unconditionally certifies Local RH AND strict zero simplicity on `[-Γ, Γ]`.
      * `criticalStrip_unconditional_open_collar_for_every_height`:
        For EVERY height `T > 0`, using Module #20's complete closure of `Re(s) = 1`
        and compactness of `[-T, T]`, there exists `δ ∈ (0, 1/2)` such that STRICTLY
        INSIDE THE OPEN CRITICAL STRIP, for all `σ ∈ [1/2 - δ, ∞)` and `γ ∈ [-T, T]`:
          `0 < (xiResolvent (γ + iσ)).im`, `0 < deriv (fun s => xiNormSq s γ) σ`,
          `riemannZeta (1/2 + σ + iγ) ≠ 0`, AND `riemannZeta (1/2 - σ + iγ) ≠ 0`!
      * `xiShiftE_zeroFree_uhp_iff_riemannHypothesis`:
        Exact biconditional: Mathlib4's `RiemannHypothesis` holds iff for every
        `α > 0` and every `z ∈ ℂ` with `0 ≤ z.im`, `xiShiftE α z ≠ 0`!
  ==============================================================================
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.XiConvexityLaguerre
import RiemannDipolar.WeilArchimedeanAndExplicitCorridor
import RiemannDipolar.ArithmeticWeilAndWideCorridor
import RiemannDipolar.UniversalWeilAndHerglotzResolvent
import RiemannDipolar.HermiteBiehlerHomotopyAndWeilPick
import RiemannDipolar.CompactMomentWeilAndHopfBlochEulerDescent
import RiemannDipolar.PhaseBarrierEulerDescentAndMultiPrimeWeil
import RiemannDipolar.GlobalOuterHalfPlaneClosureAndAllHorizonWeil

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators Classical Matrix
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick UniversalSolverLyapunovAndPrimeResolvent
open RouteABLimitBarriersAndDeBrangesSynthesis GeodesicRenormalizationAndEulerJacobiPick
open CompactMomentWeilAndHopfBlochEulerDescent CliffordPhaseEulerDescentAndPrimeWeil
open PhaseBarrierEulerDescentAndMultiPrimeWeil GlobalOuterHalfPlaneClosureAndAllHorizonWeil

namespace CriticalStripCollarAllOrderConvexityAndSchurGram

-- ==============================================================================
-- PART I: ROUTE A — EXACT GRAM FACTORIZATION EQUIVALENCE & ALL-HORIZON
--         FINITE-DIMENSIONAL POLYNOMIAL SCHUR REDUCTION
-- ==============================================================================

/-- THEOREM I.1 (EXACT GLOBAL GRAM FACTORIZATION EQUIVALENCE FOR REAL SYMMETRIC MATRICES):
    A real symmetric `n × n` matrix `W` (`W.IsHermitian`) is positive semidefinite
      `∀ v : Fin n → ℝ, 0 ≤ dotProduct v (W.mulVec v)`
    IF AND ONLY IF it admits a global Gram factorization `W = Aᵀ * A`!
    This formalizes the exact finite-dimensional target for Route A's Schur block. -/
theorem real_symmetric_psd_iff_gram_factorization {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsHermitian) :
    (∀ v : Fin n → ℝ, 0 ≤ dotProduct v (W.mulVec v)) ↔
      ∃ A : Matrix (Fin n) (Fin n) ℝ, W = Aᵀ * A := by
  constructor
  · intro hpsd
    have hspec := hW.spectral_theorem
    let U : Matrix (Fin n) (Fin n) ℝ := (hW.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    let ev : Fin n → ℝ := hW.eigenvalues
    have hev_nn : ∀ i : Fin n, 0 ≤ ev i := by
      intro i
      have hvec := hW.mulVec_eigenvectorBasis i
      have h0 := hpsd (hW.eigenvectorBasis i)
      rw [hvec, dotProduct_smul, smul_eq_mul] at h0
      have hnorm : dotProduct (⇑(hW.eigenvectorBasis i)) (⇑(hW.eigenvectorBasis i)) = 1 := by
        have horth := hW.eigenvectorBasis.orthonormal.1 i
        rw [EuclideanSpace.norm_eq] at horth
        have hsq : ∑ j : Fin n, ‖(hW.eigenvectorBasis i) j‖ ^ 2 = 1 := by
          have h1 : Real.sqrt (∑ j : Fin n, ‖(hW.eigenvectorBasis i) j‖ ^ 2) ^ 2 = 1 ^ 2 := by
            rw [horth]
          rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), one_pow] at h1
        simpa [dotProduct, Real.norm_eq_abs, sq_abs, sq] using hsq
      rw [hnorm, mul_one] at h0
      exact h0
    let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Real.sqrt (ev i)) * Uᵀ
    refine ⟨A, ?_⟩
    have hAT : Aᵀ = U * Matrix.diagonal (fun i => Real.sqrt (ev i)) := by
      dsimp [A]
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    rw [hAT]
    have hdiag : Matrix.diagonal (fun i => Real.sqrt (ev i)) *
        Matrix.diagonal (fun i => Real.sqrt (ev i)) = Matrix.diagonal ev := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; ext i; exact Real.mul_self_sqrt (hev_nn i)
    calc W = U * Matrix.diagonal ev * star U := by
          simpa [U, ev, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hspec
      _ = U * (Matrix.diagonal (fun i => Real.sqrt (ev i)) *
            Matrix.diagonal (fun i => Real.sqrt (ev i))) * Uᵀ := by
          rw [hdiag, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = U * Matrix.diagonal (fun i => Real.sqrt (ev i)) *
            (Matrix.diagonal (fun i => Real.sqrt (ev i)) * Uᵀ) := by
          simp only [Matrix.mul_assoc]
  · rintro ⟨A, rfl⟩ v
    have hdot : dotProduct v ((Aᵀ * A).mulVec v) = dotProduct (A.mulVec v) (A.mulVec v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hdot]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- THEOREM I.2 (ALL-HORIZON POLYNOMIAL SCHUR-COMPLEMENT REDUCTION ON `C([-L/2, L/2])`):
    For EVERY horizon `L > 0` and EVERY desired tail coercivity `lam_perp > 0`, there exists
    a finite moment order `M ≥ 1` such that `weilTotal L` is strictly coercive on the
    infinite-dimensional orthogonal complement `P_{<2M}^⊥` (`lam_perp * ‖w‖_2^2 ≤ weilTotal L w`),
    and consequently ANY quadratic decomposition `Q(v, w) = Q11(v) + 2 B(v, w) + weilTotal L w`
    with cross-coupling `|B(v, w)| ≤ β(v) * ‖w‖_2` is strictly positive on ALL nonzero `(v, w)`
    whenever the finite-dimensional Schur complement `Q11(v) - β(v)^2 / lam_perp > 0` on `v ≠ 0`! -/
theorem weilTotal_all_horizon_reduces_to_finite_polynomial_schur (L lam_perp : ℝ)
    (hL0 : 0 < L) (hlam : 0 < lam_perp) :
    ∃ M : ℕ, 1 ≤ M ∧
      ∀ {V : Type*} [Zero V] (Q11 : V → ℝ) (B : V → (ℝ → ℂ) → ℝ) (β : V → ℝ),
        Q11 0 = 0 → β 0 = 0 →
        (∀ v : V, v ≠ 0 → 0 < Q11 v - (β v) ^ 2 / lam_perp) →
        ∀ (v : V) (w : ℝ → ℂ),
          Continuous w →
          (∀ k : ℕ, k < 2 * M → ∫ u in (-L / 2)..(L / 2), ((u ^ k : ℝ) : ℂ) * w u = 0) →
          ((1 / (2 * Real.pi)) * (∫ t : ℝ, ‖compactFourier L w t‖ ^ 2) =
            ∫ u in (-L / 2)..(L / 2), ‖w u‖ ^ 2) →
          Integrable (fun t : ℝ => psiArch t * ‖compactFourier L w t‖ ^ 2) →
          Integrable (fun t : ℝ => ‖compactFourier L w t‖ ^ 2) →
          |B v w| ≤ β v * Real.sqrt (∫ u in (-L / 2)..(L / 2), ‖w u‖ ^ 2) →
          (v ≠ 0 ∨ 0 < ∫ u in (-L / 2)..(L / 2), ‖w u‖ ^ 2) →
          0 < Q11 v + 2 * B v w + weilTotal L w := by
  rcases weilTotal_all_horizon_finiteCodim_coercive L lam_perp hL0 with ⟨M, hM1, hcoerc⟩
  refine ⟨M, hM1, fun {V} _ Q11 B β hQ0 hβ0 hschur v w hw hmom hpar hia hip hB hne => ?_⟩
  have hnw_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖w u‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  set nw : ℝ := Real.sqrt (∫ u in (-L / 2)..(L / 2), ‖w u‖ ^ 2)
  have hnw_sq : nw ^ 2 = ∫ u in (-L / 2)..(L / 2), ‖w u‖ ^ 2 := Real.sq_sqrt hnw_nn
  have hW_ge : lam_perp * nw ^ 2 ≤ weilTotal L w := by
    rw [hnw_sq]; exact hcoerc hw hmom hpar hia hip
  have hB_lb : -(β v * nw) ≤ B v w := (abs_le.mp hB).1
  have hquad : Q11 v - (β v) ^ 2 / lam_perp + lam_perp * (nw - β v / lam_perp) ^ 2 ≤
      Q11 v + 2 * B v w + weilTotal L w := by
    have hsq : lam_perp * (nw - β v / lam_perp) ^ 2 =
        lam_perp * nw ^ 2 - 2 * (β v * nw) + (β v) ^ 2 / lam_perp := by
      field_simp [ne_of_gt hlam]; ring
    linarith
  by_cases hv : v = 0
  · subst hv
    rcases hne with hcontra | hnorm_pos
    · exact False.elim (hcontra rfl)
    · rw [hQ0]
      rw [hQ0, hβ0] at hquad
      have hpos : 0 < lam_perp * nw ^ 2 := by rw [hnw_sq]; exact mul_pos hlam hnorm_pos
      simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, zero_add] at hquad
      linarith
  · have hs := hschur v hv
    have hsq_nn : 0 ≤ lam_perp * (nw - β v / lam_perp) ^ 2 :=
      mul_nonneg (le_of_lt hlam) (sq_nonneg _)
    linarith

-- ==============================================================================
-- PART II: ROUTE B — ALL-ORDER ALTERNATING-COSINE CONVEXITY ENGINE,
--          UNCONDITIONAL OPEN CRITICAL-STRIP COLLAR FOR EVERY HEIGHT T > 0,
--          AND EXACT HERMITE-BIEHLER ZERO-FREE BICONDITIONAL FOR RH
-- ==============================================================================

/-- Helper II.1A: Elementary alternating Taylor bounds for `Real.cos` at ALL orders `n : ℕ`. -/
private lemma cos_alternating_taylor_bounds_nonneg :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (Even n → Real.cos x ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)) ∧
      (Odd n → ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cos x) := by
  intro n
  induction n with
  | zero =>
    intro x _
    refine ⟨fun _ => by simp [Real.cos_le_one], fun hodd => False.elim (by simp at hodd)⟩
  | succ m ih =>
    intro x hx
    let P : ℕ → ℝ → ℝ := fun r t =>
      ∑ k ∈ Finset.range (r + 1), (-1 : ℝ) ^ k * t ^ (2 * k) / ((2 * k).factorial : ℝ)
    let Q : ℕ → ℝ → ℝ := fun r t =>
      ∑ j ∈ Finset.range r, (-1 : ℝ) ^ (j + 1) * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)
    have hP0 : ∀ r, P r 0 = 1 := fun r => by
      dsimp [P]
      rw [Finset.sum_range_succ']
      simp [Finset.sum_eq_zero]
    have hQ0 : ∀ r, Q r 0 = 0 := fun r => by
      dsimp [Q]
      exact Finset.sum_eq_zero fun j _ => by simp
    have hderivP : ∀ t : ℝ, HasDerivAt (P (m + 1)) (Q (m + 1) t) t := fun t => by
      dsimp [P, Q]
      have hterm : ∀ k ∈ Finset.range (m + 2),
          HasDerivAt (fun s : ℝ => (-1 : ℝ) ^ k * s ^ (2 * k) / ((2 * k).factorial : ℝ))
            (if k = 0 then 0 else (-1 : ℝ) ^ k * t ^ (2 * k - 1) / ((2 * k - 1).factorial : ℝ)) t := by
        intro k _
        by_cases hk : k = 0
        · subst hk; simp only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one, ↓reduceIte]
          exact hasDerivAt_const t (1 : ℝ)
        · simp only [hk, ↓reduceIte]
          have h1 := ((hasDerivAt_pow (2 * k) t).const_mul ((-1 : ℝ) ^ k)).div_const (((2 * k).factorial : ℝ))
          refine h1.congr_deriv ?_
          have h2k : 2 * k = (2 * k - 1) + 1 := by omega
          have hfacN : (2 * k).factorial = (2 * k) * (2 * k - 1).factorial := by
            conv_lhs => rw [h2k, Nat.factorial_succ]
            rw [← h2k]
          have hfac : ((2 * k).factorial : ℝ) = ((2 * k : ℕ) : ℝ) * ((2 * k - 1).factorial : ℝ) := by
            exact_mod_cast hfacN
          have h2k_ne : ((2 * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 2 * k ≠ 0)
          rw [hfac]; field_simp [h2k_ne]
      have hsum := HasDerivAt.fun_sum hterm
      refine hsum.congr_deriv ?_
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      have hsub : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [hsub]
    have hderivQ : ∀ t : ℝ, HasDerivAt (Q (m + 1)) (-P m t) t := fun t => by
      dsimp [P, Q]
      have hterm : ∀ j ∈ Finset.range (m + 1),
          HasDerivAt (fun s : ℝ => (-1 : ℝ) ^ (j + 1) * s ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
            (-((-1 : ℝ) ^ j * t ^ (2 * j) / ((2 * j).factorial : ℝ))) t := by
        intro j _
        have h1 := ((hasDerivAt_pow (2 * j + 1) t).const_mul ((-1 : ℝ) ^ (j + 1))).div_const (((2 * j + 1).factorial : ℝ))
        refine h1.congr_deriv ?_
        have hfac : ((2 * j + 1).factorial : ℝ) = ((2 * j + 1 : ℕ) : ℝ) * ((2 * j).factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; rfl
        have hne : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
        rw [hfac, pow_succ, Nat.add_sub_cancel]; field_simp [hne]
      have hsum := HasDerivAt.fun_sum hterm
      refine hsum.congr_deriv ?_
      rw [Finset.sum_neg_distrib]
    constructor
    · intro heven
      have hodd_m : Odd m := by
        rcases heven with ⟨r, hr⟩
        exact ⟨r - 1, by omega⟩
      have hQ_ge : ∀ t : ℝ, 0 ≤ t → -Real.sin t ≤ Q (m + 1) t := by
        intro t ht
        have hmono : AntitoneOn (fun s : ℝ => -Real.sin s - Q (m + 1) s) (Ici 0) := by
          refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
            (fun s _ => ((Real.hasDerivAt_sin s).fun_neg.fun_sub (hderivQ s)).continuousAt.continuousWithinAt)
            (fun s _ => ((Real.hasDerivAt_sin s).fun_neg.fun_sub (hderivQ s)).differentiableAt.differentiableWithinAt)
            (fun s hs => ?_)
          have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
          rw [((Real.hasDerivAt_sin s).fun_neg.fun_sub (hderivQ s)).deriv]
          have hih := (ih s hs0).2 hodd_m
          linarith
        have hle := hmono (le_refl (0 : ℝ)) ht ht
        simp [hQ0] at hle; linarith
      have hP_ge : AntitoneOn (fun s : ℝ => Real.cos s - P (m + 1) s) (Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
          (fun s _ => ((Real.hasDerivAt_cos s).fun_sub (hderivP s)).continuousAt.continuousWithinAt)
          (fun s _ => ((Real.hasDerivAt_cos s).fun_sub (hderivP s)).differentiableAt.differentiableWithinAt)
          (fun s hs => ?_)
        have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
        rw [((Real.hasDerivAt_cos s).fun_sub (hderivP s)).deriv]
        linarith [hQ_ge s hs0]
      have hle := hP_ge (le_refl (0 : ℝ)) hx hx
      simp [hP0] at hle; linarith
    · intro hodd
      have heven_m : Even m := by
        rcases hodd with ⟨r, hr⟩
        exact ⟨r, by omega⟩
      have hQ_le : ∀ t : ℝ, 0 ≤ t → Q (m + 1) t ≤ -Real.sin t := by
        intro t ht
        have hmono : MonotoneOn (fun s : ℝ => -Real.sin s - Q (m + 1) s) (Ici 0) := by
          refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
            (fun s _ => ((Real.hasDerivAt_sin s).fun_neg.fun_sub (hderivQ s)).continuousAt.continuousWithinAt)
            (fun s _ => ((Real.hasDerivAt_sin s).fun_neg.fun_sub (hderivQ s)).differentiableAt.differentiableWithinAt)
            (fun s hs => ?_)
          have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
          rw [((Real.hasDerivAt_sin s).fun_neg.fun_sub (hderivQ s)).deriv]
          have hih := (ih s hs0).1 heven_m
          linarith
        have hle := hmono (le_refl (0 : ℝ)) ht ht
        simp [hQ0] at hle; linarith
      have hP_le : MonotoneOn (fun s : ℝ => Real.cos s - P (m + 1) s) (Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
          (fun s _ => ((Real.hasDerivAt_cos s).fun_sub (hderivP s)).continuousAt.continuousWithinAt)
          (fun s _ => ((Real.hasDerivAt_cos s).fun_sub (hderivP s)).differentiableAt.differentiableWithinAt)
          (fun s hs => ?_)
        have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
        rw [((Real.hasDerivAt_cos s).fun_sub (hderivP s)).deriv]
        linarith [hQ_le s hs0]
      have hle := hP_le (le_refl (0 : ℝ)) hx hx
      simp [hP0] at hle; linarith

/-- THEOREM II.1 (ALL-ORDER ALTERNATING-COSINE LOWER BOUND FOR EVERY `m : ℕ` AND `x : ℝ`):
    Generalizes Module #13's `cos_ge_taylor_six` (`m = 1`) to EVERY order `m : ℕ`:
      `∑ k ∈ Finset.range (2 * m + 2), (-1)^k * x^(2k) / (2k)! ≤ Real.cos x`! -/
theorem cos_ge_even_taylor_all_order (m : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cos x := by
  have h := (cos_alternating_taylor_bounds_nonneg (2 * m + 1) |x| (abs_nonneg x)).2 ⟨m, rfl⟩
  rw [Real.cos_abs] at h
  refine le_trans ?_ h
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  have habs : |x| ^ (2 * k) = x ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  rw [habs]

/-- Definition: The `2k`-th 2D light-cone moment `μ_{2k}(σ)` of the transverse Hessian kernel. -/
noncomputable def lightConeMoment2D (k : ℕ) (σ : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
    riemannPhi u * riemannPhi v *
      ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
       (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))

/-- Helper: Elementary domination of `(u ± v)^(2k)` and `cosh(σ*(u ± v))` on `u, v > 0`. -/
private lemma lightCone_integrand_dom (k : ℕ) (σ u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    0 ≤ riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k)) ∧
    riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k)) ≤
      (4 * (2 : ℝ) ^ (2 * k + 2)) *
        ((riemannPhi u * u ^ (2 * k + 2) * Real.cosh (|σ| * u)) * (riemannPhi v * Real.cosh (|σ| * v)) +
         (riemannPhi u * Real.cosh (|σ| * u)) * (riemannPhi v * v ^ (2 * k + 2) * Real.cosh (|σ| * v))) := by
  have hpu : 0 < riemannPhi u := riemannPhi_pos u
  have hpv : 0 < riemannPhi v := riemannPhi_pos v
  have hnn : 0 ≤ riemannPhi u * riemannPhi v *
      ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
       (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k)) := by
    have h1 : 0 ≤ (u - v) ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k
    have h2 : 0 ≤ (u + v) ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k
    exact mul_nonneg (mul_nonneg (le_of_lt hpu) (le_of_lt hpv))
      (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))) h1)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))) h2))
  refine ⟨hnn, ?_⟩
  have hch_add : Real.cosh (σ * (u + v)) ≤ 2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v) := by
    have h1 : Real.cosh (σ * (u + v)) = Real.cosh (|σ| * (u + v)) := by
      rw [← Real.cosh_abs, abs_mul, abs_of_pos (by linarith : 0 < u + v)]
    rw [h1, mul_add, Real.cosh_add]
    have hsh1 : Real.sinh (|σ| * u) ≤ Real.cosh (|σ| * u) := by
      rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-(|σ| * u))]
    have hsh2 : Real.sinh (|σ| * v) ≤ Real.cosh (|σ| * v) := by
      rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-(|σ| * v))]
    have hsh1_nn : 0 ≤ Real.sinh (|σ| * u) := Real.sinh_nonneg_iff.mpr (mul_nonneg (abs_nonneg σ) (le_of_lt hu))
    nlinarith [Real.cosh_pos (|σ| * u), Real.cosh_pos (|σ| * v)]
  have hch_sub : Real.cosh (σ * (u - v)) ≤ 2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v) := by
    refine le_trans ?_ hch_add
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)
    rw [abs_of_pos (by linarith : 0 < u + v), abs_le]; constructor <;> linarith
  have hpow_uv : (u + v) ^ (2 * k + 2) ≤ (2 : ℝ) ^ (2 * k + 2) * (u ^ (2 * k + 2) + v ^ (2 * k + 2)) := by
    have hle : u + v ≤ 2 * max u v := by linarith [le_max_left u v, le_max_right u v]
    have h1 : (u + v) ^ (2 * k + 2) ≤ (2 * max u v) ^ (2 * k + 2) :=
      pow_le_pow_left₀ (by linarith) hle (2 * k + 2)
    rw [mul_pow] at h1
    have hmax : (max u v) ^ (2 * k + 2) ≤ u ^ (2 * k + 2) + v ^ (2 * k + 2) := by
      rcases le_total u v with huv | hvu
      · rw [max_eq_right huv]; linarith [pow_nonneg (le_of_lt hu) (2 * k + 2)]
      · rw [max_eq_left hvu]; linarith [pow_nonneg (le_of_lt hv) (2 * k + 2)]
    exact le_trans h1 (mul_le_mul_of_nonneg_left hmax (by positivity))
  have hsub_le_add : |u - v| ≤ u + v := by rw [abs_le]; constructor <;> linarith
  have hterm1 : (u + v) ^ 2 * (u - v) ^ (2 * k) ≤ (u + v) ^ (2 * k + 2) := by
    have h1 : (u - v) ^ (2 * k) ≤ (u + v) ^ (2 * k) := by
      have : (u - v) ^ (2 * k) = |u - v| ^ (2 * k) := by rw [pow_mul, ← sq_abs, ← pow_mul]
      rw [this]; exact pow_le_pow_left₀ (abs_nonneg _) hsub_le_add (2 * k)
    calc (u + v) ^ 2 * (u - v) ^ (2 * k)
      _ ≤ (u + v) ^ 2 * (u + v) ^ (2 * k) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (u + v) ^ (2 * k + 2) := by rw [← pow_add, Nat.add_comm]
  have hterm2 : (u - v) ^ 2 * (u + v) ^ (2 * k) ≤ (u + v) ^ (2 * k + 2) := by
    have h1 : (u - v) ^ 2 ≤ (u + v) ^ 2 := by nlinarith
    calc (u - v) ^ 2 * (u + v) ^ (2 * k)
      _ ≤ (u + v) ^ 2 * (u + v) ^ (2 * k) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (u + v) ^ (2 * k + 2) := by rw [← pow_add, Nat.add_comm]
  have hinner : (u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
      (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k) ≤
      (4 * (2 : ℝ) ^ (2 * k + 2)) * (Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) *
        (u ^ (2 * k + 2) + v ^ (2 * k + 2)) := by
    have hc1 : (u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) ≤
        (2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) * (u + v) ^ (2 * k + 2) := by
      calc (u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k)
        _ = Real.cosh (σ * (u + v)) * ((u + v) ^ 2 * (u - v) ^ (2 * k)) := by ring
        _ ≤ (2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) * (u + v) ^ (2 * k + 2) :=
            mul_le_mul hch_add hterm1 (mul_nonneg (sq_nonneg _) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k))
              (by positivity)
    have hc2 : (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k) ≤
        (2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) * (u + v) ^ (2 * k + 2) := by
      calc (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k)
        _ = Real.cosh (σ * (u - v)) * ((u - v) ^ 2 * (u + v) ^ (2 * k)) := by ring
        _ ≤ (2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) * (u + v) ^ (2 * k + 2) :=
            mul_le_mul hch_sub hterm2 (by positivity) (by positivity)
    have hc_sum : (2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) * (u + v) ^ (2 * k + 2) +
        (2 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) * (u + v) ^ (2 * k + 2) ≤
        (4 * (2 : ℝ) ^ (2 * k + 2)) * (Real.cosh (|σ| * u) * Real.cosh (|σ| * v)) *
          (u ^ (2 * k + 2) + v ^ (2 * k + 2)) := by
      have hmul := mul_le_mul_of_nonneg_left hpow_uv
        (show 0 ≤ 4 * Real.cosh (|σ| * u) * Real.cosh (|σ| * v) by positivity)
      linarith
    linarith
  have hmul_phi := mul_le_mul_of_nonneg_left hinner (mul_nonneg (le_of_lt hpu) (le_of_lt hpv))
  linarith

/-- THEOREM II.2 (ALL-ORDER LIGHT-CONE MOMENT POLYNOMIAL LOWER BOUND FOR THE TRANSVERSE HESSIAN):
    For EVERY order `m : ℕ`, EVERY `σ : ℝ`, and EVERY `γ : ℝ`,
      `2 * ∑ k ∈ Finset.range (2 * m + 2), ((-1)^k * γ^(2k) / (2k)!) * lightConeMoment2D k σ ≤ ∂_σ^2 V(σ, γ)`!
    This formalizes the exact mathematical engine behind the 220-digit 20-zero certificate! -/
theorem xiNormSq_deriv2_ge_all_order_moment_poly (m : ℕ) (σ γ : ℝ) :
    2 * ∑ k ∈ Finset.range (2 * m + 2),
      ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) * lightConeMoment2D k σ ≤
      deriv (deriv (fun s : ℝ => xiNormSq s γ)) σ := by
  rw [xiNormSq_deriv2_eq_pastFuture_double_integral σ γ]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  -- Integrability of each inner/outer `k`-th light-cone moment integrand
  have hint_inner : ∀ k : ℕ, ∀ u : ℝ, 0 < u →
      IntegrableOn (fun v : ℝ => riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))) (Ioi 0) := by
    intro k u hu
    have hdom : IntegrableOn (fun v : ℝ =>
        (4 * (2 : ℝ) ^ (2 * k + 2)) *
          ((riemannPhi u * u ^ (2 * k + 2) * Real.cosh (|σ| * u)) * (riemannPhi v * Real.cosh (|σ| * v)) +
           (riemannPhi u * Real.cosh (|σ| * u)) * (riemannPhi v * v ^ (2 * k + 2) * Real.cosh (|σ| * v)))) (Ioi 0) := by
      have h0 : IntegrableOn (fun v : ℝ => riemannPhi v * Real.cosh (|σ| * v)) (Ioi 0) := by
        simpa [pow_zero, mul_one] using integrableOn_phi_pow_cosh 0 |σ|
      have h2k : IntegrableOn (fun v : ℝ => riemannPhi v * v ^ (2 * k + 2) * Real.cosh (|σ| * v)) (Ioi 0) :=
        integrableOn_phi_pow_cosh (2 * k + 2) |σ|
      exact ((h0.const_mul _).add (h2k.const_mul _)).const_mul _
    refine hdom.mono' ?_ (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) fun v hv => ?_)
    · exact ((continuous_const.mul continuous_riemannPhi).mul
        ((((continuous_const.add continuous_id).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_const.add continuous_id)))).mul
          ((continuous_const.sub continuous_id).pow (2 * k)) |>.add
        ((((continuous_const.sub continuous_id).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_const.sub continuous_id)))).mul
          ((continuous_const.add continuous_id).pow (2 * k))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (lightCone_integrand_dom k σ u v hu hv).1]
      exact (lightCone_integrand_dom k σ u v hu hv).2
  have hint_outer : ∀ k : ℕ,
      IntegrableOn (fun u : ℝ => ∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))) (Ioi 0) := by
    intro k
    have h0 : IntegrableOn (fun v : ℝ => riemannPhi v * Real.cosh (|σ| * v)) (Ioi 0) := by
      simpa [pow_zero, mul_one] using integrableOn_phi_pow_cosh 0 |σ|
    have h2k : IntegrableOn (fun v : ℝ => riemannPhi v * v ^ (2 * k + 2) * Real.cosh (|σ| * v)) (Ioi 0) :=
      integrableOn_phi_pow_cosh (2 * k + 2) |σ|
    set I0 : ℝ := ∫ v in Ioi (0 : ℝ), riemannPhi v * Real.cosh (|σ| * v)
    set I2k : ℝ := ∫ v in Ioi (0 : ℝ), riemannPhi v * v ^ (2 * k + 2) * Real.cosh (|σ| * v)
    have hdom_u : IntegrableOn (fun u : ℝ =>
        (4 * (2 : ℝ) ^ (2 * k + 2)) *
          ((riemannPhi u * u ^ (2 * k + 2) * Real.cosh (|σ| * u)) * I0 +
           (riemannPhi u * Real.cosh (|σ| * u)) * I2k)) (Ioi 0) :=
      ((h2k.mul_const I0).add (h0.mul_const I2k)).const_mul _
    -- Measurability of the inner integral via `AEStronglyMeasurable.integral_prod_right'`
    have hcont2 : Continuous (fun p : ℝ × ℝ => riemannPhi p.1 * riemannPhi p.2 *
        ((p.1 + p.2) ^ 2 * Real.cosh (σ * (p.1 + p.2)) * (p.1 - p.2) ^ (2 * k) +
         (p.1 - p.2) ^ 2 * Real.cosh (σ * (p.1 - p.2)) * (p.1 + p.2) ^ (2 * k))) := by
      exact ((continuous_riemannPhi.comp continuous_fst).mul (continuous_riemannPhi.comp continuous_snd)).mul
        (((((continuous_fst.add continuous_snd).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_fst.add continuous_snd)))).mul
          ((continuous_fst.sub continuous_snd).pow (2 * k))).add
        ((((continuous_fst.sub continuous_snd).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_fst.sub continuous_snd)))).mul
          ((continuous_fst.add continuous_snd).pow (2 * k))))
    refine hdom_u.mono' (hcont2.aestronglyMeasurable.integral_prod_right')
      (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) fun u hu => ?_)
    have hnn_int : 0 ≤ ∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k)) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun v hv =>
        (lightCone_integrand_dom k σ u v hu hv).1
    rw [Real.norm_eq_abs, abs_of_nonneg hnn_int]
    have hmono := MeasureTheory.setIntegral_mono_on (hint_inner k u hu)
      (((h0.const_mul (riemannPhi u * u ^ (2 * k + 2) * Real.cosh (|σ| * u))).add
        (h2k.const_mul (riemannPhi u * Real.cosh (|σ| * u)))).const_mul (4 * (2 : ℝ) ^ (2 * k + 2)))
      measurableSet_Ioi fun v hv => (lightCone_integrand_dom k σ u v hu hv).2
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul]
    have hadd_eq : ∫ v in Ioi (0 : ℝ),
        ((fun v => riemannPhi u * u ^ (2 * k + 2) * Real.cosh (|σ| * u) * (riemannPhi v * Real.cosh (|σ| * v))) +
         (fun v => riemannPhi u * Real.cosh (|σ| * u) * (riemannPhi v * v ^ (2 * k + 2) * Real.cosh (|σ| * v)))) v =
        (riemannPhi u * u ^ (2 * k + 2) * Real.cosh (|σ| * u)) * I0 +
        (riemannPhi u * Real.cosh (|σ| * u)) * I2k := by
      simp only [Pi.add_apply]
      rw [MeasureTheory.integral_add (h0.const_mul _) (h2k.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hadd_eq]
  -- Helper for finite sum of integrable functions on `Ioi 0`
  have hsum_int : ∀ {N : ℕ} {F : ℕ → ℝ → ℝ}, (∀ k < N, IntegrableOn (F k) (Ioi 0)) →
      IntegrableOn (fun x => ∑ k ∈ Finset.range N, F k x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), ∑ k ∈ Finset.range N, F k x) =
        ∑ k ∈ Finset.range N, ∫ x in Ioi (0 : ℝ), F k x := by
    intro N
    induction N with
    | zero =>
      intro F _
      simp
    | succ r ih =>
      intro F hF
      obtain ⟨hint_r, hval_r⟩ := ih fun k hk => hF k (Nat.lt_succ_of_lt hk)
      have hFr := hF r (Nat.lt_succ_self r)
      have heq_fn : (fun x => ∑ k ∈ Finset.range (r + 1), F k x) =
          fun x => (∑ k ∈ Finset.range r, F k x) + F r x := by
        ext x; rw [Finset.sum_range_succ]
      rw [heq_fn]
      refine ⟨hint_r.add hFr, ?_⟩
      rw [MeasureTheory.integral_add hint_r hFr, hval_r, Finset.sum_range_succ]
  -- Pull the finite sum inside the outer and inner integrals and compare pointwise via `cos_ge_even_taylor_all_order m`!
  have houter_pack := hsum_int (N := 2 * m + 2)
    (F := fun k u => ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) *
      (∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))))
    (fun k _ => (hint_outer k).const_mul _)
  have hsum_outer :
      ∑ k ∈ Finset.range (2 * m + 2),
        ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) * lightConeMoment2D k σ =
      ∫ u in Ioi (0 : ℝ),
        ∑ k ∈ Finset.range (2 * m + 2),
          ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
              ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
               (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))) := by
    rw [houter_pack.2]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [lightConeMoment2D]
    rw [← MeasureTheory.integral_const_mul]
  rw [hsum_outer]
  -- Integrability of the RHS outer integrand (already bounded by `lightConeMoment2D 0 σ`)
  have hrhs_inner : ∀ u : ℝ, 0 < u →
      IntegrableOn (fun v : ℝ => riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) (Ioi 0) := by
    intro u hu
    refine (hint_inner 0 u hu).mono' ?_ (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) fun v hv => ?_)
    · exact ((continuous_const.mul continuous_riemannPhi).mul
        (((((continuous_const.add continuous_id).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_const.add continuous_id)))).mul
          (Real.continuous_cos.comp (continuous_const.mul (continuous_const.sub continuous_id)))).add
        ((((continuous_const.sub continuous_id).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_const.sub continuous_id)))).mul
          (Real.continuous_cos.comp (continuous_const.mul (continuous_const.add continuous_id)))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h1 : |riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
           (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))| ≤
          riemannPhi u * riemannPhi v *
          ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * 1 + (u - v) ^ 2 * Real.cosh (σ * (u - v)) * 1) := by
        rw [abs_mul, abs_of_pos (mul_pos (riemannPhi_pos u) (riemannPhi_pos v))]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (mul_pos (riemannPhi_pos u) (riemannPhi_pos v)))
        refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))]
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))
        · rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))]
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))
      simpa [pow_zero] using h1
  have hrhs_outer :
      IntegrableOn (fun u : ℝ => ∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))) (Ioi 0) := by
    have hcont_rhs : Continuous (fun p : ℝ × ℝ => riemannPhi p.1 * riemannPhi p.2 *
        ((p.1 + p.2) ^ 2 * Real.cosh (σ * (p.1 + p.2)) * Real.cos (γ * (p.1 - p.2)) +
         (p.1 - p.2) ^ 2 * Real.cosh (σ * (p.1 - p.2)) * Real.cos (γ * (p.1 + p.2)))) := by
      exact ((continuous_riemannPhi.comp continuous_fst).mul (continuous_riemannPhi.comp continuous_snd)).mul
        (((((continuous_fst.add continuous_snd).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_fst.add continuous_snd)))).mul
          (Real.continuous_cos.comp (continuous_const.mul (continuous_fst.sub continuous_snd)))).add
        ((((continuous_fst.sub continuous_snd).pow 2).mul
          (Real.continuous_cosh.comp (continuous_const.mul (continuous_fst.sub continuous_snd)))).mul
          (Real.continuous_cos.comp (continuous_const.mul (continuous_fst.add continuous_snd)))))
    refine (hint_outer 0).mono' (hcont_rhs.aestronglyMeasurable.integral_prod_right')
      (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) fun u hu => ?_)
    rw [Real.norm_eq_abs]
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
    refine MeasureTheory.setIntegral_mono_on (hrhs_inner u hu).abs (hint_inner 0 u hu) measurableSet_Ioi fun v hv => ?_
    have h1 : |riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * Real.cos (γ * (u - v)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * Real.cos (γ * (u + v)))| ≤
        riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * 1 + (u - v) ^ 2 * Real.cosh (σ * (u - v)) * 1) := by
      rw [abs_mul, abs_of_pos (mul_pos (riemannPhi_pos u) (riemannPhi_pos v))]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (mul_pos (riemannPhi_pos u) (riemannPhi_pos v)))
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))]
        exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))
      · rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))]
        exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _)))
    simpa [pow_zero] using h1
  refine MeasureTheory.setIntegral_mono_on houter_pack.1 hrhs_outer measurableSet_Ioi fun u hu => ?_
  have hinner_pack := hsum_int (N := 2 * m + 2)
    (F := fun k v => ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) *
      (riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))))
    (fun k _ => (hint_inner k u hu).const_mul _)
  have hsum_inner :
      ∑ k ∈ Finset.range (2 * m + 2),
        ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ), riemannPhi u * riemannPhi v *
            ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
             (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))) =
      ∫ v in Ioi (0 : ℝ),
        ∑ k ∈ Finset.range (2 * m + 2),
          ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) *
            (riemannPhi u * riemannPhi v *
              ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
               (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))) := by
    rw [hinner_pack.2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← MeasureTheory.integral_const_mul]
  rw [hsum_inner]
  refine MeasureTheory.setIntegral_mono_on hinner_pack.1 (hrhs_inner u hu) measurableSet_Ioi fun v _ => ?_
  have hcos1 := cos_ge_even_taylor_all_order m (γ * (u - v))
  have hcos2 := cos_ge_even_taylor_all_order m (γ * (u + v))
  have hrearr :
      ∑ k ∈ Finset.range (2 * m + 2),
        ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) *
          (riemannPhi u * riemannPhi v *
            ((u + v) ^ 2 * Real.cosh (σ * (u + v)) * (u - v) ^ (2 * k) +
             (u - v) ^ 2 * Real.cosh (σ * (u - v)) * (u + v) ^ (2 * k))) =
      riemannPhi u * riemannPhi v *
        ((u + v) ^ 2 * Real.cosh (σ * (u + v)) *
          (∑ k ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ k * (γ * (u - v)) ^ (2 * k) / ((2 * k).factorial : ℝ)) +
         (u - v) ^ 2 * Real.cosh (σ * (u - v)) *
          (∑ k ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ k * (γ * (u + v)) ^ (2 * k) / ((2 * k).factorial : ℝ))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, mul_pow]; ring
  rw [hrearr]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (mul_pos (riemannPhi_pos u) (riemannPhi_pos v)))
  exact add_le_add
    (mul_le_mul_of_nonneg_left hcos1 (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))))
    (mul_le_mul_of_nonneg_left hcos2 (mul_nonneg (sq_nonneg _) (le_of_lt (Real.cosh_pos _))))

/-- THEOREM II.3 (COROLLARY — LOCAL RH & STRICT ZERO SIMPLICITY FROM ALL-ORDER MOMENT POLYNOMIAL):
    For ANY order `m : ℕ` and ANY height `Γ > 0`, if the degree-`(4m+2)` alternating-cosine
    light-cone moment polynomial is strictly positive on `[0, 1/2] × [-Γ, Γ]`, then:
    (1) Every zero of `riemannZeta` in the strip `(0, 1) × [-Γ, Γ]` lies on `Re(s) = 1/2` (Local RH);
    (2) Every critical-line zero `γ ∈ [-Γ, Γ]` of `Ξ(γ) = 0` is STRICTLY SIMPLE (`deriv Ξ γ ≠ 0`)! -/
theorem riemannHypothesis_local_and_simple_of_all_order_poly_pos (m : ℕ) {Γ : ℝ}
    (hpoly : ∀ σ γ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 → |γ| ≤ Γ →
      0 < ∑ k ∈ Finset.range (2 * m + 2),
        ((-1 : ℝ) ^ k * γ ^ (2 * k) / ((2 * k).factorial : ℝ)) * lightConeMoment2D k σ) :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ Γ → riemannZeta s = 0 → s.re = 1 / 2) ∧
    (∀ γ : ℝ, |γ| ≤ Γ → xiCritical γ = 0 → deriv xiCritical γ ≠ 0) := by
  exact riemannHypothesis_local_and_simple_of_hessianPos (Γ := Γ) fun σ γ hσ0 hσ1 hγ =>
    lt_of_lt_of_le (mul_pos (by norm_num) (hpoly σ γ hσ0 hσ1 hγ))
      (xiNormSq_deriv2_ge_all_order_moment_poly m σ γ)

/-- THEOREM II.4 (UNCONDITIONAL OPEN CRITICAL-STRIP COLLAR FOR EVERY HEIGHT `T > 0`!):
    Building directly on Module #20's COMPLETE closure of the exact critical-strip boundary
    `Re(s) = 1` (`σ = 1/2`), compactness of `[-T, T]` yields an explicit open collar width
    `δ ∈ (0, 1/2)` STRICTLY INSIDE THE OPEN CRITICAL STRIP `0 < σ < 1/2` for EVERY height `T > 0`:
    For EVERY `σ ∈ [1/2 - δ, ∞)` and EVERY `γ ∈ [-T, T]`:
      (1) `0 < (xiResolvent (γ + iσ)).im` (Herglotz positivity strictly inside the critical strip!),
      (2) `0 < deriv (fun s => xiNormSq s γ) σ` (positive radial force strictly inside the strip!),
      (3) `riemannZeta (1/2 + σ + iγ) ≠ 0` AND `riemannZeta (1/2 - σ + iγ) ≠ 0`
          (BOTH outer collars `(0, δ] ∪ [1 - δ, 1)` are zero-free up to height `T`!). -/
theorem criticalStrip_unconditional_open_collar_for_every_height (T : ℝ) (_hT : 0 < T) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ σ γ : ℝ, 1 / 2 - δ ≤ σ → |γ| ≤ T →
        0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
        0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
        (σ < 1 / 2 → riemannZeta (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 ∧
          riemannZeta (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0) := by
  -- Step 1: On the compact segment `K = {γ + i/2 | γ ∈ [-T, T]}`, both `riemannXi (1/2 - I*z) ≠ 0`
  -- and `0 < (xiResolvent z).im` hold everywhere (by Module #20 Theorem II.5!).
  set K : Set ℂ := (fun γ : ℝ => (γ : ℂ) + Complex.I * ((1 / 2 : ℝ) : ℂ)) '' Icc (-T) T
  have hK_comp : IsCompact K :=
    isCompact_Icc.image (Complex.continuous_ofReal.add continuous_const)
  -- Open set `U = {z : ℂ | riemannXi (1/2 - I*z) ≠ 0 ∧ 0 < (xiResolvent z).im}`
  set U : Set ℂ := {z : ℂ | riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0 ∧ 0 < (xiResolvent z).im}
  have hU_open : IsOpen U := by
    have hcont_xi : Continuous (fun z : ℂ => riemannXi ((1 / 2 : ℂ) - Complex.I * z)) :=
      riemannXi_entire.continuous.comp (continuous_const.sub (continuous_const.mul continuous_id))
    have hO1 : IsOpen {z : ℂ | riemannXi ((1 / 2 : ℂ) - Complex.I * z) ≠ 0} :=
      isOpen_ne_fun hcont_xi continuous_const
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hz1 : z ∈ {w : ℂ | riemannXi ((1 / 2 : ℂ) - Complex.I * w) ≠ 0} := hz.1
    have hcont_res : ContinuousAt (fun w : ℂ => (xiResolvent w).im) z := by
      have hmap : Differentiable ℂ (fun w : ℂ => (1 / 2 : ℂ) - Complex.I * w) :=
        (differentiable_const _).sub ((differentiable_const _).mul differentiable_id)
      have hres_diff : DifferentiableAt ℂ xiResolvent z := by
        unfold xiResolvent
        exact (differentiableAt_const _).mul
          (((differentiable_deriv_riemannXi.comp hmap).differentiableAt).div
            ((riemannXi_entire.comp hmap).differentiableAt) hz.1)
      exact Complex.continuous_im.continuousAt.comp hres_diff.continuousAt
    have hnhds1 : {w : ℂ | riemannXi ((1 / 2 : ℂ) - Complex.I * w) ≠ 0} ∈ 𝓝 z := hO1.mem_nhds hz1
    have hnhds2 : {w : ℂ | 0 < (xiResolvent w).im} ∈ 𝓝 z :=
      hcont_res.preimage_mem_nhds (isOpen_Ioi.mem_nhds (show (xiResolvent z).im ∈ Ioi (0 : ℝ) from hz.2))
    exact Filter.inter_mem hnhds1 hnhds2
  have hK_sub_U : K ⊆ U := by
    rintro _ ⟨γ, _, rfl⟩
    have hre1 : (1 : ℝ) ≤ ((1 / 2 : ℂ) - Complex.I * ((γ : ℂ) + Complex.I * ((1 / 2 : ℝ) : ℂ))).re := by
      simp; norm_num
    exact ⟨riemannXi_ne_zero_of_one_le_re hre1,
      (xiResolvent_herglotz_global_complete_outer_halfPlane_half.1 (1 / 2) γ le_rfl).1⟩
  -- Step 2: By compactness of `K ⊆ U`, obtain uniform metric thickening `r > 0`!
  rcases hK_comp.exists_thickening_subset_open hU_open hK_sub_U with ⟨r, hr_pos, hr_sub⟩
  set δ : ℝ := min (r / 2) (1 / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_lt : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨δ, hδ_pos, hδ_lt, fun σ γ hσ hγ => ?_⟩
  by_cases hge : 1 / 2 ≤ σ
  · have hout := xiResolvent_herglotz_global_complete_outer_halfPlane_half.1 σ γ hge
    exact ⟨hout.1, hout.2.1, fun hcontra => False.elim (by linarith)⟩
  · push Not at hge
    set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
    set z0 : ℂ := (γ : ℂ) + Complex.I * ((1 / 2 : ℝ) : ℂ)
    have hz0_K : z0 ∈ K := ⟨γ, abs_le.mp hγ, rfl⟩
    have hdist : dist z z0 < r := by
      rw [dist_eq_norm]
      have hsub : z - z0 = Complex.I * (((σ - 1 / 2 : ℝ) : ℂ)) := by
        dsimp [z, z0]; push_cast; ring
      rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_neg (by linarith)]
      have hδ_le : δ ≤ r / 2 := min_le_left _ _
      linarith
    have hz_U : z ∈ U := hr_sub (Metric.mem_thickening_iff.mpr ⟨z0, hz0_K, hdist⟩)
    have hxi_ne : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
      have harg : ((1 / 2 : ℂ) - Complex.I * z) = ((1 / 2 + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ) := by
        dsimp [z]; exact Complex.ext (by simp) (by simp)
      have hne_conj : riemannXi (((1 / 2 + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ)) ≠ 0 := by
        rw [← harg]; exact hz_U.1
      intro h0
      have hconj := riemannXi_conj (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ))
      rw [h0, map_zero] at hconj
      have hstar : starRingEnd ℂ (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) =
          ((1 / 2 + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ) := by
        apply Complex.ext <;> simp
      rw [hstar] at hconj
      exact hne_conj hconj
    have hV_pos : 0 < xiNormSq σ γ := by
      dsimp [xiNormSq]
      have harg : (⟨1 / 2 + σ, γ⟩ : ℂ) = ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
        apply Complex.ext <;> simp
      rw [harg]; exact sq_pos_of_pos (norm_pos_iff.mpr hxi_ne)
    have hlogF := xiResolvent_im_eq_logForce_half hxi_ne
    have hLF_pos : 0 < xiLogForce σ γ := by linarith [hlogF.2, hz_U.2]
    have hF_pos : 0 < deriv (fun s : ℝ => xiNormSq s γ) σ := by
      rw [xiLogForce_eq_force_div_normSq hV_pos] at hLF_pos
      exact (div_pos_iff_of_pos_right hV_pos).mp hLF_pos
    refine ⟨hz_U.2, hF_pos, fun hσ_lt => ?_⟩
    have hσ_pos : 0 < σ := by linarith
    have hζ_plus : riemannZeta (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
      intro h0
      have h1 : (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
        intro hz0; have := congrArg Complex.re hz0; simp at this; linarith
      have h2 : (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 1 := by
        intro hz1; have := congrArg Complex.re hz1; simp at this; linarith
      have hG_ne : Gammaℝ (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 :=
        Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
      have hxi0 : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) = 0 := by
        rw [riemannXi_eq_completedRiemannZeta h1 h2,
            show completedRiemannZeta (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) =
              riemannZeta (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
                Gammaℝ (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) by
              rw [riemannZeta_def_of_ne_zero h1, div_mul_cancel₀ _ hG_ne], h0]
        ring
      exact hxi_ne hxi0
    have hζ_minus : riemannZeta (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
      intro h0
      have h1 : (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 := by
        intro hz0; have := congrArg Complex.re hz0; simp at this; linarith
      have h2 : (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 1 := by
        intro hz1; have := congrArg Complex.re hz1; simp at this; linarith
      have hG_ne : Gammaℝ (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 :=
        Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
      have hxi0 : riemannXi (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) = 0 := by
        rw [riemannXi_eq_completedRiemannZeta h1 h2,
            show completedRiemannZeta (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) =
              riemannZeta (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
                Gammaℝ (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) by
              rw [riemannZeta_def_of_ne_zero h1, div_mul_cancel₀ _ hG_ne], h0]
        ring
      have hsym := riemannXi_one_sub (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ))
      rw [hxi0] at hsym
      have hconj := riemannXi_conj (1 - (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)))
      rw [hsym, map_zero] at hconj
      have hstar : starRingEnd ℂ (1 - (((1 / 2 - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ))) =
          ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
        apply Complex.ext
        · simp; ring
        · simp
      rw [hstar] at hconj
      exact hxi_ne hconj
    exact ⟨hζ_plus, hζ_minus⟩

/-- THEOREM II.5 (EXACT HERMITE-BIEHLER ZERO-FREE BICONDITIONAL FOR `RiemannHypothesis`):
    Mathlib4's official `RiemannHypothesis` holds IF AND ONLY IF for every `α > 0` and every
    `z : ℂ` with `0 ≤ z.im`, `xiShiftE α z ≠ 0`! -/
theorem xiShiftE_zeroFree_uhp_iff_riemannHypothesis :
    (∀ α : ℝ, 0 < α → ∀ z : ℂ, 0 ≤ z.im → xiShiftE α z ≠ 0) ↔ RiemannHypothesis := by
  constructor
  · intro hfree s hζ htriv hne1
    by_contra hne_half
    have hre_pos : 0 < s.re := by
      by_contra hle; push Not at hle
      have h1 : 1 ≤ (1 - s).re := by simp; linarith
      have hne0 : s ≠ 0 := by
        intro h0; rw [h0, riemannZeta_zero] at hζ; norm_num at hζ
      have h0lt : 0 < s.re := by
        by_contra hle'
        have hxi_ne : riemannXi (1 - s) ≠ 0 := riemannXi_ne_zero_of_one_le_re h1
        have hxi_s : riemannXi s ≠ 0 := by rw [← riemannXi_one_sub s]; exact hxi_ne
        by_cases hGs : Gammaℝ s = 0
        · rw [Gammaℝ_def, mul_eq_zero] at hGs
          rcases hGs with hpi | hgam
          · exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)))) hpi
          · rw [Complex.Gamma_eq_zero_iff] at hgam
            rcases hgam with ⟨n, hn⟩
            cases n with
            | zero =>
              have hs0 : s = 0 := by linear_combination 2 * hn
              exact hne0 hs0
            | succ k =>
              apply htriv
              push_cast at hn
              exact ⟨k, by linear_combination 2 * hn⟩
        · have h0 : riemannXi s = 0 := by
            rw [riemannXi_eq_completedRiemannZeta hne0 hne1,
                show completedRiemannZeta s = riemannZeta s * Gammaℝ s by
                  rw [riemannZeta_def_of_ne_zero hne0, div_mul_cancel₀ _ hGs], hζ]; ring
          exact hxi_s h0
      linarith
    have hre_lt1 : s.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hζ
    -- By symmetry `s` or `1 - s` has `re > 1/2`!
    have hgt_half : ∃ w : ℂ, 1 / 2 < w.re ∧ w.re < 1 ∧ riemannXi w = 0 := by
      have hne0 : s ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre_pos; linarith
      have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre_pos
      have hxi0 : riemannXi s = 0 := by
        rw [riemannXi_eq_completedRiemannZeta hne0 hne1,
            show completedRiemannZeta s = riemannZeta s * Gammaℝ s by
              rw [riemannZeta_def_of_ne_zero hne0, div_mul_cancel₀ _ hG_ne], hζ]; ring
      rcases lt_or_gt_of_ne hne_half with hlt | hgt
      · refine ⟨1 - s, by simp; linarith, by simp; linarith, ?_⟩
        rw [riemannXi_one_sub]; exact hxi0
      · exact ⟨s, hgt, hre_lt1, hxi0⟩
    rcases hgt_half with ⟨w, hw_gt, _, hw_xi⟩
    -- Set `α = w.re - 1/2 > 0` and `z = -w.im : ℂ` (on `ℝ`, `z.im = 0`)!
    have hne := hfree (w.re - 1 / 2) (by linarith) ((-w.im : ℝ) : ℂ) (by simp)
    apply hne
    dsimp [xiShiftE]
    have harg : ((1 / 2 + (w.re - 1 / 2) : ℝ) : ℂ) - Complex.I * ((-w.im : ℝ) : ℂ) = w := by
      apply Complex.ext <;> simp
    rw [harg]; exact hw_xi
  · intro hRH α hα z hz h0
    dsimp [xiShiftE] at h0
    set s : ℂ := ((1 / 2 + α : ℝ) : ℂ) - Complex.I * z
    have hs_re : 1 / 2 < s.re := by dsimp [s]; simp; linarith
    by_cases hs1 : 1 ≤ s.re
    · exact riemannXi_ne_zero_of_one_le_re hs1 h0
    · push Not at hs1
      have hs_ne0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; linarith
      have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; linarith
      have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
      rw [riemannXi_eq_completedRiemannZeta hs_ne0 hs_ne1] at h0
      have hcomp0 : completedRiemannZeta s = 0 := by
        have h1 : (1 / 2 : ℂ) ≠ 0 := by norm_num
        have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne1
        have hmul : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := mul_ne_zero (mul_ne_zero h1 hs_ne0) h2
        exact (mul_eq_zero.mp h0).resolve_left hmul
      have hζ0 : riemannZeta s = 0 := by
        rw [riemannZeta_def_of_ne_zero hs_ne0, hcomp0, zero_div]
      have hntriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, hn⟩
        have hre := congrArg Complex.re hn
        simp at hre; linarith
      have hhalf := hRH s hζ0 hntriv hs_ne1
      linarith

end CriticalStripCollarAllOrderConvexityAndSchurGram
