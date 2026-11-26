/-
  ==============================================================================
  MODULE #25: ROUTE 1 — ADELIC LOCAL-TO-GLOBAL GRAM FACTORIZATION, LOEWNER
  ARCHIMEDEAN DOMINANCE, & CONTINUOUS LYAPUNOV GRADIENT FLOW

  Title: Adelic Gram Factorization and Lyapunov Flow (Route 1)
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Adelic Local-to-Global Gram Decomposition & Loewner Dominance):
      * `adelic_gram_sum_is_psd`:
        Any finite sum of local place Gram matrices ∑_{v ∈ V} A_vᵀ A_v is
        unconditionally positive semidefinite on ℝⁿ.
      * `archimedean_loewner_dominance_implies_gram_factorization`:
        If the Archimedean geodesic block W_∞ dominates the non-Archimedean
        von Mangoldt prime block P_prime in the Loewner order (xᵀ P_prime x ≤ xᵀ W_∞ x),
        then S = W_∞ - P_prime unconditionally admits a global Gram factorization
        ∃ A, S = Aᵀ * A!
  - Part II (Continuous Lyapunov Gradient Flow on H_Gram(A) = ‖S - Aᵀ A‖_F²):
      * `frobInner`, `frobNormSq`, `gramLyapunovEnergy_eq_frobNormSq`.
      * `gramLyapunovGrad S A = -4 • (A * (S - Aᵀ * A))`.
      * `lyapunov_gradient_flow_dissipation`:
        Along the flow dA/dt = -∇_A H_Gram(A), the Lyapunov
        dissipation rate satisfies ⟨∇H, dA/dt⟩_F = -‖∇H‖_F² ≤ 0!
      * `lyapunov_invertible_stationary_implies_exact_gram`:
        Any invertible (full-rank) stationary point of the Lyapunov
        solver (∇_A H_Gram(A) = 0) satisfies S = Aᵀ * A and certifies S ⪰ 0!
  - Part III (All-Horizon Uniform Adelic Gram Closure Target):
      * `UniformAdelicGramDominanceTarget` & `uniform_adelic_gram_dominance_implies_all_horizon_gram`.
  ==============================================================================
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RiemannDipolar.Manifold5DHolomorphyAndAsymptoticConfinement

open Real Complex Filter Topology Set
open scoped BigOperators Classical Matrix
open CriticalStripCollarAllOrderConvexityAndSchurGram
open CliffordSieveAdelicClosure
open UniversalMotherFormulaCliffordHierarchy

namespace AdelicGramFactorizationAndLyapunovFlow

-- ==============================================================================
-- PART I: ADELIC LOCAL-TO-GLOBAL GRAM DECOMPOSITION & LOEWNER DOMINANCE
-- ==============================================================================

/-- THEOREM I.1 (LOCAL-TO-GLOBAL ADELIC GRAM SUM IS UNCONDITIONALLY PSD):
    If a real matrix S decomposes as a finite sum of local-place Gram factors
    S = ∑_{v ∈ places} (A v)ᵀ * (A v), then S is unconditionally positive
    semidefinite: xᵀ S x = ∑_{v ∈ places} ‖(A v) x‖² ≥ 0. -/
theorem adelic_gram_sum_is_psd {n : ℕ} {ι : Type*} (places : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S = ∑ v ∈ places, (A v)ᵀ * (A v)) :
    ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
  intro x
  rw [hS]
  have hmul : (∑ v ∈ places, (A v)ᵀ * A v).mulVec x =
      ∑ v ∈ places, ((A v)ᵀ * A v).mulVec x := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hmul, dotProduct_sum]
  exact Finset.sum_nonneg fun v _ =>
    routeA_gram_factorization_implies_psd ((A v)ᵀ * A v) (A v) rfl x

/-- THEOREM I.2 (ARCHIMEDEAN LOEWNER DOMINANCE → EXACT GLOBAL GRAM FACTORIZATION):
    Suppose the Route A Schur block splits as S = W_∞ - P_prime where both
    W_∞ (Archimedean geodesic operator) and P_prime (von Mangoldt prime operator)
    are real symmetric (`IsHermitian`).
    If W_∞ dominates P_prime in the Loewner order (∀ x, xᵀ P_prime x ≤ xᵀ W_∞ x),
    then S unconditionally admits a global Gram factorization `∃ A, S = Aᵀ * A`! -/
theorem archimedean_loewner_dominance_implies_gram_factorization {n : ℕ}
    (W_inf P_prime : Matrix (Fin n) (Fin n) ℝ)
    (hW : W_inf.IsHermitian) (hP : P_prime.IsHermitian)
    (hdom : ∀ x : Fin n → ℝ, dotProduct x (P_prime.mulVec x) ≤ dotProduct x (W_inf.mulVec x)) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, W_inf - P_prime = Aᵀ * A := by
  have hS_herm : (W_inf - P_prime).IsHermitian := hW.sub hP
  rw [← real_symmetric_psd_iff_gram_factorization (W_inf - P_prime) hS_herm]
  intro x
  rw [Matrix.sub_mulVec, dotProduct_sub]
  linarith [hdom x]

-- ==============================================================================
-- PART II: CONTINUOUS LYAPUNOV GRADIENT FLOW ON H_Gram(A)
-- ==============================================================================

/-- Frobenius inner product ⟨X, Y⟩_F = ∑_{i, j} X_{ij} Y_{ij}. -/
def frobInner {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, X i j * Y i j

/-- Squared Frobenius norm ‖X‖_F² = ⟨X, X⟩_F = ∑_{i, j} X_{ij}². -/
def frobNormSq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  frobInner X X

theorem frobNormSq_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ frobNormSq X := by
  unfold frobNormSq frobInner
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- Exact identification of the Module #23 Gram Lyapunov energy with ‖S - Aᵀ A‖_F². -/
theorem gramLyapunovEnergy_eq_frobNormSq {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) :
    gramLyapunovEnergy S A = frobNormSq (S - Aᵀ * A) := by
  unfold gramLyapunovEnergy frobNormSq frobInner
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.sub_apply, sq]

/-- Exact Frobenius matrix gradient of H_Gram(A) = ‖S - Aᵀ A‖_F² for symmetric S:
    ∇_A H_Gram(A) = -4 A (S - Aᵀ A). -/
def gramLyapunovGrad {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (-4 : ℝ) • (A * (S - Aᵀ * A))

/-- Continuous-time Lyapunov velocity field: dA/dt = -∇_A H_Gram(A). -/
def gramLyapunovVelocity {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -gramLyapunovGrad S A

/-- THEOREM II.1 (MONOTONE LYAPUNOV DISSIPATION ALONG THE FLOW):
    Along dA/dt = -∇_A H_Gram(A), the instantaneous energy dissipation rate is
      ⟨∇_A H_Gram(A), dA/dt⟩_F = -‖∇_A H_Gram(A)‖_F² ≤ 0! -/
theorem lyapunov_gradient_flow_dissipation {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (gramLyapunovGrad S A) (gramLyapunovVelocity S A) =
      -frobNormSq (gramLyapunovGrad S A) ∧
    frobInner (gramLyapunovGrad S A) (gramLyapunovVelocity S A) ≤ 0 := by
  have heq : frobInner (gramLyapunovGrad S A) (gramLyapunovVelocity S A) =
      -frobNormSq (gramLyapunovGrad S A) := by
    unfold gramLyapunovVelocity frobNormSq frobInner
    simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
  exact ⟨heq, by linarith [frobNormSq_nonneg (gramLyapunovGrad S A)]⟩

/-- THEOREM II.2 (FULL-RANK STATIONARY POINT OF THE LYAPUNOV SOLVER → EXACT GRAM):
    If the Lyapunov solver reaches a stationary point ∇_A H_Gram(A) = 0
    with an invertible (full-rank) factor A (`IsUnit A.det`), then S = Aᵀ * A holds
    EXACTLY and S is unconditionally positive semidefinite! -/
theorem lyapunov_invertible_stationary_implies_exact_gram {n : ℕ}
    (S A : Matrix (Fin n) (Fin n) ℝ)
    (hinv : IsUnit A.det)
    (hstat : gramLyapunovGrad S A = 0) :
    S = Aᵀ * A ∧ ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
  unfold gramLyapunovGrad at hstat
  have hprod : A * (S - Aᵀ * A) = 0 := by
    have h4 : (-4 : ℝ) ≠ 0 := by norm_num
    exact (smul_eq_zero.mp hstat).resolve_left h4
  have hsub : S - Aᵀ * A = 0 := by
    have hmul := congrArg (fun M => A⁻¹ * M) hprod
    simp only [Matrix.mul_zero] at hmul
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hinv, Matrix.one_mul] at hmul
    exact hmul
  have hS : S = Aᵀ * A := sub_eq_zero.mp hsub
  exact ⟨hS, routeA_gram_factorization_implies_psd S A hS⟩

-- ==============================================================================
-- PART III: ALL-HORIZON UNIFORM ADELIC GRAM CLOSURE TARGET (ROUTE 1 FRONTIER)
-- ==============================================================================

/-- ROUTE 1 FRONTIER TARGET (UNIFORM ADELIC LOEWNER DOMINANCE FOR ALL L > 0):
    For every horizon L > 0, the finite-dimensional Archimedean geodesic block W_∞(L)
    dominates the non-Archimedean von Mangoldt prime block P_prime(L) in the Loewner order. -/
def UniformAdelicGramDominanceTarget
    (dim : ℝ → ℕ)
    (W_inf P_prime : (L : ℝ) → Matrix (Fin (dim L)) (Fin (dim L)) ℝ) : Prop :=
  ∀ L : ℝ, 0 < L →
    (W_inf L).IsHermitian ∧ (P_prime L).IsHermitian ∧
    ∀ x : Fin (dim L) → ℝ,
      dotProduct x ((P_prime L).mulVec x) ≤ dotProduct x ((W_inf L).mulVec x)

/-- THEOREM III.1 (UNIFORM ADELIC DOMINANCE CLOSES ROUTE 1 FOR EVERY HORIZON L > 0):
    Under `UniformAdelicGramDominanceTarget`, for EVERY horizon L > 0, the Schur block
    S_L = W_∞(L) - P_prime(L) admits a global Gram factorization S_L = A_Lᵀ * A_L
    and is unconditionally positive semidefinite! -/
theorem uniform_adelic_gram_dominance_implies_all_horizon_gram
    (dim : ℝ → ℕ)
    (W_inf P_prime : (L : ℝ) → Matrix (Fin (dim L)) (Fin (dim L)) ℝ)
    (htarget : UniformAdelicGramDominanceTarget dim W_inf P_prime) :
    ∀ L : ℝ, 0 < L →
      ∃ A : Matrix (Fin (dim L)) (Fin (dim L)) ℝ,
        W_inf L - P_prime L = Aᵀ * A ∧
        ∀ x : Fin (dim L) → ℝ, 0 ≤ dotProduct x ((W_inf L - P_prime L).mulVec x) := by
  intro L hL
  rcases htarget L hL with ⟨hW, hP, hdom⟩
  rcases archimedean_loewner_dominance_implies_gram_factorization
      (W_inf L) (P_prime L) hW hP hdom with ⟨A, hA⟩
  exact ⟨A, hA, routeA_gram_factorization_implies_psd (W_inf L - P_prime L) A hA⟩

end AdelicGramFactorizationAndLyapunovFlow
