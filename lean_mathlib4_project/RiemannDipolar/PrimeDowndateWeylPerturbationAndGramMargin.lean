/-
  ==============================================================================
  MODULE #28: ALGEBRAIC PRIME-POWER GRAM DOWNDATE, WEYL PERTURBATION MARGIN,
  & ACCUMULATED CHEBYSHEV–VON MANGOLDT GRAM PRESERVATION (ROUTE 1)

  Title: Prime Downdate, Weyl Perturbation Margin, and Gram Preservation
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - `vecNormSq x = dotProduct x x`: Squared Euclidean norm on ℝⁿ.
  - `quadraticForm_downdate_lower_bound`:
    If `∀ x, μ * ‖x‖² ≤ xᵀ S x` and `∀ x, xᵀ P x ≤ δ * ‖x‖²`, then
    `∀ x, (μ - δ) * ‖x‖² ≤ xᵀ (S - P) x`.
  - `prime_downdate_preserves_gram_factorization`:
    If `S, P` are real symmetric and `δ ≤ μ`, then `S - P` unconditionally
    admits a global Gram factorization `∃ A, S - P = Aᵀ * A`!
  - `accumulated_prime_downdates_preserve_gram`:
    For ANY finite set of prime powers `F` with weights `c : ι → ℝ` (`c v ≥ 0`)
    and per-prime bounds `δ : ι → ℝ`, if `∑ v ∈ F, c v * δ v ≤ μ_inf`, then
    `W_inf - ∑ v ∈ F, c v • C v` unconditionally admits a global Gram
    factorization `∃ A, W_inf - ∑ v ∈ F, c v • C v = Aᵀ * A`!
  ==============================================================================
-/

import RiemannDipolar.ArbitraryDimCholeskySchurInduction

open Real Complex Filter Topology Set
open scoped BigOperators Classical Matrix
open CriticalStripCollarAllOrderConvexityAndSchurGram
open CliffordSieveAdelicClosure
open UniversalMotherFormulaCliffordHierarchy
open AdelicGramFactorizationAndLyapunovFlow

namespace PrimeDowndateWeylPerturbationAndGramMargin

/-- Squared Euclidean norm on ℝⁿ: ‖x‖² = xᵀ x. -/
def vecNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  dotProduct x x

theorem vecNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vecNormSq x := by
  unfold vecNormSq dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- THEOREM I.1 (WEYL QUADRATIC-FORM DOWNDATE LOWER BOUND):
    Subtracting a perturbation P with upper quadratic bound δ from an operator S
    with lower spectral margin μ preserves a lower margin of at least μ - δ. -/
theorem quadraticForm_downdate_lower_bound {n : ℕ}
    (S P : Matrix (Fin n) (Fin n) ℝ) (μ δ : ℝ)
    (hS : ∀ x : Fin n → ℝ, μ * vecNormSq x ≤ dotProduct x (S.mulVec x))
    (hP : ∀ x : Fin n → ℝ, dotProduct x (P.mulVec x) ≤ δ * vecNormSq x) :
    ∀ x : Fin n → ℝ, (μ - δ) * vecNormSq x ≤ dotProduct x ((S - P).mulVec x) := by
  intro x
  rw [Matrix.sub_mulVec, dotProduct_sub]
  linarith [hS x, hP x]

/-- THEOREM I.2 (SINGLE PRIME-POWER DOWNDATE PRESERVES GLOBAL GRAM FACTORIZATION):
    If S and P are real symmetric and δ ≤ μ, then S - P is unconditionally PSD
    and admits a global Gram factorization `∃ A, S - P = Aᵀ * A`. -/
theorem prime_downdate_preserves_gram_factorization {n : ℕ}
    (S P : Matrix (Fin n) (Fin n) ℝ) (μ δ : ℝ)
    (hSh : S.IsHermitian) (hPh : P.IsHermitian)
    (hS : ∀ x : Fin n → ℝ, μ * vecNormSq x ≤ dotProduct x (S.mulVec x))
    (hP : ∀ x : Fin n → ℝ, dotProduct x (P.mulVec x) ≤ δ * vecNormSq x)
    (hmargin : δ ≤ μ) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, S - P = Aᵀ * A := by
  have hsub : (S - P).IsHermitian := hSh.sub hPh
  rw [← real_symmetric_psd_iff_gram_factorization (S - P) hsub]
  intro x
  have hlow := quadraticForm_downdate_lower_bound S P μ δ hS hP x
  have hnn : 0 ≤ (μ - δ) * vecNormSq x :=
    mul_nonneg (sub_nonneg.mpr hmargin) (vecNormSq_nonneg x)
  linarith

/-- THEOREM I.3 (ACCUMULATED CHEBYSHEV–VON MANGOLDT DOWNDATES PRESERVE GRAM):
    For ANY finite set `F` of prime powers with nonnegative weights `c v ≥ 0`,
    symmetric autocorrelation matrices `C v`, and per-prime upper bounds `δ v`,
    if the Archimedean geodesic margin `μ_inf` dominates the accumulated sum
      `∑ v ∈ F, c v * δ v ≤ μ_inf`,
    then `S_L = W_inf - ∑ v ∈ F, c v • C v` unconditionally admits a global Gram
    factorization `∃ A, S_L = Aᵀ * A`! -/
theorem accumulated_prime_downdates_preserve_gram {n : ℕ} {ι : Type*}
    (F : Finset ι)
    (W_inf : Matrix (Fin n) (Fin n) ℝ)
    (c δ : ι → ℝ)
    (C : ι → Matrix (Fin n) (Fin n) ℝ)
    (μ_inf : ℝ)
    (hWh : W_inf.IsHermitian)
    (hCh : ∀ v ∈ F, (C v).IsHermitian)
    (hc : ∀ v ∈ F, 0 ≤ c v)
    (hW : ∀ x : Fin n → ℝ, μ_inf * vecNormSq x ≤ dotProduct x (W_inf.mulVec x))
    (hC : ∀ v ∈ F, ∀ x : Fin n → ℝ, dotProduct x ((C v).mulVec x) ≤ δ v * vecNormSq x)
    (hsum : ∑ v ∈ F, c v * δ v ≤ μ_inf) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      W_inf - (∑ v ∈ F, c v • C v) = Aᵀ * A := by
  let P := ∑ v ∈ F, c v • C v
  have hPh : P.IsHermitian := by
    dsimp only [P]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Matrix.conjTranspose_smul, star_trivial, (hCh v hv).eq]
  have hP : ∀ x : Fin n → ℝ, dotProduct x (P.mulVec x) ≤ (∑ v ∈ F, c v * δ v) * vecNormSq x := by
    intro x
    dsimp only [P]
    have hmul : (∑ v ∈ F, c v • C v).mulVec x = ∑ v ∈ F, c v • (C v).mulVec x := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro v _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hmul, dotProduct_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro v hv
    rw [dotProduct_smul, smul_eq_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC v hv x) (hc v hv)
  exact prime_downdate_preserves_gram_factorization W_inf P μ_inf (∑ v ∈ F, c v * δ v)
    hWh hPh hW hP hsum

end PrimeDowndateWeylPerturbationAndGramMargin
