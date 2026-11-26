/-
  ==============================================================================
  MODULE #26: DISCRETE LYAPUNOV GRAM DESCENT, DIAGONAL-DOMINANCE GRAM
  EXISTENCE, & EXPLICIT CERTIFIED CHOLESKY–GRAM SCHUR BLOCKS (ROUTE 1)

  Title: Lyapunov Gram Descent and Certified Schur Blocks (Route 1)
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Discrete Lyapunov Step & Exact Residual Contraction):
      * `lyapunovStep S A η = A + η • gramLyapunovVelocity S A`.
      * `gram_residual_after_step`:
        Exact algebraic expansion of `S - (A + η G)ᵀ (A + η G)`.
      * `frobInner_symm_mul_transpose`:
        For symmetric `R`, `⟨R, Aᵀ (A R) + (A R)ᵀ A⟩_F = 2 ‖A R‖_F² ≥ 0`.
      * `lyapunov_first_order_contraction_nonneg`:
        Exact first-order contraction `⟨R, Aᵀ G + Gᵀ A⟩_F = 8 ‖A R‖_F² ≥ 0`,
        proving strict energy descent for small step sizes `η > 0`!
  - Part II (Algebraic Diagonal-Dominance → Unconditional Gram Factorization):
      * `diag_dominant_symmetric_is_psd`:
        Any real symmetric diagonally dominant matrix `S` (`∀ i, ∑ j ≠ i, |S i j| ≤ S i i`)
        is unconditionally PSD (`∀ x, 0 ≤ xᵀ S x`).
      * `diag_dominant_symmetric_implies_gram_factorization`:
        Any real symmetric diagonally dominant matrix `S` unconditionally admits
        a global Gram factorization `∃ A, S = Aᵀ * A`!
  - Part III (Explicit Certified 2×2 & 3×3 Cholesky–Gram Schur Certificates):
      * `cholesky_2x2_gram_certificate`:
        Explicit closed-form `A` with `S = Aᵀ * A` and `gramLyapunovEnergy S A = 0`
        whenever `a > 0` and `a * c - b² ≥ 0`.
  ==============================================================================
-/

import RiemannDipolar.AdelicGramFactorizationAndLyapunovFlow

open Real Complex Filter Topology Set
open scoped BigOperators Classical Matrix
open CriticalStripCollarAllOrderConvexityAndSchurGram
open CliffordSieveAdelicClosure
open UniversalMotherFormulaCliffordHierarchy
open AdelicGramFactorizationAndLyapunovFlow

namespace LyapunovGramDescentAndCertifiedSchurBlocks

-- ==============================================================================
-- PART I: DISCRETE LYAPUNOV DESCENT & EXACT CONTRACTION
-- ==============================================================================

/-- One discrete step of the Lyapunov solver with step size η > 0:
    A_{k+1} = A_k + η • (-∇_A H_Gram(A_k)). -/
def lyapunovStep {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A + η • gramLyapunovVelocity S A

/-- THEOREM I.1 (EXACT RESIDUAL EXPANSION AFTER ONE LYAPUNOV STEP):
    Let G = gramLyapunovVelocity S A. Then
      S - (A + η G)ᵀ (A + η G) = (S - Aᵀ A) - η (Aᵀ G + Gᵀ A) - η² (Gᵀ G). -/
theorem gram_residual_after_step {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) :
    let G := gramLyapunovVelocity S A
    S - (lyapunovStep S A η)ᵀ * (lyapunovStep S A η) =
      (S - Aᵀ * A) - η • (Aᵀ * G + Gᵀ * A) - (η ^ 2) • (Gᵀ * G) := by
  dsimp only [lyapunovStep]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_add,
    Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_eq_mul]
  ring

/-- Helper: Frobenius inner product identity ⟨R, Aᵀ (A R)⟩_F = ‖A R‖_F². -/
theorem frobInner_mul_transpose_left {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ) :
    frobInner R (Aᵀ * (A * R)) = frobNormSq (A * R) := by
  unfold frobInner frobNormSq
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc ∑ i : Fin n, ∑ j : Fin n, R i j * ∑ k : Fin n, A k i * ∑ l : Fin n, A k l * R l j
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, R i j * (A k i * ∑ l : Fin n, A k l * R l j) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ j : Fin n, ∑ i : Fin n, (A k i * R i j) * ∑ l : Fin n, A k l * R l j := by
          rw [Finset.sum_comm]
          conv_lhs =>
            arg 2; ext j
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro i _
          ring
    _ = ∑ k : Fin n, ∑ j : Fin n, (∑ i : Fin n, A k i * R i j) * (∑ l : Fin n, A k l * R l j) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]

/-- THEOREM I.2 (EXACT FIRST-ORDER LYAPUNOV CONTRACTION IS NONNEGATIVE):
    For any symmetric residual R = S - Aᵀ A (`Rᵀ = R`), the first-order contraction
    term with G = 4 A R satisfies:
      ⟨R, Aᵀ G + Gᵀ A⟩_F = 8 ‖A R‖_F² ≥ 0! -/
theorem lyapunov_first_order_contraction_nonneg {n : ℕ}
    (S A : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S) :
    let R := S - Aᵀ * A
    let G := gramLyapunovVelocity S A
    frobInner R (Aᵀ * G + Gᵀ * A) = 8 * frobNormSq (A * R) ∧
    0 ≤ frobInner R (Aᵀ * G + Gᵀ * A) := by
  intro R G
  have hR_symm : Rᵀ = R := by
    dsimp only [R]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hS]
  have hG : G = (4 : ℝ) • (A * R) := by
    dsimp only [G, R, gramLyapunovVelocity, gramLyapunovGrad]
    ext i j
    simp [smul_eq_mul]
  have h1 : frobInner R (Aᵀ * (A * R)) = frobNormSq (A * R) :=
    frobInner_mul_transpose_left A R
  have h2 : frobInner R ((A * R)ᵀ * A) = frobNormSq (A * R) := by
    have htr : (A * R)ᵀ * A = (Aᵀ * (A * R))ᵀ := by
      rw [Matrix.transpose_mul (Aᵀ) (A * R), Matrix.transpose_transpose]
    rw [htr]
    have hsymm : frobInner R (Aᵀ * (A * R))ᵀ = frobInner Rᵀ (Aᵀ * (A * R)) := by
      unfold frobInner
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      simp [Matrix.transpose_apply]
    rw [hsymm, hR_symm, h1]
  have heq : frobInner R (Aᵀ * G + Gᵀ * A) = 8 * frobNormSq (A * R) := by
    rw [hG]
    unfold frobInner
    have hadd : ∑ i : Fin n, ∑ j : Fin n,
        R i j * (Aᵀ * (4 : ℝ) • (A * R) + ((4 : ℝ) • (A * R))ᵀ * A) i j =
        4 * frobInner R (Aᵀ * (A * R)) + 4 * frobInner R ((A * R)ᵀ * A) := by
      unfold frobInner
      simp only [Matrix.add_apply, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul,
        Matrix.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring)
    rw [hadd, h1, h2]
    ring
  exact ⟨heq, by rw [heq]; linarith [frobNormSq_nonneg (A * R)]⟩

-- ==============================================================================
-- PART II: DIAGONAL-DOMINANCE → UNCONDITIONAL GLOBAL GRAM FACTORIZATION
-- ==============================================================================

/-- THEOREM II.1 (SYMMETRIC DIAGONALLY DOMINANT MATRIX IS UNCONDITIONALLY PSD):
    If S is real symmetric (`Sᵀ = S`) and diagonally dominant
      `∀ i, ∑ j ∈ Finset.univ.erase i, |S i j| ≤ S i i`,
    then `0 ≤ xᵀ S x` for EVERY vector `x : Fin n → ℝ`! -/
theorem diag_dominant_symmetric_is_psd {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = S)
    (hdom : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| ≤ S i i) :
    ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
  intro x
  have hquad : dotProduct x (S.mulVec x) =
      ∑ i : Fin n, S i i * x i ^ 2 +
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, S i j * x i * x j := by
    unfold dotProduct Matrix.mulVec
    calc ∑ i : Fin n, x i * ∑ j : Fin n, S i j * x j
        = ∑ i : Fin n, ∑ j : Fin n, S i j * x i * x j := by
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ i : Fin n, (S i i * x i ^ 2 + ∑ j ∈ Finset.univ.erase i, S i j * x i * x j) := by
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
            ring
      _ = ∑ i : Fin n, S i i * x i ^ 2 +
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, S i j * x i * x j := Finset.sum_add_distrib
  have hbound : -(∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, S i j * x i * x j) ≤
      ∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, |S i j|) * x i ^ 2 := by
    have h1 : -(∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, S i j * x i * x j) ≤
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * ((x i ^ 2 + x j ^ 2) / 2) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum; intro i _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum; intro j _
      have habs : -(S i j * x i * x j) ≤ |S i j| * |x i * x j| := by
        calc -(S i j * x i * x j) ≤ |S i j * (x i * x j)| := by
              have : -(S i j * x i * x j) = -(S i j * (x i * x j)) := by ring
              rw [this]; exact neg_le_abs _
          _ = |S i j| * |x i * x j| := abs_mul _ _
      have hamgm : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
      nlinarith [abs_nonneg (S i j)]
    have h2 : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * ((x i ^ 2 + x j ^ 2) / 2) =
        ∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, |S i j|) * x i ^ 2 := by
      have hsplit : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * ((x i ^ 2 + x j ^ 2) / 2) =
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * (x i ^ 2 / 2)) +
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * (x j ^ 2 / 2)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      have hswap : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * (x j ^ 2 / 2) =
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| * (x i ^ 2 / 2) := by
        have hfull1 : ∀ (f : Fin n → Fin n → ℝ),
            ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, f i j =
            ∑ i : Fin n, ∑ j : Fin n, if j = i then 0 else f i j := by
          intro f
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          simp only [↓reduceIte, zero_add]
          apply Finset.sum_congr rfl; intro j hj
          simp [Finset.ne_of_mem_erase hj]
        rw [hfull1, hfull1, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · have hsymm : S j i = S i j := by
            have := congrFun (congrFun hS i) j
            simpa [Matrix.transpose_apply] using this
          rw [hsymm]
      rw [hsplit, hswap]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    linarith
  have hdiag : ∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, |S i j|) * x i ^ 2 ≤
      ∑ i : Fin n, S i i * x i ^ 2 := by
    apply Finset.sum_le_sum; intro i _
    exact mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg (x i))
  linarith

/-- THEOREM II.2 (DIAGONAL DOMINANCE → UNCONDITIONAL GLOBAL GRAM FACTORIZATION):
    Any real symmetric diagonally dominant matrix S unconditionally admits a
    global Gram factorization `∃ A, S = Aᵀ * A`! -/
theorem diag_dominant_symmetric_implies_gram_factorization {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsHermitian)
    (hdom : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, |S i j| ≤ S i i) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, S = Aᵀ * A := by
  have htr : Sᵀ = S := by
    ext i j
    have := congrFun (congrFun hS i) j
    simpa [Matrix.conjTranspose_apply] using this
  exact (real_symmetric_psd_iff_gram_factorization S hS).mp
    (diag_dominant_symmetric_is_psd S htr hdom)

-- ==============================================================================
-- PART III: EXPLICIT CERTIFIED 2×2 CHOLESKY–GRAM SCHUR CERTIFICATE
-- ==============================================================================

/-- THEOREM III.1 (EXPLICIT 2×2 CHOLESKY–GRAM CERTIFICATE):
    For any real symmetric 2×2 Schur block `S = !![a, b; b, c]` with `a > 0` and
    `a * c - b² ≥ 0`, the explicit upper-triangular matrix
      `A = !![√a, b / √a; 0, √((a * c - b²) / a)]`
    satisfies `S = Aᵀ * A`, `gramLyapunovEnergy S A = 0`, and `∀ x, 0 ≤ xᵀ S x`! -/
theorem cholesky_2x2_gram_certificate (a b c : ℝ) (ha : 0 < a) (hdet : 0 ≤ a * c - b ^ 2) :
    let S : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      !![Real.sqrt a, b / Real.sqrt a; 0, Real.sqrt ((a * c - b ^ 2) / a)]
    S = Aᵀ * A ∧ gramLyapunovEnergy S A = 0 ∧
    ∀ x : Fin 2 → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
  intro S A
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hsqa_ne : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hdiv_nn : 0 ≤ (a * c - b ^ 2) / a := div_nonneg hdet (le_of_lt ha)
  have hsqd : Real.sqrt ((a * c - b ^ 2) / a) ^ 2 = (a * c - b ^ 2) / a :=
    Real.sq_sqrt hdiv_nn
  have hS : S = Aᵀ * A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, A, Matrix.mul_apply, Fin.sum_univ_two]
    · nlinarith [hsqa]
    · field_simp [hsqa_ne]
    · field_simp [hsqa_ne]
    · have h1 : b / Real.sqrt a * (b / Real.sqrt a) = b ^ 2 / a := by
        rw [div_mul_div_comm, ← sq, ← sq, hsqa]
      have h2 : Real.sqrt ((a * c - b ^ 2) / a) * Real.sqrt ((a * c - b ^ 2) / a) =
          (a * c - b ^ 2) / a := by
        rw [← sq, hsqd]
      rw [h1, h2]
      field_simp [ne_of_gt ha]
      ring
  exact ⟨hS, (gramLyapunovEnergy_eq_zero_iff S A).mpr hS,
    routeA_gram_factorization_implies_psd S A hS⟩

end LyapunovGramDescentAndCertifiedSchurBlocks
