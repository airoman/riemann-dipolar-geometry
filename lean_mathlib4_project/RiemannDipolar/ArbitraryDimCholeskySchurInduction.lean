/-
  ==============================================================================
  MODULE #27: ARBITRARY-DIMENSION n × n BLOCK-SCHUR / CHOLESKY–GRAM INDUCTION
  CERTIFICATE FOR ROUTE 1 (ALL FINITE DIMENSIONS n ∈ ℕ)

  Title: Arbitrary-Dimension Block-Schur Cholesky–Gram Certification
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - `blockMatrix a b C`: Symmetric (n+1)×(n+1) block matrix with top-left `a : ℝ`,
    border `b : Fin n → ℝ`, and bottom-right `C : Matrix (Fin n) (Fin n) ℝ`.
  - `schurComplement a b C`: Exact n×n Schur complement `C - (1 / a) • (b ⊗ b)`.
  - `choleskyLift a b A_n`: Explicit upper-triangular (n+1)×(n+1) Gram lift of `A_n`.
  - `block_schur_cholesky_gram_induction`:
    For EVERY dimension `n : ℕ`, if `a > 0` and the n×n Schur complement admits
    a Gram factorization `schurComplement a b C = A_nᵀ * A_n`, then the full
    (n+1)×(n+1) block matrix `S = blockMatrix a b C` satisfies:
      `S = (choleskyLift a b A_n)ᵀ * (choleskyLift a b A_n)`,
      `gramLyapunovEnergy S (choleskyLift a b A_n) = 0`, AND
      `∀ x : Fin (n + 1) → ℝ, 0 ≤ dotProduct x (S.mulVec x)`!
  - `cholesky_1x1_gram_certificate`:
    Base case `n = 1`: `a ≥ 0 → S = Aᵀ * A ∧ gramLyapunovEnergy S A = 0 ∧ S ⪰ 0`.
  ==============================================================================
-/

import RiemannDipolar.LyapunovGramDescentAndCertifiedSchurBlocks

open Real Complex Filter Topology Set
open scoped BigOperators Classical Matrix
open CriticalStripCollarAllOrderConvexityAndSchurGram
open CliffordSieveAdelicClosure
open UniversalMotherFormulaCliffordHierarchy
open AdelicGramFactorizationAndLyapunovFlow
open LyapunovGramDescentAndCertifiedSchurBlocks

namespace ArbitraryDimCholeskySchurInduction

/-- Construct the symmetric `(n + 1) × (n + 1)` block matrix:
    top-left `a`, top-right `bᵀ`, bottom-left `b`, bottom-right `C`. -/
def blockMatrix {n : ℕ} (a : ℝ) (b : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.cases
      (Fin.cases a b j)
      (fun i' => Fin.cases (b i') (fun j' => C i' j') j)
      i

/-- Exact `n × n` Schur complement: `(C - (1 / a) b bᵀ)_{i, j} = C_{i, j} - (b i * b j) / a`. -/
noncomputable def schurComplement {n : ℕ} (a : ℝ) (b : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => C i j - (b i * b j) / a

/-- Explicit `(n + 1) × (n + 1)` upper-triangular Cholesky–Gram lift of `A_n`:
    top-left `√a`, top-right `b / √a`, bottom-left `0`, bottom-right `A_n`. -/
noncomputable def choleskyLift {n : ℕ} (a : ℝ) (b : Fin n → ℝ) (A_n : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.cases
      (Fin.cases (Real.sqrt a) (fun j' => b j' / Real.sqrt a) j)
      (fun i' => Fin.cases 0 (fun j' => A_n i' j') j)
      i

/-- THEOREM I.1 (BASE CASE n = 1 CHOLESKY–GRAM CERTIFICATE): -/
theorem cholesky_1x1_gram_certificate (a : ℝ) (ha : 0 ≤ a) :
    let S : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => a
    let A : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => Real.sqrt a
    S = Aᵀ * A ∧ gramLyapunovEnergy S A = 0 ∧
    ∀ x : Fin 1 → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
  intro S A
  have hS : S = Aᵀ * A := by
    ext i j
    simp only [S, A, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one, Matrix.of_apply]
    exact (Real.mul_self_sqrt ha).symm
  exact ⟨hS, (gramLyapunovEnergy_eq_zero_iff S A).mpr hS,
    routeA_gram_factorization_implies_psd S A hS⟩

/-- THEOREM I.2 (ARBITRARY-DIMENSION n → n + 1 BLOCK-SCHUR CHOLESKY–GRAM INDUCTION):
    For EVERY finite dimension `n : ℕ`, if `a > 0` and the `n × n` Schur complement
    `schurComplement a b C` admits a Gram factorization `A_nᵀ * A_n`, then the full
    `(n + 1) × (n + 1)` block matrix `S = blockMatrix a b C` satisfies:
      1. `S = (choleskyLift a b A_n)ᵀ * (choleskyLift a b A_n)`,
      2. `gramLyapunovEnergy S (choleskyLift a b A_n) = 0`,
      3. `∀ x : Fin (n + 1) → ℝ, 0 ≤ dotProduct x (S.mulVec x)`! -/
theorem block_schur_cholesky_gram_induction {n : ℕ}
    (a : ℝ) (b : Fin n → ℝ) (C A_n : Matrix (Fin n) (Fin n) ℝ)
    (ha : 0 < a)
    (hSchur : schurComplement a b C = A_nᵀ * A_n) :
    let S := blockMatrix a b C
    let A := choleskyLift a b A_n
    S = Aᵀ * A ∧ gramLyapunovEnergy S A = 0 ∧
    ∀ x : Fin (n + 1) → ℝ, 0 ≤ dotProduct x (S.mulVec x) := by
  intro S A
  have hsqa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (le_of_lt ha)
  have hsqa_ne : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hS : S = Aᵀ * A := by
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · -- (0, 0) entry
        simp only [S, A, blockMatrix, choleskyLift, Matrix.mul_apply, Matrix.transpose_apply,
          Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero,
          Finset.sum_const_zero, add_zero]
        exact hsqa.symm
      · -- (0, j'+1) entry
        simp only [S, A, blockMatrix, choleskyLift, Matrix.mul_apply, Matrix.transpose_apply,
          Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul,
          Finset.sum_const_zero, add_zero]
        field_simp [hsqa_ne]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · -- (i'+1, 0) entry
        simp only [S, A, blockMatrix, choleskyLift, Matrix.mul_apply, Matrix.transpose_apply,
          Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero,
          Finset.sum_const_zero, add_zero]
        field_simp [hsqa_ne]
      · -- (i'+1, j'+1) entry
        simp only [S, A, blockMatrix, choleskyLift, Matrix.mul_apply, Matrix.transpose_apply,
          Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
        have hEntry := congrFun (congrFun hSchur i') j'
        simp only [schurComplement, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply] at hEntry
        have hmul : b i' / Real.sqrt a * (b j' / Real.sqrt a) = b i' * b j' / a := by
          rw [div_mul_div_comm, hsqa]
        rw [hmul, ← hEntry]
        ring
  exact ⟨hS, (gramLyapunovEnergy_eq_zero_iff S A).mpr hS,
    routeA_gram_factorization_implies_psd S A hS⟩

end ArbitraryDimCholeskySchurInduction
