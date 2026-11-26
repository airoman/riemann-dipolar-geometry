/-
  ==============================================================================
  MODULE #31: INDETERMINACY REGULARIZATION ([∞ - ∞], [∞ / ∞], [0 / 0]) ON M⁵,
  GOLDEN-NODE (π/4) EQUIPARTITION, & CRITICAL-MODE RAYLEIGH QUOTIENT

  Title: Indeterminacy Regularization and Critical-Mode Projection on M⁵
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - `complex_phasor_unit_norm`:
    For every real phase `θ : ℝ`, `‖Complex.exp (θ * Complex.I)‖ = 1`
    (phase information on S¹ ⊂ T² never vanishes even as amplitude R → 0).
  - `golden_node_equipartition`:
    At the primordial Golden Node `θ₀ = π / 4`,
    `Real.cos (π / 4) ^ 2 = 1 / 2 ∧ Real.sin (π / 4) ^ 2 = 1 / 2`
    (matching the exact 50/50 odd-even harmonic equipartition of v_min!).
  - `regularized_inf_minus_inf_iff_ratio`:
    For `A > 0`, `0 ≤ A - B ↔ B / A ≤ 1`, reducing the `[∞ - ∞]` North-Pole
    indeterminacy `W_inf - P_prime` directly to the bounded `[∞ / ∞]` ratio.
  - `rayleighQuotient` & `rayleighQuotient_nonneg_iff_psd`:
    Exact `[0 / 0]` boundary regularization: a matrix `S` is PSD iff its
    Rayleigh quotient `(vᵀ S v) / ‖v‖²` is nonnegative for all nonzero `v`.
  ==============================================================================
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannDipolar.NorthPoleRenormalizationAndChebyshevBridge

open Real Complex Filter Topology Set
open scoped BigOperators Classical Matrix
open PrimeDowndateWeylPerturbationAndGramMargin

namespace IndeterminacyRegularizationAndCriticalModeProjection

-- ==============================================================================
-- PART I: COMPLEX PHASE PRESERVATION & GOLDEN-NODE (π/4) EQUIPARTITION
-- ==============================================================================

/-- THEOREM I.1 (UNIT-NORM PHASE PRESERVATION ON S¹ ⊂ T²):
    For every real phase angle `θ : ℝ`, the unit phasor `exp(i θ)` has norm 1.
    Under amplitude collapse `R → 0` (indeterminacy `0^0` or `0 / 0`), the
    angular phase channel on T² remains strictly unit-norm. -/
theorem complex_phasor_unit_norm (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- THEOREM I.2 (GOLDEN-NODE θ₀ = π/4 EXACT 50/50 EQUIPARTITION):
    At `θ₀ = π / 4`, `cos²(π/4) = sin²(π/4) = 1/2`, matching both the
    Clifford Torus equator and the asymptotic critical eigenmode
    `v_min → (1/√2, 1/√2, 0, ...)`. -/
theorem golden_node_equipartition :
    Real.cos (Real.pi / 4) ^ 2 = 1 / 2 ∧ Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact ⟨h, h⟩

-- ==============================================================================
-- PART II: [∞ - ∞] → [∞ / ∞] REGULARIZATION AT THE NORTH POLE θ = π
-- ==============================================================================

/-- THEOREM II.1 (EXACT [∞ - ∞] TO [∞ / ∞] REDUCTION):
    For any strictly positive Archimedean scale `A > 0` and prime sum `B : ℝ`,
      `A - B = A * (1 - B / A)` and `0 ≤ A - B ↔ B / A ≤ 1`. -/
theorem regularized_inf_minus_inf_iff_ratio {A B : ℝ} (hA : 0 < A) :
    A - B = A * (1 - B / A) ∧ (0 ≤ A - B ↔ B / A ≤ 1) := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have heq : A - B = A * (1 - B / A) := by
    field_simp [hA_ne]
  refine ⟨heq, ?_⟩
  constructor
  · intro h
    have hle : B ≤ A := by linarith
    exact (div_le_one hA).mpr hle
  · intro h
    have hle : B ≤ A := (div_le_one hA).mp h
    linarith

-- ==============================================================================
-- PART III: [0 / 0] RAYLEIGH QUOTIENT & CRITICAL-MODE POSITIVITY
-- ==============================================================================

/-- Rayleigh quotient `R(S, v) = (vᵀ S v) / ‖v‖²` for `v : Fin n → ℝ`. -/
noncomputable def rayleighQuotient {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  dotProduct v (S.mulVec v) / vecNormSq v

/-- Helper: `vecNormSq v = 0 ↔ v = 0`. -/
theorem vecNormSq_eq_zero_iff {n : ℕ} (v : Fin n → ℝ) :
    vecNormSq v = 0 ↔ v = 0 := by
  unfold vecNormSq dotProduct
  constructor
  · intro h
    ext i
    have hi : v i * v i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (v j)).mp h i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi
  · rintro rfl
    simp

/-- THEOREM III.1 (EXACT CRITICAL-MODE RAYLEIGH CHARACTERIZATION OF PSD):
    A matrix `S` is positive semidefinite (`∀ v, 0 ≤ vᵀ S v`) IF AND ONLY IF
    its Rayleigh quotient is nonnegative on every nonzero vector `v ≠ 0`! -/
theorem rayleighQuotient_nonneg_iff_psd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    (∀ v : Fin n → ℝ, v ≠ 0 → 0 ≤ rayleighQuotient S v) ↔
    (∀ v : Fin n → ℝ, 0 ≤ dotProduct v (S.mulVec v)) := by
  constructor
  · intro h v
    by_cases hv : v = 0
    · subst hv; simp
    · have hnorm_pos : 0 < vecNormSq v :=
        lt_of_le_of_ne (vecNormSq_nonneg v) (Ne.symm (mt (vecNormSq_eq_zero_iff v).mp hv))
      have hr := h v hv
      unfold rayleighQuotient at hr
      exact (div_nonneg_iff.mp hr).elim
        (fun ⟨hnum, _⟩ => hnum)
        (fun ⟨_, hden⟩ => absurd hden (not_le_of_gt hnorm_pos))
  · intro h v hv
    have hnorm_pos : 0 < vecNormSq v :=
      lt_of_le_of_ne (vecNormSq_nonneg v) (Ne.symm (mt (vecNormSq_eq_zero_iff v).mp hv))
    unfold rayleighQuotient
    exact div_nonneg (h v) (le_of_lt hnorm_pos)

end IndeterminacyRegularizationAndCriticalModeProjection
