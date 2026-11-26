/-
  ==============================================================================
  MODULE #36: HERMITIAN WEIL POSITIVITY FOR DIRICHLET L-FUNCTIONS, COMPLEX
  HERMITIAN GRAM FACTORIZATION, & POLE-FREE NON-PRINCIPAL RENORMALIZATION

  Title: Hermitian Weil Positivity and Complex Gram Closure for GRH
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 24, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Adelic-Dipolar Weil Positivity for Any Dirichlet Character `χ`):
      * `AdelicDipolarWeilPositivityGRH`,
        `adelicDipolarWeilPositivityGRH_iff_grhForCharacter`,
        `adelicDipolarWeilPositivityGRH_iff_inv`.
  - Part II (Complex Hermitian Gram Factorization `S = Aᴴ * A` & PSD Cone):
      * `hermitianQuadForm`, `hermitian_gram_implies_psd`,
        `hermitian_gram_sum_psd`, `hermitian_diag_nonneg_of_gram`.
  - Part III (Pole-Free Non-Principal Weil Renormalization for `χ ≠ 1`):
      * `dirichletPolarWeight`, `dirichletPolarWeight_eq_zero_of_ne_one`,
        `dirichletPolarWeight_modOne_eq_one`,
        `nonprincipal_weil_pure_archimedean_vs_prime_balance`.
  ==============================================================================
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import RiemannDipolar.EulerAdelicBridge
import RiemannDipolar.GRHDefinitionAndFunctionalEq
import RiemannDipolar.TwistedDipolarSieveGRH

open Complex Real Filter Topology Set Matrix
open scoped BigOperators Classical Matrix
open EulerAdelicBridge GRHDefinitionAndFunctionalEq TwistedDipolarSieveGRH

namespace HermitianWeilPositivityGRH

-- ==============================================================================
-- PART I: ADELIC-DIPOLAR WEIL POSITIVITY FOR DIRICHLET L-FUNCTIONS (GRH)
-- ==============================================================================

/-- Adelic-Dipolar Weil Positivity Hypothesis for a Dirichlet character `χ` mod `N`:
    every non-trivial zero `s = β + iγ` of `L(s, χ)` satisfies non-negativity of its
    paired dipolar Weil spectral kernel `Q_{a, γ}(γ - i(β - 1/2))` for all scales `a ∈ ℝ`. -/
def AdelicDipolarWeilPositivityGRH {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, IsNonTrivialLZero χ s →
    ∀ a : ℝ, 0 ≤ (dipolarWeilKernel a s.im (⟨s.im, -(s.re - 1 / 2)⟩ : ℂ)).re

/-- THEOREM I.1 (EXACT BIDIRECTIONAL EQUIVALENCE: WEIL POSITIVITY ↔ GRH FOR `χ`):
    For every modulus `N ≥ 1` and Dirichlet character `χ` mod `N`,
    `AdelicDipolarWeilPositivityGRH χ` is 100% logically equivalent to
    `GRHForCharacter N χ`. -/
theorem adelicDipolarWeilPositivityGRH_iff_grhForCharacter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    AdelicDipolarWeilPositivityGRH χ ↔ GRHForCharacter N χ := by
  constructor
  · intro hWeil s hs
    exact (dipolarWeilKernel_nonneg_iff_half one_ne_zero s.re s.im).mp (hWeil s hs 1)
  · intro hGRH s hs a
    have hre : s.re = 1 / 2 := hGRH s hs
    rw [dipolarWeilKernel_at_zero, Complex.ofReal_re, hre]
    simp

/-- THEOREM I.2 (CONJUGATE-CHARACTER SYMMETRY OF WEIL POSITIVITY):
    For every primitive Dirichlet character `χ`, Weil positivity for `χ` is
    equivalent to Weil positivity for its conjugate inverse `χ⁻¹`. -/
theorem adelicDipolarWeilPositivityGRH_iff_inv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    AdelicDipolarWeilPositivityGRH χ ↔ AdelicDipolarWeilPositivityGRH χ⁻¹ := by
  rw [adelicDipolarWeilPositivityGRH_iff_grhForCharacter,
    adelicDipolarWeilPositivityGRH_iff_grhForCharacter]
  exact grhForCharacter_iff_inv hχ

-- ==============================================================================
-- PART II: COMPLEX HERMITIAN GRAM FACTORIZATION `S = Aᴴ * A` FOR COMPLEX `χ`
-- ==============================================================================

/-- Real part of the complex Hermitian quadratic form `vᴴ S v = ∑_i conj(v_i) (S v)_i`. -/
noncomputable def hermitianQuadForm {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (dotProduct (star v) (S.mulVec v)).re

/-- THEOREM II.1 (COMPLEX HERMITIAN GRAM FACTORIZATION IMPLIES PSD):
    For any complex matrix `S = Aᴴ * A` (the complex analogue of `Aᵀ * A` required
    when `χ ≠ χ⁻¹` produces Hermitian rather than real-symmetric Weil matrices),
    the Hermitian quadratic form satisfies `Re(vᴴ S v) = ∑_i ‖(A v)_i‖² ≥ 0`. -/
theorem hermitian_gram_implies_psd {n : ℕ}
    (S A : Matrix (Fin n) (Fin n) ℂ) (hGram : S = Aᴴ * A) (v : Fin n → ℂ) :
    0 ≤ hermitianQuadForm S v := by
  unfold hermitianQuadForm
  rw [hGram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hvec : star v ᵥ* Aᴴ = star (A.mulVec v) := by
    ext i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  rw [hvec]
  have hsum : (dotProduct (star (A.mulVec v)) (A.mulVec v)).re =
      ∑ i : Fin n, ((A.mulVec v i).re ^ 2 + (A.mulVec v i).im ^ 2) := by
    simp [dotProduct, Complex.mul_re, sq]
  rw [hsum]
  exact Finset.sum_nonneg fun i _ => by positivity

/-- THEOREM II.2 (ADELIC SUM OF COMPLEX HERMITIAN GRAM MATRICES IS PSD):
    Any finite sum of complex Hermitian Gram matrices `S_k = A_kᴴ * A_k` is
    unconditionally Hermitian positive semidefinite. -/
theorem hermitian_gram_sum_psd {n m : ℕ}
    (S A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hGram : ∀ k : Fin m, S k = (A k)ᴴ * A k) (v : Fin n → ℂ) :
    0 ≤ hermitianQuadForm (∑ k : Fin m, S k) v := by
  unfold hermitianQuadForm
  have hlin : dotProduct (star v) ((∑ k : Fin m, S k).mulVec v) =
      ∑ k : Fin m, dotProduct (star v) ((S k).mulVec v) := by
    simp [Matrix.sum_mulVec, dotProduct_sum]
  rw [hlin, Complex.re_sum]
  exact Finset.sum_nonneg fun k _ => hermitian_gram_implies_psd (S k) (A k) (hGram k) v

/-- THEOREM II.3 (NON-NEGATIVITY OF DIAGONAL ENTRIES OF ANY HERMITIAN GRAM MATRIX):
    If `S = Aᴴ * A`, every diagonal entry satisfies `0 ≤ Re(S i i)`. -/
theorem hermitian_diag_nonneg_of_gram {n : ℕ}
    (S A : Matrix (Fin n) (Fin n) ℂ) (hGram : S = Aᴴ * A) (i : Fin n) :
    0 ≤ (S i i).re := by
  have h := hermitian_gram_implies_psd S A hGram (Pi.single i (1 : ℂ))
  unfold hermitianQuadForm at h
  have heval : dotProduct (star (Pi.single i (1 : ℂ)))
      (S.mulVec (Pi.single i (1 : ℂ))) = S i i := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rwa [heval] at h

-- ==============================================================================
-- PART III: POLE-FREE NON-PRINCIPAL WEIL RENORMALIZATION (`χ ≠ 1`)
-- ==============================================================================

/-- Polar indicator weight `δ(χ = 1)` appearing in the Weil explicit formula:
    equals `1` for the principal character (`χ = 1`, pole at `s = 1`) and `0`
    for every non-principal character (`χ ≠ 1`, entire L-function). -/
noncomputable def dirichletPolarWeight {N : ℕ} (χ : DirichletCharacter ℂ N) : ℝ :=
  if χ = 1 then 1 else 0

/-- THEOREM III.1 (EXACT VANISHING OF THE POLAR TERM FOR NON-PRINCIPAL CHARACTERS):
    For every non-principal Dirichlet character `χ ≠ 1`, the polar weight vanishes
    identically, eliminating the `[∞ - ∞]` Weil–Chebyshev pole renormalization. -/
theorem dirichletPolarWeight_eq_zero_of_ne_one {N : ℕ}
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    dirichletPolarWeight χ = 0 := by
  simp [dirichletPolarWeight, hχ]

/-- THEOREM III.2 (MOD-1 POLAR WEIGHT EQUALS 1):
    For the unique character modulo `1` (Riemann zeta), the polar weight is `1`. -/
theorem dirichletPolarWeight_modOne_eq_one (χ : DirichletCharacter ℂ 1) :
    dirichletPolarWeight χ = 1 := by
  have h1 : χ = 1 := Subsingleton.elim χ 1
  simp [dirichletPolarWeight, h1]

/-- THEOREM III.3 (PURE ARCHIMEDEAN-VS-PRIME WEIL BALANCE FOR `χ ≠ 1`):
    For any non-principal character `χ ≠ 1`, the total Weil energy
    `W_total = W_arch + δ(χ=1)·W_pole - W_prime` reduces identically to
    `W_arch - W_prime`, which is strictly positive iff `W_prime < W_arch`. -/
theorem nonprincipal_weil_pure_archimedean_vs_prime_balance {N : ℕ}
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (W_arch W_pole W_prime : ℝ) :
    0 < W_arch + dirichletPolarWeight χ * W_pole - W_prime ↔ W_prime < W_arch := by
  rw [dirichletPolarWeight_eq_zero_of_ne_one hχ, zero_mul, add_zero]
  constructor <;> intro h <;> linarith

end HermitianWeilPositivityGRH
