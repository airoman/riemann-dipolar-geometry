/-
  ==============================================================================
  MODULE #32: GLOBAL GEODESIC COMPLETENESS, PSD CONE CLOSURE &
  TRIADIC DIFFERENTIAL-INTEGRAL REDUCTION OF THE ADELIC GAP

  Title: Global Geodesic Completeness and Adelic Margin Reduction
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  1. `psd_cone_closed_under_quadratic_limit`:
     If a sequence of Gram-factorizable matrices `S_k = A_kᵀ * A_k` converges
     in quadratic form to `S_inf`, then `S_inf` is unconditionally PSD
     (`0 ≤ x ⬝ᵥ S_inf.mulVec x` for all `x`). Thus the `λ_min → 0⁺` boundary
     is topologically safe and preserves non-negativity in the limit.
  2. `geodesic_linear_deriv_bound_implies_north_pole_pos`:
     Along the compactified meridian `[0, π]` of `S³ ⊂ M⁵`, if the geodesic
     derivative `μ_tilde' θ ≥ -B` on `(0, π)` with `B * π < μ_tilde 0`,
     then `μ_tilde θ > 0` for EVERY `θ ∈ [0, π]` (including the North Pole `π`).
  3. `geodesic_log_gronwall_barrier_implies_north_pole_pos`:
     Using the exponential-logarithmic damping factor `exp (C * θ) * μ_tilde θ`,
     ANY finite relative decay bound `μ_tilde' θ ≥ -C * μ_tilde θ` on `(0, π)`
     with `μ_tilde 0 > 0` forces `μ_tilde θ ≥ μ_tilde 0 * exp (-C * π) > 0`
     uniformly on the entire compact arc `[0, π]`, unconditionally triggering
     Module #30 (`north_pole_continuity_implies_all_horizon_gram_closure`)!
  4. `kinetic_potential_bound_prevents_boundary_escape`:
     If the kinetic potential `K(φ) = 1 / (2 * φ * (1 - φ))` stays bounded by
     `M > 0` along a geodesic phase trajectory `φ(θ) ∈ (0, 1)`, then `φ(θ)` is
     uniformly confined to `[1 / (2 * M), 1 - 1 / (2 * M)]`, never touching
     the singular boundaries `0` or `1`.
  ==============================================================================
-/

import RiemannDipolar.NorthPoleRenormalizationAndChebyshevBridge
import Mathlib.Analysis.Calculus.MeanValue

open Real Filter Topology Set
open scoped BigOperators Classical Matrix
open PrimeDowndateWeylPerturbationAndGramMargin
open CompactifiedHorizonManifold5DClosure
open NorthPoleRenormalizationAndChebyshevBridge

namespace GlobalGeodesicCompletenessAndAdelicMargin

/-- THEOREM I.1 (TOPOLOGICAL CLOSEDNESS OF THE PSD / GRAM CONE):
    If for every `k : ℕ`, the matrix `S k` admits a Gram factorization
    `S k = (A k)ᵀ * (A k)`, and the quadratic forms `x ⬝ᵥ (S k).mulVec x`
    converge to `x ⬝ᵥ S_inf.mulVec x` as `k → ∞`, then `S_inf` is
    unconditionally positive semidefinite: `0 ≤ x ⬝ᵥ S_inf.mulVec x`.
    This proves that the `λ_min → 0⁺` boundary is topologically closed. -/
theorem psd_cone_closed_under_quadratic_limit
    {n : ℕ}
    (S A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (S_inf : Matrix (Fin n) (Fin n) ℝ)
    (hGram : ∀ k : ℕ, S k = (A k)ᵀ * A k)
    (hLim : ∀ x : Fin n → ℝ,
      Tendsto (fun k => dotProduct x ((S k).mulVec x)) atTop
        (𝓝 (dotProduct x (S_inf.mulVec x)))) :
    ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (S_inf.mulVec x) := by
  intro x
  have hnonneg : ∀ k : ℕ, 0 ≤ dotProduct x ((S k).mulVec x) := by
    intro k
    rw [hGram k]
    have hmul : ((A k)ᵀ * A k).mulVec x = (A k)ᵀ.mulVec ((A k).mulVec x) := by
      rw [Matrix.mulVec_mulVec]
    rw [hmul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg ((A k).mulVec x i))
  exact ge_of_tendsto (hLim x) (Eventually.of_forall hnonneg)

/-- THEOREM II.1 (GEODESIC LINEAR DERIVATIVE BOUND → NORTH-POLE POSITIVITY):
    If the renormalized margin `μ_tilde` on the compactified meridian `[0, π]`
    is continuous on `[0, π]`, has derivative `μ_tilde'` on `(0, π)` bounded
    below by `-B`, and `B * π < μ_tilde 0`, then `μ_tilde θ > 0` for EVERY
    `θ ∈ [0, π]` (including the North Pole `θ = π`). -/
theorem geodesic_linear_deriv_bound_implies_north_pole_pos
    (μ_tilde μ_tilde' : ℝ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, HasDerivAt μ_tilde (μ_tilde' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo 0 Real.pi, -B ≤ μ_tilde' θ)
    (hinit : B * Real.pi < μ_tilde 0) :
    ∀ θ ∈ Set.Icc 0 Real.pi, 0 < μ_tilde θ := by
  let g : ℝ → ℝ := fun θ => μ_tilde θ + B * θ
  have hg_cont : ContinuousOn g (Set.Icc 0 Real.pi) :=
    hcont.add (continuousOn_const.mul continuousOn_id)
  have hg_deriv : ∀ θ ∈ Set.Ioo 0 Real.pi, HasDerivAt g (μ_tilde' θ + B) θ := by
    intro θ hθ
    have h1 := hderiv θ hθ
    have h2 : HasDerivAt (fun x => B * x) (B * 1) θ := (hasDerivAt_id θ).const_mul B
    convert h1.add h2 using 1
    ring
  have hg_nonneg : ∀ θ ∈ Set.Ioo 0 Real.pi, 0 ≤ deriv g θ := by
    intro θ hθ
    rw [(hg_deriv θ hθ).deriv]
    linarith [hbound θ hθ]
  have hg_mono : MonotoneOn g (Set.Icc 0 Real.pi) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 Real.pi) hg_cont
      (fun θ hθ => (hg_deriv θ (by simpa [interior_Icc] using hθ)).differentiableAt.differentiableWithinAt)
      (fun θ hθ => hg_nonneg θ (by simpa [interior_Icc] using hθ))
  intro θ hθ
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, le_of_lt Real.pi_pos⟩
  have hle : g 0 ≤ g θ := hg_mono h0_mem hθ hθ.1
  have hBθ : B * θ ≤ B * Real.pi := mul_le_mul_of_nonneg_left hθ.2 hB
  dsimp [g] at hle
  linarith

/-- THEOREM II.2 (EXPONENTIAL-LOGARITHMIC GRONWALL BARRIER ON `[0, π]`):
    Using the exponential-logarithmic damping factor `exp (C * θ) * μ_tilde θ`:
    For ANY finite constant `C ≥ 0`, if the relative geodesic decay satisfies
    `μ_tilde' θ ≥ -C * μ_tilde θ` on `(0, π)` and `μ_tilde 0 > 0`, then
    `μ_tilde θ ≥ μ_tilde 0 * exp (-C * π) > 0` for EVERY `θ ∈ [0, π]`!
    This reduces the entire infinite-horizon gap to bounding the relative
    geodesic decay rate `μ_tilde' / μ_tilde` on the compact arc `(0, π)`. -/
theorem geodesic_log_gronwall_barrier_implies_north_pole_pos
    (μ_tilde μ_tilde' : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, HasDerivAt μ_tilde (μ_tilde' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo 0 Real.pi, -C * μ_tilde θ ≤ μ_tilde' θ)
    (hinit : 0 < μ_tilde 0) :
    ∀ θ ∈ Set.Icc 0 Real.pi, μ_tilde 0 * Real.exp (-C * Real.pi) ≤ μ_tilde θ := by
  let g : ℝ → ℝ := fun θ => Real.exp (C * θ) * μ_tilde θ
  have hexp_cont : ContinuousOn (fun θ => Real.exp (C * θ)) (Set.Icc 0 Real.pi) :=
    (continuousOn_const.mul continuousOn_id).rexp
  have hg_cont : ContinuousOn g (Set.Icc 0 Real.pi) := hexp_cont.mul hcont
  have hg_deriv : ∀ θ ∈ Set.Ioo 0 Real.pi,
      HasDerivAt g (Real.exp (C * θ) * (C * μ_tilde θ + μ_tilde' θ)) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun x => Real.exp (C * x)) (Real.exp (C * θ) * (C * 1)) θ :=
      ((hasDerivAt_id θ).const_mul C).exp
    have h2 := hderiv θ hθ
    have hprod := h1.mul h2
    convert hprod using 1
    ring
  have hg_nonneg : ∀ θ ∈ Set.Ioo 0 Real.pi, 0 ≤ deriv g θ := by
    intro θ hθ
    rw [(hg_deriv θ hθ).deriv]
    apply mul_nonneg (le_of_lt (Real.exp_pos (C * θ)))
    linarith [hbound θ hθ]
  have hg_mono : MonotoneOn g (Set.Icc 0 Real.pi) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 Real.pi) hg_cont
      (fun θ hθ => (hg_deriv θ (by simpa [interior_Icc] using hθ)).differentiableAt.differentiableWithinAt)
      (fun θ hθ => hg_nonneg θ (by simpa [interior_Icc] using hθ))
  intro θ hθ
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, le_of_lt Real.pi_pos⟩
  have hle : g 0 ≤ g θ := hg_mono h0_mem hθ hθ.1
  dsimp [g] at hle
  rw [mul_zero, Real.exp_zero, one_mul] at hle
  have hmul : μ_tilde 0 * Real.exp (-(C * θ)) ≤ μ_tilde θ := by
    have hpos : 0 < Real.exp (C * θ) := Real.exp_pos (C * θ)
    have h1 : μ_tilde 0 * Real.exp (-(C * θ)) ≤ (Real.exp (C * θ) * μ_tilde θ) * Real.exp (-(C * θ)) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt (Real.exp_pos _))
    have hcancel : (Real.exp (C * θ) * μ_tilde θ) * Real.exp (-(C * θ)) = μ_tilde θ := by
      rw [mul_assoc, mul_comm (μ_tilde θ), ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    linarith
  have hexp_le : Real.exp (-C * Real.pi) ≤ Real.exp (-(C * θ)) := by
    apply Real.exp_le_exp.mpr
    have hCθ : C * θ ≤ C * Real.pi := mul_le_mul_of_nonneg_left hθ.2 hC
    linarith
  have hstep : μ_tilde 0 * Real.exp (-C * Real.pi) ≤ μ_tilde 0 * Real.exp (-(C * θ)) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hinit)
  exact le_trans hstep hmul

/-- COROLLARY II.3 (GEODESIC GRONWALL BARRIER → STRICT POSITIVITY ON `[0, π]`):
    Under the hypotheses of Theorem II.2, `μ_tilde θ > 0` for all `θ ∈ [0, π]`,
    directly satisfying the North-Pole positivity hypothesis of Module #30. -/
theorem geodesic_log_gronwall_implies_strict_pos
    (μ_tilde μ_tilde' : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, HasDerivAt μ_tilde (μ_tilde' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo 0 Real.pi, -C * μ_tilde θ ≤ μ_tilde' θ)
    (hinit : 0 < μ_tilde 0) :
    ∀ θ ∈ Set.Icc 0 Real.pi, 0 < μ_tilde θ := by
  intro θ hθ
  have hle := geodesic_log_gronwall_barrier_implies_north_pole_pos
    μ_tilde μ_tilde' C hC hcont hderiv hbound hinit θ hθ
  have hpos : 0 < μ_tilde 0 * Real.exp (-C * Real.pi) :=
    mul_pos hinit (Real.exp_pos (-C * Real.pi))
  exact lt_of_lt_of_le hpos hle

/-- THEOREM III.1 (KINETIC POTENTIAL CONFINEMENT WALL):
    For any phase coordinate `φ ∈ (0, 1)`, if the kinetic confinement potential
    `K(φ) = 1 / (2 * φ * (1 - φ))` is bounded above by `M > 0`, then `φ` is
    strictly confined away from the singular boundaries `0` and `1`:
      `1 / (2 * M) ≤ φ`  and  `φ ≤ 1 - 1 / (2 * M)`. -/
theorem kinetic_potential_bound_prevents_boundary_escape
    {φ M : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hM : 0 < M)
    (hK : 1 / (2 * φ * (1 - φ)) ≤ M) :
    1 / (2 * M) ≤ φ ∧ φ ≤ 1 - 1 / (2 * M) := by
  have h1m : 0 < 1 - φ := by linarith
  have hden : 0 < 2 * φ * (1 - φ) := by positivity
  have hprod : 1 ≤ M * (2 * φ * (1 - φ)) := (div_le_iff₀ hden).mp hK
  have h2M : 0 < 2 * M := by positivity
  constructor
  · rw [div_le_iff₀ h2M]
    nlinarith
  · have hstep : 1 / (2 * M) ≤ 1 - φ := by
      rw [div_le_iff₀ h2M]
      nlinarith
    linarith

end GlobalGeodesicCompletenessAndAdelicMargin
