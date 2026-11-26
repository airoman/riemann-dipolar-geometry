/-
  ==============================================================================
  MODULE #29: STEREOGRAPHIC COMPACTIFICATION OF THE INFINITE HORIZON L ∈ (0, ∞)
  ONTO S³ / M⁵ AND UNIFORM COMPACT MARGIN THEOREM

  Title: Stereographic Horizon Compactification on M⁵ and Uniform Margin
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - `stereographicHorizon L = 2 * Real.arctan L`:
    Maps the unbounded horizon L ∈ (0, ∞) strictly monotonically into the
    compact polar arc (0, π) of S³ / M⁵, with L → ∞ mapping to the North Pole π.
  - `stereographicHorizon_mem_Ioo`:
    For every L > 0, `0 < stereographicHorizon L ∧ stereographicHorizon L < π`.
  - `tendsto_stereographicHorizon_atTop`:
    `Tendsto stereographicHorizon atTop (𝓝 π)`.
  - `compact_horizon_pos_implies_uniform_margin`:
    If a continuous renormalized spectral-margin function `μ_tilde : ℝ → ℝ`
    on the compactified arc `[0, π]` (including the North Pole `π` representing
    `L = ∞`) is strictly positive on `[0, π]`, then by compactness of `[0, π]`
    there exists a UNIFORM constant `c > 0` such that
      `∀ L > 0, c ≤ μ_tilde (stereographicHorizon L)`!
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Order.Compact
import RiemannDipolar.PrimeDowndateWeylPerturbationAndGramMargin

open Real Filter Topology Set
open scoped BigOperators Classical

namespace CompactifiedHorizonManifold5DClosure

/-- Stereographic polar compactification of the Weil horizon L ∈ (0, ∞) onto
    the compact meridian arc (0, π) of S³ ⊂ M⁵: θ(L) = 2 arctan(L).
    The infinite horizon L → ∞ is mapped to the North Pole θ = π. -/
noncomputable def stereographicHorizon (L : ℝ) : ℝ :=
  2 * Real.arctan L

/-- THEOREM I.1 (STRICT INCLUSION IN THE OPEN POLAR ARC (0, π)):
    For every positive horizon L > 0, θ(L) ∈ (0, π). -/
theorem stereographicHorizon_mem_Ioo {L : ℝ} (hL : 0 < L) :
    0 < stereographicHorizon L ∧ stereographicHorizon L < Real.pi := by
  unfold stereographicHorizon
  have h1 : 0 < Real.arctan L := by
    have := Real.arctan_strictMono hL
    rwa [Real.arctan_zero] at this
  have h2 : Real.arctan L < Real.pi / 2 := Real.arctan_lt_pi_div_two L
  exact ⟨by linarith, by linarith⟩

/-- THEOREM I.2 (NORTH POLE LIMIT AS L → ∞):
    As L → ∞, the stereographic horizon converges to the North Pole π on S³. -/
theorem tendsto_stereographicHorizon_atTop :
    Tendsto stereographicHorizon atTop (𝓝 Real.pi) := by
  unfold stereographicHorizon
  have h := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul (2 : ℝ)
  have hpi : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [hpi] at h
  exact h

/-- THEOREM I.3 (COMPACTNESS ON M⁵ → UNIFORM STRICTLY POSITIVE MARGIN FOR ALL L > 0):
    If a continuous renormalized margin function `μ_tilde : ℝ → ℝ` on the compact
    meridian arc `[0, π]` (including the North Pole `π` representing `L = ∞`)
    satisfies `0 < μ_tilde θ` for every `θ ∈ [0, π]`, then there exists a UNIFORM
    strictly positive constant `c > 0` bounding `μ_tilde (stereographicHorizon L)`
    from below for EVERY horizon `L > 0`! -/
theorem compact_horizon_pos_implies_uniform_margin
    (μ_tilde : ℝ → ℝ)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Set.Icc 0 Real.pi, 0 < μ_tilde θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 0 < L → c ≤ μ_tilde (stereographicHorizon L) := by
  have hne : (Set.Icc (0 : ℝ) Real.pi).Nonempty := ⟨0, Set.left_mem_Icc.mpr (le_of_lt Real.pi_pos)⟩
  rcases isCompact_Icc.exists_isMinOn hne hcont with ⟨θ_min, hθ_mem, hmin⟩
  refine ⟨μ_tilde θ_min, hpos θ_min hθ_mem, ?_⟩
  intro L hL
  have hmem : stereographicHorizon L ∈ Set.Icc 0 Real.pi := by
    have hioo := stereographicHorizon_mem_Ioo hL
    exact ⟨le_of_lt hioo.1, le_of_lt hioo.2⟩
  exact hmin hmem

end CompactifiedHorizonManifold5DClosure
