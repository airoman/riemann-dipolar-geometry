/-
  ==============================================================================
  MODULE #30: NORTH-POLE RENORMALIZATION ON S³ ⊂ M⁵ & CHEBYSHEV–VON MANGOLDT
  ALL-HORIZON GRAM CLOSURE BRIDGE (FRENTE B)

  Title: North-Pole Renormalization and Chebyshev–Gram Closure Bridge
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - `renormalized_margin_pos_iff_budget`:
    For `μ_inf > 0`, `0 < 1 - D_prime / μ_inf ↔ D_prime < μ_inf`.
  - `north_pole_continuity_implies_uniform_chebyshev_budget`:
    Combining Module #29 (`compact_horizon_pos_implies_uniform_margin`):
    If the renormalized margin `μ_tilde` is continuous and strictly positive on
    the compact arc `[0, π]` (including the North Pole `π` = `L → ∞`) and satisfies
    `μ_tilde (stereographicHorizon L) = 1 - D_prime L / μ_inf L` for all `L > 0`,
    then there exists a UNIFORM gap `c > 0` such that
      `∀ L > 0, D_prime L ≤ (1 - c) * μ_inf L`!
  - `north_pole_continuity_implies_all_horizon_gram_closure`:
    Combining Module #28 (`accumulated_prime_downdates_preserve_gram`) and
    Module #29 (`compact_horizon_pos_implies_uniform_margin`):
    Continuity and strict positivity of `μ_tilde` at the North Pole `π`
    UNCONDITIONALLY yields a global Gram factorization `∃ A_L, S_L = A_Lᵀ * A_L`
    for EVERY horizon `L > 0`!
  ==============================================================================
-/

import RiemannDipolar.CompactifiedHorizonManifold5DClosure

open Real Filter Topology Set
open scoped BigOperators Classical Matrix
open PrimeDowndateWeylPerturbationAndGramMargin
open CompactifiedHorizonManifold5DClosure

namespace NorthPoleRenormalizationAndChebyshevBridge

/-- THEOREM I.1 (RENORMALIZED MARGIN POSITIVITY ↔ CHEBYSHEV BUDGET):
    For any strictly positive Archimedean margin `μ_inf > 0`, the renormalized
    margin `1 - D_prime / μ_inf` is strictly positive iff `D_prime < μ_inf`. -/
theorem renormalized_margin_pos_iff_budget {μ_inf D_prime : ℝ} (hμ : 0 < μ_inf) :
    0 < 1 - D_prime / μ_inf ↔ D_prime < μ_inf := by
  constructor
  · intro h
    have h1 : D_prime / μ_inf < 1 := by linarith
    exact (div_lt_one hμ).mp h1
  · intro h
    have h1 : D_prime / μ_inf < 1 := (div_lt_one hμ).mpr h
    linarith

/-- THEOREM I.2 (NORTH-POLE CONTINUITY ON M⁵ → UNIFORM CHEBYSHEV GAP FOR ALL L > 0):
    If `μ_tilde : ℝ → ℝ` is continuous and strictly positive on the compact meridian
    arc `[0, π]` (including the North Pole `π` representing `L = ∞`) and equals
    `1 - D_prime L / μ_inf L` for all `L > 0`, then there exists a uniform constant
    `c > 0` such that `D_prime L ≤ (1 - c) * μ_inf L` for EVERY horizon `L > 0`! -/
theorem north_pole_continuity_implies_uniform_chebyshev_budget
    (μ_inf D_prime μ_tilde : ℝ → ℝ)
    (hμ_pos : ∀ L : ℝ, 0 < L → 0 < μ_inf L)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Set.Icc 0 Real.pi, 0 < μ_tilde θ)
    (hmatch : ∀ L : ℝ, 0 < L → μ_tilde (stereographicHorizon L) = 1 - D_prime L / μ_inf L) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 0 < L → D_prime L ≤ (1 - c) * μ_inf L := by
  rcases compact_horizon_pos_implies_uniform_margin μ_tilde hcont hpos with ⟨c, hc_pos, hc_le⟩
  refine ⟨c, hc_pos, ?_⟩
  intro L hL
  have h1 : c ≤ 1 - D_prime L / μ_inf L := by
    rw [← hmatch L hL]
    exact hc_le L hL
  have h2 : D_prime L / μ_inf L ≤ 1 - c := by linarith
  exact (div_le_iff₀ (hμ_pos L hL)).mp h2

/-- THEOREM I.3 (UNIFIED FRENTE B BRIDGE: NORTH-POLE REGULARITY → ALL-HORIZON GRAM):
    Combining Module #28 (`accumulated_prime_downdates_preserve_gram`) with
    Module #29 (`compact_horizon_pos_implies_uniform_margin`):
    If the renormalized Chebyshev–Weil margin extends continuously and positively
    to the North Pole `π` of `S³ ⊂ M⁵`, then for EVERY horizon `L > 0`, the
    full Weil–Schur operator `W_inf L - ∑ v ∈ F L, c L v • C L v` unconditionally
    admits a global Gram factorization `∃ A, S_L = Aᵀ * A`! -/
theorem north_pole_continuity_implies_all_horizon_gram_closure
    {ι : Type*}
    (dim : ℝ → ℕ)
    (F : ℝ → Finset ι)
    (W_inf : (L : ℝ) → Matrix (Fin (dim L)) (Fin (dim L)) ℝ)
    (c δ : ℝ → ι → ℝ)
    (C : (L : ℝ) → ι → Matrix (Fin (dim L)) (Fin (dim L)) ℝ)
    (μ_inf μ_tilde : ℝ → ℝ)
    (hμ_pos : ∀ L : ℝ, 0 < L → 0 < μ_inf L)
    (hWh : ∀ L : ℝ, 0 < L → (W_inf L).IsHermitian)
    (hCh : ∀ L : ℝ, 0 < L → ∀ v ∈ F L, (C L v).IsHermitian)
    (hc : ∀ L : ℝ, 0 < L → ∀ v ∈ F L, 0 ≤ c L v)
    (hW : ∀ L : ℝ, 0 < L → ∀ x : Fin (dim L) → ℝ,
      μ_inf L * vecNormSq x ≤ dotProduct x ((W_inf L).mulVec x))
    (hC : ∀ L : ℝ, 0 < L → ∀ v ∈ F L, ∀ x : Fin (dim L) → ℝ,
      dotProduct x ((C L v).mulVec x) ≤ δ L v * vecNormSq x)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hpos : ∀ θ ∈ Set.Icc 0 Real.pi, 0 < μ_tilde θ)
    (hmatch : ∀ L : ℝ, 0 < L →
      μ_tilde (stereographicHorizon L) = 1 - (∑ v ∈ F L, c L v * δ L v) / μ_inf L) :
    ∀ L : ℝ, 0 < L →
      ∃ A : Matrix (Fin (dim L)) (Fin (dim L)) ℝ,
        W_inf L - (∑ v ∈ F L, c L v • C L v) = Aᵀ * A := by
  let D_prime : ℝ → ℝ := fun L => ∑ v ∈ F L, c L v * δ L v
  rcases north_pole_continuity_implies_uniform_chebyshev_budget
      μ_inf D_prime μ_tilde hμ_pos hcont hpos hmatch with ⟨gap, hgap_pos, hgap_le⟩
  intro L hL
  have hsum : ∑ v ∈ F L, c L v * δ L v ≤ μ_inf L := by
    have h1 := hgap_le L hL
    have h2 : (1 - gap) * μ_inf L ≤ μ_inf L := by
      nlinarith [hμ_pos L hL]
    exact le_trans h1 h2
  exact accumulated_prime_downdates_preserve_gram (F L) (W_inf L) (c L) (δ L) (C L) (μ_inf L)
    (hWh L hL) (hCh L hL) (hc L hL) (hW L hL) (hC L hL) hsum

end NorthPoleRenormalizationAndChebyshevBridge
