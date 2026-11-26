/-
  ==============================================================================
  MODULE #35: TWISTED DIPOLAR SIEVE, CHARACTER ORTHOGONALITY, TWISTED
  CLIFFORD–VON MANGOLDT COUPLING, & SPECTRAL BRIDGE FOR DIRICHLET L-FUNCTIONS

  Title: Twisted Dipolar Prime Sieve and Spectral Bridge for GRH
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 24, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Twisted von Mangoldt Weight & Unit-Circle Norm Bounds):
      * `twistedVonMangoldt`, `norm_twistedVonMangoldt_le`,
        `twistedVonMangoldt_modOne`, `twistedVonMangoldt_sum_norm_le`.
  - Part II (Dirichlet Character Orthogonality & Neutrality on ZMod N):
      * `dirichlet_character_sum_neutrality`, `twisted_unit_norm_eq_one`.
  - Part III (Twisted Clifford–von Mangoldt Coupling & Critical-Line Nullity):
      * `twistedCliffordCoupling`, `twistedCliffordCoupling_eq_zero_on_critical_line`,
        `twistedCliffordCoupling_odd_in_beta`, `twistedCliffordCoupling_modOne_eq`.
  - Part IV (Twisted Spectral Bridge Target ↔ GRHForCharacter):
      * `twistedMonopolarDrift`, `twistedMonopolarDrift_eq_zero_iff_half`,
        `TwistedSpectralBridgeTarget`, `twistedSpectralBridgeTarget_iff_grhForCharacter`.
  ==============================================================================
-/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannDipolar.GRHDefinitionAndFunctionalEq
import RiemannDipolar.CliffordSieveAdelicClosure

open Complex Real Filter Topology Set
open scoped BigOperators Classical
open GRHDefinitionAndFunctionalEq CliffordSieveAdelicClosure

namespace TwistedDipolarSieveGRH

-- ==============================================================================
-- PART I: TWISTED VON MANGOLDT WEIGHT & UNIT-CIRCLE NORM BOUNDS
-- ==============================================================================

/-- Twisted von Mangoldt arithmetic weight `Λ_χ(n) = χ(n) · Λ(n) ∈ ℂ`
    weighting prime powers `p^k` by the Dirichlet character phase `χ(p^k)`. -/
noncomputable def twistedVonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- THEOREM I.1 (NORM DOMINANCE BY UNTWISTED VON MANGOLDT):
    For every modulus `N`, Dirichlet character `χ`, and `n ∈ ℕ`,
    `‖χ(n) Λ(n)‖ ≤ Λ(n)`. -/
theorem norm_twistedVonMangoldt_le {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖twistedVonMangoldt χ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  unfold twistedVonMangoldt
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
  nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]

/-- THEOREM I.2 (MOD-1 REDUCTION TO CLASSICAL VON MANGOLDT):
    For the unique Dirichlet character `χ` modulo `1`, `twistedVonMangoldt χ n`
    reduces identically to the classical von Mangoldt weight `Λ(n)`. -/
theorem twistedVonMangoldt_modOne (χ : DirichletCharacter ℂ 1) (n : ℕ) :
    twistedVonMangoldt χ n = (ArithmeticFunction.vonMangoldt n : ℂ) := by
  unfold twistedVonMangoldt
  have h1 : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h1, map_one, one_mul]

/-- THEOREM I.3 (TRIANGLE-INEQUALITY BOUND FOR TWISTED CHEBYSHEV SUMS):
    For any cutoff `N_max`, the twisted Chebyshev sum is bounded in modulus by
    the classical Chebyshev sum `ψ(N_max) = ∑_{n < N_max} Λ(n)`. -/
theorem twistedVonMangoldt_sum_norm_le {N : ℕ} (χ : DirichletCharacter ℂ N) (N_max : ℕ) :
    ‖∑ n ∈ Finset.range N_max, twistedVonMangoldt χ n‖ ≤
      ∑ n ∈ Finset.range N_max, ArithmeticFunction.vonMangoldt n := by
  calc ‖∑ n ∈ Finset.range N_max, twistedVonMangoldt χ n‖
      ≤ ∑ n ∈ Finset.range N_max, ‖twistedVonMangoldt χ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N_max, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum fun n _ => norm_twistedVonMangoldt_le χ n

-- ==============================================================================
-- PART II: DIRICHLET CHARACTER ORTHOGONALITY & UNIT-CIRCLE RIGIDITY
-- ==============================================================================

/-- THEOREM II.1 (EXACT DIPOLAR NEUTRALITY OF NON-PRINCIPAL CHARACTERS ON ZMod N):
    Every non-principal Dirichlet character `χ ≠ 1` sums identically to zero over
    a complete residue system modulo `N`: `∑_{a ∈ ZMod N} χ(a) = 0`. -/
theorem dirichlet_character_sum_neutrality {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∑ a : ZMod N, χ a = 0 :=
  χ.sum_eq_zero_of_ne_one hχ

/-- THEOREM II.2 (UNIT-CIRCLE CHARACTER NORM ON COPRIME RESIDUE CLASSES):
    For every unit `u : (ZMod N)ˣ`, `‖χ u‖ = 1` (since `χ u` is a root of unity). -/
theorem twisted_unit_norm_eq_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    ‖χ (u : ZMod N)‖ = 1 := by
  have h1 : ‖χ (u : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (u : ZMod N)
  have h2 : ‖χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N)‖ ≤ 1 :=
    DirichletCharacter.norm_le_one χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N)
  have hmul : χ (u : ZMod N) * χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hnorm_mul : ‖χ (u : ZMod N)‖ * ‖χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N)‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  nlinarith [norm_nonneg (χ (u : ZMod N)), norm_nonneg (χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N))]

-- ==============================================================================
-- PART III: TWISTED CLIFFORD–VON MANGOLDT COUPLING & CRITICAL-LINE NULLITY
-- ==============================================================================

/-- Twisted Clifford–von Mangoldt monopolar coupling for a Dirichlet character `χ`:
    `C_χ(β, γ; N_max) = ∑_{2 ≤ n < N_max} χ(n) Λ(n) e^{-½ ln n} cos(γ ln n) sinh((β - ½) ln n)`. -/
noncomputable def twistedCliffordCoupling {N : ℕ} (χ : DirichletCharacter ℂ N)
    (β γ : ℝ) (N_max : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 2 N_max,
    twistedVonMangoldt χ n *
      ((Real.exp (-(1 / 2) * Real.log (n : ℝ)) *
        Real.cos (γ * Real.log (n : ℝ)) *
        Real.sinh ((β - 1 / 2) * Real.log (n : ℝ)) : ℝ) : ℂ)

/-- THEOREM III.1 (EXACT CRITICAL-LINE NULLITY FOR EVERY DIRICHLET CHARACTER):
    On the Clifford equator `β = 1/2`, the twisted Clifford–von Mangoldt coupling
    vanishes identically for EVERY modulus `N`, character `χ`, frequency `γ`, and cutoff `N_max`. -/
theorem twistedCliffordCoupling_eq_zero_on_critical_line {N : ℕ}
    (χ : DirichletCharacter ℂ N) (γ : ℝ) (N_max : ℕ) :
    twistedCliffordCoupling χ (1 / 2) γ N_max = 0 := by
  unfold twistedCliffordCoupling
  apply Finset.sum_eq_zero
  intro n _
  simp [Real.sinh_zero]

/-- THEOREM III.2 (EXACT ANTISYMMETRY UNDER FUNCTIONAL REFLECTION `β ↔ 1 - β`):
    Reflecting across the critical line negates the twisted Clifford–von Mangoldt
    coupling identically for every Dirichlet character `χ`. -/
theorem twistedCliffordCoupling_odd_in_beta {N : ℕ}
    (χ : DirichletCharacter ℂ N) (β γ : ℝ) (N_max : ℕ) :
    twistedCliffordCoupling χ (1 - β) γ N_max =
      -twistedCliffordCoupling χ β γ N_max := by
  unfold twistedCliffordCoupling
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hsub : (1 - β - 1 / 2) * Real.log (n : ℝ) = -((β - 1 / 2) * Real.log (n : ℝ)) := by ring
  rw [hsub, Real.sinh_neg]
  push_cast
  ring

/-- THEOREM III.3 (MOD-1 SPECIALIZATION TO UNTWISTED CLIFFORD–VON MANGOLDT COUPLING):
    For `N = 1`, `twistedCliffordCoupling` coincides with the real-embedded
    `cliffordVonMangoldtCoupling` of Module #22. -/
theorem twistedCliffordCoupling_modOne_eq (χ : DirichletCharacter ℂ 1)
    (β γ : ℝ) (N_max : ℕ) :
    twistedCliffordCoupling χ β γ N_max =
      (cliffordVonMangoldtCoupling β γ N_max : ℂ) := by
  unfold twistedCliffordCoupling cliffordVonMangoldtCoupling
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [twistedVonMangoldt_modOne χ n]
  push_cast
  ring

-- ==============================================================================
-- PART IV: TWISTED SPECTRAL BRIDGE EQUIVALENCE ↔ `GRHForCharacter`
-- ==============================================================================

/-- Off-line hyperbolic radial drift amplitude `|sinh((Re(s) - 1/2) · τ)|`
    at logarithmic scale `τ > 0`. -/
noncomputable def twistedMonopolarDrift (s : ℂ) (τ : ℝ) : ℝ :=
  |Real.sinh ((s.re - 1 / 2) * τ)|

/-- THEOREM IV.1 (RADIAL DRIFT VANISHING ↔ CRITICAL LINE):
    For any `τ > 0`, `twistedMonopolarDrift s τ = 0` iff `s.re = 1/2`. -/
theorem twistedMonopolarDrift_eq_zero_iff_half (s : ℂ) (τ : ℝ) (hτ : 0 < τ) :
    twistedMonopolarDrift s τ = 0 ↔ s.re = 1 / 2 := by
  unfold twistedMonopolarDrift
  rw [abs_eq_zero]
  constructor
  · intro h
    have hmul : (s.re - 1 / 2) * τ = 0 := Real.sinh_eq_zero.mp h
    rcases mul_eq_zero.mp hmul with h1 | h2
    · linarith
    · linarith
  · intro h
    rw [h]
    simp [Real.sinh_zero]

/-- Twisted Spectral Bridge Target for a Dirichlet character `χ` mod `N`:
    every non-trivial zero of `L(s, χ)` has identically zero monopolar radial drift
    across all logarithmic scales `τ > 0`. -/
def TwistedSpectralBridgeTarget {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, IsNonTrivialLZero χ s → ∀ τ : ℝ, 0 < τ → twistedMonopolarDrift s τ = 0

/-- THEOREM IV.2 (EXACT BIDIRECTIONAL EQUIVALENCE: TWISTED SPECTRAL BRIDGE ↔ GRH):
    For every modulus `N ≥ 1` and Dirichlet character `χ` mod `N`,
    `TwistedSpectralBridgeTarget χ` is 100% logically equivalent to `GRHForCharacter N χ`. -/
theorem twistedSpectralBridgeTarget_iff_grhForCharacter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    TwistedSpectralBridgeTarget χ ↔ GRHForCharacter N χ := by
  constructor
  · intro h s hs
    exact (twistedMonopolarDrift_eq_zero_iff_half s 1 zero_lt_one).mp (h s hs 1 zero_lt_one)
  · intro hGRH s hs τ hτ
    exact (twistedMonopolarDrift_eq_zero_iff_half s τ hτ).mpr (hGRH s hs)

end TwistedDipolarSieveGRH
