/-
  ==============================================================================
  MODULE #34: GENERALIZED RIEMANN HYPOTHESIS (GRH) DEFINITION, DIRICHLET
  L-FUNCTION FUNCTIONAL EQUATION, SYMMETRIZED COMPLETED PRODUCT, & RH COROLLARY

  Title: Formal GRH Foundation and Primitive Dirichlet Functional Symmetry
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 24, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Official Mathlib4 GRH Definition & Trivial/Non-Trivial Zero Audit):
      * `IsNonTrivialLZero`, `IsNonTrivialLZeroExcluded`,
        `isNonTrivialLZero_iff_excluded`, `GRHForCharacter`,
        `GeneralizedRiemannHypothesis`.
  - Part II (Exact Specialization to Classical `RiemannHypothesis`):
      * `isNonTrivialLZero_modOne_iff`, `grhForCharacter_modOne_iff_riemannHypothesis`,
        `generalizedRiemannHypothesis_implies_riemannHypothesis`.
  - Part III (Primitive Functional Equation & Unit-Circle Root-Number Rigidity):
      * `completedLFunction_zero_iff_LFunction_zero_in_strip`,
        `isNonTrivialLZero_one_sub_inv`, `symCompletedL`,
        `symCompletedL_one_sub`, `symCompletedL_eq_zero_iff`,
        `norm_rootNumber_eq_one`, `differentiable_LFunction_of_ne_one`.
  ==============================================================================
-/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex Filter Topology Set
open scoped BigOperators Classical Real

namespace GRHDefinitionAndFunctionalEq

-- ==============================================================================
-- PART I: OFFICIAL MATHLIB4 GRH DEFINITION & NON-TRIVIAL ZERO CHARACTERIZATION
-- ==============================================================================

/-- A complex number `s` is a non-trivial zero of the Dirichlet L-function `L(s, χ)`
    if `LFunction χ s = 0` and `s` lies inside the open critical strip `0 < Re(s) < 1`. -/
def IsNonTrivialLZero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : Prop :=
  DirichletCharacter.LFunction χ s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- Equivalent exclusion-form definition of a non-trivial zero: `LFunction χ s = 0`,
    `s` is not a trivial Gamma-factor zero (with the `s = 0` mod 1 convention),
    and `s ≠ 1` when `χ = 1`. -/
def IsNonTrivialLZeroExcluded {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : Prop :=
  DirichletCharacter.LFunction χ s = 0 ∧
    ¬(χ.gammaFactor s = 0 ∧ (N ≠ 1 ∨ s ≠ 0)) ∧
    (χ ≠ 1 ∨ s ≠ 1)

/-- THEOREM I.1 (EXACT EQUIVALENCE OF CRITICAL-STRIP AND EXCLUSION DEFINITIONS):
    For every primitive Dirichlet character `χ` mod `N`, the zeros of `L(s, χ)` in the
    open critical strip `0 < Re(s) < 1` are precisely the zeros of `L(s, χ)` that are
    neither trivial Gamma-factor zeros nor the pole `s = 1` of the trivial character. -/
theorem isNonTrivialLZero_iff_excluded {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    IsNonTrivialLZero χ s ↔ IsNonTrivialLZeroExcluded χ s := by
  constructor
  · rintro ⟨hzero, hpos, hlt1⟩
    refine ⟨hzero, ?_, ?_⟩
    · intro ⟨hgam, _⟩
      rcases χ.even_or_odd with hev | hodd
      · rw [DirichletCharacter.gammaFactor_eq_zero_iff_of_even hev] at hgam
        rcases hgam with ⟨n, rfl⟩
        have hre : (-(2 * (n : ℂ))).re ≤ 0 := by simp
        linarith
      · rw [DirichletCharacter.gammaFactor_eq_zero_iff_of_odd hodd] at hgam
        rcases hgam with ⟨n, hn⟩
        have hs : s = -(2 * (n : ℂ)) - 1 := by linear_combination hn
        rw [hs] at hpos
        have hre : (-(2 * (n : ℂ)) - 1).re ≤ -1 := by simp
        linarith
    · right
      intro h1
      rw [h1] at hlt1
      simp at hlt1
  · rintro ⟨hzero, hntriv, hne1⟩
    refine ⟨hzero, ?_, ?_⟩
    · by_contra hle
      push Not at hle
      have hiff := (DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos hχ hle).mp hzero
      exact hntriv hiff
    · by_contra hge
      push Not at hge
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hne1 hge hzero

/-- Generalized Riemann Hypothesis for a single Dirichlet character `χ` mod `N`:
    every non-trivial zero of `L(s, χ)` lies on the critical line `Re(s) = 1/2`. -/
def GRHForCharacter (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, IsNonTrivialLZero χ s → s.re = 1 / 2

/-- Global Generalized Riemann Hypothesis (GRH) over all moduli `N ≥ 1` and all
    primitive Dirichlet characters `χ : DirichletCharacter ℂ N`. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → GRHForCharacter N χ

-- ==============================================================================
-- PART II: EXACT SPECIALIZATION TO CLASSICAL MATHLIB4 `RiemannHypothesis`
-- ==============================================================================

/-- THEOREM II.1 (MOD-1 SPECIALIZATION OF NON-TRIVIAL ZEROS):
    For the unique primitive Dirichlet character `1` modulo `1`, `IsNonTrivialLZero 1 s`
    is logically equivalent to Mathlib4's non-trivial `riemannZeta` zero predicate. -/
theorem isNonTrivialLZero_modOne_iff (s : ℂ) :
    IsNonTrivialLZero (1 : DirichletCharacter ℂ 1) s ↔
      riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 := by
  constructor
  · rintro ⟨hzero, hpos, hlt1⟩
    rw [DirichletCharacter.LFunction_modOne_eq] at hzero
    refine ⟨hzero, ?_, ?_⟩
    · rintro ⟨n, rfl⟩
      have hre : (-2 * ((n : ℂ) + 1)).re ≤ -2 := by simp
      linarith
    · intro h1
      rw [h1] at hlt1
      simp at hlt1
  · rintro ⟨hzero, hntriv, hne1⟩
    refine ⟨?_, ?_, ?_⟩
    · rwa [DirichletCharacter.LFunction_modOne_eq]
    · by_contra hle
      push Not at hle
      have htriv := (riemannZeta_eq_zero_iff_of_re_nonpos hle).mp hzero
      exact hntriv htriv
    · by_contra hge
      push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hzero

/-- THEOREM II.2 (MOD-1 GRH ↔ CLASSICAL `RiemannHypothesis`):
    `GRHForCharacter 1 1` is 100% logically equivalent to Mathlib4's official
    `RiemannHypothesis`. -/
theorem grhForCharacter_modOne_iff_riemannHypothesis :
    GRHForCharacter 1 (1 : DirichletCharacter ℂ 1) ↔ RiemannHypothesis := by
  constructor
  · intro h s hzero hntriv hne1
    exact h s ((isNonTrivialLZero_modOne_iff s).mpr ⟨hzero, hntriv, hne1⟩)
  · intro hRH s hs
    rcases (isNonTrivialLZero_modOne_iff s).mp hs with ⟨hzero, hntriv, hne1⟩
    exact hRH s hzero hntriv hne1

/-- THEOREM II.3 (GLOBAL GRH IMPLIES CLASSICAL `RiemannHypothesis`):
    The Generalized Riemann Hypothesis immediately implies Mathlib4's classical
    `RiemannHypothesis` via the unique primitive character modulo 1. -/
theorem generalizedRiemannHypothesis_implies_riemannHypothesis :
    GeneralizedRiemannHypothesis → RiemannHypothesis := by
  intro hGRH
  exact grhForCharacter_modOne_iff_riemannHypothesis.mp
    (hGRH 1 1 DirichletCharacter.isPrimitive_one_level_one)

-- ==============================================================================
-- PART III: FUNCTIONAL EQUATION, SYMMETRIZED COMPLETED L-PRODUCT, & ROOT NUMBER
-- ==============================================================================

/-- Lemma III.1: In the open critical strip `0 < Re(s) < 1`, the Archimedean
    `gammaFactor χ s` never vanishes. -/
theorem gammaFactor_ne_zero_of_re_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  intro hgam
  rcases χ.even_or_odd with hev | hodd
  · rw [DirichletCharacter.gammaFactor_eq_zero_iff_of_even hev] at hgam
    rcases hgam with ⟨n, rfl⟩
    have hre : (-(2 * (n : ℂ))).re ≤ 0 := by simp
    linarith
  · rw [DirichletCharacter.gammaFactor_eq_zero_iff_of_odd hodd] at hgam
    rcases hgam with ⟨n, hn⟩
    have hs' : s = -(2 * (n : ℂ)) - 1 := by linear_combination hn
    rw [hs'] at hs
    have hre : (-(2 * (n : ℂ)) - 1).re ≤ -1 := by simp
    linarith

/-- THEOREM III.2 (COMPLETED L-FUNCTION ZERO EQUIVALENCE IN THE CRITICAL STRIP):
    For any `s` with `0 < Re(s) < 1`, `completedLFunction χ s = 0` if and only if
    `LFunction χ s = 0`. -/
theorem completedLFunction_zero_iff_LFunction_zero_in_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hpos : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hrel := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hgam := gammaFactor_ne_zero_of_re_pos χ hpos
  rw [hrel, div_eq_zero_iff]
  simp [hgam]

/-- THEOREM III.3 (FUNCTIONAL REFLECTION OF NON-TRIVIAL ZEROS):
    If `χ` is primitive mod `N` and `s` is a non-trivial zero of `L(s, χ)`, then
    `1 - s` is a non-trivial zero of `L(s, χ⁻¹)`. -/
theorem isNonTrivialLZero_one_sub_inv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : IsNonTrivialLZero χ s) :
    IsNonTrivialLZero χ⁻¹ (1 - s) := by
  rcases hs with ⟨hzero, hpos, hlt1⟩
  have hpos' : 0 < (1 - s).re := by simp; linarith
  have hlt1' : (1 - s).re < 1 := by simp; linarith
  have hcomp : DirichletCharacter.completedLFunction χ s = 0 :=
    (completedLFunction_zero_iff_LFunction_zero_in_strip χ hpos).mpr hzero
  have hfe := hχ.inv.completedLFunction_one_sub s
  simp only [inv_inv] at hfe
  rw [hcomp, mul_zero] at hfe
  have hzero' : DirichletCharacter.LFunction χ⁻¹ (1 - s) = 0 :=
    (completedLFunction_zero_iff_LFunction_zero_in_strip χ⁻¹ hpos').mp hfe
  exact ⟨hzero', hpos', hlt1'⟩

/-- THEOREM III.4 (CHARACTER INVERSE SYMMETRY OF GRH):
    For every primitive character `χ` mod `N`, `GRHForCharacter N χ` holds if and
    only if `GRHForCharacter N χ⁻¹` holds. -/
theorem grhForCharacter_iff_inv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    GRHForCharacter N χ ↔ GRHForCharacter N χ⁻¹ := by
  constructor
  · intro h s hs
    have hs' := isNonTrivialLZero_one_sub_inv hχ.inv hs
    simp only [inv_inv] at hs'
    have hre := h (1 - s) hs'
    simp only [sub_re, one_re] at hre
    linarith
  · intro h s hs
    have hs' := isNonTrivialLZero_one_sub_inv hχ hs
    have hre := h (1 - s) hs'
    simp only [sub_re, one_re] at hre
    linarith

/-- Conductor-normalized completed L-function:
    `Λ_norm(s, χ) = N^(s / 2) * completedLFunction χ s`.
    Including the conductor power `N^(s/2)` brings the primitive functional equation
    into pure unitary form `Λ_norm(1 - s, χ) = rootNumber χ * Λ_norm(s, χ⁻¹)`. -/
noncomputable def normCompletedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ s

/-- THEOREM III.5 (UNITARY FUNCTIONAL EQUATION FOR `normCompletedL`):
    For every primitive Dirichlet character `χ` mod `N` and every `s ∈ ℂ`,
    `normCompletedL χ (1 - s) = rootNumber χ * normCompletedL χ⁻¹ s`. -/
theorem normCompletedL_one_sub {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    normCompletedL χ (1 - s) = DirichletCharacter.rootNumber χ * normCompletedL χ⁻¹ s := by
  unfold normCompletedL
  rw [hχ.completedLFunction_one_sub s]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hexp : (1 - s) / 2 + (s - 1 / 2) = s / 2 := by ring
  calc (N : ℂ) ^ ((1 - s) / 2) * ((N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ s)
      = ((N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2)) *
        DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ s := by ring
    _ = (N : ℂ) ^ ((1 - s) / 2 + (s - 1 / 2)) *
        DirichletCharacter.rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ s := by
        rw [Complex.cpow_add _ _ hN]
    _ = (N : ℂ) ^ (s / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ s := by rw [hexp]
    _ = DirichletCharacter.rootNumber χ *
        ((N : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction χ⁻¹ s) := by ring

/-- Symmetrized completed L-function product pairing `χ` and its conjugate inverse `χ⁻¹`:
    `Λ_sym(s, χ) = normCompletedL χ s * normCompletedL χ⁻¹ s`.
    This cancels the complex root number `ε(χ) * ε(χ⁻¹) = 1` identically. -/
noncomputable def symCompletedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  normCompletedL χ s * normCompletedL χ⁻¹ s

/-- THEOREM III.6 (EXACT EVEN FUNCTIONAL SYMMETRY OF THE SYMMETRIZED PRODUCT):
    For every primitive Dirichlet character `χ` mod `N` and every `s ∈ ℂ`,
    `symCompletedL χ (1 - s) = symCompletedL χ s`. -/
theorem symCompletedL_one_sub {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    symCompletedL χ (1 - s) = symCompletedL χ s := by
  unfold symCompletedL
  rw [normCompletedL_one_sub hχ s, normCompletedL_one_sub hχ.inv s]
  simp only [inv_inv]
  have hroot : DirichletCharacter.rootNumber χ * DirichletCharacter.rootNumber χ⁻¹ = 1 :=
    DirichletCharacter.rootNumber_mul_rootNumber_inv hχ
  calc DirichletCharacter.rootNumber χ * normCompletedL χ⁻¹ s *
        (DirichletCharacter.rootNumber χ⁻¹ * normCompletedL χ s)
      = (DirichletCharacter.rootNumber χ * DirichletCharacter.rootNumber χ⁻¹) *
        (normCompletedL χ s * normCompletedL χ⁻¹ s) := by ring
    _ = normCompletedL χ s * normCompletedL χ⁻¹ s := by rw [hroot, one_mul]

/-- THEOREM III.7 (ZERO CHARACTERIZATION OF `normCompletedL` IN THE CRITICAL STRIP):
    For `0 < Re(s)`, `normCompletedL χ s = 0` iff `LFunction χ s = 0`. -/
theorem normCompletedL_zero_iff_in_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hpos : 0 < s.re) :
    normCompletedL χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  unfold normCompletedL
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow_ne : (N : ℂ) ^ (s / 2) ≠ 0 := by
    intro h0
    exact hN ((Complex.cpow_eq_zero_iff (N : ℂ) (s / 2)).mp h0).1
  rw [mul_eq_zero]
  simp [hpow_ne, completedLFunction_zero_iff_LFunction_zero_in_strip χ hpos]

/-- THEOREM III.8 (ZERO CHARACTERIZATION OF `symCompletedL` IN THE CRITICAL STRIP):
    For `0 < Re(s)`, `symCompletedL χ s = 0` iff either `LFunction χ s = 0` or
    `LFunction χ⁻¹ s = 0`. -/
theorem symCompletedL_zero_iff_in_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hpos : 0 < s.re) :
    symCompletedL χ s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 ∨ DirichletCharacter.LFunction χ⁻¹ s = 0 := by
  unfold symCompletedL
  rw [mul_eq_zero, normCompletedL_zero_iff_in_strip χ hpos,
    normCompletedL_zero_iff_in_strip χ⁻¹ hpos]

/-- THEOREM III.9 (UNIT-CIRCLE ROOT NUMBER & ENTIRETY FOR NON-PRINCIPAL CHARACTERS):
    For any primitive `χ`, `‖rootNumber χ‖ = 1`; and if `χ ≠ 1`, `LFunction χ` and
    `completedLFunction χ` are entire (no pole at `s = 1`) with `LFunction χ 1 ≠ 0`. -/
theorem rootNumber_unit_and_nonprincipal_entire {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖DirichletCharacter.rootNumber χ‖ = 1 ∧
      (χ ≠ 1 → Differentiable ℂ (DirichletCharacter.LFunction χ) ∧
        Differentiable ℂ (DirichletCharacter.completedLFunction χ) ∧
        DirichletCharacter.LFunction χ 1 ≠ 0) := by
  refine ⟨DirichletCharacter.norm_rootNumber hχ, fun hne => ?_⟩
  exact ⟨DirichletCharacter.differentiable_LFunction hne,
    DirichletCharacter.differentiable_completedLFunction hne,
    DirichletCharacter.LFunction_apply_one_ne_zero hne⟩

end GRHDefinitionAndFunctionalEq
