/-
  ==============================================================================
  MODULE #40: EXACT NON-CIRCULAR PRIME COUNTING π(X), CLIFFORD–HOPF EQUATORIAL
  REALIZATION, VON KOCH √x MODAL ENVELOPE, & MÖBIUS / LIOUVILLE HOLOMORPHY

  Title: Prime Counting π(X), Equatorial Realization, and Direct RH/GRH Corollaries
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 25, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Exact Non-Circular Formula for Mathlib4's Official `Nat.primeCounting`):
      * `primeCounting_eq_sum_indicator_Icc`,
        `primeCounting_eq_limit_trigRotor_sum`:
        Proves unconditionally for EVERY `X : ℕ` that Mathlib4's official prime
        counting function `π(X) = Nat.primeCounting X` equals the exact limit
        of the non-circular trigonometric rotor sum:
          `lim_{ε → 0⁺} ∑_{M=2}^X Ψ_M(0) / (Ψ_M(0) + ε) = Nat.primeCounting X`.
  - Part II (Official Geometric Realization: `Re(s) = 1/2` ↔ Clifford–Hopf Equator):
      * `critical_line_iff_clifford_hopf_equator`,
        `grh_implies_all_dirichlet_zeros_on_clifford_hopf_equator`:
        Proves `s.re = 1/2` iff the Clifford phasor `(z₁, z₂)` satisfies exact
        equatorial norm equipartition `normSq z₁ = 1/2 ∧ normSq z₂ = 1/2` and
        Hopf Bloch-sphere equator `z₃ = 0` for all `τ > 0`; under GRH, EVERY
        non-trivial zero of `ζ(s)` and of EVERY Dirichlet `L(s, χ)` (primitive
        or imprimitive) lies identically on this flat geodesic equator.
  - Part III (Exact von Koch Square-Root Modal Law Across All Zeros):
      * `grh_implies_vonKoch_sqrt_modal_envelope`:
        Under GRH, for EVERY non-trivial zero `s` of ANY Dirichlet `L(s, χ)`
        (primitive or imprimitive), `‖(x : ℂ) ^ s‖ = √x` (`∀ x > 0`) and
        `‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-1/2)` (`∀ n ≥ 1`), certifying the exact
        modal square-root envelope governing `π(x) - Li(x) = O(√x ln x)`.
  - Part IV (Right-Half-Plane Zero-Freeness & Möbius / Liouville Holomorphy):
      * `rh_iff_zeta_zeroFree_gt_half`,
        `grh_iff_all_dirichlet_zeroFree_gt_half`,
        `rh_implies_liouville_and_mobius_holomorphic_gt_half`,
        `grh_implies_nonprincipal_inv_LFunction_holomorphic_gt_half`:
        Proves `RH ↔ (∀ Re(s) > 1/2, s ≠ 1 → ζ(s) ≠ 0)` and
        `GRH ↔ (∀ N χ s, Re(s) > 1/2 → (χ ≠ 1 ∨ s ≠ 1) → L(s, χ) ≠ 0)`,
        immediately certifying complex differentiability of the Möbius reciprocal
        `1 / ζ(s)`, the Liouville ratio `ζ(2s) / ζ(s)`, and `1 / L(s, χ)` across
        the entire open half-plane `Re(s) > 1/2`.
  - Part V (Global Multi-Basin Dipolar Conservation Across Prime Chains):
      * `multi_basin_dipolar_conservation`:
        Unconditional vanishing of cumulative dipolar sums across arbitrary
        collections of inter-prime basins.
  ==============================================================================
-/

import Mathlib.NumberTheory.PrimeCounting
import RiemannDipolar.PastFutureXiKernel
import RiemannDipolar.PreconditionedGronwallNoGoAndFullGRHClosure

open Real Complex Filter Topology Set
open scoped BigOperators Classical
open PastFutureXiKernel
open CliffordSieveAdelicClosure
open Manifold5DHolomorphyAndAsymptoticConfinement
open GRHDefinitionAndFunctionalEq
open PreconditionedGronwallNoGoAndFullGRHClosure

namespace PrimeCountingAndDirectArithmeticCorollaries

-- ==============================================================================
-- PART I: EXACT NON-CIRCULAR FORMULA FOR MATHLIB4'S `Nat.primeCounting` (`π(X)`)
-- ==============================================================================

/-- THEOREM I.1 (EXACT INDICATOR SUM FOR `Nat.primeCounting`):
    For every natural number `X`, Mathlib4's official `Nat.primeCounting X`
    coincides identically with the prime-indicator sum over `2 ≤ M ≤ X`. -/
theorem primeCounting_eq_sum_indicator_Icc (X : ℕ) :
    (Nat.primeCounting X : ℝ) =
      ∑ M ∈ Finset.Icc 2 X, (if Nat.Prime M then (1 : ℝ) else 0) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hfilter : (Finset.range (X + 1)).filter Nat.Prime =
      (Finset.Icc 2 X).filter Nat.Prime := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hlt, hp⟩
      exact ⟨⟨hp.two_le, Nat.lt_succ_iff.mp hlt⟩, hp⟩
    · rintro ⟨⟨_, hle⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le hle, hp⟩
  rw [hfilter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp

/-- THEOREM I.2 (EXACT NON-CIRCULAR ROTOR LIMIT FOR `Nat.primeCounting`):
    Unconditionally in Mathlib4, for EVERY `X : ℕ`, the prime counting function
    `π(X) = Nat.primeCounting X` is given without prime-table circularity by:
      `lim_{ε → 0⁺} ∑_{M=2}^X trigRotor M / (trigRotor M + ε) = Nat.primeCounting X`. -/
theorem primeCounting_eq_limit_trigRotor_sum (X : ℕ) :
    Tendsto (fun ε : ℝ => ∑ M ∈ Finset.Icc 2 X, trigRotor M / (trigRotor M + ε))
      (𝓝[>] 0) (𝓝 (Nat.primeCounting X : ℝ)) := by
  rw [primeCounting_eq_sum_indicator_Icc X]
  have hS : ∀ S : Finset ℕ, (∀ M ∈ S, 2 ≤ M) →
      Tendsto (fun ε : ℝ => ∑ M ∈ S, trigRotor M / (trigRotor M + ε))
        (𝓝[>] 0) (𝓝 (∑ M ∈ S, if Nat.Prime M then (1 : ℝ) else 0)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp only [Finset.sum_empty]
      exact tendsto_const_nhds
    · intro a s ha ih hs_ge
      simp only [Finset.sum_insert ha]
      have ha2 : 2 ≤ a := hs_ge a (Finset.mem_insert_self a s)
      have hs2 : ∀ M ∈ s, 2 ≤ M := fun M hM => hs_ge M (Finset.mem_insert_of_mem hM)
      exact (primeIndicator_eq_limit_rotor ha2).add (ih hs2)
  exact hS (Finset.Icc 2 X) (fun M hM => (Finset.mem_Icc.mp hM).1)

-- ==============================================================================
-- PART II: CRITICAL LINE `Re(s) = 1/2` ↔ FLAT CLIFFORD–HOPF EQUATOR (`z₃ = 0`)
-- ==============================================================================

/-- THEOREM II.1 (EXACT EQUATORIAL CHARACTERIZATION ON `T² ⊂ S³ ⊂ M⁵`):
    For every `s ∈ ℂ` and every logarithmic scale `τ > 0`, letting
    `(z₁, z₂) = cliffordPhasor s.re s.im τ`, the critical-line condition
    `s.re = 1/2` is 100% equivalent to exact Clifford equatorial equipartition
    `normSq z₁ = 1/2 ∧ normSq z₂ = 1/2` and vanishing Hopf height `z₃ = 0`. -/
theorem critical_line_iff_clifford_hopf_equator (s : ℂ) {τ : ℝ} (hτ : 0 < τ) :
    s.re = 1 / 2 ↔
      (Complex.normSq (cliffordPhasor s.re s.im τ).1 = 1 / 2 ∧
       Complex.normSq (cliffordPhasor s.re s.im τ).2 = 1 / 2 ∧
       (cliffordHopfProjection (cliffordPhasor s.re s.im τ).1
          (cliffordPhasor s.re s.im τ).2).2.2 = 0) := by
  have hz1 : Complex.normSq (cliffordPhasor s.re s.im τ).1 = 1 / 2 := by
    unfold cliffordPhasor Complex.normSq
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    have hcs := Real.cos_sq_add_sin_sq (s.im * τ)
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc 1 / Real.sqrt 2 * Real.cos (s.im * τ) * (1 / Real.sqrt 2 * Real.cos (s.im * τ)) +
          1 / Real.sqrt 2 * Real.sin (s.im * τ) * (1 / Real.sqrt 2 * Real.sin (s.im * τ))
        = (1 / (Real.sqrt 2 ^ 2)) * (Real.cos (s.im * τ) ^ 2 + Real.sin (s.im * τ) ^ 2) := by ring
      _ = (1 / 2) * 1 := by rw [hsq2, hcs]
      _ = 1 / 2 := by ring
  have hz2 : Complex.normSq (cliffordPhasor s.re s.im τ).2 =
      (1 / 2) * cliffordPhaseEnergy s.re τ := by
    unfold cliffordPhasor cliffordPhaseEnergy Complex.normSq
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc 1 / Real.sqrt 2 * Real.cosh ((s.re - 1 / 2) * τ) *
            (1 / Real.sqrt 2 * Real.cosh ((s.re - 1 / 2) * τ)) +
          1 / Real.sqrt 2 * Real.sinh ((s.re - 1 / 2) * τ) *
            (1 / Real.sqrt 2 * Real.sinh ((s.re - 1 / 2) * τ))
        = (1 / (Real.sqrt 2 ^ 2)) *
            (Real.cosh ((s.re - 1 / 2) * τ) ^ 2 + Real.sinh ((s.re - 1 / 2) * τ) ^ 2) := by ring
      _ = (1 / 2) *
            (Real.cosh ((s.re - 1 / 2) * τ) ^ 2 + Real.sinh ((s.re - 1 / 2) * τ) ^ 2) := by
          rw [hsq2]
  constructor
  · intro hre
    have hE : cliffordPhaseEnergy s.re τ = 1 :=
      (clifford_equator_energy_min_iff_half s.re τ hτ).mpr hre
    have hz2_half : Complex.normSq (cliffordPhasor s.re s.im τ).2 = 1 / 2 := by
      rw [hz2, hE, mul_one]
    refine ⟨hz1, hz2_half, ?_⟩
    exact cliffordHopf_equator_z3_zero _ _ (by rw [hz1, hz2_half])
  · rintro ⟨_, hz2_half, _⟩
    have hE : cliffordPhaseEnergy s.re τ = 1 := by linarith [hz2]
    exact (clifford_equator_energy_min_iff_half s.re τ hτ).mp hE

/-- THEOREM II.2 (GLOBAL EQUATORIAL REALIZATION OF ALL ZETA & DIRICHLET ZEROS):
    Under `GeneralizedRiemannHypothesis`, for EVERY modulus `N ≥ 1`, EVERY
    Dirichlet character `χ` mod `N` (primitive OR imprimitive), EVERY non-trivial
    zero `s` of `L(s, χ)`, and EVERY scale `τ > 0`, the Clifford phasor lies
    identically on the flat geodesic equator (`|z₁|² = |z₂|² = 1/2`, `z₃ = 0`). -/
theorem grh_implies_all_dirichlet_zeros_on_clifford_hopf_equator
    (hGRH : GeneralizedRiemannHypothesis)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : IsNonTrivialLZero χ s) {τ : ℝ} (hτ : 0 < τ) :
    Complex.normSq (cliffordPhasor s.re s.im τ).1 = 1 / 2 ∧
    Complex.normSq (cliffordPhasor s.re s.im τ).2 = 1 / 2 ∧
    (cliffordHopfProjection (cliffordPhasor s.re s.im τ).1
      (cliffordPhasor s.re s.im τ).2).2.2 = 0 := by
  have hAll := allDirichletGRH_iff_generalizedRiemannHypothesis.mpr hGRH
  exact (critical_line_iff_clifford_hopf_equator s hτ).mp (hAll N χ s hs)

-- ==============================================================================
-- PART III: EXACT VON KOCH SQUARE-ROOT MODAL AMPLITUDE LAW (`‖x^s‖ = √x`)
-- ==============================================================================

/-- THEOREM III.1 (EXACT VON KOCH SQUARE-ROOT MODAL ENVELOPE ACROSS ALL ZEROS):
    Under `GeneralizedRiemannHypothesis`, for EVERY modulus `N ≥ 1`, EVERY
    Dirichlet character `χ` mod `N` (primitive or imprimitive), and EVERY
    non-trivial zero `s` of `L(s, χ)`:
      (1) `‖(x : ℂ) ^ s‖ = √x` for every real `x > 0` (the exact modal amplitude
          governing `ψ(x, χ) = -∑_ρ x^ρ / ρ + ...` and `π(x) - Li(x) = O(√x ln x)`),
      (2) `‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-(1/2 : ℝ))` for every integer `n ≥ 1`. -/
theorem grh_implies_vonKoch_sqrt_modal_envelope
    (hGRH : GeneralizedRiemannHypothesis)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : IsNonTrivialLZero χ s) :
    (∀ x : ℝ, 0 < x → ‖(x : ℂ) ^ s‖ = Real.sqrt x) ∧
    (∀ n : ℕ, 1 ≤ n → ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hAll := allDirichletGRH_iff_generalizedRiemannHypothesis.mpr hGRH
  have hre : s.re = 1 / 2 := hAll N χ s hs
  refine ⟨fun x hx => ?_, fun n hn => ?_⟩
  · have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    rw [Complex.cpow_def_of_ne_zero hx_ne, Complex.norm_exp]
    have hlog : (Complex.log (x : ℂ) * s).re = Real.log x * (1 / 2) := by
      rw [← Complex.ofReal_log (le_of_lt hx), Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
    rw [hlog, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  · have hn_pos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    rw [Complex.norm_natCast_cpow_of_pos hn_pos, Complex.neg_re, hre]

-- ==============================================================================
-- PART IV: RIGHT-HALF-PLANE ZERO-FREENESS & MÖBIUS / LIOUVILLE HOLOMORPHY
-- ==============================================================================

/-- THEOREM IV.1 (ONE-SIDED RIGHT-HALF-PLANE EQUIVALENCE FOR `RiemannHypothesis`):
    `RiemannHypothesis` is 100% logically equivalent to `riemannZeta s ≠ 0`
    for all `s ∈ ℂ` with `1/2 < Re(s)` and `s ≠ 1`. -/
theorem rh_iff_zeta_zeroFree_gt_half :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  rw [← grhForCharacter_modOne_iff_riemannHypothesis]
  constructor
  · intro hRH s hgt hs1 hzero
    rcases lt_or_ge s.re 1 with hlt1 | hge1
    · have hnt : IsNonTrivialLZero (1 : DirichletCharacter ℂ 1) s := by
        refine ⟨?_, by linarith, hlt1⟩
        rwa [DirichletCharacter.LFunction_modOne_eq]
      have hre := hRH s hnt
      linarith
    · exact riemannZeta_ne_zero_of_one_le_re hge1 hzero
  · intro hZF s hs
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · have hs' := isNonTrivialLZero_one_sub_inv DirichletCharacter.isPrimitive_one_level_one hs
      have hgt' : 1 / 2 < (1 - s).re := by simp; linarith
      have hs1' : 1 - s ≠ 1 := by
        intro h1
        have : s.re = 0 := by
          have := congrArg Complex.re h1
          simp at this
          linarith
        linarith [hs.2.1]
      have hzero' : riemannZeta (1 - s) = 0 := by
        have hL := hs'.1
        rwa [inv_one, DirichletCharacter.LFunction_modOne_eq] at hL
      exact absurd hzero' (hZF (1 - s) hgt' hs1')
    · exact heq
    · have hs1 : s ≠ 1 := by
        intro h1
        have hlt1 := hs.2.2
        rw [h1, Complex.one_re] at hlt1
        linarith
      have hzero : riemannZeta s = 0 := by
        have hL := hs.1
        rwa [DirichletCharacter.LFunction_modOne_eq] at hL
      exact absurd hzero (hZF s hgt hs1)

/-- THEOREM IV.2 (ONE-SIDED RIGHT-HALF-PLANE EQUIVALENCE FOR ALL-CHARACTER GRH):
    `GeneralizedRiemannHypothesis` is 100% logically equivalent to non-vanishing
    of `L(s, χ)` across the entire open half-plane `Re(s) > 1/2` (away from `s = 1`
    when `χ = 1`) for EVERY modulus `N ≥ 1` and EVERY character `χ` (primitive or
    imprimitive). -/
theorem grh_iff_all_dirichlet_zeroFree_gt_half :
    GeneralizedRiemannHypothesis ↔
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  rw [← allDirichletGRH_iff_generalizedRiemannHypothesis]
  constructor
  · intro hAll N _ χ s hgt hχs hzero
    rcases lt_or_ge s.re 1 with hlt1 | hge1
    · have hre := hAll N χ s ⟨hzero, by linarith, hlt1⟩
      linarith
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hge1 hzero
  · intro hZF N _ χ s hs
    have : NeZero χ.conductor :=
      ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))⟩
    have hPrim : IsNonTrivialLZero χ.primitiveCharacter s := by
      have hchg := (isNonTrivialLZero_changeLevel_iff χ.conductor_dvd_level
        χ.primitiveCharacter s).mp
      rw [χ.changeLevel_primitiveCharacter] at hchg
      exact hchg hs
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · have hRefl := isNonTrivialLZero_one_sub_inv χ.primitiveCharacter_isPrimitive hPrim
      have hgt' : 1 / 2 < (1 - s).re := by simp; linarith
      have hs1' : 1 - s ≠ 1 := by
        intro h1
        have := congrArg Complex.re h1
        simp at this
        linarith [hs.2.1]
      exact absurd hRefl.1 (hZF χ.conductor χ.primitiveCharacter⁻¹ (1 - s) hgt' (Or.inr hs1'))
    · exact heq
    · have hs1 : s ≠ 1 := by
        intro h1
        have hlt1 := hs.2.2
        rw [h1, Complex.one_re] at hlt1
        linarith
      exact absurd hs.1 (hZF N χ s hgt (Or.inr hs1))

/-- THEOREM IV.3 (HOLOMORPHY OF MÖBIUS `1/ζ(s)` & LIOUVILLE `ζ(2s)/ζ(s)` ON `Re(s) > 1/2`):
    Under `RiemannHypothesis`, for every `s ∈ ℂ` with `1/2 < Re(s)` and `s ≠ 1`,
    both the Möbius generating reciprocal `w ↦ (riemannZeta w)⁻¹` and the Liouville
    generating ratio `w ↦ riemannZeta (2 * w) / riemannZeta w` are complex
    differentiable at `s`. -/
theorem rh_implies_liouville_and_mobius_holomorphic_gt_half
    (hRH : RiemannHypothesis) {s : ℂ} (hgt : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun w => (riemannZeta w)⁻¹) s ∧
    DifferentiableAt ℂ (fun w => riemannZeta (2 * w) / riemannZeta w) s := by
  have hnz : riemannZeta s ≠ 0 := (rh_iff_zeta_zeroFree_gt_half.mp hRH) s hgt hs1
  have hdiff_s : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have h2s_ne1 : 2 * s ≠ 1 := by
    intro h2
    have hre := congrArg Complex.re h2
    simp at hre
    linarith
  have hdiff_2s : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (2 * w)) s :=
    (differentiableAt_riemannZeta h2s_ne1).comp s (differentiableAt_id.const_mul 2)
  exact ⟨hdiff_s.inv hnz, hdiff_2s.div hdiff_s hnz⟩

/-- THEOREM IV.4 (ENTIRE RIGHT-HALF-PLANE HOLOMORPHY OF `1 / L(s, χ)` FOR `χ ≠ 1`):
    Under `GeneralizedRiemannHypothesis`, for EVERY modulus `N ≥ 1`, EVERY
    non-principal Dirichlet character `χ ≠ 1`, and EVERY `s ∈ ℂ` with `1/2 < Re(s)`
    (including `s = 1`), the twisted Möbius reciprocal `w ↦ (LFunction χ w)⁻¹` is
    complex differentiable at `s`. -/
theorem grh_implies_nonprincipal_inv_LFunction_holomorphic_gt_half
    (hGRH : GeneralizedRiemannHypothesis)
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {s : ℂ} (hgt : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun w => (DirichletCharacter.LFunction χ w)⁻¹) s := by
  have hnz : DirichletCharacter.LFunction χ s ≠ 0 :=
    (grh_iff_all_dirichlet_zeroFree_gt_half.mp hGRH) N χ s hgt (Or.inl hχ)
  exact (DirichletCharacter.differentiable_LFunction hχ s).inv hnz

-- ==============================================================================
-- PART V: GLOBAL MULTI-BASIN DIPOLAR CONSERVATION ACROSS ARBITRARY PRIME CHAINS
-- ==============================================================================

/-- THEOREM V.1 (MULTI-BASIN GLOBAL DIPOLAR CONSERVATION):
    If `basins : Finset ι` indexes any finite collection of inter-prime basins
    each satisfying exact dipolar neutrality `basinSum b = 0`, their cumulative
    global dipolar sum vanishes identically (`∑ b ∈ basins, basinSum b = 0`). -/
theorem multi_basin_dipolar_conservation {ι : Type*}
    (basins : Finset ι) (p_left p_right : ι → ℕ)
    (_hgap : ∀ b ∈ basins, p_left b + 1 ≤ p_right b) :
    ∑ b ∈ basins,
      (∑ N ∈ Finset.Ico (p_left b + 1) (p_right b),
        (((p_right b : ℤ) - N) - ((N : ℤ) - p_left b))) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  let L := p_right b - (p_left b + 1)
  have hbij : ∑ N ∈ Finset.Ico (p_left b + 1) (p_right b),
      (((p_right b : ℤ) - N) - ((N : ℤ) - p_left b)) =
      ∑ k ∈ Finset.range L, ((L : ℤ) - 1 - 2 * (k : ℤ)) := by
    apply Finset.sum_bij (fun N _ => N - (p_left b + 1))
    · intro N hN
      rw [Finset.mem_Ico] at hN
      rw [Finset.mem_range]
      omega
    · intro N₁ hN₁ N₂ hN₂ heq
      rw [Finset.mem_Ico] at hN₁ hN₂
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      refine ⟨p_left b + 1 + k, ?_, by omega⟩
      rw [Finset.mem_Ico]
      omega
    · intro N hN
      rw [Finset.mem_Ico] at hN
      dsimp [L]
      omega
  rw [hbij]
  have hzero_range : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((n : ℤ) - 1 - 2 * (k : ℤ)) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hsplit : ∑ x ∈ Finset.range m, (((m + 1 : ℕ) : ℤ) - 1 - 2 * (x : ℤ)) =
          (∑ x ∈ Finset.range m, ((m : ℤ) - 1 - 2 * (x : ℤ))) + ∑ _x ∈ Finset.range m, (1 : ℤ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        push_cast
        ring
      rw [hsplit, ih, zero_add, Finset.sum_const, Finset.card_range]
      push_cast
      ring
  exact hzero_range L

end PrimeCountingAndDirectArithmeticCorollaries
