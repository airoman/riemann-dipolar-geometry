/-
  ==============================================================================
  MODULE #33: ICOSIAN Γ₁₂₀ GOLDEN-RATIO COORDINATES ON S³, HURWITZ–KAM
  DIOPHANTINE SPIRAL EXPLORATION ON T² ⊂ M⁵, MOD-5 PRIME SPLITTING IN ℤ[φ],
  AND THE GOLDEN-REGULATOR GEODESIC GRONWALL BOUNDARY

  Title: Golden-Ratio Icosian Coordinates, Diophantine Geodesic Spiral on M⁵,
         and Arithmetic Regulator Coupling
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 23, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Explicit Icosian Γ₁₂₀ Coordinates on S³ ⊂ M⁵ via Mathlib4 `goldenRatio`):
      * `goldenRatio_decimal_enclosure`: `1.6180339 < φ < 1.6180340`.
      * `goldenRatio_sq_add_inv_sq`: `φ² + (φ⁻¹)² = 3`.
      * `icosian_golden_vertex_on_unit_S3`: Every signed icosian quaternion vertex
        `(s₁ φ / 2, s₂ / 2, s₃ φ⁻¹ / 2, 0)` of the binary icosahedral group Γ₁₂₀
        lies identically on the unit 3-sphere S³ (`x² + y² + z² + w² = 1`).
      * `icosianGoldenManifold5DPoint` & `icosian_manifold5D_ground_state_iff_half`:
        Explicit embedding into M⁵ = (S³ / Γ₁₂₀) × T² with ground state iff `β = 1/2`.
  - Part II (Golden Geodesic Spiral Explorer on T² ⊂ M⁵ & Golden Angle):
      * `goldenAngle_identities_and_bounds`: `θ_golden = 2π / φ² = 2π(2 - φ) ∈ (0, π)`
        with exact partition `θ_golden + 2π / φ = 2π`.
      * `goldenSpiral_equatorial_and_hopf_null`: The golden geodesic spiral on T²
        maintains exact Clifford norm equipartition `(1/2, 1/2)` and Hopf `z₃ = 0`.
      * `goldenRegulator_exp_scale`: `exp(n · ln φ) = φⁿ` (`ln φ > 0` regulator).
  - Part III (ℤ[φ] Norm Anisotropy & Unconditional Hurwitz–KAM Non-Resonance):
      * `goldenQuadraticNorm_ne_zero` & `goldenQuadraticNorm_abs_ge_one`:
        For all `(p, q) ∈ ℤ² \ {(0, 0)}`, `p² - p q - q² ≠ 0` and `1 ≤ |p² - p q - q²|`.
      * `golden_spiral_diophantine_lower_bound`: For all `p ∈ ℤ` and `q ≥ 1` with
        `|q φ - p| ≤ 1`, `1 / (√5 q + 1) ≤ |q φ - p|` (strict KAM resonance avoidance).
  - Part IV (Mod-5 Prime Splitting Law, Binet–Fibonacci Coupling, & Gronwall Gate):
      * `binet_sqrt5_fib_identity`: `√5 · F_n = φⁿ - ψⁿ` on Mathlib4's `Nat.fib`.
      * `golden_charPoly_ramified_at_five`: `r² - r - 1 = 0 ↔ r = 3` in `ZMod 5`.
      * `golden_regulator_gronwall_pos_on_meridian`: A golden-regulator relative
        decay bound `μ_tilde' θ ≥ -(ln φ · C) μ_tilde θ` on `(0, π)` forces
        `μ_tilde θ ≥ μ_tilde 0 · φ^(-C π) > 0` across all `θ ∈ [0, π]`.
  ==============================================================================
-/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import RiemannDipolar.Manifold5DHolomorphyAndAsymptoticConfinement
import RiemannDipolar.GlobalGeodesicCompletenessAndAdelicMargin

open Real Complex Filter Topology Set
open scoped BigOperators Classical Matrix goldenRatio
open CliffordSieveAdelicClosure
open Manifold5DHolomorphyAndAsymptoticConfinement
open GlobalGeodesicCompletenessAndAdelicMargin

namespace GoldenRatioSpiralAndIcosianManifold5D

-- ==============================================================================
-- PART I: EXPLICIT ICOSIAN Γ₁₂₀ COORDINATES ON S³ ⊂ M⁵ = (S³ / Γ₁₂₀) × T²
-- ==============================================================================

/-- THEOREM I.1 (SEVEN-DECIMAL ENCLOSURE OF THE GOLDEN RATIO φ ≈ 1.6180339887):
    Mathlib4's official `Real.goldenRatio = (1 + √5) / 2` satisfies
    `1.6180339 < φ < 1.6180340`, with strictly positive logarithmic regulator `ln φ > 0`. -/
theorem goldenRatio_decimal_enclosure :
    (16180339 : ℝ) / 10000000 < φ ∧
    φ < (16180340 : ℝ) / 10000000 ∧
    0 < Real.log φ := by
  have hlow_sq : ((22360678 : ℝ) / 10000000) ^ 2 < 5 := by norm_num
  have hhigh_sq : (5 : ℝ) < ((22360680 : ℝ) / 10000000) ^ 2 := by norm_num
  have hsqrt_low : (22360678 : ℝ) / 10000000 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    exact hlow_sq
  have hsqrt_high : Real.sqrt 5 < (22360680 : ℝ) / 10000000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    exact hhigh_sq
  refine ⟨?_, ?_, Real.log_pos Real.one_lt_goldenRatio⟩
  · unfold Real.goldenRatio
    linarith
  · unfold Real.goldenRatio
    linarith

/-- THEOREM I.2 (EXACT ICOSIAN QUADRATIC IDENTITY φ² + φ⁻² = 3):
    Using `φ² = φ + 1` and `φ⁻¹ = -ψ = φ - 1`, the sum of squares of the golden ratio
    and its reciprocal equals `3` identically. -/
theorem goldenRatio_sq_add_inv_sq :
    φ ^ 2 + (φ⁻¹) ^ 2 = 3 := by
  rw [Real.inv_goldenRatio]
  have hpsi : -ψ = φ - 1 := by linarith [Real.goldenRatio_add_goldenConj]
  rw [hpsi]
  calc φ ^ 2 + (φ - 1) ^ 2
      = 2 * φ ^ 2 - 2 * φ + 1 := by ring
    _ = 2 * (φ + 1) - 2 * φ + 1 := by rw [Real.goldenRatio_sq]
    _ = 3 := by ring

/-- THEOREM I.3 (EXPLICIT Γ₁₂₀ BINARY ICOSAHEDRAL VERTICES ON THE UNIT 3-SPHERE S³):
    For any sign choices `s₁, s₂, s₃ ∈ ℝ` with `sᵢ² = 1`, the golden icosian vertex
    `(s₁ φ / 2, s₂ / 2, s₃ φ⁻¹ / 2, 0)` of the 600-cell / binary icosahedral group Γ₁₂₀
    lies identically on the unit 3-sphere `S³ ⊂ ℝ⁴`. -/
theorem icosian_golden_vertex_on_unit_S3
    (s₁ s₂ s₃ : ℝ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) (hs₃ : s₃ ^ 2 = 1) :
    (s₁ * φ / 2) ^ 2 + (s₂ / 2) ^ 2 + (s₃ * φ⁻¹ / 2) ^ 2 + (0 : ℝ) ^ 2 = 1 := by
  calc (s₁ * φ / 2) ^ 2 + (s₂ / 2) ^ 2 + (s₃ * φ⁻¹ / 2) ^ 2 + (0 : ℝ) ^ 2
      = (s₁ ^ 2 * φ ^ 2 + s₂ ^ 2 + s₃ ^ 2 * (φ⁻¹) ^ 2) / 4 := by ring
    _ = (1 * φ ^ 2 + 1 + 1 * (φ⁻¹) ^ 2) / 4 := by rw [hs₁, hs₂, hs₃]
    _ = ((φ ^ 2 + (φ⁻¹) ^ 2) + 1) / 4 := by ring
    _ = (3 + 1) / 4 := by rw [goldenRatio_sq_add_inv_sq]
    _ = 1 := by norm_num

/-- Explicit constructor embedding any golden icosian generator of `Γ₁₂₀ ⊂ S³`
    paired with toroidal Clifford coordinates `(u, v) ∈ T²` into `M⁵ = (S³ / Γ₁₂₀) × T²`. -/
noncomputable def icosianGoldenManifold5DPoint
    (s₁ s₂ s₃ : ℝ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) (hs₃ : s₃ ^ 2 = 1)
    (u v : ℝ) : Manifold5DPoint where
  x := s₁ * φ / 2
  y := s₂ / 2
  z := s₃ * φ⁻¹ / 2
  w := 0
  u := u
  v := v
  hS3 := icosian_golden_vertex_on_unit_S3 s₁ s₂ s₃ hs₁ hs₂ hs₃

/-- THEOREM I.4 (5D ICOSIAN GROUND-STATE CHARACTERIZATION OF THE CRITICAL LINE):
    At every golden icosian fiber point of `M⁵ = (S³ / Γ₁₂₀) × T²`, the total 5D energy
    equals its minimal ground-state value `2` if and only if `β = 1 / 2`. -/
theorem icosian_manifold5D_ground_state_iff_half
    (s₁ s₂ s₃ : ℝ) (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1) (hs₃ : s₃ ^ 2 = 1)
    (u v β : ℝ) :
    manifold5D_energy (icosianGoldenManifold5DPoint s₁ s₂ s₃ hs₁ hs₂ hs₃ u v) β = 2 ↔
    β = 1 / 2 :=
  (manifold5D_energy_min_iff_half
    (icosianGoldenManifold5DPoint s₁ s₂ s₃ hs₁ hs₂ hs₃ u v) β).2

-- ==============================================================================
-- PART II: GOLDEN GEODESIC SPIRAL EXPLORER ON T² ⊂ M⁵ & GOLDEN ANGLE
-- ==============================================================================

/-- The Golden Angle `θ_golden = 2π / φ² ≈ 137.50776°` (in radians) governing
    minimal-impedance angular dispersion on `S¹ ⊂ T²`. -/
noncomputable def goldenAngle : ℝ :=
  2 * Real.pi / (φ ^ 2)

/-- THEOREM II.1 (EXACT GOLDEN ANGLE PARTITION & RADIAN BOUNDS):
    `θ_golden = 2π(2 - φ)`, `0 < θ_golden < π`, and `θ_golden + 2π / φ = 2π`. -/
theorem goldenAngle_identities_and_bounds :
    goldenAngle = 2 * Real.pi * (2 - φ) ∧
    0 < goldenAngle ∧
    goldenAngle < Real.pi ∧
    goldenAngle + 2 * Real.pi / φ = 2 * Real.pi := by
  have hphi_ne : φ ≠ 0 := Real.goldenRatio_ne_zero
  have hphi2_ne : φ ^ 2 ≠ 0 := pow_ne_zero 2 hphi_ne
  have hmul : φ ^ 2 * (2 - φ) = 1 := by
    calc φ ^ 2 * (2 - φ)
        = (φ + 1) * (2 - φ) := by rw [Real.goldenRatio_sq]
      _ = 2 + φ - φ ^ 2 := by ring
      _ = 2 + φ - (φ + 1) := by rw [Real.goldenRatio_sq]
      _ = 1 := by ring
  have h1 : goldenAngle = 2 * Real.pi * (2 - φ) := by
    unfold goldenAngle
    rw [div_eq_iff hphi2_ne]
    exact (calc 2 * Real.pi * (2 - φ) * φ ^ 2
        = 2 * Real.pi * (φ ^ 2 * (2 - φ)) := by ring
      _ = 2 * Real.pi * 1 := by rw [hmul]
      _ = 2 * Real.pi := by ring).symm
  have hbounds := goldenRatio_decimal_enclosure
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h1]
    apply mul_pos (by positivity)
    linarith [hbounds.2.1]
  · rw [h1]
    have h2phi : 2 * (2 - φ) < 1 := by linarith [hbounds.1]
    nlinarith
  · unfold goldenAngle
    rw [div_add_div _ _ hphi2_ne hphi_ne, div_eq_iff (mul_ne_zero hphi2_ne hphi_ne)]
    calc 2 * Real.pi * φ + φ ^ 2 * (2 * Real.pi)
        = 2 * Real.pi * φ * (1 + φ) := by ring
      _ = 2 * Real.pi * φ * φ ^ 2 := by rw [add_comm, ← Real.goldenRatio_sq]
      _ = 2 * Real.pi * (φ ^ 2 * φ) := by ring

/-- The Golden Geodesic Spiral on `T² ⊂ S³` at logarithmic scale `τ`:
    `γ_φ(τ) = cliffordPhasor(1/2, φ, τ)`. -/
noncomputable def goldenSpiralPhasor (τ : ℝ) : ℂ × ℂ :=
  cliffordPhasor (1 / 2) φ τ

/-- THEOREM II.2 (EQUATORIAL NORM CONSERVATION & HOPF NULLITY OF THE GOLDEN SPIRAL):
    For every logarithmic scale `τ ∈ ℝ`, the golden geodesic spiral `γ_φ(τ)` lies
    identically on the Clifford equator `‖z₁‖² = ‖z₂‖² = 1/2` of the unit 3-sphere `S³`
    and maintains zero vertical Hopf drift (`z₃ = 0`). -/
theorem goldenSpiral_equatorial_and_hopf_null (τ : ℝ) :
    ‖(goldenSpiralPhasor τ).1‖ ^ 2 = 1 / 2 ∧
    ‖(goldenSpiralPhasor τ).2‖ ^ 2 = 1 / 2 ∧
    (cliffordHopfProjection (goldenSpiralPhasor τ).1 (goldenSpiralPhasor τ).2).2.2 = 0 := by
  have hsqrt2 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hz1 : ‖(goldenSpiralPhasor τ).1‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [goldenSpiralPhasor, cliffordPhasor]
    calc (1 / Real.sqrt 2) * Real.cos (φ * τ) * ((1 / Real.sqrt 2) * Real.cos (φ * τ)) +
         (1 / Real.sqrt 2) * Real.sin (φ * τ) * ((1 / Real.sqrt 2) * Real.sin (φ * τ))
        = (1 / Real.sqrt 2) ^ 2 * (Real.cos (φ * τ) ^ 2 + Real.sin (φ * τ) ^ 2) := by ring
      _ = (1 / 2) * 1 := by rw [hsqrt2, Real.cos_sq_add_sin_sq]
      _ = 1 / 2 := by ring
  have hz2 : ‖(goldenSpiralPhasor τ).2‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [goldenSpiralPhasor, cliffordPhasor]
    have hsub : (1 / 2 - 1 / 2 : ℝ) * τ = 0 := by ring
    rw [hsub, Real.cosh_zero, Real.sinh_zero]
    calc (1 / Real.sqrt 2) * 1 * ((1 / Real.sqrt 2) * 1) +
         (1 / Real.sqrt 2) * 0 * ((1 / Real.sqrt 2) * 0)
        = (1 / Real.sqrt 2) ^ 2 := by ring
      _ = 1 / 2 := hsqrt2
  refine ⟨hz1, hz2, cliffordHopf_equator_z3_zero _ _ ?_⟩
  rw [← Complex.sq_norm, ← Complex.sq_norm, hz1, hz2]

/-- THEOREM II.3 (EXACT LOGARITHMIC REGULATOR SCALING OF THE GOLDEN SPIRAL):
    Stepping by `n` multiples of the fundamental regulator `Reg(ℚ(√5)) = ln φ`
    scales radial logarithmic time by exact powers `φⁿ`. -/
theorem goldenRegulator_exp_scale (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log φ) = φ ^ n := by
  rw [Real.exp_nat_mul, Real.exp_log Real.goldenRatio_pos]

-- ==============================================================================
-- PART III: ℤ[φ] NORM ANISOTROPY & HURWITZ–KAM DIOPHANTINE NON-RESONANCE ON T²
-- ==============================================================================

/-- Algebraic norm `N_{ℚ(√5)/ℚ}(p - q φ) = p² - p q - q²` on `ℤ × ℤ`. -/
def goldenQuadraticNorm (p q : ℤ) : ℤ :=
  p ^ 2 - p * q - q ^ 2

/-- THEOREM III.1 (EXACT REAL FACTORIZATION OF THE GOLDEN NORM):
    Over `ℝ`, `p² - p q - q² = (p - q φ)(p - q ψ)`. -/
theorem goldenQuadraticNorm_factorization (p q : ℤ) :
    ((goldenQuadraticNorm p q : ℤ) : ℝ) =
    ((p : ℝ) - (q : ℝ) * φ) * ((p : ℝ) - (q : ℝ) * ψ) := by
  unfold goldenQuadraticNorm
  push_cast
  calc (p : ℝ) ^ 2 - (p : ℝ) * (q : ℝ) - (q : ℝ) ^ 2
      = (p : ℝ) ^ 2 - (p : ℝ) * (q : ℝ) * 1 + (q : ℝ) ^ 2 * (-1) := by ring
    _ = (p : ℝ) ^ 2 - (p : ℝ) * (q : ℝ) * (φ + ψ) + (q : ℝ) ^ 2 * (φ * ψ) := by
          rw [Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]
    _ = ((p : ℝ) - (q : ℝ) * φ) * ((p : ℝ) - (q : ℝ) * ψ) := by ring

/-- THEOREM III.2 (UNCONDITIONAL ANISOTROPY OF `p² - p q - q²` ON `ℤ² \ {(0,0)}`):
    Because `φ` and `ψ` are irrational (`Real.goldenRatio_irrational`),
    `p² - p q - q² ≠ 0` for every non-zero integer pair `(p, q) ≠ (0, 0)`. -/
theorem goldenQuadraticNorm_ne_zero {p q : ℤ} (hne : p ≠ 0 ∨ q ≠ 0) :
    goldenQuadraticNorm p q ≠ 0 := by
  intro hzero
  by_cases hq : q = 0
  · subst hq
    unfold goldenQuadraticNorm at hzero
    simp at hzero
    rcases hne with hp | hq0
    · exact hp hzero
    · exact hq0 rfl
  · have hreal : ((goldenQuadraticNorm p q : ℤ) : ℝ) = 0 := by exact_mod_cast hzero
    rw [goldenQuadraticNorm_factorization] at hreal
    have hq_real : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
    rcases mul_eq_zero.mp hreal with h1 | h2
    · apply Real.goldenRatio_irrational
      refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
      push_cast
      rw [div_eq_iff hq_real]
      linarith
    · apply Real.goldenConj_irrational
      refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
      push_cast
      rw [div_eq_iff hq_real]
      linarith

/-- COROLLARY III.3 (INTEGER NORM INTEGRALITY FLOOR `1 ≤ |p² - p q - q²|`):
    Every non-zero element of `ℤ[φ]` has norm magnitude at least `1`. -/
theorem goldenQuadraticNorm_abs_ge_one {p q : ℤ} (hne : p ≠ 0 ∨ q ≠ 0) :
    (1 : ℝ) ≤ |((goldenQuadraticNorm p q : ℤ) : ℝ)| := by
  have hnz : goldenQuadraticNorm p q ≠ 0 := goldenQuadraticNorm_ne_zero hne
  have habs_int : (1 : ℤ) ≤ |goldenQuadraticNorm p q| := Int.one_le_abs hnz
  exact_mod_cast habs_int

/-- THEOREM III.4 (UNCONDITIONAL HURWITZ–KAM DIOPHANTINE LOWER BOUND ON T²):
    Along the golden geodesic spiral on `T² ⊂ M⁵`, every integer harmonic `(p, q)`
    with `1 ≤ q` and `|q φ - p| ≤ 1` is strictly bounded away from rational phase
    resonance by `1 / (√5 q + 1) ≤ |q φ - p|`. -/
theorem golden_spiral_diophantine_lower_bound
    (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hclose : |(q : ℝ) * φ - (p : ℝ)| ≤ 1) :
    1 / (Real.sqrt 5 * (q : ℝ) + 1) ≤ |(q : ℝ) * φ - (p : ℝ)| := by
  have hq_int_ne : (q : ℤ) ≠ 0 := by omega
  have hnorm := goldenQuadraticNorm_abs_ge_one (p := p) (q := (q : ℤ)) (Or.inr hq_int_ne)
  rw [goldenQuadraticNorm_factorization, abs_mul] at hnorm
  have hcast : (((q : ℤ) : ℝ)) = (q : ℝ) := by norm_cast
  rw [hcast] at hnorm
  have hsymm : |(p : ℝ) - (q : ℝ) * φ| = |(q : ℝ) * φ - (p : ℝ)| := abs_sub_comm _ _
  rw [hsymm] at hnorm
  have hconj_bound : |(p : ℝ) - (q : ℝ) * ψ| ≤ Real.sqrt 5 * (q : ℝ) + 1 := by
    have hsplit : (p : ℝ) - (q : ℝ) * ψ = ((p : ℝ) - (q : ℝ) * φ) + (q : ℝ) * (φ - ψ) := by ring
    rw [hsplit, Real.goldenRatio_sub_goldenConj]
    have htri := abs_add_le ((p : ℝ) - (q : ℝ) * φ) ((q : ℝ) * Real.sqrt 5)
    have hpos_q : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have hpos_s5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have habs_prod : |(q : ℝ) * Real.sqrt 5| = Real.sqrt 5 * (q : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg hpos_q hpos_s5), mul_comm]
    rw [hsymm, habs_prod] at htri
    linarith
  have hden_pos : 0 < Real.sqrt 5 * (q : ℝ) + 1 := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hs5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  rw [div_le_iff₀ hden_pos]
  have hmul : |(q : ℝ) * φ - (p : ℝ)| * |(p : ℝ) - (q : ℝ) * ψ| ≤
      |(q : ℝ) * φ - (p : ℝ)| * (Real.sqrt 5 * (q : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hconj_bound (abs_nonneg _)
  linarith

-- ==============================================================================
-- PART IV: MOD-5 PRIME SPLITTING, BINET–FIBONACCI, & GOLDEN GRONWALL GATE
-- ==============================================================================

/-- THEOREM IV.1 (EXACT BINET–FIBONACCI COUPLING ON MATHLIB4 `Nat.fib`):
    For every `n ∈ ℕ`, `√5 · F_n = φⁿ - ψⁿ`. -/
theorem binet_sqrt5_fib_identity (n : ℕ) :
    Real.sqrt 5 * (Nat.fib n : ℝ) = φ ^ n - ψ ^ n := by
  rw [Real.coe_fib_eq n]
  have hs5 : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  exact mul_div_cancel₀ _ hs5

/-- THEOREM IV.2 (EXACT RAMIFICATION OF THE GOLDEN CHARACTERISTIC POLYNOMIAL AT `p = 5`):
    In `ZMod 5`, `X² - X - 1 = (X - 3)²` has the unique double root `r = 3`,
    encoding the ramification `(5) = (√5)²` of `p = 5` in `ℤ[φ]`, while non-zero
    squares in `ZMod 5` lie strictly in `{1, 4}` (`±1 mod 5`, governing split vs. inert primes). -/
theorem golden_charPoly_ramified_at_five :
    (∀ r : ZMod 5, r ^ 2 - r - 1 = 0 ↔ r = 3) ∧
    (∀ u : ZMod 5, u ≠ 0 → u ^ 2 = 1 ∨ u ^ 2 = 4) := by
  decide

/-- THEOREM IV.3 (GOLDEN-REGULATOR GEODESIC GRONWALL BARRIER ON `[0, π]`):
    Along the stereographic meridian `θ(L) = 2 arctan(L) ∈ [0, π]` of `S³ ⊂ M⁵`,
    if the renormalized Weil–Gram margin `μ_tilde` obeys a relative decay rate
    bounded by a multiple `C ≥ 0` of the golden regulator `ln φ > 0`:
      `-(ln φ · C) · μ_tilde θ ≤ μ_tilde' θ`  on `(0, π)` with `μ_tilde 0 > 0`,
    then `μ_tilde θ ≥ μ_tilde 0 · φ^(-C π) > 0` across the ENTIRE compact meridian
    `[0, π]` (including the North Pole `θ = π`), triggering all-horizon Gram closure. -/
theorem golden_regulator_gronwall_pos_on_meridian
    (μ_tilde μ_tilde' : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, HasDerivAt μ_tilde (μ_tilde' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo 0 Real.pi, -(Real.log φ * C) * μ_tilde θ ≤ μ_tilde' θ)
    (hinit : 0 < μ_tilde 0) :
    ∀ θ ∈ Set.Icc 0 Real.pi,
      μ_tilde 0 * φ ^ (-C * Real.pi) ≤ μ_tilde θ ∧ 0 < μ_tilde θ := by
  have hlog_pos : 0 < Real.log φ := (goldenRatio_decimal_enclosure).2.2
  have hC_gold : 0 ≤ Real.log φ * C := mul_nonneg (le_of_lt hlog_pos) hC
  intro θ hθ
  have hgronwall := geodesic_log_gronwall_barrier_implies_north_pole_pos
    μ_tilde μ_tilde' (Real.log φ * C) hC_gold hcont hderiv
    (fun t ht => by simpa [neg_mul] using hbound t ht) hinit θ hθ
  have hrpow : φ ^ (-C * Real.pi) = Real.exp (-(Real.log φ * C) * Real.pi) := by
    rw [Real.rpow_def_of_pos Real.goldenRatio_pos]
    congr 1
    ring
  rw [← hrpow] at hgronwall
  have hstrict : 0 < μ_tilde 0 * φ ^ (-C * Real.pi) :=
    mul_pos hinit (Real.rpow_pos_of_pos Real.goldenRatio_pos (-C * Real.pi))
  exact ⟨hgronwall, lt_of_lt_of_le hstrict hgronwall⟩

end GoldenRatioSpiralAndIcosianManifold5D
