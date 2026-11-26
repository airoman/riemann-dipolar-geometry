/-
  ==============================================================================
  EULER PRODUCT ON THE INFINITE-DIMENSIONAL BOHR TORUS T^inf,
  ADELIC RING A_Q COUPLING, HARDY Z BRIDGE, AND EXACT EQUIVALENCE
  BETWEEN SpectralBridgeTarget AND MATHLIB4 RiemannHypothesis

  Title: Coupling the Clifford Torus T^2 to the Bohr Torus T^inf and
         the Rational Adele Ring A_Q
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I:   Unconditional proof that riemannZeta has no real zeros in (0, 1)
              via analytic continuation of Dirichlet eta(s) = (1 - 2^(1-s)) zeta(s),
              upgrading the single-target reduction directly to Mathlib4 official
              `RiemannHypothesis` and proving the EXACT equivalence:
                `SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight) <-> RiemannHypothesis`.
  - Part II:  Direct symmetry group of non-trivial zeros of `riemannZeta`
              (conjugation + functional reflection s <-> 1 - s) and equivalence
              with Mathlib4 `hardyZ` on the critical line beta = 1/2.
  - Part III: Coupling T^2 to the infinite-dimensional Bohr torus T^inf = prod_p S^1_p:
              * Exact Unique-Factorization lifting of N^{-s} to T^inf.
              * Unconditional proof of Q-linear independence of {log p : p prime}
                (the exact arithmetic invariant distinguishing zeta(s) from
                 Davenport-Heilbronn counterexamples).
              * Coupling to Mathlib4 Euler product `riemannZeta_eulerProduct_tprod`,
                von Mangoldt logarithmic derivative, and Tao logDeriv functional equation.
              * The L^2(T^inf) Critical-Line Phase-Transition Theorem:
                  Summable (sum_p ||p^{-s}||^2) <-> 1/2 < beta,
                so beta = 1/2 is the unique symmetric boundary where neither the
                forward nor the functional-dual L^2(T^inf) energy converges.
  - Part IV:  Adelic Space A_Q = R x A_{Q,f} (`NumberField.AdeleRing (O Q) Q`):
              * Exact Archimedean and finite-adelic norms of principal ideles N in N^+.
              * Adelic logarithmic conservation law: log ||N_inf|| + log ||N_fin|| = 0.
              * Exact Adelic-T^2 Identity:
                  N^{-1/2} sinh((beta - 1/2) log N) = (1/2) (||N_fin||^{1-beta} - ||N_inf||^{-beta}),
                identifying the T^2 monopolar radial drift with the Archimedean vs.
                finite-adelic scale imbalance on A_Q.
              * Archimedean Jacobi theta modular duality (the infinite-place fiber
                of the adelic theta function).
  - Part V:   Dipolar Weil Positivity Criterion and Three-Way Equivalence:
              * Explicit anti-symmetric dipolar Weil wavepacket H_{a,gamma}(z) = sin(a(z - gamma)):
                non-negative (sin^2 >= 0) on the critical line, strictly negative
                (-sinh^2(a(beta - 1/2)) < 0) at any off-line zero.
              * Three-Way Master Equivalence:
                  `RiemannHypothesis`
                  <-> `SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)`
                  <-> `AdelicDipolarWeilPositivity`.
  ==============================================================================
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HardyZ
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.SumPrimeReciprocals
import RiemannDipolar.AnalyticReduction
import RiemannDipolar.Mathlib4Bridge
import RiemannDipolar.CliffordGeodesics
import RiemannDipolar.MonopolarDivergence

open Real Complex Filter Topology Set
open scoped ComplexConjugate NumberField NumberField.AdeleRing
open RiemannAnalyticReduction Mathlib4RiemannBridge UnifiedMathlib4Geodesic
open UnconditionalMonopolarDivergence

namespace EulerAdelicBridge

-- ==============================================================================
-- PART I: NON-VANISHING OF riemannZeta ON (0, 1) AND EXACT EQUIVALENCE WITH
--         MATHLIB4 OFFICIAL `RiemannHypothesis`
-- ==============================================================================

/-- Paired alternating Dirichlet eta summand: (2k + 1)^{-s} - (2k + 2)^{-s}. -/
noncomputable def etaTerm (k : ℕ) (s : ℂ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)

/-- The Dirichlet eta function eta(s) = sum_{k=0}^inf ((2k + 1)^{-s} - (2k + 2)^{-s}),
    analytic on the entire right half-plane {s : C | 0 < Re(s)}. -/
noncomputable def dirichletEta (s : ℂ) : ℂ :=
  ∑' k : ℕ, etaTerm k s

/-- Exact finite-sum algebraic identity connecting paired eta partial sums
    to standard Dirichlet partial sums. -/
lemma finset_etaTerm_eq (N : ℕ) (s : ℂ) :
    ∑ k ∈ Finset.range N, etaTerm k s =
      (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) -
      2 * (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h2 : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [Finset.sum_range_succ, ih, h2, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have hmul : (2 : ℂ) ^ (-s) * (((N + 1 : ℕ) : ℂ) ^ (-s)) =
        ((2 * N + 2 : ℕ) : ℂ) ^ (-s) := by
      have hcast : ((2 * N + 2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((N + 1 : ℕ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
      simp
    have h2' : ((2 * N + 1 + 1 : ℕ) : ℂ) = ((2 * N + 2 : ℕ) : ℂ) := by norm_cast
    rw [h2']
    dsimp [etaTerm]
    calc (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) -
            2 * (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) +
            (((2 * N + 1 : ℕ) : ℂ) ^ (-s) - ((2 * N + 2 : ℕ) : ℂ) ^ (-s))
      _ = (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) +
            ((2 * N + 1 : ℕ) : ℂ) ^ (-s) + ((2 * N + 2 : ℕ) : ℂ) ^ (-s) -
            2 * (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) -
            2 * ((2 * N + 2 : ℕ) : ℂ) ^ (-s) := by ring
      _ = (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) +
            ((2 * N + 1 : ℕ) : ℂ) ^ (-s) + ((2 * N + 2 : ℕ) : ℂ) ^ (-s) -
            2 * (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) -
            2 * ((2 : ℂ) ^ (-s) * ((N + 1 : ℕ) : ℂ) ^ (-s)) := by rw [hmul]
      _ = (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) +
            ((2 * N + 1 : ℕ) : ℂ) ^ (-s) + ((2 * N + 2 : ℕ) : ℂ) ^ (-s) -
            2 * (2 : ℂ) ^ (-s) *
              ((∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) + ((N + 1 : ℕ) : ℂ) ^ (-s)) := by ring

/-- Mean-value bound on each paired eta term:
    ||(2k + 1)^{-s} - (2k + 2)^{-s}|| <= ||s|| * (2k + 1)^{-(Re(s) + 1)} for Re(s) > 0. -/
lemma norm_etaTerm_le (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖etaTerm k s‖ ≤ ‖s‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)) := by
  let a : ℝ := (2 * k + 1 : ℕ)
  let b : ℝ := (2 * k + 2 : ℕ)
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; norm_cast; omega
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  let f' : ℝ → ℂ := fun x => (-s) * (x : ℂ) ^ (-s - 1)
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    have h_slit : (x : ℂ) ∈ Complex.slitPlane :=
      Or.inl (by simpa using hx_pos)
    have h_cpow : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) (x : ℂ) := by
      simpa [mul_comm] using (Complex.hasStrictDerivAt_cpow_const (c := -s) h_slit).hasDerivAt
    simpa [f, f'] using h_cpow.comp_ofReal
  have hbound : ∀ x ∈ Set.Icc a b, ‖f' x‖ ≤ ‖s‖ * a ^ (-(s.re + 1)) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    dsimp [f']
    rw [norm_mul, norm_neg]
    have hnorm_pow : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      congr 1
      simp only [sub_re, neg_re, one_re]
      ring
    rw [hnorm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos ha_pos hx.1 (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hderiv x hx).differentiableAt)
    (fun x hx => by
      rw [(hderiv x hx).deriv]
      exact hbound x hx)
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hba : ‖b - a‖ = 1 := by
    dsimp [a, b]
    have : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
    rw [this, abs_one]
  rw [hba, mul_one] at hmvt
  have hsymm : ‖etaTerm k s‖ = ‖f b - f a‖ := by
    dsimp [etaTerm, f, a, b]
    rw [norm_sub_rev]
  rw [hsymm]
  exact hmvt

/-- The majorant series k ↦ R * (2k + 1)^{-(δ + 1)} is summable for any δ > 0. -/
lemma summable_eta_majorant (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun k : ℕ => R * ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1))) := by
  have hbase : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(δ + 1))) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (δ + 1)) :=
      Real.summable_one_div_nat_rpow.mpr (by linarith)
    have h2 : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ (δ + 1)) :=
      (summable_nat_add_iff 1).mpr h1
    refine h2.congr fun k => ?_
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg _)]
  refine (hbase.mul_left |R|).of_norm_bounded (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg R)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by norm_cast; omega) (by linarith)

/-- `dirichletEta` is complex-differentiable on the entire open right half-plane Re(s) > 0. -/
theorem differentiableOn_dirichletEta :
    DifferentiableOn ℂ dirichletEta {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hδ : 0 < s₀.re / 2 := by linarith [show 0 < s₀.re from hs₀]
  let δ := s₀.re / 2
  let R := ‖s₀‖ + 1
  let U : Set ℂ := {w : ℂ | δ < w.re ∧ ‖w‖ < R}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hs₀_mem : s₀ ∈ U := ⟨by dsimp [δ]; linarith [show 0 < s₀.re from hs₀], by dsimp [R]; linarith⟩
  have hterm_diff : ∀ k : ℕ, DifferentiableOn ℂ (etaTerm k) U := by
    intro k w _
    have h1 : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
      (differentiableAt_id.neg.const_cpow (Or.inl h2))).differentiableWithinAt
  have hterm_le : ∀ k : ℕ, ∀ w ∈ U,
      ‖etaTerm k w‖ ≤ R * ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by
    intro k w hw
    have hw_pos : 0 < w.re := lt_trans hδ hw.1
    have h1 := norm_etaTerm_le k hw_pos
    have h2 : ((2 * k + 1 : ℕ) : ℝ) ^ (-(w.re + 1)) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega)
      linarith [hw.1]
    calc ‖etaTerm k w‖
      _ ≤ ‖w‖ * ((2 * k + 1 : ℕ) : ℝ) ^ (-(w.re + 1)) := h1
      _ ≤ R * ((2 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) :=
          mul_le_mul (le_of_lt hw.2) h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by dsimp [R]; positivity)
  have hdiffU : DifferentiableOn ℂ dirichletEta U :=
    differentiableOn_tsum_of_summable_norm (summable_eta_majorant R hδ) hterm_diff hU_open hterm_le
  exact (hdiffU.differentiableAt (hU_open.mem_nhds hs₀_mem)).differentiableWithinAt

/-- Agreement of `dirichletEta s` with `(1 - 2 * 2^{-s}) * riemannZeta s` on Re(s) > 1. -/
theorem dirichletEta_eq_mul_riemannZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    dirichletEta s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  have hs_pos : 0 < s.re := by linarith
  have hsum_eta : Summable (fun k : ℕ => etaTerm k s) :=
    (summable_eta_majorant ‖s‖ hs_pos).of_norm_bounded (fun k => norm_etaTerm_le k hs_pos)
  have hsum_zeta : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ s)) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have h2 := (summable_nat_add_iff 1).mpr h1
    refine h2.congr fun n => ?_
    rw [Complex.cpow_neg, one_div]
  have hzeta_eq : ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_neg, one_div]
    push_cast
    rfl
  have hT_lhs : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, etaTerm k s) atTop
      (𝓝 (dirichletEta s)) :=
    hsum_eta.hasSum.tendsto_sum_nat
  have hT_z1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    rw [← hzeta_eq]
    exact hsum_zeta.hasSum.tendsto_sum_nat.comp
      (Filter.tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id)
  have hT_z2 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    rw [← hzeta_eq]
    exact hsum_zeta.hasSum.tendsto_sum_nat
  have hT_rhs : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) -
      2 * (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)))
      atTop (𝓝 ((1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s)) := by
    have h := hT_z1.sub (hT_z2.const_mul (2 * (2 : ℂ) ^ (-s)))
    simpa [sub_mul, one_mul] using h
  have hT_lhs' : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range (2 * N), ((n + 1 : ℕ) : ℂ) ^ (-s)) -
      2 * (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)))
      atTop (𝓝 (dirichletEta s)) := by
    refine hT_lhs.congr fun N => finset_etaTerm_eq N s
  exact tendsto_nhds_unique hT_lhs' hT_rhs

/-- Helper: `{s : ℂ | 0 < s.re ∧ s ≠ 1}` is path-connected (hence preconnected). -/
lemma isPreconnected_rightHalfPlane_compl_one :
    IsPreconnected {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}
  let p₀ : ℂ := ⟨2, 1⟩
  have hp₀ : p₀ ∈ U := by
    refine ⟨by simp [p₀], ?_⟩
    intro h
    have : p₀.re = (1 : ℂ).re := congrArg Complex.re h
    simp [p₀] at this
  have hseg : ∀ a b : ℂ, (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • a + t • b ∈ U) →
      JoinedIn U a b := by
    intro a b hmem
    refine ⟨{
      toFun := fun t => (1 - (t : ℝ)) • a + (t : ℝ) • b
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => hmem t.1 t.2.1 t.2.2⟩
  have hpath : IsPathConnected U := by
    refine ⟨p₀, hp₀, fun z hz => ?_⟩
    by_cases him : z.im ≠ 0
    · let m : ℂ := ⟨2, z.im⟩
      have h1 : JoinedIn U z m := by
        apply hseg
        intro t ht0 ht1
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, m]
          rcases eq_or_lt_of_le ht0 with rfl | ht_pos
          · linarith [hz.1]
          · nlinarith [hz.1]
        · intro heq
          have him_eq := congrArg Complex.im heq
          simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, add_zero, Complex.one_im, m] at him_eq
          apply him
          linarith
      have h2 : JoinedIn U m p₀ := by
        apply hseg
        intro t ht0 ht1
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, m, p₀]
          linarith
        · intro heq
          have hre_eq := congrArg Complex.re heq
          simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re, m, p₀] at hre_eq
          linarith
      exact (h1.trans h2).symm
    · push Not at him
      have hre_ne : z.re ≠ 1 := by
        intro hre
        apply hz.2
        exact Complex.ext (by simp [hre]) (by simp [him])
      let m : ℂ := ⟨z.re, 1⟩
      have h1 : JoinedIn U z m := by
        apply hseg
        intro t ht0 ht1
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, m]
          linarith [hz.1]
        · intro heq
          have hre_eq := congrArg Complex.re heq
          simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re, m] at hre_eq
          apply hre_ne
          linarith
      have h2 : JoinedIn U m p₀ := by
        apply hseg
        intro t ht0 ht1
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, m, p₀]
          rcases eq_or_lt_of_le ht0 with rfl | ht_pos
          · linarith [hz.1]
          · nlinarith [hz.1]
        · intro heq
          have him_eq := congrArg Complex.im heq
          simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, add_zero, Complex.one_im, m, p₀] at him_eq
          linarith
      exact (h1.trans h2).symm
  exact hpath.isConnected.isPreconnected

/-- Analytic identity `dirichletEta s = (1 - 2 * 2^{-s}) * riemannZeta s`
    valid throughout the entire punctured right half-plane {s : C | 0 < Re(s), s != 1}. -/
theorem dirichletEta_eq_mul_riemannZeta_of_re_pos {s : ℂ} (hs : 0 < s.re) (hne : s ≠ 1) :
    dirichletEta s = (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  have hU_eq : U = {z : ℂ | 0 < z.re} ∩ ({1}ᶜ) := by ext z; simp [U]
  have hU_open : IsOpen U := by
    rw [hU_eq]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ dirichletEta U :=
    (differentiableOn_dirichletEta.mono (fun z (hz : z ∈ U) => hz.1)).analyticOnNhd hU_open
  have hg_diff : DifferentiableOn ℂ (fun z : ℂ => (1 - 2 * (2 : ℂ) ^ (-z)) * riemannZeta z) U := by
    intro z hz
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (-w)) z :=
      differentiableAt_id.neg.const_cpow (Or.inl h2)
    have hfac : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * (2 : ℂ) ^ (-w)) z :=
      (differentiableAt_const 1).sub (hpow.const_mul 2)
    exact (hfac.mul (differentiableAt_riemannZeta hz.2)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => (1 - 2 * (2 : ℂ) ^ (-z)) * riemannZeta z) U :=
    hg_diff.analyticOnNhd hU_open
  have h2_mem : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : ∀ᶠ z in 𝓝[≠] (2 : ℂ),
      dirichletEta z = (1 - 2 * (2 : ℂ) ^ (-z)) * riemannZeta z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hmem] with z hz
    exact dirichletEta_eq_mul_riemannZeta_of_one_lt_re hz
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    isPreconnected_rightHalfPlane_compl_one h2_mem hev.frequently ⟨hs, hne⟩

/-- THEOREM I.1 (Unconditional Non-Vanishing of riemannZeta on the Real Interval (0, 1)):
    For every real x in (0, 1), Re(zeta(x)) < 0, and in particular zeta(x) != 0. -/
theorem riemannZeta_re_neg_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  have hxne : (x : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have heq := dirichletEta_eq_mul_riemannZeta_of_re_pos (s := (x : ℂ)) (by simpa using hx0) hxne
  have hsum_eta : Summable (fun k : ℕ => etaTerm k (x : ℂ)) :=
    (summable_eta_majorant ‖(x : ℂ)‖ (by simpa using hx0)).of_norm_bounded
      (fun k => norm_etaTerm_le k (by simpa using hx0))
  have hterm_re : ∀ k : ℕ, (etaTerm k (x : ℂ)).re =
      ((2 * k + 1 : ℕ) : ℝ) ^ (-x) - ((2 * k + 2 : ℕ) : ℝ) ^ (-x) := by
    intro k
    dsimp [etaTerm]
    have h1 : (((2 * k + 1 : ℕ) : ℂ) ^ (-(x : ℂ))) = ((((2 * k + 1 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    have h2 : (((2 * k + 2 : ℕ) : ℂ) ^ (-(x : ℂ))) = ((((2 * k + 2 : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    rw [h1, h2, Complex.ofReal_re, Complex.ofReal_re]
  have heta_re_pos : 0 < (dirichletEta (x : ℂ)).re := by
    dsimp [dirichletEta]
    rw [Complex.re_tsum hsum_eta]
    have hsum_re : Summable (fun k : ℕ => (etaTerm k (x : ℂ)).re) :=
      (Complex.hasSum_re hsum_eta.hasSum).summable
    refine Summable.tsum_pos hsum_re (fun k => ?_) 0 ?_
    · rw [hterm_re k]
      have hle : ((2 * k + 2 : ℕ) : ℝ) ^ (-x) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (-x) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by norm_cast; omega) (by linarith)
      linarith
    · rw [hterm_re 0]
      simp only [mul_zero, zero_add, Nat.cast_one, Real.one_rpow, Nat.cast_ofNat]
      have hlt : (2 : ℝ) ^ (-x) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      linarith
  have hfac_real : (1 - 2 * (2 : ℂ) ^ (-(x : ℂ))) = (((1 - 2 * (2 : ℝ) ^ (-x)) : ℝ) : ℂ) := by
    have h2pow : (2 : ℂ) ^ (-(x : ℂ)) = (((2 : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_neg, Complex.ofReal_cpow (by norm_num)]
    rw [h2pow]
    push_cast
    rfl
  have hrhs_re : ((1 - 2 * (2 : ℂ) ^ (-(x : ℂ))) * riemannZeta (x : ℂ)).re =
      (1 - 2 * (2 : ℝ) ^ (-x)) * (riemannZeta (x : ℂ)).re := by
    rw [hfac_real, Complex.re_ofReal_mul]
  have hfac_neg : 1 - 2 * (2 : ℝ) ^ (-x) < 0 := by
    have h2 : (2 : ℝ) ^ (1 - x) > 1 :=
      Real.one_lt_rpow (by norm_num) (by linarith)
    have hrew : 2 * (2 : ℝ) ^ (-x) = (2 : ℝ) ^ (1 - x) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
    linarith
  rw [heq, hrhs_re] at heta_re_pos
  nlinarith

theorem riemannZeta_ne_zero_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro h
  have hlt := riemannZeta_re_neg_of_Ioo hx0 hx1
  rw [h, Complex.zero_re] at hlt
  linarith

/-- Every non-trivial zero in Mathlib4 official `RiemannHypothesis` satisfies
    `IsNonTrivialZetaZero s.re s.im` (i.e., 0 < Re(s) < 1 and Im(s) != 0). -/
theorem isNonTrivialZetaZero_of_mathlib_rh_hyp (s : ℂ)
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (_hone : s ≠ 1) :
    IsNonTrivialZetaZero s.re s.im := by
  have hlt1 : s.re < 1 := by
    by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz
  have hpos : 0 < s.re := by
    by_contra hle
    push Not at hle
    exact htriv ((riemannZeta_eq_zero_iff_of_re_nonpos hle).mp hz)
  have him : s.im ≠ 0 := by
    intro him0
    have hs_real : s = (s.re : ℂ) := Complex.ext rfl (by simp [him0])
    rw [hs_real] at hz
    exact riemannZeta_ne_zero_of_Ioo hpos hlt1 hz
  refine ⟨hpos, hlt1, him, ?_⟩
  have hs_eta : (⟨s.re, s.im⟩ : ℂ) = s := Complex.eta s
  rw [hs_eta]
  exact hz

/-- THEOREM I.2 (Reduction of Mathlib4 Official `RiemannHypothesis` to `SpectralBridgeTarget`):
    Because `MonopolarOmegaDivergenceTarget` is proved unconditionally and `riemannZeta`
    has no real zeros in (0, 1), `SpectralBridgeTarget` implies Mathlib4 `RiemannHypothesis`. -/
theorem mathlib_riemannHypothesis_of_spectralBridge
    (h_bridge : SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)) :
    RiemannHypothesis := by
  intro s hz htriv hone
  exact riemann_hypothesis_from_single_spectral_bridge h_bridge s.re s.im
    (isNonTrivialZetaZero_of_mathlib_rh_hyp s hz htriv hone)

/-- Helper: On the critical line beta = 1/2, the monopolar drift vanishes identically,
    so `GlobalMonopolarBounded g (1/2) gamma` holds unconditionally with bound C = 0. -/
theorem globalMonopolarBounded_at_half (g : ℕ → ℝ) (gamma : ℝ) :
    GlobalMonopolarBounded g (1 / 2) gamma := by
  refine ⟨0, fun X => ?_⟩
  have hzero : globalMonopolarSum g (1 / 2) gamma X = 0 := by
    dsimp [globalMonopolarSum, monopolarTerm]
    apply Finset.sum_eq_zero
    intro N _
    have : ((1 / 2 : ℝ) - 1 / 2) * Real.log (N : ℝ) = 0 := by ring
    rw [this, Real.sinh_zero]
    simp
  rw [hzero, norm_zero]

/-- THEOREM I.3 (EXACT LOGICAL EQUIVALENCE WITH MATHLIB4 `RiemannHypothesis`):
    `SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)` is neither strictly
    stronger nor strictly weaker than the Riemann Hypothesis: it is 100% logically
    equivalent to Mathlib4 official `RiemannHypothesis`. -/
theorem spectralBridge_iff_mathlib_riemannHypothesis :
    SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight) ↔ RiemannHypothesis := by
  constructor
  · exact mathlib_riemannHypothesis_of_spectralBridge
  · intro hRH beta gamma hzero
    have hs_eq : riemannZeta (⟨beta, gamma⟩ : ℂ) = 0 := hzero.2.2.2
    have htriv : ¬ ∃ n : ℕ, (⟨beta, gamma⟩ : ℂ) = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      linarith [hzero.1]
    have hone : (⟨beta, gamma⟩ : ℂ) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hzero.2.1]
    have hbeta : beta = 1 / 2 := hRH ⟨beta, gamma⟩ hs_eq htriv hone
    rw [hbeta]
    exact globalMonopolarBounded_at_half primeGapWeight gamma

-- ==============================================================================
-- PART II: EXACT SYMMETRY GROUP OF riemannZeta ZEROS & HARDY Z(t) BRIDGE
-- ==============================================================================

/-- Conjugation symmetry of non-trivial zeros directly on Mathlib4 `riemannZeta`. -/
theorem isNonTrivialZetaZero_conj {beta gamma : ℝ} (h : IsNonTrivialZetaZero beta gamma) :
    IsNonTrivialZetaZero beta (-gamma) := by
  refine ⟨h.1, h.2.1, neg_ne_zero.mpr h.2.2.1, ?_⟩
  have hconj : (⟨beta, -gamma⟩ : ℂ) = conj (⟨beta, gamma⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hconj, riemannZeta_conj, h.2.2.2, map_zero]

/-- Functional reflection symmetry (beta, gamma) ↦ (1 - beta, gamma) directly on
    Mathlib4 `riemannZeta`, coupling functional duality to the critical strip. -/
theorem isNonTrivialZetaZero_one_sub {beta gamma : ℝ} (h : IsNonTrivialZetaZero beta gamma) :
    IsNonTrivialZetaZero (1 - beta) gamma := by
  refine ⟨by linarith [h.2.1], by linarith [h.1], h.2.2.1, ?_⟩
  let s : ℂ := ⟨beta, gamma⟩
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp [s] at this
    linarith [h.1]
  have hs_comp0 : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [s, h.1])
    rw [h.2.2.2] at hdef
    exact (div_eq_zero_iff.mp hdef.symm).resolve_right hG
  have h1s_comp0 : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub, hs_comp0]
  have h1s_ne0 : 1 - s ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp [s] at this
    linarith [h.2.1]
  have h1s_zeta0 : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero h1s_ne0, h1s_comp0, zero_div]
  have hconj_eq : (⟨1 - beta, gamma⟩ : ℂ) = conj (1 - s) := by
    apply Complex.ext <;> simp [s]
  rw [hconj_eq, riemannZeta_conj, h1s_zeta0, map_zero]

/-- Direct bridge between the critical-line zero predicate and Mathlib4 `hardyZ`:
    for gamma != 0, `IsNonTrivialZetaZero (1/2) gamma <-> hardyZ gamma = 0`. -/
theorem isNonTrivialZetaZero_half_iff_hardyZ {gamma : ℝ} (hgamma : gamma ≠ 0) :
    IsNonTrivialZetaZero (1 / 2) gamma ↔ hardyZ gamma = 0 := by
  rw [hardyZ_eq_zero_iff]
  have hmk : (⟨1 / 2, gamma⟩ : ℂ) = (1 : ℂ) / 2 + (gamma : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  constructor
  · intro h
    rw [← hmk]
    exact h.2.2.2
  · intro hz
    refine ⟨by norm_num, by norm_num, hgamma, ?_⟩
    rw [hmk]
    exact hz

-- ==============================================================================
-- PART III: COUPLING T^2 TO THE INFINITE-DIMENSIONAL BOHR TORUS T^inf AND
--           THE EULER PRODUCT
-- ==============================================================================

/-- Predicate asserting that a prime-indexed phase vector lies on the
    infinite-dimensional Bohr torus T^inf = prod_{p prime} S^1_p. -/
def OnBohrTorus (ω : Nat.Primes → ℂ) : Prop :=
  ∀ p : Nat.Primes, ‖ω p‖ = 1

/-- The canonical Archimedean-to-Bohr diagonal geodesic flow Theta_inf(gamma) in T^inf:
    Theta_inf(gamma)(p) = exp(-i * gamma * log p) in S^1_p. -/
noncomputable def bohrGeodesic (gamma : ℝ) (p : Nat.Primes) : ℂ :=
  Complex.exp (-(gamma * Real.log (p : ℝ) : ℝ) * Complex.I)

/-- Every point on the diagonal flow Theta_inf(gamma) lies on the unit Bohr torus T^inf. -/
theorem bohrGeodesic_on_torus (gamma : ℝ) : OnBohrTorus (bohrGeodesic gamma) := by
  intro p
  dsimp [bohrGeodesic]
  have : (-(gamma * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I =
      ((-(gamma * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; rfl
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- Exact formula for a prime power p^{-(beta + i*gamma)} in Bohr-torus coordinates. -/
lemma prime_cpow_eq_bohr (p : Nat.Primes) (beta gamma : ℝ) :
    ((p : ℕ) : ℂ) ^ (-(⟨beta, gamma⟩ : ℂ)) =
      (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * bohrGeodesic gamma p := by
  have hp_pos : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.mpr p.prop.pos
  have hp_ne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp_ne, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp]
  dsimp [bohrGeodesic]
  rw [← Complex.exp_add]
  congr 1
  have hlog : Complex.log ((p : ℕ) : ℂ) = (Real.log ((p : ℕ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [hlog]
  apply Complex.ext <;> simp <;> ring

/-- THEOREM III.1 (Exact T^2 <-> T^inf Unique-Factorization Coupling):
    For every positive integer N >= 1 and s = beta + i*gamma, the Archimedean T^2
    phasor N^{-s} factors EXACTLY into the product of local Bohr-torus coordinates
    indexed by the prime divisors of N. -/
theorem archimedean_phasor_eq_bohr_prod {N : ℕ} (hN : N ≠ 0) (beta gamma : ℝ) :
    (N : ℂ) ^ (-(⟨beta, gamma⟩ : ℂ)) =
      ∏ p ∈ N.primeFactors,
        ((((p : ℝ) ^ (-beta) : ℝ) : ℂ) * Complex.exp (-(gamma * Real.log (p : ℝ) : ℝ) * Complex.I)) ^
          (N.factorization p) := by
  let s : ℂ := ⟨beta, gamma⟩
  have hfac : N = ∏ p ∈ N.primeFactors, p ^ (N.factorization p) :=
    Nat.prod_primeFactors_pow_factorization hN
  conv_lhs => rw [hfac]
  rw [Nat.cast_prod]
  have hprod_cpow : ∀ (S : Finset ℕ) (e : ℕ → ℕ),
      (∀ p ∈ S, 0 < p) →
      (∏ p ∈ S, ((p ^ e p : ℕ) : ℂ)) ^ (-s) = ∏ p ∈ S, ((p : ℂ) ^ (-s)) ^ (e p) := by
    intro S e hpos
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_pos : 0 < a := hpos a (Finset.mem_insert_self a S)
      have hS_pos : ∀ p ∈ S, 0 < p := fun p hp => hpos p (Finset.mem_insert_of_mem hp)
      have ha_nonneg : (0 : ℝ) ≤ (a ^ e a : ℕ) := Nat.cast_nonneg _
      have hprod_nonneg : (0 : ℝ) ≤ (∏ p ∈ S, p ^ e p : ℕ) := Nat.cast_nonneg _
      have hcast_prod : (∏ p ∈ S, ((p ^ e p : ℕ) : ℂ)) = (((∏ p ∈ S, p ^ e p : ℕ) : ℝ) : ℂ) := by
        simp [Nat.cast_prod]
      rw [← Complex.ofReal_natCast (a ^ e a), hcast_prod,
          Complex.mul_cpow_ofReal_nonneg ha_nonneg hprod_nonneg, ← hcast_prod, ih hS_pos]
      congr 1
      have hpow : (((a ^ e a : ℕ) : ℝ) : ℂ) ^ (-s) = ((a : ℂ) ^ (-s)) ^ (e a) := by
        rw [Complex.ofReal_natCast, Nat.cast_pow,
            ← Complex.natCast_cpow_natCast_mul a (e a) (-s),
            mul_comm (e a : ℂ) (-s), mul_comm (-s) (e a : ℂ), Complex.cpow_nat_mul]
      exact hpow
  rw [hprod_cpow N.primeFactors N.factorization (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpr : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have heq := prime_cpow_eq_bohr ⟨p, hpr⟩ beta gamma
  dsimp [bohrGeodesic] at heq
  rw [heq]

/-- THEOREM III.2 (Q-Linear Independence of Prime Logarithms on the Bohr Torus T^inf):
    The frequency basis {log p : p prime} of the infinite-dimensional Bohr torus T^inf
    is linearly independent over Q. This is the exact multiplicative invariant separating
    riemannZeta from Davenport-Heilbronn counterexamples. -/
theorem log_primes_linearIndependent_rat :
    LinearIndependent ℚ (fun p : Nat.Primes => Real.log (p : ℝ)) := by
  rw [linearIndependent_iff']
  intro s g hsum
  let D : ℕ := ∏ p ∈ s, (g p).den
  have hD_pos : 0 < D := Finset.prod_pos fun p _ => (g p).pos
  have hD_ne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
  let c : Nat.Primes → ℤ := fun p =>
    if p ∈ s then (g p).num * ((D / (g p).den : ℕ) : ℤ) else 0
  have hcg : ∀ p ∈ s, ((c p : ℤ) : ℝ) = (D : ℝ) * ((g p : ℚ) : ℝ) := by
    intro p hp
    have hcp_eq : c p = (g p).num * ((D / (g p).den : ℕ) : ℤ) := by simp [c, hp]
    rw [hcp_eq]
    have hdvd : (g p).den ∣ D := Finset.dvd_prod_of_mem (fun q => (g q).den) hp
    have hmul_div : (D / (g p).den) * (g p).den = D := Nat.div_mul_cancel hdvd
    have hq : ((g p : ℚ) : ℝ) = ((g p).num : ℝ) / ((g p).den : ℝ) := Rat.cast_def (g p)
    have hden_ne : ((g p).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (g p).pos)
    have hmul_div_r : ((D / (g p).den : ℕ) : ℝ) * ((g p).den : ℝ) = (D : ℝ) := by
      exact_mod_cast hmul_div
    rw [hq, Int.cast_mul, Int.cast_natCast]
    field_simp [hden_ne]
    rw [mul_assoc, hmul_div_r, mul_comm]
  have hsum_int : ∑ p ∈ s, ((c p : ℤ) : ℝ) * Real.log (p : ℝ) = 0 := by
    have hscaled : (D : ℝ) * (∑ p ∈ s, g p • Real.log (p : ℝ)) = 0 := by
      rw [hsum, mul_zero]
    rw [Finset.mul_sum] at hscaled
    rw [← hscaled]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hcg p hp, Rat.smul_def, mul_assoc]
  let s_pos := s.filter (fun p => 0 ≤ c p)
  let s_neg := s.filter (fun p => c p < 0)
  have hsplit : ∑ p ∈ s_pos, ((c p).natAbs : ℝ) * Real.log (p : ℝ) =
      ∑ p ∈ s_neg, ((c p).natAbs : ℝ) * Real.log (p : ℝ) := by
    have hdisj : Disjoint s_pos s_neg := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; omega
    have hunion : s_pos ∪ s_neg = s := by
      ext p
      simp only [s_pos, s_neg, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      · intro hp
        by_cases h0 : 0 ≤ c p
        · exact Or.inl ⟨hp, h0⟩
        · exact Or.inr ⟨hp, by omega⟩
    rw [← hunion, Finset.sum_union hdisj] at hsum_int
    have h1 : ∑ p ∈ s_pos, ((c p : ℤ) : ℝ) * Real.log (p : ℝ) =
        ∑ p ∈ s_pos, ((c p).natAbs : ℝ) * Real.log (p : ℝ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hc0 : 0 ≤ c p := (Finset.mem_filter.mp hp).2
      have habs : ((c p).natAbs : ℤ) = c p := by omega
      have hcast : ((c p : ℤ) : ℝ) = ((c p).natAbs : ℝ) := by
        have := congrArg (Int.cast (R := ℝ)) habs
        simpa using this.symm
      rw [hcast]
    have h2 : ∑ p ∈ s_neg, ((c p : ℤ) : ℝ) * Real.log (p : ℝ) =
        -(∑ p ∈ s_neg, ((c p).natAbs : ℝ) * Real.log (p : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hc0 : c p < 0 := (Finset.mem_filter.mp hp).2
      have habs : ((c p).natAbs : ℤ) = -c p := by omega
      have hcast : ((c p : ℤ) : ℝ) = -((c p).natAbs : ℝ) := by
        have h' : ((c p).natAbs : ℝ) = -((c p : ℤ) : ℝ) := by
          have := congrArg (Int.cast (R := ℝ)) habs
          simpa using this
        linarith
      rw [hcast, neg_mul]
    rw [h1, h2] at hsum_int
    linarith
  have hexp_eq : Real.exp (∑ p ∈ s_pos, ((c p).natAbs : ℝ) * Real.log (p : ℝ)) =
      Real.exp (∑ p ∈ s_neg, ((c p).natAbs : ℝ) * Real.log (p : ℝ)) :=
    congrArg Real.exp hsplit
  have hexp_prod : ∀ T : Finset Nat.Primes,
      Real.exp (∑ p ∈ T, ((c p).natAbs : ℝ) * Real.log (p : ℝ)) =
        ((∏ p ∈ T, (p : ℕ) ^ (c p).natAbs : ℕ) : ℝ) := by
    intro T
    rw [Real.exp_sum, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hp_pos : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.mpr p.prop.pos
    rw [Real.exp_nat_mul, Real.exp_log hp_pos, Nat.cast_pow]
  rw [hexp_prod s_pos, hexp_prod s_neg] at hexp_eq
  have hnat_eq : ∏ p ∈ s_pos, (p : ℕ) ^ (c p).natAbs =
      ∏ p ∈ s_neg, (p : ℕ) ^ (c p).natAbs :=
    Nat.cast_injective hexp_eq
  have hprime_dvd_finset_prod : ∀ (q : Nat.Primes) (T : Finset Nat.Primes) (f : Nat.Primes → ℕ),
      (q : ℕ) ∣ ∏ p ∈ T, f p → ∃ p ∈ T, (q : ℕ) ∣ f p := by
    intro q T f
    classical
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      intro h1
      exact False.elim (q.prop.not_dvd_one h1)
    | insert a T ha ih =>
      rw [Finset.prod_insert ha]
      intro hdvd
      rcases q.prop.dvd_mul.mp hdvd with hqa | hqT
      · exact ⟨a, Finset.mem_insert_self a T, hqa⟩
      · obtain ⟨p, hpT, hqp⟩ := ih hqT
        exact ⟨p, Finset.mem_insert_of_mem hpT, hqp⟩
  have hc_zero : ∀ p ∈ s, c p = 0 := by
    intro q hq
    by_contra hcq
    have hpos_abs : 0 < (c q).natAbs := Int.natAbs_pos.mpr hcq
    by_cases hq_sign : 0 ≤ c q
    · have hq_mem : q ∈ s_pos := Finset.mem_filter.mpr ⟨hq, hq_sign⟩
      have hdvd_lhs : (q : ℕ) ∣ ∏ p ∈ s_pos, (p : ℕ) ^ (c p).natAbs :=
        dvd_trans (dvd_pow_self (q : ℕ) (ne_of_gt hpos_abs))
          (Finset.dvd_prod_of_mem _ hq_mem)
      rw [hnat_eq] at hdvd_lhs
      obtain ⟨p, hp_mem, hdvd_pow⟩ := hprime_dvd_finset_prod q s_neg _ hdvd_lhs
      have hdvd_p : (q : ℕ) ∣ (p : ℕ) := q.prop.dvd_of_dvd_pow hdvd_pow
      have hqp_val : (q : ℕ) = (p : ℕ) :=
        (Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp hdvd_p
      have hqp : q = p := Subtype.ext hqp_val
      have hp_neg : c p < 0 := (Finset.mem_filter.mp hp_mem).2
      rw [← hqp] at hp_neg
      omega
    · have hq_mem : q ∈ s_neg := Finset.mem_filter.mpr ⟨hq, by omega⟩
      have hdvd_rhs : (q : ℕ) ∣ ∏ p ∈ s_neg, (p : ℕ) ^ (c p).natAbs :=
        dvd_trans (dvd_pow_self (q : ℕ) (ne_of_gt hpos_abs))
          (Finset.dvd_prod_of_mem _ hq_mem)
      rw [← hnat_eq] at hdvd_rhs
      obtain ⟨p, hp_mem, hdvd_pow⟩ := hprime_dvd_finset_prod q s_pos _ hdvd_rhs
      have hdvd_p : (q : ℕ) ∣ (p : ℕ) := q.prop.dvd_of_dvd_pow hdvd_pow
      have hqp_val : (q : ℕ) = (p : ℕ) :=
        (Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp hdvd_p
      have hqp : q = p := Subtype.ext hqp_val
      have hp_nonneg : 0 ≤ c p := (Finset.mem_filter.mp hp_mem).2
      rw [← hqp] at hp_nonneg
      omega
  intro p hp
  have hcp := hc_zero p hp
  have hreal := hcg p hp
  rw [hcp, Int.cast_zero] at hreal
  have hgp_r : ((g p : ℚ) : ℝ) = 0 := (mul_eq_zero.mp hreal.symm).resolve_left hD_ne
  exact Rat.cast_eq_zero.mp hgp_r

/-- THEOREM III.3 (Direct Coupling of the Bohr Torus Geodesic to Mathlib4 Euler Product):
    For Re(s) = beta > 1, the Euler product evaluated along the diagonal Bohr geodesic
    Theta_inf(gamma) equals `riemannZeta (beta + i*gamma)`. -/
theorem eulerProduct_bohrTorus_tprod {beta gamma : ℝ} (hbeta : 1 < beta) :
    ∏' p : Nat.Primes, (1 - (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * bohrGeodesic gamma p)⁻¹ =
      riemannZeta (⟨beta, gamma⟩ : ℂ) := by
  have hs : 1 < (⟨beta, gamma⟩ : ℂ).re := hbeta
  rw [← riemannZeta_eulerProduct_tprod hs]
  refine tprod_congr fun p => ?_
  rw [prime_cpow_eq_bohr p beta gamma]

/-- Exact local Euler-factor modulus envelope on the Bohr torus T^inf for all beta > 0. -/
theorem eulerFactor_bohr_norm_bounds {ω : Nat.Primes → ℂ} (hω : OnBohrTorus ω)
    (p : Nat.Primes) {beta : ℝ} (hbeta : 0 < beta) :
    (1 + (p : ℝ) ^ (-beta))⁻¹ ≤
      ‖(1 - (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p)⁻¹‖ ∧
    ‖(1 - (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p)⁻¹‖ ≤
      (1 - (p : ℝ) ^ (-beta))⁻¹ := by
  have hp_gt1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  have hr_pos : 0 < (p : ℝ) ^ (-beta) := Real.rpow_pos_of_pos (by linarith) _
  have hr_lt1 : (p : ℝ) ^ (-beta) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
  have hterm_norm : ‖(((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p‖ = (p : ℝ) ^ (-beta) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr_pos), hω p, mul_one]
  have hlow : 1 - (p : ℝ) ^ (-beta) ≤ ‖1 - (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p)
    rw [norm_one, hterm_norm] at h
    exact h
  have hhigh : ‖1 - (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p‖ ≤ 1 + (p : ℝ) ^ (-beta) := by
    have h := norm_sub_le (1 : ℂ) ((((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p)
    rw [norm_one, hterm_norm] at h
    exact h
  have hpos_denom : 0 < 1 - (p : ℝ) ^ (-beta) := by linarith
  have hnorm_pos : 0 < ‖1 - (((p : ℝ) ^ (-beta) : ℝ) : ℂ) * ω p‖ :=
    lt_of_lt_of_le hpos_denom hlow
  rw [norm_inv]
  constructor
  · exact inv_anti₀ hnorm_pos hhigh
  · exact inv_anti₀ hpos_denom hlow

/-- THEOREM III.4 (The L^2(T^inf) Critical-Line Phase-Transition Theorem):
    The Bohr-torus L^2 prime-phase energy sum_{p prime} ||p^{-(beta + i*gamma)}||^2
    converges if and only if beta > 1/2. -/
theorem bohr_L2_energy_summable_iff_gt_half (beta gamma : ℝ) :
    Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-(⟨beta, gamma⟩ : ℂ))‖ ^ 2) ↔
      (1 / 2 : ℝ) < beta := by
  have hrew : (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-(⟨beta, gamma⟩ : ℂ))‖ ^ 2) =
      (fun p : Nat.Primes => (p : ℝ) ^ (-2 * beta)) := by
    ext p
    have hp_pos : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.mpr p.prop.pos
    rw [prime_cpow_eq_bohr p beta gamma, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hp_pos) _),
        bohrGeodesic_on_torus gamma p, mul_one, ← Real.rpow_natCast,
        ← Real.rpow_mul (le_of_lt hp_pos)]
    congr 1
    push_cast
    ring
  rw [hrew, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- COROLLARY III.5 (Symmetric L^2(T^inf) Critical-Line Characterization):
    The critical line beta = 1/2 is the UNIQUE real abscissa where neither the forward
    L^2(T^inf) prime-phase energy nor the functional-dual L^2(T^inf) energy converges. -/
theorem bohr_L2_dual_energy_critical_line_iff (beta gamma : ℝ) :
    (¬ Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-(⟨beta, gamma⟩ : ℂ))‖ ^ 2) ∧
     ¬ Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-(⟨1 - beta, gamma⟩ : ℂ))‖ ^ 2)) ↔
      beta = 1 / 2 := by
  rw [bohr_L2_energy_summable_iff_gt_half beta gamma,
      bohr_L2_energy_summable_iff_gt_half (1 - beta) gamma]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; rw [h]; constructor <;> linarith

/-- Direct packaging of Mathlib4's von Mangoldt logarithmic derivative (Re(s) > 1)
    and Terence Tao's functional equation for logDeriv riemannZeta across s <-> 1 - s. -/
theorem zeta_logDeriv_euler_bridge {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

theorem zeta_logDeriv_functional_bridge {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) + Complex.log (2 * Real.pi) -
        Complex.digamma s + (Real.pi : ℂ) / 2 * Complex.tan (Real.pi * s / 2) :=
  logDeriv_riemannZeta_one_sub hs hz

-- ==============================================================================
-- PART IV: ADELIC SPACE A_Q = R x A_{Q,f} AND IDELIC COUPLING TO T^2 & THETA
-- ==============================================================================

/-- Exact Archimedean norm of a positive integer N embedded in the rational adele ring A_Q. -/
theorem adelic_archimedean_norm_nat (N : ℕ) :
    ‖(algebraMap ℚ 𝔸[ℚ] (N : ℚ)).1‖ = (N : ℝ) := by
  rw [NumberField.AdeleRing.algebraMap_fst_def,
      NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm]
  simp only [Algebra.norm_self, MonoidHom.id_apply, Rat.cast_abs, Rat.cast_natCast]
  exact abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)

/-- Exact finite-adelic norm of a positive integer N >= 1 embedded in A_Q:
    ||N_fin||_{A_f} = N^{-1}. -/
theorem adelic_finite_norm_nat {N : ℕ} (hN : 0 < N) :
    ‖(algebraMap ℚ 𝔸[ℚ] (N : ℚ)).2‖ = (N : ℝ)⁻¹ := by
  have hq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  rw [NumberField.AdeleRing.algebraMap_snd_def,
      NumberField.FiniteAdeleRing.coe_norm_eq_inv_abs_norm hq]
  simp only [Algebra.norm_self, MonoidHom.id_apply, Rat.cast_inv, Rat.cast_abs, Rat.cast_natCast]
  rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]

/-- THEOREM IV.1 (Global Adelic Logarithmic Conservation Law on A_Q):
    For every N >= 1 embedded as a principal idele in A_Q^x, the Archimedean
    logarithmic coordinate log ||N_inf|| and the finite-adelic logarithmic coordinate
    log ||N_fin|| sum identically to 0. -/
theorem adelic_log_product_conservation {N : ℕ} (hN : 0 < N) :
    Real.log ‖(algebraMap ℚ 𝔸[ℚ] (N : ℚ)).1‖ +
      Real.log ‖(algebraMap ℚ 𝔸[ℚ] (N : ℚ)).2‖ = 0 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [adelic_archimedean_norm_nat N, adelic_finite_norm_nat hN, Real.log_inv]
  ring

/-- THEOREM IV.2 (THE ADELIC-T^2 BRIDGE IDENTITY):
    For every N >= 1 and beta in R, the T^2 monopolar hyperbolic radial drift
      N^{-1/2} * sinh((beta - 1/2) * log N)
    is IDENTICALLY half the imbalance between the finite-adelic weight
    ||N_fin||_{A_f}^{1 - beta} and the Archimedean weight ||N_inf||_inf^{-beta}
    inside Mathlib4's rational adele ring `NumberField.AdeleRing (O Q) Q`! -/
theorem monopolar_drift_eq_adelic_imbalance {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sinh ((beta - 1 / 2) * Real.log (N : ℝ)) =
      (1 / 2 : ℝ) *
        (‖(algebraMap ℚ 𝔸[ℚ] (N : ℚ)).2‖ ^ (1 - beta) -
         ‖(algebraMap ℚ 𝔸[ℚ] (N : ℚ)).1‖ ^ (-beta)) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [adelic_archimedean_norm_nat N, adelic_finite_norm_nat hN,
      Real.inv_rpow (le_of_lt hN_pos), ← Real.rpow_neg (le_of_lt hN_pos),
      Real.sinh_eq, Real.rpow_def_of_pos hN_pos, Real.rpow_def_of_pos hN_pos,
      Real.rpow_def_of_pos hN_pos]
  have h1 : Real.exp (Real.log (N : ℝ) * (-(1 / 2 : ℝ))) *
      Real.exp ((beta - 1 / 2) * Real.log (N : ℝ)) =
      Real.exp (Real.log (N : ℝ) * -(1 - beta)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (Real.log (N : ℝ) * (-(1 / 2 : ℝ))) *
      Real.exp (-((beta - 1 / 2) * Real.log (N : ℝ))) =
      Real.exp (Real.log (N : ℝ) * -beta) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h2

/-- THEOREM IV.3 (Archimedean Jacobi Theta Modular Duality — The Infinite-Place
    Fiber of the Adelic Theta Function):
    For every real t > 0, jacobiTheta(i / t) = sqrt(t) * jacobiTheta(i * t). -/
theorem archimedean_jacobiTheta_duality {t : ℝ} (ht : 0 < t) :
    jacobiTheta (Complex.I * ((1 / t : ℝ) : ℂ)) =
      (Real.sqrt t : ℂ) * jacobiTheta (Complex.I * (t : ℂ)) := by
  let τ : UpperHalfPlane := ⟨Complex.I * (t : ℂ), by simp [ht]⟩
  have hS := jacobiTheta_S_smul τ
  have hτ_val : (τ : ℂ) = Complex.I * (t : ℂ) := rfl
  have hS_val : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = Complex.I * ((1 / t : ℝ) : ℂ) := by
    have hcoe : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = (-(τ : ℂ))⁻¹ :=
      congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul τ)
    rw [hcoe, hτ_val]
    have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    push_cast
    field_simp [ht_ne, Complex.I_ne_zero]
    rw [Complex.I_sq]
  have hfac : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) := by
    rw [hτ_val]
    have hmul : -Complex.I * (Complex.I * (t : ℂ)) = (t : ℂ) := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [hmul, Real.sqrt_eq_rpow]
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hhalf, Complex.ofReal_cpow (le_of_lt ht)]
  rw [hS_val, hfac, hτ_val] at hS
  exact hS

-- ==============================================================================
-- PART V: DIPOLAR WEIL POSITIVITY CRITERION & THREE-WAY MASTER EQUIVALENCE
-- ==============================================================================

/-- The anti-symmetric dipolar Weil spectral wavepacket centered at height gamma
    with scale parameter a: H_{a, gamma}(z) = sin(a * (z - gamma)). -/
noncomputable def dipolarWeilSymbol (a gamma : ℝ) (z : ℂ) : ℂ :=
  Complex.sin ((a : ℂ) * (z - (gamma : ℂ)))

/-- The paired Weil quadratic spectral kernel Q_{a, gamma}(z) = H(z) * conj(H(conj z)).
    On the real axis (critical line z = t in R), Q(t) = |H(t)|^2 >= 0;
    off the real axis (z = gamma - i*(beta - 1/2)), Q(z) = -sinh^2(a*(beta - 1/2)) < 0! -/
noncomputable def dipolarWeilKernel (a gamma : ℝ) (z : ℂ) : ℂ :=
  dipolarWeilSymbol a gamma z * conj (dipolarWeilSymbol a gamma (conj z))

/-- THEOREM V.1 (Non-Negativity on the Critical Line):
    For every real spectral height t in R (corresponding to a critical-line zero
    rho = 1/2 + i*t), the dipolar Weil kernel equals sin^2(a*(t - gamma)) >= 0. -/
theorem dipolarWeilKernel_critical_line (a gamma t : ℝ) :
    dipolarWeilKernel a gamma (t : ℂ) = ((Real.sin (a * (t - gamma)) ^ 2 : ℝ) : ℂ) := by
  dsimp [dipolarWeilKernel, dipolarWeilSymbol]
  rw [Complex.conj_ofReal]
  have harg : (a : ℂ) * ((t : ℂ) - (gamma : ℂ)) = ((a * (t - gamma) : ℝ) : ℂ) := by
    push_cast; ring
  rw [harg, ← Complex.ofReal_sin, Complex.conj_ofReal]
  push_cast
  ring

/-- THEOREM V.2 (Exact Off-Line Negative Spectral Signature):
    At the spectral coordinate z_rho = gamma - i*(beta - 1/2) of any zero
    rho = beta + i*gamma, the dipolar Weil kernel evaluates EXACTLY to
      Q_{a, gamma}(z_rho) = -sinh^2(a * (beta - 1/2)),
    linking Weil positivity directly to the square of the hyperbolic radial drift. -/
theorem dipolarWeilKernel_at_zero (a beta gamma : ℝ) :
    dipolarWeilKernel a gamma (⟨gamma, -(beta - 1 / 2)⟩ : ℂ) =
      ((-(Real.sinh (a * (beta - 1 / 2)) ^ 2) : ℝ) : ℂ) := by
  dsimp [dipolarWeilKernel, dipolarWeilSymbol]
  have hz1 : (a : ℂ) * ((⟨gamma, -(beta - 1 / 2)⟩ : ℂ) - (gamma : ℂ)) =
      ((-(a * (beta - 1 / 2)) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp; ring
  have hz2 : (a : ℂ) * (conj (⟨gamma, -(beta - 1 / 2)⟩ : ℂ) - (gamma : ℂ)) =
      ((a * (beta - 1 / 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hz1, hz2, Complex.sin_mul_I, Complex.sin_mul_I]
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_sinh, Real.sinh_neg]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  have hI : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  calc (-(Real.sinh (a * (beta - 1 / 2)) : ℂ)) * Complex.I *
        ((Real.sinh (a * (beta - 1 / 2)) : ℂ) * -Complex.I)
    _ = -(Real.sinh (a * (beta - 1 / 2)) : ℂ) ^ 2 * (Complex.I * (-Complex.I)) := by ring
    _ = -(Real.sinh (a * (beta - 1 / 2)) : ℂ) ^ 2 * 1 := by rw [hI]
    _ = ((-(Real.sinh (a * (beta - 1 / 2)) ^ 2) : ℝ) : ℂ) := by push_cast; ring

/-- THEOREM V.3 (Exact Positivity Characterization of the Critical Line):
    For any nonzero scale a != 0, the dipolar Weil kernel at z_rho has non-negative
    real part if and only if beta = 1/2. -/
theorem dipolarWeilKernel_nonneg_iff_half {a : ℝ} (ha : a ≠ 0) (beta gamma : ℝ) :
    0 ≤ (dipolarWeilKernel a gamma (⟨gamma, -(beta - 1 / 2)⟩ : ℂ)).re ↔ beta = 1 / 2 := by
  rw [dipolarWeilKernel_at_zero, Complex.ofReal_re]
  constructor
  · intro h
    have hsq : Real.sinh (a * (beta - 1 / 2)) ^ 2 = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    have hsinh : Real.sinh (a * (beta - 1 / 2)) = 0 := sq_eq_zero_iff.mp hsq
    have hmul : a * (beta - 1 / 2) = 0 := Real.sinh_eq_zero.mp hsinh
    have hsub : beta - 1 / 2 = 0 := (mul_eq_zero.mp hmul).resolve_left ha
    linarith
  · intro h
    rw [h]
    simp

/-- Global Adelic-Dipolar Weil Positivity Hypothesis:
    Every non-trivial zero rho = beta + i*gamma of `riemannZeta` satisfies
    non-negativity of its dipolar Weil kernel for all scales a in R. -/
def AdelicDipolarWeilPositivity : Prop :=
  ∀ beta gamma : ℝ, IsNonTrivialZetaZero beta gamma →
    ∀ a : ℝ, 0 ≤ (dipolarWeilKernel a gamma (⟨gamma, -(beta - 1 / 2)⟩ : ℂ)).re

/-- THEOREM V.4 (THREE-WAY MASTER EQUIVALENCE IN MATHLIB4):
    The following three statements are 100% logically equivalent in Mathlib4:
      (1) Mathlib4 official `RiemannHypothesis`,
      (2) `SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)`,
      (3) `AdelicDipolarWeilPositivity`. -/
theorem three_way_equivalence_rh_spectralBridge_adelicWeil :
    (RiemannHypothesis ↔ SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)) ∧
    (SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight) ↔ AdelicDipolarWeilPositivity) := by
  have h1 := spectralBridge_iff_mathlib_riemannHypothesis.symm
  have h2 : SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight) ↔
      AdelicDipolarWeilPositivity := by
    constructor
    · intro hSB beta gamma hzero a
      have hbeta : beta = 1 / 2 :=
        riemann_hypothesis_from_single_spectral_bridge hSB beta gamma hzero
      rw [dipolarWeilKernel_at_zero, Complex.ofReal_re, hbeta]
      simp
    · intro hWeil beta gamma hzero
      have hpos := hWeil beta gamma hzero 1
      have hbeta : beta = 1 / 2 :=
        (dipolarWeilKernel_nonneg_iff_half one_ne_zero beta gamma).mp hpos
      rw [hbeta]
      exact globalMonopolarBounded_at_half primeGapWeight gamma
  exact ⟨h1, h2⟩

end EulerAdelicBridge
