/-
  ==============================================================================
  UNCONDITIONAL MATHLIB4 PROOF OF `MonopolarOmegaDivergenceTarget`
  Title: Unconditional Divergence of the Global Monopolar Prime-Gap Sum Off Re(s) = 1/2
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 21, 2026

  OVERVIEW (0 'sorry', 0 hidden axioms):
  1. Constructs the exact bounding primes `p_prev N = max {p ∈ ℙ : p ≤ N}` and
     `p_next N = min {p ∈ ℙ : p ≥ N}` using `Nat.exists_infinite_primes` and `Finset.sup`.
  2. Defines the exact prime-gap monopolar weight `primeGapWeight N`:
       - 0 if N < 2 or N is prime,
       - (p_next N - p_prev N : ℝ) if N ≥ 4 is composite,
     and proves unconditionally `0 ≤ primeGapWeight N` and `2 ≤ primeGapWeight N`
     for every composite integer N ≥ 4.
  3. Defines the concrete global monopolar partial sum over ℂ:
       M(K; β, γ) = ∑_{N=0}^{K} primeGapWeight(N) * (sinh((β - 1/2) ln N) / √N) * e^{-iγ ln N}
  4. Proves UNCONDITIONALLY via coherent logarithmic phase windows
     [exp((2πk - π/3)/|γ|), exp((2πk + π/3)/|γ|)] where cos(γ ln N) ≥ 1/2 that:
       ∀ β γ : ℝ, β ≠ 1/2 → ¬ (∃ C : ℝ, ∀ K : ℕ, ‖M(K; β, γ)‖ ≤ C).
     This closes `MonopolarOmegaDivergenceTarget` completely in Mathlib4, reducing
     the Riemann Hypothesis formally to the single remaining target `SpectralBridgeTarget`.
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannDipolar.AnalyticReduction
import RiemannDipolar.Mathlib4Bridge

open Real Complex Filter Topology BigOperators
open RiemannAnalyticReduction
open Mathlib4RiemannBridge

namespace UnconditionalMonopolarDivergence

-- ==============================================================================
-- PART I: EXACT BOUNDING PRIMES p_prev(N), p_next(N), AND GAP WEIGHT g(N)
-- ==============================================================================

/-- Exact future bounding prime: p_next(N) = min { p ∈ ℙ : p ≥ N } -/
noncomputable def p_next (N : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes N)

/-- Exact past bounding prime: p_prev(N) = max { p ∈ ℙ : p ≤ N } (0 if N < 2) -/
def p_prev (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter Nat.Prime).sup id

lemma p_next_ge (N : ℕ) : N ≤ p_next N :=
  (Nat.find_spec (Nat.exists_infinite_primes N)).1

lemma p_next_prime (N : ℕ) : Nat.Prime (p_next N) :=
  (Nat.find_spec (Nat.exists_infinite_primes N)).2

lemma p_next_gt_of_not_prime (N : ℕ) (h : ¬ Nat.Prime N) : N + 1 ≤ p_next N := by
  have hge := p_next_ge N
  have hp := p_next_prime N
  have hne : p_next N ≠ N := fun heq => h (heq ▸ hp)
  omega

lemma p_prev_le (N : ℕ) : p_prev N ≤ N := by
  dsimp [p_prev]
  apply Finset.sup_le
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact Nat.lt_succ_iff.mp hp.1

lemma p_prev_le_pred_of_not_prime (N : ℕ) (h : ¬ Nat.Prime N) : p_prev N ≤ N - 1 := by
  dsimp [p_prev]
  apply Finset.sup_le
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  have hle : p ≤ N := Nat.lt_succ_iff.mp hp.1
  have hne : p ≠ N := fun heq => h (heq ▸ hp.2)
  change p ≤ N - 1
  omega

/--
  The exact discrete prime-gap monopolar weight g(N) = k_i(N) + k_r(N):
  - Equal to 0 on primes (and N < 2), where k_i(N) = k_r(N) = 0.
  - Equal to p_next(N) - p_prev(N) = g_m on composite interior integers.
-/
noncomputable def primeGapWeight (N : ℕ) : ℝ :=
  if N < 2 ∨ Nat.Prime N then 0 else ((p_next N - p_prev N : ℕ) : ℝ)

lemma primeGapWeight_nonneg (N : ℕ) : 0 ≤ primeGapWeight N := by
  dsimp [primeGapWeight]
  split_ifs
  · exact le_refl 0
  · exact Nat.cast_nonneg _

lemma primeGapWeight_ge_two_of_composite (N : ℕ) (hN : 4 ≤ N) (hcomp : ¬ Nat.Prime N) :
    2 ≤ primeGapWeight N := by
  dsimp [primeGapWeight]
  have hcond : ¬ (N < 2 ∨ Nat.Prime N) := fun h => h.elim (by omega) hcomp
  simp only [hcond, ↓reduceIte]
  have h1 : N + 1 ≤ p_next N := p_next_gt_of_not_prime N hcomp
  have h2 : p_prev N ≤ N - 1 := p_prev_le_pred_of_not_prime N hcomp
  have hdiff : 2 ≤ p_next N - p_prev N := by omega
  exact_mod_cast hdiff

lemma even_ge_four_not_prime (j : ℕ) (hj : 2 ≤ j) : ¬ Nat.Prime (2 * j) := by
  intro hp
  have hdvd : 2 ∣ 2 * j := dvd_mul_right 2 j
  rcases hp.eq_one_or_self_of_dvd 2 hdvd with h1 | h2
  · omega
  · omega

-- ==============================================================================
-- PART II: CONCRETE COMPLEX MONOPOLAR SUM M(K; β, γ)
-- ==============================================================================

/-- Single integer term of the monopolar scale drift sum in ℂ -/
noncomputable def monopolarTerm (g : ℕ → ℝ) (β γ : ℝ) (N : ℕ) : ℂ :=
  ((g N * (Real.sinh ((β - 1 / 2) * Real.log N) / Real.sqrt N) : ℝ) : ℂ) *
    Complex.exp (-(γ * Real.log N : ℝ) * Complex.I)

/-- Global monopolar partial sum M(K; β, γ) up to cutoff K -/
noncomputable def globalMonopolarSum (g : ℕ → ℝ) (β γ : ℝ) (K : ℕ) : ℂ :=
  ∑ N ∈ Finset.range (K + 1), monopolarTerm g β γ N

/-- Boundedness predicate for the global monopolar partial sums -/
def GlobalMonopolarBounded (g : ℕ → ℝ) (β γ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ K : ℕ, ‖globalMonopolarSum g β γ K‖ ≤ C

lemma monopolarTerm_re (g : ℕ → ℝ) (β γ : ℝ) (N : ℕ) :
    (monopolarTerm g β γ N).re =
      g N * (Real.sinh ((β - 1 / 2) * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N) := by
  dsimp [monopolarTerm]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have harg : -(γ * Real.log N : ℝ) * Complex.I = ((-(γ * Real.log N) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

lemma sum_Ioc_eq_sub (f : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    ∑ N ∈ Finset.Ioc A B, f N =
      (∑ N ∈ Finset.range (B + 1), f N) - (∑ N ∈ Finset.range (A + 1), f N) := by
  have hsub : Finset.range (A + 1) ⊆ Finset.range (B + 1) :=
    Finset.range_mono (Nat.succ_le_succ hAB)
  have hsdiff : Finset.range (B + 1) \ Finset.range (A + 1) = Finset.Ioc A B := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]

-- ==============================================================================
-- PART III: ELEMENTARY ANALYTIC LOWER BOUNDS (sinh x ≥ x/2, cos ≥ 1/2)
-- ==============================================================================

lemma half_le_sinh_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x / 2 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma cos_ge_half_of_close_to_two_pi_mul (x : ℝ) (k : ℕ)
    (hlo : 2 * Real.pi * k - Real.pi / 3 ≤ x)
    (hhi : x ≤ 2 * Real.pi * k + Real.pi / 3) :
    (1 / 2 : ℝ) ≤ Real.cos x := by
  have hper : Real.cos x = Real.cos (x - (k : ℤ) * (2 * Real.pi)) := by
    rw [Real.cos_sub_int_mul_two_pi]
  rw [hper]
  set t := x - (k : ℤ) * (2 * Real.pi)
  have ht_abs : |t| ≤ Real.pi / 3 := by
    rw [abs_le]
    have hk : ((k : ℤ) : ℝ) * (2 * Real.pi) = 2 * Real.pi * (k : ℝ) := by push_cast; ring
    dsimp [t]
    rw [hk]
    constructor <;> linarith
  rw [← Real.cos_abs t]
  have hpi : |t| ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos_le := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) (by linarith [Real.pi_pos]) ht_abs
  rw [Real.cos_pi_div_three] at hcos_le
  exact hcos_le

-- ==============================================================================
-- PART IV: BLOCK LOWER BOUND OVER EVEN COMPOSITE INTEGERS IN [A, B]
-- ==============================================================================

/--
  Key Coherent-Window Lower Bound:
  If 4 ≤ A ≤ B and cos(γ * ln N) ≥ 1/2 for every N ∈ (A, B], then
    |(M(B) - M(A)).re| ≥ ((B / 2 - A / 2 : ℕ) : ℝ) * (|β - 1/2| * ln 2 / (2 * √B)).
-/
lemma coherent_block_lower_bound (g : ℕ → ℝ) (β γ : ℝ)
    (hg_nonneg : ∀ N, 0 ≤ g N)
    (hg_comp : ∀ N, 4 ≤ N → ¬ Nat.Prime N → 2 ≤ g N)
    (A B : ℕ) (hA4 : 4 ≤ A) (hAB : A ≤ B)
    (hcos : ∀ N ∈ Finset.Ioc A B, (1 / 2 : ℝ) ≤ Real.cos (γ * Real.log N)) :
    ((B / 2 - A / 2 : ℕ) : ℝ) * (|β - 1 / 2| * Real.log 2 / (2 * Real.sqrt B)) ≤
      ‖globalMonopolarSum g β γ B - globalMonopolarSum g β γ A‖ := by
  set δ := |β - 1 / 2|
  have hδ_nonneg : 0 ≤ δ := abs_nonneg _
  set sgn : ℝ := if 0 ≤ β - 1 / 2 then 1 else -1
  have hsgn_abs : |sgn| = 1 := by
    dsimp [sgn]; split_ifs <;> norm_num
  have hsgn_sinh : ∀ N : ℕ, sgn * Real.sinh ((β - 1 / 2) * Real.log N) = Real.sinh (δ * Real.log N) := by
    intro N
    dsimp [sgn, δ]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · have hlt : β - 1 / 2 < 0 := lt_of_not_ge h
      rw [abs_of_neg hlt]
      have : -((β - 1 / 2) * Real.log N) = -(β - 1 / 2) * Real.log N := by ring
      rw [← this, Real.sinh_neg]
      ring
  have hdiff_eq : globalMonopolarSum g β γ B - globalMonopolarSum g β γ A =
      ∑ N ∈ Finset.Ioc A B, monopolarTerm g β γ N :=
    (sum_Ioc_eq_sub (monopolarTerm g β γ) A B hAB).symm
  rw [hdiff_eq]
  have hre_bound : |(∑ N ∈ Finset.Ioc A B, monopolarTerm g β γ N).re| ≤
      ‖∑ N ∈ Finset.Ioc A B, monopolarTerm g β γ N‖ := Complex.abs_re_le_norm _
  refine le_trans ?_ hre_bound
  have hre_sum : (∑ N ∈ Finset.Ioc A B, monopolarTerm g β γ N).re =
      ∑ N ∈ Finset.Ioc A B,
        g N * (Real.sinh ((β - 1 / 2) * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun N _ => monopolarTerm_re g β γ N
  rw [hre_sum]
  have habs_sgn : |∑ N ∈ Finset.Ioc A B,
      g N * (Real.sinh ((β - 1 / 2) * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N)| =
      |∑ N ∈ Finset.Ioc A B,
        g N * (Real.sinh (δ * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N)| := by
    calc |∑ N ∈ Finset.Ioc A B,
            g N * (Real.sinh ((β - 1 / 2) * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N)|
      _ = |sgn * ∑ N ∈ Finset.Ioc A B,
            g N * (Real.sinh ((β - 1 / 2) * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N)| := by
          rw [abs_mul, hsgn_abs, one_mul]
      _ = |∑ N ∈ Finset.Ioc A B,
            g N * (Real.sinh (δ * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N)| := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun N _ => ?_
          rw [← hsgn_sinh N]
          ring
  rw [habs_sgn]
  -- Every term in the signed sum on Ioc A B is non-negative
  have hterm_nonneg : ∀ N ∈ Finset.Ioc A B,
      0 ≤ g N * (Real.sinh (δ * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N) := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 4 < N := lt_of_le_of_lt hA4 (Finset.mem_Ioc.mp hN).1
      exact_mod_cast (by omega : 1 ≤ N)
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have hsinh : 0 ≤ Real.sinh (δ * Real.log (N : ℝ)) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg hδ_nonneg hlog)
    have hcosN : 0 ≤ Real.cos (γ * Real.log (N : ℝ)) := le_trans (by norm_num) (hcos N hN)
    exact mul_nonneg (mul_nonneg (hg_nonneg N) (div_nonneg hsinh (Real.sqrt_nonneg _))) hcosN
  have hsum_nonneg : 0 ≤ ∑ N ∈ Finset.Ioc A B,
      g N * (Real.sinh (δ * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N) :=
    Finset.sum_nonneg hterm_nonneg
  rw [abs_of_nonneg hsum_nonneg]
  -- Restrict sum to even integers 2*j for j ∈ Icc (A/2 + 1) (B/2)
  set E := (Finset.Icc (A / 2 + 1) (B / 2)).image (fun j => 2 * j)
  have hE_sub : E ⊆ Finset.Ioc A B := by
    intro N hN
    rcases Finset.mem_image.mp hN with ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ioc]
    omega
  have hsum_ge_E := Finset.sum_le_sum_of_subset_of_nonneg hE_sub (fun N hN _ => hterm_nonneg N hN)
  refine le_trans ?_ hsum_ge_E
  -- Lower bound each term on E
  have hterm_E : ∀ N ∈ E,
      δ * Real.log 2 / (2 * Real.sqrt B) ≤
        g N * (Real.sinh (δ * Real.log N) / Real.sqrt N) * Real.cos (γ * Real.log N) := by
    intro N hN
    rcases Finset.mem_image.mp hN with ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    have hj2 : 2 ≤ j := by omega
    have hN4 : 4 ≤ 2 * j := by omega
    have hcomp : ¬ Nat.Prime (2 * j) := even_ge_four_not_prime j hj2
    have hg2 : 2 ≤ g (2 * j) := hg_comp (2 * j) hN4 hcomp
    have hN_mem : 2 * j ∈ Finset.Ioc A B := hE_sub hN
    have hcos_half : (1 / 2 : ℝ) ≤ Real.cos (γ * Real.log (2 * j : ℕ)) := hcos (2 * j) hN_mem
    have hN_le_B : ((2 * j : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp hN_mem).2
    have hN_pos : (0 : ℝ) < ((2 * j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * j)
    have hsqrt_pos : 0 < Real.sqrt ((2 * j : ℕ) : ℝ) := Real.sqrt_pos.mpr hN_pos
    have hsqrt_le : Real.sqrt ((2 * j : ℕ) : ℝ) ≤ Real.sqrt (B : ℝ) := Real.sqrt_le_sqrt hN_le_B
    have hlog2_le : Real.log 2 ≤ Real.log ((2 * j : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ 2 * j))
    have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hsinh_ge : δ * Real.log 2 / 2 ≤ Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) := by
      have hx : 0 ≤ δ * Real.log ((2 * j : ℕ) : ℝ) :=
        mul_nonneg hδ_nonneg (le_trans hlog2_nonneg hlog2_le)
      calc δ * Real.log 2 / 2
        _ ≤ δ * Real.log ((2 * j : ℕ) : ℝ) / 2 := by
            gcongr
        _ ≤ Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) := half_le_sinh_of_nonneg hx
    have hdiv_ge : δ * Real.log 2 / (2 * Real.sqrt (B : ℝ)) ≤
        Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) / Real.sqrt ((2 * j : ℕ) : ℝ) := by
      calc δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))
        _ = (δ * Real.log 2 / 2) / Real.sqrt (B : ℝ) := by ring
        _ ≤ (δ * Real.log 2 / 2) / Real.sqrt ((2 * j : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt_le
        _ ≤ Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) / Real.sqrt ((2 * j : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_right hsinh_ge (le_of_lt hsqrt_pos)
    have h1 : (2 : ℝ) * (δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))) * (1 / 2) =
        δ * Real.log 2 / (2 * Real.sqrt (B : ℝ)) := by ring
    calc δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))
      _ = 2 * (δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))) * (1 / 2) := h1.symm
      _ ≤ g (2 * j) * (Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) / Real.sqrt ((2 * j : ℕ) : ℝ)) *
          Real.cos (γ * Real.log ((2 * j : ℕ) : ℝ)) := by
          have hpos1 : 0 ≤ δ * Real.log 2 / (2 * Real.sqrt (B : ℝ)) := by positivity
          have hpos2 : 0 ≤ g (2 * j) *
              (Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) / Real.sqrt ((2 * j : ℕ) : ℝ)) := by
            have hsinh0 : 0 ≤ Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) :=
              le_trans (by positivity) hsinh_ge
            exact mul_nonneg (hg_nonneg _) (div_nonneg hsinh0 (le_of_lt hsqrt_pos))
          have hmul1 : 2 * (δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))) ≤
              g (2 * j) * (Real.sinh (δ * Real.log ((2 * j : ℕ) : ℝ)) / Real.sqrt ((2 * j : ℕ) : ℝ)) :=
            mul_le_mul hg2 hdiv_ge hpos1 (hg_nonneg _)
          exact mul_le_mul hmul1 hcos_half (by norm_num) hpos2
  have hsum_const := Finset.sum_le_sum hterm_E
  rw [Finset.sum_const, nsmul_eq_mul] at hsum_const
  -- Compute cardinality of E = B/2 - A/2
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun _ _ h => by dsimp at h; omega
  have hcard : E.card = B / 2 - A / 2 := by
    dsimp [E]
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  rw [hcard] at hsum_const
  exact hsum_const

-- ==============================================================================
-- PART V: UNCONDITIONAL PROOF OF `MonopolarOmegaDivergenceTarget`
-- ==============================================================================

/--
  MAIN THEOREM (Unconditional Proof of `MonopolarOmegaDivergenceTarget`):
  For ANY weight g ≥ 0 satisfying g(N) ≥ 2 on composite integers N ≥ 4
  (in particular `primeGapWeight`), ANY β ≠ 1/2, and ANY γ ∈ ℝ,
  the global complex monopolar partial sum M(K; β, γ) is UNBOUNDED.
  (0 'sorry', 0 hidden axioms.)
-/
theorem monopolar_unbounded_of_ne_half (g : ℕ → ℝ) (β γ : ℝ)
    (hg_nonneg : ∀ N, 0 ≤ g N)
    (hg_comp : ∀ N, 4 ≤ N → ¬ Nat.Prime N → 2 ≤ g N)
    (hβ : β ≠ 1 / 2) :
    ¬ GlobalMonopolarBounded g β γ := by
  intro ⟨C, hC⟩
  set δ := |β - 1 / 2|
  have hδ_pos : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hβ)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C' := max C 0
  have hC'_nonneg : 0 ≤ C' := le_max_right C 0
  have hdiff_bdd : ∀ A B : ℕ, ‖globalMonopolarSum g β γ B - globalMonopolarSum g β γ A‖ ≤ 2 * C' := by
    intro A B
    calc ‖globalMonopolarSum g β γ B - globalMonopolarSum g β γ A‖
      _ ≤ ‖globalMonopolarSum g β γ B‖ + ‖globalMonopolarSum g β γ A‖ := norm_sub_le _ _
      _ ≤ C' + C' := add_le_add (le_trans (hC B) (le_max_left C 0))
                                (le_trans (hC A) (le_max_left C 0))
      _ = 2 * C' := by ring
  by_cases hγ : γ = 0
  · -- Case 1: γ = 0 (cos(0) = 1 ≥ 1/2 everywhere)
    subst hγ
    set c0 := δ * Real.log 2 / 2
    have hc0_pos : 0 < c0 := by positivity
    -- Pick m large enough so that √m * c0 / 2 > 2 * C'
    obtain ⟨m, hm⟩ := exists_nat_gt (max 4 ((4 * C' / c0 + 1) ^ 2))
    have hm4 : 4 < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
    have hm_gt : (4 * C' / c0 + 1) ^ 2 < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
    have hB_le : (2 * m + 4 : ℝ) ≤ 4 * (m : ℝ) := by linarith
    have hsqrt_le : Real.sqrt (2 * m + 4 : ℕ) ≤ 2 * Real.sqrt m := by
      have hcast : ((2 * m + 4 : ℕ) : ℝ) = 2 * (m : ℝ) + 4 := by push_cast; ring
      rw [hcast]
      calc Real.sqrt (2 * (m : ℝ) + 4)
        _ ≤ Real.sqrt (4 * (m : ℝ)) := Real.sqrt_le_sqrt hB_le
        _ = Real.sqrt 4 * Real.sqrt m := Real.sqrt_mul (by norm_num) _
        _ = 2 * Real.sqrt m := by
            have : Real.sqrt 4 = 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            rw [this]
    have hlb := coherent_block_lower_bound g β 0 hg_nonneg hg_comp 4 (2 * m + 4)
      (le_refl 4) (by omega) (fun N _ => by simp; norm_num)
    have hcard_eq : (2 * m + 4) / 2 - 4 / 2 = m := by omega
    rw [hcard_eq] at hlb
    have hbdd := hdiff_bdd 4 (2 * m + 4)
    have hcomb := le_trans hlb hbdd
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have hsqrtm_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
    have hsqrtB_pos : 0 < Real.sqrt (2 * m + 4 : ℕ) := by
      apply Real.sqrt_pos.mpr; positivity
    have hge_half : (Real.sqrt m / 2) * c0 ≤
        (m : ℝ) * (δ * Real.log 2 / (2 * Real.sqrt (2 * m + 4 : ℕ))) := by
      calc (Real.sqrt m / 2) * c0
        _ = (m : ℝ) * (δ * Real.log 2 / (2 * (2 * Real.sqrt m))) := by
            have hsq : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt (le_of_lt hm_pos)
            dsimp [c0]
            field_simp [ne_of_gt hsqrtm_pos]
            linarith [hsq]
        _ ≤ (m : ℝ) * (δ * Real.log 2 / (2 * Real.sqrt (2 * m + 4 : ℕ))) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hm_pos)
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            linarith
    have hgt_bound : 2 * C' < (Real.sqrt m / 2) * c0 := by
      have hsqrt_gt : 4 * C' / c0 + 1 < Real.sqrt m := by
        have hnonneg : 0 ≤ 4 * C' / c0 + 1 := by positivity
        rw [← Real.sqrt_sq hnonneg]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) hm_gt
      have h1 : (4 * C' / c0 + 1) * (c0 / 2) < Real.sqrt m * (c0 / 2) :=
        mul_lt_mul_of_pos_right hsqrt_gt (by positivity)
      have h2 : (4 * C' / c0 + 1) * (c0 / 2) = 2 * C' + c0 / 2 := by
        field_simp [ne_of_gt hc0_pos]; ring
      linarith
    linarith
  · -- Case 2: γ ≠ 0 (Coherent logarithmic phase windows [exp((2πk - π/3)/|γ|), exp((2πk + π/3)/|γ|)])
    set ω := |γ|
    have hω_pos : 0 < ω := abs_pos.mpr hγ
    set q := Real.exp (2 * Real.pi / (3 * ω))
    have hq_gt_one : 1 < q := Real.one_lt_exp_iff.mpr (by positivity)
    have hq_pos : 0 < q := by linarith
    have hq_sub_pos : 0 < q - 1 := by linarith
    -- Constant factor K_const > 0 such that block sum ≥ K_const * √(a_k)
    set K_const := (q - 1) * δ * Real.log 2 / (8 * Real.sqrt q)
    have hK_pos : 0 < K_const := by positivity
    -- Choose threshold T so that: a_k ≥ T implies a_k ≥ 4, (q - 1) * a_k ≥ 16, and K_const * √(a_k) > 2 * C'
    set T := max (max 4 (16 / (q - 1))) ((2 * C' / K_const + 1) ^ 2)
    have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
    -- Pick k : ℕ so large that a_k = exp((2πk - π/3)/ω) ≥ T
    obtain ⟨k, hk⟩ := exists_nat_gt ((ω * Real.log T + Real.pi / 3) / (2 * Real.pi))
    set a_k := Real.exp ((2 * Real.pi * (k : ℝ) - Real.pi / 3) / ω)
    set b_k := Real.exp ((2 * Real.pi * (k : ℝ) + Real.pi / 3) / ω)
    have ha_ge_T : T ≤ a_k := by
      have harg : Real.log T ≤ (2 * Real.pi * (k : ℝ) - Real.pi / 3) / ω := by
        have hpi2 : 0 < 2 * Real.pi := by positivity
        have h1 : (ω * Real.log T + Real.pi / 3) < 2 * Real.pi * (k : ℝ) := by
          have := (div_lt_iff₀ hpi2).mp hk
          linarith
        exact (le_div_iff₀ hω_pos).mpr (by linarith)
      calc T = Real.exp (Real.log T) := (Real.exp_log hT_pos).symm
        _ ≤ a_k := Real.exp_le_exp.mpr harg
    have ha_ge_4 : 4 ≤ a_k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha_ge_T
    have ha_pos : 0 < a_k := by linarith
    have hgap_ge_16 : 16 ≤ (q - 1) * a_k := by
      have h1 : 16 / (q - 1) ≤ a_k :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha_ge_T
      have h2 := (div_le_iff₀ hq_sub_pos).mp h1
      linarith
    have hb_eq : b_k = q * a_k := by
      dsimp [b_k, q, a_k]
      rw [← Real.exp_add]
      congr 1
      field_simp [ne_of_gt hω_pos]
      ring
    -- Natural endpoints A = ⌈a_k⌉₊, B = ⌊b_k⌋₊
    set A := Nat.ceil a_k
    set B := Nat.floor b_k
    have hA_ge_a : a_k ≤ (A : ℝ) := Nat.le_ceil a_k
    have hA_lt : (A : ℝ) < a_k + 1 := Nat.ceil_lt_add_one (le_of_lt ha_pos)
    have hB_le_b : (B : ℝ) ≤ b_k := Nat.floor_le (by positivity)
    have hB_gt : b_k - 1 < (B : ℝ) := Nat.sub_one_lt_floor b_k
    have hA4 : 4 ≤ A := by
      have : (4 : ℝ) ≤ (A : ℝ) := le_trans ha_ge_4 hA_ge_a
      exact_mod_cast this
    have hBA_real : (q - 1) * a_k - 2 < (B : ℝ) - (A : ℝ) := by linarith [hb_eq]
    have hAB : A ≤ B := by
      have : (A : ℝ) < (B : ℝ) := by linarith
      exact_mod_cast le_of_lt this
    -- Verify cos(γ * log N) ≥ 1/2 for all N ∈ Ioc A B
    have hcos_block : ∀ N ∈ Finset.Ioc A B, (1 / 2 : ℝ) ≤ Real.cos (γ * Real.log N) := by
      intro N hN
      rw [Finset.mem_Ioc] at hN
      have hN_ge_a : a_k ≤ (N : ℝ) := le_trans hA_ge_a (by exact_mod_cast le_of_lt hN.1)
      have hN_le_b : (N : ℝ) ≤ b_k := le_trans (by exact_mod_cast hN.2) hB_le_b
      have hlog_lo : (2 * Real.pi * (k : ℝ) - Real.pi / 3) / ω ≤ Real.log (N : ℝ) := by
        have := Real.log_le_log ha_pos hN_ge_a
        rwa [Real.log_exp] at this
      have hlog_hi : Real.log (N : ℝ) ≤ (2 * Real.pi * (k : ℝ) + Real.pi / 3) / ω := by
        have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le ha_pos hN_ge_a
        have := Real.log_le_log hN_pos hN_le_b
        rwa [Real.log_exp] at this
      have hmul_lo : 2 * Real.pi * (k : ℝ) - Real.pi / 3 ≤ ω * Real.log (N : ℝ) := by
        have := mul_le_mul_of_nonneg_left hlog_lo (le_of_lt hω_pos)
        rwa [mul_div_cancel₀ _ (ne_of_gt hω_pos)] at this
      have hmul_hi : ω * Real.log (N : ℝ) ≤ 2 * Real.pi * (k : ℝ) + Real.pi / 3 := by
        have := mul_le_mul_of_nonneg_left hlog_hi (le_of_lt hω_pos)
        rwa [mul_div_cancel₀ _ (ne_of_gt hω_pos)] at this
      have hcos_abs : Real.cos (γ * Real.log (N : ℝ)) = Real.cos (ω * Real.log (N : ℝ)) := by
        dsimp [ω]
        rcases le_or_gt 0 γ with hγp | hγn
        · rw [abs_of_nonneg hγp]
        · rw [abs_of_neg hγn, neg_mul, Real.cos_neg]
      rw [hcos_abs]
      exact cos_ge_half_of_close_to_two_pi_mul (ω * Real.log (N : ℝ)) k hmul_lo hmul_hi
    -- Apply coherent_block_lower_bound
    have hlb := coherent_block_lower_bound g β γ hg_nonneg hg_comp A B hA4 hAB hcos_block
    have hbdd := hdiff_bdd A B
    have hcomb := le_trans hlb hbdd
    -- Lower bound the cardinality (B/2 - A/2) ≥ (q - 1) * a_k / 4
    have hcard_ge : (q - 1) * a_k / 4 ≤ ((B / 2 - A / 2 : ℕ) : ℝ) := by
      have hnat_bound : B - A ≤ 2 * (B / 2 - A / 2) + 2 := by omega
      have hreal_bound : (B : ℝ) - (A : ℝ) ≤ 2 * ((B / 2 - A / 2 : ℕ) : ℝ) + 2 := by
        have h1 : ((B - A : ℕ) : ℝ) ≤ ((2 * (B / 2 - A / 2) + 2 : ℕ) : ℝ) := by exact_mod_cast hnat_bound
        rw [Nat.cast_sub hAB] at h1
        push_cast at h1
        exact h1
      linarith
    -- Upper bound √B ≤ √q * √a_k
    have hsqrtB_le : Real.sqrt (B : ℝ) ≤ Real.sqrt q * Real.sqrt a_k := by
      calc Real.sqrt (B : ℝ)
        _ ≤ Real.sqrt b_k := Real.sqrt_le_sqrt hB_le_b
        _ = Real.sqrt (q * a_k) := by rw [hb_eq]
        _ = Real.sqrt q * Real.sqrt a_k := Real.sqrt_mul (le_of_lt hq_pos) a_k
    have hsqrtB_pos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < B))
    have hsqrta_pos : 0 < Real.sqrt a_k := Real.sqrt_pos.mpr ha_pos
    have hsqrtq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
    have hstep_ge : K_const * Real.sqrt a_k ≤
        ((B / 2 - A / 2 : ℕ) : ℝ) * (δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))) := by
      calc K_const * Real.sqrt a_k
        _ = ((q - 1) * a_k / 4) * (δ * Real.log 2 / (2 * (Real.sqrt q * Real.sqrt a_k))) := by
            have hsq : Real.sqrt a_k * Real.sqrt a_k = a_k := Real.mul_self_sqrt (le_of_lt ha_pos)
            dsimp [K_const]
            field_simp [ne_of_gt hsqrta_pos, ne_of_gt hsqrtq_pos]
            nlinarith [hsq]
        _ ≤ ((B / 2 - A / 2 : ℕ) : ℝ) * (δ * Real.log 2 / (2 * Real.sqrt (B : ℝ))) := by
            apply mul_le_mul hcard_ge _ (by positivity) (Nat.cast_nonneg _)
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            linarith
    have hgt_bound : 2 * C' < K_const * Real.sqrt a_k := by
      have ha_sq : (2 * C' / K_const + 1) ^ 2 ≤ a_k :=
        le_trans (le_max_right _ _) ha_ge_T
      have hsqrt_ge : 2 * C' / K_const + 1 ≤ Real.sqrt a_k := by
        have hnn : 0 ≤ 2 * C' / K_const + 1 := by positivity
        rw [← Real.sqrt_sq hnn]
        exact Real.sqrt_le_sqrt ha_sq
      have h1 : K_const * (2 * C' / K_const + 1) ≤ K_const * Real.sqrt a_k :=
        mul_le_mul_of_nonneg_left hsqrt_ge (le_of_lt hK_pos)
      have h2 : K_const * (2 * C' / K_const + 1) = 2 * C' + K_const := by
        field_simp [ne_of_gt hK_pos]
      linarith
    linarith

/--
  COROLLARY (Formal Closure of `MonopolarOmegaDivergenceTarget` in Mathlib4):
  Instantiating `GlobalMonopolarBounded` with the exact arithmetic prime-gap weight
  `primeGapWeight(N) = p_next(N) - p_prev(N)` closes `MonopolarOmegaDivergenceTarget`
  100% unconditionally with 0 'sorry' and 0 axioms.
-/
theorem monopolar_omega_divergence_target_proved :
    MonopolarOmegaDivergenceTarget (GlobalMonopolarBounded primeGapWeight) := by
  intro beta gamma hbeta
  exact monopolar_unbounded_of_ne_half primeGapWeight beta gamma
    primeGapWeight_nonneg primeGapWeight_ge_two_of_composite hbeta

/--
  SINGLE-TARGET REDUCTION OF THE RIEMANN HYPOTHESIS ON MATHLIB4 `riemannZeta`:
  Because `MonopolarOmegaDivergenceTarget` is now PROVED UNCONDITIONALLY,
  the entire Riemann Hypothesis in Mathlib4 reduces formally to the SINGLE
  open target `SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight)`.
-/
theorem riemann_hypothesis_from_single_spectral_bridge
    (h_bridge : SpectralBridgeTarget (GlobalMonopolarBounded primeGapWeight))
    (beta gamma : ℝ)
    (h_zero : IsNonTrivialZetaZero beta gamma) :
    beta = 1 / 2 :=
  riemann_hypothesis_from_targets (GlobalMonopolarBounded primeGapWeight)
    h_bridge monopolar_omega_divergence_target_proved beta gamma h_zero

end UnconditionalMonopolarDivergence
