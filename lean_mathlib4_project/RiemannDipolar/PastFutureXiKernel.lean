/-
  ==============================================================================
  EXACT PAST-FUTURE GEODESIC KERNEL OF RIEMANN XI, TRIGONOMETRIC ROTOR CLOSURE,
  EXACT VON MANGOLDT REPRESENTATION, AND POLYA-JENSEN / WEIL-GRAM FOUNDATIONS

  Title: Exact Past-Future Integral Representation of completedRiemannZeta and
         Riemann Xi, Analytic Closure of Theorems 2.1 & 4.2, and Foundations for
         Routes A (Adelic Gram Positivity) and B (Polya-Jensen Hyperbolicity)
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I:   Complete analytic closure of Theorem 2.1 in Mathlib4:
              the trigonometric rotor Psi(M) = prod_{q=2}^{floor(sqrt M)} sin^2(pi*M/q)
              satisfies Psi(M) > 0 <-> Nat.Prime M and
              lim_{eps -> 0+} Psi(M) / (Psi(M) + eps) = 1_P(M) for all M >= 2.
  - Part II:  Complete formal closure of Theorem 4.2 (von Mangoldt function as
              exact logarithmic prime-power indicator sum) and unconditional
              non-vanishing of every finite Euler product on Re(s) > 0.
  - Part III: Exact Past-Future Geodesic Integral Representation directly on
              Mathlib4 `completedRiemannZeta₀` and entire `riemannXi`:
              * Exact theta-tail split at t = 1 (t = exp(2u), u > 0 future vs. u < 0 past):
                  completedRiemannZeta₀(beta + i*gamma)
                    = 4 * integral_{0}^{inf} psi(e^{2u}) e^{u/2} cosh(u*(sigma + i*gamma)) du.
              * Boundary derivative F'(0) = -1/4 proved directly from
                `archimedean_jacobiTheta_duality`.
              * Exact double integration by parts establishing Riemann's positive
                past-future Fourier-Laplace kernel Phi(u) > 0 (u >= 0):
                  riemannXi(beta + i*gamma)
                    = 2 * integral_{0}^{inf} Phi(u) * [cosh(sigma*u) cos(gamma*u)
                                                      + i * sinh(sigma*u) sin(gamma*u)] du.
              * Exact equivalence for 0 < beta < 1:
                  riemannZeta(beta + i*gamma) = 0 <->
                    (int_0^inf Phi(u) cosh(sigma*u) cos(gamma*u) du = 0) /\
                    (int_0^inf Phi(u) sinh(sigma*u) sin(gamma*u) du = 0).
  - Part IV:  Polya-Jensen moments b_k = int_0^inf Phi(u) u^{2k} du > 0,
              unconditional Turan / degree-2 Jensen hyperbolicity
              b_{k+1}^2 <= b_k * b_{k+2} for all k : N (Route B foundation),
              and Hermitian Gram positive semi-definiteness (Route A foundation).
  ==============================================================================
-/

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import RiemannDipolar.AnalyticReduction
import RiemannDipolar.Mathlib4Bridge
import RiemannDipolar.CliffordGeodesics
import RiemannDipolar.MonopolarDivergence
import RiemannDipolar.EulerAdelicBridge

open Real Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate
open RiemannAnalyticReduction Mathlib4RiemannBridge UnifiedMathlib4Geodesic
open UnconditionalMonopolarDivergence EulerAdelicBridge

namespace PastFutureXiKernel

-- ==============================================================================
-- PART I: ANALYTIC CLOSURE OF THEOREM 2.1 (TRIGONOMETRIC ROTOR Psi_N)
-- ==============================================================================

/-- The non-circular trigonometric prime rotor:
    Psi(M) = prod_{q = 2}^{floor(sqrt M)} sin^2(pi * M / q). -/
noncomputable def trigRotor (M : ℕ) : ℝ :=
  ∏ q ∈ Finset.Icc 2 (Nat.sqrt M), (Real.sin (Real.pi * (M : ℝ) / (q : ℝ))) ^ 2

lemma trigRotor_nonneg (M : ℕ) : 0 ≤ trigRotor M := by
  dsimp [trigRotor]
  exact Finset.prod_nonneg fun _ _ => sq_nonneg _

lemma sin_pi_nat_div_eq_zero_iff_dvd {M q : ℕ} (hq : 0 < q) :
    Real.sin (Real.pi * (M : ℝ) / (q : ℝ)) = 0 ↔ q ∣ M := by
  rw [Real.sin_eq_zero_iff]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hq_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  constructor
  · rintro ⟨k, hk⟩
    have hmul : (k : ℝ) * (q : ℝ) = (M : ℝ) := by
      have h1 : (k : ℝ) * Real.pi * (q : ℝ) = Real.pi * (M : ℝ) := by
        calc (k : ℝ) * Real.pi * (q : ℝ)
          _ = (Real.pi * (M : ℝ) / (q : ℝ)) * (q : ℝ) := by rw [hk]
          _ = Real.pi * (M : ℝ) := div_mul_cancel₀ _ hq_ne
      have h2 : Real.pi * ((k : ℝ) * (q : ℝ)) = Real.pi * (M : ℝ) := by linarith
      exact mul_left_cancel₀ hpi h2
    have hk_nonneg : 0 ≤ k := by
      by_contra hneg
      push Not at hneg
      have hkr : (k : ℝ) < 0 := Int.cast_lt_zero.mpr hneg
      have hqr : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
      have : (k : ℝ) * (q : ℝ) < 0 := mul_neg_of_neg_of_pos hkr hqr
      linarith [Nat.cast_nonneg (α := ℝ) M]
    have hnat : k.toNat * q = M := by
      have hk_eq : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
        exact_mod_cast this
      have hreal : ((k.toNat * q : ℕ) : ℝ) = (M : ℝ) := by
        push_cast; rw [hk_eq]; exact hmul
      exact Nat.cast_injective hreal
    exact ⟨k.toNat, by rw [mul_comm, hnat]⟩
  · rintro ⟨m, rfl⟩
    refine ⟨(m : ℤ), ?_⟩
    push_cast
    field_simp [hq_ne]

/-- THEOREM I.1 (Analytic Closure of Theorem 2.1 — Exactness of Trigonometric Rotor):
    For every M >= 2, the trigonometric rotor Psi(M) is strictly positive if and
    only if M is prime. -/
theorem trigRotor_pos_iff_prime {M : ℕ} (hM : 2 ≤ M) :
    0 < trigRotor M ↔ Nat.Prime M := by
  rw [deterministic_sieve_iff_prime M hM]
  dsimp [trigRotor]
  constructor
  · intro hpos q hq2 hqsq hdvd
    have hq_le : q ≤ Nat.sqrt M := Nat.le_sqrt.mpr hqsq
    have hmem : q ∈ Finset.Icc 2 (Nat.sqrt M) := Finset.mem_Icc.mpr ⟨hq2, hq_le⟩
    have hsin0 : Real.sin (Real.pi * (M : ℝ) / (q : ℝ)) = 0 :=
      (sin_pi_nat_div_eq_zero_iff_dvd (by omega)).mpr hdvd
    have hprod0 : ∏ r ∈ Finset.Icc 2 (Nat.sqrt M),
        (Real.sin (Real.pi * (M : ℝ) / (r : ℝ))) ^ 2 = 0 :=
      Finset.prod_eq_zero hmem (by rw [hsin0, sq, mul_zero])
    linarith
  · intro hno_dvd
    apply Finset.prod_pos
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hq2, hqle⟩
    have hqsq : q * q ≤ M := Nat.le_sqrt.mp hqle
    have hndvd : ¬ (q ∣ M) := hno_dvd q hq2 hqsq
    have hsin_ne : Real.sin (Real.pi * (M : ℝ) / (q : ℝ)) ≠ 0 :=
      mt (sin_pi_nat_div_eq_zero_iff_dvd (by omega)).mp hndvd
    exact sq_pos_of_ne_zero hsin_ne

theorem trigRotor_eq_zero_iff_not_prime {M : ℕ} (hM : 2 ≤ M) :
    trigRotor M = 0 ↔ ¬ Nat.Prime M := by
  constructor
  · intro h0 hp
    have hpos := (trigRotor_pos_iff_prime hM).mpr hp
    linarith
  · intro hnp
    have hnotpos : ¬ (0 < trigRotor M) := mt (trigRotor_pos_iff_prime hM).mp hnp
    exact le_antisymm (le_of_not_gt hnotpos) (trigRotor_nonneg M)

/-- THEOREM I.2 (Exact Analytic Prime Indicator Limit):
    For every M >= 2, lim_{eps -> 0+} Psi(M) / (Psi(M) + eps) equals 1 if M is
    prime and 0 if M is composite. -/
theorem primeIndicator_eq_limit_rotor {M : ℕ} (hM : 2 ≤ M) :
    Tendsto (fun ε : ℝ => trigRotor M / (trigRotor M + ε))
      (𝓝[>] 0) (𝓝 (if Nat.Prime M then (1 : ℝ) else 0)) := by
  by_cases hp : Nat.Prime M
  · simp only [hp, ↓reduceIte]
    have hpos : 0 < trigRotor M := (trigRotor_pos_iff_prime hM).mpr hp
    have hlim : Tendsto (fun ε : ℝ => trigRotor M / (trigRotor M + ε))
        (𝓝 0) (𝓝 (trigRotor M / (trigRotor M + 0))) := by
      refine Tendsto.div tendsto_const_nhds (tendsto_const_nhds.add tendsto_id) ?_
      linarith
    rw [add_zero, div_self (ne_of_gt hpos)] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds
  · simp only [hp, ↓reduceIte]
    have h0 : trigRotor M = 0 := (trigRotor_eq_zero_iff_not_prime hM).mpr hp
    simp only [h0, zero_div]
    exact tendsto_const_nhds

-- ==============================================================================
-- PART II: FORMAL CLOSURE OF THEOREM 4.2 (VON MANGOLDT) & FINITE EULER PRODUCTS
-- ==============================================================================

section VonMangoldt
open Classical

/-- Exact prime-power logarithmic detector at exponent k:
    equals log(N) / k if N = p^k for some prime p, and 0 otherwise. -/
noncomputable def primePowerLogTerm (N k : ℕ) : ℝ :=
  if ∃ p : ℕ, Nat.Prime p ∧ p ^ k = N then Real.log (N : ℝ) / (k : ℝ) else 0

/-- THEOREM II.1 (Formal Closure of Theorem 4.2 — Exact von Mangoldt Sum):
    For every integer N >= 2, Mathlib4's `ArithmeticFunction.vonMangoldt N` equals
    the finite logarithmic prime-power indicator sum over k in [1, floor(log_2 N)]. -/
theorem vonMangoldt_eq_sum_prime_powers {N : ℕ} (hN : 2 ≤ N) :
    ArithmeticFunction.vonMangoldt N =
      ∑ k ∈ Finset.Icc 1 (Nat.log 2 N), primePowerLogTerm N k := by
  by_cases hpp : IsPrimePow N
  · rcases (isPrimePow_nat_iff N).mp hpp with ⟨p, m, hp, hm_pos, rfl⟩
    rw [ArithmeticFunction.vonMangoldt_apply_pow (ne_of_gt hm_pos),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hm_le_log : m ≤ Nat.log 2 (p ^ m) := by
      have h2le : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
      exact (Nat.le_log_iff_pow_le (by norm_num) (by positivity)).mpr h2le
    have hm_mem : m ∈ Finset.Icc 1 (Nat.log 2 (p ^ m)) :=
      Finset.mem_Icc.mpr ⟨hm_pos, hm_le_log⟩
    rw [Finset.sum_eq_single m]
    · dsimp [primePowerLogTerm]
      have hex : ∃ q : ℕ, Nat.Prime q ∧ q ^ m = p ^ m := ⟨p, hp, rfl⟩
      simp only [hex, ↓reduceIte, Nat.cast_pow, Real.log_pow]
      have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm_pos)
      field_simp [hm_ne]
    · intro k hk hkm
      dsimp [primePowerLogTerm]
      have hnot : ¬ ∃ q : ℕ, Nat.Prime q ∧ q ^ k = p ^ m := by
        rintro ⟨q, hq, hqeq⟩
        have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
        have hqp : q = p := by
          have hdvd : q ∣ p ^ m := by
            rw [← hqeq]
            exact dvd_pow_self q (ne_of_gt hk_pos)
          exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
        rw [hqp] at hqeq
        exact hkm (Nat.pow_right_injective hp.two_le hqeq)
      simp [hnot]
    · intro hnotmem
      exact False.elim (hnotmem hm_mem)
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hk_pos : 0 < k := (Finset.mem_Icc.mp hk).1
    dsimp [primePowerLogTerm]
    have hnot : ¬ ∃ p : ℕ, Nat.Prime p ∧ p ^ k = N := by
      rintro ⟨p, hp, hpeq⟩
      exact hpp ((isPrimePow_nat_iff N).mpr ⟨p, k, hp, hk_pos, hpeq⟩)
    simp [hnot]

end VonMangoldt

/-- THEOREM II.2 (Strict Non-Vanishing of Every Finite Euler Product on Re(s) > 0):
    For any cutoff Y : N and any complex s with Re(s) > 0, the finite-place
    truncated Euler product never vanishes. -/
theorem finite_eulerProduct_ne_zero (Y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∏ p ∈ Nat.primesBelow Y, (1 - (p : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hpr : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
  have hp_gt1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hpr.one_lt
  have hnorm_lt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    have hp_pos : (0 : ℝ) < (p : ℕ) := by linarith
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
  have hsub_ne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h0
    have heq : (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
    rw [heq, norm_one] at hnorm_lt
    linarith
  exact inv_ne_zero hsub_ne

-- ==============================================================================
-- PART III: EXACT PAST-FUTURE GEODESIC INTEGRAL OF completedRiemannZeta & XI
-- ==============================================================================

/-- Elementary bound: for x >= 0 and k : N, x^k <= k! * exp(x). -/
lemma pow_le_factorial_mul_exp (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx (k + 1)
  have hterm : x ^ k / (k.factorial : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hle := (div_le_iff₀ hfac_pos).mp (le_trans hterm h)
  linarith

/-- Helper: for any c > 0 and k : N, `n ↦ (n+1)^k * exp(-c * (n+1)^2)` is summable. -/
lemma summable_pow_mul_exp_neg_sq (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let r : ℝ := Real.exp (-(c / 2))
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => ((k.factorial : ℝ) / (c / 2) ^ k) * r ^ (n + 1)) := by
    have h1 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one (le_of_lt hr_pos) hr_lt1
    have h2 : Summable (fun n : ℕ => r ^ (n + 1)) := (summable_nat_add_iff 1).mpr h1
    exact h2.mul_left _
  refine hgeom.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have hm_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hm_le_sq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  have hpow := pow_le_factorial_mul_exp k (x := (c / 2) * ((n + 1 : ℕ) : ℝ)) (by positivity)
  rw [mul_pow] at hpow
  have hc2_pos : 0 < (c / 2) ^ k := by positivity
  have hbound : ((n + 1 : ℕ) : ℝ) ^ k ≤
      ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp ((c / 2) * ((n + 1 : ℕ) : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2_pos]
    linarith
  have hexp_le : Real.exp ((c / 2) * ((n + 1 : ℕ) : ℝ)) *
      Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ r ^ (n + 1) := by
    rw [← Real.exp_add, show r ^ (n + 1) = Real.exp (((n + 1 : ℕ) : ℝ) * -(c / 2)) by
      dsimp [r]; rw [← Real.exp_nat_mul]]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc ((n + 1 : ℕ) : ℝ) ^ k * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)
    _ ≤ (((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp ((c / 2) * ((n + 1 : ℕ) : ℝ))) *
          Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hbound (le_of_lt (Real.exp_pos _))
    _ = ((k.factorial : ℝ) / (c / 2) ^ k) *
          (Real.exp ((c / 2) * ((n + 1 : ℕ) : ℝ)) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) := by ring
    _ ≤ ((k.factorial : ℝ) / (c / 2) ^ k) * r ^ (n + 1) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)

/-- The Jacobi theta tail psi(t) = sum_{n=1}^inf exp(-pi * n^2 * t). -/
noncomputable def jacobiPsi (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)

lemma summable_jacobiPsi_term {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)) := by
  have h := summable_pow_mul_exp_neg_sq 0 (c := Real.pi * t) (by positivity)
  refine h.congr fun n => ?_
  simp only [pow_zero, one_mul]
  congr 1
  ring

/-- Strict positivity of the Jacobi theta tail psi(t) > 0 for every t > 0. -/
theorem jacobiPsi_pos {t : ℝ} (ht : 0 < t) : 0 < jacobiPsi t := by
  dsimp [jacobiPsi]
  exact Summable.tsum_pos (summable_jacobiPsi_term ht)
    (fun n => le_of_lt (Real.exp_pos _)) 0 (Real.exp_pos _)

/-- Exact identity linking jacobiPsi(t) to Mathlib4's `HurwitzZeta.evenKernel 0 t`. -/
theorem two_mul_jacobiPsi_eq_evenKernel_sub_one {t : ℝ} (ht : 0 < t) :
    2 * jacobiPsi t = HurwitzZeta.evenKernel 0 t - 1 := by
  have hcos := HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at hcos
  have hsum : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t))
      (HurwitzZeta.evenKernel 0 t - 1) := by
    rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
    exact hcos.congr_fun fun n => by push_cast; rfl
  rw [← hsum.tsum_eq, jacobiPsi, tsum_mul_left]

/-- Exact link between jacobiPsi(t) and Mathlib4's `jacobiTheta (I * t)`. -/
theorem jacobiPsi_eq_theta_sub_one_div_two {t : ℝ} (ht : 0 < t) :
    (jacobiPsi t : ℂ) = (jacobiTheta (Complex.I * (t : ℂ)) - 1) / 2 := by
  have h1 := two_mul_jacobiPsi_eq_evenKernel_sub_one ht
  have heven : ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) = jacobiTheta (Complex.I * (t : ℂ)) := by
    have h0 : (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := rfl
    rw [h0, HurwitzZeta.evenKernel_def, jacobiTheta_eq_jacobiTheta₂]
    simp
  have hcast : ((2 * jacobiPsi t : ℝ) : ℂ) = jacobiTheta (Complex.I * (t : ℂ)) - 1 := by
    rw [h1, Complex.ofReal_sub, Complex.ofReal_one, heven]
  push_cast at hcast
  linear_combination (1 / 2 : ℂ) * hcast

/-- Functional modular duality of jacobiPsi(t):
    1 + 2 * psi(1/t) = sqrt(t) * (1 + 2 * psi(t)) for all t > 0. -/
theorem jacobiPsi_functional_duality {t : ℝ} (ht : 0 < t) :
    1 + 2 * jacobiPsi (1 / t) = Real.sqrt t * (1 + 2 * jacobiPsi t) := by
  have hduality := archimedean_jacobiTheta_duality ht
  have h1 := jacobiPsi_eq_theta_sub_one_div_two (one_div_pos.mpr ht)
  have h2 := jacobiPsi_eq_theta_sub_one_div_two ht
  have hC : ((1 + 2 * jacobiPsi (1 / t) : ℝ) : ℂ) =
      ((Real.sqrt t * (1 + 2 * jacobiPsi t) : ℝ) : ℂ) := by
    push_cast
    rw [h1, h2]
    linear_combination hduality
  exact Complex.ofReal_injective hC

/-- Explicit upper bound on jacobiPsi(t) for t > 0. -/
lemma jacobiPsi_le {t : ℝ} (ht : 0 < t) :
    jacobiPsi t ≤ Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t)) := by
  let y := Real.exp (-Real.pi * t)
  have hy_pos : 0 < y := Real.exp_pos _
  have hy_lt1 : y < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hgeom : HasSum (fun n : ℕ => y ^ (n + 1)) (y / (1 - y)) := by
    simp_rw [pow_succ', div_eq_mul_inv]
    exact (hasSum_geometric_of_lt_one (le_of_lt hy_pos) hy_lt1).mul_left y
  rw [← hgeom.tsum_eq]
  refine (summable_jacobiPsi_term ht).tsum_le_tsum (fun n => ?_) hgeom.summable
  have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  have hy_pow : y ^ (n + 1) = Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * t) := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hy_pow]
  apply Real.exp_le_exp.mpr
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  nlinarith

/-- The symmetrized past-future theta amplitude F(u) = psi(e^{2u}) * e^{u/2}. -/
noncomputable def thetaHalf (u : ℝ) : ℝ :=
  jacobiPsi (Real.exp (2 * u)) * Real.exp (u / 2)

/-- Individual term f_n(u) = exp(u/2 - pi * (n+1)^2 * e^{2u}) of thetaHalf(u). -/
noncomputable def thetaHalfTerm (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))

/-- First derivative of thetaHalfTerm n at u. -/
noncomputable def thetaHalfTermDeriv (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 2 - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) * thetaHalfTerm n u

/-- Second derivative of thetaHalfTerm n at u. -/
noncomputable def thetaHalfTermDeriv2 (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 4 - 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) +
    4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u)) * thetaHalfTerm n u

/-- First derivative of thetaHalf(u). -/
noncomputable def thetaHalfDeriv (u : ℝ) : ℝ :=
  ∑' n : ℕ, thetaHalfTermDeriv n u

/-- Second derivative of thetaHalf(u). -/
noncomputable def thetaHalfDeriv2 (u : ℝ) : ℝ :=
  ∑' n : ℕ, thetaHalfTermDeriv2 n u

/-- Riemann's exact positive past-future Fourier-Laplace kernel:
    Phi(u) = F''(u) - (1/4) F(u)
           = 2 * sum_{n=1}^inf (2*pi^2*n^4*e^{9u/2} - 3*pi*n^2*e^{5u/2}) exp(-pi*n^2*e^{2u}). -/
noncomputable def riemannPhiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
    6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) * thetaHalfTerm n u

noncomputable def riemannPhi (u : ℝ) : ℝ :=
  ∑' n : ℕ, riemannPhiTerm n u

lemma thetaHalf_eq_tsum (u : ℝ) : thetaHalf u = ∑' n : ℕ, thetaHalfTerm n u := by
  dsimp [thetaHalf, jacobiPsi, thetaHalfTerm]
  rw [← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [← Real.exp_add]
  congr 1
  ring

lemma hasDerivAt_thetaHalfTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaHalfTerm n) (thetaHalfTermDeriv n u) u := by
  change HasDerivAt
    (fun x : ℝ => Real.exp (x / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)))
    ((1 / 2 - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) *
      Real.exp (u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) u
  have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) u := by
    simpa using (hasDerivAt_id u).div_const 2
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * u) * 2) u := by
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
      simpa using (hasDerivAt_id u).const_mul 2
    exact hlin.exp
  have h3 : HasDerivAt (fun x : ℝ => x / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))
      (1 / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * (Real.exp (2 * u) * 2)) u :=
    h1.sub (h2.const_mul _)
  convert h3.exp using 1
  ring

lemma hasDerivAt_thetaHalfTermDeriv (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaHalfTermDeriv n) (thetaHalfTermDeriv2 n u) u := by
  change HasDerivAt
    (fun x : ℝ => (1 / 2 - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)) * thetaHalfTerm n x)
    (thetaHalfTermDeriv2 n u) u
  have hexp2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * u) * 2) u := by
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
      simpa using (hasDerivAt_id u).const_mul 2
    exact hlin.exp
  have hpref : HasDerivAt (fun x : ℝ => 1 / 2 - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))
      (0 - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * (Real.exp (2 * u) * 2)) u :=
    (hasDerivAt_const u (1 / 2 : ℝ)).sub (hexp2.const_mul _)
  have hprod := hpref.mul (hasDerivAt_thetaHalfTerm n u)
  convert hprod using 1
  dsimp [thetaHalfTermDeriv2, thetaHalfTermDeriv]
  have he4 : Real.exp (4 * u) = Real.exp (2 * u) * Real.exp (2 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he4]
  ring

lemma norm_thetaHalfTerm_le_on_Ioo {a R : ℝ} (n : ℕ) {u : ℝ} (hu : u ∈ Ioo a R) :
    ‖thetaHalfTerm n u‖ ≤ Real.exp (R / 2) * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  dsimp [thetaHalfTerm]
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : u / 2 ≤ R / 2 := by linarith [hu.2]
  have h2 : Real.exp (2 * a) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith [hu.1])
  have h3 : Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * a) ≤
      Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

lemma norm_thetaHalfTermDeriv_le_on_Ioo {a R : ℝ} (n : ℕ) {u : ℝ} (hu : u ∈ Ioo a R) :
    ‖thetaHalfTermDeriv n u‖ ≤
      ((1 / 2 + 2 * Real.pi * Real.exp (2 * R)) * Real.exp (R / 2)) *
        (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  dsimp [thetaHalfTermDeriv]
  rw [abs_mul]
  have h1 : |(1 / 2 : ℝ) - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)| ≤
      (1 / 2 + 2 * Real.pi * Real.exp (2 * R)) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hnsq : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have hge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    have he2 : Real.exp (2 * u) ≤ Real.exp (2 * R) := Real.exp_le_exp.mpr (by linarith [hu.2])
    have habs : |(1 / 2 : ℝ) - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)| ≤
        1 / 2 + 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by
      have hpos : 0 ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have hterm2 : 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) ≤
        2 * Real.pi * Real.exp (2 * R) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have h3 := mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)
      linarith
    linarith
  have h2 := norm_thetaHalfTerm_le_on_Ioo n hu
  rw [Real.norm_eq_abs] at h2
  calc |(1 / 2 : ℝ) - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)| * |thetaHalfTerm n u|
    _ ≤ ((1 / 2 + 2 * Real.pi * Real.exp (2 * R)) * ((n + 1 : ℕ) : ℝ) ^ 2) *
          (Real.exp (R / 2) * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = ((1 / 2 + 2 * Real.pi * Real.exp (2 * R)) * Real.exp (R / 2)) *
          (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
        ring

lemma norm_thetaHalfTermDeriv2_le_on_Ioo {a R : ℝ} (n : ℕ) {u : ℝ} (hu : u ∈ Ioo a R) :
    ‖thetaHalfTermDeriv2 n u‖ ≤
      ((1 / 4 + 6 * Real.pi * Real.exp (2 * R) + 4 * Real.pi ^ 2 * Real.exp (4 * R)) * Real.exp (R / 2)) *
        (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  dsimp [thetaHalfTermDeriv2]
  rw [abs_mul]
  have hge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hnsq_ge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hnsq_le : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := by
    have h4 : ((n + 1 : ℕ) : ℝ) ^ 4 = (((n + 1 : ℕ) : ℝ) ^ 2) ^ 2 := by ring
    rw [h4]; nlinarith
  have h1_le : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := le_trans hnsq_ge1 hnsq_le
  have he2 : Real.exp (2 * u) ≤ Real.exp (2 * R) := Real.exp_le_exp.mpr (by linarith [hu.2])
  have he4 : Real.exp (4 * u) ≤ Real.exp (4 * R) := Real.exp_le_exp.mpr (by linarith [hu.2])
  have h1 : |(1 / 4 : ℝ) - 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) +
      4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u)| ≤
      (1 / 4 + 6 * Real.pi * Real.exp (2 * R) + 4 * Real.pi ^ 2 * Real.exp (4 * R)) *
        ((n + 1 : ℕ) : ℝ) ^ 4 := by
    have hp1 : 0 ≤ 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
    have hp2 : 0 ≤ 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) := by positivity
    have habs : |(1 / 4 : ℝ) - 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) +
        4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u)| ≤
        1 / 4 + 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) +
        4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) := by
      rw [abs_le]
      constructor <;> linarith
    have ht1 : 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) ≤
        6 * Real.pi * Real.exp (2 * R) * ((n + 1 : ℕ) : ℝ) ^ 4 := by
      have h_a : 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) ≤
          6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (2 * R) := by
        have := mul_le_mul hnsq_le he2 (le_of_lt (Real.exp_pos _)) (by positivity)
        nlinarith [Real.pi_pos]
      linarith
    have ht2 : 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) ≤
        4 * Real.pi ^ 2 * Real.exp (4 * R) * ((n + 1 : ℕ) : ℝ) ^ 4 := by
      have h3 := mul_le_mul_of_nonneg_left he4 (by positivity : 0 ≤ 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4)
      linarith
    linarith
  have h2 := norm_thetaHalfTerm_le_on_Ioo n hu
  rw [Real.norm_eq_abs] at h2
  calc _ ≤ ((1 / 4 + 6 * Real.pi * Real.exp (2 * R) + 4 * Real.pi ^ 2 * Real.exp (4 * R)) *
          ((n + 1 : ℕ) : ℝ) ^ 4) *
          (Real.exp (R / 2) * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = ((1 / 4 + 6 * Real.pi * Real.exp (2 * R) + 4 * Real.pi ^ 2 * Real.exp (4 * R)) * Real.exp (R / 2)) *
          (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi * Real.exp (2 * a)) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
        ring

lemma summable_thetaHalfTerm (u : ℝ) : Summable (fun n => thetaHalfTerm n u) := by
  have hu : u ∈ Ioo (u - 1) (u + 1) := ⟨by linarith, by linarith⟩
  have hmaj : Summable (fun n : ℕ => Real.exp ((u + 1) / 2) *
      (((n + 1 : ℕ) : ℝ) ^ 0 * Real.exp (-(Real.pi * Real.exp (2 * (u - 1))) * ((n + 1 : ℕ) : ℝ) ^ 2))) :=
    (summable_pow_mul_exp_neg_sq 0 (c := Real.pi * Real.exp (2 * (u - 1))) (by positivity)).mul_left _
  refine hmaj.of_norm_bounded fun n => ?_
  simpa only [pow_zero, one_mul] using norm_thetaHalfTerm_le_on_Ioo n hu

lemma summable_thetaHalfTermDeriv (u : ℝ) : Summable (fun n => thetaHalfTermDeriv n u) := by
  have hu : u ∈ Ioo (u - 1) (u + 1) := ⟨by linarith, by linarith⟩
  have hmaj := (summable_pow_mul_exp_neg_sq 2 (c := Real.pi * Real.exp (2 * (u - 1))) (by positivity)).mul_left
    ((1 / 2 + 2 * Real.pi * Real.exp (2 * (u + 1))) * Real.exp ((u + 1) / 2))
  exact hmaj.of_norm_bounded fun n => norm_thetaHalfTermDeriv_le_on_Ioo n hu

lemma summable_thetaHalfTermDeriv2 (u : ℝ) : Summable (fun n => thetaHalfTermDeriv2 n u) := by
  have hu : u ∈ Ioo (u - 1) (u + 1) := ⟨by linarith, by linarith⟩
  have hmaj := (summable_pow_mul_exp_neg_sq 4 (c := Real.pi * Real.exp (2 * (u - 1))) (by positivity)).mul_left
    ((1 / 4 + 6 * Real.pi * Real.exp (2 * (u + 1)) + 4 * Real.pi ^ 2 * Real.exp (4 * (u + 1))) *
      Real.exp ((u + 1) / 2))
  exact hmaj.of_norm_bounded fun n => norm_thetaHalfTermDeriv2_le_on_Ioo n hu

lemma hasDerivAt_thetaHalf (u : ℝ) : HasDerivAt thetaHalf (thetaHalfDeriv u) u := by
  have hfun : thetaHalf = fun z => ∑' n, thetaHalfTerm n z := funext thetaHalf_eq_tsum
  rw [hfun]
  let a := u - 1
  let R := u + 1
  have hu : u ∈ Ioo a R := ⟨by dsimp [a]; linarith, by dsimp [R]; linarith⟩
  have hmaj := (summable_pow_mul_exp_neg_sq 2 (c := Real.pi * Real.exp (2 * a)) (by positivity)).mul_left
    ((1 / 2 + 2 * Real.pi * Real.exp (2 * R)) * Real.exp (R / 2))
  exact hasDerivAt_tsum_of_isPreconnected hmaj isOpen_Ioo (convex_Ioo a R).isPreconnected
    (fun n y _ => hasDerivAt_thetaHalfTerm n y)
    (fun n y hy => norm_thetaHalfTermDeriv_le_on_Ioo n hy)
    hu (summable_thetaHalfTerm u) hu

lemma hasDerivAt_thetaHalfDeriv (u : ℝ) : HasDerivAt thetaHalfDeriv (thetaHalfDeriv2 u) u := by
  let a := u - 1
  let R := u + 1
  have hu : u ∈ Ioo a R := ⟨by dsimp [a]; linarith, by dsimp [R]; linarith⟩
  have hmaj := (summable_pow_mul_exp_neg_sq 4 (c := Real.pi * Real.exp (2 * a)) (by positivity)).mul_left
    ((1 / 4 + 6 * Real.pi * Real.exp (2 * R) + 4 * Real.pi ^ 2 * Real.exp (4 * R)) * Real.exp (R / 2))
  exact hasDerivAt_tsum_of_isPreconnected hmaj isOpen_Ioo (convex_Ioo a R).isPreconnected
    (fun n y _ => hasDerivAt_thetaHalfTermDeriv n y)
    (fun n y hy => norm_thetaHalfTermDeriv2_le_on_Ioo n hy)
    hu (summable_thetaHalfTermDeriv u) hu

/-- Exact algebraic relation: Phi(u) = F''(u) - (1/4) F(u). -/
lemma riemannPhi_eq_deriv2_sub_quarter (u : ℝ) :
    riemannPhi u = thetaHalfDeriv2 u - (1 / 4 : ℝ) * thetaHalf u := by
  rw [riemannPhi, thetaHalfDeriv2, thetaHalf_eq_tsum, ← tsum_mul_left,
      ← (summable_thetaHalfTermDeriv2 u).tsum_sub ((summable_thetaHalfTerm u).mul_left (1 / 4))]
  refine tsum_congr fun n => ?_
  dsimp [riemannPhiTerm, thetaHalfTermDeriv2]
  ring

/-- THEOREM III.1 (Exact Boundary Derivative F'(0) = -1/4 from Jacobi Theta Duality):
    Because G(u) = e^{u/2} + 2 * F(u) = e^{u/2} * theta(i * e^{2u}) is an even
    differentiable function on R (by `archimedean_jacobiTheta_duality`), G'(0) = 0,
    which forces F'(0) = -1/4! -/
theorem thetaHalfDeriv_zero : thetaHalfDeriv 0 = -(1 / 4 : ℝ) := by
  let G : ℝ → ℝ := fun u => Real.exp (u / 2) + 2 * thetaHalf u
  have hGeven : ∀ u : ℝ, G (-u) = G u := by
    intro u
    dsimp [G, thetaHalf]
    have ht_pos : 0 < Real.exp (2 * u) := Real.exp_pos _
    have hinv : Real.exp (2 * -u) = 1 / Real.exp (2 * u) := by
      rw [one_div, ← Real.exp_neg]; congr 1; ring
    have hsqrt : Real.sqrt (Real.exp (2 * u)) = Real.exp u := by
      rw [Real.sqrt_eq_iff_eq_sq (le_of_lt ht_pos) (le_of_lt (Real.exp_pos u)), sq, ← Real.exp_add]
      congr 1; ring
    have hdual := jacobiPsi_functional_duality ht_pos
    rw [← hinv, hsqrt] at hdual
    have he1 : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-u / 2) + 2 * (jacobiPsi (Real.exp (2 * -u)) * Real.exp (-u / 2))
      _ = Real.exp (-u / 2) * (1 + 2 * jacobiPsi (Real.exp (2 * -u))) := by ring
      _ = Real.exp (-u / 2) * (Real.exp u * (1 + 2 * jacobiPsi (Real.exp (2 * u)))) := by rw [hdual]
      _ = (Real.exp (-u / 2) * Real.exp u) * (1 + 2 * jacobiPsi (Real.exp (2 * u))) := by ring
      _ = Real.exp (u / 2) * (1 + 2 * jacobiPsi (Real.exp (2 * u))) := by rw [he1]
      _ = Real.exp (u / 2) + 2 * (jacobiPsi (Real.exp (2 * u)) * Real.exp (u / 2)) := by ring
  have hG_deriv : HasDerivAt G (1 / 2 + 2 * thetaHalfDeriv 0) 0 := by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (0 / 2) * (1 / 2)) 0 := by
      have hlin : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
      exact hlin.exp
    simp only [zero_div, Real.exp_zero, one_mul] at h1
    exact h1.add ((hasDerivAt_thetaHalf 0).const_mul 2)
  have hG_neg_deriv : HasDerivAt (fun x => G (-x)) (-(1 / 2 + 2 * thetaHalfDeriv 0)) 0 := by
    have hG_at_neg0 : HasDerivAt G (1 / 2 + 2 * thetaHalfDeriv 0) (-0) := by
      simpa using hG_deriv
    have hcomp : HasDerivAt (fun x => G (-x)) ((1 / 2 + 2 * thetaHalfDeriv 0) * (-1)) 0 :=
      hG_at_neg0.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have hmul : (1 / 2 + 2 * thetaHalfDeriv 0) * (-1 : ℝ) = -(1 / 2 + 2 * thetaHalfDeriv 0) := by ring
    rwa [hmul] at hcomp
  have heq_fun : (fun x => G (-x)) = G := funext hGeven
  rw [heq_fun] at hG_neg_deriv
  have hval := hG_deriv.unique hG_neg_deriv
  linarith

/-- THEOREM III.1b (Global Past-Future Even Symmetry of Riemann's Kernel Phi(-u) = Phi(u)):
    Because G(u) = e^{u/2} + 2 F(u) is even on all of R, G''(u) - (1/4) G(u) = 2 Phi(u)
    is strictly even across past (u < 0) and future (u > 0) geodesic time. -/
theorem riemannPhi_even (u : ℝ) : riemannPhi (-u) = riemannPhi u := by
  let G : ℝ → ℝ := fun x => Real.exp (x / 2) + 2 * thetaHalf x
  let G' : ℝ → ℝ := fun x => (1 / 2 : ℝ) * Real.exp (x / 2) + 2 * thetaHalfDeriv x
  let G'' : ℝ → ℝ := fun x => (1 / 4 : ℝ) * Real.exp (x / 2) + 2 * thetaHalfDeriv2 x
  have hGeven : ∀ x : ℝ, G (-x) = G x := by
    intro x
    dsimp [G, thetaHalf]
    have ht_pos : 0 < Real.exp (2 * x) := Real.exp_pos _
    have hinv : Real.exp (2 * -x) = 1 / Real.exp (2 * x) := by
      rw [one_div, ← Real.exp_neg]; congr 1; ring
    have hsqrt : Real.sqrt (Real.exp (2 * x)) = Real.exp x := by
      rw [Real.sqrt_eq_iff_eq_sq (le_of_lt ht_pos) (le_of_lt (Real.exp_pos x)), sq, ← Real.exp_add]
      congr 1; ring
    have hdual := jacobiPsi_functional_duality ht_pos
    rw [← hinv, hsqrt] at hdual
    have he1 : Real.exp (-x / 2) * Real.exp x = Real.exp (x / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-x / 2) + 2 * (jacobiPsi (Real.exp (2 * -x)) * Real.exp (-x / 2))
      _ = Real.exp (-x / 2) * (1 + 2 * jacobiPsi (Real.exp (2 * -x))) := by ring
      _ = Real.exp (-x / 2) * (Real.exp x * (1 + 2 * jacobiPsi (Real.exp (2 * x)))) := by rw [hdual]
      _ = (Real.exp (-x / 2) * Real.exp x) * (1 + 2 * jacobiPsi (Real.exp (2 * x))) := by ring
      _ = Real.exp (x / 2) * (1 + 2 * jacobiPsi (Real.exp (2 * x))) := by rw [he1]
      _ = Real.exp (x / 2) + 2 * (jacobiPsi (Real.exp (2 * x)) * Real.exp (x / 2)) := by ring
  have hG1 : ∀ x : ℝ, HasDerivAt G (G' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
      (by simpa using (hasDerivAt_id x).div_const 2 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x).exp
    have h1' : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) ((1 / 2 : ℝ) * Real.exp (x / 2)) x := by
      convert h1 using 1; ring
    exact h1'.add ((hasDerivAt_thetaHalf x).const_mul 2)
  have hG2 : ∀ x : ℝ, HasDerivAt G' (G'' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
      (by simpa using (hasDerivAt_id x).div_const 2 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x).exp
    have h1' : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * Real.exp (y / 2)) ((1 / 4 : ℝ) * Real.exp (x / 2)) x := by
      convert h1.const_mul (1 / 2 : ℝ) using 1; ring
    exact h1'.add ((hasDerivAt_thetaHalfDeriv x).const_mul 2)
  have hG'odd : ∀ x : ℝ, G' (-x) = -G' x := by
    intro x
    have hcomp : HasDerivAt (fun y => G (-y)) (G' (-x) * (-1)) x :=
      (hG1 (-x)).comp x (hasDerivAt_neg x)
    have heq : (fun y => G (-y)) = G := funext hGeven
    rw [heq] at hcomp
    have hval := (hG1 x).unique hcomp
    linarith
  have hG''even : ∀ x : ℝ, G'' (-x) = G'' x := by
    intro x
    have hcomp : HasDerivAt (fun y => G' (-y)) (G'' (-x) * (-1)) x :=
      (hG2 (-x)).comp x (hasDerivAt_neg x)
    have heq : (fun y => G' (-y)) = fun y => -G' y := funext hG'odd
    rw [heq] at hcomp
    have hneg : HasDerivAt (fun y => -G' y) (-G'' x) x := (hG2 x).neg
    have hval := hneg.unique hcomp
    linarith
  have h2phi : ∀ x : ℝ, 2 * riemannPhi x = G'' x - (1 / 4 : ℝ) * G x := by
    intro x
    rw [riemannPhi_eq_deriv2_sub_quarter x]
    dsimp [G, G'']
    ring
  have h1 := h2phi (-u)
  have h2 := h2phi u
  rw [hG''even u, hGeven u] at h1
  linarith

/-- THEOREM III.2 (Strict Positivity of Riemann's Past-Future Kernel Phi(u) > 0 for all u >= 0):
    For every u >= 0, EVERY summand of riemannPhi(u) is strictly positive (since 2*pi > 3),
    hence riemannPhi(u) > 0 unconditionally. -/
theorem riemannPhi_pos_of_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 < riemannPhi u := by
  have hsum : Summable (fun n => riemannPhiTerm n u) := by
    have h1 := summable_thetaHalfTermDeriv2 u
    have h2 := (summable_thetaHalfTerm u).mul_left (1 / 4)
    refine (h1.sub h2).congr fun n => ?_
    dsimp [riemannPhiTerm, thetaHalfTermDeriv2]
    ring
  refine Summable.tsum_pos hsum (fun n => ?_) 0 ?_
  · dsimp [riemannPhiTerm]
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have he2 : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have he4 : Real.exp (4 * u) = Real.exp (2 * u) * Real.exp (2 * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpref : 0 ≤ 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
        6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by
      rw [he4]
      have hfac : 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * (Real.exp (2 * u) * Real.exp (2 * u)) -
          6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) =
          2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) *
            (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) - 3) := by ring
      rw [hfac]
      have hinner : 0 ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) - 3 := by
        have hnsq : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
        have hprod : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by nlinarith
        nlinarith
      exact mul_nonneg (by positivity) hinner
    exact mul_nonneg hpref (le_of_lt (Real.exp_pos _))
  · dsimp [riemannPhiTerm]
    have he2 : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have he4 : Real.exp (4 * u) = Real.exp (2 * u) * Real.exp (2 * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpref : 0 < 4 * Real.pi ^ 2 * ((0 + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) -
        6 * Real.pi * ((0 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by
      rw [he4]
      simp only [Nat.zero_add, Nat.cast_one, one_pow, mul_one]
      have hfac : 4 * Real.pi ^ 2 * (Real.exp (2 * u) * Real.exp (2 * u)) -
          6 * Real.pi * Real.exp (2 * u) =
          2 * Real.pi * Real.exp (2 * u) * (2 * Real.pi * Real.exp (2 * u) - 3) := by ring
      rw [hfac]
      exact mul_pos (by positivity) (by nlinarith)
    exact mul_pos hpref (Real.exp_pos _)

/-- COROLLARY III.2b (Global Strict Positivity of Phi(u) > 0 on ALL of R):
    Combining riemannPhi_pos_of_nonneg with past-future symmetry riemannPhi_even,
    Phi(u) is strictly positive across past (u < 0), present (u = 0), and future (u > 0). -/
theorem riemannPhi_pos (u : ℝ) : 0 < riemannPhi u := by
  rcases le_total 0 u with hu | hu
  · exact riemannPhi_pos_of_nonneg hu
  · rw [← riemannPhi_even u]
    exact riemannPhi_pos_of_nonneg (by linarith)

/-- Super-exponential tail bound for thetaHalf, thetaHalfDeriv, and thetaHalfDeriv2 on u >= 0:
    all three decay faster than exp(-2 * e^{2u}) * C, hence faster than exp(-A * u) for any A! -/
lemma norm_thetaHalf_superexp {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaHalf u‖ ≤ (1 / (1 - Real.exp (-Real.pi))) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) := by
  have ht1 : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have ht_pos : 0 < Real.exp (2 * u) := by linarith
  have hpsi := jacobiPsi_le ht_pos
  have hdenom_le : 1 - Real.exp (-Real.pi) ≤ 1 - Real.exp (-Real.pi * Real.exp (2 * u)) := by
    have : Real.exp (-Real.pi * Real.exp (2 * u)) ≤ Real.exp (-Real.pi) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hdenom_pos : 0 < 1 - Real.exp (-Real.pi) := by
    have : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
    linarith
  have hdiv : Real.exp (-Real.pi * Real.exp (2 * u)) / (1 - Real.exp (-Real.pi * Real.exp (2 * u))) ≤
      Real.exp (-Real.pi * Real.exp (2 * u)) / (1 - Real.exp (-Real.pi)) :=
    div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hdenom_pos hdenom_le
  dsimp [thetaHalf]
  rw [abs_of_pos (mul_pos (jacobiPsi_pos ht_pos) (Real.exp_pos _))]
  calc jacobiPsi (Real.exp (2 * u)) * Real.exp (u / 2)
    _ ≤ (Real.exp (-Real.pi * Real.exp (2 * u)) / (1 - Real.exp (-Real.pi))) * Real.exp (u / 2) :=
        mul_le_mul_of_nonneg_right (le_trans hpsi hdiv) (le_of_lt (Real.exp_pos _))
    _ = (1 / (1 - Real.exp (-Real.pi))) * (Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u))) := by ring
    _ = (1 / (1 - Real.exp (-Real.pi))) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) := by
        rw [← Real.exp_add]; congr 2; ring

lemma norm_thetaHalfDeriv_superexp :
    ∃ C > 0, ∀ v ≥ 0,
      ‖thetaHalfDeriv v‖ ≤ C * Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) := by
  let S : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
  have hS_sum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    summable_pow_mul_exp_neg_sq 2 (by positivity)
  have hS_pos : 0 < S :=
    Summable.tsum_pos hS_sum (fun n => by positivity) 0 (by positivity)
  refine ⟨(1 / 2 + 2 * Real.pi) * S, by positivity, fun v hv => ?_⟩
  have he2_ge1 : (1 : ℝ) ≤ Real.exp (2 * v) := Real.one_le_exp (by linarith)
  have hterm : ∀ n : ℕ, ‖thetaHalfTermDeriv n v‖ ≤
      ((1 / 2 + 2 * Real.pi) * Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v))) *
        (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    intro n
    dsimp [thetaHalfTermDeriv, thetaHalfTerm]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hnsq_ge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    have hpref : |(1 / 2 : ℝ) - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)| ≤
        (1 / 2 + 2 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by
      have hp : 0 ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by positivity
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_pos]
    have hexp : Real.exp (2 * v) * Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)) ≤
        Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) *
          Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : (Real.pi / 2) * Real.exp (2 * v) ≤ (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by
        have := mul_le_mul_of_nonneg_right hnsq_ge1 (by positivity : 0 ≤ (Real.pi / 2) * Real.exp (2 * v))
        linarith
      have hb : (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by
        have := mul_le_mul_of_nonneg_left he2_ge1 (by positivity : 0 ≤ (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
        linarith
      linarith
    calc |(1 / 2 : ℝ) - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)| *
          Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v))
      _ ≤ ((1 / 2 + 2 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)) *
            Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)) :=
          mul_le_mul_of_nonneg_right hpref (le_of_lt (Real.exp_pos _))
      _ = (1 / 2 + 2 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 2 *
            (Real.exp (2 * v) * Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v))) := by ring
      _ ≤ (1 / 2 + 2 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 2 *
            (Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) *
              Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((1 / 2 + 2 * Real.pi) * Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v))) *
            (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by ring
  have hbound_sum := hS_sum.mul_left ((1 / 2 + 2 * Real.pi) * Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)))
  calc ‖thetaHalfDeriv v‖
    _ ≤ ∑' n : ℕ, ‖thetaHalfTermDeriv n v‖ := norm_tsum_le_tsum_norm (summable_thetaHalfTermDeriv v).norm
    _ ≤ ∑' n : ℕ, ((1 / 2 + 2 * Real.pi) * Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v))) *
          (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
        (summable_thetaHalfTermDeriv v).norm.tsum_le_tsum hterm hbound_sum
    _ = ((1 / 2 + 2 * Real.pi) * S) * Real.exp (5 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) := by
        rw [tsum_mul_left]; dsimp [S]; ring

lemma norm_riemannPhi_superexp :
    ∃ C > 0, ∀ v ≥ 0,
      ‖riemannPhi v‖ ≤ C * Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) := by
  let S : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
  have hS_sum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 *
      Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    summable_pow_mul_exp_neg_sq 4 (by positivity)
  have hS_pos : 0 < S :=
    Summable.tsum_pos hS_sum (fun n => by positivity) 0 (by positivity)
  refine ⟨(4 * Real.pi ^ 2 + 6 * Real.pi) * S, by positivity, fun v hv => ?_⟩
  have he2_ge1 : (1 : ℝ) ≤ Real.exp (2 * v) := Real.one_le_exp (by linarith)
  have he4 : Real.exp (4 * v) = Real.exp (2 * v) * Real.exp (2 * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsum_phi : Summable (fun n => riemannPhiTerm n v) := by
    have h1 := summable_thetaHalfTermDeriv2 v
    have h2 := (summable_thetaHalfTerm v).mul_left (1 / 4)
    refine (h1.sub h2).congr fun n => ?_
    dsimp [riemannPhiTerm, thetaHalfTermDeriv2]; ring
  have hterm : ∀ n : ℕ, ‖riemannPhiTerm n v‖ ≤
      ((4 * Real.pi ^ 2 + 6 * Real.pi) * Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v))) *
        (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    intro n
    dsimp [riemannPhiTerm, thetaHalfTerm]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hnsq_ge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hnsq_le : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := by
      have h4 : ((n + 1 : ℕ) : ℝ) ^ 4 = (((n + 1 : ℕ) : ℝ) ^ 2) ^ 2 := by ring
      rw [h4]; nlinarith
    have he2_le4 : Real.exp (2 * v) ≤ Real.exp (4 * v) := by rw [he4]; nlinarith
    have hpref : |4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * v) -
        6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)| ≤
        (4 * Real.pi ^ 2 + 6 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * v) := by
      have hp1 : 0 ≤ 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * v) := by positivity
      have hp2 : 0 ≤ 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by positivity
      have hp2_le : 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) ≤
          6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * v) := by
        have := mul_le_mul hnsq_le he2_le4 (le_of_lt (Real.exp_pos _)) (by positivity)
        nlinarith [Real.pi_pos]
      rw [abs_le]
      constructor <;> linarith
    have hexp : Real.exp (4 * v) * Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)) ≤
        Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) *
          Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : (Real.pi / 2) * Real.exp (2 * v) ≤ (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by
        have := mul_le_mul_of_nonneg_right hnsq_ge1 (by positivity : 0 ≤ (Real.pi / 2) * Real.exp (2 * v))
        linarith
      have hb : (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) := by
        have := mul_le_mul_of_nonneg_left he2_ge1 (by positivity : 0 ≤ (Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
        linarith
      linarith
    calc _ ≤ ((4 * Real.pi ^ 2 + 6 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * v)) *
            Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v)) :=
          mul_le_mul_of_nonneg_right hpref (le_of_lt (Real.exp_pos _))
      _ = (4 * Real.pi ^ 2 + 6 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 4 *
            (Real.exp (4 * v) * Real.exp (v / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v))) := by ring
      _ ≤ (4 * Real.pi ^ 2 + 6 * Real.pi) * ((n + 1 : ℕ) : ℝ) ^ 4 *
            (Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) *
              Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((4 * Real.pi ^ 2 + 6 * Real.pi) * Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v))) *
            (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) := by ring
  have hbound_sum := hS_sum.mul_left ((4 * Real.pi ^ 2 + 6 * Real.pi) * Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)))
  calc ‖riemannPhi v‖
    _ ≤ ∑' n : ℕ, ‖riemannPhiTerm n v‖ := norm_tsum_le_tsum_norm hsum_phi.norm
    _ ≤ ∑' n : ℕ, ((4 * Real.pi ^ 2 + 6 * Real.pi) * Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v))) *
          (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
        hsum_phi.norm.tsum_le_tsum hterm hbound_sum
    _ = ((4 * Real.pi ^ 2 + 6 * Real.pi) * S) * Real.exp (9 * v / 2 - (Real.pi / 2) * Real.exp (2 * v)) := by
        rw [tsum_mul_left]; dsimp [S]; ring

/-- Helper: for any A, c > 0, `exp(A * u - c * exp(2 * u))` is eventually bounded by
    `exp(-u)` and hence integrable on `(0, inf)` and tends to 0 at `+inf`. -/
lemma superexp_eventually_le_exp_neg (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ u in atTop, Real.exp (A * u - c * Real.exp (2 * u)) ≤ Real.exp (-u) := by
  -- Since exp(2u) >= 1 + 2u + 2u^2 for u >= 0, c * exp(2u) >= 2c u^2 dominates (A + 1) u!
  filter_upwards [eventually_ge_atTop (max 1 ((|A| + 1) / (2 * c) + 1))] with u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu2 : (|A| + 1) / (2 * c) + 1 ≤ u := le_trans (le_max_right _ _) hu
  have hquad : 2 * u ^ 2 ≤ Real.exp (2 * u) := by
    have h := pow_le_factorial_mul_exp 2 (x := 2 * u) (by linarith)
    norm_num at h
    linarith
  apply Real.exp_le_exp.mpr
  have hAu : A * u ≤ |A| * u := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
  have hcu : (|A| + 1) * u ≤ 2 * c * u ^ 2 := by
    have hlt : (|A| + 1) / (2 * c) ≤ u := by linarith
    have hmul : |A| + 1 ≤ u * (2 * c) := (div_le_iff₀ (by positivity)).mp hlt
    nlinarith
  nlinarith

lemma integrableOn_superexp (A : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (A * u - c * Real.exp (2 * u))) (Ioi 0) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (superexp_eventually_le_exp_neg A hc)
  let M' := max M 1
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (A * u - c * Real.exp (2 * u))) (Ioc 0 M') :=
    (Continuous.continuousOn (by fun_prop)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (A * u - c * Real.exp (2 * u))) (Ioi M') := by
    refine (integrableOn_exp_mul_Ioi (show (-1 : ℝ) < 0 by norm_num) M').mono'
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (le_of_lt (Real.exp_pos _)), neg_one_mul]
    exact hM u (le_trans (le_max_left M 1) (le_of_lt hu))
  have hunion : Ioi (0 : ℝ) = Ioc 0 M' ∪ Ioi M' := (Ioc_union_Ioi_eq_Ioi (le_trans zero_le_one (le_max_right M 1))).symm
  rw [hunion]
  exact h1.union h2

lemma tendsto_superexp_zero (A : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.exp (A * u - c * Real.exp (2 * u))) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun u => le_of_lt (Real.exp_pos _))
    (superexp_eventually_le_exp_neg A hc) ?_
  exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

lemma norm_complex_cosh_le (u : ℝ) (hu : 0 ≤ u) (w : ℂ) :
    ‖Complex.cosh ((u : ℂ) * w)‖ ≤ Real.exp (|w.re| * u) := by
  rw [Complex.cosh]
  have h1 : ‖Complex.exp ((u : ℂ) * w)‖ ≤ Real.exp (|w.re| * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [le_abs_self w.re]
  have h2 : ‖Complex.exp (-((u : ℂ) * w))‖ ≤ Real.exp (|w.re| * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [neg_le_abs w.re]
  calc ‖(Complex.exp ((u : ℂ) * w) + Complex.exp (-((u : ℂ) * w))) / 2‖
    _ = ‖Complex.exp ((u : ℂ) * w) + Complex.exp (-((u : ℂ) * w))‖ / 2 := by
        rw [norm_div, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp ((u : ℂ) * w)‖ + ‖Complex.exp (-((u : ℂ) * w))‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ (Real.exp (|w.re| * u) + Real.exp (|w.re| * u)) / 2 := by linarith
    _ = Real.exp (|w.re| * u) := by ring

lemma norm_complex_sinh_le (u : ℝ) (hu : 0 ≤ u) (w : ℂ) :
    ‖Complex.sinh ((u : ℂ) * w)‖ ≤ Real.exp (|w.re| * u) := by
  rw [Complex.sinh]
  have h1 : ‖Complex.exp ((u : ℂ) * w)‖ ≤ Real.exp (|w.re| * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [le_abs_self w.re]
  have h2 : ‖Complex.exp (-((u : ℂ) * w))‖ ≤ Real.exp (|w.re| * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [neg_le_abs w.re]
  calc ‖(Complex.exp ((u : ℂ) * w) - Complex.exp (-((u : ℂ) * w))) / 2‖
    _ = ‖Complex.exp ((u : ℂ) * w) - Complex.exp (-((u : ℂ) * w))‖ / 2 := by
        rw [norm_div, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp ((u : ℂ) * w)‖ + ‖Complex.exp (-((u : ℂ) * w))‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp (|w.re| * u) + Real.exp (|w.re| * u)) / 2 := by linarith
    _ = Real.exp (|w.re| * u) := by ring

/-- THEOREM III.3 (Exact Past-Future Geodesic Integral of Mathlib4 `completedRiemannZeta₀`):
    For EVERY complex s = beta + i*gamma, Mathlib4's entire modified completed zeta
    function `completedRiemannZeta₀` equals the exact past-future hyperbolic integral
    along geodesic logarithmic time u in (0, inf):
      completedRiemannZeta₀(beta + i*gamma)
        = 4 * integral_{0}^{inf} psi(e^{2u}) e^{u/2} cosh(u * ((beta - 1/2) + i*gamma)) du. -/
theorem completedRiemannZeta₀_eq_past_future_integral (beta gamma : ℝ) :
    completedRiemannZeta₀ (⟨beta, gamma⟩ : ℂ) =
      4 * ∫ u in Ioi (0 : ℝ),
        ((thetaHalf u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ)) := by
  let s : ℂ := ⟨beta, gamma⟩
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef]
  let f_fut : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun x => P.f x - P.f₀)
  let f_past : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator (fun x => P.f x - (P.ε * ((x ^ (-P.k) : ℝ) : ℂ)) • P.g₀)
  have hP_conv : ∀ z : ℂ, MellinConvergent P.f_modif z :=
    fun z => (P.isStrongFEPair_toStrongFEPair.hasMellin z).1
  have hconv_fut : ∀ z : ℂ, MellinConvergent f_fut z := by
    intro z
    have h_eq : EqOn (fun x : ℝ => (x : ℂ) ^ (z - 1) • f_fut x)
        ((Ioi (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (z - 1) • P.f_modif x)) (Ioi (0 : ℝ)) := by
      intro x _
      by_cases h1 : 1 < x
      · have hmem : x ∈ Ioi (1 : ℝ) := mem_Ioi.mpr h1
        have hnot : x ∉ Ioo (0 : ℝ) 1 := notMem_Ioo_of_ge h1.le
        simp only [f_fut, WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem hmem,
          indicator_of_notMem hnot, add_zero]
      · have hnot : x ∉ Ioi (1 : ℝ) := mem_Ioi.not.mpr h1
        simp only [f_fut, indicator_of_notMem hnot, smul_zero]
    exact ((hP_conv z).indicator measurableSet_Ioi).congr_fun h_eq.symm measurableSet_Ioi
  have hconv_past : ∀ z : ℂ, MellinConvergent f_past z := by
    intro z
    have h_eq : EqOn (fun x : ℝ => (x : ℂ) ^ (z - 1) • f_past x)
        ((Ioo (0 : ℝ) 1).indicator (fun x : ℝ => (x : ℂ) ^ (z - 1) • P.f_modif x)) (Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := mem_Ioi.mp hx
      by_cases h1 : x < 1
      · have hmem : x ∈ Ioo (0 : ℝ) 1 := mem_Ioo.mpr ⟨hx0, h1⟩
        have hnot : x ∉ Ioi (1 : ℝ) := notMem_Ioi.mpr h1.le
        simp only [f_past, WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem hmem,
          indicator_of_notMem hnot, zero_add]
      · have hnot : x ∉ Ioo (0 : ℝ) 1 := fun h => h1 h.2
        simp only [f_past, indicator_of_notMem hnot, smul_zero]
    exact ((hP_conv z).indicator measurableSet_Ioo).congr_fun h_eq.symm measurableSet_Ioi
  have hsplit_mellin : mellin P.f_modif (s / 2) = mellin f_fut (s / 2) + mellin f_past (s / 2) := by
    have hadd := hasMellin_add (hconv_fut (s / 2)) (hconv_past (s / 2))
    exact hadd.2
  -- Change of variables t ↦ 1/t shows mellin f_past (s / 2) = mellin f_fut ((1 - s) / 2)
  have hmellin_past : mellin f_past (s / 2) = mellin f_fut ((1 - s) / 2) := by
    have h1 := mellin_comp_rpow f_fut ((s - 1) / 2) (-1)
    simp only [abs_neg, abs_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one,
      rpow_neg_one, ← one_div] at h1
    have hneg : -((s - 1) / 2) = (1 - s) / 2 := by ring
    rw [hneg] at h1
    have h2 := mellin_cpow_smul (fun t => f_fut (1 / t)) (s / 2) (-(1 / 2 : ℂ))
    have hexp : s / 2 + -(1 / 2 : ℂ) = (s - 1) / 2 := by ring
    rw [hexp, h1] at h2
    rw [← h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := mem_Ioi.mp ht
    simp only [smul_eq_mul]
    by_cases ht1 : t < 1
    · have hinv : 1 < 1 / t := (one_lt_div ht0).mpr ht1
      have hfe := P.hf_modif_FE (1 / t) (one_div_pos.mpr ht0)
      have h11 : 1 / (1 / t) = t := one_div_one_div t
      rw [h11] at hfe
      have hp_eq : f_past t = P.f_modif t := by
        rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr ht1.le), zero_add]
      have hf_eq : f_fut (1 / t) = P.f_modif (1 / t) := by
        rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioo_of_ge hinv.le), add_zero]
      have hsymm : P.symm = P := HurwitzZeta.hurwitzEvenFEPair_zero_symm
      have hg_eq : P.g_modif (1 / t) = P.f_modif (1 / t) := by
        change P.symm.f_modif (1 / t) = P.f_modif (1 / t)
        rw [hsymm]
      rw [hp_eq, hfe, hg_eq, ← hf_eq]
      have hPε : P.ε = 1 := rfl
      have hPk : P.k = 1 / 2 := rfl
      rw [hPε, hPk, one_mul, smul_eq_mul]
      have hpow : (((1 / t) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
        rw [one_div, Real.inv_rpow (le_of_lt ht0), ← Real.rpow_neg (le_of_lt ht0),
            Complex.ofReal_cpow (le_of_lt ht0)]
        push_cast; rfl
      rw [hpow]
    · have hnot_oo : t ∉ Ioo (0 : ℝ) 1 := fun h => ht1 h.2
      have hnot_oi : 1 / t ∉ Ioi (1 : ℝ) := by
        simp only [mem_Ioi, not_lt]
        exact (div_le_one ht0).mpr (not_lt.mp ht1)
      dsimp only [f_past, f_fut]
      rw [indicator_of_notMem hnot_oo, indicator_of_notMem hnot_oi, mul_zero, mul_zero, mul_zero]
  -- Combine future and past integrals over Ioi 1
  have hfut_ind : ∀ z : ℂ, EqOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * f_fut t)
      ((Ioi (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * ((2 * jacobiPsi t : ℝ) : ℂ))) (Ioi (0 : ℝ)) := by
    intro z t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    by_cases h1 : 1 < t
    · have hmem : t ∈ Ioi (1 : ℝ) := mem_Ioi.mpr h1
      simp only [f_fut, indicator_of_mem hmem]
      congr 1
      have hPf : P.f t = ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) := rfl
      have hPf0 : P.f₀ = 1 := by simp [P, HurwitzZeta.hurwitzEvenFEPair]
      rw [hPf, hPf0, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          two_mul_jacobiPsi_eq_evenKernel_sub_one ht0]
    · have hnot : t ∉ Ioi (1 : ℝ) := mem_Ioi.not.mpr h1
      simp only [f_fut, indicator_of_notMem hnot, mul_zero]
  have hfut_int : ∀ z : ℂ, mellin f_fut z =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * ((2 * jacobiPsi t : ℝ) : ℂ) := by
    intro z
    dsimp [mellin]
    rw [setIntegral_congr_fun measurableSet_Ioi (hfut_ind z),
        setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hint_t1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * ((2 * jacobiPsi t : ℝ) : ℂ)) (Ioi 1) := by
    have h0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) * f_fut t) (Ioi (0 : ℝ)) := hconv_fut (s / 2)
    have h := h0.congr_fun (hfut_ind (s / 2)) measurableSet_Ioi
    rw [integrableOn_indicator_iff (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ))).nullMeasurableSet,
        inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)] at h
    exact h
  have hint_t2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 - s) / 2 - 1) * ((2 * jacobiPsi t : ℝ) : ℂ)) (Ioi 1) := by
    have h0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 - s) / 2 - 1) * f_fut t) (Ioi (0 : ℝ)) :=
      hconv_fut ((1 - s) / 2)
    have h := h0.congr_fun (hfut_ind ((1 - s) / 2)) measurableSet_Ioi
    rw [integrableOn_indicator_iff (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ))).nullMeasurableSet,
        inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)] at h
    exact h
  rw [hsplit_mellin, hmellin_past, hfut_int (s / 2), hfut_int ((1 - s) / 2),
      ← integral_add hint_t1 hint_t2]
  -- Change of variable t = Real.exp (2 * u) mapping Ioi 0 onto Ioi 1
  let φ : ℝ → ℝ := fun u => Real.exp (2 * u)
  have himg : φ '' Ioi 0 = Ioi 1 := by
    ext t
    simp only [mem_image, mem_Ioi, φ]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.one_lt_exp_iff.mpr (by linarith)
    · intro ht
      refine ⟨Real.log t / 2, by have := Real.log_pos ht; linarith, ?_⟩
      rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (by linarith)]
  have hφ_deriv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (2 * Real.exp (2 * u)) (Ioi 0) u := by
    intro u _
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by simpa using (hasDerivAt_id u).const_mul 2
    have h := hlin.exp
    simpa [φ, mul_comm] using h.hasDerivWithinAt
  have hφ_inj : InjOn φ (Ioi 0) := by
    intro u _ v _ huv
    have h := Real.exp_injective huv
    linarith
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ_deriv hφ_inj]
  -- Simplify integrand to 8 * thetaHalf u * cosh(u * (s - 1/2)) and divide by 2
  have h_integrand : EqOn (fun u : ℝ =>
      |2 * Real.exp (2 * u)| •
        ((φ u : ℂ) ^ (s / 2 - 1) * ((2 * jacobiPsi (φ u) : ℝ) : ℂ) +
         (φ u : ℂ) ^ ((1 - s) / 2 - 1) * ((2 * jacobiPsi (φ u) : ℝ) : ℂ)))
      (fun u : ℝ => (8 : ℂ) * (((thetaHalf u : ℝ) : ℂ) *
        Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ)))) (Ioi 0) := by
    intro u _
    dsimp only
    rw [abs_of_pos (by positivity), Complex.real_smul]
    dsimp [φ, thetaHalf]
    have hcp1 : ((Real.exp (2 * u) : ℝ) : ℂ) ^ (s / 2 - 1) =
        Complex.exp (((2 * u : ℝ) : ℂ) * (s / 2 - 1)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))),
          ← Complex.ofReal_log (le_of_lt (Real.exp_pos _)), Real.log_exp]
    have hcp2 : ((Real.exp (2 * u) : ℝ) : ℂ) ^ ((1 - s) / 2 - 1) =
        Complex.exp (((2 * u : ℝ) : ℂ) * ((1 - s) / 2 - 1)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))),
          ← Complex.ofReal_log (le_of_lt (Real.exp_pos _)), Real.log_exp]
    rw [hcp1, hcp2, Complex.cosh]
    have hs_sub : (⟨beta - 1 / 2, gamma⟩ : ℂ) = s - 1 / 2 := by
      apply Complex.ext <;> simp [s]
    rw [hs_sub]
    have hmul1 : Complex.exp (2 * (u : ℂ)) * Complex.exp (2 * (u : ℂ) * (s / 2 - 1)) =
        Complex.exp ((u : ℂ) / 2) * Complex.exp ((u : ℂ) * (s - 1 / 2)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have hmul2 : Complex.exp (2 * (u : ℂ)) * Complex.exp (2 * (u : ℂ) * ((1 - s) / 2 - 1)) =
        Complex.exp ((u : ℂ) / 2) * Complex.exp (-((u : ℂ) * (s - 1 / 2))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    push_cast
    linear_combination
      4 * (jacobiPsi (Real.exp (2 * u)) : ℂ) * hmul1 +
      4 * (jacobiPsi (Real.exp (2 * u)) : ℂ) * hmul2
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand, integral_const_mul]
  ring

/-- THEOREM III.4 (Real/Imaginary Past-Future Hyperbolic Split of `completedRiemannZeta₀`):
    Re(Lambda_0(beta + i*gamma)) carries cosh((beta-1/2)u) cos(gamma u),
    Im(Lambda_0(beta + i*gamma)) carries sinh((beta-1/2)u) sin(gamma u). -/
lemma complex_cosh_re_im (u sigma gamma : ℝ) :
    (Complex.cosh ((u : ℂ) * (⟨sigma, gamma⟩ : ℂ))).re = Real.cosh (sigma * u) * Real.cos (gamma * u) ∧
    (Complex.cosh ((u : ℂ) * (⟨sigma, gamma⟩ : ℂ))).im = Real.sinh (sigma * u) * Real.sin (gamma * u) := by
  have hmul : (u : ℂ) * (⟨sigma, gamma⟩ : ℂ) = ((sigma * u : ℝ) : ℂ) + ((gamma * u : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp; ring
    · simp; ring
  rw [hmul, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

theorem completedRiemannZeta₀_re_im_pastFuture (beta gamma : ℝ) :
    (completedRiemannZeta₀ (⟨beta, gamma⟩ : ℂ)).re =
      4 * ∫ u in Ioi (0 : ℝ), thetaHalf u * Real.cosh ((beta - 1 / 2) * u) * Real.cos (gamma * u) ∧
    (completedRiemannZeta₀ (⟨beta, gamma⟩ : ℂ)).im =
      4 * ∫ u in Ioi (0 : ℝ), thetaHalf u * Real.sinh ((beta - 1 / 2) * u) * Real.sin (gamma * u) := by
  have hint : IntegrableOn (fun u : ℝ => ((thetaHalf u : ℝ) : ℂ) *
      Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))) (Ioi 0) := by
    have hc : Continuous thetaHalf := continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaHalf u).continuousAt
    have hcont : Continuous (fun u : ℝ => ((thetaHalf u : ℝ) : ℂ) *
        Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))) :=
      (Complex.continuous_ofReal.comp hc).mul (by fun_prop)
    refine ((integrableOn_superexp (1 / 2 + |beta - 1 / 2|) Real.pi_pos).const_mul
      (1 / (1 - Real.exp (-Real.pi)))).mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real]
    have h1 := norm_thetaHalf_superexp (le_of_lt hu)
    have h2 := norm_complex_cosh_le u (le_of_lt hu) ⟨beta - 1 / 2, gamma⟩
    simp only at h2
    calc ‖thetaHalf u‖ * ‖Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))‖
      _ ≤ ((1 / (1 - Real.exp (-Real.pi))) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) *
            Real.exp (|beta - 1 / 2| * u) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by
            have : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
            have : 0 < 1 - Real.exp (-Real.pi) := by linarith
            positivity)
      _ = (1 / (1 - Real.exp (-Real.pi))) *
            Real.exp ((1 / 2 + |beta - 1 / 2|) * u - Real.pi * Real.exp (2 * u)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [completedRiemannZeta₀_eq_past_future_integral]
  have hre : (4 * ∫ u in Ioi (0 : ℝ), ((thetaHalf u : ℝ) : ℂ) *
      Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))).re =
      4 * ∫ u in Ioi (0 : ℝ), (((thetaHalf u : ℝ) : ℂ) *
        Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))).re := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    congr 1
    simpa [Complex.reCLM_apply] using (Complex.reCLM.integral_comp_comm hint).symm
  have him : (4 * ∫ u in Ioi (0 : ℝ), ((thetaHalf u : ℝ) : ℂ) *
      Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))).im =
      4 * ∫ u in Ioi (0 : ℝ), (((thetaHalf u : ℝ) : ℂ) *
        Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ))).im := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
    congr 1
    simpa [Complex.imCLM_apply] using (Complex.imCLM.integral_comp_comm hint).symm
  constructor
  · rw [hre]; congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [Complex.re_ofReal_mul, (complex_cosh_re_im u (beta - 1 / 2) gamma).1]
    ring
  · rw [him]; congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [Complex.im_ofReal_mul, (complex_cosh_re_im u (beta - 1 / 2) gamma).2]
    ring

/-- The entire Riemann Xi function: xi(s) = (1/2) * s * (s - 1) * Lambda(s)
    = (1/2) * (s * (s - 1) * completedRiemannZeta₀(s) + 1). -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem riemannXi_entire : Differentiable ℂ riemannXi := by
  have h1 : Differentiable ℂ (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) :=
    ((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).mul
      differentiable_completedZeta₀).add (differentiable_const 1)
  exact h1.const_mul (1 / 2 : ℂ)

theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  dsimp [riemannXi]
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem riemannXi_eq_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  dsimp [riemannXi]
  rw [completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

theorem riemannXi_eq_zero_iff_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; linarith
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  simp [hs0, hs1', hG]

lemma continuous_riemannPhi : Continuous riemannPhi := by
  have hfun : riemannPhi = fun u => thetaHalfDeriv2 u - (1 / 4 : ℝ) * thetaHalf u :=
    funext riemannPhi_eq_deriv2_sub_quarter
  rw [hfun]
  have hc1 : Continuous thetaHalf := continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaHalf u).continuousAt
  have hc2 : Continuous thetaHalfDeriv2 := by
    rw [continuous_iff_continuousAt]
    intro u
    let a := u - 1
    let R := u + 1
    have hu : u ∈ Ioo a R := ⟨by dsimp [a]; linarith, by dsimp [R]; linarith⟩
    have hmaj := (summable_pow_mul_exp_neg_sq 4 (c := Real.pi * Real.exp (2 * a)) (by positivity)).mul_left
      ((1 / 4 + 6 * Real.pi * Real.exp (2 * R) + 4 * Real.pi ^ 2 * Real.exp (4 * R)) * Real.exp (R / 2))
    have hcon : ContinuousOn thetaHalfDeriv2 (Ioo a R) :=
      continuousOn_tsum (fun n => (show Continuous (thetaHalfTermDeriv2 n) by
        unfold thetaHalfTermDeriv2 thetaHalfTerm; fun_prop).continuousOn)
        hmaj (fun n x hx => norm_thetaHalfTermDeriv2_le_on_Ioo n hx)
    exact hcon.continuousAt (isOpen_Ioo.mem_nhds hu)
  exact hc2.sub (hc1.const_mul (1 / 4))

/-- THEOREM III.5 (Riemann's Exact Past-Future Integral Representation of `riemannXi`):
    Integrating by parts twice on (0, inf) and using F'(0) = -1/4 cancels the
    pole term +1 identically and yields Riemann's exact formula:
      riemannXi(beta + i*gamma)
        = 2 * integral_{0}^{inf} Phi(u) * cosh(u * ((beta - 1/2) + i*gamma)) du. -/
theorem riemannXi_eq_pastFuture_phi_integral (beta gamma : ℝ) :
    riemannXi (⟨beta, gamma⟩ : ℂ) =
      2 * ∫ u in Ioi (0 : ℝ),
        ((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * (⟨beta - 1 / 2, gamma⟩ : ℂ)) := by
  let s : ℂ := ⟨beta, gamma⟩
  let w : ℂ := ⟨beta - 1 / 2, gamma⟩
  have hsw : s * (s - 1) = w ^ 2 - 1 / 4 := by
    have hws : w = s - 1 / 2 := by apply Complex.ext <;> simp [w, s]
    rw [hws]; ring
  -- Define boundary primitive B(u) = F(u) * w * sinh(u * w) - F'(u) * cosh(u * w)
  let B : ℝ → ℂ := fun u =>
    ((thetaHalf u : ℝ) : ℂ) * (w * Complex.sinh ((u : ℂ) * w)) -
    ((thetaHalfDeriv u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)
  let B' : ℝ → ℂ := fun u =>
    ((thetaHalf u : ℝ) : ℂ) * (w ^ 2 * Complex.cosh ((u : ℂ) * w)) -
    ((thetaHalfDeriv2 u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)
  have hB_deriv : ∀ u : ℝ, HasDerivAt B (B' u) u := by
    intro u
    have hF : HasDerivAt (fun x : ℝ => ((thetaHalf x : ℝ) : ℂ)) ((thetaHalfDeriv u : ℝ) : ℂ) u :=
      (hasDerivAt_thetaHalf u).ofReal_comp
    have hF' : HasDerivAt (fun x : ℝ => ((thetaHalfDeriv x : ℝ) : ℂ)) ((thetaHalfDeriv2 u : ℝ) : ℂ) u :=
      (hasDerivAt_thetaHalfDeriv u).ofReal_comp
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) * w) w u := by
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) u := (hasDerivAt_id u).ofReal_comp
      simpa using h1.mul_const w
    have hsinh : HasDerivAt (fun x : ℝ => Complex.sinh ((x : ℂ) * w)) (Complex.cosh ((u : ℂ) * w) * w) u :=
      (Complex.hasDerivAt_sinh _).comp u hlin
    have hcosh : HasDerivAt (fun x : ℝ => Complex.cosh ((x : ℂ) * w)) (Complex.sinh ((u : ℂ) * w) * w) u :=
      (Complex.hasDerivAt_cosh _).comp u hlin
    have ht1 := hF.mul (hsinh.const_mul w)
    have ht2 := hF'.mul hcosh
    convert ht1.sub ht2 using 1
    dsimp [B']
    ring
  -- B(0) = 1/4 since sinh(0) = 0, cosh(0) = 1, and thetaHalfDeriv 0 = -1/4!
  have hB0 : B 0 = 1 / 4 := by
    dsimp [B]
    rw [thetaHalfDeriv_zero]
    simp
  -- B(u) -> 0 as u -> +inf by super-exponential decay
  have hB_top : Tendsto B atTop (𝓝 0) := by
    obtain ⟨C1, hC1_pos, hD1⟩ := norm_thetaHalfDeriv_superexp
    have ht1 : Tendsto (fun u : ℝ => ((thetaHalf u : ℝ) : ℂ) * (w * Complex.sinh ((u : ℂ) * w)))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hlim1 : Tendsto (fun u : ℝ => ‖w‖ * (1 / (1 - Real.exp (-Real.pi))) *
          Real.exp ((1 / 2 + |w.re|) * u - Real.pi * Real.exp (2 * u))) atTop (𝓝 0) := by
        simpa using (tendsto_superexp_zero (1 / 2 + |w.re|) Real.pi_pos).const_mul
          (‖w‖ * (1 / (1 - Real.exp (-Real.pi))))
      refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hlim1
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      rw [norm_mul, norm_mul, Complex.norm_real]
      have hF := norm_thetaHalf_superexp hu
      have hs := norm_complex_sinh_le u hu w
      have hpos : 0 ≤ 1 / (1 - Real.exp (-Real.pi)) := by
        have : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
        have : 0 < 1 - Real.exp (-Real.pi) := by linarith
        positivity
      calc ‖thetaHalf u‖ * (‖w‖ * ‖Complex.sinh ((u : ℂ) * w)‖)
        _ ≤ ((1 / (1 - Real.exp (-Real.pi))) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) *
              (‖w‖ * Real.exp (|w.re| * u)) :=
            mul_le_mul hF (mul_le_mul_of_nonneg_left hs (norm_nonneg w)) (by positivity) (by positivity)
        _ = ‖w‖ * (1 / (1 - Real.exp (-Real.pi))) *
              (Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) * Real.exp (|w.re| * u)) := by ring
        _ = ‖w‖ * (1 / (1 - Real.exp (-Real.pi))) *
              Real.exp ((1 / 2 + |w.re|) * u - Real.pi * Real.exp (2 * u)) := by
            rw [← Real.exp_add]; congr 2; ring
    have ht2 : Tendsto (fun u : ℝ => ((thetaHalfDeriv u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hlim0 : Tendsto (fun u : ℝ => C1 * Real.exp ((5 / 2 + |w.re|) * u - (Real.pi / 2) * Real.exp (2 * u)))
          atTop (𝓝 0) := by
        simpa using (tendsto_superexp_zero (5 / 2 + |w.re|) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul C1
      refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hlim0
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      rw [norm_mul, Complex.norm_real]
      have hF' := hD1 u hu
      have hc := norm_complex_cosh_le u hu w
      calc ‖thetaHalfDeriv u‖ * ‖Complex.cosh ((u : ℂ) * w)‖
        _ ≤ (C1 * Real.exp (5 * u / 2 - (Real.pi / 2) * Real.exp (2 * u))) * Real.exp (|w.re| * u) :=
            mul_le_mul hF' hc (norm_nonneg _) (by positivity)
        _ = C1 * Real.exp ((5 / 2 + |w.re|) * u - (Real.pi / 2) * Real.exp (2 * u)) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    simpa [B] using ht1.sub ht2
  -- Integrability of the two components of B'
  have hint_F : IntegrableOn (fun u : ℝ => ((thetaHalf u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)) (Ioi 0) := by
    have hc : Continuous thetaHalf := continuous_iff_continuousAt.mpr fun u => (hasDerivAt_thetaHalf u).continuousAt
    refine ((integrableOn_superexp (1 / 2 + |w.re|) Real.pi_pos).const_mul
      (1 / (1 - Real.exp (-Real.pi)))).mono' ((Complex.continuous_ofReal.comp hc).mul (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real]
    have hpos : 0 ≤ 1 / (1 - Real.exp (-Real.pi)) := by
      have : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
      have : 0 < 1 - Real.exp (-Real.pi) := by linarith
      positivity
    calc ‖thetaHalf u‖ * ‖Complex.cosh ((u : ℂ) * w)‖
      _ ≤ ((1 / (1 - Real.exp (-Real.pi))) * Real.exp (u / 2 - Real.pi * Real.exp (2 * u))) *
            Real.exp (|w.re| * u) :=
          mul_le_mul (norm_thetaHalf_superexp (le_of_lt hu)) (norm_complex_cosh_le u (le_of_lt hu) w)
            (norm_nonneg _) (by positivity)
      _ = (1 / (1 - Real.exp (-Real.pi))) * Real.exp ((1 / 2 + |w.re|) * u - Real.pi * Real.exp (2 * u)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hint_Phi : IntegrableOn (fun u : ℝ => ((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)) (Ioi 0) := by
    obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
    refine ((integrableOn_superexp (9 / 2 + |w.re|) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul C2).mono'
      ((Complex.continuous_ofReal.comp continuous_riemannPhi).mul (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real]
    calc ‖riemannPhi u‖ * ‖Complex.cosh ((u : ℂ) * w)‖
      _ ≤ (C2 * Real.exp (9 * u / 2 - (Real.pi / 2) * Real.exp (2 * u))) * Real.exp (|w.re| * u) :=
          mul_le_mul (hPhi_le u (le_of_lt hu)) (norm_complex_cosh_le u (le_of_lt hu) w)
            (norm_nonneg _) (by positivity)
      _ = C2 * Real.exp ((9 / 2 + |w.re|) * u - (Real.pi / 2) * Real.exp (2 * u)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  -- Rewrite B'(u) = (w^2 - 1/4) * F(u) * cosh(uw) - Phi(u) * cosh(uw)
  have hB'_eq : B' = fun u => (w ^ 2 - 1 / 4) * (((thetaHalf u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)) -
      ((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w) := by
    ext u
    dsimp [B']
    rw [riemannPhi_eq_deriv2_sub_quarter u]
    push_cast
    ring
  have hint_B' : IntegrableOn B' (Ioi 0) := by
    rw [hB'_eq]
    exact (hint_F.const_mul (w ^ 2 - 1 / 4)).sub hint_Phi
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hB_deriv u) hint_B' hB_top
  rw [hB0, zero_sub, hB'_eq, integral_sub (hint_F.const_mul _) hint_Phi, integral_const_mul] at hFTC
  -- hFTC says: (w^2 - 1/4) * I_F - I_Phi = -1/4
  -- Therefore (w^2 - 1/4) * (4 * I_F) + 1 = 4 * I_Phi, so xi(s) = (1/2) * (4 * I_Phi) = 2 * I_Phi!
  dsimp [riemannXi]
  rw [show (⟨beta, gamma⟩ : ℂ) = s from rfl, hsw, completedRiemannZeta₀_eq_past_future_integral beta gamma]
  linear_combination 2 * hFTC

/-- THEOREM III.6 (Exact Past-Future Coupled System for Zeros of `riemannZeta`):
    For any s = beta + i*gamma in the critical strip 0 < beta < 1,
    riemannZeta(beta + i*gamma) = 0 holds if and only if BOTH the even cosh-cos
    integral AND the odd sinh-sin integral against Riemann's positive kernel
    Phi(u) > 0 vanish simultaneously! -/
theorem riemannXi_re_im_pastFuture_phi (beta gamma : ℝ) :
    (riemannXi (⟨beta, gamma⟩ : ℂ)).re =
      2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cosh ((beta - 1 / 2) * u) * Real.cos (gamma * u) ∧
    (riemannXi (⟨beta, gamma⟩ : ℂ)).im =
      2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.sinh ((beta - 1 / 2) * u) * Real.sin (gamma * u) := by
  let w : ℂ := ⟨beta - 1 / 2, gamma⟩
  have hint_Phi : IntegrableOn (fun u : ℝ => ((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)) (Ioi 0) := by
    obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
    refine ((integrableOn_superexp (9 / 2 + |w.re|) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul C2).mono'
      ((Complex.continuous_ofReal.comp continuous_riemannPhi).mul (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real]
    calc ‖riemannPhi u‖ * ‖Complex.cosh ((u : ℂ) * w)‖
      _ ≤ (C2 * Real.exp (9 * u / 2 - (Real.pi / 2) * Real.exp (2 * u))) * Real.exp (|w.re| * u) :=
          mul_le_mul (hPhi_le u (le_of_lt hu)) (norm_complex_cosh_le u (le_of_lt hu) w)
            (norm_nonneg _) (by positivity)
      _ = C2 * Real.exp ((9 / 2 + |w.re|) * u - (Real.pi / 2) * Real.exp (2 * u)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [riemannXi_eq_pastFuture_phi_integral beta gamma]
  have hre_comm : (∫ u in Ioi (0 : ℝ), ((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)).re =
      ∫ u in Ioi (0 : ℝ), (((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)).re := by
    have h := (Complex.reCLM.integral_comp_comm hint_Phi).symm
    simpa only [Complex.reCLM_apply] using h
  have him_comm : (∫ u in Ioi (0 : ℝ), ((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)).im =
      ∫ u in Ioi (0 : ℝ), (((riemannPhi u : ℝ) : ℂ) * Complex.cosh ((u : ℂ) * w)).im := by
    have h := (Complex.imCLM.integral_comp_comm hint_Phi).symm
    simpa only [Complex.imCLM_apply] using h
  constructor
  · rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    congr 1
    rw [show (⟨beta - 1 / 2, gamma⟩ : ℂ) = w from rfl, hre_comm]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [Complex.re_ofReal_mul, (complex_cosh_re_im u (beta - 1 / 2) gamma).1]
    ring
  · rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
    congr 1
    rw [show (⟨beta - 1 / 2, gamma⟩ : ℂ) = w from rfl, him_comm]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [Complex.im_ofReal_mul, (complex_cosh_re_im u (beta - 1 / 2) gamma).2]
    ring

theorem riemannZeta_zero_iff_pastFuture_coupled_integrals {beta gamma : ℝ}
    (h0 : 0 < beta) (h1 : beta < 1) :
    riemannZeta (⟨beta, gamma⟩ : ℂ) = 0 ↔
      (∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cosh ((beta - 1 / 2) * u) * Real.cos (gamma * u) = 0 ∧
       ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.sinh ((beta - 1 / 2) * u) * Real.sin (gamma * u) = 0) := by
  rw [← riemannXi_eq_zero_iff_riemannZeta (s := ⟨beta, gamma⟩) (by simpa using h0) (by simpa using h1),
      Complex.ext_iff, Complex.zero_re, Complex.zero_im,
      (riemannXi_re_im_pastFuture_phi beta gamma).1,
      (riemannXi_re_im_pastFuture_phi beta gamma).2]
  constructor
  · rintro ⟨hre, him⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hre, him⟩
    exact ⟨by linarith, by linarith⟩

/-- COROLLARY III.6b (Exact Reality of riemannXi on the Critical Line Re(s) = 1/2):
    Because sinh(0) = 0, the odd past-future integral vanishes identically on beta = 1/2,
    so riemannXi(1/2 + i*gamma) is purely real for every gamma : R. -/
theorem riemannXi_im_half_eq_zero (gamma : ℝ) :
    (riemannXi (⟨1 / 2, gamma⟩ : ℂ)).im = 0 := by
  rw [(riemannXi_re_im_pastFuture_phi (1 / 2) gamma).2]
  simp [sub_self]

-- ==============================================================================
-- PART IV: POLYA-JENSEN MOMENTS (ROUTE B) & HERMITIAN GRAM POSITIVITY (ROUTE A)
-- ==============================================================================

/-- The k-th Polya-Jensen moment of Riemann's past-future kernel Phi(u):
    b_k = integral_{0}^{inf} Phi(u) * u^{2k} du. -/
noncomputable def polyaMoment (k : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), riemannPhi u * u ^ (2 * k)

lemma integrableOn_polyaMoment (k : ℕ) :
    IntegrableOn (fun u : ℝ => riemannPhi u * u ^ (2 * k)) (Ioi 0) := by
  obtain ⟨C2, hC2_pos, hPhi_le⟩ := norm_riemannPhi_superexp
  refine ((integrableOn_superexp (9 / 2 + 1) (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul
    (C2 * ((2 * k).factorial : ℝ))).mono'
    ((continuous_riemannPhi.mul (continuous_pow (2 * k))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (le_of_lt hu) _)]
  have hpow := pow_le_factorial_mul_exp (2 * k) (le_of_lt hu)
  calc ‖riemannPhi u‖ * u ^ (2 * k)
    _ ≤ (C2 * Real.exp (9 * u / 2 - (Real.pi / 2) * Real.exp (2 * u))) *
          (((2 * k).factorial : ℝ) * Real.exp u) :=
        mul_le_mul (hPhi_le u (le_of_lt hu)) hpow (pow_nonneg (le_of_lt hu) _) (by positivity)
    _ = C2 * ((2 * k).factorial : ℝ) *
          (Real.exp (9 * u / 2 - (Real.pi / 2) * Real.exp (2 * u)) * Real.exp u) := by ring
    _ = C2 * ((2 * k).factorial : ℝ) *
          Real.exp ((9 / 2 + 1) * u - (Real.pi / 2) * Real.exp (2 * u)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- THEOREM IV.1 (Strict Positivity of All Polya-Jensen Moments b_k > 0):
    Every even moment b_k = int_0^inf Phi(u) u^{2k} du is strictly positive. -/
theorem polyaMoment_pos (k : ℕ) : 0 < polyaMoment k := by
  dsimp [polyaMoment]
  have hf_cont : ContinuousOn (fun u : ℝ => riemannPhi u * u ^ (2 * k)) (Ioi 0) :=
    (continuous_riemannPhi.mul (continuous_pow (2 * k))).continuousOn
  have hf_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ riemannPhi u * u ^ (2 * k) := fun u hu =>
    mul_nonneg (le_of_lt (riemannPhi_pos_of_nonneg (le_of_lt hu))) (pow_nonneg (le_of_lt hu) _)
  have h1_pos : 0 < riemannPhi 1 * (1 : ℝ) ^ (2 * k) := by
    simpa using riemannPhi_pos_of_nonneg zero_le_one
  exact setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.eventually_of_mem (ae_restrict_mem measurableSet_Ioi) hf_nonneg)
    (integrableOn_polyaMoment k) |>.mpr <| by
      have hopen : IsOpen ({u : ℝ | 0 < riemannPhi u * u ^ (2 * k)} ∩ Ioi 0) :=
        (isOpen_lt continuous_const (continuous_riemannPhi.mul (continuous_pow (2 * k)))).inter isOpen_Ioi
      have hmem : (1 : ℝ) ∈ {u : ℝ | 0 < riemannPhi u * u ^ (2 * k)} ∩ Ioi 0 :=
        ⟨h1_pos, mem_Ioi.mpr zero_lt_one⟩
      have hsub : {u : ℝ | 0 < riemannPhi u * u ^ (2 * k)} ∩ Ioi 0 ⊆
          Function.support (fun u : ℝ => riemannPhi u * u ^ (2 * k)) ∩ Ioi 0 :=
        fun u hu => ⟨ne_of_gt hu.1, hu.2⟩
      exact lt_of_lt_of_le (hopen.measure_pos volume ⟨1, hmem⟩) (measure_mono hsub)

/-- THEOREM IV.2 (Unconditional Turan / Degree-2 Jensen Hyperbolicity for All k : N):
    For EVERY shift k : N, the Polya-Jensen moments of Riemann's kernel Phi(u) satisfy
      b_{k+1}^2 <= b_k * b_{k+2}
    (log-convexity of the moment sequence, anchoring Route B). -/
theorem polyaMoment_turan_logconvex (k : ℕ) :
    (polyaMoment (k + 1)) ^ 2 ≤ polyaMoment k * polyaMoment (k + 2) := by
  have hquad : ∀ x : ℝ, 0 ≤ polyaMoment k + 2 * x * polyaMoment (k + 1) + x ^ 2 * polyaMoment (k + 2) := by
    intro x
    have h0 := integrableOn_polyaMoment k
    have h1 := (integrableOn_polyaMoment (k + 1)).const_mul (2 * x)
    have h2 := (integrableOn_polyaMoment (k + 2)).const_mul (x ^ 2)
    have h01 : IntegrableOn (fun u : ℝ => riemannPhi u * u ^ (2 * k) +
        2 * x * (riemannPhi u * u ^ (2 * (k + 1)))) (Ioi 0) := h0.add h1
    have heq : polyaMoment k + 2 * x * polyaMoment (k + 1) + x ^ 2 * polyaMoment (k + 2) =
        ∫ u in Ioi (0 : ℝ), riemannPhi u * (u ^ k + x * u ^ (k + 2)) ^ 2 := by
      dsimp [polyaMoment]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add h0 h1,
          ← integral_add h01 h2]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      have hp1 : u ^ (2 * (k + 1)) = u ^ k * u ^ (k + 2) := by rw [← pow_add]; congr 1; omega
      have hp2 : u ^ (2 * (k + 2)) = (u ^ (k + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
      have hp0 : u ^ (2 * k) = (u ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
      rw [hp0, hp1, hp2]
      ring
    rw [heq]
    exact setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (le_of_lt (riemannPhi_pos_of_nonneg (le_of_lt hu))) (sq_nonneg _)
  have hb2_pos : 0 < polyaMoment (k + 2) := polyaMoment_pos (k + 2)
  have hspec := hquad (-(polyaMoment (k + 1) / polyaMoment (k + 2)))
  have hsimp : polyaMoment k + 2 * (-(polyaMoment (k + 1) / polyaMoment (k + 2))) * polyaMoment (k + 1) +
      (-(polyaMoment (k + 1) / polyaMoment (k + 2))) ^ 2 * polyaMoment (k + 2) =
      (polyaMoment k * polyaMoment (k + 2) - (polyaMoment (k + 1)) ^ 2) / polyaMoment (k + 2) := by
    field_simp [ne_of_gt hb2_pos]
    ring
  rw [hsimp, div_nonneg_iff] at hspec
  rcases hspec with ⟨hnum, _⟩ | ⟨_, hden⟩
  · linarith
  · linarith

/-- THEOREM IV.2b (General Order-N Stieltjes-Hamburger Hankel Positivity of Polya-Jensen Moments):
    For EVERY order N : N and EVERY real coefficient vector c : Fin N -> R, the N x N
    Hankel quadratic form H_{ij} = polyaMoment (i + j) is non-negative:
      sum_{i, j} c_i * c_j * b_{i+j} = int_0^inf Phi(u) * (sum_i c_i u^{2i})^2 du >= 0. -/
theorem polyaMoment_hankel_psd (N : ℕ) (c : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, c i * c j * polyaMoment (i.1 + j.1) := by
  have hint_pair : ∀ i j : Fin N,
      IntegrableOn (fun u : ℝ => c i * c j * (riemannPhi u * u ^ (2 * (i.1 + j.1)))) (Ioi 0) :=
    fun i j => (integrableOn_polyaMoment (i.1 + j.1)).const_mul (c i * c j)
  have heq : ∑ i : Fin N, ∑ j : Fin N, c i * c j * polyaMoment (i.1 + j.1) =
      ∫ u in Ioi (0 : ℝ), riemannPhi u * (∑ i : Fin N, c i * u ^ (2 * i.1)) ^ 2 := by
    have h1 : ∑ i : Fin N, ∑ j : Fin N, c i * c j * polyaMoment (i.1 + j.1) =
        ∑ i : Fin N, ∑ j : Fin N, ∫ u in Ioi (0 : ℝ), c i * c j * (riemannPhi u * u ^ (2 * (i.1 + j.1))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      dsimp [polyaMoment]
      rw [integral_const_mul]
    rw [h1]
    have h2 : ∀ i : Fin N,
        ∑ j : Fin N, ∫ u in Ioi (0 : ℝ), c i * c j * (riemannPhi u * u ^ (2 * (i.1 + j.1))) =
        ∫ u in Ioi (0 : ℝ), ∑ j : Fin N, c i * c j * (riemannPhi u * u ^ (2 * (i.1 + j.1))) :=
      fun i => (integral_finsetSum Finset.univ (fun j _ => hint_pair i j)).symm
    simp_rw [h2]
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hint_pair i j))]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * (i.1 + j.1) = 2 * i.1 + 2 * j.1 by omega, pow_add]
    ring
  rw [heq]
  exact setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (le_of_lt (riemannPhi_pos u)) (sq_nonneg _)

/-- THEOREM IV.3 (Positive Semi-Definiteness of Finite-Place Hermitian Gram Forms — Route A):
    For any finite basis of complex feature vectors v : iota -> Fin M -> C and any
    coefficient vector c : iota -> C, the Hermitian Gram quadratic form
      sum_{i, j} conj(c_i) * c_j * sum_m conj(v_i m) * v_j m
    is purely real and non-negative (equals sum_m ||sum_i c_i * v_i m||^2 >= 0). -/
theorem finite_gram_form_nonneg {ι : Type*} (S : Finset ι) {M : ℕ}
    (v : ι → Fin M → ℂ) (c : ι → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * (∑ m : Fin M, conj (v i m) * v j m)).re := by
  have heq : ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * (∑ m : Fin M, conj (v i m) * v j m) =
      ∑ m : Fin M, (((‖∑ i ∈ S, c i * v i m‖ ^ 2 : ℝ) : ℂ)) := by
    have hswap : ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * (∑ m : Fin M, conj (v i m) * v j m) =
        ∑ m : Fin M, (∑ i ∈ S, conj (c i * v i m)) * (∑ j ∈ S, c j * v j m) := by
      calc ∑ i ∈ S, ∑ j ∈ S, conj (c i) * c j * (∑ m : Fin M, conj (v i m) * v j m)
        _ = ∑ i ∈ S, ∑ j ∈ S, ∑ m : Fin M, conj (c i * v i m) * (c j * v j m) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [map_mul]; ring
        _ = ∑ i ∈ S, ∑ m : Fin M, ∑ j ∈ S, conj (c i * v i m) * (c j * v j m) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m : Fin M, ∑ i ∈ S, ∑ j ∈ S, conj (c i * v i m) * (c j * v j m) :=
            Finset.sum_comm
        _ = ∑ m : Fin M, (∑ i ∈ S, conj (c i * v i m)) * (∑ j ∈ S, c j * v j m) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
    rw [hswap]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← map_sum, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heq, Complex.re_sum]
  refine Finset.sum_nonneg fun m _ => ?_
  rw [Complex.ofReal_re]
  exact sq_nonneg _

end PastFutureXiKernel
