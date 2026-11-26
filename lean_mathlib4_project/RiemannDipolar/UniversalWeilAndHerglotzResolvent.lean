/-
  ==============================================================================
  ROUTE A UNIVERSAL FINITE-CODIMENSION COERCIVITY OF THE ARITHMETIC WEIL
  FUNCTIONAL, HERGLOTZ-PICK SPECTRAL RESOLVENT DUALITY, AND ROUTE B
  LOCAL RIEMANN HYPOTHESIS WITH ZERO SIMPLICITY & ANGULAR COMPACTIFICATION

  Title: Universal Weil Coercivity, Herglotz-Pick Resolvent, and Local RH
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 22, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Route A — Universal Finite-Codimension Coercivity for ALL L > 0):
      * `norm_exp_neg_I_sub_taylor_le`: Exact Taylor remainder `‖e^{-ix} - ∑_{m<N} (-ix)^m/m!‖ ≤ |x|^N/N!`.
      * `exists_pow_div_factorial_lt`: Elementary super-exponential factorial decay `a^N / N! → 0`.
      * `compactFourier_norm_sq_le_of_moment_orthog`: Uniform Fourier suppression on `[-T, T]`
        for continuous functions orthogonal to the first `N` monomials `{1, u, ..., u^{N-1}}`.
      * `weilPrime_refined_norm_bound`: Split prime-shift operator norm using the 1/2-factor
        disjoint-strip bound for `L/2 ≤ log n ≤ L` and Cauchy-Schwarz for `log n < L/2`.
      * `weilTotal_universal_finite_codim_coercive`: For EVERY `L > 0` (arbitrarily many
        active primes `p^m ≤ e^L`) and EVERY coercivity floor `c ∈ ℝ`, there exists `N : ℕ`
        such that `c * ‖g‖_2^2 ≤ weilTotal L g` for every continuous `g` orthogonal to
        `{1, u, ..., u^{N-1}}` on `[-L/2, L/2]` (essential spectrum = +∞, zero discretization).
      * `weilTotal_strict_pos_on_finite_codim`: Strict positivity of `weilTotal L g` on a
        finite-codimension subspace for EVERY `L > 0`.
  - Part II (Spectral Resolvent, Phase-Force Duality, Herglotz-Pick & Off-Line Detection):
      * `xiResolvent_im_eq_logForce_half`: `Im(R_ξ(γ + iσ)) = Re(ξ'/ξ(1/2 + σ + iγ)) = (1/2) * ∂_σ log V`.
      * `xiResolvent_im_eq_phase_deriv_gamma`: Exact Cauchy-Riemann phase-monotonicity law
        `Θ'(γ) = Im(R_ξ(γ + iσ))` for any C^1 polar representation `ξ = r e^{iΘ}`.
      * `riemannHypothesis_of_xiResolventHerglotz`: Herglotz positivity of `R_ξ` on the
        upper half-strip `0 < σ < 1/2` implies Mathlib4's official `RiemannHypothesis`.
      * `resolventCritSum_im_pos`, `resolventCritSum_schwarzPick_le`,
        `resolventCritSum_pickMatrix_psd`, `resolventCritSum_idos_integral`:
        Exact Herglotz positivity, Schwarz-Pick hyperbolic contraction `Im(z)‖G'(z)‖ ≤ Im(G(z))`,
        all-order Pick-Nevanlinna matrix PSD, and exact Stieltjes-Perron IDOS integral
        `(1/π) ∫ Im G(γ + iσ) dγ = ∑ w_m` for every finite family of critical-line poles.
      * `resolventOfflinePair_neg_inside` & `resolventOfflinePair_violates_schwarzPick_outside`:
        Any symmetric off-line zero pair `1/2 ± δ + iγ_0` (`δ > 0`) violates Herglotz
        positivity inside `0 < σ < δ` AND strictly violates Schwarz-Pick hyperbolic contraction
        `σ ‖G'(γ_0 + iσ)‖ / Im(G(γ_0 + iσ)) = (σ^2 + δ^2)/(σ^2 - δ^2) > 1` for EVERY `σ > δ`
        (remote detection even in the Euler-product half-plane `Re(s) > 1`).
  - Part III (Route B — All-Order Light-Cone Parity, Local RH + Simplicity, Angular Strip):
      * `lightCone_even_power_parity_identity`: Exact all-order (`2k ∈ 2ℕ`) cosh/sinh parity
        separation of `(u+v)^2(u-v)^{2k} cosh(σ(u+v)) + (u-v)^2(u+v)^{2k} cosh(σ(u-v))`.
      * `riemannHypothesis_local_and_simple_of_hessianPos`: For ANY height `Γ ≥ 0`,
        positivity of `∂_σ^2 V(σ, γ)` on `[0, 1/2] × [-Γ, Γ]` proves unconditionally BOTH
        Local RH (`ζ(s) = 0 ∧ |Im(s)| ≤ Γ → Re(s) = 1/2`) AND strict simplicity of every
        critical-line zero with `|γ| ≤ Γ` (`Ξ'(γ) ≠ 0`).
      * `stripAngleBeta_mem_Ioo`, `stripAngleBeta_reflect`, `stripAngleBeta_eq_half_iff`,
        `stripKineticBarrier_ge_two_and_eq_iff`, `xiNormSq_angular_deriv_eq`, &
        `riemannHypothesis_of_angularDescent`: Compactified angular strip coordinate
        `β(θ) = cos^2(θ/2)`, kinetic barrier `1/(2β(1-β)) = 2/sin^2(θ) ≥ 2` with unique
        minimum at `θ = π/2 ↔ β = 1/2`, and angular descent reduction to `RiemannHypothesis`.
  ==============================================================================
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannDipolar.ArithmeticWeilAndWideCorridor

noncomputable section

open Real Complex MeasureTheory Filter Set Topology BigOperators
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor

namespace UniversalWeilAndHerglotzResolvent

-- ==============================================================================
-- PART I: ROUTE A — UNIVERSAL FINITE-CODIMENSION COERCIVITY FOR EVERY L > 0
-- ==============================================================================

/-- Helper: continuity of a finite sum of continuous functions. -/
private lemma continuous_sum_finset {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x : ℝ => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact continuous_const
  | @insert a s ha ih =>
    have hrew : (fun x : ℝ => ∑ i ∈ insert a s, f i x) =
        fun x : ℝ => f a x + ∑ i ∈ s, f i x := by
      ext x; exact Finset.sum_insert ha
    rw [hrew]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Helper: interval integral of a finite sum of interval-integrable functions. -/
private lemma intervalIntegral_sum_finset {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {a b : ℝ} {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ x in a..b, (∑ i ∈ s, f i x) = ∑ i ∈ s, ∫ x in a..b, f i x := by
  have hint_sum : ∀ t : Finset ι, (∀ i ∈ t, IntervalIntegrable (f i) volume a b) →
      IntervalIntegrable (fun x : ℝ => ∑ i ∈ t, f i x) volume a b := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp only [Finset.sum_empty]; exact intervalIntegrable_const
    | @insert j t hj iht =>
      intro hft
      have hr : (fun x : ℝ => ∑ i ∈ insert j t, f i x) =
          fun x : ℝ => f j x + ∑ i ∈ t, f i x := by ext x; exact Finset.sum_insert hj
      rw [hr]
      exact (hft j (Finset.mem_insert_self j t)).add
        (iht fun i hi => hft i (Finset.mem_insert_of_mem hi))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hrew : (fun x : ℝ => ∑ i ∈ insert k s, f i x) =
        fun x : ℝ => f k x + ∑ i ∈ s, f i x := by
      ext x; exact Finset.sum_insert hk
    rw [hrew, intervalIntegral.integral_add (hf k (Finset.mem_insert_self k s))
          (hint_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert hk]

/-- Helper: Bochner integral of a finite sum of integrable real functions. -/
private lemma integral_sum_finset_real {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, Integrable (f i)) :
    ∫ x : ℝ, (∑ i ∈ s, f i x) = ∑ i ∈ s, ∫ x : ℝ, f i x := by
  have hint_sum : ∀ t : Finset ι, (∀ i ∈ t, Integrable (f i)) →
      Integrable (fun x : ℝ => ∑ i ∈ t, f i x) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp only [Finset.sum_empty]; exact integrable_zero ℝ ℝ volume
    | @insert j t hj iht =>
      intro hft
      have hr : (fun x : ℝ => ∑ i ∈ insert j t, f i x) =
          fun x : ℝ => f j x + ∑ i ∈ t, f i x := by ext x; exact Finset.sum_insert hj
      rw [hr]
      exact (hft j (Finset.mem_insert_self j t)).add
        (iht fun i hi => hft i (Finset.mem_insert_of_mem hi))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hrew : (fun x : ℝ => ∑ i ∈ insert k s, f i x) =
        fun x : ℝ => f k x + ∑ i ∈ s, f i x := by
      ext x; exact Finset.sum_insert hk
    rw [hrew, MeasureTheory.integral_add (hf k (Finset.mem_insert_self k s))
          (hint_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert hk]

/-- Auxiliary: Exact complex Taylor remainder bound on the unit circle `e^{-ix}`:
    for every `N : ℕ` and every `x : ℝ`,
      `‖exp (-I * x) - ∑ m ∈ Finset.range N, (-I * x)^m / m!‖ ≤ |x|^N / N!`. -/
theorem norm_exp_neg_I_sub_taylor_le (N : ℕ) :
    ∀ x : ℝ, ‖Complex.exp (-Complex.I * (x : ℂ)) -
      ∑ m ∈ Finset.range N, (-Complex.I * (x : ℂ)) ^ m / (Nat.factorial m : ℂ)‖ ≤
      |x| ^ N / (Nat.factorial N : ℝ) := by
  induction N with
  | zero =>
    intro x
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]
    have hnorm : ‖Complex.exp (-Complex.I * (x : ℂ))‖ = 1 := by
      have harg : -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    exact le_of_eq hnorm
  | succ N ih =>
    intro x
    let R : ℕ → ℝ → ℂ := fun n s =>
      Complex.exp (-Complex.I * (s : ℂ)) -
        ∑ m ∈ Finset.range n, (-Complex.I * (s : ℂ)) ^ m / (Nat.factorial m : ℂ)
    change ‖R (N + 1) x‖ ≤ |x| ^ (N + 1) / (Nat.factorial (N + 1) : ℝ)
    have hR0 : R (N + 1) 0 = 0 := by
      dsimp [R]
      rw [Finset.sum_range_succ']
      simp [Nat.factorial_zero]
    have hderiv : ∀ s : ℝ, HasDerivAt (R (N + 1)) (-Complex.I * R N s) s := by
      intro s
      have hlin : HasDerivAt (fun t : ℝ => -Complex.I * (t : ℂ)) (-Complex.I) s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-Complex.I)
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ)))
          (-Complex.I * Complex.exp (-Complex.I * (s : ℂ))) s := by
        have h1 := (Complex.hasDerivAt_exp (-Complex.I * (s : ℂ))).scomp s hlin
        simpa [Function.comp_def, smul_eq_mul, mul_comm] using h1
      have hsum : HasDerivAt
          (fun t : ℝ => ∑ m ∈ Finset.range (N + 1), (-Complex.I * (t : ℂ)) ^ m / (Nat.factorial m : ℂ))
          (-Complex.I * ∑ m ∈ Finset.range N, (-Complex.I * (s : ℂ)) ^ m / (Nat.factorial m : ℂ)) s := by
        have hshift : (fun t : ℝ => ∑ m ∈ Finset.range (N + 1), (-Complex.I * (t : ℂ)) ^ m / (Nat.factorial m : ℂ)) =
            fun t : ℝ => (∑ m ∈ Finset.range N,
              (-Complex.I * (t : ℂ)) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) + (1 : ℂ) := by
          ext t
          rw [Finset.sum_range_succ']
          simp [Nat.factorial_zero]
        rw [hshift]
        have hterm : ∀ m ∈ Finset.range N,
            HasDerivAt (fun t : ℝ => (-Complex.I * (t : ℂ)) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ))
              (-Complex.I * ((-Complex.I * (s : ℂ)) ^ m / (Nat.factorial m : ℂ))) s := by
          intro m _
          have hpow := (hlin.pow (m + 1)).div_const (Nat.factorial (m + 1) : ℂ)
          convert hpow using 1
          have hfac : (Nat.factorial (m + 1) : ℂ) = ((m + 1 : ℕ) : ℂ) * (Nat.factorial m : ℂ) := by
            exact_mod_cast Nat.factorial_succ m
          have hne1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
          have hne2 : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
          simp only [Nat.add_sub_cancel]
          rw [hfac]
          field_simp [hne1, hne2]
        have hfin : HasDerivAt
            (fun t : ℝ => ∑ m ∈ Finset.range N, (-Complex.I * (t : ℂ)) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ))
            (∑ m ∈ Finset.range N, -Complex.I * ((-Complex.I * (s : ℂ)) ^ m / (Nat.factorial m : ℂ))) s :=
          HasDerivAt.fun_sum hterm
        simpa [Finset.mul_sum] using hfin.add_const (1 : ℂ)
      have hsub : HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ)) -
          ∑ m ∈ Finset.range (N + 1), (-Complex.I * (t : ℂ)) ^ m / (Nat.factorial m : ℂ))
          ((-Complex.I * Complex.exp (-Complex.I * (s : ℂ))) -
            (-Complex.I * ∑ m ∈ Finset.range N, (-Complex.I * (s : ℂ)) ^ m / (Nat.factorial m : ℂ))) s :=
        hexp.fun_sub hsum
      simpa [R, mul_sub] using hsub
    have hcont : Continuous (fun s : ℝ => -Complex.I * R N s) := by
      dsimp [R]
      refine continuous_const.mul ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).sub ?_)
      exact continuous_sum_finset fun m _ =>
        ((continuous_const.mul Complex.continuous_ofReal).pow m).div_const _
    have hftc : ∫ s in (0 : ℝ)..x, (-Complex.I * R N s) = R (N + 1) x - R (N + 1) 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
        (hcont.intervalIntegrable (μ := volume) 0 x)
    rw [hR0, sub_zero] at hftc
    rw [← hftc]
    have hbd_fn : ∀ s : ℝ, ‖-Complex.I * R N s‖ ≤ |s| ^ N / (Nat.factorial N : ℝ) := by
      intro s
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact ih s
    rcases le_total 0 x with hx | hx
    · have hle := intervalIntegral.norm_integral_le_of_norm_le hx
        (f := fun s : ℝ => -Complex.I * R N s)
        (g := fun s : ℝ => s ^ N / (Nat.factorial N : ℝ))
        (Filter.Eventually.of_forall fun s hs => by
          have hs0 : 0 ≤ s := le_of_lt hs.1
          have h := hbd_fn s
          rwa [abs_of_nonneg hs0] at h)
        (((continuous_pow N).div_const _).intervalIntegrable (μ := volume) 0 x)
      have hint : ∫ s in (0 : ℝ)..x, s ^ N / (Nat.factorial N : ℝ) =
          x ^ (N + 1) / (Nat.factorial (N + 1) : ℝ) := by
        rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero N), sub_zero]
        have hfac : (Nat.factorial (N + 1) : ℝ) = ((N + 1 : ℕ) : ℝ) * (Nat.factorial N : ℝ) := by
          exact_mod_cast Nat.factorial_succ N
        rw [hfac, div_div]; push_cast; ring
      rw [hint] at hle
      rwa [abs_of_nonneg hx]
    · rw [intervalIntegral.integral_symm, norm_neg]
      have hle := intervalIntegral.norm_integral_le_of_norm_le hx
        (f := fun s : ℝ => -Complex.I * R N s)
        (g := fun s : ℝ => (-s) ^ N / (Nat.factorial N : ℝ))
        (Filter.Eventually.of_forall fun s hs => by
          have hs0 : s ≤ 0 := hs.2
          have h := hbd_fn s
          rwa [abs_of_nonpos hs0] at h)
        ((((continuous_neg).pow N).div_const _).intervalIntegrable (μ := volume) x 0)
      have hint : ∫ s in x..(0 : ℝ), (-s) ^ N / (Nat.factorial N : ℝ) =
          (-x) ^ (N + 1) / (Nat.factorial (N + 1) : ℝ) := by
        have hcomp := intervalIntegral.integral_comp_neg
          (f := fun s : ℝ => s ^ N / (Nat.factorial N : ℝ)) (a := x) (b := 0)
        simp only [neg_zero] at hcomp
        rw [hcomp, intervalIntegral.integral_div, integral_pow,
            zero_pow (Nat.succ_ne_zero N), sub_zero]
        have hfac : (Nat.factorial (N + 1) : ℝ) = ((N + 1 : ℕ) : ℝ) * (Nat.factorial N : ℝ) := by
          exact_mod_cast Nat.factorial_succ N
        rw [hfac, div_div]; push_cast; ring
      rw [hint] at hle
      rwa [abs_of_nonpos hx]

/-- Elementary super-exponential decay: for every `a ≥ 0` and `ε > 0`,
    there exists `N : ℕ` with `a ^ N / N! < ε`. -/
theorem exists_pow_div_factorial_lt {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N : ℕ, a ^ N / (Nat.factorial N : ℝ) < ε := by
  let K : ℕ := Nat.ceil (2 * a) + 1
  have hK_ge : 2 * a ≤ (K : ℝ) := by
    have := Nat.le_ceil (2 * a)
    have h1 : (Nat.ceil (2 * a) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith
  have hstep : ∀ j : ℕ, a ^ (K + j) / (Nat.factorial (K + j) : ℝ) ≤
      (a ^ K / (Nat.factorial K : ℝ)) * (1 / 2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hfac : (Nat.factorial (K + (j + 1)) : ℝ) =
          ((K + j + 1 : ℕ) : ℝ) * (Nat.factorial (K + j) : ℝ) := by
        have : K + (j + 1) = (K + j) + 1 := by omega
        rw [this]; exact_mod_cast Nat.factorial_succ (K + j)
      have hpow : a ^ (K + (j + 1)) = a * a ^ (K + j) := by
        have : K + (j + 1) = (K + j) + 1 := by omega
        rw [this, pow_succ']
      have hratio : a / ((K + j + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        have hpos : (0 : ℝ) < ((K + j + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_div_iff₀ hpos (by norm_num)]
        have hge : (K : ℝ) ≤ ((K + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ K + j + 1)
        linarith
      rw [hpow, hfac, mul_div_mul_comm, pow_succ]
      have hnn1 : 0 ≤ a ^ (K + j) / (Nat.factorial (K + j) : ℝ) := by positivity
      calc (a / ((K + j + 1 : ℕ) : ℝ)) * (a ^ (K + j) / (Nat.factorial (K + j) : ℝ))
        _ ≤ (1 / 2 : ℝ) * (a ^ (K + j) / (Nat.factorial (K + j) : ℝ)) :=
            mul_le_mul_of_nonneg_right hratio hnn1
        _ ≤ (1 / 2 : ℝ) * ((a ^ K / (Nat.factorial K : ℝ)) * (1 / 2 : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (a ^ K / (Nat.factorial K : ℝ)) * ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ)) := by ring
  let C : ℝ := a ^ K / (Nat.factorial K : ℝ)
  have hC_nn : 0 ≤ C := by positivity
  -- Choose j with (C + 1) / (j + 1) < ε, using (1/2)^j ≤ 1/(j + 1) since j + 1 ≤ 2^j (for j ≥ 0)!
  have hpow2 : ∀ j : ℕ, (j + 1 : ℝ) ≤ (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      push_cast at ih ⊢
      rw [pow_succ]
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      linarith
  let j : ℕ := Nat.ceil ((C + 1) / ε) + 1
  refine ⟨K + j, ?_⟩
  have h1 := hstep j
  have h2 : (1 / 2 : ℝ) ^ j ≤ 1 / ((j : ℝ) + 1) := by
    rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
    exact_mod_cast hpow2 j
  have h3 : (C + 1) / ε < (j : ℝ) + 1 := by
    have hce := Nat.le_ceil ((C + 1) / ε)
    have hlt : (Nat.ceil ((C + 1) / ε) : ℝ) < (j : ℝ) + 1 := by
      dsimp [j]; push_cast; linarith
    linarith
  have h4 : C * (1 / ((j : ℝ) + 1)) < ε := by
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [mul_one_div, div_lt_iff₀ hpos]
    have hmul : C + 1 < ((j : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h3
    linarith
  calc a ^ (K + j) / (Nat.factorial (K + j) : ℝ)
    _ ≤ C * (1 / 2 : ℝ) ^ j := h1
    _ ≤ C * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2 hC_nn
    _ < ε := h4

/-- THEOREM I.3 (Uniform Low-Frequency Fourier Suppression by Moment Orthogonality):
    If `g : ℝ → ℂ` is continuous on `[-L/2, L/2]` (`L > 0`) and orthogonal to the first
    `N` monomials `{1, u, ..., u^{N-1}}`, then for EVERY frequency `|t| ≤ T` (`T ≥ 0`),
      `‖compactFourier L g t‖^2 ≤ L * ((L * T / 2)^N / N!)^2 * ∫_{-L/2}^{L/2} ‖g u‖^2 du`. -/
theorem compactFourier_norm_sq_le_of_moment_orthog {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T)
    {N : ℕ} {g : ℝ → ℂ} (hg : Continuous g)
    (horth : ∀ m < N, ∫ u in (-L / 2)..(L / 2), g u * (u : ℂ) ^ m = 0)
    {t : ℝ} (ht : |t| ≤ T) :
    ‖compactFourier L g t‖ ^ 2 ≤
      L * ((L * T / 2) ^ N / (Nat.factorial N : ℝ)) ^ 2 *
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  -- Step 1: Subtract the degree-(N-1) Taylor polynomial of e^{itu} = e^{-i(-tu)}
  have hpoly_zero : ∫ u in (-L / 2)..(L / 2),
      g u * ∑ m ∈ Finset.range N, (Complex.I * (t : ℂ) * (u : ℂ)) ^ m / (Nat.factorial m : ℂ) = 0 := by
    have hrew : (fun u : ℝ => g u * ∑ m ∈ Finset.range N,
        (Complex.I * (t : ℂ) * (u : ℂ)) ^ m / (Nat.factorial m : ℂ)) =
        fun u : ℝ => ∑ m ∈ Finset.range N,
          ((Complex.I * (t : ℂ)) ^ m / (Nat.factorial m : ℂ)) * (g u * (u : ℂ) ^ m) := by
      ext u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_pow]; ring
    rw [hrew, intervalIntegral_sum_finset]
    · refine Finset.sum_eq_zero fun m hm => ?_
      rw [intervalIntegral.integral_const_mul, horth m (Finset.mem_range.mp hm), mul_zero]
    · intro m _
      exact (continuous_const.mul (hg.mul (Complex.continuous_ofReal.pow m))).intervalIntegrable
        (μ := volume) (-L / 2) (L / 2)
  have hdiff_eq : compactFourier L g t = ∫ u in (-L / 2)..(L / 2),
      g u * (Complex.exp (-Complex.I * ((-t * u : ℝ) : ℂ)) -
        ∑ m ∈ Finset.range N, (-Complex.I * ((-t * u : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)) := by
    have hcont1 : Continuous (fun u : ℝ => g u * Complex.exp (-Complex.I * ((-t * u : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))))
    have hcont2 : Continuous (fun u : ℝ => g u * ∑ m ∈ Finset.range N,
        (-Complex.I * ((-t * u : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)) :=
      hg.mul (continuous_sum_finset fun m _ =>
        ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_id))).pow m).div_const _)
    have hsub := intervalIntegral.integral_sub
      (hcont1.intervalIntegrable (μ := volume) (-L / 2) (L / 2))
      (hcont2.intervalIntegrable (μ := volume) (-L / 2) (L / 2))
    have hpoly_eq : (fun u : ℝ => g u * ∑ m ∈ Finset.range N,
        (-Complex.I * ((-t * u : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)) =
        fun u : ℝ => g u * ∑ m ∈ Finset.range N,
          (Complex.I * (t : ℂ) * (u : ℂ)) ^ m / (Nat.factorial m : ℂ) := by
      ext u; congr 1; refine Finset.sum_congr rfl fun m _ => ?_
      push_cast; ring_nf
    rw [hpoly_eq, hpoly_zero, sub_zero] at hsub
    have hf1 : (fun u : ℝ => g u * Complex.exp (-Complex.I * ((-t * u : ℝ) : ℂ))) =
        fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) := by
      ext u; push_cast; ring_nf
    have hsub' : ∫ u in (-L / 2)..(L / 2),
        g u * (Complex.exp (-Complex.I * ((-t * u : ℝ) : ℂ)) -
          ∑ m ∈ Finset.range N, (-Complex.I * ((-t * u : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)) =
        ∫ u in (-L / 2)..(L / 2), g u * Complex.exp (-Complex.I * ((-t * u : ℝ) : ℂ)) := by
      simpa [mul_sub] using hsub
    dsimp [compactFourier]
    rw [hsub', hf1]
  -- Step 2: Pointwise bound by M := (L*T/2)^N / N! and Cauchy-Schwarz on [-L/2, L/2]
  set M : ℝ := (L * T / 2) ^ N / (Nat.factorial N : ℝ)
  have hM_nn : 0 ≤ M := by positivity
  have hle : -L / 2 ≤ L / 2 := by linarith
  have hnorm_le : ‖compactFourier L g t‖ ≤ M * ∫ u in (-L / 2)..(L / 2), ‖g u‖ := by
    rw [hdiff_eq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall fun u hu => ?_)
      ((continuous_const.mul hg.norm).intervalIntegrable (μ := volume) (-L / 2) (L / 2))
    rw [norm_mul, mul_comm]
    have htu_abs : |-t * u| ≤ L * T / 2 := by
      rw [abs_mul, abs_neg]
      have hu_abs : |u| ≤ L / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
      calc |t| * |u| ≤ T * (L / 2) := mul_le_mul ht hu_abs (abs_nonneg u) hT
        _ = L * T / 2 := by ring
    have hrem : ‖Complex.exp (-Complex.I * ((-t * u : ℝ) : ℂ)) -
        ∑ m ∈ Finset.range N, (-Complex.I * ((-t * u : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)‖ ≤ M := by
      calc _ ≤ |-t * u| ^ N / (Nat.factorial N : ℝ) := norm_exp_neg_I_sub_taylor_le N (-t * u)
        _ ≤ (L * T / 2) ^ N / (Nat.factorial N : ℝ) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) htu_abs N) (by positivity)
    exact mul_le_mul_of_nonneg_right hrem (norm_nonneg _)
  -- Step 3: Square and apply Cauchy-Schwarz (∫ ‖g‖)^2 ≤ L * ∫ ‖g‖^2
  have hcs : (∫ u in (-L / 2)..(L / 2), ‖g u‖) ^ 2 ≤ L * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    have hquad : ∀ α : ℝ, 0 ≤ ∫ u in (-L / 2)..(L / 2), (‖g u‖ - α) ^ 2 := fun α =>
      intervalIntegral.integral_nonneg hle (fun _ _ => sq_nonneg _)
    have hexp : ∀ α : ℝ, ∫ u in (-L / 2)..(L / 2), (‖g u‖ - α) ^ 2 =
        (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) - 2 * α * (∫ u in (-L / 2)..(L / 2), ‖g u‖) + α ^ 2 * L := by
      intro α
      have h1 : (fun u : ℝ => (‖g u‖ - α) ^ 2) =
          fun u : ℝ => (‖g u‖ ^ 2 - (2 * α) * ‖g u‖) + α ^ 2 := by ext u; ring
      have hadd := intervalIntegral.integral_add
        (f := fun u : ℝ => ‖g u‖ ^ 2 - (2 * α) * ‖g u‖) (g := fun _ : ℝ => α ^ 2)
        (((hg.norm.pow 2).sub (continuous_const.mul hg.norm)).intervalIntegrable (μ := volume) (-L / 2) (L / 2))
        (continuous_const.intervalIntegrable (μ := volume) (-L / 2) (L / 2))
      have hsub := intervalIntegral.integral_sub
        (f := fun u : ℝ => ‖g u‖ ^ 2) (g := fun u : ℝ => (2 * α) * ‖g u‖)
        ((hg.norm.pow 2).intervalIntegrable (μ := volume) (-L / 2) (L / 2))
        ((continuous_const.mul hg.norm).intervalIntegrable (μ := volume) (-L / 2) (L / 2))
      rw [h1, hadd, hsub, intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hspec := hquad ((∫ u in (-L / 2)..(L / 2), ‖g u‖) / L)
    rw [hexp] at hspec
    have hmul := mul_nonneg hspec (le_of_lt hL)
    have hne : L ≠ 0 := ne_of_gt hL
    have hid : ((∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) -
        2 * ((∫ u in (-L / 2)..(L / 2), ‖g u‖) / L) * (∫ u in (-L / 2)..(L / 2), ‖g u‖) +
        ((∫ u in (-L / 2)..(L / 2), ‖g u‖) / L) ^ 2 * L) * L =
        L * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) - (∫ u in (-L / 2)..(L / 2), ‖g u‖) ^ 2 := by
      field_simp [hne]; ring
    linarith
  have hint_nn : 0 ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ :=
    intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
  have hsq : ‖compactFourier L g t‖ ^ 2 ≤ M ^ 2 * (∫ u in (-L / 2)..(L / 2), ‖g u‖) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
    simpa [mul_pow] using this
  have hmul_cs : M ^ 2 * (∫ u in (-L / 2)..(L / 2), ‖g u‖) ^ 2 ≤
      M ^ 2 * (L * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hcs (sq_nonneg M)
  linarith

/-- THEOREM I.4 (Refined Split Multi-Prime Operator Norm Bound):
    Using the disjoint-strip 1/2-factor bound (`shift_overlap_re_le_half_L2_of_disjoint`) for
    all prime powers with `L/2 ≤ log n ≤ L` and Cauchy-Schwarz for `log n < L/2`,
      `|W_prime(L, g)| ≤ (∑_{2 ≤ n ≤ ⌊e^L⌋} (if L/2 ≤ log n then 1 else 2) * Λ(n)/√n) * ‖g‖_2^2`. -/
theorem weilPrime_refined_norm_bound {L : ℝ} (_hL : 0 < L) {g : ℝ → ℂ} (hg : Continuous g) :
    |weilPrime L g| ≤
      (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        (if L / 2 ≤ Real.log (n : ℝ) then (1 : ℝ) else 2) *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ))) *
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  dsimp [weilPrime]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htri : |∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| ≤
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
        |(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
          (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
            g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| :=
    Finset.abs_sum_le_sum_abs _ _
  have hterm : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      2 * |(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        (∫ u in (-L / 2 + Real.log (n : ℝ))..(L / 2),
          g u * starRingEnd ℂ (g (u - Real.log (n : ℝ)))).re| ≤
      (if L / 2 ≤ Real.log (n : ℝ) then (1 : ℝ) else 2) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)) *
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hn_le_exp : (n : ℝ) ≤ Real.exp L :=
      (Nat.le_floor_iff (le_of_lt (Real.exp_pos L))).mp hn.2
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hlog_le : Real.log (n : ℝ) ≤ L := by
      have := Real.log_le_log (by linarith : (0 : ℝ) < n) hn_le_exp
      rwa [Real.log_exp] at this
    have hcoeff_nn : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    rw [abs_mul, abs_of_nonneg hcoeff_nn]
    by_cases hhalf : L / 2 ≤ Real.log (n : ℝ)
    · simp only [hhalf, ↓reduceIte, one_mul]
      have hsh := shift_overlap_re_le_half_L2_of_disjoint hhalf hlog_le hg
      have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hcoeff_nn) (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    · simp only [hhalf, ↓reduceIte]
      have hsh := shift_overlap_re_le_L2 hlog_nn hlog_le hg
      have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsh hcoeff_nn) (by norm_num : (0 : ℝ) ≤ 2)
      linarith
  have hsum_le := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum_le
  have hmul2 := mul_le_mul_of_nonneg_left htri (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- THEOREM I.5 (UNIVERSAL FINITE-CODIMENSION COERCIVITY OF THE CONTINUOUS ARITHMETIC
    WEIL FUNCTIONAL FOR EVERY `L > 0` AND EVERY TARGET MARGIN `c ∈ ℝ`):
    For EVERY support length `L > 0` (incorporating ALL exact `vonMangoldt` prime powers
    `p^m ≤ e^L`) and EVERY coercivity constant `c ∈ ℝ`, there exists an explicit finite
    codimension `N : ℕ` such that for EVERY continuous `g : ℝ → ℂ` on `[-L/2, L/2]`
    orthogonal to the `N` monomials `{1, u, ..., u^{N-1}}`,
      `c * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ weilTotal L g`.
    (Establishes unconditionally with zero discretization that the essential high-frequency
    spectrum of the full continuous arithmetic Weil operator is `+∞` for EVERY `L > 0`.) -/
theorem weilTotal_universal_finite_codim_coercive {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∃ N : ℕ, ∀ (g : ℝ → ℂ), Continuous g →
      (Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
        (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
          ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) →
      Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2) →
      (∀ m < N, ∫ u in (-L / 2)..(L / 2), g u * (u : ℂ) ^ m = 0) →
      c * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  -- Step 1: Uniform L^2 lower bound on W_pole(L, g) - W_prime(L, g) ≥ -M_L * ‖g‖_2^2
  let P_L : ℝ := 2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
    ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
  let M_L : ℝ := 2 * (Real.sinh (L / 2) - L / 2) + P_L
  -- Step 2: Choose frequency cutoff T ≥ 1 such that psiLb3 T ≥ M_L + c + 1
  let T : ℝ := 7 * Real.exp (|M_L + c| + 7)
  have hT_pos : 0 < T := by positivity
  have hpsiT_ge : M_L + c + 1 ≤ psiLb3 T := by
    dsimp [psiLb3]
    have hC := archimedeanWeilConst_lt
    have hr0 : 0 ≤ (4 * T ^ 2) / (1 / 4 + T ^ 2) := by positivity
    have hr1 : 0 ≤ ((4 / 5 : ℝ) * T ^ 2) / (25 / 4 + T ^ 2) := by positivity
    have hr2 : 0 ≤ ((4 / 9 : ℝ) * T ^ 2) / (81 / 4 + T ^ 2) := by positivity
    have hlog_ge : 2 * (|M_L + c| + 7) ≤ Real.log (1 + 4 * T ^ 2 / 169) := by
      have hexp_le : Real.exp (2 * (|M_L + c| + 7)) ≤ 1 + 4 * T ^ 2 / 169 := by
        have hT2 : 4 * T ^ 2 / 169 = (196 / 169 : ℝ) * Real.exp (2 * (|M_L + c| + 7)) := by
          dsimp [T]
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num; ring
        rw [hT2]
        have hepos := Real.exp_pos (2 * (|M_L + c| + 7))
        linarith
      have h1 := Real.log_le_log (Real.exp_pos _) hexp_le
      rwa [Real.log_exp] at h1
    have habs : M_L + c ≤ |M_L + c| := le_abs_self _
    linarith
  -- Step 3: Upper bound on low-frequency penalty factor D_T := (L / π) * T * (psiLb3 T + 6)
  have hpsiT_nn : 0 ≤ psiLb3 T + 6 := by
    dsimp [psiLb3]
    have hC := archimedeanWeilConst_lt
    have h1 : 0 ≤ (4 * T ^ 2) / (1 / 4 + T ^ 2) := by positivity
    have h2 : 0 ≤ ((4 / 5 : ℝ) * T ^ 2) / (25 / 4 + T ^ 2) := by positivity
    have h3 : 0 ≤ ((4 / 9 : ℝ) * T ^ 2) / (81 / 4 + T ^ 2) := by positivity
    have h4 : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + 4 * T ^ 2 / 169) :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg T]))
    linarith
  let D_T : ℝ := (L / Real.pi) * T * (psiLb3 T + 6) + 1
  have hD_pos : 0 < D_T := by positivity
  -- Choose N so that ((L*T/2)^N / N!) < 1 / √(D_T) (so square * D_T ≤ 1!)
  obtain ⟨N, hN⟩ := exists_pow_div_factorial_lt (a := L * T / 2) (ε := 1 / Real.sqrt D_T)
    (by positivity) (by positivity)
  have hN_sq : ((L * T / 2) ^ N / (Nat.factorial N : ℝ)) ^ 2 * D_T ≤ 1 := by
    have h1 : ((L * T / 2) ^ N / (Nat.factorial N : ℝ)) ^ 2 ≤ (1 / Real.sqrt D_T) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (le_of_lt hN) 2
    have h2 : (1 / Real.sqrt D_T) ^ 2 = 1 / D_T := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hD_pos)]
    rw [h2] at h1
    have hmul := mul_le_mul_of_nonneg_right h1 (le_of_lt hD_pos)
    have hsimp : (1 / D_T) * D_T = 1 := one_div_mul_cancel (ne_of_gt hD_pos)
    linarith
  -- Step 4: Verify coercivity for every moment-orthogonal continuous g
  refine ⟨N, fun g hg hplanch hpsi_int horth => ?_⟩
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- Pole + Prime lower bound:
  have hpole := weilPole_lower_bound_all (le_of_lt hL) hg
  have hprime := weilPrime_general_norm_bound hL hg
  have hprime_le : weilPrime L g ≤ P_L * N2 := (le_abs_self _).trans hprime
  -- Archimedean lower bound via cutoff at T:
  have hdiff_int : Integrable (fun t : ℝ => (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2) := by
    have h1 := hpsi_int.sub (hplanch.1.const_mul (psiLb3 T))
    exact h1.congr (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 =
      psiLb3 T * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) +
        ∫ t : ℝ, (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add (hplanch.1.const_mul (psiLb3 T)) hdiff_int]
    congr 1; ext t; ring
  have htail_nn : ∀ t : ℝ, T ≤ |t| → 0 ≤ (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
    intro t ht
    have h1 : psiLb3 T ≤ psiArch T := psiArch_ge_psiLb3 T
    have h2 : psiArch T ≤ psiArch |t| := by
      rcases eq_or_lt_of_le ht with heq | hlt
      · rw [← heq]
      · exact le_of_lt (psiArch_strictMono_nonneg (le_of_lt hT_pos) (abs_nonneg t) hlt)
    have h3 : psiArch |t| = psiArch t := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, psiArch_even]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  set M_fac : ℝ := (L * T / 2) ^ N / (Nat.factorial N : ℝ)
  have hlow_pt : ∀ t : ℝ,
      (Icc (-T) T).indicator (fun _ : ℝ => -(psiLb3 T + 6) * (L * M_fac ^ 2 * N2)) t ≤
        (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
    intro t
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]
      have ht_abs : |t| ≤ T := abs_le.mpr ht
      have hpsi_low : -(psiLb3 T + 6) ≤ psiArch t - psiLb3 T := by
        have h1 : -6 ≤ psiLb3 t := by
          dsimp [psiLb3]
          have hC := archimedeanWeilConst_lt
          have h0 : 0 ≤ (4 * t ^ 2) / (1 / 4 + t ^ 2) := by positivity
          have h1' : 0 ≤ ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2) := by positivity
          have h2' : 0 ≤ ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2) := by positivity
          have h3' : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169) :=
            mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg t]))
          linarith
        linarith [psiArch_ge_psiLb3 t]
      have hfour : ‖compactFourier L g t‖ ^ 2 ≤ L * M_fac ^ 2 * N2 :=
        compactFourier_norm_sq_le_of_moment_orthog hL (le_of_lt hT_pos) hg horth ht_abs
      have hm1 : -(psiLb3 T + 6) * (L * M_fac ^ 2 * N2) ≤
          -(psiLb3 T + 6) * ‖compactFourier L g t‖ ^ 2 := by nlinarith
      have hm2 : -(psiLb3 T + 6) * ‖compactFourier L g t‖ ^ 2 ≤
          (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hpsi_low (sq_nonneg _)
      linarith
    · rw [indicator_of_notMem ht]
      have habs : T ≤ |t| := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact htail_nn t habs
  have hint_ind : Integrable ((Icc (-T) T).indicator
      (fun _ : ℝ => -(psiLb3 T + 6) * (L * M_fac ^ 2 * N2))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hmono_int := integral_mono hint_ind hdiff_int hlow_pt
  rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      intervalIntegral.integral_const, smul_eq_mul] at hmono_int
  have harch_ge : (psiLb3 T - M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6))) * N2 ≤
      (1 / (2 * Real.pi)) * ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 := by
    have hmul_pi := mul_le_mul_of_nonneg_left hmono_int (by positivity : 0 ≤ 1 / (2 * Real.pi))
    have htot : (1 / (2 * Real.pi)) * ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 =
        psiLb3 T * N2 + (1 / (2 * Real.pi)) * ∫ t : ℝ, (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
      rw [hsplit, mul_add, ← hplanch.2]; ring
    have hsimp_lhs : (1 / (2 * Real.pi)) * ((T - -T) * (-(psiLb3 T + 6) * (L * M_fac ^ 2 * N2))) =
        -(M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6))) * N2 := by
      field_simp [ne_of_gt Real.pi_pos]; ring
    rw [hsimp_lhs] at hmul_pi
    linarith
  have hpen_le_one : M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6)) ≤ 1 := by
    have hsub : (L / Real.pi) * T * (psiLb3 T + 6) ≤ D_T := by dsimp [D_T]; linarith
    calc M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6))
      _ ≤ M_fac ^ 2 * D_T := mul_le_mul_of_nonneg_left hsub (sq_nonneg _)
      _ ≤ 1 := hN_sq
  have hcoeff : c ≤ (psiLb3 T - M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6))) - M_L := by
    linarith
  have hmul_N2 := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal
  change c * N2 ≤ weilPole L g + (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) - weilPrime L g
  have hpole'' : -(2 * (Real.sinh (L / 2) - L / 2) * N2) ≤ weilPole L g := by
    have h1 : -(2 * (Real.sinh (L / 2) - L / 2)) * N2 ≤ weilPole L g := hpole
    linarith
  have hM_eq : M_L * N2 = 2 * (Real.sinh (L / 2) - L / 2) * N2 + P_L * N2 := by dsimp [M_L]; ring
  have hdist : (psiLb3 T - M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6)) - M_L) * N2 =
      (psiLb3 T - M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6))) * N2 - M_L * N2 := by ring
  calc c * N2
    _ ≤ (psiLb3 T - M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6)) - M_L) * N2 := hmul_N2
    _ = -(2 * (Real.sinh (L / 2) - L / 2) * N2) +
          (psiLb3 T - M_fac ^ 2 * ((L / Real.pi) * T * (psiLb3 T + 6))) * N2 - P_L * N2 := by
        rw [hdist, hM_eq]; ring
    _ ≤ weilPole L g + (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) - weilPrime L g :=
        sub_le_sub (add_le_add hpole'' harch_ge) hprime_le

/-- COROLLARY I.6 (Strict Positivity of `weilTotal` on a Finite-Codimension Subspace for ALL `L > 0`):
    For EVERY `L > 0`, there exists `N : ℕ` such that every continuous `g` on `[-L/2, L/2]`
    with positive `L^2` norm and orthogonal to `{1, u, ..., u^{N-1}}` satisfies `0 < weilTotal L g`. -/
theorem weilTotal_strict_pos_on_finite_codim {L : ℝ} (hL : 0 < L) :
    ∃ N : ℕ, ∀ (g : ℝ → ℂ), Continuous g →
      (Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
        (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
          ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) →
      Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2) →
      (∀ m < N, ∫ u in (-L / 2)..(L / 2), g u * (u : ℂ) ^ m = 0) →
      0 < (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) →
      0 < weilTotal L g := by
  obtain ⟨N, hN⟩ := weilTotal_universal_finite_codim_coercive hL 1
  refine ⟨N, fun g hg hplanch hint horth hpos => ?_⟩
  have h := hN g hg hplanch hint horth
  linarith

-- ==============================================================================
-- PART II: SPECTRAL RESOLVENT, CAUCHY-RIEMANN PHASE LAW, HERGLOTZ-PICK & IDOS
-- ==============================================================================

/-- The Spectral Resolvent of `riemannXi` on the upper half-plane `Im(z) > 0`:
    `R_ξ(z) = i * (ξ'/ξ)(1/2 - i*z)`.
    Writing `z = γ + i*σ`, `1/2 - i*z = 1/2 + σ - i*γ`, so away from zeros
    `Im(R_ξ(γ + iσ)) = Re((ξ'/ξ)(1/2 + σ + iγ)) = (1/2) * ∂_σ log V(σ, γ)`. -/
noncomputable def xiResolvent (z : ℂ) : ℂ :=
  Complex.I * (deriv riemannXi (1 / 2 - Complex.I * z) / riemannXi (1 / 2 - Complex.I * z))

/-- Auxiliary: Equality between `⟨a, b⟩ : ℂ` and `↑a + I * ↑b`. -/
private lemma complex_mk_eq_add_I (a b : ℝ) :
    (⟨a, b⟩ : ℂ) = (a : ℂ) + Complex.I * (b : ℂ) := by
  apply Complex.ext <;> simp

/-- Auxiliary: Schwarz reflection of `deriv riemannXi`: `ξ'(conj s) = conj (ξ'(s))`. -/
private lemma deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannXi s) := by
  have hcomp : HasDerivAt (fun w : ℂ => starRingEnd ℂ (riemannXi (starRingEnd ℂ w)))
      (starRingEnd ℂ (deriv riemannXi (starRingEnd ℂ s))) s := by
    have hd := (riemannXi_entire.differentiableAt (x := starRingEnd ℂ s)).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope]
    have h1 := hasDerivAt_iff_tendsto_slope.mp hd
    have hmap : Filter.Tendsto (fun w : ℂ => starRingEnd ℂ w) (𝓝[≠] s) (𝓝[≠] (starRingEnd ℂ s)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact fun heq => hw (by simpa using congrArg (starRingEnd ℂ) heq)
    have h2 := Complex.continuous_conj.continuousAt.tendsto.comp (h1.comp hmap)
    refine h2.congr fun w => ?_
    simp only [Function.comp_apply, slope_def_field]
    rw [map_div₀, map_sub, map_sub, Complex.conj_conj, Complex.conj_conj]
  have heq : (fun w : ℂ => starRingEnd ℂ (riemannXi (starRingEnd ℂ w))) = riemannXi := by
    ext w; rw [riemannXi_conj, Complex.conj_conj]
  rw [heq] at hcomp
  have huniq := hcomp.unique (riemannXi_entire.differentiableAt (x := s)).hasDerivAt
  have := congrArg (starRingEnd ℂ) huniq
  simpa using this

/-- Auxiliary: Derivative of `σ ↦ xiNormSq σ γ` equals `2 * Re(ξ'(1/2+σ+iγ) * conj(ξ(1/2+σ+iγ)))`. -/
private lemma deriv_xiNormSq_eq_two_re_mul_conj (σ γ : ℝ) :
    deriv (fun s : ℝ => xiNormSq s γ) σ =
      2 * (deriv riemannXi ((1 / 2 + σ : ℝ) + Complex.I * γ) *
        starRingEnd ℂ (riemannXi ((1 / 2 + σ : ℝ) + Complex.I * γ))).re := by
  rw [(hasDerivAt_xiNormSq_sigma σ γ).deriv, complex_mk_eq_add_I]
  congr 2
  exact mul_comm _ _

/-- THEOREM II.1 (EXACT RESOLVENT–LOGARITHMIC FORCE DUALITY):
    For every `σ, γ : ℝ` with `ξ(1/2 + σ + iγ) ≠ 0`, the imaginary part of the spectral
    resolvent `R_ξ(γ + iσ)` equals both `Re(ξ'/ξ(1/2 + σ + iγ))` and `(1/2) * xiLogForce σ γ`. -/
theorem xiResolvent_im_eq_logForce_half {σ γ : ℝ}
    (hxi : riemannXi ((1 / 2 + σ : ℝ) + Complex.I * γ) ≠ 0) :
    (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im =
      (deriv riemannXi ((1 / 2 + σ : ℝ) + Complex.I * γ) /
        riemannXi ((1 / 2 + σ : ℝ) + Complex.I * γ)).re ∧
    (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im = (1 / 2 : ℝ) * xiLogForce σ γ := by
  let s : ℂ := ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * γ
  have harg : (1 / 2 : ℂ) - Complex.I * ((γ : ℂ) + Complex.I * (σ : ℂ)) = starRingEnd ℂ s := by
    apply Complex.ext <;> simp [s]
  have hres_im : (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im =
      (deriv riemannXi s / riemannXi s).re := by
    dsimp [xiResolvent]
    rw [harg, deriv_riemannXi_conj, riemannXi_conj, ← map_div₀, Complex.mul_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.conj_re]
  refine ⟨hres_im, ?_⟩
  have hV_eq : xiNormSq σ γ = ‖riemannXi s‖ ^ 2 := by
    dsimp [xiNormSq, s]; rw [complex_mk_eq_add_I]
  have hVpos : 0 < xiNormSq σ γ := by
    rw [hV_eq]; exact sq_pos_of_pos (norm_pos_iff.mpr hxi)
  rw [xiLogForce_eq_force_div_normSq hVpos, deriv_xiNormSq_eq_two_re_mul_conj, hres_im, hV_eq]
  rw [Complex.sq_norm]
  have hdiv : (deriv riemannXi s / riemannXi s).re =
      (deriv riemannXi s * starRingEnd ℂ (riemannXi s)).re / Complex.normSq (riemannXi s) := by
    rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  rw [hdiv]; ring

/-- THEOREM II.2 (EXACT CAUCHY-RIEMANN PHASE-MONOTONICITY LAW):
    For any real `C^1` polar representation `ξ(1/2 + σ + iγ) = r(γ) * exp(i * Θ(γ))`
    around a point `(σ, γ)` with `r(γ) > 0`, the vertical phase velocity `Θ'(γ)` equals
    identically `Im(R_ξ(γ + iσ)) = (1/2) * ∂_σ log V(σ, γ)`. -/
theorem xiResolvent_im_eq_phase_deriv_gamma {σ γ : ℝ} {r Θ : ℝ → ℝ} {r' Θ' : ℝ}
    (hr_pos : 0 < r γ) (hr : HasDerivAt r r' γ) (hΘ : HasDerivAt Θ Θ' γ)
    (hpol : ∀ y : ℝ, riemannXi ((1 / 2 + σ : ℝ) + Complex.I * y) =
      (r y : ℂ) * Complex.exp (Complex.I * (Θ y : ℂ))) :
    Θ' = (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  let s : ℂ := ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * γ
  have hxi_ne : riemannXi s ≠ 0 := by
    rw [hpol γ]
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hr_pos) (Complex.exp_ne_zero _)
  have hd_lhs : HasDerivAt (fun y : ℝ => riemannXi ((1 / 2 + σ : ℝ) + Complex.I * y))
      (Complex.I * deriv riemannXi s) γ := by
    have hlin : HasDerivAt (fun y : ℝ => ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * y) Complex.I γ := by
      have hc : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) Complex.I γ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := γ)).const_mul Complex.I
      exact hc.const_add ((1 / 2 + σ : ℝ) : ℂ)
    have h1 := (riemannXi_entire.differentiableAt (x := s)).hasDerivAt.scomp γ hlin
    simpa [s, Function.comp_def, smul_eq_mul] using h1
  have hd_rhs : HasDerivAt (fun y : ℝ => (r y : ℂ) * Complex.exp (Complex.I * (Θ y : ℂ)))
      ((r' : ℂ) * Complex.exp (Complex.I * (Θ γ : ℂ)) +
        (r γ : ℂ) * (Complex.I * (Θ' : ℂ) * Complex.exp (Complex.I * (Θ γ : ℂ)))) γ := by
    have hrC : HasDerivAt (fun y : ℝ => (r y : ℂ)) (r' : ℂ) γ :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt γ hr
    have hΘC : HasDerivAt (fun y : ℝ => Complex.I * (Θ y : ℂ)) (Complex.I * (Θ' : ℂ)) γ :=
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt γ hΘ).const_mul Complex.I
    have hexpC : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (Θ y : ℂ)))
        ((Complex.I * (Θ' : ℂ)) * Complex.exp (Complex.I * (Θ γ : ℂ))) γ := by
      have h1 := (Complex.hasDerivAt_exp (Complex.I * (Θ γ : ℂ))).scomp γ hΘC
      simpa [Function.comp_def, smul_eq_mul] using h1
    convert hrC.fun_mul hexpC using 1
  have hfun_eq : (fun y : ℝ => riemannXi ((1 / 2 + σ : ℝ) + Complex.I * y)) =
      fun y : ℝ => (r y : ℂ) * Complex.exp (Complex.I * (Θ y : ℂ)) := funext hpol
  rw [hfun_eq] at hd_lhs
  have hEq := hd_lhs.unique hd_rhs
  have hdiv : Complex.I * (deriv riemannXi s / riemannXi s) = (r' / r γ : ℂ) + Complex.I * (Θ' : ℂ) := by
    have h1 : Complex.I * deriv riemannXi s / riemannXi s =
        ((r' : ℂ) * Complex.exp (Complex.I * (Θ γ : ℂ)) +
          (r γ : ℂ) * (Complex.I * (Θ' : ℂ) * Complex.exp (Complex.I * (Θ γ : ℂ)))) /
        ((r γ : ℂ) * Complex.exp (Complex.I * (Θ γ : ℂ))) := by
      rw [hEq, hpol γ]
    have hrne : (r γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr_pos
    have hene : Complex.exp (Complex.I * (Θ γ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    rw [mul_div_assoc] at h1
    rw [h1]
    field_simp [hrne, hene]
  have him := congrArg Complex.im hdiv
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at him
  have hdiv_im : ((r' : ℂ) / (r γ : ℂ)).im = 0 := by
    rw [← Complex.ofReal_div, Complex.ofReal_im]
  rw [hdiv_im, zero_add] at him
  rw [(xiResolvent_im_eq_logForce_half hxi_ne).1]
  exact him.symm

/-- Global Herglotz Positivity of the Spectral Resolvent on the upper half-strip `0 < σ < 1/2`. -/
def XiResolventHerglotz : Prop :=
  ∀ σ γ : ℝ, 0 < σ → σ < 1 / 2 →
    riemannXi ((1 / 2 + σ : ℝ) + Complex.I * γ) ≠ 0 ∧
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im

/-- THEOREM II.3 (Unconditional Herglotz-Resolvent Reduction to Mathlib4's `RiemannHypothesis`):
    If `R_ξ(γ + iσ)` is analytic with strictly positive imaginary part on `0 < σ < 1/2`,
    then Mathlib4's official `RiemannHypothesis` holds! -/
theorem riemannHypothesis_of_xiResolventHerglotz (hH : XiResolventHerglotz) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiLogForcePos
  intro σ γ hσ0 hσ1
  obtain ⟨hxi, him⟩ := hH σ γ hσ0 hσ1
  have hV : 0 < xiNormSq σ γ := by
    dsimp [xiNormSq]; rw [complex_mk_eq_add_I]; exact sq_pos_of_pos (norm_pos_iff.mpr hxi)
  have hlog := (xiResolvent_im_eq_logForce_half hxi).2
  exact ⟨hV, by linarith⟩

/-- Finite critical-line spectral resolvent `G(z) = ∑_{m ∈ S} w_m / (γ_m - z)` and its derivative. -/
noncomputable def resolventCritSum {ι : Type*} (S : Finset ι) (w γ : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ m ∈ S, (w m : ℂ) / ((γ m : ℂ) - z)

noncomputable def resolventCritSumDeriv {ι : Type*} (S : Finset ι) (w γ : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ m ∈ S, (w m : ℂ) / ((γ m : ℂ) - z) ^ 2

/-- THEOREM II.4 (Exact Herglotz Positivity & Schwarz-Pick Hyperbolic Contraction for Critical Poles):
    For any finite family of real critical-line poles `{γ_m}_{m ∈ S}` with `w_m > 0`,
    and every `z ∈ ℂ` in the upper half-plane (`0 < z.im`):
    (1) `Im(G(z)) = ∑_{m ∈ S} w_m * z.im / ((γ_m - z.re)^2 + z.im^2) > 0` (whenever `S.Nonempty`),
    (2) Exact derivative `HasDerivAt (resolventCritSum S w γ) (resolventCritSumDeriv S w γ z) z`,
    (3) Exact Schwarz-Pick hyperbolic contraction: `z.im * ‖G'(z)‖ ≤ Im(G(z))`! -/
theorem resolventCritSum_herglotz_and_schwarzPick {ι : Type*} (S : Finset ι) (w γ : ι → ℝ)
    (hw : ∀ m ∈ S, 0 < w m) {z : ℂ} (hz : 0 < z.im) :
    (resolventCritSum S w γ z).im =
      ∑ m ∈ S, w m * z.im / ((γ m - z.re) ^ 2 + z.im ^ 2) ∧
    (S.Nonempty → 0 < (resolventCritSum S w γ z).im) ∧
    HasDerivAt (resolventCritSum S w γ) (resolventCritSumDeriv S w γ z) z ∧
    z.im * ‖resolventCritSumDeriv S w γ z‖ ≤ (resolventCritSum S w γ z).im := by
  have hterm_im : ∀ m : ι, ((w m : ℂ) / ((γ m : ℂ) - z)).im =
      w m * z.im / ((γ m - z.re) ^ 2 + z.im ^ 2) := by
    intro m
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.normSq_apply, zero_mul, zero_sub]
    ring
  have him_eq : (resolventCritSum S w γ z).im =
      ∑ m ∈ S, w m * z.im / ((γ m - z.re) ^ 2 + z.im ^ 2) := by
    dsimp [resolventCritSum]
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun m _ => hterm_im m
  have him_pos : S.Nonempty → 0 < (resolventCritSum S w γ z).im := by
    intro hne
    rw [him_eq]
    exact Finset.sum_pos (fun m hm => div_pos (mul_pos (hw m hm) hz) (by positivity)) hne
  have hderiv : HasDerivAt (resolventCritSum S w γ) (resolventCritSumDeriv S w γ z) z := by
    dsimp [resolventCritSum, resolventCritSumDeriv]
    refine HasDerivAt.fun_sum fun m _ => ?_
    have hne : (γ m : ℂ) - z ≠ 0 := by
      intro h0
      have hi := congrArg Complex.im h0
      simp at hi; linarith
    have hsub : HasDerivAt (fun u : ℂ => (γ m : ℂ) - u) (-1) z := by
      simpa using (hasDerivAt_const z (γ m : ℂ)).fun_sub (hasDerivAt_id z)
    have hdiv := (hasDerivAt_const z (w m : ℂ)).fun_div hsub hne
    convert hdiv using 1; ring
  have hsp : z.im * ‖resolventCritSumDeriv S w γ z‖ ≤ (resolventCritSum S w γ z).im := by
    rw [him_eq]
    dsimp [resolventCritSumDeriv]
    have htri : ‖∑ m ∈ S, (w m : ℂ) / ((γ m : ℂ) - z) ^ 2‖ ≤
        ∑ m ∈ S, ‖(w m : ℂ) / ((γ m : ℂ) - z) ^ 2‖ := norm_sum_le _ _
    have hmul := mul_le_mul_of_nonneg_left htri (le_of_lt hz)
    rw [Finset.mul_sum] at hmul
    refine hmul.trans (Finset.sum_le_sum fun m hm => ?_)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (hw m hm)),
        norm_pow, Complex.sq_norm]
    have hns : Complex.normSq ((γ m : ℂ) - z) = (γ m - z.re) ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq_apply, sq]
    rw [hns]; ring_nf; exact le_rfl
  exact ⟨him_eq, him_pos, hderiv, hsp⟩

/-- THEOREM II.5 (ALL-ORDER PICK-NEVANLINNA MATRIX POSITIVE SEMI-DEFINITENESS FOR CRITICAL POLES):
    For EVERY finite set of critical-line poles `{γ_m}_{m ∈ S}` (`w_m ≥ 0`), EVERY finite set of
    upper half-plane sample points `{z_j}_{j ∈ I}` (`Im(z_j) > 0`), and EVERY vector `c : I → ℂ`,
    the Hermitian Pick quadratic form is an exact sum of squares:
      `Re ∑_{j,k ∈ I} c_j * conj(c_k) * (G(z_j) - conj(G(z_k))) / (z_j - conj(z_k))
         = ∑_{m ∈ S} w_m * ‖∑_{j ∈ I} c_j / (γ_m - z_j)‖^2 ≥ 0`! -/
theorem resolventCritSum_pickMatrix_psd {ι κ : Type*} (S : Finset ι) (I : Finset κ)
    (w γ : ι → ℝ) (hw : ∀ m ∈ S, 0 ≤ w m)
    (z : κ → ℂ) (hz : ∀ j ∈ I, 0 < (z j).im) (c : κ → ℂ) :
    (∑ j ∈ I, ∑ k ∈ I, c j * starRingEnd ℂ (c k) *
      ((resolventCritSum S w γ (z j) - starRingEnd ℂ (resolventCritSum S w γ (z k))) /
        (z j - starRingEnd ℂ (z k)))).re =
      ∑ m ∈ S, w m * ‖∑ j ∈ I, c j / ((γ m : ℂ) - z j)‖ ^ 2 ∧
    0 ≤ (∑ j ∈ I, ∑ k ∈ I, c j * starRingEnd ℂ (c k) *
      ((resolventCritSum S w γ (z j) - starRingEnd ℂ (resolventCritSum S w γ (z k))) /
        (z j - starRingEnd ℂ (z k)))).re := by
  have hsingle : ∀ m : ι, ∀ j ∈ I, ∀ k ∈ I,
      ((w m : ℂ) / ((γ m : ℂ) - z j) - starRingEnd ℂ ((w m : ℂ) / ((γ m : ℂ) - z k))) /
        (z j - starRingEnd ℂ (z k)) =
      (w m : ℂ) * (1 / ((γ m : ℂ) - z j)) * starRingEnd ℂ (1 / ((γ m : ℂ) - z k)) := by
    intro m j hj k hk
    have hzj : (γ m : ℂ) - z j ≠ 0 := fun h0 => by
      have hi := congrArg Complex.im h0; simp at hi; linarith [hz j hj]
    have hzk : (γ m : ℂ) - starRingEnd ℂ (z k) ≠ 0 := fun h0 => by
      have hi := congrArg Complex.im h0; simp at hi; linarith [hz k hk]
    have hdiff : z j - starRingEnd ℂ (z k) ≠ 0 := fun h0 => by
      have hi := congrArg Complex.im h0; simp at hi; linarith [hz j hj, hz k hk]
    simp only [map_div₀, map_sub, Complex.conj_ofReal, map_one]
    field_simp [hzj, hzk, hdiff]
    ring
  have hsum_eq : ∑ j ∈ I, ∑ k ∈ I, c j * starRingEnd ℂ (c k) *
      ((resolventCritSum S w γ (z j) - starRingEnd ℂ (resolventCritSum S w γ (z k))) /
        (z j - starRingEnd ℂ (z k))) =
      ∑ m ∈ S, (w m : ℂ) *
        ((∑ j ∈ I, c j / ((γ m : ℂ) - z j)) * starRingEnd ℂ (∑ k ∈ I, c k / ((γ m : ℂ) - z k))) := by
    have hstep1 : ∀ j ∈ I, ∀ k ∈ I,
        c j * starRingEnd ℂ (c k) *
          ((resolventCritSum S w γ (z j) - starRingEnd ℂ (resolventCritSum S w γ (z k))) /
            (z j - starRingEnd ℂ (z k))) =
        ∑ m ∈ S, (w m : ℂ) *
          ((c j / ((γ m : ℂ) - z j)) * starRingEnd ℂ (c k / ((γ m : ℂ) - z k))) := by
      intro j hj k hk
      dsimp [resolventCritSum]
      rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsingle m j hj k hk]
      simp only [div_eq_mul_inv, map_mul, map_inv₀, one_mul]
      ring
    calc ∑ j ∈ I, ∑ k ∈ I, c j * starRingEnd ℂ (c k) *
            ((resolventCritSum S w γ (z j) - starRingEnd ℂ (resolventCritSum S w γ (z k))) /
              (z j - starRingEnd ℂ (z k)))
      _ = ∑ j ∈ I, ∑ k ∈ I, ∑ m ∈ S, (w m : ℂ) *
            ((c j / ((γ m : ℂ) - z j)) * starRingEnd ℂ (c k / ((γ m : ℂ) - z k))) :=
          Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hstep1 j hj k hk
      _ = ∑ j ∈ I, ∑ m ∈ S, ∑ k ∈ I, (w m : ℂ) *
            ((c j / ((γ m : ℂ) - z j)) * starRingEnd ℂ (c k / ((γ m : ℂ) - z k))) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ m ∈ S, ∑ j ∈ I, ∑ k ∈ I, (w m : ℂ) *
            ((c j / ((γ m : ℂ) - z j)) * starRingEnd ℂ (c k / ((γ m : ℂ) - z k))) :=
          Finset.sum_comm
      _ = ∑ m ∈ S, (w m : ℂ) *
            ((∑ j ∈ I, c j / ((γ m : ℂ) - z j)) * starRingEnd ℂ (∑ k ∈ I, c k / ((γ m : ℂ) - z k))) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_sum, Finset.sum_mul]
          simp only [Finset.mul_sum]
  have hre : (∑ j ∈ I, ∑ k ∈ I, c j * starRingEnd ℂ (c k) *
      ((resolventCritSum S w γ (z j) - starRingEnd ℂ (resolventCritSum S w γ (z k))) /
        (z j - starRingEnd ℂ (z k)))).re =
      ∑ m ∈ S, w m * ‖∑ j ∈ I, c j / ((γ m : ℂ) - z j)‖ ^ 2 := by
    rw [hsum_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set u : ℂ := ∑ j ∈ I, c j / ((γ m : ℂ) - z j)
    have hu : u * starRingEnd ℂ u = (Complex.normSq u : ℂ) := Complex.mul_conj u
    rw [hu, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.sq_norm]
  refine ⟨hre, ?_⟩
  rw [hre]
  exact Finset.sum_nonneg fun m hm => mul_nonneg (hw m hm) (sq_nonneg _)

/-- Auxiliary: Exact Poisson-kernel integral `(1/π) ∫_{-∞}^{∞} σ / ((γ - γ₀)^2 + σ^2) dγ = 1`. -/
private lemma integral_poisson_kernel_eq_pi {σ γ0 : ℝ} (hσ : 0 < σ) :
    ∫ γ : ℝ, σ / ((γ - γ0) ^ 2 + σ ^ 2) = Real.pi := by
  let f : ℝ → ℝ := fun γ => Real.arctan ((γ - γ0) / σ)
  let f' : ℝ → ℝ := fun γ => σ / ((γ - γ0) ^ 2 + σ ^ 2)
  have hderiv : ∀ γ : ℝ, HasDerivAt f (f' γ) γ := by
    intro γ
    have hlin : HasDerivAt (fun x : ℝ => (x - γ0) / σ) (1 / σ) γ := by
      have := ((hasDerivAt_id γ).sub_const γ0).div_const σ
      simpa using this
    refine ((Real.hasDerivAt_arctan ((γ - γ0) / σ)).comp γ hlin).congr_deriv ?_
    dsimp [f']
    have hσne : σ ≠ 0 := ne_of_gt hσ
    have hden : (γ - γ0) ^ 2 + σ ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hσne, hden]; ring
  have hlin_top : Filter.Tendsto (fun γ : ℝ => (γ - γ0) / σ) atTop atTop :=
    (Filter.tendsto_id.atTop_add tendsto_const_nhds).atTop_div_const hσ
  have hlin_bot : Filter.Tendsto (fun γ : ℝ => (γ - γ0) / σ) atBot atBot :=
    (Filter.tendsto_id.atBot_add tendsto_const_nhds).atBot_div_const hσ
  have htop : Filter.Tendsto f atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hlin_top
  have hbot : Filter.Tendsto f atBot (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hlin_bot
  have hf'_nn : ∀ γ : ℝ, 0 ≤ f' γ := fun γ => by dsimp [f']; positivity
  have hint_pos : IntegrableOn f' (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hderiv x) (fun x _ => hf'_nn x) htop
  have hint_neg : IntegrableOn f' (Iic 0) := by
    let g : ℝ → ℝ := fun x => -f (-x)
    let g' : ℝ → ℝ := fun x => f' (-x)
    have hg_deriv : ∀ x : ℝ, HasDerivAt g (g' x) x := by
      intro x
      have h1 : HasDerivAt (fun t : ℝ => f (-t)) (f' (-x) * (-1)) x :=
        (hderiv (-x)).comp x (hasDerivAt_neg x)
      simpa [g, g'] using h1.fun_neg
    have hg_top : Filter.Tendsto g atTop (𝓝 (Real.pi / 2)) := by
      have hneg_top : Filter.Tendsto (fun x : ℝ => -x) atTop atBot := Filter.tendsto_neg_atTop_atBot
      have := (hbot.comp hneg_top).neg
      simpa [g] using this
    have hint_g : IntegrableOn g' (Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hg_deriv x) (fun x _ => hf'_nn (-x)) hg_top
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (f := f') (s := Iio 0) (MeasurableEquiv.neg ℝ).measurableEmbedding
    have hIio : IntegrableOn f' (Iio 0) := by
      rw [← hmp]
      have hpre' : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by ext x; simp
      rw [hpre']; exact hint_g
    have hEq : Iic (0 : ℝ) = Iio 0 ∪ {0} := Iio_union_right.symm
    rw [hEq]; exact hIio.union (integrableOn_singleton (hx := by simp))
  have hf'_int : Integrable f' := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hint_neg.union hint_pos
  have hval := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hf'_int hbot htop
  dsimp [f'] at hval
  linarith

/-- THEOREM II.6 (EXACT STIELTJES-PERRON IDOS INTEGRAL FOR CRITICAL RESOLVENTS):
    For EVERY finite set of critical-line poles `{γ_m}_{m ∈ S}` with weights `w_m`,
    and EVERY positive height `σ > 0`, the integrated resolvent density recovers the exact
    total spectral weight (independent of `σ > 0`):
      `(1 / π) * ∫_{-∞}^{∞} Im(G(γ + iσ)) dγ = ∑_{m ∈ S} w_m`. -/
theorem resolventCritSum_idos_integral {ι : Type*} [DecidableEq ι] (S : Finset ι) (w γ : ι → ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    (1 / Real.pi) * ∫ x : ℝ, (resolventCritSum S w γ ((x : ℂ) + Complex.I * (σ : ℂ))).im =
      ∑ m ∈ S, w m := by
  have hrew : (fun x : ℝ => (resolventCritSum S w γ ((x : ℂ) + Complex.I * (σ : ℂ))).im) =
      fun x : ℝ => ∑ m ∈ S, w m * (σ / ((x - γ m) ^ 2 + σ ^ 2)) := by
    ext x
    dsimp [resolventCritSum]
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.normSq_apply,
      zero_mul, one_mul, mul_zero, sub_zero, zero_add, add_zero, zero_sub]
    ring
  rw [hrew]
  have hint_m : ∀ m : ι, Integrable (fun x : ℝ => w m * (σ / ((x - γ m) ^ 2 + σ ^ 2))) := by
    intro m
    have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.arctan ((t - γ m) / σ))
        (σ / ((x - γ m) ^ 2 + σ ^ 2)) x := by
      intro x
      have hlin : HasDerivAt (fun t : ℝ => (t - γ m) / σ) (1 / σ) x := by
        simpa using ((hasDerivAt_id x).sub_const (γ m)).div_const σ
      refine ((Real.hasDerivAt_arctan ((x - γ m) / σ)).comp x hlin).congr_deriv ?_
      have hσne : σ ≠ 0 := ne_of_gt hσ
      have hden : (x - γ m) ^ 2 + σ ^ 2 ≠ 0 := ne_of_gt (by positivity)
      field_simp [hσne, hden]; ring
    have hlin_top : Filter.Tendsto (fun x : ℝ => (x - γ m) / σ) atTop atTop :=
      (Filter.tendsto_id.atTop_add tendsto_const_nhds).atTop_div_const hσ
    have hlin_bot : Filter.Tendsto (fun x : ℝ => (x - γ m) / σ) atBot atBot :=
      (Filter.tendsto_id.atBot_add tendsto_const_nhds).atBot_div_const hσ
    have htop : Filter.Tendsto (fun t : ℝ => Real.arctan ((t - γ m) / σ)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hlin_top
    have hbot : Filter.Tendsto (fun t : ℝ => Real.arctan ((t - γ m) / σ)) atBot (𝓝 (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hlin_bot
    have hpos : IntegrableOn (fun x : ℝ => σ / ((x - γ m) ^ 2 + σ ^ 2)) (Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hderiv x) (fun x _ => by positivity) htop
    have hneg : IntegrableOn (fun x : ℝ => σ / ((x - γ m) ^ 2 + σ ^ 2)) (Iic 0) := by
      have hg_d : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -Real.arctan ((-t - γ m) / σ))
          (σ / ((-x - γ m) ^ 2 + σ ^ 2)) x := by
        intro x
        have h1 : HasDerivAt (fun t : ℝ => Real.arctan ((-t - γ m) / σ))
            ((σ / ((-x - γ m) ^ 2 + σ ^ 2)) * (-1)) x :=
          (hderiv (-x)).comp x (hasDerivAt_neg x)
        simpa using h1.fun_neg
      have hg_top : Filter.Tendsto (fun t : ℝ => -Real.arctan ((-t - γ m) / σ)) atTop (𝓝 (Real.pi / 2)) := by
        simpa using (hbot.comp Filter.tendsto_neg_atTop_atBot).neg
      have hg_int : IntegrableOn (fun x : ℝ => σ / ((-x - γ m) ^ 2 + σ ^ 2)) (Ioi 0) :=
        integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hg_d x) (fun x _ => by positivity) hg_top
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (f := fun x : ℝ => σ / ((x - γ m) ^ 2 + σ ^ 2)) (s := Iio 0)
        (MeasurableEquiv.neg ℝ).measurableEmbedding
      have hIio : IntegrableOn (fun x : ℝ => σ / ((x - γ m) ^ 2 + σ ^ 2)) (Iio 0) := by
        rw [← hmp]
        have hpre : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by ext x; simp
        rw [hpre]; exact hg_int
      have hEq : Iic (0 : ℝ) = Iio 0 ∪ {0} := Iio_union_right.symm
      rw [hEq]; exact hIio.union (integrableOn_singleton (hx := by simp))
    have hbase : Integrable (fun x : ℝ => σ / ((x - γ m) ^ 2 + σ ^ 2)) := by
      rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
      exact hneg.union hpos
    exact hbase.const_mul (w m)
  rw [integral_sum_finset_real (fun m _ => hint_m m)]
  have hsum_pi : ∑ m ∈ S, ∫ x : ℝ, w m * (σ / ((x - γ m) ^ 2 + σ ^ 2)) =
      (∑ m ∈ S, w m) * Real.pi := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MeasureTheory.integral_const_mul, integral_poisson_kernel_eq_pi hσ]
  rw [hsum_pi]
  field_simp [ne_of_gt Real.pi_pos]

/-- Symmetric off-line zero pair resolvent `G_off(z) = 1/((γ₀ - iδ) - z) + 1/((γ₀ + iδ) - z)`
    (corresponding to the functional-equation pair `1/2 ± δ + iγ₀` with `δ > 0`),
    and its exact complex derivative `G_off'(z)`. -/
noncomputable def resolventOfflinePair (γ0 δ : ℝ) (z : ℂ) : ℂ :=
  1 / (((γ0 : ℂ) - Complex.I * (δ : ℂ)) - z) + 1 / (((γ0 : ℂ) + Complex.I * (δ : ℂ)) - z)

noncomputable def resolventOfflinePairDeriv (γ0 δ : ℝ) (z : ℂ) : ℂ :=
  1 / (((γ0 : ℂ) - Complex.I * (δ : ℂ)) - z) ^ 2 + 1 / (((γ0 : ℂ) + Complex.I * (δ : ℂ)) - z) ^ 2

/-- THEOREM II.7 (EXACT OFF-LINE ZERO PAIR VIOLATION — BOTH INSIDE `0 < σ < δ` AND REMOTELY
    FOR EVERY `σ > δ`, EVEN IN THE EULER-PRODUCT HALF-PLANE `Re(s) > 1`!):
    For any symmetric off-line pair `1/2 ± δ + iγ₀` (`δ > 0`) evaluated at `z = γ₀ + iσ` (`σ > 0`, `σ ≠ δ`):
    (1) Exact closed form: `Im(G_off(γ₀ + iσ)) = 2σ / (σ^2 - δ^2)`.
    (2) Inside (`0 < σ < δ`): `Im(G_off(γ₀ + iσ)) < 0` (violates Herglotz positivity!).
    (3) Outside (EVERY `σ > δ` — arbitrarily far from the critical line!):
        `0 < Im(G_off(γ₀ + iσ))`, YET `G_off` strictly violates Schwarz-Pick hyperbolic
        contraction with the exact ratio:
          `σ * ‖G_off'(γ₀ + iσ)‖ = ((σ^2 + δ^2) / (σ^2 - δ^2)) * Im(G_off(γ₀ + iσ)) > Im(G_off(γ₀ + iσ))`! -/
theorem resolventOfflinePair_exact_and_remote_violation {γ0 δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hne : σ ≠ δ) :
    let z : ℂ := (γ0 : ℂ) + Complex.I * (σ : ℂ)
    (resolventOfflinePair γ0 δ z).im = 2 * σ / (σ ^ 2 - δ ^ 2) ∧
    (σ < δ → (resolventOfflinePair γ0 δ z).im < 0) ∧
    (δ < σ →
      HasDerivAt (resolventOfflinePair γ0 δ) (resolventOfflinePairDeriv γ0 δ z) z ∧
      0 < (resolventOfflinePair γ0 δ z).im ∧
      σ * ‖resolventOfflinePairDeriv γ0 δ z‖ =
        ((σ ^ 2 + δ ^ 2) / (σ ^ 2 - δ ^ 2)) * (resolventOfflinePair γ0 δ z).im ∧
      (resolventOfflinePair γ0 δ z).im < σ * ‖resolventOfflinePairDeriv γ0 δ z‖) := by
  intro z
  have h1 : ((γ0 : ℂ) - Complex.I * (δ : ℂ)) - z = -Complex.I * ((σ : ℂ) + (δ : ℂ)) := by
    dsimp [z]; ring
  have h2 : ((γ0 : ℂ) + Complex.I * (δ : ℂ)) - z = -Complex.I * ((σ : ℂ) - (δ : ℂ)) := by
    dsimp [z]; ring
  have hne_p : (σ : ℂ) + (δ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]; exact_mod_cast ne_of_gt (by linarith : 0 < σ + δ)
  have hne_m : (σ : ℂ) - (δ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hne
  have hne_I : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have hsq_ne : (σ : ℂ) ^ 2 - (δ : ℂ) ^ 2 ≠ 0 := by
    have hfac : (σ : ℂ) ^ 2 - (δ : ℂ) ^ 2 = ((σ : ℂ) - (δ : ℂ)) * ((σ : ℂ) + (δ : ℂ)) := by ring
    rw [hfac]; exact mul_ne_zero hne_m hne_p
  have hval : resolventOfflinePair γ0 δ z = Complex.I * (((2 * σ / (σ ^ 2 - δ ^ 2) : ℝ) : ℂ)) := by
    dsimp [resolventOfflinePair]
    rw [h1, h2]
    push_cast
    field_simp [hne_p, hne_m, hne_I, hsq_ne]
    ring_nf
    simp [Complex.I_sq]
    ring
  have him_eq : (resolventOfflinePair γ0 δ z).im = 2 * σ / (σ ^ 2 - δ ^ 2) := by
    rw [hval, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  refine ⟨him_eq, ?_, ?_⟩
  · intro hlt
    rw [him_eq]
    have hden_neg : σ ^ 2 - δ ^ 2 < 0 := by nlinarith
    exact div_neg_of_pos_of_neg (by linarith) hden_neg
  · intro hgt
    have hden_pos : 0 < σ ^ 2 - δ ^ 2 := by nlinarith
    have him_pos : 0 < (resolventOfflinePair γ0 δ z).im := by
      rw [him_eq]; exact div_pos (by linarith) hden_pos
    have hderiv : HasDerivAt (resolventOfflinePair γ0 δ) (resolventOfflinePairDeriv γ0 δ z) z := by
      dsimp [resolventOfflinePair, resolventOfflinePairDeriv]
      have hd1 : HasDerivAt (fun u : ℂ => 1 / (((γ0 : ℂ) - Complex.I * (δ : ℂ)) - u))
          (1 / (((γ0 : ℂ) - Complex.I * (δ : ℂ)) - z) ^ 2) z := by
        have hsub : HasDerivAt (fun u : ℂ => ((γ0 : ℂ) - Complex.I * (δ : ℂ)) - u) (-1) z := by
          simpa using (hasDerivAt_const z _).fun_sub (hasDerivAt_id z)
        have hnz : ((γ0 : ℂ) - Complex.I * (δ : ℂ)) - z ≠ 0 := by
          rw [h1]; exact mul_ne_zero hne_I hne_p
        convert (hasDerivAt_const z (1 : ℂ)).fun_div hsub hnz using 1; ring
      have hd2 : HasDerivAt (fun u : ℂ => 1 / (((γ0 : ℂ) + Complex.I * (δ : ℂ)) - u))
          (1 / (((γ0 : ℂ) + Complex.I * (δ : ℂ)) - z) ^ 2) z := by
        have hsub : HasDerivAt (fun u : ℂ => ((γ0 : ℂ) + Complex.I * (δ : ℂ)) - u) (-1) z := by
          simpa using (hasDerivAt_const z _).fun_sub (hasDerivAt_id z)
        have hnz : ((γ0 : ℂ) + Complex.I * (δ : ℂ)) - z ≠ 0 := by
          rw [h2]; exact mul_ne_zero hne_I hne_m
        convert (hasDerivAt_const z (1 : ℂ)).fun_div hsub hnz using 1; ring
      exact hd1.fun_add hd2
    have hd_val : resolventOfflinePairDeriv γ0 δ z =
        ((-(2 * (σ ^ 2 + δ ^ 2) / (σ ^ 2 - δ ^ 2) ^ 2) : ℝ) : ℂ) := by
      dsimp [resolventOfflinePairDeriv]
      rw [h1, h2]
      push_cast
      have hI2 : (-Complex.I) ^ 2 = (-1 : ℂ) := by ring_nf; exact Complex.I_sq
      rw [mul_pow, mul_pow, hI2]
      field_simp [hne_p, hne_m, hsq_ne]
      ring
    have hnorm_d : ‖resolventOfflinePairDeriv γ0 δ z‖ = 2 * (σ ^ 2 + δ ^ 2) / (σ ^ 2 - δ ^ 2) ^ 2 := by
      rw [hd_val, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    have hratio : σ * ‖resolventOfflinePairDeriv γ0 δ z‖ =
        ((σ ^ 2 + δ ^ 2) / (σ ^ 2 - δ ^ 2)) * (resolventOfflinePair γ0 δ z).im := by
      rw [hnorm_d, him_eq]
      have hden_ne : σ ^ 2 - δ ^ 2 ≠ 0 := ne_of_gt hden_pos
      field_simp [hden_ne]
    have hgt1 : 1 < (σ ^ 2 + δ ^ 2) / (σ ^ 2 - δ ^ 2) := by
      rw [one_lt_div hden_pos]; nlinarith
    have hviol : (resolventOfflinePair γ0 δ z).im < σ * ‖resolventOfflinePairDeriv γ0 δ z‖ := by
      rw [hratio]
      have := mul_lt_mul_of_pos_right hgt1 him_pos
      linarith
    exact ⟨hderiv, him_pos, hratio, hviol⟩

-- ==============================================================================
-- PART III: ROUTE B — ALL-ORDER LIGHT-CONE PARITY, LOCAL RH + SIMPLICITY,
--           AND COMPACTIFIED ANGULAR STRIP COORDINATE β = cos^2(θ/2)
-- ==============================================================================

/-- THEOREM III.1 (EXACT ALL-ORDER 2D LIGHT-CONE PARITY SEPARATION IDENTITY):
    For EVERY Taylor order `2k` (`k : ℕ`) and ALL `u, v, σ : ℝ`, the 2D light-cone
    kernel splits cleanly into a `v`-even polynomial times `cosh(σu)cosh(σv)` plus
    a `v`-odd polynomial times `sinh(σu)sinh(σv)` (which vanishes identically at `σ = 0`):
      `(u+v)^2*(u-v)^{2k}*cosh(σ(u+v)) + (u-v)^2*(u+v)^{2k}*cosh(σ(u-v))
        = P_even(u, v) * cosh(σu)*cosh(σv) + P_odd(u, v) * sinh(σu)*sinh(σv)`,
    with `P_even(u, -v) = P_even(u, v)` and `P_odd(u, -v) = -P_odd(u, v)`! -/
theorem lightCone_even_power_parity_identity (k : ℕ) (u v σ : ℝ) :
    let P_even : ℝ → ℝ → ℝ := fun a b => (a + b) ^ 2 * (a - b) ^ (2 * k) + (a - b) ^ 2 * (a + b) ^ (2 * k)
    let P_odd  : ℝ → ℝ → ℝ := fun a b => (a + b) ^ 2 * (a - b) ^ (2 * k) - (a - b) ^ 2 * (a + b) ^ (2 * k)
    (u + v) ^ 2 * (u - v) ^ (2 * k) * Real.cosh (σ * (u + v)) +
      (u - v) ^ 2 * (u + v) ^ (2 * k) * Real.cosh (σ * (u - v)) =
      P_even u v * (Real.cosh (σ * u) * Real.cosh (σ * v)) +
        P_odd u v * (Real.sinh (σ * u) * Real.sinh (σ * v)) ∧
    P_even u (-v) = P_even u v ∧
    P_odd u (-v) = -P_odd u v := by
  intro P_even P_odd
  have hch_add : Real.cosh (σ * (u + v)) =
      Real.cosh (σ * u) * Real.cosh (σ * v) + Real.sinh (σ * u) * Real.sinh (σ * v) := by
    rw [mul_add, Real.cosh_add]
  have hch_sub : Real.cosh (σ * (u - v)) =
      Real.cosh (σ * u) * Real.cosh (σ * v) - Real.sinh (σ * u) * Real.sinh (σ * v) := by
    rw [mul_sub, Real.cosh_sub]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [P_even, P_odd]; rw [hch_add, hch_sub]; ring
  · dsimp [P_even]; ring
  · dsimp [P_odd]; ring

/-- THEOREM III.2 (LOCAL RIEMANN HYPOTHESIS + ZERO SIMPLICITY FROM FINITE-HEIGHT HESSIAN POSITIVITY):
    For ANY height `Γ ≥ 0` (INCLUDING heights `Γ > γ₁ = 14.1347, γ₂ = 21.0220, ...` crossing
    critical-line zeros!), if the transverse Hessian `∂_σ^2 V(σ, γ) > 0` for all `σ ∈ [0, 1/2]`
    and `|γ| ≤ Γ`, then BOTH:
    (1) **Local RH up to `Γ`**: EVERY zero of Mathlib4's `riemannZeta` in the critical strip
        `0 < s.re < 1` with `|s.im| ≤ Γ` lies strictly on the critical line `s.re = 1/2`, AND
    (2) **Zero Simplicity up to `Γ`**: EVERY critical-line zero `γ ∈ [-Γ, Γ]` (`Xi(γ) = 0`)
        is strictly simple (`deriv xiCritical γ ≠ 0`)! -/
theorem riemannHypothesis_local_and_simple_of_hessianPos {Γ : ℝ}
    (hH : ∀ σ γ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 → |γ| ≤ Γ →
      0 < deriv (fun t : ℝ => deriv (fun u : ℝ => xiNormSq u γ) t) σ) :
    (∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ Γ → riemannZeta s = 0 → s.re = 1 / 2) ∧
    (∀ γ : ℝ, |γ| ≤ Γ → xiCritical γ = 0 → deriv xiCritical γ ≠ 0) := by
  -- Step 1: From ∂_σ^2 V > 0 on [0, 1/2] and ∂_σ V(0, γ) = 0, deduce ∂_σ V > 0 on (0, 1/2]
  have hF : ∀ σ γ : ℝ, 0 < σ → σ ≤ 1 / 2 → |γ| ≤ Γ →
      0 < deriv (fun u : ℝ => xiNormSq u γ) σ := by
    intro σ γ hσ0 hσ1 hγ
    have hd : ∀ t ∈ Icc (0 : ℝ) σ,
        HasDerivAt (fun u : ℝ => deriv (fun x : ℝ => xiNormSq x γ) u)
          (deriv (fun u : ℝ => deriv (fun x : ℝ => xiNormSq x γ) u) t) t :=
      fun t _ => (hasDerivAt_xiNormSq_deriv_sigma t γ).differentiableAt.hasDerivAt
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope
      (fun u : ℝ => deriv (fun x : ℝ => xiNormSq x γ) u)
      (fun u : ℝ => deriv (fun t : ℝ => deriv (fun x : ℝ => xiNormSq x γ) t) u)
      hσ0 (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
    rw [xiNormSq_deriv_sigma_zero, sub_zero, sub_zero] at hmv
    have hhc := hH c γ (le_of_lt hc.1) (le_trans (le_of_lt hc.2) hσ1) hγ
    have hmul := mul_pos hhc hσ0
    rw [hmv, div_mul_cancel₀ _ (ne_of_gt hσ0)] at hmul
    exact hmul
  -- Step 2: Strict monotonicity V(σ, γ) > V(0, γ) ≥ 0 for all σ ∈ (0, 1/2)
  have hV_gt : ∀ σ γ : ℝ, 0 < σ → σ < 1 / 2 → |γ| ≤ Γ → 0 < xiNormSq σ γ := by
    intro σ γ hσ0 hσ1 hγ
    have hd : ∀ t ∈ Icc (0 : ℝ) σ,
        HasDerivAt (fun u : ℝ => xiNormSq u γ) (deriv (fun u : ℝ => xiNormSq u γ) t) t :=
      fun t _ => (hasDerivAt_xiNormSq_sigma t γ).differentiableAt.hasDerivAt
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope
      (fun u : ℝ => xiNormSq u γ) (fun u : ℝ => deriv (fun x : ℝ => xiNormSq x γ) u)
      hσ0 (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
    rw [sub_zero] at hmv
    have hfc := hF c γ hc.1 (le_trans (le_of_lt hc.2) (le_of_lt hσ1)) hγ
    have hmul := mul_pos hfc hσ0
    rw [hmv, div_mul_cancel₀ _ (ne_of_gt hσ0)] at hmul
    have hV0_nn : 0 ≤ xiNormSq 0 γ := sq_nonneg _
    linarith
  constructor
  · -- Part (1): Local RH up to Γ
    intro s hs0 hs1 him hzeta
    by_contra hne_half
    have hxi0 : riemannXi s = 0 := (riemannXi_eq_zero_iff_riemannZeta hs0 hs1).mpr hzeta
    set σ : ℝ := |s.re - 1 / 2|
    have hσ0 : 0 < σ := abs_pos.mpr (sub_ne_zero.mpr hne_half)
    have hσ1 : σ < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hV_pos := hV_gt σ s.im hσ0 hσ1 him
    have hV_zero : xiNormSq σ s.im = 0 := by
      rcases lt_or_gt_of_ne hne_half with hlt | hgt
      · have hσ_eq : σ = 1 / 2 - s.re := by
          dsimp [σ]; rw [abs_of_neg (by linarith)]; ring
        have harg : (⟨1 / 2 + σ, s.im⟩ : ℂ) = 1 - starRingEnd ℂ s := by
          apply Complex.ext
          · simp [hσ_eq]; ring
          · simp
        dsimp [xiNormSq]
        rw [harg, riemannXi_one_sub, riemannXi_conj, hxi0, map_zero, norm_zero, zero_pow (by norm_num)]
      · have hσ_eq : σ = s.re - 1 / 2 := by
          dsimp [σ]; rw [abs_of_pos (by linarith)]
        have harg : (⟨1 / 2 + σ, s.im⟩ : ℂ) = s := by
          apply Complex.ext <;> simp [hσ_eq]
        dsimp [xiNormSq]
        rw [harg, hxi0, norm_zero, zero_pow (by norm_num)]
    linarith
  · -- Part (2): Strict Simplicity of every critical-line zero with |γ| ≤ Γ
    intro γ hγ hXi0 hXi'0
    have hpos := hH 0 γ le_rfl (by norm_num) hγ
    rw [xiNormSq_deriv2_sigma_zero_eq_laguerre, hXi0, hXi'0] at hpos
    norm_num at hpos

/-- Compactified angular strip coordinate `β(θ) = cos^2(θ/2) = (1 + cos θ)/2`
    mapping the open angular interval `θ ∈ (0, π)` bijectively onto the critical strip `(0, 1)`,
    and its natural kinetic barrier metric `g(θ) = 1 / (2 * β(θ) * (1 - β(θ)))`. -/
def stripAngleBeta (θ : ℝ) : ℝ := (Real.cos (θ / 2)) ^ 2

def stripAngleSigma (θ : ℝ) : ℝ := (1 / 2 : ℝ) * Real.cos θ

def stripKineticBarrier (θ : ℝ) : ℝ := 1 / (2 * stripAngleBeta θ * (1 - stripAngleBeta θ))

/-- THEOREM III.3 (COMPACTIFIED ANGULAR STRIP GEOMETRY & KINETIC BARRIER MINIMUM AT `β = 1/2`):
    Under `β(θ) = cos^2(θ/2)` on `θ ∈ (0, π)`:
    (1) `β(θ) = 1/2 + (1/2) cos θ ∈ (0, 1)`,
    (2) Functional reflection `β(π - θ) = 1 - β(θ)` and `β(θ) = 1/2 ↔ θ = π/2`,
    (3) The kinetic barrier equals `2 / sin^2(θ) ≥ 2` and attains its UNIQUE global minimum `2`
        on `(0, π)` if and only if `θ = π/2` (`β = 1/2`)! -/
theorem stripAngle_geometry_and_barrier {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    stripAngleBeta θ = 1 / 2 + stripAngleSigma θ ∧
    0 < stripAngleBeta θ ∧ stripAngleBeta θ < 1 ∧
    stripAngleBeta (Real.pi - θ) = 1 - stripAngleBeta θ ∧
    (stripAngleBeta θ = 1 / 2 ↔ θ = Real.pi / 2) ∧
    stripKineticBarrier θ = 2 / (Real.sin θ) ^ 2 ∧
    2 ≤ stripKineticBarrier θ ∧
    (stripKineticBarrier θ = 2 ↔ θ = Real.pi / 2) := by
  have hcos_eq : stripAngleBeta θ = 1 / 2 + stripAngleSigma θ := by
    dsimp [stripAngleBeta, stripAngleSigma]
    have h2 := Real.cos_two_mul (θ / 2)
    have hmul : 2 * (θ / 2) = θ := by ring
    rw [hmul] at h2
    linarith
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hcos_lt1 : Real.cos θ < 1 := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hlt : (Real.cos θ) ^ 2 < 1 := by nlinarith [sq_pos_of_pos hsin_pos]
    nlinarith [sq_nonneg (1 - Real.cos θ)]
  have hcos_gt_neg1 : -1 < Real.cos θ := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hlt : (Real.cos θ) ^ 2 < 1 := by nlinarith [sq_pos_of_pos hsin_pos]
    nlinarith [sq_nonneg (1 + Real.cos θ)]
  have hβ0 : 0 < stripAngleBeta θ := by rw [hcos_eq]; dsimp [stripAngleSigma]; linarith
  have hβ1 : stripAngleBeta θ < 1 := by rw [hcos_eq]; dsimp [stripAngleSigma]; linarith
  have hrefl : stripAngleBeta (Real.pi - θ) = 1 - stripAngleBeta θ := by
    have h1 : stripAngleBeta (Real.pi - θ) = 1 / 2 + (1 / 2 : ℝ) * Real.cos (Real.pi - θ) := by
      dsimp [stripAngleBeta]
      have h2 := Real.cos_two_mul ((Real.pi - θ) / 2)
      have hmul : 2 * ((Real.pi - θ) / 2) = Real.pi - θ := by ring
      rw [hmul] at h2; linarith
    rw [h1, Real.cos_pi_sub, hcos_eq]; dsimp [stripAngleSigma]; ring
  have hhalf : stripAngleBeta θ = 1 / 2 ↔ θ = Real.pi / 2 := by
    rw [hcos_eq]; dsimp [stripAngleSigma]
    constructor
    · intro h
      have hc0 : Real.cos θ = 0 := by linarith
      have hinj := Real.strictAntiOn_cos.injOn
      exact hinj ⟨le_of_lt h0, le_of_lt hπ⟩ ⟨by positivity, by linarith [Real.pi_pos]⟩
        (by rw [hc0, Real.cos_pi_div_two])
    · intro h; rw [h, Real.cos_pi_div_two]; ring
  have hbar_eq : stripKineticBarrier θ = 2 / (Real.sin θ) ^ 2 := by
    dsimp [stripKineticBarrier]
    rw [hcos_eq]; dsimp [stripAngleSigma]
    have hprod : 2 * (1 / 2 + 1 / 2 * Real.cos θ) * (1 - (1 / 2 + 1 / 2 * Real.cos θ)) =
        (1 - (Real.cos θ) ^ 2) / 2 := by ring
    have hsq := Real.sin_sq_add_cos_sq θ
    have h1m : 1 - (Real.cos θ) ^ 2 = (Real.sin θ) ^ 2 := by linarith
    rw [hprod, h1m]
    have hsne : (Real.sin θ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hsin_pos)
    field_simp [hsne]
  have hbar_ge : 2 ≤ stripKineticBarrier θ := by
    rw [hbar_eq, le_div_iff₀ (sq_pos_of_pos hsin_pos)]
    have hsq := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg (Real.cos θ)]
  have hbar_iff : stripKineticBarrier θ = 2 ↔ θ = Real.pi / 2 := by
    rw [hbar_eq, div_eq_iff (ne_of_gt (sq_pos_of_pos hsin_pos))]
    constructor
    · intro h
      have hsq := Real.sin_sq_add_cos_sq θ
      have hc2 : (Real.cos θ) ^ 2 = 0 := by linarith
      have hc0 : Real.cos θ = 0 := sq_eq_zero_iff.mp hc2
      exact Real.strictAntiOn_cos.injOn ⟨le_of_lt h0, le_of_lt hπ⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩ (by rw [hc0, Real.cos_pi_div_two])
    · intro h; rw [h, Real.sin_pi_div_two]; ring
  exact ⟨hcos_eq, hβ0, hβ1, hrefl, hhalf, hbar_eq, hbar_ge, hbar_iff⟩

/-- THEOREM III.4 (ANGULAR DESCENT CHAIN RULE & REDUCTION TO MATHLIB4's `RiemannHypothesis`):
    Along the compactified strip `θ ↦ V((1/2) cos θ, γ)`:
    (1) Exact angular derivative: `-∂_θ V((1/2) cos θ, γ) = (1/2) sin θ * ∂_σ V((1/2) cos θ, γ)`,
    (2) Strict angular descent `-∂_θ V((1/2) cos θ, γ) > 0` for all `θ ∈ (0, π/2)` and `γ ∈ ℝ`
        implies Mathlib4's official `RiemannHypothesis` unconditionally! -/
theorem xiNormSq_angular_deriv_eq (θ γ : ℝ) :
    -deriv (fun t : ℝ => xiNormSq (stripAngleSigma t) γ) θ =
      (1 / 2 : ℝ) * Real.sin θ * deriv (fun s : ℝ => xiNormSq s γ) (stripAngleSigma θ) := by
  have hsig : HasDerivAt stripAngleSigma (-(1 / 2 : ℝ) * Real.sin θ) θ := by
    show HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.cos t) (-(1 / 2 : ℝ) * Real.sin θ) θ
    simpa [mul_neg, neg_mul] using (Real.hasDerivAt_cos θ).const_mul (1 / 2 : ℝ)
  have hV := (hasDerivAt_xiNormSq_sigma (stripAngleSigma θ) γ).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => xiNormSq (stripAngleSigma t) γ)
      (deriv (fun s : ℝ => xiNormSq s γ) (stripAngleSigma θ) * (-(1 / 2 : ℝ) * Real.sin θ)) θ :=
    hV.comp θ hsig
  rw [hcomp.deriv]; ring

theorem riemannHypothesis_of_angularDescent
    (hdesc : ∀ θ γ : ℝ, 0 < θ → θ < Real.pi / 2 →
      0 < -deriv (fun t : ℝ => xiNormSq (stripAngleSigma t) γ) θ) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiTransverseForcePos
  intro γ σ hσ
  -- Map σ ∈ (0, 1/2) to θ = arccos(2σ) ∈ (0, π/2):
  let θ : ℝ := Real.arccos (2 * σ)
  have h2σ_pos : 0 < 2 * σ := by linarith [hσ.1]
  have h2σ_lt1 : 2 * σ < 1 := by linarith [hσ.2]
  have hθ_pos : 0 < θ := Real.arccos_pos.mpr h2σ_lt1
  have hθ_lt : θ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr h2σ_pos
  have hsig_eq : stripAngleSigma θ = σ := by
    dsimp [stripAngleSigma, θ]
    rw [Real.cos_arccos (by linarith) (by linarith)]; ring
  have hd_pos := hdesc θ γ hθ_pos hθ_lt
  rw [xiNormSq_angular_deriv_eq, hsig_eq] at hd_pos
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])
  have hfac_pos : 0 < (1 / 2 : ℝ) * Real.sin θ := by positivity
  exact (mul_pos_iff_of_pos_left hfac_pos).mp hd_pos

end UniversalWeilAndHerglotzResolvent

