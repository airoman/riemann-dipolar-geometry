/-
  ==============================================================================
  MODULE #14: UNIVERSAL HOPFIELD-BOLTZMANN SOLVER LYAPUNOV THEORY, ADAPTIVE
              RESOLVENT-UNIVERSAL PRECONDITIONER, AND EXACT ALL-PRIMES
              VON MANGOLDT RESOLVENT BRIDGE (LEAN 4 + MATHLIB4)
  ==============================================================================

  Author: Mariano Martín Ramírez Tamayo
  Affiliation: Independent Researcher

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):

  PART I (EXACT ENTROPY BARRIER & BREGMAN CONVEXITY OF `tanh` / `artanh`):
    1. `tanh_abs_lt_one`, `artanh_tanh_eq`, & `tanh_artanh_eq`:
       Exact bijection between `ℝ` and `(-1, 1)` under `Real.tanh` and
       `artanh x = (1/2) * log((1 + x)/(1 - x))`.
    2. `hasDerivAt_artanh` & `hasDerivAt_binEntropy`:
       Exact derivatives `d/dx artanh(x) = 1/(1 - x^2) ≥ 1` and
       `d/dx Φ_ent(x) = artanh(x)` on `(-1, 1)`.
    3. `artanh_mul_sub_sq_ge_quartic` & `binEntropy_sub_half_sq_ge_quartic`:
       Sharp global quartic lower bounds on `(-1, 1)`:
       `x * artanh(x) - x^2 ≥ x^4 / 3` and `Φ_ent(x) - x^2 / 2 ≥ x^4 / 12`.
    4. `binEntropy_bregman_ge_half_sq`:
       Exact 1-strong convexity (Bregman divergence lower bound) on `(-1, 1)`:
       `Φ_ent(x) - Φ_ent(y) - artanh(y) * (x - y) ≥ (1/2) * (x - y)^2`.

  PART II (EXACT LYAPUNOV DESCENT & PHASE-TRANSITION THEORY OF UNIVERSAL SOLVER):
    5. `universalSolver_exact_lyapunov_descent`:
       For EVERY symmetric PSD coupling `Q` and EVERY state `s ∈ (-1, 1)^N`,
       one synchronous step `s' = tanh(Q s)` of the Universal Formula obeys:
         `L_Q(s') + (1/2)*(s' - s)^T Q (s' - s) + (1/2)*‖s' - s‖_2^2 ≤ L_Q(s)`.
       Guarantees strict monotonic Lyapunov descent and excludes period-2 cycles.
    6. `universalSolver_neg_witness_of_nonzero_fixedPoint` &
       `universalSolver_unique_zero_of_psd`:
       For shifted coupling `Q = I - (1/μ) W` (`μ > 0`), EVERY non-zero fixed point
       `s = tanh(Q s)` (`s ≠ 0`) is a zero-false-positive strict negativity witness:
         `s^T W s ≤ -(μ / 3) * ∑_i s_i^4 < 0`.
       Conversely, whenever `W ⪰ 0`, `s = 0` is the UNIQUE fixed point of `tanh(Q s)`
       and `L_Q(s) ≥ (1/12) * ∑_i s_i^4 > 0` for all `s ≠ 0`.
    7. `universalSolver_psd_iff_freeEnergy_nonneg`:
       EXACT BICONDITIONAL PHASE-TRANSITION EQUIVALENCE:
         `W ⪰ 0  ↔  ∀ s ∈ (-1, 1)^N, L_{I - (1/μ)W}(s) ≥ 0`.
    8. `adaptiveResolventUniversal_neg_witness` &
       `adaptiveResolventUniversal_unique_zero_of_psd`:
       For the Adaptive Resolvent-Universal Solver `s = tanh(δ * (W + δ I)^{-1} s)`
       (`δ > 0`, written `W u + δ u = s`, `s = tanh(δ u)`):
         `u^T W u ≤ -(1/δ) * ‖W u‖_2^2 - (1/(3*δ)) * ∑_i s_i^4`.
       Thus `W ⪰ 0` implies `s = u = 0` uniquely for every `δ > 0`, while any
       non-zero fixed point yields an amplified strict negativity witness `u^T W u < 0`.

  PART III (EXACT ALL-PRIMES VON MANGOLDT RESOLVENT BRIDGE & PICK-SOLVER LIFTING):
    9. `xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im`:
       EXACT ALL-PRIMES IDENTITY ON `Im(z) > 1/2` directly linking Mathlib4's
       `LSeries ↗ArithmeticFunction.vonMangoldt` and `Complex.digamma` to `xiResolvent`:
         `R_ξ(z) = i * (1/s + 1/(s - 1) - (1/2) * log π + (1/2) * digamma(s/2) - L(Λ, s))`
       where `s = 1/2 - i*z` (`Re(s) > 1`).
   10. `hermitian_psd_iff_realLifted_psd` &
       `universalSolver_realLifted_pick_iff_hermitian_psd`:
       Exact equivalence between complex Hermitian Pick matrix PSD (`P ⪰ 0`),
       its `2n × 2n` real symmetric lifting `P_tilde ⪰ 0`, and global non-negativity
       of the Universal Solver free energy `L_{I - (1/μ) P_tilde}(s) ≥ 0` on `(-1, 1)^{2n}`.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import RiemannDipolar.HermiteBiehlerHomotopyAndWeilPick

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators LSeries.notation
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick

namespace UniversalSolverLyapunovAndPrimeResolvent

-- ==============================================================================
-- PART I: EXACT ENTROPY BARRIER & BREGMAN CONVEXITY OF `tanh` / `artanh`
-- ==============================================================================

/-- Inverse hyperbolic tangent `artanh(x) = (1/2) * log((1 + x) / (1 - x))` on `(-1, 1)`. -/
noncomputable def artanh (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))

/-- Binary entropy barrier (exact Legendre dual of `log cosh`, Level `+1` integral of `artanh`):
    `Φ_ent(x) = ((1 + x)/2) * log(1 + x) + ((1 - x)/2) * log(1 - x)`. -/
noncomputable def binEntropy (x : ℝ) : ℝ :=
  ((1 + x) / 2) * Real.log (1 + x) + ((1 - x) / 2) * Real.log (1 - x)

/-- THEOREM I.1A (Strict Boundedness of `Real.tanh`):
    For EVERY `y : ℝ`, `|Real.tanh y| < 1`. -/
theorem tanh_abs_lt_one (y : ℝ) : |Real.tanh y| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : 0 < (Real.exp y + Real.exp (-y)) / 2 := by positivity
  rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
  rw [abs_lt]
  constructor
  · have : 0 < Real.exp y := Real.exp_pos y; linarith
  · have : 0 < Real.exp (-y) := Real.exp_pos (-y); linarith

/-- THEOREM I.1B (Exact Inverse Identity `artanh (Real.tanh y) = y`):
    For EVERY `y : ℝ`, `artanh (Real.tanh y) = y`. -/
theorem artanh_tanh_eq (y : ℝ) : artanh (Real.tanh y) = y := by
  dsimp [artanh]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hp : 0 < Real.exp y := Real.exp_pos y
  have hm : 0 < Real.exp (-y) := Real.exp_pos (-y)
  have hden : (Real.exp y + Real.exp (-y)) / 2 ≠ 0 := by linarith
  have hratio : (1 + (Real.exp y - Real.exp (-y)) / 2 / ((Real.exp y + Real.exp (-y)) / 2)) /
      (1 - (Real.exp y - Real.exp (-y)) / 2 / ((Real.exp y + Real.exp (-y)) / 2)) =
      Real.exp (2 * y) := by
    have hexp2 : Real.exp y / Real.exp (-y) = Real.exp (2 * y) := by
      rw [← Real.exp_sub]; congr 1; ring
    rw [← hexp2]
    field_simp [hden, ne_of_gt hm]
    ring
  rw [hratio, Real.log_exp]
  ring

/-- THEOREM I.1C (Exact Inverse Identity `Real.tanh (artanh x) = x` on `(-1, 1)`):
    For EVERY `x : ℝ` with `|x| < 1`, `Real.tanh (artanh x) = x`. -/
theorem tanh_artanh_eq {x : ℝ} (hx : |x| < 1) : Real.tanh (artanh x) = x := by
  have hx1 : -1 < x := (abs_lt.mp hx).1
  have hx2 : x < 1 := (abs_lt.mp hx).2
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hratio_pos : 0 < (1 + x) / (1 - x) := div_pos hp hm
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  dsimp [artanh]
  have he1 : Real.exp ((1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))) =
      Real.sqrt ((1 + x) / (1 - x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hratio_pos]
    congr 1; ring
  have he2 : Real.exp (-((1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)))) =
      1 / Real.sqrt ((1 + x) / (1 - x)) := by
    rw [Real.exp_neg, he1, one_div]
  rw [he1, he2]
  set r : ℝ := Real.sqrt ((1 + x) / (1 - x))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hratio_pos
  have hr_sq : r ^ 2 = (1 + x) / (1 - x) := Real.sq_sqrt (le_of_lt hratio_pos)
  have hden_pos : 0 < r + 1 / r := by positivity
  have hstep : (r - 1 / r) / 2 / ((r + 1 / r) / 2) = (r ^ 2 - 1) / (r ^ 2 + 1) := by
    field_simp [ne_of_gt hr_pos, ne_of_gt hden_pos]
  rw [hstep, hr_sq]
  field_simp [ne_of_gt hm]
  ring

/-- THEOREM I.2A (Exact Derivative of `artanh`):
    For EVERY `x ∈ (-1, 1)`, `HasDerivAt artanh (1 / (1 - x^2)) x`. -/
theorem hasDerivAt_artanh {x : ℝ} (hx : |x| < 1) :
    HasDerivAt artanh (1 / (1 - x ^ 2)) x := by
  have hp : (1 + x) ≠ 0 := by linarith [(abs_lt.mp hx).1]
  have hm : (1 - x) ≠ 0 := by linarith [(abs_lt.mp hx).2]
  have hratio_ne : (1 + x) / (1 - x) ≠ 0 := div_ne_zero hp hm
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id' x)
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
  have hq : HasDerivAt (fun t : ℝ => (1 + t) / (1 - t)) (2 / (1 - x) ^ 2) x := by
    refine (h1.fun_div h2 hm).congr_deriv ?_
    ring
  have hlog : HasDerivAt (fun t : ℝ => Real.log ((1 + t) / (1 - t)))
      ((2 / (1 - x) ^ 2) / ((1 + x) / (1 - x))) x := hq.log hratio_ne
  have hmul := hlog.const_mul (1 / 2 : ℝ)
  refine hmul.congr_deriv ?_
  have hsq : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  rw [hsq]
  field_simp [hp, hm]

/-- THEOREM I.2B (Exact Derivative of Binary Entropy Barrier `binEntropy`):
    For EVERY `x ∈ (-1, 1)`, `HasDerivAt binEntropy (artanh x) x`. -/
theorem hasDerivAt_binEntropy {x : ℝ} (hx : |x| < 1) :
    HasDerivAt binEntropy (artanh x) x := by
  have hp : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have hm : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id' x)
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
  have hlin1 : HasDerivAt (fun t : ℝ => (1 + t) / 2) (1 / 2) x := h1.div_const 2
  have hlin2 : HasDerivAt (fun t : ℝ => (1 - t) / 2) (-1 / 2) x := h2.div_const 2
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x :=
    h1.log (ne_of_gt hp)
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - x)) x :=
    h2.log (ne_of_gt hm)
  have hp1 := hlin1.fun_mul hlog1
  have hp2 := hlin2.fun_mul hlog2
  refine (hp1.fun_add hp2).congr_deriv ?_
  dsimp [artanh]
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
  field_simp [ne_of_gt hp, ne_of_gt hm]
  ring

/-- Auxiliary monotonicity helper on `[0, 1)`: if `f 0 = 0` and `0 ≤ f' x` on `[0, 1)`,
    then `0 ≤ f x` for all `x ∈ [0, 1)`. -/
private lemma nonneg_on_Ico_zero_one {f : ℝ → ℝ} (f' : ℝ → ℝ) (h0 : f 0 = 0)
    (hd : ∀ x ∈ Ico (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Ico (0 : ℝ) 1, 0 ≤ f' x) :
    ∀ x ∈ Ico (0 : ℝ) 1, 0 ≤ f x := by
  have hmono : MonotoneOn f (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hx' : x ∈ Ico (0 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
      rw [(hd x hx').deriv]
      exact hnn x hx'
  intro x hx
  have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have := hmono h0mem hx hx.1
  linarith

/-- THEOREM I.3A (SHARP QUARTIC LOWER BOUND ON `x * artanh(x) - x^2`):
    For EVERY `x ∈ (-1, 1)`, `x^4 / 3 ≤ x * artanh(x) - x^2`. -/
theorem artanh_mul_sub_sq_ge_quartic {x : ℝ} (hx : |x| < 1) :
    x ^ 4 / 3 ≤ x * artanh x - x ^ 2 := by
  -- First prove on [0, 1): artanh x ≥ x + x^3 / 3!
  have hpos : ∀ y ∈ Ico (0 : ℝ) 1, 0 ≤ artanh y - (y + y ^ 3 / 3) := by
    refine nonneg_on_Ico_zero_one
      (fun y => 1 / (1 - y ^ 2) - (1 + ((3 : ℕ) : ℝ) * y ^ (3 - 1) / 3))
      (by dsimp [artanh]; norm_num) (fun y hy => ?_) (fun y hy => ?_)
    · have hy_abs : |y| < 1 := abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩
      have hsub := (hasDerivAt_artanh hy_abs).fun_sub
        ((hasDerivAt_id' y).fun_add ((hasDerivAt_pow 3 y).div_const 3))
      exact hsub
    · have h1my2 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      have hdiff : 1 / (1 - y ^ 2) - (1 + ((3 : ℕ) : ℝ) * y ^ (3 - 1) / 3) = y ^ 4 / (1 - y ^ 2) := by
        have hy2 : ((3 : ℕ) : ℝ) * y ^ (3 - 1) / 3 = y ^ 2 := by norm_num
        rw [hy2]; field_simp [ne_of_gt h1my2]; ring
      rw [hdiff]; positivity
  rcases le_total 0 x with hnn | hnp
  · have hx' : x ∈ Ico (0 : ℝ) 1 := ⟨hnn, (abs_lt.mp hx).2⟩
    have h := hpos x hx'
    nlinarith
  · have hnx' : -x ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith [(abs_lt.mp hx).1]⟩
    have h := hpos (-x) hnx'
    have hodd : artanh (-x) = -artanh x := by
      dsimp [artanh]
      have hinv : (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ := by
        have hp : (1 + x) ≠ 0 := by linarith [(abs_lt.mp hx).1]
        have hm : (1 - x) ≠ 0 := by linarith [(abs_lt.mp hx).2]
        field_simp [hp, hm]; ring
      rw [hinv, Real.log_inv]; ring
    rw [hodd] at h
    nlinarith

/-- THEOREM I.3B (SHARP QUARTIC LOWER BOUND ON `Φ_ent(x) - x^2 / 2`):
    For EVERY `x ∈ (-1, 1)`, `x^4 / 12 ≤ binEntropy x - x^2 / 2`. -/
theorem binEntropy_sub_half_sq_ge_quartic {x : ℝ} (hx : |x| < 1) :
    x ^ 4 / 12 ≤ binEntropy x - x ^ 2 / 2 := by
  have hpos : ∀ y ∈ Ico (0 : ℝ) 1, 0 ≤ binEntropy y - (y ^ 2 / 2 + y ^ 4 / 12) := by
    refine nonneg_on_Ico_zero_one
      (fun y => artanh y - (y + y ^ 3 / 3))
      (by dsimp [binEntropy]; norm_num) (fun y hy => ?_) (fun y hy => ?_)
    · have hy_abs : |y| < 1 := abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩
      exact ((hasDerivAt_binEntropy hy_abs).fun_sub
        (((hasDerivAt_pow 2 y).div_const 2).fun_add ((hasDerivAt_pow 4 y).div_const 12))).congr_deriv
        (by norm_num; ring)
    · have hy_abs : |y| < 1 := abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩
      rcases eq_or_lt_of_le hy.1 with rfl | hy_pos
      · dsimp [artanh]; norm_num
      · have hq := artanh_mul_sub_sq_ge_quartic hy_abs
        have : 0 ≤ y * (artanh y - (y + y ^ 3 / 3)) := by linarith
        exact nonneg_of_mul_nonneg_right this hy_pos
  rcases le_total 0 x with hnn | hnp
  · have h := hpos x ⟨hnn, (abs_lt.mp hx).2⟩; linarith
  · have h := hpos (-x) ⟨by linarith, by linarith [(abs_lt.mp hx).1]⟩
    have heven : binEntropy (-x) = binEntropy x := by
      dsimp [binEntropy]; ring_nf
    rw [heven] at h
    have hpow : (-x) ^ 2 / 2 + (-x) ^ 4 / 12 = x ^ 2 / 2 + x ^ 4 / 12 := by ring
    linarith

/-- THEOREM I.4 (EXACT 1-STRONG CONVEXITY / BREGMAN DIVERGENCE BOUND OF `binEntropy`):
    For EVERY `x, y ∈ (-1, 1)`:
      `(1 / 2) * (x - y)^2 ≤ binEntropy x - binEntropy y - artanh y * (x - y)`. -/
theorem binEntropy_bregman_ge_half_sq {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    (1 / 2 : ℝ) * (x - y) ^ 2 ≤ binEntropy x - binEntropy y - artanh y * (x - y) := by
  let g : ℝ → ℝ := fun t => binEntropy t - binEntropy y - artanh y * (t - y) - (1 / 2) * (t - y) ^ 2
  have hg_y : g y = 0 := by dsimp [g]; ring
  have hgd : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (artanh t - artanh y - (t - y)) t := by
    intro t ht
    have ht_abs : |t| < 1 := abs_lt.mpr ht
    have h1 := hasDerivAt_binEntropy ht_abs
    have h2 := hasDerivAt_const t (binEntropy y)
    have h3 : HasDerivAt (fun s : ℝ => artanh y * (s - y)) (artanh y) t := by
      simpa using ((hasDerivAt_id' t).fun_sub (hasDerivAt_const t y)).const_mul (artanh y)
    have h4 : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * (s - y) ^ 2) (t - y) t := by
      have hp := ((hasDerivAt_id' t).fun_sub (hasDerivAt_const t y)).pow 2
      exact (hp.const_mul (1 / 2 : ℝ)).congr_deriv (by norm_num; ring)
    exact (((h1.fun_sub h2).fun_sub h3).fun_sub h4).congr_deriv (by ring)
  -- Auxiliary: h(t) = artanh t - t is monotone on (-1, 1) since h'(t) = 1/(1-t^2) - 1 = t^2/(1-t^2) ≥ 0!
  have hart_mono : MonotoneOn (fun t : ℝ => artanh t - t) (Ioo (-1 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo (-1) 1)
    · exact fun t ht => ((hasDerivAt_artanh (abs_lt.mpr ht)).fun_sub (hasDerivAt_id' t)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hasDerivAt_artanh (abs_lt.mpr (interior_subset ht))).fun_sub (hasDerivAt_id' t)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [((hasDerivAt_artanh (abs_lt.mpr ht)).fun_sub (hasDerivAt_id' t)).deriv]
      have h1mt2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hdiff : 1 / (1 - t ^ 2) - 1 = t ^ 2 / (1 - t ^ 2) := by field_simp [ne_of_gt h1mt2]; ring
      rw [hdiff]; positivity
  have hgx : 0 ≤ g x := by
    rcases le_total y x with hyx | hxy
    · -- On [y, x] ⊆ (-1, 1), g'(t) = (artanh t - t) - (artanh y - y) ≥ 0
      have hmono : MonotoneOn g (Icc y x) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc y x)
        · exact fun t ht => (hgd t ⟨by linarith [(abs_lt.mp hy).1, ht.1], by linarith [(abs_lt.mp hx).2, ht.2]⟩).continuousAt.continuousWithinAt
        · intro t ht
          have ht' := interior_subset ht
          exact (hgd t ⟨by linarith [(abs_lt.mp hy).1, ht'.1], by linarith [(abs_lt.mp hx).2, ht'.2]⟩).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have ht_ioo : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp hy).1, ht.1], by linarith [(abs_lt.mp hx).2, ht.2]⟩
          rw [(hgd t ht_ioo).deriv]
          have h := hart_mono (abs_lt.mp hy) ht_ioo (le_of_lt ht.1)
          linarith
      have := hmono (Set.left_mem_Icc.mpr hyx) (Set.right_mem_Icc.mpr hyx) hyx
      linarith
    · -- On [x, y] ⊆ (-1, 1), g'(t) = (artanh t - t) - (artanh y - y) ≤ 0, so g is antitone
      have hanti : AntitoneOn g (Icc x y) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc x y)
        · exact fun t ht => (hgd t ⟨by linarith [(abs_lt.mp hx).1, ht.1], by linarith [(abs_lt.mp hy).2, ht.2]⟩).continuousAt.continuousWithinAt
        · intro t ht
          have ht' := interior_subset ht
          exact (hgd t ⟨by linarith [(abs_lt.mp hx).1, ht'.1], by linarith [(abs_lt.mp hy).2, ht'.2]⟩).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have ht_ioo : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp hx).1, ht.1], by linarith [(abs_lt.mp hy).2, ht.2]⟩
          rw [(hgd t ht_ioo).deriv]
          have h := hart_mono ht_ioo (abs_lt.mp hy) (le_of_lt ht.2)
          linarith
      have := hanti (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
      linarith
  dsimp [g] at hgx
  linarith

-- ==============================================================================
-- PART II: EXACT LYAPUNOV DESCENT & PHASE-TRANSITION THEORY OF UNIVERSAL SOLVER
-- ==============================================================================

/-- Real quadratic form `v^T M v = ∑_i ∑_j v_i * M_{ij} * v_j`. -/
def realQuadForm {N : ℕ} (M : Fin N → Fin N → ℝ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i * M i j * v j

/-- One synchronous step of the Universal Formula (Hopfield/Boltzmann solver):
    `s'_i = tanh(∑_j Q_{ij} s_j)`. -/
noncomputable def universalStep {N : ℕ} (Q : Fin N → Fin N → ℝ) (s : Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (∑ j : Fin N, Q i j * s j)

/-- Exact Boltzmann-Hopfield free energy functional (Level `+1` integral):
    `L_Q(s) = -(1/2) * s^T Q s + ∑_i Φ_ent(s_i)`. -/
noncomputable def universalFreeEnergy {N : ℕ} (Q : Fin N → Fin N → ℝ) (s : Fin N → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * realQuadForm Q s + ∑ i : Fin N, binEntropy (s i)

/-- Shifted coupling matrix `Q = I - (1/μ) W` (`μ > 0`) for spectral positivity testing. -/
noncomputable def shiftedCoupling {N : ℕ} (W : Fin N → Fin N → ℝ) (μ : ℝ) : Fin N → Fin N → ℝ :=
  fun i j => (if i = j then (1 : ℝ) else 0) - W i j / μ

/-- Auxiliary quadratic expansion for symmetric matrices:
    `s'^T Q s' - s^T Q s = (s' - s)^T Q (s' - s) + 2 * ∑_i (s'_i - s_i) * (Q s)_i`. -/
private lemma realQuadForm_sub_symm {N : ℕ} (Q : Fin N → Fin N → ℝ)
    (hQsym : ∀ i j, Q i j = Q j i) (s s' : Fin N → ℝ) :
    realQuadForm Q s' - realQuadForm Q s =
      realQuadForm Q (fun i => s' i - s i) +
      2 * ∑ i : Fin N, (s' i - s i) * (∑ j : Fin N, Q i j * s j) := by
  dsimp [realQuadForm]
  have hcross : (∑ i : Fin N, ∑ j : Fin N, s' i * Q i j * s j) =
      ∑ i : Fin N, ∑ j : Fin N, s i * Q i j * s' j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hQsym j i]; ring
  have hexp1 : (∑ i : Fin N, ∑ j : Fin N, (s' i - s i) * Q i j * (s' j - s j)) =
      (∑ i : Fin N, ∑ j : Fin N, s' i * Q i j * s' j) -
      (∑ i : Fin N, ∑ j : Fin N, s' i * Q i j * s j) -
      (∑ i : Fin N, ∑ j : Fin N, s i * Q i j * s' j) +
      (∑ i : Fin N, ∑ j : Fin N, s i * Q i j * s j) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hexp2 : (∑ i : Fin N, (s' i - s i) * (∑ j : Fin N, Q i j * s j)) =
      (∑ i : Fin N, ∑ j : Fin N, s' i * Q i j * s j) -
      (∑ i : Fin N, ∑ j : Fin N, s i * Q i j * s j) := by
    have h1 : ∀ i : Fin N, (s' i - s i) * (∑ j : Fin N, Q i j * s j) =
        (∑ j : Fin N, s' i * Q i j * s j) - (∑ j : Fin N, s i * Q i j * s j) := by
      intro i
      rw [sub_mul, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
    simp only [h1, Finset.sum_sub_distrib]
  rw [hexp1, hexp2, hcross]
  ring

/-- THEOREM II.1 (EXACT DISCRETE LYAPUNOV DESCENT OF THE UNIVERSAL SOLVER):
    For EVERY symmetric matrix `Q : Fin N → Fin N → ℝ` and EVERY state `s ∈ (-1, 1)^N`,
    setting `s' = universalStep Q s = tanh(Q s)`:
      `L_Q(s') + (1/2) * (s' - s)^T Q (s' - s) + (1/2) * ∑_i (s'_i - s_i)^2 ≤ L_Q(s)`.
    In particular, whenever `Q ⪰ 0` (`∀ v, 0 ≤ v^T Q v`), EVERY synchronous iteration of
    the Universal Formula strictly decreases the free energy `L_Q` by at least
    `(1/2) * ‖s' - s‖_2^2`, guaranteeing global Lyapunov stability and excluding period-2 cycles. -/
theorem universalSolver_exact_lyapunov_descent {N : ℕ} (Q : Fin N → Fin N → ℝ)
    (hQsym : ∀ i j, Q i j = Q j i) (s : Fin N → ℝ) (hs : ∀ i, |s i| < 1) :
    let s' := universalStep Q s
    universalFreeEnergy Q s' +
      (1 / 2 : ℝ) * realQuadForm Q (fun i => s' i - s i) +
      (1 / 2 : ℝ) * ∑ i : Fin N, (s' i - s i) ^ 2 ≤
    universalFreeEnergy Q s := by
  intro s'
  have hs' : ∀ i, |s' i| < 1 := fun i => tanh_abs_lt_one _
  have hart_s' : ∀ i, artanh (s' i) = ∑ j : Fin N, Q i j * s j := fun i => artanh_tanh_eq _
  have hbreg : ∑ i : Fin N, ((1 / 2 : ℝ) * (s i - s' i) ^ 2) ≤
      ∑ i : Fin N, (binEntropy (s i) - binEntropy (s' i) - artanh (s' i) * (s i - s' i)) :=
    Finset.sum_le_sum fun i _ => binEntropy_bregman_ge_half_sq (hs i) (hs' i)
  have hsq_sym : (∑ i : Fin N, ((1 / 2 : ℝ) * (s i - s' i) ^ 2)) =
      (1 / 2 : ℝ) * ∑ i : Fin N, (s' i - s i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hsum_breg : (∑ i : Fin N, (binEntropy (s i) - binEntropy (s' i) - artanh (s' i) * (s i - s' i))) =
      (∑ i : Fin N, binEntropy (s i)) - (∑ i : Fin N, binEntropy (s' i)) +
      ∑ i : Fin N, (s' i - s i) * (∑ j : Fin N, Q i j * s j) := by
    have hpt : ∀ i : Fin N,
        binEntropy (s i) - binEntropy (s' i) - artanh (s' i) * (s i - s' i) =
        binEntropy (s i) - binEntropy (s' i) + (s' i - s i) * (∑ j : Fin N, Q i j * s j) := by
      intro i; rw [hart_s' i]; ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsq_sym, hsum_breg] at hbreg
  have hquad := realQuadForm_sub_symm Q hQsym s s'
  dsimp [universalFreeEnergy]
  linarith

/-- Auxiliary: Quadratic form identity for `shiftedCoupling W μ = I - (1/μ) W`. -/
private lemma realQuadForm_shiftedCoupling {N : ℕ} (W : Fin N → Fin N → ℝ) (μ : ℝ) (v : Fin N → ℝ) :
    realQuadForm (shiftedCoupling W μ) v =
      (∑ i : Fin N, v i ^ 2) - realQuadForm W v / μ := by
  dsimp [realQuadForm, shiftedCoupling]
  have h1 : ∀ i : Fin N, ∑ j : Fin N, v i * ((if i = j then (1 : ℝ) else 0) - W i j / μ) * v j =
      v i ^ 2 - (∑ j : Fin N, v i * W i j * v j) / μ := by
    intro i
    have hsplit : ∀ j : Fin N,
        v i * ((if i = j then (1 : ℝ) else 0) - W i j / μ) * v j =
        (if i = j then v i ^ 2 else 0) - (v i * W i j * v j) / μ := by
      intro j; split_ifs with h <;> subst_vars <;> ring
    simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
               Finset.sum_div]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_div]

/-- THEOREM II.2A (ZERO-FALSE-POSITIVE NEGATIVITY WITNESS FROM ANY NON-ZERO FIXED POINT):
    For ANY matrix `W : Fin N → Fin N → ℝ` and ANY shift `μ > 0`, EVERY fixed point
    `s = universalStep (shiftedCoupling W μ) s` satisfies:
      `s^T W s ≤ -(μ / 3) * ∑_i s_i^4`.
    Hence ANY non-zero fixed point `s ≠ 0` is an instant, rigorous strict negativity witness
    `s^T W s < 0`! -/
theorem universalSolver_neg_witness_of_nonzero_fixedPoint {N : ℕ} (W : Fin N → Fin N → ℝ)
    {μ : ℝ} (hμ : 0 < μ) {s : Fin N → ℝ}
    (hfp : universalStep (shiftedCoupling W μ) s = s) :
    realQuadForm W s ≤ -(μ / 3) * ∑ i : Fin N, s i ^ 4 := by
  have hs_lt : ∀ i, |s i| < 1 := fun i => by rw [← hfp]; exact tanh_abs_lt_one _
  have hart_eq : ∀ i, artanh (s i) = ∑ j : Fin N, shiftedCoupling W μ i j * s j := fun i => by
    conv_lhs => rw [← hfp]
    exact artanh_tanh_eq _
  have hsum_art : ∑ i : Fin N, s i * artanh (s i) = realQuadForm (shiftedCoupling W μ) s := by
    dsimp [realQuadForm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hart_eq i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [realQuadForm_shiftedCoupling] at hsum_art
  have hq_ge : ∑ i : Fin N, (s i ^ 4 / 3) ≤ ∑ i : Fin N, (s i * artanh (s i) - s i ^ 2) :=
    Finset.sum_le_sum fun i _ => artanh_mul_sub_sq_ge_quartic (hs_lt i)
  rw [Finset.sum_sub_distrib, hsum_art, ← Finset.sum_div] at hq_ge
  have hneg : (∑ i : Fin N, s i ^ 4) / 3 ≤ -(realQuadForm W s / μ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hneg (le_of_lt hμ)
  have hsimp : μ * -(realQuadForm W s / μ) = -realQuadForm W s := by
    field_simp [ne_of_gt hμ]
  rw [hsimp] at hmul
  linarith

/-- THEOREM II.2B (UNIQUENESS OF `s = 0` & STRICT QUARTIC FREE-ENERGY FLOOR WHEN `W ⪰ 0`):
    Whenever `W ⪰ 0` (`∀ v, 0 ≤ realQuadForm W v`) and `μ > 0`, letting `Q = I - (1/μ) W`:
    (1) For EVERY `s ∈ (-1, 1)^N`, `L_Q(s) ≥ (1 / 12) * ∑_i s_i^4 ≥ 0`,
    (2) `s = 0` is the UNIQUE fixed point of `universalStep Q` on ALL of `ℝ^N`. -/
theorem universalSolver_unique_zero_of_psd {N : ℕ} (W : Fin N → Fin N → ℝ)
    (hW : ∀ v : Fin N → ℝ, 0 ≤ realQuadForm W v) {μ : ℝ} (hμ : 0 < μ) :
    (∀ s : Fin N → ℝ, (∀ i, |s i| < 1) →
      (1 / 12 : ℝ) * ∑ i : Fin N, s i ^ 4 ≤ universalFreeEnergy (shiftedCoupling W μ) s) ∧
    (∀ s : Fin N → ℝ, universalStep (shiftedCoupling W μ) s = s → s = 0) := by
  constructor
  · intro s hs
    dsimp [universalFreeEnergy]
    rw [realQuadForm_shiftedCoupling]
    have hW_nn : 0 ≤ realQuadForm W s / μ := div_nonneg (hW s) (le_of_lt hμ)
    have hent : ∑ i : Fin N, (s i ^ 4 / 12) ≤ ∑ i : Fin N, (binEntropy (s i) - s i ^ 2 / 2) :=
      Finset.sum_le_sum fun i _ => binEntropy_sub_half_sq_ge_quartic (hs i)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hent
    linarith
  · intro s hfp
    have hneg := universalSolver_neg_witness_of_nonzero_fixedPoint W hμ hfp
    have hpos := hW s
    have hsum4_le : ∑ i : Fin N, s i ^ 4 ≤ 0 := by nlinarith
    ext i
    have hi_le : s i ^ 4 ≤ 0 := by
      have hsingle : s i ^ 4 ≤ ∑ j : Fin N, s j ^ 4 :=
        Finset.single_le_sum (f := fun j => s j ^ 4) (fun j _ => by positivity) (Finset.mem_univ i)
      linarith
    have h4 : s i ^ 4 = 0 := le_antisymm hi_le (by positivity)
    exact eq_zero_of_pow_eq_zero h4

/-- Auxiliary elementary upper bound on `binEntropy x - x^2 / 2` for `|x| ≤ 1/2`:
    `binEntropy x - x^2 / 2 ≤ x^4 / 4`. -/
private lemma binEntropy_sub_half_sq_le_quartic {x : ℝ} (hx : |x| ≤ 1 / 2) :
    binEntropy x - x ^ 2 / 2 ≤ x ^ 4 / 4 := by
  -- First prove on [0, 1/2]: artanh y - y ≤ y^3 (since deriv = y^2/(1-y^2) ≤ (4/3)*y^2 ≤ 3*y^2!)
  have hart_ub : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → artanh y - y ≤ y ^ 3 := by
    have hmono : MonotoneOn (fun t : ℝ => t ^ 3 - (artanh t - t)) (Icc (0 : ℝ) (1 / 2)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      · exact fun t ht => (((hasDerivAt_pow 3 t).fun_sub
          ((hasDerivAt_artanh (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).fun_sub
            (hasDerivAt_id' t)))).continuousAt.continuousWithinAt
      · intro t ht
        have ht' := interior_subset ht
        exact (((hasDerivAt_pow 3 t).fun_sub
          ((hasDerivAt_artanh (abs_lt.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩)).fun_sub
            (hasDerivAt_id' t)))).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htabs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [(((hasDerivAt_pow 3 t).fun_sub ((hasDerivAt_artanh htabs).fun_sub (hasDerivAt_id' t)))).deriv]
        have h1mt2 : (3 / 4 : ℝ) ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
        have hdiv : 1 / (1 - t ^ 2) - 1 ≤ (4 / 3 : ℝ) * t ^ 2 := by
          have h1 : 1 / (1 - t ^ 2) - 1 = t ^ 2 / (1 - t ^ 2) := by
            field_simp [ne_of_gt (by linarith : 0 < 1 - t ^ 2)]; ring
          rw [h1, div_le_iff₀ (by linarith : 0 < 1 - t ^ 2)]
          nlinarith [sq_nonneg t]
        have hpow3 : ((3 : ℕ) : ℝ) * t ^ (3 - 1) = 3 * t ^ 2 := by norm_num
        rw [hpow3]
        nlinarith [sq_nonneg t]
    intro y hy0 hy1
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_refl 0, by norm_num⟩
    have h := hmono h0mem ⟨hy0, hy1⟩ hy0
    have h0 : (0 : ℝ) ^ 3 - (artanh 0 - 0) = 0 := by dsimp [artanh]; norm_num
    linarith
  -- Integrate once: on [0, 1/2], x^4/4 - (binEntropy x - x^2/2) has deriv = x^3 - (artanh x - x) ≥ 0!
  have hmono_ent : MonotoneOn (fun t : ℝ => t ^ 4 / 4 - (binEntropy t - t ^ 2 / 2)) (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    · exact fun t ht => ((((hasDerivAt_pow 4 t).div_const 4).fun_sub
        ((hasDerivAt_binEntropy (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).fun_sub
          ((hasDerivAt_pow 2 t).div_const 2)))).continuousAt.continuousWithinAt
    · intro t ht
      have ht' := interior_subset ht
      exact ((((hasDerivAt_pow 4 t).div_const 4).fun_sub
        ((hasDerivAt_binEntropy (abs_lt.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩)).fun_sub
          ((hasDerivAt_pow 2 t).div_const 2)))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htabs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [((((hasDerivAt_pow 4 t).div_const 4).fun_sub
        ((hasDerivAt_binEntropy htabs).fun_sub ((hasDerivAt_pow 2 t).div_const 2)))).deriv]
      have h1 : ((4 : ℕ) : ℝ) * t ^ (4 - 1) / 4 = t ^ 3 := by norm_num
      have h2 : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by norm_num
      rw [h1, h2]
      linarith [hart_ub t (le_of_lt ht.1) (le_of_lt ht.2)]
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_refl 0, by norm_num⟩
  rcases le_total 0 x with hnn | hnp
  · have hxmem : x ∈ Icc (0 : ℝ) (1 / 2) := ⟨hnn, (abs_le.mp hx).2⟩
    have h := hmono_ent h0mem hxmem hnn
    have h0 : (0 : ℝ) ^ 4 / 4 - (binEntropy 0 - 0 ^ 2 / 2) = 0 := by dsimp [binEntropy]; norm_num
    linarith
  · have hnxmem : -x ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith, by linarith [(abs_le.mp hx).1]⟩
    have h := hmono_ent h0mem hnxmem (by linarith)
    have h0 : (0 : ℝ) ^ 4 / 4 - (binEntropy 0 - 0 ^ 2 / 2) = 0 := by dsimp [binEntropy]; norm_num
    have heven : binEntropy (-x) = binEntropy x := by dsimp [binEntropy]; ring_nf
    dsimp only at h
    rw [heven] at h
    have hp : (-x) ^ 4 / 4 = x ^ 4 / 4 := by ring
    have hp2 : (-x) ^ 2 / 2 = x ^ 2 / 2 := by ring
    linarith

/-- THEOREM II.3 (EXACT BICONDITIONAL PHASE-TRANSITION EQUIVALENCE FOR THE UNIVERSAL SOLVER):
    For EVERY real matrix `W : Fin N → Fin N → ℝ` and EVERY `μ > 0`:
      `(∀ v, 0 ≤ v^T W v) ↔ (∀ s ∈ (-1, 1)^N, 0 ≤ L_{I - (1/μ) W}(s))`.
    Thus Pick-Weil positive semi-definiteness is 100% logically equivalent to global
    non-negativity of the Universal Solver Boltzmann-Hopfield free energy. -/
theorem universalSolver_psd_iff_freeEnergy_nonneg {N : ℕ} (W : Fin N → Fin N → ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    (∀ v : Fin N → ℝ, 0 ≤ realQuadForm W v) ↔
    (∀ s : Fin N → ℝ, (∀ i, |s i| < 1) → 0 ≤ universalFreeEnergy (shiftedCoupling W μ) s) := by
  constructor
  · intro hW s hs
    have h := (universalSolver_unique_zero_of_psd W hW hμ).1 s hs
    have hnn : 0 ≤ (1 / 12 : ℝ) * ∑ i : Fin N, s i ^ 4 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
    linarith
  · intro hL v
    by_contra hlt
    push Not at hlt
    -- Let M = 1 + ∑_i |v i| > 0; scale s_i = ε * v_i with small ε > 0 so |s_i| ≤ 1/2 and L(ε v) < 0!
    set A : ℝ := -realQuadForm W v / (2 * μ)
    have hA_pos : 0 < A := div_pos (by linarith) (by linarith)
    set B4 : ℝ := (1 / 4 : ℝ) * ∑ i : Fin N, v i ^ 4
    have hB4_nn : 0 ≤ B4 := mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by positivity)
    set M1 : ℝ := 1 + ∑ i : Fin N, |v i|
    have hM1_pos : 0 < M1 := by
      have : 0 ≤ ∑ i : Fin N, |v i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    set ε : ℝ := min (1 / (2 * M1)) (Real.sqrt (A / (2 * (B4 + 1))))
    have hε_pos : 0 < ε := by
      refine lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
    have hε_half : ∀ i : Fin N, |ε * v i| ≤ 1 / 2 := by
      intro i
      rw [abs_mul, abs_of_pos hε_pos]
      have hvi_le : |v i| ≤ M1 := by
        have h1 : |v i| ≤ ∑ j : Fin N, |v j| :=
          Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        linarith
      have hε1 : ε ≤ 1 / (2 * M1) := min_le_left _ _
      calc ε * |v i| ≤ (1 / (2 * M1)) * M1 := mul_le_mul hε1 hvi_le (abs_nonneg _) (by positivity)
        _ = 1 / 2 := by field_simp [ne_of_gt hM1_pos]
    have hε_lt1 : ∀ i : Fin N, |ε * v i| < 1 := fun i => lt_of_le_of_lt (hε_half i) (by norm_num)
    have hL_nn := hL (fun i => ε * v i) hε_lt1
    have hquad_scale : realQuadForm W (fun i => ε * v i) = ε ^ 2 * realQuadForm W v := by
      dsimp [realQuadForm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hent_ub : ∑ i : Fin N, (binEntropy (ε * v i) - (ε * v i) ^ 2 / 2) ≤ ε ^ 4 * B4 := by
      calc ∑ i : Fin N, (binEntropy (ε * v i) - (ε * v i) ^ 2 / 2)
        _ ≤ ∑ i : Fin N, ((ε * v i) ^ 4 / 4) :=
            Finset.sum_le_sum fun i _ => binEntropy_sub_half_sq_le_quartic (hε_half i)
        _ = ε ^ 4 * B4 := by
            dsimp [B4]; rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
    have hL_ub : universalFreeEnergy (shiftedCoupling W μ) (fun i => ε * v i) ≤
        -ε ^ 2 * A + ε ^ 4 * B4 := by
      dsimp [universalFreeEnergy]
      rw [realQuadForm_shiftedCoupling, hquad_scale]
      rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hent_ub
      have hA_eq : ε ^ 2 * realQuadForm W v / μ * (1 / 2) = -(ε ^ 2 * A) := by
        dsimp [A]; field_simp [ne_of_gt hμ]
      linarith
    have hε2_le : ε ^ 2 ≤ A / (2 * (B4 + 1)) := by
      have h1 : ε ≤ Real.sqrt (A / (2 * (B4 + 1))) := min_le_right _ _
      have h2 := pow_le_pow_left₀ (le_of_lt hε_pos) h1 2
      rwa [Real.sq_sqrt (by positivity)] at h2
    have hB4_bound : ε ^ 2 * B4 ≤ A / 2 := by
      have h1 : ε ^ 2 * B4 ≤ (A / (2 * (B4 + 1))) * B4 :=
        mul_le_mul_of_nonneg_right hε2_le hB4_nn
      have h2 : (A / (2 * (B4 + 1))) * B4 ≤ A / 2 := by
        have hpos_den : 0 < 2 * (B4 + 1) := by linarith
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos_den (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      linarith
    have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε_pos
    have hneg_L : -ε ^ 2 * A + ε ^ 4 * B4 < 0 := by
      have heq : -ε ^ 2 * A + ε ^ 4 * B4 = ε ^ 2 * (ε ^ 2 * B4 - A) := by ring
      rw [heq]
      exact mul_neg_of_pos_of_neg hε2_pos (by linarith)
    linarith

/-- THEOREM II.4 (EXACT ADAPTIVE RESOLVENT-UNIVERSAL PRECONDITIONER — AMPLIFIED WITNESS):
    For ANY real matrix `W : Fin N → Fin N → ℝ`, ANY shift `δ > 0`, and ANY pair `(s, u)`
    solving the Adaptive Resolvent-Universal fixed-point equations
      `∑_j W_{ij} u_j + δ u_i = s_i`  and  `s_i = tanh(δ u_i)`
    (i.e. `s = tanh(δ (W + δ I)^{-1} s)` with resolvent witness `u = (W + δ I)^{-1} s`):
    (1) `u^T W u ≤ -(1/δ) * ∑_i (W u)_i^2 - (1/(3*δ)) * ∑_i s_i^4`,
    (2) Consequently, whenever `W ⪰ 0`, `s = 0` and `u = 0` is the UNIQUE fixed point for EVERY `δ > 0`,
        while ANY non-zero fixed point `s ≠ 0` yields an amplified strict negativity witness `u^T W u < 0`! -/
theorem adaptiveResolventUniversal_neg_witness_and_unique_zero {N : ℕ} (W : Fin N → Fin N → ℝ)
    {del : ℝ} (hdel : 0 < del) {s u : Fin N → ℝ}
    (hres : ∀ i : Fin N, (∑ j : Fin N, W i j * u j) + del * u i = s i)
    (hfp : ∀ i : Fin N, Real.tanh (del * u i) = s i) :
    realQuadForm W u ≤
      -(1 / del) * (∑ i : Fin N, (∑ j : Fin N, W i j * u j) ^ 2) -
      (1 / (3 * del)) * (∑ i : Fin N, s i ^ 4) := by
  have hs_lt : ∀ i, |s i| < 1 := fun i => by rw [← hfp i]; exact tanh_abs_lt_one _
  have hart_eq : ∀ i, artanh (s i) = del * u i := fun i => by
    rw [← hfp i]; exact artanh_tanh_eq _
  have hq_ge : ∑ i : Fin N, (s i ^ 4 / 3) ≤ ∑ i : Fin N, (s i * artanh (s i) - s i ^ 2) :=
    Finset.sum_le_sum fun i _ => artanh_mul_sub_sq_ge_quartic (hs_lt i)
  have hident : ∑ i : Fin N, (s i * artanh (s i) - s i ^ 2) =
      -(∑ i : Fin N, (∑ j : Fin N, W i j * u j) ^ 2) - del * realQuadForm W u := by
    have hpt : ∀ i : Fin N, s i * artanh (s i) - s i ^ 2 =
        -(∑ j : Fin N, W i j * u j) ^ 2 - del * (∑ j : Fin N, u i * W i j * u j) := by
      intro i
      rw [hart_eq i, ← hres i]
      have hmul : u i * (∑ j : Fin N, W i j * u j) = ∑ j : Fin N, u i * W i j * u j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      rw [← hmul]
      ring
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rfl
  rw [hident, ← Finset.sum_div] at hq_ge
  have hstep : del * realQuadForm W u ≤
      -(∑ i : Fin N, (∑ j : Fin N, W i j * u j) ^ 2) - (∑ i : Fin N, s i ^ 4) / 3 := by linarith
  have hdiv := div_le_div_of_nonneg_right hstep (le_of_lt hdel)
  rw [mul_div_cancel_left₀ _ (ne_of_gt hdel)] at hdiv
  calc realQuadForm W u
    _ ≤ (-(∑ i : Fin N, (∑ j : Fin N, W i j * u j) ^ 2) - (∑ i : Fin N, s i ^ 4) / 3) / del := hdiv
    _ = -(1 / del) * (∑ i : Fin N, (∑ j : Fin N, W i j * u j) ^ 2) -
          (1 / (3 * del)) * (∑ i : Fin N, s i ^ 4) := by field_simp [ne_of_gt hdel]

theorem adaptiveResolventUniversal_unique_zero_of_psd {N : ℕ} (W : Fin N → Fin N → ℝ)
    (hW : ∀ v : Fin N → ℝ, 0 ≤ realQuadForm W v) {del : ℝ} (hdel : 0 < del) {s u : Fin N → ℝ}
    (hres : ∀ i : Fin N, (∑ j : Fin N, W i j * u j) + del * u i = s i)
    (hfp : ∀ i : Fin N, Real.tanh (del * u i) = s i) :
    s = 0 ∧ u = 0 := by
  have hneg := adaptiveResolventUniversal_neg_witness_and_unique_zero W hdel hres hfp
  have hW_nn := hW u
  have h1_nn : 0 ≤ (1 / del) * ∑ i : Fin N, (∑ j : Fin N, W i j * u j) ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h2_nn : 0 ≤ (1 / (3 * del)) * ∑ i : Fin N, s i ^ 4 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  have hs0 : s = 0 := by
    have hsum4_le : ∑ i : Fin N, s i ^ 4 ≤ 0 := by
      have : (1 / (3 * del)) * ∑ i : Fin N, s i ^ 4 ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_right this (by positivity)
    ext i
    have hi_le : s i ^ 4 ≤ 0 := le_trans
      (Finset.single_le_sum (f := fun j => s j ^ 4) (fun _ _ => by positivity) (Finset.mem_univ i)) hsum4_le
    exact eq_zero_of_pow_eq_zero (le_antisymm hi_le (by positivity))
  refine ⟨hs0, ?_⟩
  ext i
  have hfp_i : Real.tanh (del * u i) = 0 := by rw [hfp i, hs0]; rfl
  have hart_i : del * u i = 0 := by
    rw [← artanh_tanh_eq (del * u i), hfp_i]
    dsimp [artanh]; norm_num
  exact (mul_eq_zero.mp hart_i).resolve_left (ne_of_gt hdel)

-- ==============================================================================
-- PART III: EXACT ALL-PRIMES VON MANGOLDT RESOLVENT BRIDGE & PICK-SOLVER LIFTING
-- ==============================================================================

/-- THEOREM III.1 (EXACT ALL-PRIMES `vonMangoldt` RESOLVENT BRIDGE ON `Im(z) > 1/2`):
    For EVERY `z : ℂ` with `1 / 2 < z.im` (equivalently `s = 1/2 - i*z` satisfies `1 < s.re`,
    the exact half-plane of absolute convergence of the Euler product over ALL primes):
      `R_ξ(z) = i * (1/s + 1/(s - 1) - (1/2) * log π + (1/2) * digamma(s / 2) - L(Λ, s))`,
    directly linking Mathlib4's `LSeries ↗ArithmeticFunction.vonMangoldt` (all infinitely many
    primes) to the spectral resolvent `xiResolvent z` and every Pick matrix entry on `Im(z) > 1/2`. -/
theorem xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im {z : ℂ} (hz : 1 / 2 < z.im) :
    let s : ℂ := 1 / 2 - Complex.I * z
    xiResolvent z =
      Complex.I * (1 / s + 1 / (s - 1) - (1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) := by
  intro s
  have hs_re : 1 < s.re := by
    dsimp [s]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
               Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, sub_neg_eq_add]
    linarith
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs_re; norm_num at hs_re
  have hs1 : s ≠ 1 := by intro h1; rw [h1] at hs_re; norm_num at hs_re
  have hs1_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hzeta_nz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs_re)
  have hpi_nz : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hgamma_nz : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hcpow_nz : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_nz)
  -- Local equality in a neighborhood of s: riemannXi w = (1/2) * w * (w - 1) * π^(-w/2) * Γ(w/2) * ζ(w)
  have hloc : riemannXi =ᶠ[𝓝 s] fun w : ℂ =>
      (1 / 2 : ℂ) * w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2)) * Complex.Gamma (w / 2) * riemannZeta w := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs_re] with w hw
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; norm_num at hw
    have hw1 : w - 1 ≠ 0 := by intro h1; have : w = 1 := sub_eq_zero.mp h1; rw [this] at hw; norm_num at hw
    have hw1' : 1 - w ≠ 0 := by intro h1; apply hw1; linear_combination -h1
    have hcomp : completedRiemannZeta w =
        (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) * riemannZeta w := by
      have hdef := riemannZeta_def_of_ne_zero hw0
      rw [Complex.Gammaℝ_def] at hdef
      have hg_nz : (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) ≠ 0 :=
        mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_nz))
          (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
      rw [hdef, mul_div_cancel₀ _ hg_nz]
    dsimp [riemannXi]
    have hxi_comp : riemannXi w = (1 / 2 : ℂ) * (w * (w - 1) * completedRiemannZeta w) := by
      dsimp [riemannXi]
      rw [completedRiemannZeta_eq]
      field_simp [hw0, hw1']
      ring
    dsimp [riemannXi] at hxi_comp
    rw [hxi_comp, hcomp]
    ring
  have hlogd_eq : logDeriv riemannXi s =
      logDeriv (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2)) *
        Complex.Gamma (w / 2) * riemannZeta w) s :=
    (logDeriv_congr_nhds hloc).eq_of_nhds
  -- Differentiability of each factor at s
  have hd_half : DifferentiableAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) s := differentiableAt_const _
  have hd_id : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have hd_sub : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := differentiableAt_id.sub (differentiableAt_const _)
  have hd_exp : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi_nz)
  have hg_diff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    refine Complex.differentiableAt_Gamma (s / 2) ?_
    intro m hm
    have hre_eq := congrArg Complex.re hm
    simp at hre_eq
    linarith
  have harg_half : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id' s).div_const 2
  have hcomp_gam : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ)) s :=
    hg_diff.hasDerivAt.comp s harg_half
  have hd_gam : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s :=
    hcomp_gam.differentiableAt
  have hd_zeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  -- Compute logDeriv of each factor cleanly
  have hld_const : logDeriv (fun _ : ℂ => (1 / 2 : ℂ)) s = 0 := by
    simp [logDeriv_apply]
  have hld_id : logDeriv (fun w : ℂ => w) s = 1 / s := by
    simp [logDeriv_apply]
  have hld_sub : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    have hd : HasDerivAt (fun w : ℂ => w - 1) 1 s := by
      simpa using (hasDerivAt_id' s).fun_sub (hasDerivAt_const s (1 : ℂ))
    rw [logDeriv_apply, hd.deriv]
  have hld_cpow : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s =
      -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) := by
    have harg : HasDerivAt (fun w : ℂ => -w / 2) (-(1 / 2 : ℂ)) s :=
      ((hasDerivAt_id' s).neg.div_const 2).congr_deriv (by ring)
    have hcp := harg.const_cpow (Or.inl hpi_nz)
    rw [logDeriv_apply, hcp.deriv]
    field_simp [hcpow_nz]
  have hld_gam : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s =
      (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    rw [logDeriv_apply, hcomp_gam.deriv, Complex.digamma_def, logDeriv_apply]
    ring
  have hld_zeta : logDeriv riemannZeta s =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have hvm := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs_re
    rw [logDeriv_apply]
    have heq : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        -deriv riemannZeta s / riemannZeta s := by
      simpa [LSeries.term] using hvm
    rw [heq, neg_div, neg_neg]
  -- Expand product logDeriv via `logDeriv_fun_mul`
  have hhalf_nz : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have h12_nz : (1 / 2 : ℂ) * s ≠ 0 := mul_ne_zero hhalf_nz hs0
  have h123_nz : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := mul_ne_zero h12_nz hs1_sub
  have h1234_nz : (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := mul_ne_zero h123_nz hcpow_nz
  have h12345_nz : (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
    mul_ne_zero h1234_nz hgamma_nz
  have hd12 : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w) s := hd_half.mul hd_id
  have hd123 : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1)) s := hd12.mul hd_sub
  have hd1234 : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1) * (Real.pi : ℂ) ^ (-w / 2)) s :=
    hd123.mul hd_exp
  have hd12345 : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) *
      Complex.Gamma (w / 2)) s := hd1234.mul hd_gam
  rw [logDeriv_fun_mul s h12345_nz hzeta_nz hd12345 hd_zeta,
      logDeriv_fun_mul s h1234_nz hgamma_nz hd1234 hd_gam,
      logDeriv_fun_mul s h123_nz hcpow_nz hd123 hd_exp,
      logDeriv_fun_mul s h12_nz hs1_sub hd12 hd_sub,
      logDeriv_fun_mul s hhalf_nz hs0 hd_half hd_id] at hlogd_eq
  rw [hld_const, hld_id, hld_sub, hld_cpow, hld_gam, hld_zeta] at hlogd_eq
  dsimp [xiResolvent]
  change Complex.I * logDeriv riemannXi s = _
  rw [hlogd_eq]
  ring

/-- `2n × 2n` real symmetric lifting `[[Re P, -Im P], [Im P, Re P]]` of an `n × n` complex
    Hermitian matrix `P` (indexed via `Fin (n + n)` splitting on `< n` vs `≥ n`). -/
def realLiftedMatrix {n : ℕ} (P : Fin n → Fin n → ℂ) (a b : Fin (n + n)) : ℝ :=
  if ha : a.val < n then
    if hb : b.val < n then (P ⟨a.val, ha⟩ ⟨b.val, hb⟩).re
    else -(P ⟨a.val, ha⟩ ⟨b.val - n, by omega⟩).im
  else
    if hb : b.val < n then (P ⟨a.val - n, by omega⟩ ⟨b.val, hb⟩).im
    else (P ⟨a.val - n, by omega⟩ ⟨b.val - n, by omega⟩).re

/-- Exact algebraic identity between complex Hermitian quadratic form `Re(∑ conj(c_j) P_{jk} c_k)`
    and real symmetric quadratic form `v^T P_tilde v` on `Fin (n + n)`. -/
private lemma realQuadForm_realLifted_eq_hermitian {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) (v : Fin (n + n) → ℝ) :
    let c : Fin n → ℂ := fun j =>
      ((v ⟨j.val, by omega⟩ : ℝ) : ℂ) + Complex.I * ((v ⟨j.val + n, by omega⟩ : ℝ) : ℂ)
    realQuadForm (realLiftedMatrix P) v =
      (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re := by
  intro c
  dsimp [realQuadForm]
  have hsplit : ∀ f : Fin (n + n) → ℝ,
      ∑ a : Fin (n + n), f a =
        (∑ j : Fin n, f ⟨j.val, by omega⟩) + (∑ j : Fin n, f ⟨j.val + n, by omega⟩) := by
    intro f
    rw [Fin.sum_univ_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ext; dsimp [Fin.natAdd]; omega
  rw [hsplit]
  have hinner : ∀ a : Fin (n + n),
      (∑ b : Fin (n + n), v a * realLiftedMatrix P a b * v b) =
        (∑ k : Fin n, v a * realLiftedMatrix P a ⟨k.val, by omega⟩ * v ⟨k.val, by omega⟩) +
        (∑ k : Fin n, v a * realLiftedMatrix P a ⟨k.val + n, by omega⟩ * v ⟨k.val + n, by omega⟩) :=
    fun a => hsplit _
  simp only [hinner, Finset.sum_add_distrib]
  -- Simplify realLiftedMatrix on the four blocks
  have hb00 : ∀ j k : Fin n, realLiftedMatrix P ⟨j.val, by omega⟩ ⟨k.val, by omega⟩ = (P j k).re := by
    intro j k; dsimp [realLiftedMatrix]; simp [j.isLt, k.isLt]
  have hb01 : ∀ j k : Fin n, realLiftedMatrix P ⟨j.val, by omega⟩ ⟨k.val + n, by omega⟩ = -(P j k).im := by
    intro j k; dsimp [realLiftedMatrix]
    have hnot : ¬(k.val + n < n) := by omega
    simp [j.isLt, hnot]
  have hb10 : ∀ j k : Fin n, realLiftedMatrix P ⟨j.val + n, by omega⟩ ⟨k.val, by omega⟩ = (P j k).im := by
    intro j k; dsimp [realLiftedMatrix]
    have hnot : ¬(j.val + n < n) := by omega
    simp [k.isLt, hnot]
  have hb11 : ∀ j k : Fin n, realLiftedMatrix P ⟨j.val + n, by omega⟩ ⟨k.val + n, by omega⟩ = (P j k).re := by
    intro j k; dsimp [realLiftedMatrix]
    have hnot1 : ¬(j.val + n < n) := by omega
    have hnot2 : ¬(k.val + n < n) := by omega
    simp [hnot1, hnot2]
  simp only [hb00, hb01, hb10, hb11]
  -- Match term-by-term with Re(∑_j ∑_k conj(c_j) * P_{jk} * c_k)
  simp only [Complex.re_sum]
  have hrhs : ∑ j : Fin n, ∑ k : Fin n, (starRingEnd ℂ (c j) * P j k * c k).re =
      ∑ j : Fin n, ∑ k : Fin n,
        (v ⟨j.val, by omega⟩ * (P j k).re * v ⟨k.val, by omega⟩ +
         v ⟨j.val, by omega⟩ * (-(P j k).im) * v ⟨k.val + n, by omega⟩ +
         v ⟨j.val + n, by omega⟩ * (P j k).im * v ⟨k.val, by omega⟩ +
         v ⟨j.val + n, by omega⟩ * (P j k).re * v ⟨k.val + n, by omega⟩) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [c]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
               Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
               Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hrhs]
  simp only [Finset.sum_add_distrib]
  have _ := hHerm
  ring

/-- THEOREM III.2 (HERMITIAN PICK MATRIX PSD ↔ REAL LIFTING PSD ↔ UNIVERSAL SOLVER FREE ENERGY):
    For EVERY `n × n` complex Hermitian matrix `P` (`P k j = conj (P j k)`) and EVERY `μ > 0`,
    the following three statements are 100% logically equivalent:
    (1) `P` is Hermitian positive semi-definite: `∀ c : Fin n → ℂ, 0 ≤ Re(∑ conj(c_j) P_{jk} c_k)`,
    (2) Its `2n × 2n` real symmetric lifting `P_tilde = realLiftedMatrix P` is real PSD,
    (3) The Universal Solver Boltzmann-Hopfield free energy `L_{I - (1/μ) P_tilde}(s) ≥ 0`
        holds globally across the open hypercube `(-1, 1)^{2n}`. -/
theorem universalSolver_realLifted_pick_iff_hermitian_psd {n : ℕ} (P : Fin n → Fin n → ℂ)
    (hHerm : ∀ j k, P k j = starRingEnd ℂ (P j k)) {μ : ℝ} (hμ : 0 < μ) :
    ((∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ↔
     (∀ v : Fin (n + n) → ℝ, 0 ≤ realQuadForm (realLiftedMatrix P) v)) ∧
    ((∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ↔
     (∀ s : Fin (n + n) → ℝ, (∀ i, |s i| < 1) →
       0 ≤ universalFreeEnergy (shiftedCoupling (realLiftedMatrix P) μ) s)) := by
  have h12 : (∀ c : Fin n → ℂ, 0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * P j k * c k).re) ↔
      (∀ v : Fin (n + n) → ℝ, 0 ≤ realQuadForm (realLiftedMatrix P) v) := by
    constructor
    · intro hP v
      rw [realQuadForm_realLifted_eq_hermitian P hHerm v]
      exact hP _
    · intro hR c
      let v : Fin (n + n) → ℝ := fun a =>
        if ha : a.val < n then (c ⟨a.val, ha⟩).re else (c ⟨a.val - n, by omega⟩).im
      have hv_eq := realQuadForm_realLifted_eq_hermitian P hHerm v
      have hc_eq : (fun j : Fin n =>
          ((v ⟨j.val, by omega⟩ : ℝ) : ℂ) + Complex.I * ((v ⟨j.val + n, by omega⟩ : ℝ) : ℂ)) = c := by
        ext j
        dsimp [v]
        have hnot : ¬(j.val + n < n) := by omega
        simp only [j.isLt, hnot, ↓reduceDIte, Nat.add_sub_cancel, Fin.eta]
        rw [mul_comm Complex.I, Complex.re_add_im]
      rw [hc_eq] at hv_eq
      rw [← hv_eq]
      exact hR v
  exact ⟨h12, h12.trans (universalSolver_psd_iff_freeEnergy_nonneg (realLiftedMatrix P) hμ)⟩

end UniversalSolverLyapunovAndPrimeResolvent
