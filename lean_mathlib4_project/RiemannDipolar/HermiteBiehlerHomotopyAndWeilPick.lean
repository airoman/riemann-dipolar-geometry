/-
  ==============================================================================
  MODULE #13: HERMITE-BIEHLER / SCHUR-CAYLEY HOMOTOPY, CAUSAL WAVELET
              WEIL-PICK UNIFICATION, AND PARITY-DECOUPLED CONTINUOUS WEIL
              POSITIVITY (LEAN 4 + MATHLIB4)
  ==============================================================================

  Author: Mariano Martín Ramírez Tamayo
  Affiliation: Independent Researcher

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):

  PART I (ROUTE B — HERMITE-BIEHLER / SCHUR-CAYLEY HOMOTOPY E_α, S_α, M_α):
    1. `xiShiftE_schwarz_and_boundary_unitary`:
       Defining `E_α(z) = ξ(1/2 + α - iz)`, `E_α^#(z) = ξ(1/2 + α + iz)`,
       `S_α(z) = E_α^#(z) / E_α(z)`, and `M_α(z) = i * (1 - S_α(z)) / (1 + S_α(z))`,
       proves exact Schwarz reflection `E_α^#(z) = conj(E_α(conj z))`, functional-equation
       shift identity `E_α^#(z) = ξ(1/2 - α - iz)`, boundary unitarity `‖S_α(γ)‖ = 1` on `ℝ`,
       and exact modulus-potential identities `‖E_α(γ + iσ)‖^2 = V(α + σ, γ)` and
       `‖E_α^#(γ + iσ)‖^2 = V(α - σ, γ)`.
    2. `cayley_schur_iff_herglotz`:
       Exact Möbius identity `Im(i * (1 - w)/(1 + w)) = (1 - ‖w‖^2) / ‖1 + w‖^2`,
       proving `‖w‖ < 1 ↔ 0 < Im(i * (1 - w)/(1 + w))`.
    3. `pickMatrix_cayley_schur_congruence`:
       Exact all-order Hermitian Pick-Schur congruence identity proving that the
       `n × n` Herglotz-Pick matrix of `M_α` is positive semi-definite if and only if
       the `n × n` Schur-Pick matrix `(1 - S_α(z_j) conj(S_α(z_k))) / (-i(z_j - conj z_k))`
       is positive semi-definite.
    4. `xiShiftE_half_zeroFree_uhp`:
       UNCONDITIONAL strip-boundary baseline at `α = 1/2`: `E_{1/2}(z) = ξ(1 - iz) ≠ 0`
       on the entire closed upper half-plane `Im(z) ≥ 0` (so `S_{1/2}` is unconditionally
       pole-free on `overline(ℍ)`).
    5. `zeroFreeStrip_of_hermiteBiehler` & `riemannHypothesis_of_hermiteBiehler_all`:
       Exact zero-free strip exclusion: strict Hermite-Biehler `‖E_α^#(z)‖ < ‖E_α(z)‖` on `ℍ`
       excludes every zero of `riemannXi` (and `riemannZeta`) with `|Re(s) - 1/2| > α`;
       survival of the homotopy for all `α ∈ (0, 1/2)` implies Mathlib4's official
       `RiemannHypothesis`.
    6. `xiCayley_div_alpha_tendsto_xiResolvent`:
       Exact infinitesimal homotopy limit `lim_{α → 0} M_α(z) / α = R_ξ(z) = i*(ξ'/ξ)(1/2 - iz)`.
    7. `finiteStripQuartet_hermiteBiehler_exact_threshold`:
       Exact converse for every real-symmetric finite strip quartet product with zero offsets
       `|δ_m| ≤ Δ`: strict Hermite-Biehler holds for EVERY `α > Δ` (unconditionally at
       `α = 1/2` whenever `Δ < 1/2`, and for every `α > 0` on the critical line `Δ = 0`).

  PART II (EXACT ROUTE A ↔ ROUTE B UNIFICATION — CAUSAL EXPONENTIAL WAVELETS):
    8. `causalWavelet_fourier_eq_resolvent_kernel`:
       For `g_z(u) = exp(i*z*u) * 1_{u ≥ 0}` (`Im(z) > 0`), exact Laplace-Fourier transform
       `∫_{u > 0} exp(i*(z - t)*u) du = -i / (t - z)`.
    9. `causalWavelet_autocorrelation_eq`:
       Exact cross-correlation `∫_{v > 0} conj(g_{z_1}(v)) * g_{z_2}(v + u) dv =
       (i / (z_2 - conj z_1)) * exp(i * z_2 * u)` for all `z_1, z_2 ∈ ℍ`, `u ≥ 0`.
   10. `weilSpectralSum_causalWavelet_eq_pickForm`:
       GRAND ROUTE A ↔ ROUTE B UNIFICATION: evaluating the Weil spectral quadratic form
       on causal exponential wavelets `g(u) = ∑ c_j g_{z_j}(u)` equals IDENTICALLY the
       Hermitian Pick-Nevanlinna quadratic form of the spectral resolvent `G(z)`.

  PART III (ROUTE A — EXACT EVEN/ODD DECOUPLING & WIDER ZERO-DISCRETIZATION POSITIVITY):
   11. `weilTotal_even_odd_decouple`:
       Exact continuous orthogonal decoupling `W_total(L, g_e + g_o) = W_total(L, g_e) + W_total(L, g_o)`
       for EVERY `L > 0` (including ALL active `vonMangoldt` prime-shift terms).
   12. `compactFourier_odd_norm_sq_le` & `compactFourier_even_zeroMean_norm_sq_le`:
       Sharp parity Fourier suppression bounds `‖g_hat(t)‖^2 ≤ min(L, L^3 * t^2 / 12) * ‖g‖_2^2`
       (all continuous odd `g`) and `‖g_hat(t)‖^2 ≤ min(L, L^5 * t^4 / 320) * ‖g‖_2^2`
       (all continuous even zero-mean `g`).
   13. `weilTotal_continuous_pos_odd_up_to_three_tenths`:
       Unconditional infinite-dimensional continuous arithmetic Weil positivity on ALL
       odd continuous functions for `0 < L ≤ 3/10` (`2.4x` wider than `1/8`, zero discretization):
       `W_total(L, g) ≥ (1/100) * ‖g‖_2^2`.
   14. `weilTotal_continuous_pos_even_zeroMean_up_to_four_ninths`:
       Unconditional infinite-dimensional continuous arithmetic Weil positivity on ALL
       even zero-mean continuous functions for `0 < L ≤ 4/9` (`3.56x` wider than `1/8`, zero discretization):
       `W_total(L, g) ≥ (1/25) * ‖g‖_2^2`.

  PART IV (ROUTE B — EXACT ORDER-6 ALTERNATING COSINE LOWER BOUND):
   15. `cos_ge_taylor_six`:
       Unconditional global inequality `1 - x^2/2 + x^4/24 - x^6/720 ≤ cos x` for all `x : ℝ`,
       justifying higher-order alternating-cosine light-cone corridors.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannDipolar.UniversalWeilAndHerglotzResolvent

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent

namespace HermiteBiehlerHomotopyAndWeilPick

-- ==============================================================================
-- PART I: ROUTE B — HERMITE-BIEHLER / SCHUR-CAYLEY HOMOTOPY E_α, S_α, M_α
-- ==============================================================================

/-- Shifted Hermite-Biehler entire function `E_α(z) = ξ(1/2 + α - i*z)`. -/
noncomputable def xiShiftE (α : ℝ) (z : ℂ) : ℂ :=
  riemannXi (((1 / 2 + α : ℝ) : ℂ) - Complex.I * z)

/-- Schwarz conjugate of `E_α`: `E_α^#(z) = ξ(1/2 + α + i*z)`. -/
noncomputable def xiShiftE_sharp (α : ℝ) (z : ℂ) : ℂ :=
  riemannXi (((1 / 2 + α : ℝ) : ℂ) + Complex.I * z)

/-- Meromorphic Schur scattering ratio `S_α(z) = E_α^#(z) / E_α(z)`. -/
noncomputable def xiSchur (α : ℝ) (z : ℂ) : ℂ :=
  xiShiftE_sharp α z / xiShiftE α z

/-- Cayley-Herglotz homotopy transform `M_α(z) = i * (1 - S_α(z)) / (1 + S_α(z))`. -/
noncomputable def xiCayley (α : ℝ) (z : ℂ) : ℂ :=
  Complex.I * ((1 - xiSchur α z) / (1 + xiSchur α z))

/-- THEOREM I.1 (EXACT SCHWARZ CONJUGATION, BOUNDARY UNITARITY, AND POTENTIAL DUALITY):
    For every `α : ℝ` and `z : ℂ`:
    (1) `E_α^#(z) = conj(E_α(conj z))`,
    (2) `E_α^#(z) = ξ(1/2 - α - i*z)` (by the functional equation `ξ(1 - s) = ξ(s)`),
    (3) On the real axis `γ : ℝ`, whenever `E_α(γ) ≠ 0`, `‖S_α(γ)‖ = 1`,
    (4) For `z = γ + i*σ`, `‖E_α(γ + iσ)‖^2 = V(α + σ, γ)` and `‖E_α^#(γ + iσ)‖^2 = V(α - σ, γ)`. -/
theorem xiShiftE_schwarz_and_boundary_unitary (α : ℝ) :
    (∀ z : ℂ, xiShiftE_sharp α z = starRingEnd ℂ (xiShiftE α (starRingEnd ℂ z))) ∧
    (∀ z : ℂ, xiShiftE_sharp α z = riemannXi (((1 / 2 - α : ℝ) : ℂ) - Complex.I * z)) ∧
    (∀ γ : ℝ, xiShiftE α (γ : ℂ) ≠ 0 → ‖xiSchur α (γ : ℂ)‖ = 1) ∧
    (∀ σ γ : ℝ,
      ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 = xiNormSq (α + σ) γ ∧
      ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 = xiNormSq (α - σ) γ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    dsimp [xiShiftE, xiShiftE_sharp]
    rw [← riemannXi_conj]
    congr 1
    apply Complex.ext <;> simp
  · intro z
    dsimp [xiShiftE_sharp]
    rw [← riemannXi_one_sub]
    congr 1
    apply Complex.ext <;> simp; ring
  · intro γ hne
    dsimp [xiSchur]
    have hconj : xiShiftE_sharp α (γ : ℂ) = starRingEnd ℂ (xiShiftE α (γ : ℂ)) := by
      dsimp [xiShiftE, xiShiftE_sharp]
      rw [← riemannXi_conj]
      congr 1
      apply Complex.ext <;> simp
    rw [hconj, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]
  · intro σ γ
    constructor
    · dsimp [xiShiftE]
      have harg : (((1 / 2 + α : ℝ) : ℂ) - Complex.I * ((γ : ℂ) + Complex.I * (σ : ℂ))) =
          (⟨1 / 2 + (α + σ), -γ⟩ : ℂ) := by
        apply Complex.ext <;> simp; ring
      rw [harg]
      change xiNormSq (α + σ) (-γ) = xiNormSq (α + σ) γ
      exact xiNormSq_even_gamma (α + σ) γ
    · dsimp [xiShiftE_sharp]
      have harg : (((1 / 2 + α : ℝ) : ℂ) + Complex.I * ((γ : ℂ) + Complex.I * (σ : ℂ))) =
          (⟨1 / 2 + (α - σ), γ⟩ : ℂ) := by
        apply Complex.ext <;> simp; ring
      rw [harg]
      rfl

/-- THEOREM I.2 (EXACT CAYLEY-SCHUR-HERGLOTZ EQUIVALENCE):
    For every `w : ℂ` with `1 + w ≠ 0`:
      `Im(i * (1 - w) / (1 + w)) = (1 - ‖w‖^2) / ‖1 + w‖^2`,
    and consequently `‖w‖ < 1 ↔ 0 < Im(i * (1 - w) / (1 + w))`. -/
theorem cayley_schur_iff_herglotz {w : ℂ} (hw : 1 + w ≠ 0) :
    (Complex.I * ((1 - w) / (1 + w))).im = (1 - ‖w‖ ^ 2) / ‖1 + w‖ ^ 2 ∧
    (‖w‖ < 1 ↔ 0 < (Complex.I * ((1 - w) / (1 + w))).im) := by
  have him : (Complex.I * ((1 - w) / (1 + w))).im = (1 - ‖w‖ ^ 2) / ‖1 + w‖ ^ 2 := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
               Complex.one_re, Complex.one_im, zero_sub, zero_add]
    have hden : 0 < (1 + w.re) * (1 + w.re) + w.im * w.im := by
      have h := Complex.normSq_pos.mpr hw
      rw [Complex.normSq_apply] at h
      simpa [Complex.add_re, Complex.add_im] using h
    field_simp [ne_of_gt hden]
    ring
  refine ⟨him, ?_⟩
  rw [him]
  have hden_pos : 0 < ‖1 + w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  rw [div_pos_iff_of_pos_right hden_pos, sub_pos]
  constructor
  · intro hlt
    have : ‖w‖ ^ 2 < 1 ^ 2 := pow_lt_pow_left₀ hlt (norm_nonneg w) (by norm_num)
    linarith
  · intro hsq
    by_contra hge
    push Not at hge
    have : (1 : ℝ) ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
    linarith

/-- Auxiliary: Clean algebraic kernel identity `(2 * I) / w = 2 / (-I * w)`. -/
private lemma two_I_div_eq_two_div_neg_I (w : ℂ) :
    (2 * Complex.I) / w = (2 : ℂ) / (-Complex.I * w) := by
  by_cases hw : w = 0
  · rw [hw]; simp
  · have hI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    field_simp [hw, hI]
    ring_nf; rw [Complex.I_sq]

/-- THEOREM I.3 (EXACT ALL-ORDER HERMITIAN PICK-SCHUR CONGRUENCE):
    For any `n : ℕ`, any points `z : Fin n → ℂ`, any Schur values `S : Fin n → ℂ`
    with `1 + S_j ≠ 0`, Cayley transforms `M_j = i * (1 - S_j)/(1 + S_j)`, and any
    vector `c : Fin n → ℂ`, setting `ct_j = c_j / (1 + S_j)`:
      `∑_{j, k} c_j * conj(c_k) * (M_j - conj(M_k)) / (z_j - conj(z_k))
        = 2 * ∑_{j, k} ct_j * conj(ct_k) * (1 - S_j * conj(S_k)) / (-i * (z_j - conj(z_k)))`.
    Hence the Herglotz-Pick matrix of `M` is PSD if and only if the Schur-Pick matrix of `S` is PSD. -/
theorem pickMatrix_cayley_schur_congruence {n : ℕ} (z S c : Fin n → ℂ)
    (hS : ∀ j, 1 + S j ≠ 0) :
    let M : Fin n → ℂ := fun j => Complex.I * ((1 - S j) / (1 + S j))
    let ct : Fin n → ℂ := fun j => c j / (1 + S j)
    ∑ j : Fin n, ∑ k : Fin n,
      c j * starRingEnd ℂ (c k) * ((M j - starRingEnd ℂ (M k)) / (z j - starRingEnd ℂ (z k))) =
    (2 : ℂ) * ∑ j : Fin n, ∑ k : Fin n,
      ct j * starRingEnd ℂ (ct k) *
        ((1 - S j * starRingEnd ℂ (S k)) / (-Complex.I * (z j - starRingEnd ℂ (z k)))) := by
  intro M ct
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hj : 1 + S j ≠ 0 := hS j
  have hk_conj : starRingEnd ℂ (1 + S k) ≠ 0 := by
    intro h0; apply hS k; simpa using congrArg (starRingEnd ℂ) h0
  have hterm : M j - starRingEnd ℂ (M k) =
      (2 * Complex.I) * (1 - S j * starRingEnd ℂ (S k)) /
        ((1 + S j) * starRingEnd ℂ (1 + S k)) := by
    dsimp [M]
    have hk_conj' : 1 + starRingEnd ℂ (S k) ≠ 0 := by simpa [map_add, map_one] using hk_conj
    rw [map_mul, map_div₀, map_sub, map_add, map_one, Complex.conj_I]
    field_simp [hj, hk_conj']
    ring
  by_cases hzk : z j - starRingEnd ℂ (z k) = 0
  · rw [hzk]; simp
  · rw [hterm]
    dsimp [ct]
    rw [map_div₀]
    have hI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    have h1 := two_I_div_eq_two_div_neg_I (z j - starRingEnd ℂ (z k))
    have hfrac : (2 * Complex.I) * (1 - S j * starRingEnd ℂ (S k)) /
        ((1 + S j) * starRingEnd ℂ (1 + S k)) / (z j - starRingEnd ℂ (z k)) =
        (2 : ℂ) * ((1 - S j * starRingEnd ℂ (S k)) / (-Complex.I * (z j - starRingEnd ℂ (z k)))) /
        ((1 + S j) * starRingEnd ℂ (1 + S k)) := by
      field_simp [hj, hk_conj, hzk, hI] at h1 ⊢
      linear_combination (1 - S j * starRingEnd ℂ (S k)) * h1
    rw [hfrac]
    field_simp [hj, hk_conj, hzk, hI]

/-- THEOREM I.4 (UNCONDITIONAL STRIP-BOUNDARY BASELINE AT `α = 1/2`):
    For EVERY `z : ℂ` in the closed upper half-plane (`0 ≤ z.im`), `E_{1/2}(z) = ξ(1 - iz) ≠ 0`.
    Thus the boundary Schur scattering function `S_{1/2}(z) = ξ(1 + iz) / ξ(1 - iz)` is
    UNCONDITIONALLY pole-free on the entire closed upper half-plane `overline(ℍ)`. -/
theorem xiShiftE_half_zeroFree_uhp {z : ℂ} (hz : 0 ≤ z.im) :
    xiShiftE (1 / 2) z ≠ 0 := by
  dsimp [xiShiftE]
  apply riemannXi_ne_zero_of_one_le_re
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
             zero_mul, one_mul, zero_sub, sub_neg_eq_add]
  linarith

/-- THEOREM I.5A (ZERO-FREE STRIP EXCLUSION FROM HERMITE-BIEHLER INEQUALITY AT LEVEL `α`):
    For any `α > 0`, if `E_α` satisfies the strict Hermite-Biehler inequality
    `‖E_α^#(γ + iσ)‖ < ‖E_α(γ + iσ)‖` for all `σ > 0` and `γ : ℝ`, then `riemannXi`
    has NO zeros in the region `|Re(s) - 1/2| > α`. -/
theorem zeroFreeStrip_of_hermiteBiehler {α : ℝ} (_hα : 0 < α)
    (hHB : ∀ σ γ : ℝ, 0 < σ →
      ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ <
      ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖) :
    ∀ s : ℂ, α < |s.re - 1 / 2| → riemannXi s ≠ 0 := by
  intro s hs hzero
  set δ : ℝ := |s.re - 1 / 2|
  have hσ_pos : 0 < δ - α := sub_pos.mpr hs
  have hlt := hHB (δ - α) s.im hσ_pos
  have hsq : ‖xiShiftE_sharp α ((s.im : ℂ) + Complex.I * ((δ - α : ℝ) : ℂ))‖ ^ 2 <
      ‖xiShiftE α ((s.im : ℂ) + Complex.I * ((δ - α : ℝ) : ℂ))‖ ^ 2 :=
    pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
  have hpot := (xiShiftE_schwarz_and_boundary_unitary α).2.2.2 (δ - α) s.im
  rw [hpot.1, hpot.2] at hsq
  have hsum : α + (δ - α) = δ := by ring
  rw [hsum] at hsq
  have hV_zero : xiNormSq δ s.im = 0 := by
    have hs_eq : s = (⟨1 / 2 + (s.re - 1 / 2), s.im⟩ : ℂ) := by
      apply Complex.ext <;> simp
    have hV_s : xiNormSq (s.re - 1 / 2) s.im = 0 := by
      dsimp [xiNormSq]
      rw [← hs_eq, hzero, norm_zero, zero_pow (by norm_num)]
    rcases le_total 0 (s.re - 1 / 2) with hnn | hnp
    · rw [show δ = s.re - 1 / 2 from abs_of_nonneg hnn]; exact hV_s
    · rw [show δ = -(s.re - 1 / 2) from abs_of_nonpos hnp, xiNormSq_even_sigma]; exact hV_s
  rw [hV_zero] at hsq
  have hnn_lhs : 0 ≤ xiNormSq (α - (δ - α)) s.im := sq_nonneg _
  linarith

/-- THEOREM I.5B (HERMITE-BIEHLER / SCHUR HOMOTOPY REDUCTION TO `RiemannHypothesis`):
    If the strict Hermite-Biehler inequality `‖E_α^#(γ + iσ)‖ < ‖E_α(γ + iσ)‖` (equivalently
    `‖S_α(γ + iσ)‖ < 1` or `0 < Im(M_α(γ + iσ))`) survives for every `α ∈ (0, 1/2)`, then
    Mathlib4's official `RiemannHypothesis` holds UNCONDITIONALLY. -/
theorem riemannHypothesis_of_hermiteBiehler_all
    (hHB_all : ∀ α : ℝ, 0 < α → α < 1 / 2 → ∀ σ γ : ℝ, 0 < σ →
      ‖xiShiftE_sharp α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ <
      ‖xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ))‖) :
    RiemannHypothesis := by
  intro s hs htriv hone
  have hstrip : 0 < s.re ∧ s.re < 1 := by
    constructor
    · by_contra hle
      push Not at hle
      have hre1 : 1 ≤ (1 - s).re := by simp; linarith
      by_cases hs0 : s = 0
      · rw [hs0, riemannZeta_zero] at hs; norm_num at hs
      · have hgz := riemannZeta_ne_zero_of_one_le_re (s := 1 - s) hre1
        have h1s : 1 - s ≠ 0 := by intro h0; apply hone; linear_combination -h0
        have hcomp0 : completedRiemannZeta s = 0 := by
          have hrel := riemannZeta_def_of_ne_zero hs0
          rw [hrel, div_eq_zero_iff] at hs
          rcases hs with h | h
          · exact h
          · exfalso
            rw [Complex.Gammaℝ_def] at h
            have h1 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
              Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_cast; exact Real.pi_ne_zero))
            have h2 : Complex.Gamma (s / 2) ≠ 0 := by
              apply Complex.Gamma_ne_zero
              intro m hm
              cases m with
              | zero =>
                simp at hm
                exact hs0 hm
              | succ k =>
                apply htriv
                refine ⟨k, ?_⟩
                push_cast at hm ⊢
                linear_combination 2 * hm
            exact mul_ne_zero h1 h2 h
        have hcomp1 : completedRiemannZeta (1 - s) = 0 := by
          rw [completedRiemannZeta_one_sub, hcomp0]
        have hrel1 := riemannZeta_def_of_ne_zero h1s
        rw [hrel1, hcomp1, zero_div] at hgz
        exact hgz rfl
    · by_contra hge
      push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hs
  have hxi0 : riemannXi s = 0 := by
    have hnz0 : s ≠ 0 := fun h0 => by rw [h0] at hstrip; simp at hstrip
    have hcomp0 : completedRiemannZeta s = 0 := by
      have hrel := riemannZeta_def_of_ne_zero hnz0
      rw [hrel, div_eq_zero_iff] at hs
      rcases hs with h | h
      · exact h
      · exfalso
        rw [Complex.Gammaℝ_def] at h
        have h1 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
          Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_cast; exact Real.pi_ne_zero))
        have h2 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
        exact mul_ne_zero h1 h2 h
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hone
    have hval : riemannXi s = (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta s) := by
      dsimp [riemannXi]
      rw [completedRiemannZeta_eq]
      field_simp [hnz0, hs1]
      ring
    rw [hval, hcomp0, mul_zero, mul_zero]
  by_contra hne
  have hpos : 0 < |s.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt_half : |s.re - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  let α : ℝ := |s.re - 1 / 2| / 2
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hα_lt : α < 1 / 2 := by dsimp [α]; linarith
  have hα_strict : α < |s.re - 1 / 2| := by dsimp [α]; linarith
  exact zeroFreeStrip_of_hermiteBiehler hα_pos (hHB_all α hα_pos hα_lt) s hα_strict hxi0

/-- THEOREM I.6 (EXACT INFINITESIMAL HOMOTOPY LIMIT `M_α(z) / α → R_ξ(z)` AS `α → 0`):
    At every `z : ℂ` where `ξ(1/2 - i*z) ≠ 0`, the rescaled Cayley-Herglotz homotopy
    `M_α(z) / α` converges as `α → 0` (`α ≠ 0`) to the exact spectral resolvent
    `R_ξ(z) = i * (ξ'/ξ)(1/2 - i*z)`. -/
theorem xiCayley_div_alpha_tendsto_xiResolvent {z : ℂ}
    (hxi : riemannXi (1 / 2 - Complex.I * z) ≠ 0) :
    Tendsto (fun α : ℝ => xiCayley α z / (α : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 (xiResolvent z)) := by
  let w : ℂ := 1 / 2 - Complex.I * z
  have hw : riemannXi w ≠ 0 := hxi
  have hE_eq : ∀ α : ℝ, xiShiftE α z = riemannXi (w + (α : ℂ)) := by
    intro α; dsimp [xiShiftE, w]; congr 1; push_cast; ring
  have hEs_eq : ∀ α : ℝ, xiShiftE_sharp α z = riemannXi (w - (α : ℂ)) := by
    intro α
    rw [(xiShiftE_schwarz_and_boundary_unitary α).2.1 z]
    dsimp [w]; congr 1; push_cast; ring
  have hcont_w : ContinuousAt riemannXi w := riemannXi_entire.continuous.continuousAt
  have hmap_add : Tendsto (fun α : ℝ => w + (α : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 w) := by
    have h1 : Tendsto (fun α : ℝ => w + (α : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (w + (0 : ℂ))) :=
      tendsto_const_nhds.add Complex.continuous_ofReal.continuousAt.tendsto
    simp only [add_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hmap_sub : Tendsto (fun α : ℝ => w - (α : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 w) := by
    have h1 : Tendsto (fun α : ℝ => w - (α : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (w - (0 : ℂ))) :=
      tendsto_const_nhds.sub Complex.continuous_ofReal.continuousAt.tendsto
    simp only [sub_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hE_lim : Tendsto (fun α : ℝ => xiShiftE α z) (𝓝[≠] (0 : ℝ)) (𝓝 (riemannXi w)) :=
    (hcont_w.tendsto.comp hmap_add).congr fun α => (hE_eq α).symm
  have hEs_lim : Tendsto (fun α : ℝ => xiShiftE_sharp α z) (𝓝[≠] (0 : ℝ)) (𝓝 (riemannXi w)) :=
    (hcont_w.tendsto.comp hmap_sub).congr fun α => (hEs_eq α).symm
  have hd : HasDerivAt riemannXi (deriv riemannXi w) w :=
    (riemannXi_entire.differentiableAt (x := w)).hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hadd_within : Tendsto (fun α : ℝ => w + (α : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] w) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmap_add ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    intro heq
    have h0 : (α : ℂ) = 0 := by simpa using congrArg (· - w) heq
    exact hα (Complex.ofReal_eq_zero.mp h0)
  have hsub_within : Tendsto (fun α : ℝ => w - (α : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] w) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmap_sub ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    intro heq
    have h0 : (α : ℂ) = 0 := sub_eq_self.mp heq
    exact hα (Complex.ofReal_eq_zero.mp h0)
  have hq1 : Tendsto (fun α : ℝ => (riemannXi (w + (α : ℂ)) - riemannXi w) / (α : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv riemannXi w)) := by
    refine (hslope.comp hadd_within).congr fun α => ?_
    simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
  have hq2 : Tendsto (fun α : ℝ => (riemannXi w - riemannXi (w - (α : ℂ))) / (α : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv riemannXi w)) := by
    refine (hslope.comp hsub_within).congr fun α => ?_
    simp only [Function.comp_apply, slope_def_field, sub_sub_cancel_left]
    rw [div_neg, ← neg_div, neg_sub]
  have hnum : Tendsto (fun α : ℝ => (xiShiftE α z - xiShiftE_sharp α z) / (α : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 * deriv riemannXi w)) := by
    have hsum := hq1.add hq2
    rw [show deriv riemannXi w + deriv riemannXi w = 2 * deriv riemannXi w by ring] at hsum
    refine hsum.congr fun α => ?_
    rw [hE_eq α, hEs_eq α, ← add_div]; ring
  have hden : Tendsto (fun α : ℝ => xiShiftE α z + xiShiftE_sharp α z)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 * riemannXi w)) := by
    have h := hE_lim.add hEs_lim
    rwa [show riemannXi w + riemannXi w = 2 * riemannXi w by ring] at h
  have hden_nz : (2 : ℂ) * riemannXi w ≠ 0 := mul_ne_zero (by norm_num) hw
  have hquot : Tendsto (fun α : ℝ =>
      Complex.I * (((xiShiftE α z - xiShiftE_sharp α z) / (α : ℂ)) /
        (xiShiftE α z + xiShiftE_sharp α z)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (xiResolvent z)) := by
    have h := (hnum.div hden hden_nz).const_mul Complex.I
    convert h using 2
    dsimp [xiResolvent, w]
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    field_simp [h2, hw]
  have hev_E : ∀ᶠ α : ℝ in 𝓝[≠] (0 : ℝ), xiShiftE α z ≠ 0 :=
    hE_lim.eventually (isOpen_ne.mem_nhds hw)
  refine hquot.congr' ?_
  filter_upwards [hev_E, self_mem_nhdsWithin] with α hE_nz hα_nz
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα_nz
  dsimp [xiCayley, xiSchur]
  have h1 : 1 - xiShiftE_sharp α z / xiShiftE α z =
      (xiShiftE α z - xiShiftE_sharp α z) / xiShiftE α z := by
    field_simp [hE_nz]
  have h2 : 1 + xiShiftE_sharp α z / xiShiftE α z =
      (xiShiftE α z + xiShiftE_sharp α z) / xiShiftE α z := by
    field_simp [hE_nz]
  rw [h1, h2]
  by_cases hsum_nz : xiShiftE α z + xiShiftE_sharp α z = 0
  · rw [hsum_nz]; simp
  · field_simp [hE_nz, hsum_nz, hαc]

/-- Real-symmetric, functional-equation-invariant finite strip quartet product:
    `Q(s) = ∏_{m ∈ I} (((s - 1/2 - δ_m)^2 + γ_m^2) * ((s - 1/2 + δ_m)^2 + γ_m^2))`.
    Each factor carries the exact symmetric quartet `1/2 ± δ_m ± i*γ_m`. -/
noncomputable def finiteStripQuartet {ι : Type*} (I : Finset ι) (δ γ₀ : ι → ℝ) (s : ℂ) : ℂ :=
  ∏ m ∈ I, (((s - (1 / 2 : ℂ) - (δ m : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)) *
            ((s - (1 / 2 : ℂ) + (δ m : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)))

/-- Auxiliary: Strict modulus monotonicity of a single real-symmetric pair factor `(w - d)^2 + g^2`
    when `α > d` and `σ > 0`: `‖(α - σ - d + iγ)^2 + g^2‖ < ‖(α + σ - d - iγ)^2 + g^2‖`. -/
private lemma pair_factor_norm_lt {α σ d γ g : ℝ} (hd : d < α) (hσ : 0 < σ) :
    ‖(((α - σ - d : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ^ 2 + ((g : ℂ) ^ 2)‖ <
    ‖(((α + σ - d : ℝ) : ℂ) - Complex.I * (γ : ℂ)) ^ 2 + ((g : ℂ) ^ 2)‖ := by
  -- Factor (w^2 + g^2) = (w - i*g) * (w + i*g), and notice conj reverses sign of γ!
  have hf1 : ∀ a b : ℝ,
      (((a : ℂ) + Complex.I * (b : ℂ)) ^ 2 + ((g : ℂ) ^ 2)) =
      ((a : ℂ) + Complex.I * ((b - g : ℝ) : ℂ)) * ((a : ℂ) + Complex.I * ((b + g : ℝ) : ℂ)) := by
    intro a b; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hnorm_ab : ∀ a b : ℝ, ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have hlhs : ‖(((α - σ - d : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ^ 2 + ((g : ℂ) ^ 2)‖ ^ 2 =
      ((α - σ - d) ^ 2 + (γ - g) ^ 2) * ((α - σ - d) ^ 2 + (γ + g) ^ 2) := by
    rw [hf1 (α - σ - d) γ, norm_mul, mul_pow, hnorm_ab, hnorm_ab]
  have hrhs_eq : (((α + σ - d : ℝ) : ℂ) - Complex.I * (γ : ℂ)) =
      ((α + σ - d : ℝ) : ℂ) + Complex.I * ((-γ : ℝ) : ℂ) := by
    push_cast; ring
  have hrhs : ‖(((α + σ - d : ℝ) : ℂ) - Complex.I * (γ : ℂ)) ^ 2 + ((g : ℂ) ^ 2)‖ ^ 2 =
      ((α + σ - d) ^ 2 + (γ + g) ^ 2) * ((α + σ - d) ^ 2 + (γ - g) ^ 2) := by
    rw [hrhs_eq, hf1 (α + σ - d) (-γ), norm_mul, mul_pow, hnorm_ab, hnorm_ab]
    have h1 : (-γ - g) ^ 2 = (γ + g) ^ 2 := by ring
    have h2 : (-γ + g) ^ 2 = (γ - g) ^ 2 := by ring
    rw [h1, h2]
  have hsq_lt : (α - σ - d) ^ 2 < (α + σ - d) ^ 2 := by
    have hdiff : (α + σ - d) ^ 2 - (α - σ - d) ^ 2 = 4 * (α - d) * σ := by ring
    have hpos : 0 < 4 * (α - d) * σ := by nlinarith
    linarith
  have hA1 : 0 ≤ (α - σ - d) ^ 2 + (γ - g) ^ 2 := by positivity
  have hA2 : 0 ≤ (α - σ - d) ^ 2 + (γ + g) ^ 2 := by positivity
  have hB1 : 0 < (α + σ - d) ^ 2 + (γ - g) ^ 2 := by nlinarith [sq_nonneg (γ - g)]
  have hB2 : 0 < (α + σ - d) ^ 2 + (γ + g) ^ 2 := by nlinarith [sq_nonneg (γ + g)]
  have hprod_lt : ((α - σ - d) ^ 2 + (γ - g) ^ 2) * ((α - σ - d) ^ 2 + (γ + g) ^ 2) <
      ((α + σ - d) ^ 2 + (γ + g) ^ 2) * ((α + σ - d) ^ 2 + (γ - g) ^ 2) := by
    calc ((α - σ - d) ^ 2 + (γ - g) ^ 2) * ((α - σ - d) ^ 2 + (γ + g) ^ 2)
      _ < ((α + σ - d) ^ 2 + (γ - g) ^ 2) * ((α + σ - d) ^ 2 + (γ + g) ^ 2) := by
          nlinarith
      _ = ((α + σ - d) ^ 2 + (γ + g) ^ 2) * ((α + σ - d) ^ 2 + (γ - g) ^ 2) := mul_comm _ _
  have hnorm_sq : ‖(((α - σ - d : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ^ 2 + ((g : ℂ) ^ 2)‖ ^ 2 <
      ‖(((α + σ - d : ℝ) : ℂ) - Complex.I * (γ : ℂ)) ^ 2 + ((g : ℂ) ^ 2)‖ ^ 2 := by
    rw [hlhs, hrhs]; exact hprod_lt
  by_contra hge
  push Not at hge
  have := pow_le_pow_left₀ (norm_nonneg _) hge 2
  linarith

/-- THEOREM I.7 (EXACT HERMITE-BIEHLER CONVERSE & SHARP OFFSET THRESHOLD FOR STRIP QUARTETS):
    For any nonempty finite family of symmetric strip quartets `1/2 ± δ_m ± i*γ_m` with `|δ_m| ≤ Δ`,
    and for EVERY `α > Δ`, `σ > 0`, and `γ : ℝ`, the strict Hermite-Biehler inequality holds:
      `‖Q(1/2 + α - σ + i*γ)‖ < ‖Q(1/2 + α + σ - i*γ)‖`.
    In particular:
    - Whenever all zeros lie strictly inside the critical strip (`Δ < 1/2`), `α = 1/2` satisfies
      strict Hermite-Biehler UNCONDITIONALLY.
    - Whenever all zeros lie on the critical line (`Δ = 0`), strict Hermite-Biehler holds for
      EVERY `α > 0`. -/
theorem finiteStripQuartet_hermiteBiehler_exact_threshold {ι : Type*} (I : Finset ι)
    (hI : I.Nonempty) (δ γ₀ : ι → ℝ) {Δ α σ γ : ℝ}
    (hδ : ∀ m ∈ I, |δ m| ≤ Δ) (hα : Δ < α) (hσ : 0 < σ) :
    ‖finiteStripQuartet I δ γ₀ (((1 / 2 + α - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ))‖ <
    ‖finiteStripQuartet I δ γ₀ (((1 / 2 + α + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ))‖ := by
  dsimp [finiteStripQuartet]
  rw [norm_prod, norm_prod]
  have hterm_lt : ∀ m ∈ I,
      ‖(((1 / 2 + α - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) - 1 / 2 - (δ m : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)‖ *
      ‖(((1 / 2 + α - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) - 1 / 2 + (δ m : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)‖ <
      ‖(((1 / 2 + α + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ) - 1 / 2 - (δ m : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)‖ *
      ‖(((1 / 2 + α + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ) - 1 / 2 + (δ m : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)‖ := by
    intro m hm
    have hm_abs := abs_le.mp (hδ m hm)
    have h1 := pair_factor_norm_lt (α := α) (d := δ m) (g := γ₀ m) (γ := γ) (by linarith) hσ
    have h2 := pair_factor_norm_lt (α := α) (d := -(δ m)) (g := γ₀ m) (γ := γ) (by linarith) hσ
    have heq1_l : (((1 / 2 + α - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) - 1 / 2 - (δ m : ℂ)) =
        (((α - σ - δ m : ℝ) : ℂ) + Complex.I * (γ : ℂ)) := by push_cast; ring
    have heq1_r : (((1 / 2 + α + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ) - 1 / 2 - (δ m : ℂ)) =
        (((α + σ - δ m : ℝ) : ℂ) - Complex.I * (γ : ℂ)) := by push_cast; ring
    have heq2_l : (((1 / 2 + α - σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) - 1 / 2 + (δ m : ℂ)) =
        (((α - σ - -(δ m) : ℝ) : ℂ) + Complex.I * (γ : ℂ)) := by push_cast; ring
    have heq2_r : (((1 / 2 + α + σ : ℝ) : ℂ) - Complex.I * (γ : ℂ) - 1 / 2 + (δ m : ℂ)) =
        (((α + σ - -(δ m) : ℝ) : ℂ) - Complex.I * (γ : ℂ)) := by push_cast; ring
    rw [heq1_l, heq1_r, heq2_l, heq2_r]
    have hpos1 : 0 < ‖(((α + σ - δ m : ℝ) : ℂ) - Complex.I * (γ : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)‖ :=
      lt_of_le_of_lt (norm_nonneg _) h1
    have hpos2 : 0 < ‖(((α + σ - -(δ m) : ℝ) : ℂ) - Complex.I * (γ : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)‖ :=
      lt_of_le_of_lt (norm_nonneg _) h2
    nlinarith [norm_nonneg ((((α - σ - δ m : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2)),
               norm_nonneg ((((α - σ - -(δ m) : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ^ 2 + ((γ₀ m : ℂ) ^ 2))]
  have hprod_lt_aux : ∀ (S : Finset ι) (f g : ι → ℝ), S.Nonempty →
      (∀ m ∈ S, 0 ≤ f m) → (∀ m ∈ S, f m < g m) → ∏ m ∈ S, f m < ∏ m ∈ S, g m := by
    classical
    intro S f g hS hf hfg
    induction S using Finset.induction_on with
    | empty => exact absurd hS Finset.not_nonempty_empty
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_nn : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have ha_lt : f a < g a := hfg a (Finset.mem_insert_self a s)
      rcases s.eq_empty_or_nonempty with rfl | hs_ne
      · simpa using ha_lt
      · have hs_lt := ih hs_ne (fun m hm => hf m (Finset.mem_insert_of_mem hm))
          (fun m hm => hfg m (Finset.mem_insert_of_mem hm))
        have hs_nn : 0 ≤ ∏ m ∈ s, f m := Finset.prod_nonneg (fun m hm => hf m (Finset.mem_insert_of_mem hm))
        have hg_pos : 0 < g a := lt_of_le_of_lt ha_nn ha_lt
        nlinarith
  exact hprod_lt_aux I _ _ hI (fun _ _ => norm_nonneg _) (fun m hm => by
    rw [norm_mul, norm_mul]; exact hterm_lt m hm)

-- ==============================================================================
-- PART II: EXACT ROUTE A ↔ ROUTE B UNIFICATION — CAUSAL EXPONENTIAL WAVELETS
-- ==============================================================================

/-- Causal future-only exponential wavelet `g_z(u) = exp(i*z*u) * 1_{u ≥ 0}` for `z ∈ ℍ`. -/
noncomputable def causalWavelet (z : ℂ) (u : ℝ) : ℂ :=
  if 0 ≤ u then Complex.exp (Complex.I * z * (u : ℂ)) else 0

/-- Exact improper Bochner integral `∫_{u > 0} exp(c * u) du = -1 / c` for every `c : ℂ`
    with `c.re < 0`. -/
private lemma integral_Ioi_cexp_eq {c : ℂ} (hc : c.re < 0) :
    ∫ u in Ioi (0 : ℝ), Complex.exp (c * (u : ℂ)) = -(1 : ℂ) / c := by
  have hc_nz : c ≠ 0 := by intro h0; rw [h0] at hc; simp at hc
  let F : ℝ → ℂ := fun u => Complex.exp (c * (u : ℂ)) / c
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt F (Complex.exp (c * (u : ℂ))) u := by
    intro u _
    have hmul : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c u := by
      have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      simpa using hid.const_mul c
    have hexp : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
        (Complex.exp (c * (u : ℂ)) * c) u := hmul.cexp
    simpa [F, mul_div_cancel_right₀ _ hc_nz] using hexp.div_const c
  have hint : IntegrableOn (fun u : ℝ => Complex.exp (c * (u : ℂ))) (Ioi (0 : ℝ)) volume := by
    have hcont : Continuous (fun u : ℝ => Complex.exp (c * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hbound : IntegrableOn (fun u : ℝ => Real.exp (c.re * u)) (Ioi (0 : ℝ)) volume :=
      integrableOn_exp_mul_Ioi hc 0
    refine hbound.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with u
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact le_rfl
  have hlim : Tendsto F atTop (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm_eq : (fun u : ℝ => ‖F u‖) = fun u : ℝ => Real.exp (c.re * u) / ‖c‖ := by
      ext u
      dsimp [F]
      rw [norm_div, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hnorm_eq]
    have h1 : Tendsto (fun u : ℝ => c.re * u) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg hc tendsto_id
    have h2 : Tendsto (fun u : ℝ => Real.exp (c.re * u)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.div_const ‖c‖
  have hval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  dsimp [F] at hval
  simp only [mul_zero, Complex.exp_zero, zero_sub] at hval
  rw [hval, neg_div]

/-- THEOREM II.1 (EXACT LAPLACE-FOURIER TRANSFORM OF CAUSAL WAVELET = RESOLVENT CAUCHY KERNEL):
    For every `z ∈ ℍ` (`0 < z.im`) and every real frequency `t : ℝ`:
      `∫_{u > 0} g_z(u) * exp(-i * t * u) du = -i / (t - z)`. -/
theorem causalWavelet_fourier_eq_resolvent_kernel {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), causalWavelet z u * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)) =
      -Complex.I / ((t : ℂ) - z) := by
  have hcongr : EqOn (fun u : ℝ => causalWavelet z u * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ)))
      (fun u : ℝ => Complex.exp ((Complex.I * (z - (t : ℂ))) * (u : ℂ))) (Ioi (0 : ℝ)) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    dsimp [causalWavelet]
    rw [ite_eq_left_iff.mpr (fun h => absurd hu0 h), ← Complex.exp_add]
    congr 1; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
  have hre : (Complex.I * (z - (t : ℂ))).re < 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
               Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith
  rw [integral_Ioi_cexp_eq hre]
  have htz : (t : ℂ) - z ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hzt : z - (t : ℂ) ≠ 0 := fun h0 => htz (by linear_combination -h0)
  field_simp [Complex.I_ne_zero, htz, hzt]
  ring_nf; rw [Complex.I_sq]; ring

/-- THEOREM II.2 (EXACT CAUSAL WAVELET CROSS-CORRELATION KERNEL):
    For every `z_1, z_2 ∈ ℍ` (`0 < z_1.im`, `0 < z_2.im`) and every lag `u ≥ 0`:
      `∫_{v > 0} conj(g_{z_1}(v)) * g_{z_2}(v + u) dv = (i / (z_2 - conj z_1)) * exp(i * z_2 * u)`. -/
theorem causalWavelet_autocorrelation_eq {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    {u : ℝ} (hu : 0 ≤ u) :
    ∫ v in Ioi (0 : ℝ), starRingEnd ℂ (causalWavelet z₁ v) * causalWavelet z₂ (v + u) =
      (Complex.I / (z₂ - starRingEnd ℂ z₁)) * Complex.exp (Complex.I * z₂ * (u : ℂ)) := by
  have hcongr : EqOn (fun v : ℝ => starRingEnd ℂ (causalWavelet z₁ v) * causalWavelet z₂ (v + u))
      (fun v : ℝ => Complex.exp (Complex.I * z₂ * (u : ℂ)) *
        Complex.exp ((Complex.I * (z₂ - starRingEnd ℂ z₁)) * (v : ℂ))) (Ioi (0 : ℝ)) := by
    intro v hv
    have hv0 : 0 ≤ v := le_of_lt hv
    have hvu0 : 0 ≤ v + u := add_nonneg hv0 hu
    dsimp [causalWavelet]
    rw [ite_eq_left_iff.mpr (fun h => absurd hv0 h), ite_eq_left_iff.mpr (fun h => absurd hvu0 h),
        ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I,
        Complex.conj_ofReal, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
      MeasureTheory.integral_const_mul]
  have hre : (Complex.I * (z₂ - starRingEnd ℂ z₁)).re < 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
               Complex.sub_im, Complex.conj_im, sub_neg_eq_add]
    linarith
  rw [integral_Ioi_cexp_eq hre]
  have hden : z₂ - starRingEnd ℂ z₁ ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hfrac : -(1 : ℂ) / (Complex.I * (z₂ - starRingEnd ℂ z₁)) =
      Complex.I / (z₂ - starRingEnd ℂ z₁) := by
    field_simp [Complex.I_ne_zero, hden]
    ring_nf; rw [Complex.I_sq]
  rw [hfrac, mul_comm]

/-- THEOREM II.3 (GRAND ROUTE A ↔ ROUTE B UNIFICATION — CAUSAL WAVELET WEIL-PICK IDENTITY):
    For any finite real spectral family `{(γ_m, w_m)}_{m ∈ I}` (`w_m > 0`), any points
    `z : Fin n → ℂ` in `ℍ` (`0 < (z j).im`), and any complex weights `c : Fin n → ℂ`,
    evaluating the Weil spectral quadratic form on the causal exponential wavelet superposition
    `g(u) = ∑_j c_j g_{z_j}(u)` equals IDENTICALLY the Hermitian Pick-Nevanlinna quadratic form
    of the spectral resolvent `G(z) = ∑_{m ∈ I} w_m / (γ_m - z)`:
      `∑_{m ∈ I} w_m * ‖∑_j c_j * (∫_{u > 0} g_{z_j}(u) exp(-i γ_m u) du)‖^2
        = Re(∑_{j, k} conj(c_j) * c_k * (G(z_k) - conj(G(z_j))) / (z_k - conj(z_j)))`. -/
theorem weilSpectralSum_causalWavelet_eq_pickForm {ι : Type*} (I : Finset ι)
    (γ_p w : ι → ℝ) {n : ℕ} (z c : Fin n → ℂ) (hz : ∀ j, 0 < (z j).im) :
    ∑ m ∈ I, w m *
      ‖∑ j : Fin n, c j *
        (∫ u in Ioi (0 : ℝ), causalWavelet (z j) u * Complex.exp (-Complex.I * (γ_p m : ℂ) * (u : ℂ)))‖ ^ 2 =
    (∑ j : Fin n, ∑ k : Fin n,
      starRingEnd ℂ (c j) * c k *
        ((resolventCritSum I w γ_p (z k) - starRingEnd ℂ (resolventCritSum I w γ_p (z j))) /
          (z k - starRingEnd ℂ (z j)))).re := by
  have hlhs_simp : ∀ m ∈ I,
      ‖∑ j : Fin n, c j *
        (∫ u in Ioi (0 : ℝ), causalWavelet (z j) u * Complex.exp (-Complex.I * (γ_p m : ℂ) * (u : ℂ)))‖ ^ 2 =
      ‖∑ j : Fin n, c j / ((γ_p m : ℂ) - z j)‖ ^ 2 := by
    intro m _
    have hsum : (∑ j : Fin n, c j *
        (∫ u in Ioi (0 : ℝ), causalWavelet (z j) u * Complex.exp (-Complex.I * (γ_p m : ℂ) * (u : ℂ)))) =
        (-Complex.I) * (∑ j : Fin n, c j / ((γ_p m : ℂ) - z j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [causalWavelet_fourier_eq_resolvent_kernel (hz j) (γ_p m)]
      ring
    rw [hsum, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hlhs : (∑ m ∈ I, w m *
      ‖∑ j : Fin n, c j *
        (∫ u in Ioi (0 : ℝ), causalWavelet (z j) u * Complex.exp (-Complex.I * (γ_p m : ℂ) * (u : ℂ)))‖ ^ 2) =
      ∑ m ∈ I, w m * ‖∑ j : Fin n, c j / ((γ_p m : ℂ) - z j)‖ ^ 2 :=
    Finset.sum_congr rfl fun m hm => by rw [hlhs_simp m hm]
  rw [hlhs]
  -- Now prove the exact algebraic identity between the Hermitian Pick form and the spectral sum!
  have hpick_alg :
      (∑ j : Fin n, ∑ k : Fin n,
        starRingEnd ℂ (c j) * c k *
          ((resolventCritSum I w γ_p (z k) - starRingEnd ℂ (resolventCritSum I w γ_p (z j))) /
            (z k - starRingEnd ℂ (z j)))) =
      ∑ m ∈ I, (w m : ℂ) *
        (starRingEnd ℂ (∑ j : Fin n, c j / ((γ_p m : ℂ) - z j)) *
          (∑ k : Fin n, c k / ((γ_p m : ℂ) - z k))) := by
    have hterm_jk : ∀ j k : Fin n,
        starRingEnd ℂ (c j) * c k *
          ((resolventCritSum I w γ_p (z k) - starRingEnd ℂ (resolventCritSum I w γ_p (z j))) /
            (z k - starRingEnd ℂ (z j))) =
        ∑ m ∈ I, (w m : ℂ) *
          (starRingEnd ℂ (c j / ((γ_p m : ℂ) - z j)) * (c k / ((γ_p m : ℂ) - z k))) := by
      intro j k
      dsimp [resolventCritSum]
      rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hne_j : (γ_p m : ℂ) - starRingEnd ℂ (z j) ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith [hz j]
      have hne_k : (γ_p m : ℂ) - z k ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith [hz k]
      have hne_jk : z k - starRingEnd ℂ (z j) ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp at this; linarith [hz j, hz k]
      rw [map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]
      rw [map_div₀, map_sub, Complex.conj_ofReal]
      field_simp [hne_j, hne_k, hne_jk]
      ring
    calc ∑ j : Fin n, ∑ k : Fin n,
          starRingEnd ℂ (c j) * c k *
            ((resolventCritSum I w γ_p (z k) - starRingEnd ℂ (resolventCritSum I w γ_p (z j))) /
              (z k - starRingEnd ℂ (z j)))
      _ = ∑ j : Fin n, ∑ k : Fin n, ∑ m ∈ I, (w m : ℂ) *
            (starRingEnd ℂ (c j / ((γ_p m : ℂ) - z j)) * (c k / ((γ_p m : ℂ) - z k))) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hterm_jk j k
      _ = ∑ j : Fin n, ∑ m ∈ I, ∑ k : Fin n, (w m : ℂ) *
            (starRingEnd ℂ (c j / ((γ_p m : ℂ) - z j)) * (c k / ((γ_p m : ℂ) - z k))) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ m ∈ I, ∑ j : Fin n, ∑ k : Fin n, (w m : ℂ) *
            (starRingEnd ℂ (c j / ((γ_p m : ℂ) - z j)) * (c k / ((γ_p m : ℂ) - z k))) :=
          Finset.sum_comm
      _ = ∑ m ∈ I, (w m : ℂ) *
            (starRingEnd ℂ (∑ j : Fin n, c j / ((γ_p m : ℂ) - z j)) *
              (∑ k : Fin n, c k / ((γ_p m : ℂ) - z k))) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_sum, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
  rw [hpick_alg]
  -- Take real part of ∑ m ∈ I, w m * (conj S_m * S_m) = ∑ m ∈ I, w m * ‖S_m‖^2
  have hre_sum : ∀ (S : Finset ι) (F : ι → ℂ), (∑ m ∈ S, F m).re = ∑ m ∈ S, (F m).re := by
    classical
    intro S F
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Complex.add_re, ih, Finset.sum_insert ha]
  rw [hre_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcsq : ∀ u : ℂ, ((w m : ℂ) * (starRingEnd ℂ u * u)).re = w m * ‖u‖ ^ 2 := by
    intro u
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  exact (hcsq _).symm

-- ==============================================================================
-- PART III: ROUTE A — EXACT EVEN/ODD DECOUPLING & WIDER ZERO-DISCRETIZATION POSITIVITY
-- ==============================================================================

/-- Auxiliary: Symmetric interval integral of an odd complex function vanishes identically. -/
private lemma intervalIntegral_odd_zero (a : ℝ) {f : ℝ → ℂ} (hodd : ∀ u, f (-u) = -f u) :
    ∫ u in (-a)..a, f u = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg (f := f) (a := -a) (b := a)
  rw [neg_neg] at hcomp
  have hfun : (fun u : ℝ => f (-u)) = fun u : ℝ => -f u := funext hodd
  rw [hfun, intervalIntegral.integral_neg] at hcomp
  have h2 : (2 : ℂ) * (∫ u in (-a)..a, f u) = 0 := by linear_combination -hcomp
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Auxiliary: Full-line Bochner integral of an odd real function vanishes identically. -/
private lemma integral_univ_odd_zero {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t) :
    ∫ t : ℝ, f t = 0 := by
  have hcomp : ∫ t : ℝ, f (-t) = ∫ t : ℝ, f t := MeasureTheory.integral_neg_eq_self f volume
  have hfun : (fun t : ℝ => f (-t)) = fun t : ℝ => -f t := funext hodd
  rw [hfun, MeasureTheory.integral_neg] at hcomp
  linarith

/-- THEOREM III.1 (EXACT CONTINUOUS EVEN-ODD ORTHOGONAL DECOUPLING OF `weilTotal` FOR ALL `L > 0`):
    For EVERY `L > 0` (with arbitrarily many active `vonMangoldt` primes), every continuous even
    `g_e` (`g_e (-u) = g_e u`), and every continuous odd `g_o` (`g_o (-u) = -g_o u`) obeying
    Archimedean integrability:
      `W_total(L, g_e + g_o) = W_total(L, g_e) + W_total(L, g_o)`.
    Every single component — pole, Archimedean, and all prime-shift operators — decouples
    orthogonally without remainder. -/
theorem weilTotal_even_odd_decouple {L : ℝ} {g_e g_o : ℝ → ℂ}
    (hge : Continuous g_e) (hgo : Continuous g_o)
    (heven : ∀ u, g_e (-u) = g_e u) (hodd : ∀ u, g_o (-u) = -g_o u)
    (hint_e : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g_e t‖ ^ 2))
    (hint_o : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g_o t‖ ^ 2))
    (hint_c : Integrable (fun t : ℝ =>
      2 * psiArch t * (compactFourier L g_e t * starRingEnd ℂ (compactFourier L g_o t)).re)) :
    weilTotal L (fun u => g_e u + g_o u) = weilTotal L g_e + weilTotal L g_o := by
  -- 1. Pole decoupling
  have hpole_dec : weilPole L (fun u => g_e u + g_o u) = weilPole L g_e + weilPole L g_o := by
    rw [weilPole_eq_cosh_sub_sinh L (hge.fun_add hgo),
        weilPole_eq_cosh_sub_sinh L hge, weilPole_eq_cosh_sub_sinh L hgo]
    have hce_int : IntervalIntegrable (fun u => g_e u * ((Real.cosh (u / 2) : ℝ) : ℂ)) volume (-L / 2) (L / 2) :=
      (hge.mul (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
    have hco_int : IntervalIntegrable (fun u => g_o u * ((Real.cosh (u / 2) : ℝ) : ℂ)) volume (-L / 2) (L / 2) :=
      (hgo.mul (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
    have hse_int : IntervalIntegrable (fun u => g_e u * ((Real.sinh (u / 2) : ℝ) : ℂ)) volume (-L / 2) (L / 2) :=
      (hge.mul (Complex.continuous_ofReal.comp (Real.continuous_sinh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
    have hso_int : IntervalIntegrable (fun u => g_o u * ((Real.sinh (u / 2) : ℝ) : ℂ)) volume (-L / 2) (L / 2) :=
      (hgo.mul (Complex.continuous_ofReal.comp (Real.continuous_sinh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
    have hneg_half : -(L / 2) = -L / 2 := by ring
    have hco0 : ∫ u in (-L / 2)..(L / 2), g_o u * ((Real.cosh (u / 2) : ℝ) : ℂ) = 0 := by
      rw [← hneg_half]
      exact intervalIntegral_odd_zero (L / 2) fun u => by
        rw [hodd u, show -u / 2 = -(u / 2) by ring, Real.cosh_neg]; ring
    have hse0 : ∫ u in (-L / 2)..(L / 2), g_e u * ((Real.sinh (u / 2) : ℝ) : ℂ) = 0 := by
      rw [← hneg_half]
      exact intervalIntegral_odd_zero (L / 2) fun u => by
        rw [heven u, show -u / 2 = -(u / 2) by ring, Real.sinh_neg, Complex.ofReal_neg]; ring
    have hcosh_add : (∫ u in (-L / 2)..(L / 2), (g_e u + g_o u) * ((Real.cosh (u / 2) : ℝ) : ℂ)) =
        ∫ u in (-L / 2)..(L / 2), g_e u * ((Real.cosh (u / 2) : ℝ) : ℂ) := by
      have h1 : (fun u => (g_e u + g_o u) * ((Real.cosh (u / 2) : ℝ) : ℂ)) =
          fun u => g_e u * ((Real.cosh (u / 2) : ℝ) : ℂ) + g_o u * ((Real.cosh (u / 2) : ℝ) : ℂ) := by
        ext u; ring
      rw [h1, intervalIntegral.integral_add hce_int hco_int, hco0, add_zero]
    have hsinh_add : (∫ u in (-L / 2)..(L / 2), (g_e u + g_o u) * ((Real.sinh (u / 2) : ℝ) : ℂ)) =
        ∫ u in (-L / 2)..(L / 2), g_o u * ((Real.sinh (u / 2) : ℝ) : ℂ) := by
      have h1 : (fun u => (g_e u + g_o u) * ((Real.sinh (u / 2) : ℝ) : ℂ)) =
          fun u => g_e u * ((Real.sinh (u / 2) : ℝ) : ℂ) + g_o u * ((Real.sinh (u / 2) : ℝ) : ℂ) := by
        ext u; ring
      rw [h1, intervalIntegral.integral_add hse_int hso_int, hse0, zero_add]
    rw [hcosh_add, hsinh_add, hco0, hse0]
    norm_num; ring
  -- 2. Archimedean decoupling
  have hfour_add : ∀ t : ℝ, compactFourier L (fun u => g_e u + g_o u) t =
      compactFourier L g_e t + compactFourier L g_o t := by
    intro t
    dsimp [compactFourier]
    have hi1 : IntervalIntegrable (fun u : ℝ => g_e u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)))
        volume (-L / 2) (L / 2) :=
      (hge.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => g_o u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)))
        volume (-L / 2) (L / 2) :=
      (hgo.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hi1 hi2]
    refine intervalIntegral.integral_congr fun u _ => by ring
  have hfour_even : ∀ t : ℝ, compactFourier L g_e (-t) = compactFourier L g_e t := by
    intro t
    dsimp [compactFourier]
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => g_e u * Complex.exp (Complex.I * (-t : ℝ) * (u : ℂ))) (a := -L / 2) (b := L / 2)
    have hneg1 : -(L / 2) = -L / 2 := by ring
    have hneg2 : -(-L / 2) = L / 2 := by ring
    rw [hneg1, hneg2] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [heven u]
    congr 2; push_cast; ring
  have hfour_odd : ∀ t : ℝ, compactFourier L g_o (-t) = -compactFourier L g_o t := by
    intro t
    dsimp [compactFourier]
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => g_o u * Complex.exp (Complex.I * (-t : ℝ) * (u : ℂ))) (a := -L / 2) (b := L / 2)
    have hneg1 : -(L / 2) = -L / 2 := by ring
    have hneg2 : -(-L / 2) = L / 2 := by ring
    rw [hneg1, hneg2] at hcomp
    rw [← hcomp, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [hodd u, neg_mul]
    congr 3; push_cast; ring
  have harch_dec : (∫ t : ℝ, psiArch t * ‖compactFourier L (fun u => g_e u + g_o u) t‖ ^ 2) =
      (∫ t : ℝ, psiArch t * ‖compactFourier L g_e t‖ ^ 2) +
      (∫ t : ℝ, psiArch t * ‖compactFourier L g_o t‖ ^ 2) := by
    have hfun : (fun t : ℝ => psiArch t * ‖compactFourier L (fun u => g_e u + g_o u) t‖ ^ 2) =
        fun t : ℝ => (psiArch t * ‖compactFourier L g_e t‖ ^ 2 +
          psiArch t * ‖compactFourier L g_o t‖ ^ 2) +
          2 * psiArch t * (compactFourier L g_e t * starRingEnd ℂ (compactFourier L g_o t)).re := by
      ext t
      rw [hfour_add t]
      have hsq : ∀ a b : ℂ, ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (a * starRingEnd ℂ b).re := by
        intro a b
        rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
            Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
      rw [hsq]; ring
    have hint_eo : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g_e t‖ ^ 2 +
        psiArch t * ‖compactFourier L g_o t‖ ^ 2) := hint_e.add hint_o
    rw [hfun, MeasureTheory.integral_add hint_eo hint_c,
        MeasureTheory.integral_add hint_e hint_o]
    have hcross0 : ∫ t : ℝ, 2 * psiArch t *
        (compactFourier L g_e t * starRingEnd ℂ (compactFourier L g_o t)).re = 0 := by
      apply integral_univ_odd_zero
      intro t
      rw [psiArch_even, hfour_even, hfour_odd, map_neg, mul_neg, Complex.neg_re]; ring
    rw [hcross0, add_zero]
  -- 3. Prime-shift decoupling for EVERY shift δ = log n
  have hprime_dec : weilPrime L (fun u => g_e u + g_o u) = weilPrime L g_e + weilPrime L g_o := by
    dsimp [weilPrime]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← mul_add]
    congr 1
    set δ : ℝ := Real.log (n : ℝ)
    have hee : IntervalIntegrable (fun u => g_e u * starRingEnd ℂ (g_e (u - δ))) volume (-L / 2 + δ) (L / 2) :=
      (hge.mul (Complex.continuous_conj.comp (hge.comp (continuous_id.sub continuous_const)))).intervalIntegrable _ _
    have hoo : IntervalIntegrable (fun u => g_o u * starRingEnd ℂ (g_o (u - δ))) volume (-L / 2 + δ) (L / 2) :=
      (hgo.mul (Complex.continuous_conj.comp (hgo.comp (continuous_id.sub continuous_const)))).intervalIntegrable _ _
    have heo : IntervalIntegrable (fun u => g_e u * starRingEnd ℂ (g_o (u - δ))) volume (-L / 2 + δ) (L / 2) :=
      (hge.mul (Complex.continuous_conj.comp (hgo.comp (continuous_id.sub continuous_const)))).intervalIntegrable _ _
    have hoe : IntervalIntegrable (fun u => g_o u * starRingEnd ℂ (g_e (u - δ))) volume (-L / 2 + δ) (L / 2) :=
      (hgo.mul (Complex.continuous_conj.comp (hge.comp (continuous_id.sub continuous_const)))).intervalIntegrable _ _
    have hsplit_int : (∫ u in (-L / 2 + δ)..(L / 2),
        (g_e u + g_o u) * starRingEnd ℂ (g_e (u - δ) + g_o (u - δ))) =
        (∫ u in (-L / 2 + δ)..(L / 2), g_e u * starRingEnd ℂ (g_e (u - δ))) +
        (∫ u in (-L / 2 + δ)..(L / 2), g_o u * starRingEnd ℂ (g_o (u - δ))) +
        ((∫ u in (-L / 2 + δ)..(L / 2), g_e u * starRingEnd ℂ (g_o (u - δ))) +
         (∫ u in (-L / 2 + δ)..(L / 2), g_o u * starRingEnd ℂ (g_e (u - δ)))) := by
      have hfun : (fun u => (g_e u + g_o u) * starRingEnd ℂ (g_e (u - δ) + g_o (u - δ))) =
          fun u => (g_e u * starRingEnd ℂ (g_e (u - δ)) + g_o u * starRingEnd ℂ (g_o (u - δ))) +
            (g_e u * starRingEnd ℂ (g_o (u - δ)) + g_o u * starRingEnd ℂ (g_e (u - δ))) := by
        ext u; rw [map_add]; ring
      rw [hfun, intervalIntegral.integral_add (hee.add hoo) (heo.add hoe),
          intervalIntegral.integral_add hee hoo, intervalIntegral.integral_add heo hoe]
    -- Cross-shift symmetry via u ↦ δ - v: ∫ g_e(u) conj(g_o(u - δ)) = - conj(∫ g_o(v) conj(g_e(v - δ)))!
    have hcross_shift : (∫ u in (-L / 2 + δ)..(L / 2), g_e u * starRingEnd ℂ (g_o (u - δ))) =
        -starRingEnd ℂ (∫ v in (-L / 2 + δ)..(L / 2), g_o v * starRingEnd ℂ (g_e (v - δ))) := by
      have hsub := intervalIntegral.integral_comp_sub_left
        (f := fun u : ℝ => g_e u * starRingEnd ℂ (g_o (u - δ))) (a := -L / 2 + δ) (b := L / 2) δ
      have hl1 : δ - L / 2 = -L / 2 + δ := by ring
      have hl2 : δ - (-L / 2 + δ) = L / 2 := by ring
      rw [hl1, hl2] at hsub
      rw [← hsub]
      have hconj_int : starRingEnd ℂ (∫ v in (-L / 2 + δ)..(L / 2), g_o v * starRingEnd ℂ (g_e (v - δ))) =
          ∫ v in (-L / 2 + δ)..(L / 2), starRingEnd ℂ (g_o v * starRingEnd ℂ (g_e (v - δ))) := by
        symm
        exact (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hoe)
      rw [hconj_int, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun v _ => ?_
      rw [map_mul, Complex.conj_conj]
      have h1 : g_e (δ - v) = g_e (v - δ) := by rw [← heven (v - δ)]; congr 1; ring
      have h2 : g_o (δ - v - δ) = -g_o v := by rw [show δ - v - δ = -v by ring, hodd v]
      rw [h1, h2, map_neg]; ring
    rw [hsplit_int, hcross_shift, Complex.add_re, Complex.add_re, Complex.add_re,
        Complex.neg_re, Complex.conj_re]
    ring
  unfold weilTotal
  rw [hpole_dec, harch_dec, hprime_dec]
  ring

/-- THEOREM III.2A (SHARP ODD FOURIER SUPPRESSION BOUND):
    For EVERY `L ≥ 0`, every continuous ODD function `g : ℝ → ℂ` (`g (-u) = -g u`), and every `t : ℝ`:
      `‖compactFourier L g t‖^2 ≤ min L (L^3 * t^2 / 12) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem compactFourier_odd_norm_sq_le {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ} (hg : Continuous g)
    (hodd : ∀ u, g (-u) = -g u) (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤
      min L (L ^ 3 * t ^ 2 / 12) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  rw [min_mul_of_nonneg _ _ (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _))]
  refine le_min (fourierTransform_norm_sq_le_L_mul_L2 hL hg t) ?_
  -- Since g is odd, g(u) * cos(t*u) is odd so ∫ g(u) e^{i t u} du = i * ∫ g(u) sin(t*u) du!
  have hcos0 : ∫ u in (-L / 2)..(L / 2), g u * ((Real.cos (t * u) : ℝ) : ℂ) = 0 := by
    have hneg : -(L / 2) = -L / 2 := by ring
    rw [← hneg]
    exact intervalIntegral_odd_zero (L / 2) fun u => by
      rw [hodd u, mul_neg, Real.cos_neg]; ring
  have hsin_eq : compactFourier L g t =
      Complex.I * ∫ u in (-L / 2)..(L / 2), g u * ((Real.sin (t * u) : ℝ) : ℂ) := by
    dsimp [compactFourier]
    have hci : IntervalIntegrable (fun u => g u * ((Real.cos (t * u) : ℝ) : ℂ)) volume (-L / 2) (L / 2) :=
      (hg.mul (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
    have hsi : IntervalIntegrable (fun u => g u * (Complex.I * ((Real.sin (t * u) : ℝ) : ℂ))) volume (-L / 2) (L / 2) :=
      (hg.mul (continuous_const.mul (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _
    have hfun : (fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        fun u : ℝ => g u * ((Real.cos (t * u) : ℝ) : ℂ) + g u * (Complex.I * ((Real.sin (t * u) : ℝ) : ℂ)) := by
      ext u
      have hexp : Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) =
          ((Real.cos (t * u) : ℝ) : ℂ) + Complex.I * ((Real.sin (t * u) : ℝ) : ℂ) := by
        rw [show Complex.I * (t : ℂ) * (u : ℂ) = (((t * u : ℝ) : ℂ) * Complex.I) by push_cast; ring,
            Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]; ring
      rw [hexp, mul_add]
    rw [hfun, intervalIntegral.integral_add hci hsi, hcos0, zero_add]
    rw [show (fun u : ℝ => g u * (Complex.I * ((Real.sin (t * u) : ℝ) : ℂ))) =
          fun u : ℝ => Complex.I * (g u * ((Real.sin (t * u) : ℝ) : ℂ)) by ext u; ring,
        intervalIntegral.integral_const_mul]
  rw [hsin_eq, norm_mul, Complex.norm_I, one_mul]
  -- By Cauchy-Schwarz: ‖∫ g(u) sin(tu) du‖ ≤ ∫ ‖g(u)‖ |t*u| du, and (∫ f*h)^2 ≤ (∫ f^2)(∫ h^2)!
  have hab : -L / 2 ≤ L / 2 := by linarith
  have hnorm_le : ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.sin (t * u) : ℝ) : ℂ)‖ ≤
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u| := by
    calc ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.sin (t * u) : ℝ) : ℂ)‖
      _ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u * ((Real.sin (t * u) : ℝ) : ℂ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u| := by
          refine intervalIntegral.integral_mono_on hab ?_ ?_ fun u _ => ?_
          · exact (continuous_norm.comp (hg.mul (Complex.continuous_ofReal.comp
              (Real.continuous_sin.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _
          · exact ((continuous_norm.comp hg).mul (continuous_abs.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs) (norm_nonneg _)
  -- Elementary Cauchy-Schwarz on [-L/2, L/2]: (∫ ‖g(u)‖ * |t*u|)^2 ≤ (∫ ‖g‖^2) * (∫ (t*u)^2)
  have hcs : (∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u|) ^ 2 ≤
      (∫ u in (-L / 2)..(L / 2), (t * u) ^ 2) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
    set A : ℝ := ∫ u in (-L / 2)..(L / 2), (t * u) ^ 2
    set B : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u|
    set C : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
    have hquad : ∀ lam : ℝ, 0 ≤ A * lam ^ 2 + 2 * B * lam + C := by
      intro lam
      have hnn : 0 ≤ ∫ u in (-L / 2)..(L / 2), (lam * |t * u| + ‖g u‖) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
      have h1 : IntervalIntegrable (fun u : ℝ => lam ^ 2 * (t * u) ^ 2) volume (-L / 2) (L / 2) :=
        (continuous_const.mul ((continuous_const.mul continuous_id).pow 2)).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun u : ℝ => (2 * lam) * (‖g u‖ * |t * u|)) volume (-L / 2) (L / 2) :=
        (continuous_const.mul ((continuous_norm.comp hg).mul
          (continuous_abs.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
      have h3 : IntervalIntegrable (fun u : ℝ => ‖g u‖ ^ 2) volume (-L / 2) (L / 2) :=
        ((continuous_norm.comp hg).pow 2).intervalIntegrable _ _
      have hexp : (fun u : ℝ => (lam * |t * u| + ‖g u‖) ^ 2) =
          fun u : ℝ => (lam ^ 2 * (t * u) ^ 2 + (2 * lam) * (‖g u‖ * |t * u|)) + ‖g u‖ ^ 2 := by
        ext u; rw [add_sq, mul_pow, sq_abs]; ring
      rw [hexp, intervalIntegral.integral_add (h1.add h2) h3,
          intervalIntegral.integral_add h1 h2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnn
      linarith
    by_cases hA : A = 0
    · have hB0 : B = 0 := by
        by_contra hBne
        have h := hquad (-(C + 1) / (2 * B))
        rw [hA] at h
        have hsimp : 2 * B * (-(C + 1) / (2 * B)) = -(C + 1) := by field_simp [hBne]
        linarith
      rw [hA, hB0]; norm_num
    · have hA_pos : 0 < A := lt_of_le_of_ne
        (intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)) (Ne.symm hA)
      have h := hquad (-B / A)
      have hsimp : A * (-B / A) ^ 2 + 2 * B * (-B / A) + C = C - B ^ 2 / A := by
        field_simp [ne_of_gt hA_pos]; ring
      rw [hsimp] at h
      have hmul := mul_le_mul_of_nonneg_left (show B ^ 2 / A ≤ C by linarith) (le_of_lt hA_pos)
      have hca : A * (B ^ 2 / A) = B ^ 2 := mul_div_cancel₀ _ (ne_of_gt hA_pos)
      linarith
  have hint_u2 : ∫ u in (-L / 2)..(L / 2), (t * u) ^ 2 = L ^ 3 * t ^ 2 / 12 := by
    have hfun : (fun u : ℝ => (t * u) ^ 2) = fun u : ℝ => t ^ 2 * u ^ 2 := by ext u; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    ring
  rw [hint_u2] at hcs
  have hsq_le : ‖∫ u in (-L / 2)..(L / 2), g u * ((Real.sin (t * u) : ℝ) : ℂ)‖ ^ 2 ≤
      (∫ u in (-L / 2)..(L / 2), ‖g u‖ * |t * u|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
  linarith

/-- Auxiliary elementary bound: `|Real.cos x - 1| ≤ x ^ 2 / 2` for all `x : ℝ`. -/
private lemma abs_cos_sub_one_le (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  have h1 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h2 : 1 - x ^ 2 / 2 ≤ Real.cos x := by
    have h := Real.one_sub_sq_div_two_le_cos (x := x)
    linarith
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- THEOREM III.2B (SHARP EVEN ZERO-MEAN FOURIER SUPPRESSION BOUND):
    For EVERY `L ≥ 0`, every continuous EVEN function `g : ℝ → ℂ` (`g (-u) = g u`) with
    zero mean (`∫_{-L/2}^{L/2} g(u) du = 0`), and every `t : ℝ`:
      `‖compactFourier L g t‖^2 ≤ min L (L^5 * t^4 / 320) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem compactFourier_even_zeroMean_norm_sq_le {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ} (hg : Continuous g)
    (heven : ∀ u, g (-u) = g u) (hmean : ∫ u in (-L / 2)..(L / 2), g u = 0) (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤
      min L (L ^ 5 * t ^ 4 / 320) * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  rw [min_mul_of_nonneg _ _ (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _))]
  refine le_min (fourierTransform_norm_sq_le_L_mul_L2 hL hg t) ?_
  have hsin0 : ∫ u in (-L / 2)..(L / 2), g u * (Complex.I * ((Real.sin (t * u) : ℝ) : ℂ)) = 0 := by
    have hneg : -(L / 2) = -L / 2 := by ring
    rw [← hneg]
    exact intervalIntegral_odd_zero (L / 2) fun u => by
      rw [heven u, mul_neg, Real.sin_neg, Complex.ofReal_neg]; ring
  have hcos_eq : compactFourier L g t =
      ∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) - 1 : ℝ) : ℂ)) := by
    dsimp [compactFourier]
    have hci : IntervalIntegrable (fun u => g u * ((Real.cos (t * u) : ℝ) : ℂ)) volume (-L / 2) (L / 2) :=
      (hg.mul (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
    have hsi : IntervalIntegrable (fun u => g u * (Complex.I * ((Real.sin (t * u) : ℝ) : ℂ))) volume (-L / 2) (L / 2) :=
      (hg.mul (continuous_const.mul (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _
    have hfun : (fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        fun u : ℝ => g u * ((Real.cos (t * u) : ℝ) : ℂ) + g u * (Complex.I * ((Real.sin (t * u) : ℝ) : ℂ)) := by
      ext u
      have hexp : Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) =
          ((Real.cos (t * u) : ℝ) : ℂ) + Complex.I * ((Real.sin (t * u) : ℝ) : ℂ) := by
        rw [show Complex.I * (t : ℂ) * (u : ℂ) = (((t * u : ℝ) : ℂ) * Complex.I) by push_cast; ring,
            Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]; ring
      rw [hexp, mul_add]
    rw [hfun, intervalIntegral.integral_add hci hsi, hsin0, add_zero]
    have hsub : (fun u : ℝ => g u * (((Real.cos (t * u) - 1 : ℝ) : ℂ))) =
        fun u : ℝ => g u * ((Real.cos (t * u) : ℝ) : ℂ) - g u := by
      ext u; push_cast; ring
    rw [hsub, intervalIntegral.integral_sub hci (hg.intervalIntegrable _ _), hmean, sub_zero]
  rw [hcos_eq]
  have hab : -L / 2 ≤ L / 2 := by linarith
  have hnorm_le : ‖∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) - 1 : ℝ) : ℂ))‖ ≤
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ * ((t * u) ^ 2 / 2) := by
    calc ‖∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) - 1 : ℝ) : ℂ))‖
      _ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u * (((Real.cos (t * u) - 1 : ℝ) : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ * ((t * u) ^ 2 / 2) := by
          refine intervalIntegral.integral_mono_on hab ?_ ?_ fun u _ => ?_
          · exact (continuous_norm.comp (hg.mul (Complex.continuous_ofReal.comp
              ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const)))).intervalIntegrable _ _
          · exact ((continuous_norm.comp hg).mul (((continuous_const.mul continuous_id).pow 2).div_const 2)).intervalIntegrable _ _
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (abs_cos_sub_one_le (t * u)) (norm_nonneg _)
  have hcs : (∫ u in (-L / 2)..(L / 2), ‖g u‖ * ((t * u) ^ 2 / 2)) ^ 2 ≤
      (∫ u in (-L / 2)..(L / 2), ((t * u) ^ 2 / 2) ^ 2) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
    set A : ℝ := ∫ u in (-L / 2)..(L / 2), ((t * u) ^ 2 / 2) ^ 2
    set B : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ * ((t * u) ^ 2 / 2)
    set C : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
    have hquad : ∀ lam : ℝ, 0 ≤ A * lam ^ 2 + 2 * B * lam + C := by
      intro lam
      have hnn : 0 ≤ ∫ u in (-L / 2)..(L / 2), (lam * ((t * u) ^ 2 / 2) + ‖g u‖) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
      have h1 : IntervalIntegrable (fun u : ℝ => lam ^ 2 * ((t * u) ^ 2 / 2) ^ 2) volume (-L / 2) (L / 2) :=
        (continuous_const.mul ((((continuous_const.mul continuous_id).pow 2).div_const 2).pow 2)).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun u : ℝ => (2 * lam) * (‖g u‖ * ((t * u) ^ 2 / 2))) volume (-L / 2) (L / 2) :=
        (continuous_const.mul ((continuous_norm.comp hg).mul
          (((continuous_const.mul continuous_id).pow 2).div_const 2))).intervalIntegrable _ _
      have h3 : IntervalIntegrable (fun u : ℝ => ‖g u‖ ^ 2) volume (-L / 2) (L / 2) :=
        ((continuous_norm.comp hg).pow 2).intervalIntegrable _ _
      have hexp : (fun u : ℝ => (lam * ((t * u) ^ 2 / 2) + ‖g u‖) ^ 2) =
          fun u : ℝ => (lam ^ 2 * ((t * u) ^ 2 / 2) ^ 2 + (2 * lam) * (‖g u‖ * ((t * u) ^ 2 / 2))) + ‖g u‖ ^ 2 := by
        ext u; ring
      rw [hexp, intervalIntegral.integral_add (h1.add h2) h3,
          intervalIntegral.integral_add h1 h2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnn
      linarith
    by_cases hA : A = 0
    · have hB0 : B = 0 := by
        by_contra hBne
        have h := hquad (-(C + 1) / (2 * B))
        rw [hA] at h
        have hsimp : 2 * B * (-(C + 1) / (2 * B)) = -(C + 1) := by field_simp [hBne]
        linarith
      rw [hA, hB0]; norm_num
    · have hA_pos : 0 < A := lt_of_le_of_ne
        (intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)) (Ne.symm hA)
      have h := hquad (-B / A)
      have hsimp : A * (-B / A) ^ 2 + 2 * B * (-B / A) + C = C - B ^ 2 / A := by
        field_simp [ne_of_gt hA_pos]; ring
      rw [hsimp] at h
      have hmul := mul_le_mul_of_nonneg_left (show B ^ 2 / A ≤ C by linarith) (le_of_lt hA_pos)
      have hca : A * (B ^ 2 / A) = B ^ 2 := mul_div_cancel₀ _ (ne_of_gt hA_pos)
      linarith
  have hint_u4 : ∫ u in (-L / 2)..(L / 2), ((t * u) ^ 2 / 2) ^ 2 = L ^ 5 * t ^ 4 / 320 := by
    have hfun : (fun u : ℝ => ((t * u) ^ 2 / 2) ^ 2) = fun u : ℝ => (t ^ 4 / 4) * u ^ 4 := by
      ext u; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    ring
  rw [hint_u4] at hcs
  have hsq_le : ‖∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) - 1 : ℝ) : ℂ))‖ ^ 2 ≤
      (∫ u in (-L / 2)..(L / 2), ‖g u‖ * ((t * u) ^ 2 / 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
  linarith

-- Elementary rational log helpers for Theorems III.3 & III.4

/-- Universal Taylor-5 exponential upper bound for `0 ≤ x ≤ 4` via `exp x = (exp(x/4))^4`. -/
private lemma log_ge_of_exp_div4_lt {x a : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) (_ha : 0 < a)
    (ht : (1 + (x / 4) + (x / 4) ^ 2 / 2 + (x / 4) ^ 3 / 6 + (x / 4) ^ 4 / 24 +
      (x / 4) ^ 5 * (6 / (120 * 5))) ^ 4 ≤ a) :
    x ≤ Real.log a := by
  have hy0 : 0 ≤ x / 4 := by linarith
  have hy1 : x / 4 ≤ 1 := by linarith
  have h1 := exp_le_taylor_of_nonneg_le_one hy0 hy1 (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h1
  norm_num at h1
  have hpow : Real.exp x = (Real.exp (x / 4)) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp_le : Real.exp x ≤ a := by
    rw [hpow]
    calc (Real.exp (x / 4)) ^ (4 : ℕ)
      _ ≤ (1 + x / 4 + (x / 4) ^ 2 / 2 + (x / 4) ^ 3 / 6 + (x / 4) ^ 4 / 24 +
            (x / 4) ^ 5 * (6 / (120 * 5))) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) (by linarith) 4
      _ ≤ a := ht
  have := Real.log_le_log (Real.exp_pos x) hexp_le
  rwa [Real.log_exp] at this

private lemma log_1193_div_169_le : Real.log (1 + 4 * (16 : ℝ) ^ 2 / 169) ≤ 196 / 100 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := (196 / 100 : ℝ)) (by norm_num) 9
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h1
  have hlt : (1 : ℝ) + 4 * (16 : ℝ) ^ 2 / 169 ≤ Real.exp (196 / 100 : ℝ) := by
    norm_num at h1 ⊢; linarith
  have := Real.log_le_log (by positivity) hlt
  rwa [Real.log_exp] at this

private lemma log_1193_div_169_ge : (195 / 100 : ℝ) ≤ Real.log (1 + 4 * (16 : ℝ) ^ 2 / 169) := by
  apply log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity)
  norm_num

/-- Auxiliary monotonicity of `psiLb3` on `[0, ∞)`. -/
private lemma psiLb3_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    psiLb3 a ≤ psiLb3 b := by
  have hsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  dsimp [psiLb3]
  have hr : ∀ p c : ℝ, 0 < p → 0 ≤ c → (c * a ^ 2) / (p + a ^ 2) ≤ (c * b ^ 2) / (p + b ^ 2) := by
    intro p c hp hc
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcp : 0 ≤ c * p := mul_nonneg hc (le_of_lt hp)
    nlinarith
  have h0 := hr (1 / 4) 4 (by norm_num) (by norm_num)
  have h1 := hr (25 / 4) (4 / 5) (by norm_num) (by norm_num)
  have h2 := hr (81 / 4) (4 / 9) (by norm_num) (by norm_num)
  have hl : Real.log (1 + 4 * a ^ 2 / 169) ≤ Real.log (1 + 4 * b ^ 2 / 169) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- Auxiliary continuity of `psiLb3`. -/
private lemma continuous_psiLb3 : Continuous psiLb3 := by
  have hc0 : Continuous (fun t : ℝ => (4 * t ^ 2) / (1 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 / 4 + t ^ 2))
  have hc1 : Continuous (fun t : ℝ => ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 25 / 4 + t ^ 2))
  have hc2 : Continuous (fun t : ℝ => ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2)) :=
    (continuous_const.mul (continuous_pow 2)).div
      (continuous_const.add (continuous_pow 2)) (fun t => ne_of_gt (by positivity : (0 : ℝ) < 81 / 4 + t ^ 2))
  have hcl : Continuous (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)) :=
    continuous_const.mul
      (Continuous.log (continuous_const.add ((continuous_const.mul (continuous_pow 2)).div_const 169))
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + 4 * t ^ 2 / 169)))
  exact (((continuous_const.add hc0).add hc1).add hc2).add hcl

/-- Generic Archimedean cutoff lower bound at `T = 16` for any even continuous nonnegative
    Fourier envelope `K : ℝ → ℝ` obeying `‖g_hat(t)‖^2 ≤ K(t) * N2`. -/
private lemma arch_cutoff_16_ge_of_envelope {L : ℝ} (_hL : 0 < L) {g : ℝ → ℂ}
    (hplanch : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hpsi_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_even : ∀ t, K (-t) = K t)
    (hK_bd : ∀ t : ℝ, ‖compactFourier L g t‖ ^ 2 ≤ K t * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)) :
    (psiLb3 16 - (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t)) *
      (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤
    (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) := by
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hdiff_int : Integrable (fun t : ℝ => (psiArch t - psiLb3 16) * ‖compactFourier L g t‖ ^ 2) := by
    have h1 := hpsi_int.sub (hplanch.1.const_mul (psiLb3 16))
    exact h1.congr (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 =
      psiLb3 16 * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) +
        ∫ t : ℝ, (psiArch t - psiLb3 16) * ‖compactFourier L g t‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add (hplanch.1.const_mul (psiLb3 16)) hdiff_int]
    congr 1; ext t; ring
  have hlow_pt : ∀ t : ℝ,
      (Icc (-16 : ℝ) 16).indicator (fun s : ℝ => -(psiLb3 16 - psiLb3 s) * (K s * N2)) t ≤
        (psiArch t - psiLb3 16) * ‖compactFourier L g t‖ ^ 2 := by
    intro t
    by_cases ht : t ∈ Icc (-16 : ℝ) 16
    · rw [indicator_of_mem ht]
      have habs : |t| ≤ 16 := abs_le.mpr ht
      have hlb_eq : psiLb3 |t| = psiLb3 t := by dsimp [psiLb3]; rw [sq_abs]
      have hgap_nn : 0 ≤ psiLb3 16 - psiLb3 t := by
        rw [← hlb_eq]; exact sub_nonneg.mpr (psiLb3_mono_nonneg (abs_nonneg t) habs)
      have hle_arch : -(psiLb3 16 - psiLb3 t) ≤ psiArch t - psiLb3 16 := by
        linarith [psiArch_ge_psiLb3 t]
      have hfour := hK_bd t
      have hm1 : -(psiLb3 16 - psiLb3 t) * (K t * N2) ≤
          -(psiLb3 16 - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 := by nlinarith
      have hm2 : -(psiLb3 16 - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 ≤
          (psiArch t - psiLb3 16) * ‖compactFourier L g t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hle_arch (sq_nonneg _)
      linarith
    · rw [indicator_of_notMem ht]
      have habs : 16 ≤ |t| := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have h1 : psiLb3 16 ≤ psiArch 16 := psiArch_ge_psiLb3 16
      have h2 : psiArch 16 ≤ psiArch |t| := by
        rcases eq_or_lt_of_le habs with heq | hlt
        · rw [← heq]
        · exact le_of_lt (psiArch_strictMono_nonneg (by norm_num) (abs_nonneg t) hlt)
      have h3 : psiArch |t| = psiArch t := by
        rcases le_total 0 t with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, psiArch_even]
      exact mul_nonneg (by linarith) (sq_nonneg _)
  have hcont_f : Continuous (fun s : ℝ => (psiLb3 16 - psiLb3 s) * K s) :=
    (continuous_const.sub continuous_psiLb3).mul hK_cont
  have hcont_ind : Continuous (fun s : ℝ => -(psiLb3 16 - psiLb3 s) * (K s * N2)) := by
    have heq : (fun s : ℝ => -(psiLb3 16 - psiLb3 s) * (K s * N2)) =
        fun s : ℝ => (-N2) * ((psiLb3 16 - psiLb3 s) * K s) := by ext s; ring
    rw [heq]; exact continuous_const.mul hcont_f
  have hint_ind : Integrable ((Icc (-16 : ℝ) 16).indicator
      (fun s : ℝ => -(psiLb3 16 - psiLb3 s) * (K s * N2))) :=
    (hcont_ind.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hmono_int := integral_mono hint_ind hdiff_int hlow_pt
  rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-16 : ℝ) ≤ 16)] at hmono_int
  have heven_int : ∫ s in (-16 : ℝ)..16, -(psiLb3 16 - psiLb3 s) * (K s * N2) =
      -(2 * N2 * ∫ s in (0 : ℝ)..16, (psiLb3 16 - psiLb3 s) * K s) := by
    have hcomp : ∫ s in (-16 : ℝ)..0, (psiLb3 16 - psiLb3 s) * K s =
        ∫ s in (0 : ℝ)..16, (psiLb3 16 - psiLb3 s) * K s := by
      have h := intervalIntegral.integral_comp_neg
        (f := fun s : ℝ => (psiLb3 16 - psiLb3 s) * K s) (a := -16) (b := 0)
      simp only [neg_zero, neg_neg] at h
      have hf : (fun s : ℝ => (psiLb3 16 - psiLb3 (-s)) * K (-s)) =
          fun s : ℝ => (psiLb3 16 - psiLb3 s) * K s := by
        ext s; rw [hK_even s]; dsimp [psiLb3]; rw [neg_sq]
      rw [hf] at h; exact h
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hcont_f.intervalIntegrable (μ := volume) (-16) 0)
      (hcont_f.intervalIntegrable (μ := volume) 0 16)
    rw [show (fun s : ℝ => -(psiLb3 16 - psiLb3 s) * (K s * N2)) =
          fun s : ℝ => (-N2) * ((psiLb3 16 - psiLb3 s) * K s) by ext s; ring,
        intervalIntegral.integral_const_mul, ← hadd, hcomp]
    ring
  rw [heven_int] at hmono_int
  have hmul_pi := mul_le_mul_of_nonneg_left hmono_int (by positivity : 0 ≤ 1 / (2 * Real.pi))
  have htot : (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) =
      psiLb3 16 * N2 + (1 / (2 * Real.pi)) * ∫ t : ℝ, (psiArch t - psiLb3 16) * ‖compactFourier L g t‖ ^ 2 := by
    rw [hsplit, mul_add, ← hplanch.2]; ring
  have hsimp : (1 / (2 * Real.pi)) * (-(2 * N2 * ∫ s in (0 : ℝ)..16, (psiLb3 16 - psiLb3 s) * K s)) =
      -((1 / Real.pi) * ∫ s in (0 : ℝ)..16, (psiLb3 16 - psiLb3 s) * K s) * N2 := by
    field_simp [ne_of_gt Real.pi_pos]
  rw [hsimp] at hmul_pi
  linarith

/-- Elementary Riemann upper bound on a subinterval `[a, b]` (`0 ≤ a ≤ b ≤ 16`) for
    `∫_a^b (psiLb3 16 - psiLb3 t) * K t dt` when `K t ≤ U t`. -/
private lemma subint_gap_le_of_le16 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 16)
    {K U : ℝ → ℝ} (hK : Continuous K) (hU : Continuous U)
    (hKU : ∀ t ∈ Icc a b, K t ≤ U t) (hUnn : ∀ t ∈ Icc a b, 0 ≤ U t) :
    ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
      (psiLb3 16 - psiLb3 a) * ∫ t in a..b, U t := by
  have hcontL : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 t) * K t) :=
    (continuous_const.sub continuous_psiLb3).mul hK
  have hcontR : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 a) * U t) :=
    continuous_const.mul hU
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab (hcontL.intervalIntegrable _ _)
    (hcontR.intervalIntegrable _ _) fun t ht => ?_
  have hmono1 : psiLb3 a ≤ psiLb3 t := psiLb3_mono_nonneg ha ht.1
  have hmono2 : psiLb3 t ≤ psiLb3 16 := psiLb3_mono_nonneg (le_trans ha ht.1) (le_trans ht.2 hb)
  have hgap : psiLb3 16 - psiLb3 t ≤ psiLb3 16 - psiLb3 a := by linarith
  have h1 : (psiLb3 16 - psiLb3 t) * K t ≤ (psiLb3 16 - psiLb3 t) * U t :=
    mul_le_mul_of_nonneg_left (hKU t ht) (sub_nonneg.mpr hmono2)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hgap (hUnn t ht))

/-- Conservative rational lower bounds for `psiLb3 t + archimedeanWeilConst` at sample points. -/
private lemma psiLb3_diff_le_of_log_lo {a lo : ℝ}
    (hlog_lo : lo ≤ Real.log (1 + 4 * a ^ 2 / 169)) :
    psiLb3 16 - psiLb3 a ≤
      ((4 * (16 : ℝ) ^ 2) / (1 / 4 + 16 ^ 2) + ((4 / 5 : ℝ) * 16 ^ 2) / (25 / 4 + 16 ^ 2) +
       ((4 / 9 : ℝ) * 16 ^ 2) / (81 / 4 + 16 ^ 2) + (1 / 2 : ℝ) * (196 / 100)) -
      ((4 * a ^ 2) / (1 / 4 + a ^ 2) + ((4 / 5 : ℝ) * a ^ 2) / (25 / 4 + a ^ 2) +
       ((4 / 9 : ℝ) * a ^ 2) / (81 / 4 + a ^ 2) + (1 / 2 : ℝ) * lo) := by
  dsimp [psiLb3]
  linarith [log_1193_div_169_le]

/-- THEOREM III.3 (UNCONDITIONAL INFINITE-DIMENSIONAL CONTINUOUS ARITHMETIC WEIL POSITIVITY
    ON ALL ODD CONTINUOUS FUNCTIONS FOR `0 < L ≤ 3/10` — `2.4x` WIDER, ZERO DISCRETIZATION):
    For EVERY `0 < L ≤ 3/10` and EVERY continuous ODD function `g : ℝ → ℂ` on `[-L/2, L/2]`
    obeying Plancherel and Archimedean integrability:
      `W_total(L, g) ≥ (1 / 100) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem weilTotal_continuous_pos_odd_up_to_three_tenths {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 3 / 10)
    {g : ℝ → ℂ} (hg : Continuous g) (hodd : ∀ u, g (-u) = -g u)
    (hplanch : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hpsi_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2)) :
    (1 / 100 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  -- Step 1: L ≤ 3/10 < log 2 so W_prime = 0
  have hL_lt_log2 : L ≤ Real.log 2 := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have he : Real.exp (1 / 2 : ℝ) < 2 := by linarith [exp_half_lt_17_div_10]
      have := Real.log_lt_log (Real.exp_pos _) he
      rwa [Real.log_exp] at this
    linarith
  have hprime0 : weilPrime L g = 0 := weilPrime_eq_zero_of_le_log_two hL_lt_log2 g
  unfold weilTotal
  rw [hprime0, sub_zero]
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- Step 2: Apply Archimedean cutoff at T = 16 with K(t) = min L (L^3 * t^2 / 12)
  let K : ℝ → ℝ := fun t => min L (L ^ 3 * t ^ 2 / 12)
  have hK_cont : Continuous K :=
    continuous_const.min ((continuous_const.mul (continuous_pow 2)).div_const 12)
  have hK_even : ∀ t, K (-t) = K t := fun t => by dsimp [K]; rw [neg_sq]
  have harch := arch_cutoff_16_ge_of_envelope hL0 hplanch hpsi_int hK_cont hK_even
    (fun t => compactFourier_odd_norm_sq_le (le_of_lt hL0) hg hodd t)
  -- Step 3: Split ∫_0^{16} into 6 elementary subintervals: [0,1], [1,3], [3,6], [6,9], [9,12], [12,16]
  have hf_cont : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 t) * K t) :=
    (continuous_const.sub continuous_psiLb3).mul hK_cont
  have hsplit6 : ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t =
      (∫ t in (0 : ℝ)..1, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (1 : ℝ)..3, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (3 : ℝ)..6, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (6 : ℝ)..9, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (9 : ℝ)..12, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (12 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 1) (hf_cont.intervalIntegrable (μ := volume) 1 3)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 3) (hf_cont.intervalIntegrable (μ := volume) 3 6)
    have h3 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 6) (hf_cont.intervalIntegrable (μ := volume) 6 9)
    have h4 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 9) (hf_cont.intervalIntegrable (μ := volume) 9 12)
    have h5 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 12) (hf_cont.intervalIntegrable (μ := volume) 12 16)
    linarith
  have hL3 : L ^ 3 ≤ (3 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ (le_of_lt hL0) hL 3
  -- Helper for low subintervals [a, b] using U(t) = (3/10)^3 * t^2 / 12
  have hlow_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 16 →
      ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
        (psiLb3 16 - psiLb3 a) * ((3 / 10 : ℝ) ^ 3 * (b ^ 3 - a ^ 3) / 36) := by
    intro a b ha hab hb
    let U : ℝ → ℝ := fun t => (3 / 10 : ℝ) ^ 3 * t ^ 2 / 12
    have hU_cont : Continuous U := (continuous_const.mul (continuous_pow 2)).div_const 12
    have h := subint_gap_le_of_le16 (U := U) ha hab hb hK_cont hU_cont
      (fun t _ => le_trans (min_le_right _ _) (by dsimp [U]; nlinarith [sq_nonneg t]))
      (fun t _ => by dsimp [U]; positivity)
    have hint : ∫ t in a..b, U t = (3 / 10 : ℝ) ^ 3 * (b ^ 3 - a ^ 3) / 36 := by
      have hfun : U = fun t : ℝ => ((3 / 10 : ℝ) ^ 3 / 12) * t ^ 2 := by ext t; dsimp [U]; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow]; ring
    rwa [hint] at h
  -- Helper for high subintervals [a, b] using U(t) = 3/10
  have hhi_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 16 →
      ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
        (psiLb3 16 - psiLb3 a) * ((3 / 10 : ℝ) * (b - a)) := by
    intro a b ha hab hb
    have h := subint_gap_le_of_le16 (U := fun _ : ℝ => (3 / 10 : ℝ)) ha hab hb hK_cont continuous_const
      (fun t _ => le_trans (min_le_left _ _) hL) (fun _ _ => by norm_num)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  -- Rational gap upper bounds at a = 0, 1, 3, 6, 9, 12
  have hg0 : psiLb3 16 - psiLb3 0 ≤ 617 / 100 := by
    have h := psiLb3_diff_le_of_log_lo (a := 0) (lo := 0) (by norm_num)
    norm_num at h; linarith
  have hg1 : psiLb3 16 - psiLb3 1 ≤ 283 / 100 := by
    have hl : (2 / 100 : ℝ) ≤ Real.log (1 + 4 * (1 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg3 : psiLb3 16 - psiLb3 3 ≤ 158 / 100 := by
    have hl : (19 / 100 : ℝ) ≤ Real.log (1 + 4 * (3 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg6 : psiLb3 16 - psiLb3 6 ≤ 93 / 100 := by
    have hl : (61 / 100 : ℝ) ≤ Real.log (1 + 4 * (6 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg9 : psiLb3 16 - psiLb3 9 ≤ 56 / 100 := by
    have hl : (107 / 100 : ℝ) ≤ Real.log (1 + 4 * (9 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg12 : psiLb3 16 - psiLb3 12 ≤ 30 / 100 := by
    have hl : (148 / 100 : ℝ) ≤ Real.log (1 + 4 * (12 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hs01 := hlow_sub 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hs13 := hlow_sub 1 3 (by norm_num) (by norm_num) (by norm_num)
  have hs36 := hlow_sub 3 6 (by norm_num) (by norm_num) (by norm_num)
  have hs69 := hhi_sub 6 9 (by norm_num) (by norm_num) (by norm_num)
  have hs912 := hhi_sub 9 12 (by norm_num) (by norm_num) (by norm_num)
  have hs1216 := hhi_sub 12 16 (by norm_num) (by norm_num) (by norm_num)
  have hint_tot_le : ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t ≤ 199 / 100 := by
    rw [hsplit6]
    norm_num at hs01 hs13 hs36 hs69 hs912 hs1216
    linarith
  have hpen_le : (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) ≤ 634 / 1000 := by
    have hpi_lo : (31415 / 10000 : ℝ) < Real.pi := by have h := Real.pi_gt_d4; norm_num at h ⊢; linarith
    have hint_nn : 0 ≤ ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t := by
      refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
      have hm := psiLb3_mono_nonneg ht.1 ht.2
      have hKnn : 0 ≤ K t := le_min (le_of_lt hL0) (by positivity)
      exact mul_nonneg (sub_nonneg.mpr hm) hKnn
    have h1 : 1 / Real.pi ≤ 1 / (31415 / 10000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (le_of_lt hpi_lo)
    have h2 : (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) ≤
        (1 / (31415 / 10000 : ℝ)) * (199 / 100) :=
      mul_le_mul h1 hint_tot_le hint_nn (by positivity)
    have hnum : (1 / (31415 / 10000 : ℝ)) * (199 / 100) ≤ 634 / 1000 := by norm_num
    linarith
  have hpsi16_ge : (66 / 100 : ℝ) ≤ psiLb3 16 := by
    dsimp [psiLb3]
    have hC := archimedeanWeilConst_lt
    have hl := log_1193_div_169_ge
    norm_num at hl ⊢
    linarith
  -- Step 4: Pole penalty bound 2 * (sinh(L/2) - L/2) ≤ 12/1000 for L ≤ 3/10 (so L/2 ≤ 3/20)
  have hpole := weilPole_lower_bound_all (le_of_lt hL0) hg
  have hsinh_le : Real.sinh (L / 2) - L / 2 ≤ 6 / 1000 := by
    have hx0 : 0 ≤ L / 2 := by linarith
    have hx1 : L / 2 ≤ 3 / 20 := by linarith
    have hexp_p := exp_le_taylor_of_nonneg_le_one hx0 (by linarith) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp_p
    have hexp_m : 1 - L / 2 ≤ Real.exp (-(L / 2)) := by
      have := Real.add_one_le_exp (-(L / 2)); linarith
    rw [Real.sinh_eq]
    have hp2 : (L / 2) ^ 2 ≤ (3 / 20 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
    have hp3 : (L / 2) ^ 3 ≤ (3 / 20 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx1 3
    have hp4 : (L / 2) ^ 4 ≤ (3 / 20 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx1 4
    norm_num at hexp_p hp2 hp3 hp4
    linarith
  have hcoeff : (1 / 100 : ℝ) ≤ (psiLb3 16 - (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t)) -
      2 * (Real.sinh (L / 2) - L / 2) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  have hpole' : -(2 * (Real.sinh (L / 2) - L / 2) * N2) ≤ weilPole L g := by
    have h1 : -(2 * (Real.sinh (L / 2) - L / 2)) * N2 ≤ weilPole L g := hpole
    linarith
  linarith [harch, hpole', hmul]

/-- THEOREM III.4 (UNCONDITIONAL INFINITE-DIMENSIONAL CONTINUOUS ARITHMETIC WEIL POSITIVITY
    ON ALL EVEN ZERO-MEAN CONTINUOUS FUNCTIONS FOR `0 < L ≤ 4/9` — `3.56x` WIDER, ZERO DISCRETIZATION):
    For EVERY `0 < L ≤ 4/9` and EVERY continuous EVEN function `g : ℝ → ℂ` on `[-L/2, L/2]`
    with zero mean (`∫_{-L/2}^{L/2} g(u) du = 0`) obeying Plancherel and Archimedean integrability:
      `W_total(L, g) ≥ (1 / 25) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem weilTotal_continuous_pos_even_zeroMean_up_to_four_ninths {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 4 / 9)
    {g : ℝ → ℂ} (hg : Continuous g) (heven : ∀ u, g (-u) = g u)
    (hmean : ∫ u in (-L / 2)..(L / 2), g u = 0)
    (hplanch : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hpsi_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2)) :
    (1 / 25 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  -- Step 1: L ≤ 4/9 < log 2 so W_prime = 0, AND W_pole ≥ 0 by evenness!
  have hL_lt_log2 : L ≤ Real.log 2 := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have he : Real.exp (1 / 2 : ℝ) < 2 := by linarith [exp_half_lt_17_div_10]
      have := Real.log_lt_log (Real.exp_pos _) he
      rwa [Real.log_exp] at this
    linarith
  have hprime0 : weilPrime L g = 0 := weilPrime_eq_zero_of_le_log_two hL_lt_log2 g
  have hpole_nn : 0 ≤ weilPole L g := weilPole_even_nonneg L hg heven
  unfold weilTotal
  rw [hprime0, sub_zero]
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- Step 2: Apply Archimedean cutoff at T = 16 with K(t) = min L (L^5 * t^4 / 320)
  let K : ℝ → ℝ := fun t => min L (L ^ 5 * t ^ 4 / 320)
  have hK_cont : Continuous K :=
    continuous_const.min ((continuous_const.mul (continuous_pow 4)).div_const 320)
  have hK_even : ∀ t, K (-t) = K t := fun t => by
    dsimp [K]; rw [show (-t) ^ (4 : ℕ) = t ^ (4 : ℕ) by ring]
  have harch := arch_cutoff_16_ge_of_envelope hL0 hplanch hpsi_int hK_cont hK_even
    (fun t => compactFourier_even_zeroMean_norm_sq_le (le_of_lt hL0) hg heven hmean t)
  -- Step 3: Split ∫_0^{16} into 7 elementary subintervals: [0,1], [1,3], [3,6], [6,8], [8,11], [11,14], [14,16]
  have hf_cont : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 t) * K t) :=
    (continuous_const.sub continuous_psiLb3).mul hK_cont
  have hsplit7 : ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t =
      (∫ t in (0 : ℝ)..1, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (1 : ℝ)..3, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (3 : ℝ)..6, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (6 : ℝ)..8, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (8 : ℝ)..11, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (11 : ℝ)..14, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (14 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 1) (hf_cont.intervalIntegrable (μ := volume) 1 3)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 3) (hf_cont.intervalIntegrable (μ := volume) 3 6)
    have h3 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 6) (hf_cont.intervalIntegrable (μ := volume) 6 8)
    have h4 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 8) (hf_cont.intervalIntegrable (μ := volume) 8 11)
    have h5 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 11) (hf_cont.intervalIntegrable (μ := volume) 11 14)
    have h6 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 14) (hf_cont.intervalIntegrable (μ := volume) 14 16)
    linarith
  have hL5 : L ^ 5 ≤ (4 / 9 : ℝ) ^ 5 := pow_le_pow_left₀ (le_of_lt hL0) hL 5
  have hlow_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 16 →
      ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
        (psiLb3 16 - psiLb3 a) * ((4 / 9 : ℝ) ^ 5 * (b ^ 5 - a ^ 5) / 1600) := by
    intro a b ha hab hb
    let U : ℝ → ℝ := fun t => (4 / 9 : ℝ) ^ 5 * t ^ 4 / 320
    have hU_cont : Continuous U := (continuous_const.mul (continuous_pow 4)).div_const 320
    have h := subint_gap_le_of_le16 (U := U) ha hab hb hK_cont hU_cont
      (fun t _ => le_trans (min_le_right _ _) (by
        dsimp [U]
        have ht4 : 0 ≤ t ^ (4 : ℕ) := by positivity
        nlinarith))
      (fun t _ => by dsimp [U]; positivity)
    have hint : ∫ t in a..b, U t = (4 / 9 : ℝ) ^ 5 * (b ^ 5 - a ^ 5) / 1600 := by
      have hfun : U = fun t : ℝ => ((4 / 9 : ℝ) ^ 5 / 320) * t ^ 4 := by ext t; dsimp [U]; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow]; ring
    rwa [hint] at h
  have hhi_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 16 →
      ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
        (psiLb3 16 - psiLb3 a) * ((4 / 9 : ℝ) * (b - a)) := by
    intro a b ha hab hb
    have h := subint_gap_le_of_le16 (U := fun _ : ℝ => (4 / 9 : ℝ)) ha hab hb hK_cont continuous_const
      (fun t _ => le_trans (min_le_left _ _) hL) (fun _ _ => by norm_num)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hg0 : psiLb3 16 - psiLb3 0 ≤ 617 / 100 := by
    have h := psiLb3_diff_le_of_log_lo (a := 0) (lo := 0) (by norm_num)
    norm_num at h; linarith
  have hg1 : psiLb3 16 - psiLb3 1 ≤ 283 / 100 := by
    have hl : (2 / 100 : ℝ) ≤ Real.log (1 + 4 * (1 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg3 : psiLb3 16 - psiLb3 3 ≤ 158 / 100 := by
    have hl : (19 / 100 : ℝ) ≤ Real.log (1 + 4 * (3 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg6 : psiLb3 16 - psiLb3 6 ≤ 93 / 100 := by
    have hl : (61 / 100 : ℝ) ≤ Real.log (1 + 4 * (6 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg8 : psiLb3 16 - psiLb3 8 ≤ 66 / 100 := by
    have hl : (92 / 100 : ℝ) ≤ Real.log (1 + 4 * (8 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg11 : psiLb3 16 - psiLb3 11 ≤ 39 / 100 := by
    have hl : (135 / 100 : ℝ) ≤ Real.log (1 + 4 * (11 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hg14 : psiLb3 16 - psiLb3 14 ≤ 16 / 100 := by
    have hl : (172 / 100 : ℝ) ≤ Real.log (1 + 4 * (14 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_diff_le_of_log_lo hl
    norm_num at h; linarith
  have hs01 := hlow_sub 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hs13 := hlow_sub 1 3 (by norm_num) (by norm_num) (by norm_num)
  have hs36 := hlow_sub 3 6 (by norm_num) (by norm_num) (by norm_num)
  have hs68 := hlow_sub 6 8 (by norm_num) (by norm_num) (by norm_num)
  have hs811 := hhi_sub 8 11 (by norm_num) (by norm_num) (by norm_num)
  have hs1114 := hhi_sub 11 14 (by norm_num) (by norm_num) (by norm_num)
  have hs1416 := hhi_sub 14 16 (by norm_num) (by norm_num) (by norm_num)
  have hint_tot_le : ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t ≤ 194 / 100 := by
    rw [hsplit7]
    norm_num at hs01 hs13 hs36 hs68 hs811 hs1114 hs1416
    linarith
  have hpen_le : (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) ≤ 618 / 1000 := by
    have hpi_lo : (31415 / 10000 : ℝ) < Real.pi := by have h := Real.pi_gt_d4; norm_num at h ⊢; linarith
    have hint_nn : 0 ≤ ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t := by
      refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
      have hm := psiLb3_mono_nonneg ht.1 ht.2
      have hKnn : 0 ≤ K t := le_min (le_of_lt hL0) (by positivity)
      exact mul_nonneg (sub_nonneg.mpr hm) hKnn
    have h1 : 1 / Real.pi ≤ 1 / (31415 / 10000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (le_of_lt hpi_lo)
    have h2 : (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) ≤
        (1 / (31415 / 10000 : ℝ)) * (194 / 100) :=
      mul_le_mul h1 hint_tot_le hint_nn (by positivity)
    have hnum : (1 / (31415 / 10000 : ℝ)) * (194 / 100) ≤ 618 / 1000 := by norm_num
    linarith
  have hpsi16_ge : (66 / 100 : ℝ) ≤ psiLb3 16 := by
    dsimp [psiLb3]
    have hC := archimedeanWeilConst_lt
    have hl := log_1193_div_169_ge
    norm_num at hl ⊢
    linarith
  have hcoeff : (1 / 25 : ℝ) ≤ psiLb3 16 - (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  linarith [harch, hpole_nn, hmul]

-- ==============================================================================
-- PART IV: ROUTE B — EXACT ORDER-6 ALTERNATING COSINE LOWER BOUND
-- ==============================================================================

/-- Auxiliary: Nonnegativity on `[0, ∞)` from `f 0 = 0` and `0 ≤ f' x` for all `x ≥ 0`. -/
private lemma nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ}
    (h0 : f 0 = 0) (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hnn x (le_of_lt hx)
  intro x hx
  have hmem0 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (le_refl 0)
  have := hmono hmem0 hx hx
  linarith

/-- THEOREM IV.1 (EXACT ORDER-6 ALTERNATING COSINE LOWER BOUND ON ALL OF `ℝ`):
    For EVERY `x : ℝ`,
      `1 - x^2 / 2 + x^4 / 24 - x^6 / 720 ≤ cos x`.
    Together with `lightCone_even_power_parity_identity` (Module #12), this yields exact
    order-6 alternating-cosine lower bounds on the transverse Hessian `m_2(σ, γ)`. -/
theorem cos_ge_taylor_six (x : ℝ) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  suffices hpos : ∀ y : ℝ, 0 ≤ y → 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 ≤ Real.cos y by
    rcases le_total 0 x with hx | hx
    · exact hpos x hx
    · have h := hpos (-x) (by linarith)
      rw [Real.cos_neg] at h
      have heq : 1 - (-x) ^ 2 / 2 + (-x) ^ 4 / 24 - (-x) ^ 6 / 720 =
          1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by ring
      linarith
  have hpow_d : ∀ (k : ℕ) (c : ℝ) (y : ℝ),
      HasDerivAt (fun t : ℝ => t ^ k / c) (((k : ℝ) * y ^ (k - 1)) / c) y := fun k c y =>
    (hasDerivAt_pow k y).div_const c
  -- Step 1: 0 ≤ 1 - cos y
  have hf0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ 1 - Real.cos y := fun y _ => by linarith [Real.cos_le_one y]
  -- Step 2: 0 ≤ y - sin y
  have hf1 : ∀ y : ℝ, 0 ≤ y → 0 ≤ y - Real.sin y :=
    nonneg_of_hasDerivAt_nonneg (by simp)
      (fun y => ((hasDerivAt_id' y).fun_sub (Real.hasDerivAt_sin y))) hf0
  -- Step 3: 0 ≤ cos y - (1 - y^2 / 2)
  have hf2 : ∀ y : ℝ, 0 ≤ y → 0 ≤ Real.cos y - (1 - y ^ 2 / 2) :=
    nonneg_of_hasDerivAt_nonneg (by simp)
      (fun y => ((Real.hasDerivAt_cos y).fun_sub
        ((hasDerivAt_const y (1 : ℝ)).fun_sub (hpow_d 2 2 y))).congr_deriv (by norm_num; ring)) hf1
  -- Step 4: 0 ≤ sin y - (y - y^3 / 6)
  have hf3 : ∀ y : ℝ, 0 ≤ y → 0 ≤ Real.sin y - (y - y ^ 3 / 6) :=
    nonneg_of_hasDerivAt_nonneg (by simp)
      (fun y => ((Real.hasDerivAt_sin y).fun_sub
        ((hasDerivAt_id' y).fun_sub (hpow_d 3 6 y))).congr_deriv (by norm_num; ring)) hf2
  -- Step 5: 0 ≤ (1 - y^2 / 2 + y^4 / 24) - cos y
  have hf4 : ∀ y : ℝ, 0 ≤ y → 0 ≤ (1 - y ^ 2 / 2 + y ^ 4 / 24) - Real.cos y :=
    nonneg_of_hasDerivAt_nonneg (by simp)
      (fun y => ((((hasDerivAt_const y (1 : ℝ)).fun_sub (hpow_d 2 2 y)).fun_add
        (hpow_d 4 24 y)).fun_sub (Real.hasDerivAt_cos y)).congr_deriv (by norm_num; ring)) hf3
  -- Step 6: 0 ≤ (y - y^3 / 6 + y^5 / 120) - sin y
  have hf5 : ∀ y : ℝ, 0 ≤ y → 0 ≤ (y - y ^ 3 / 6 + y ^ 5 / 120) - Real.sin y :=
    nonneg_of_hasDerivAt_nonneg (by simp)
      (fun y => ((((hasDerivAt_id' y).fun_sub (hpow_d 3 6 y)).fun_add
        (hpow_d 5 120 y)).fun_sub (Real.hasDerivAt_sin y)).congr_deriv (by norm_num; ring)) hf4
  -- Step 7: 0 ≤ cos y - (1 - y^2 / 2 + y^4 / 24 - y^6 / 720)
  have hf6 : ∀ y : ℝ, 0 ≤ y → 0 ≤ Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720) :=
    nonneg_of_hasDerivAt_nonneg (by simp)
      (fun y => ((Real.hasDerivAt_cos y).fun_sub
        ((((hasDerivAt_const y (1 : ℝ)).fun_sub (hpow_d 2 2 y)).fun_add
          (hpow_d 4 24 y)).fun_sub (hpow_d 6 720 y))).congr_deriv (by norm_num; ring)) hf5
  intro y hy
  linarith [hf6 y hy]

end HermiteBiehlerHomotopyAndWeilPick
