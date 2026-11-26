/-
  ==============================================================================
  MODULE #17: COMPACTLY SUPPORTED MOMENT-ORTHOGONAL WEIL POSITIVITY CROSSING
              p = 2 AND FOR ALL HORIZONS L > 0, PRIME KURAMOTO PHASE-ORDER
              COHERENCE, GLOBAL EULER HALF-PLANE DESCENT TO sigma >= 7/2
              (Re(s) >= 4), HOPF-BLOCH SPHERE S^3 -> S^2 EMBEDDING, AND
              ACCUMULATED DE BRANGES PHASE MEMORY / POISSON-WINDING QUANTIZATION
              (LEAN 4 + MATHLIB4)
  ==============================================================================

  Author: Mariano Martín Ramírez Tamayo
  Affiliation: Independent Researcher

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):

  PART I (ROUTE A — ALL-ORDER TAYLOR ENVELOPES, FIRST PRIME-ACTIVE CONTINUOUS
          ZERO-DISCRETIZATION POSITIVITY PAST log 2, UNIVERSAL COMPACT-SUPPORT
          FINITE-CODIMENSION POSITIVITY FOR ALL L > 0, CHEBYSHEV-WEIL TRANSFER,
          AND PRIME KURAMOTO PHASE-ORDER COHERENCE):
    1. `cos_sub_taylor_even_abs_le` & `sin_sub_taylor_odd_abs_le`:
       Exact all-order alternating Taylor remainder bounds on all of `ℝ` for
       every `m : ℕ`:
         `|cos x - cosTaylorPoly m x| ≤ |x|^(2m) / (2m)!`,
         `|sin x - sinTaylorPoly m x| ≤ |x|^(2m+1) / (2m+1)!`.
    2. `compactFourier_even_moments_norm_sq_le` &
       `compactFourier_all_moments_norm_sq_le`:
       Sharp compact-support Fourier suppression envelopes for continuous
       functions on `[-L/2, L/2]` orthogonal to monomials `u^k`.
    3. `weilTotal_continuous_pos_prime_two_active_up_to_three_quarters`:
       FIRST CONTINUOUS ZERO-DISCRETIZATION ARITHMETIC WEIL POSITIVITY WITH
       PRIME `p = 2` ACTIVE (`L > log 2`):
       For EVERY `0 < L ≤ 3/4` (crossing `log 2 ≈ 0.693147`) and EVERY
       continuous even `g` on `[-L/2, L/2]` orthogonal to `{1, u^2, u^4, u^6, u^8}`
       obeying Plancherel and Archimedean integrability:
         `(1 / 20) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ W_total(L, g)`.
    4. `weilTotal_compact_finite_codimension_pos_all_L`:
       UNIVERSAL COMPACTLY SUPPORTED FINITE-CODIMENSION WEIL POSITIVITY FOR
       EVERY `L > 0` (completely resolving the Paley-Wiener obstruction):
       For EVERY horizon `L > 0` (arbitrarily large, with ALL active
       `vonMangoldt` primes `p^k ≤ e^L`) and EVERY `c > 0`, there exists an
       explicit finite codimension `m : ℕ` such that for EVERY continuous
       `g : ℝ → ℂ` on `[-L/2, L/2]` orthogonal to `{1, u, ..., u^(2m-1)}`:
         `c * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ W_total(L, g)`.
    5. `chebyshev_weil_fluctuation_transfer_bound`:
       Quantitative Chebyshev-Weil transfer inequality showing that
       `|ψ(e^u) - e^u| ≤ M * e^(Θ u)` implies
       `|E_Cheb(L, g)| ≤ 2 M ∫_0^L e^((Θ - 1/2) u) |h'(u) - (1/2) h(u)| du`,
       with horizon-uniform non-exponential factor `e^((Θ - 1/2) u) = 1`
       precisely at the critical exponent `Θ = 1/2`.
    6. `primeKuramotoOrder_bounds_and_sync_zero`:
       Weighted prime-power Kuramoto order parameter `K_L(t)` and coherence
       `r_L(t) ∈ [0, 1]`, with exact constructive synchronization `r_L(0) = 1`
       and `|Re K_L(t)| ≤ r_L(t) * B_0(L)`.

  PART II (ROUTE B — TIGHT EULER-MASCHERONI BOUND, REAL DIGAMMA INCREMENT,
           SHARP EULER L-SERIES BOUNDS AT β = 4, 5, 6, AND 2.14x GLOBAL
           ALL-γ EULER HALF-PLANE DESCENT TO σ ≥ 7/2 (Re(s) ≥ 4)):
    7. `eulerMascheroniConstant_lt_586_div_1000` &
       `complex_digamma_real_diff_ge_finset`:
       Tight rational upper bound `γ_E < 586 / 1000` from `harmonic 64 - 6 log 2`
       and finite-sum lower bound on real digamma increments `ψ(b) - ψ(a)`.
    8. `vonMangoldt_lseries_norm_le_of_four_five_six_le`:
       Uniform-in-`γ` Euler-product bounds `‖L(Λ, ⟨β, -γ⟩)‖ ≤ 68/1000` (`β ≥ 4`),
       `≤ 29/1000` (`β ≥ 5`), and `≤ 14/1000` (`β ≥ 6`).
    9. `xiResolvent_herglotz_global_euler_halfPlane_seven_halves`:
       UNCONDITIONAL 2.14x GLOBAL EULER HALF-PLANE DESCENT FOR ALL `γ ∈ ℝ`:
       For EVERY `σ ≥ 7 / 2` (`Re(s) ≥ 4`) and EVERY `γ : ℝ` (to `±∞`):
         (a) `0 < (xiResolvent (γ + iσ)).im`,
         (b) `0 < deriv (fun s => xiNormSq s γ) σ` and `0 < xiLogForce σ γ`,
         (c) `0 < (logDeriv (xiSchur σ) γ).im`,
         (d) `‖xiSchur α (γ + iσ)‖ < 1` whenever `0 < α, 0 < σ, 7/2 ≤ |σ - α|`.

  PART III (ROUTE B — HOPF-BLOCH SPHERE S^3 -> S^2 EMBEDDING OF (E_α, E_α^#),
            NORTHERN HEMISPHERE EQUIVALENCE TO RIEMANN HYPOTHESIS, ACCUMULATED
            DE BRANGES PHASE MEMORY, AND POISSON-WINDING QUANTIZATION):
   10. `hopfBloch_unit_sphere_and_equator`:
       Exact Hopf projection `(X_α, Y_α, Z_α)` onto the unit sphere `S^2`
       (`X^2 + Y^2 + Z^2 = 1`) mapping the real axis `ℝ` onto the exact
       equator `Z_α(γ) = 0, X_α(γ)^2 + Y_α(γ)^2 = 1`.
   11. `hopfBloch_northern_hemisphere_iff_schur_and_potential`:
       Exact identities `Z_α = (1 - ‖S_α‖^2)/(1 + ‖S_α‖^2) =
       (V(α+σ,γ) - V(α-σ,γ))/(V(α+σ,γ) + V(α-σ,γ))`, proving
       `0 < Z_α ↔ ‖S_α‖ < 1 ↔ V(α-σ,γ) < V(α+σ,γ)`.
   12. `riemannHypothesis_of_hopfBloch_northern_hemisphere` &
       `hopfBloch_northern_hemisphere_unconditional_euler_seven_halves`:
       Strict open Northern Hemisphere confinement `0 < Z_α` on `ℍ` for all
       `α ∈ (0, 1/2)` implies Mathlib4's official `RiemannHypothesis`;
       unconditional certification on `7/2 ≤ |σ - α|` for ALL `γ ∈ ℝ`.
   13. `deBrangesPhaseMemory_strictMono_of_pos`,
       `deBrangesPhaseMemory_pos_unconditional_euler_seven_halves`, &
       `poisson_winding_number_quantization`:
       Strictly positive accumulated de Branges phase memory on all of `ℝ` for
       `α ≥ 7/2`, and exact integer winding quantization
       `(1/π) ∫_{-∞}^{∞} ∑_{j : Fin N} η_j / ((t - γ_j)^2 + η_j^2) dt = N`.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannDipolar.GeodesicRenormalizationAndEulerJacobiPick

open Real Complex Filter Topology Set MeasureTheory
open scoped BigOperators Pointwise
open PastFutureXiKernel XiConvexityLaguerre UnconditionalCorridorAndProlate
open CertificateAndSpectralBridge WeilArchimedeanAndExplicitCorridor
open ArithmeticWeilAndWideCorridor UniversalWeilAndHerglotzResolvent
open HermiteBiehlerHomotopyAndWeilPick UniversalSolverLyapunovAndPrimeResolvent
open RouteABLimitBarriersAndDeBrangesSynthesis GeodesicRenormalizationAndEulerJacobiPick

namespace CompactMomentWeilAndHopfBlochEulerDescent

-- ==============================================================================
-- PART I: ROUTE A — ALL-ORDER TAYLOR ENVELOPES, PRIME-ACTIVE CONTINUOUS WEIL
--         POSITIVITY (L ≤ 3/4, p = 2 ACTIVE), UNIVERSAL COMPACT-SUPPORT
--         FINITE-CODIMENSION POSITIVITY FOR ALL L > 0, CHEBYSHEV-WEIL TRANSFER,
--         AND PRIME KURAMOTO PHASE-ORDER COHERENCE
-- ==============================================================================

/-- Even-order cosine Taylor polynomial `∑_{k < m} (-1)^k x^(2k) / (2k)!`. -/
noncomputable def cosTaylorPoly (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- Odd-order sine Taylor polynomial `∑_{k < m} (-1)^k x^(2k+1) / (2k+1)!`. -/
noncomputable def sinTaylorPoly (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

/-- Helper: Nonnegativity on `[0, ∞)` from `f 0 = 0` and `0 ≤ f' x` for all `x ≥ 0`. -/
private lemma nonneg_of_hasDerivAt_nonneg_Ici {f f' : ℝ → ℝ}
    (h0 : f 0 = 0) (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hnn x (le_of_lt hx)
  intro x hx
  have := hmono (Set.mem_Ici.mpr (le_refl 0)) hx hx
  linarith

/-- Helper: Derivative of `sinTaylorPoly m` equals `cosTaylorPoly m`. -/
private lemma hasDerivAt_sinTaylorPoly (m : ℕ) (x : ℝ) :
    HasDerivAt (sinTaylorPoly m) (cosTaylorPoly m x) x := by
  dsimp [sinTaylorPoly, cosTaylorPoly]
  have hterm : ∀ k ∈ Finset.range m,
      HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
        ((-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)) x := by
    intro k _
    have h1 := ((hasDerivAt_pow (2 * k + 1) x).const_mul ((-1 : ℝ) ^ k)).div_const
      (((2 * k + 1).factorial : ℝ))
    refine h1.congr_deriv ?_
    have hfac : ((2 * k + 1).factorial : ℝ) = ((2 * k + 1 : ℕ) : ℝ) * ((2 * k).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_succ (2 * k)
    have hne1 : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne2 : ((2 * k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k)
    rw [hfac, Nat.add_sub_cancel]
    field_simp [hne1, hne2]
  exact HasDerivAt.fun_sum hterm

/-- Helper: Derivative of `cosTaylorPoly (m + 1)` equals `-sinTaylorPoly m`. -/
private lemma hasDerivAt_cosTaylorPoly_succ (m : ℕ) (x : ℝ) :
    HasDerivAt (cosTaylorPoly (m + 1)) (-sinTaylorPoly m x) x := by
  have heq : cosTaylorPoly (m + 1) =
      fun t : ℝ => (1 : ℝ) + ∑ k ∈ Finset.range m,
        (-1 : ℝ) ^ (k + 1) * t ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) := by
    ext t
    dsimp [cosTaylorPoly]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    rw [add_comm]
    congr 1
  rw [heq]
  have hterm : ∀ k ∈ Finset.range m,
      HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ (k + 1) * t ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ))
        (-((-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))) x := by
    intro k _
    have h1 := ((hasDerivAt_pow (2 * k + 2) x).const_mul ((-1 : ℝ) ^ (k + 1))).div_const
      (((2 * k + 2).factorial : ℝ))
    refine h1.congr_deriv ?_
    have hfac : ((2 * k + 2).factorial : ℝ) = ((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_succ (2 * k + 1)
    have hne1 : ((2 * k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne2 : ((2 * k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
    have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    rw [hfac, hsub, pow_succ]
    field_simp [hne1, hne2]
  have hsum := (hasDerivAt_const x (1 : ℝ)).fun_add (HasDerivAt.fun_sum hterm)
  refine hsum.congr_deriv ?_
  rw [zero_add, Finset.sum_neg_distrib]
  rfl

/-- Helper: `cosTaylorPoly (m + 1) 0 = 1` and `sinTaylorPoly m 0 = 0`. -/
private lemma taylorPoly_zero (m : ℕ) :
    cosTaylorPoly (m + 1) 0 = 1 ∧ sinTaylorPoly m 0 = 0 := by
  constructor
  · dsimp [cosTaylorPoly]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    have h0 : ∑ k ∈ Finset.range m,
        (-1 : ℝ) ^ (k + 1) * (0 : ℝ) ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hne : 2 * (k + 1) ≠ 0 := by omega
      rw [zero_pow hne, mul_zero, zero_div]
    rw [h0, zero_add]
  · dsimp [sinTaylorPoly]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : 2 * k + 1 ≠ 0 := by omega
    rw [zero_pow hne, mul_zero, zero_div]

/-- THEOREM I.1 (ALL-ORDER ALTERNATING TAYLOR REMAINDER BOUNDS FOR `cos` AND `sin` ON `ℝ`):
    For EVERY `m : ℕ` and EVERY `x : ℝ`:
      `|cos x - cosTaylorPoly m x| ≤ |x|^(2m) / (2m)!` and
      `|sin x - sinTaylorPoly m x| ≤ |x|^(2m+1) / (2m+1)!`. -/
theorem cos_sin_sub_taylor_abs_le (m : ℕ) :
    (∀ x : ℝ, |Real.cos x - cosTaylorPoly m x| ≤ |x| ^ (2 * m) / ((2 * m).factorial : ℝ)) ∧
    (∀ x : ℝ, |Real.sin x - sinTaylorPoly m x| ≤ |x| ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) := by
  -- First prove both inequalities for all `x ≥ 0` by induction on `m`
  have hnonneg : ∀ n : ℕ,
      (∀ x : ℝ, 0 ≤ x → |Real.cos x - cosTaylorPoly n x| ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x → |Real.sin x - sinTaylorPoly n x| ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
    intro n
    have hstep_sin : ∀ k : ℕ,
        (∀ x : ℝ, 0 ≤ x → |Real.cos x - cosTaylorPoly k x| ≤ x ^ (2 * k) / ((2 * k).factorial : ℝ)) →
        (∀ x : ℝ, 0 ≤ x → |Real.sin x - sinTaylorPoly k x| ≤ x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by
      intro k hcos x hx
      have hd_pow : ∀ t : ℝ,
          HasDerivAt (fun u : ℝ => u ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
            (t ^ (2 * k) / ((2 * k).factorial : ℝ)) t := by
        intro t
        have h1 := (hasDerivAt_pow (2 * k + 1) t).div_const (((2 * k + 1).factorial : ℝ))
        refine h1.congr_deriv ?_
        have hfac : ((2 * k + 1).factorial : ℝ) = ((2 * k + 1 : ℕ) : ℝ) * ((2 * k).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_succ (2 * k)
        have hne1 : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hne2 : ((2 * k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k)
        rw [hfac, Nat.add_sub_cancel]; field_simp [hne1, hne2]
      have hplus : ∀ t : ℝ, 0 ≤ t →
          0 ≤ t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) - (Real.sin t - sinTaylorPoly k t) :=
        nonneg_of_hasDerivAt_nonneg_Ici
          (by simp [(taylorPoly_zero k).2])
          (fun t => (hd_pow t).fun_sub ((Real.hasDerivAt_sin t).fun_sub (hasDerivAt_sinTaylorPoly k t)))
          (fun t ht => by linarith [(abs_le.mp (hcos t ht)).2])
      have hminus : ∀ t : ℝ, 0 ≤ t →
          0 ≤ t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) + (Real.sin t - sinTaylorPoly k t) :=
        nonneg_of_hasDerivAt_nonneg_Ici
          (by simp [(taylorPoly_zero k).2])
          (fun t => (hd_pow t).fun_add ((Real.hasDerivAt_sin t).fun_sub (hasDerivAt_sinTaylorPoly k t)))
          (fun t ht => by linarith [(abs_le.mp (hcos t ht)).1])
      exact abs_le.mpr ⟨by linarith [hminus x hx], by linarith [hplus x hx]⟩
    induction n with
    | zero =>
      have hcos0 : ∀ x : ℝ, 0 ≤ x → |Real.cos x - cosTaylorPoly 0 x| ≤ x ^ (2 * 0) / ((2 * 0).factorial : ℝ) := by
        intro x _
        simp [cosTaylorPoly, Real.abs_cos_le_one]
      exact ⟨hcos0, hstep_sin 0 hcos0⟩
    | succ k ih =>
      have hcos_succ : ∀ x : ℝ, 0 ≤ x →
          |Real.cos x - cosTaylorPoly (k + 1) x| ≤ x ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) := by
        intro x hx
        have hd_pow : ∀ t : ℝ,
            HasDerivAt (fun u : ℝ => u ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ))
              (t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) t := by
          intro t
          have h1 := (hasDerivAt_pow (2 * (k + 1)) t).div_const (((2 * (k + 1)).factorial : ℝ))
          refine h1.congr_deriv ?_
          have hidx : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
          have hfac : ((2 * (k + 1)).factorial : ℝ) =
              ((2 * (k + 1) : ℕ) : ℝ) * ((2 * k + 1).factorial : ℝ) := by
            rw [hidx]; exact_mod_cast Nat.factorial_succ (2 * k + 1)
          have hne1 : ((2 * (k + 1) : ℕ) : ℝ) ≠ 0 := by positivity
          have hne2 : ((2 * k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
          have hsub : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          rw [hfac, hsub]; field_simp [hne1, hne2]
        have hplus : ∀ t : ℝ, 0 ≤ t →
            0 ≤ t ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) - (Real.cos t - cosTaylorPoly (k + 1) t) :=
          nonneg_of_hasDerivAt_nonneg_Ici
            (f' := fun t => t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) + (Real.sin t - sinTaylorPoly k t))
            (by
              have hne : 2 * (k + 1) ≠ 0 := by omega
              rw [zero_pow hne, zero_div, Real.cos_zero, (taylorPoly_zero k).1]; ring)
            (fun t => ((hd_pow t).fun_sub ((Real.hasDerivAt_cos t).fun_sub
              (hasDerivAt_cosTaylorPoly_succ k t))).congr_deriv (by ring))
            (fun t ht => by linarith [(abs_le.mp (ih.2 t ht)).1])
        have hminus : ∀ t : ℝ, 0 ≤ t →
            0 ≤ t ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) + (Real.cos t - cosTaylorPoly (k + 1) t) :=
          nonneg_of_hasDerivAt_nonneg_Ici
            (f' := fun t => t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) - (Real.sin t - sinTaylorPoly k t))
            (by
              have hne : 2 * (k + 1) ≠ 0 := by omega
              rw [zero_pow hne, zero_div, Real.cos_zero, (taylorPoly_zero k).1]; ring)
            (fun t => ((hd_pow t).fun_add ((Real.hasDerivAt_cos t).fun_sub
              (hasDerivAt_cosTaylorPoly_succ k t))).congr_deriv (by ring))
            (fun t ht => by linarith [(abs_le.mp (ih.2 t ht)).2])
        exact abs_le.mpr ⟨by linarith [hminus x hx], by linarith [hplus x hx]⟩
      exact ⟨hcos_succ, hstep_sin (k + 1) hcos_succ⟩
  -- Extend from `x ≥ 0` to all `x : ℝ` by even/odd parity
  have hcos_even : ∀ x : ℝ, cosTaylorPoly m (-x) = cosTaylorPoly m x := by
    intro x; dsimp [cosTaylorPoly]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_mul, neg_sq, ← pow_mul]
  have hsin_odd : ∀ x : ℝ, sinTaylorPoly m (-x) = -sinTaylorPoly m x := by
    intro x; dsimp [sinTaylorPoly]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul]; ring
  constructor
  · intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact (hnonneg m).1 x hx
    · rw [abs_of_nonpos hx, ← Real.cos_neg, ← hcos_even x]
      exact (hnonneg m).1 (-x) (by linarith)
  · intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; exact (hnonneg m).2 x hx
    · rw [abs_of_nonpos hx]
      have h1 : |Real.sin x - sinTaylorPoly m x| = |Real.sin (-x) - sinTaylorPoly m (-x)| := by
        rw [Real.sin_neg, hsin_odd x, ← abs_neg]; congr 1; ring
      rw [h1]
      exact (hnonneg m).2 (-x) (by linarith)

/-- Helper: Cauchy-Schwarz inequality for continuous real-valued weights on `[-L/2, L/2]`:
    `(∫_{-L/2}^{L/2} ‖g u‖ * w(u) du)^2 ≤ (∫_{-L/2}^{L/2} w(u)^2 du) * (∫_{-L/2}^{L/2} ‖g u‖^2 du)`. -/
private lemma cauchy_schwarz_interval_weight {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ} {w : ℝ → ℝ}
    (hg : Continuous g) (hw : Continuous w) :
    (∫ u in (-L / 2)..(L / 2), ‖g u‖ * w u) ^ 2 ≤
      (∫ u in (-L / 2)..(L / 2), w u ^ 2) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) := by
  have hab : -L / 2 ≤ L / 2 := by linarith
  set A : ℝ := ∫ u in (-L / 2)..(L / 2), w u ^ 2
  set B : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ * w u
  set C : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hquad : ∀ lam : ℝ, 0 ≤ A * lam ^ 2 + 2 * B * lam + C := by
    intro lam
    have hnn : 0 ≤ ∫ u in (-L / 2)..(L / 2), (lam * w u + ‖g u‖) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
    have h1 : IntervalIntegrable (fun u : ℝ => lam ^ 2 * w u ^ 2) volume (-L / 2) (L / 2) :=
      (continuous_const.mul (hw.pow 2)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun u : ℝ => (2 * lam) * (‖g u‖ * w u)) volume (-L / 2) (L / 2) :=
      (continuous_const.mul ((continuous_norm.comp hg).mul hw)).intervalIntegrable _ _
    have h3 : IntervalIntegrable (fun u : ℝ => ‖g u‖ ^ 2) volume (-L / 2) (L / 2) :=
      ((continuous_norm.comp hg).pow 2).intervalIntegrable _ _
    have hexp : (fun u : ℝ => (lam * w u + ‖g u‖) ^ 2) =
        fun u : ℝ => (lam ^ 2 * w u ^ 2 + (2 * lam) * (‖g u‖ * w u)) + ‖g u‖ ^ 2 := by
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

/-- Helper: Continuity of a finite sum of continuous functions. -/
private lemma continuous_finset_sum' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) {f : ι → α → β}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact continuous_const
  | insert a s ha ih =>
    have hrew : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      ext x; exact Finset.sum_insert ha
    rw [hrew]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Helper: Interval-integrability of a finite sum of complex functions. -/
private lemma intervalIntegrable_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun u => ∑ i ∈ s, f i u) volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact intervalIntegrable_const
  | insert k t hk ih =>
    have hr : (fun u => ∑ i ∈ insert k t, f i u) = fun u => f k u + ∑ i ∈ t, f i u := by
      ext u; exact Finset.sum_insert hk
    rw [hr]
    exact (hf k (Finset.mem_insert_self k t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Helper: Interval integral of a finite sum of interval-integrable complex functions. -/
private lemma intervalIntegral_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ u in a..b, (∑ i ∈ s, f i u) = ∑ i ∈ s, ∫ u in a..b, f i u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hrew : (fun u => ∑ i ∈ insert j s, f i u) = fun u => f j u + ∑ i ∈ s, f i u := by
      ext u; exact Finset.sum_insert hj
    have hsum_int : IntervalIntegrable (fun u => ∑ i ∈ s, f i u) volume a b :=
      intervalIntegrable_finset_sum' s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [hrew, intervalIntegral.integral_add (hf j (Finset.mem_insert_self j s)) hsum_int,
        Finset.sum_insert hj, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Helper: Universal `L`-cap `‖compactFourier L g t‖^2 ≤ L * ∫ ‖g‖^2` for any continuous `g`. -/
private lemma compactFourier_norm_sq_le_L {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℂ} (hg : Continuous g) (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤ L * ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hab : -L / 2 ≤ L / 2 := by linarith
  have hnorm_le : ‖compactFourier L g t‖ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ * (1 : ℝ) := by
    dsimp [compactFourier]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    refine intervalIntegral.integral_mono_on hab
      ((continuous_norm.comp (hg.mul (Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal)))))).intervalIntegrable _ _)
      (((continuous_norm.comp hg).mul continuous_const).intervalIntegrable _ _) fun u _ => ?_
    rw [norm_mul, mul_one]
    have hunit : ‖Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))‖ = 1 := by
      have harg : Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [hunit, mul_one]
  have hcs := cauchy_schwarz_interval_weight hL hg continuous_const (w := fun _ => (1 : ℝ))
  have hint1 : ∫ _u in (-L / 2)..(L / 2), (1 : ℝ) ^ 2 = L := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hint1] at hcs
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2) hcs

/-- THEOREM I.2A (ALL-ORDER COMPACT-SUPPORT FOURIER SUPPRESSION FOR EVEN MOMENT-ORTHOGONAL FUNCTIONS):
    For EVERY `L ≥ 0`, EVERY `m : ℕ`, and EVERY continuous even function `g : ℝ → ℂ` on `[-L/2, L/2]`
    with `m` vanishing even moments (`∀ k < m, ∫_{-L/2}^{L/2} u^(2k) * g(u) du = 0`):
      `‖compactFourier L g t‖^2 ≤
        min L (L^(4m+1) * t^(4m) / ((4m+1) * 2^(4m) * ((2m)!)^2)) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem compactFourier_even_moments_norm_sq_le {L : ℝ} (hL : 0 ≤ L) (m : ℕ)
    {g : ℝ → ℂ} (hg : Continuous g) (heven : ∀ u, g (-u) = g u)
    (hmom : ∀ k : ℕ, k < m → ∫ u in (-L / 2)..(L / 2), ((u ^ (2 * k) : ℝ) : ℂ) * g u = 0)
    (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤
      min L (L ^ (4 * m + 1) * t ^ (4 * m) /
        (((4 * m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * m) * (((2 * m).factorial : ℝ) ^ 2))) *
      ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  rw [min_mul_of_nonneg _ _ (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _))]
  refine le_min (compactFourier_norm_sq_le_L hL hg t) ?_
  have hab : -L / 2 ≤ L / 2 := by linarith
  -- Step 1: By evenness of `g`, `compactFourier L g t = ∫ g(u) * cos(t*u) du`
  have hsin_zero : ∫ u in (-L / 2)..(L / 2), g u * (((Real.sin (t * u) : ℝ) : ℂ)) = 0 := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => g u * (((Real.sin (t * u) : ℝ) : ℂ))) (a := -L / 2) (b := L / 2)
    have harg : (fun u : ℝ => g (-u) * (((Real.sin (t * -u) : ℝ) : ℂ))) =
        fun u => -(g u * (((Real.sin (t * u) : ℝ) : ℂ))) := by
      ext u; rw [heven u, mul_neg, Real.sin_neg, Complex.ofReal_neg]; ring
    rw [harg, intervalIntegral.integral_neg] at hcomp
    have hlim1 : -(-L / 2) = L / 2 := by ring
    have hlim2 : -(L / 2) = -L / 2 := by ring
    rw [hlim1, hlim2] at hcomp
    have h2 : (2 : ℂ) * ∫ u in (-L / 2)..(L / 2), g u * (((Real.sin (t * u) : ℝ) : ℂ)) = 0 := by
      linear_combination -hcomp
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hcos_eq : compactFourier L g t =
      ∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) : ℝ) : ℂ)) := by
    dsimp [compactFourier]
    have hsplit : (fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        fun u => g u * (((Real.cos (t * u) : ℝ) : ℂ)) +
          Complex.I * (g u * (((Real.sin (t * u) : ℝ) : ℂ))) := by
      ext u
      have harg : Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    have hcont_c : Continuous (fun u : ℝ => g u * (((Real.cos (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hcont_s : Continuous (fun u : ℝ => g u * (((Real.sin (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
    have hcont_is : Continuous (fun u : ℝ => Complex.I * (g u * (((Real.sin (t * u) : ℝ) : ℂ)))) :=
      continuous_const.mul hcont_s
    rw [hsplit, intervalIntegral.integral_add (hcont_c.intervalIntegrable (μ := volume) _ _)
        (hcont_is.intervalIntegrable (μ := volume) _ _),
        intervalIntegral.integral_const_mul, hsin_zero, mul_zero, add_zero]
  -- Step 2: Subtract `cosTaylorPoly m (t * u)` using vanishing moments
  have hpoly_zero : ∫ u in (-L / 2)..(L / 2), g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ)) = 0 := by
    have hrew : (fun u : ℝ => g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ))) =
        fun u => ∑ k ∈ Finset.range m,
          (((((-1 : ℝ) ^ k * t ^ (2 * k) / ((2 * k).factorial : ℝ)) : ℝ) : ℂ)) *
            (((u ^ (2 * k) : ℝ) : ℂ) * g u) := by
      ext u; dsimp [cosTaylorPoly]; rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow]; push_cast; ring
    rw [hrew, intervalIntegral_finset_sum']
    · refine Finset.sum_eq_zero fun k hk => ?_
      rw [intervalIntegral.integral_const_mul, hmom k (Finset.mem_range.mp hk), mul_zero]
    · intro k _
      exact (continuous_const.mul ((Complex.continuous_ofReal.comp (continuous_pow (2 * k))).mul hg)).intervalIntegrable _ _
  have hsub_eq : compactFourier L g t =
      ∫ u in (-L / 2)..(L / 2), g u * (((Real.cos (t * u) - cosTaylorPoly m (t * u) : ℝ) : ℂ)) := by
    have hcont_c : Continuous (fun u : ℝ => g u * (((Real.cos (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hcont_p : Continuous (fun u : ℝ => g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ))) := by
      refine hg.mul (Complex.continuous_ofReal.comp ?_)
      dsimp [cosTaylorPoly]
      exact continuous_finset_sum' _ fun k _ =>
        ((continuous_const.mul ((continuous_const.mul continuous_id).pow (2 * k))).div_const _)
    have hpt : (fun u : ℝ => g u * (((Real.cos (t * u) - cosTaylorPoly m (t * u) : ℝ) : ℂ))) =
        fun u => g u * (((Real.cos (t * u) : ℝ) : ℂ)) - g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ)) := by
      ext u; push_cast; ring
    rw [hpt, intervalIntegral.integral_sub (hcont_c.intervalIntegrable _ _) (hcont_p.intervalIntegrable _ _),
        hpoly_zero, sub_zero, hcos_eq]
  -- Step 3: Pointwise Taylor remainder bound + Cauchy-Schwarz!
  let w : ℝ → ℝ := fun u => (t * u) ^ (2 * m) / ((2 * m).factorial : ℝ)
  have hw_cont : Continuous w := ((continuous_const.mul continuous_id).pow (2 * m)).div_const _
  have hnorm_le : ‖compactFourier L g t‖ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ * w u := by
    rw [hsub_eq]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    have hcont_l : Continuous (fun u : ℝ => ‖g u * (((Real.cos (t * u) - cosTaylorPoly m (t * u) : ℝ) : ℂ))‖) := by
      refine continuous_norm.comp (hg.mul (Complex.continuous_ofReal.comp ?_))
      exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub
        (continuous_finset_sum' _ fun k _ =>
          (continuous_const.mul ((continuous_const.mul continuous_id).pow (2 * k))).div_const _)
    refine intervalIntegral.integral_mono_on hab (hcont_l.intervalIntegrable _ _)
      (((continuous_norm.comp hg).mul hw_cont).intervalIntegrable _ _) fun u _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hrem := (cos_sin_sub_taylor_abs_le m).1 (t * u)
    have habs_pow : |t * u| ^ (2 * m) = (t * u) ^ (2 * m) := by
      rw [pow_mul, sq_abs, ← pow_mul]
    rw [habs_pow] at hrem
    exact mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
  have hcs := cauchy_schwarz_interval_weight hL hg hw_cont
  have hint_w : ∫ u in (-L / 2)..(L / 2), w u ^ 2 =
      L ^ (4 * m + 1) * t ^ (4 * m) /
        (((4 * m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * m) * (((2 * m).factorial : ℝ) ^ 2)) := by
    have hfun : (fun u : ℝ => w u ^ 2) =
        fun u => (t ^ (4 * m) / (((2 * m).factorial : ℝ) ^ 2)) * u ^ (4 * m) := by
      ext u; dsimp [w]; rw [div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      have h4 : 2 * m * 2 = 4 * m := by omega
      rw [h4]; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    have hodd : (-L / 2) ^ (4 * m + 1) = -(L / 2) ^ (4 * m + 1) := by
      rw [show -L / 2 = -(L / 2) by ring, Odd.neg_pow ⟨2 * m, by omega⟩]
    rw [hodd, sub_neg_eq_add, div_pow, pow_succ (2 : ℝ) (4 * m)]
    have hne_f : ((2 * m).factorial : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero (2 * m))
    have hne_c : ((4 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne_2 : (2 : ℝ) ^ (4 * m) ≠ 0 := by positivity
    push_cast
    field_simp [hne_f, hne_c, hne_2]
    ring
  rw [hint_w] at hcs
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2) hcs

/-- THEOREM I.2B (UNIVERSAL COMPACT-SUPPORT FOURIER SUPPRESSION FOR ARBITRARY `2m`-MOMENT-ORTHOGONAL
    CONTINUOUS FUNCTIONS — NO PARITY RESTRICTION):
    For EVERY `L ≥ 0`, EVERY `m : ℕ`, and EVERY continuous `g : ℝ → ℂ` on `[-L/2, L/2]`
    with `∀ k < 2*m, ∫_{-L/2}^{L/2} u^k * g(u) du = 0`:
      `‖compactFourier L g t‖^2 ≤
        L * ((|t| * (L / 2))^(2m) / (2m)! + (|t| * (L / 2))^(2m+1) / (2m+1)!)^2 *
          ∫_{-L/2}^{L/2} ‖g(u)‖^2 du`. -/
theorem compactFourier_all_moments_norm_sq_le {L : ℝ} (hL : 0 ≤ L) (m : ℕ)
    {g : ℝ → ℂ} (hg : Continuous g)
    (hmom : ∀ k : ℕ, k < 2 * m → ∫ u in (-L / 2)..(L / 2), ((u ^ k : ℝ) : ℂ) * g u = 0)
    (t : ℝ) :
    ‖compactFourier L g t‖ ^ 2 ≤
      L * ((|t| * (L / 2)) ^ (2 * m) / ((2 * m).factorial : ℝ) +
           (|t| * (L / 2)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2 *
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2 := by
  have hab : -L / 2 ≤ L / 2 := by linarith
  -- Subtract `cosTaylorPoly m (t * u) + I * sinTaylorPoly m (t * u)` (all degrees < 2m!)
  have hcos_zero : ∫ u in (-L / 2)..(L / 2), g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ)) = 0 := by
    have hrew : (fun u : ℝ => g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ))) =
        fun u => ∑ k ∈ Finset.range m,
          (((((-1 : ℝ) ^ k * t ^ (2 * k) / ((2 * k).factorial : ℝ)) : ℝ) : ℂ)) *
            (((u ^ (2 * k) : ℝ) : ℂ) * g u) := by
      ext u; dsimp [cosTaylorPoly]; rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_; rw [mul_pow]; push_cast; ring
    rw [hrew, intervalIntegral_finset_sum']
    · refine Finset.sum_eq_zero fun k hk => ?_
      have hlt : 2 * k < 2 * m := by have := Finset.mem_range.mp hk; omega
      rw [intervalIntegral.integral_const_mul, hmom (2 * k) hlt, mul_zero]
    · intro k _
      exact (continuous_const.mul ((Complex.continuous_ofReal.comp (continuous_pow (2 * k))).mul hg)).intervalIntegrable _ _
  have hsin_zero : ∫ u in (-L / 2)..(L / 2), g u * (((sinTaylorPoly m (t * u) : ℝ) : ℂ)) = 0 := by
    have hrew : (fun u : ℝ => g u * (((sinTaylorPoly m (t * u) : ℝ) : ℂ))) =
        fun u => ∑ k ∈ Finset.range m,
          (((((-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) : ℝ) : ℂ)) *
            (((u ^ (2 * k + 1) : ℝ) : ℂ) * g u) := by
      ext u; dsimp [sinTaylorPoly]; rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_; rw [mul_pow]; push_cast; ring
    rw [hrew, intervalIntegral_finset_sum']
    · refine Finset.sum_eq_zero fun k hk => ?_
      have hlt : 2 * k + 1 < 2 * m := by have := Finset.mem_range.mp hk; omega
      rw [intervalIntegral.integral_const_mul, hmom (2 * k + 1) hlt, mul_zero]
    · intro k _
      exact (continuous_const.mul ((Complex.continuous_ofReal.comp (continuous_pow (2 * k + 1))).mul hg)).intervalIntegrable _ _
  let rem : ℝ → ℂ := fun u =>
    (((Real.cos (t * u) - cosTaylorPoly m (t * u) : ℝ) : ℂ)) +
      Complex.I * (((Real.sin (t * u) - sinTaylorPoly m (t * u) : ℝ) : ℂ))
  have hrem_cont : Continuous rem := by
    dsimp [rem]
    have hc1 : Continuous (fun u : ℝ => Real.cos (t * u) - cosTaylorPoly m (t * u)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub
        (continuous_finset_sum' _ fun k _ =>
          (continuous_const.mul ((continuous_const.mul continuous_id).pow (2 * k))).div_const _)
    have hs1 : Continuous (fun u : ℝ => Real.sin (t * u) - sinTaylorPoly m (t * u)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).sub
        (continuous_finset_sum' _ fun k _ =>
          (continuous_const.mul ((continuous_const.mul continuous_id).pow (2 * k + 1))).div_const _)
    exact (Complex.continuous_ofReal.comp hc1).add (continuous_const.mul (Complex.continuous_ofReal.comp hs1))
  have hsub_eq : compactFourier L g t = ∫ u in (-L / 2)..(L / 2), g u * rem u := by
    dsimp [compactFourier]
    have hcont_exp : Continuous (fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) :=
      hg.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have hcont_cp : Continuous (fun u : ℝ => g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (continuous_finset_sum' _ fun k _ =>
        (continuous_const.mul ((continuous_const.mul continuous_id).pow (2 * k))).div_const _))
    have hcont_sp : Continuous (fun u : ℝ => g u * (((sinTaylorPoly m (t * u) : ℝ) : ℂ))) :=
      hg.mul (Complex.continuous_ofReal.comp (continuous_finset_sum' _ fun k _ =>
        (continuous_const.mul ((continuous_const.mul continuous_id).pow (2 * k + 1))).div_const _))
    have hpt : (fun u : ℝ => g u * rem u) =
        fun u => (g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) -
          g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ))) -
          Complex.I * (g u * (((sinTaylorPoly m (t * u) : ℝ) : ℂ))) := by
      ext u; dsimp [rem]
      have harg : Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
    have hcont_sub : Continuous (fun u : ℝ => g u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) -
        g u * (((cosTaylorPoly m (t * u) : ℝ) : ℂ))) := hcont_exp.sub hcont_cp
    have hcont_isp : Continuous (fun u : ℝ => Complex.I * (g u * (((sinTaylorPoly m (t * u) : ℝ) : ℂ)))) :=
      continuous_const.mul hcont_sp
    rw [hpt, intervalIntegral.integral_sub (hcont_sub.intervalIntegrable (μ := volume) _ _)
        (hcont_isp.intervalIntegrable (μ := volume) _ _),
        intervalIntegral.integral_sub (hcont_exp.intervalIntegrable (μ := volume) _ _)
          (hcont_cp.intervalIntegrable (μ := volume) _ _),
        intervalIntegral.integral_const_mul, hcos_zero, hsin_zero]
    ring
  set M : ℝ := (|t| * (L / 2)) ^ (2 * m) / ((2 * m).factorial : ℝ) +
      (|t| * (L / 2)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)
  have hnorm_le : ‖compactFourier L g t‖ ≤ ∫ u in (-L / 2)..(L / 2), ‖g u‖ * M := by
    rw [hsub_eq]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    refine intervalIntegral.integral_mono_on hab
      ((continuous_norm.comp (hg.mul hrem_cont)).intervalIntegrable _ _)
      (((continuous_norm.comp hg).mul continuous_const).intervalIntegrable _ _) fun u hu => ?_
    rw [norm_mul]
    have hu_abs : |u| ≤ L / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have htu_abs : |t * u| ≤ |t| * (L / 2) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hu_abs (abs_nonneg t)
    have hrem_norm : ‖rem u‖ ≤ M := by
      dsimp [rem, M]
      have h1 := norm_add_le (((Real.cos (t * u) - cosTaylorPoly m (t * u) : ℝ) : ℂ))
        (Complex.I * (((Real.sin (t * u) - sinTaylorPoly m (t * u) : ℝ) : ℂ)))
      rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs] at h1
      have hc := (cos_sin_sub_taylor_abs_le m).1 (t * u)
      have hs := (cos_sin_sub_taylor_abs_le m).2 (t * u)
      have hp1 : |t * u| ^ (2 * m) / ((2 * m).factorial : ℝ) ≤
          (|t| * (L / 2)) ^ (2 * m) / ((2 * m).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) htu_abs (2 * m)) (by positivity)
      have hp2 : |t * u| ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤
          (|t| * (L / 2)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) htu_abs (2 * m + 1)) (by positivity)
      linarith
    exact mul_le_mul_of_nonneg_left hrem_norm (norm_nonneg _)
  have hcs := cauchy_schwarz_interval_weight hL hg continuous_const (w := fun _ => M)
  have hint_M : ∫ _u in (-L / 2)..(L / 2), M ^ 2 = L * M ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hint_M] at hcs
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2) hcs

-- Auxiliary `psiLb3` monotonicity, continuity, and arbitrary-cutoff Archimedean lemma

private lemma psiLb3_mono_nonneg' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
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

private lemma continuous_psiLb3' : Continuous psiLb3 := by
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

/-- Generic Archimedean cutoff lower bound at ANY `T ≥ 0` for any even continuous envelope `K`. -/
private lemma arch_cutoff_T_ge_of_envelope {L T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℂ}
    (hplanch : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hpsi_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2))
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_even : ∀ t, K (-t) = K t)
    (hK_bd : ∀ t : ℝ, ‖compactFourier L g t‖ ^ 2 ≤ K t * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)) :
    (psiLb3 T - (1 / Real.pi) * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t)) *
      (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤
    (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) := by
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hdiff_int : Integrable (fun t : ℝ => (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2) := by
    have h1 := hpsi_int.sub (hplanch.1.const_mul (psiLb3 T))
    exact h1.congr (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2 =
      psiLb3 T * (∫ t : ℝ, ‖compactFourier L g t‖ ^ 2) +
        ∫ t : ℝ, (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add (hplanch.1.const_mul (psiLb3 T)) hdiff_int]
    congr 1; ext t; ring
  have hlow_pt : ∀ t : ℝ,
      (Icc (-T) T).indicator (fun s : ℝ => -(psiLb3 T - psiLb3 s) * (K s * N2)) t ≤
        (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
    intro t
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]
      have habs : |t| ≤ T := abs_le.mpr ht
      have hlb_eq : psiLb3 |t| = psiLb3 t := by dsimp [psiLb3]; rw [sq_abs]
      have hgap_nn : 0 ≤ psiLb3 T - psiLb3 t := by
        rw [← hlb_eq]; exact sub_nonneg.mpr (psiLb3_mono_nonneg' (abs_nonneg t) habs)
      have hle_arch : -(psiLb3 T - psiLb3 t) ≤ psiArch t - psiLb3 T := by
        linarith [psiArch_ge_psiLb3 t]
      have hfour := hK_bd t
      have hm1 : -(psiLb3 T - psiLb3 t) * (K t * N2) ≤
          -(psiLb3 T - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 := by nlinarith
      have hm2 : -(psiLb3 T - psiLb3 t) * ‖compactFourier L g t‖ ^ 2 ≤
          (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hle_arch (sq_nonneg _)
      linarith
    · rw [indicator_of_notMem ht]
      have habs : T ≤ |t| := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have h1 : psiLb3 T ≤ psiArch T := psiArch_ge_psiLb3 T
      have h2 : psiArch T ≤ psiArch |t| := by
        rcases eq_or_lt_of_le habs with heq | hlt
        · rw [← heq]
        · exact le_of_lt (psiArch_strictMono_nonneg hT (abs_nonneg t) hlt)
      have h3 : psiArch |t| = psiArch t := by
        rcases le_total 0 t with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, psiArch_even]
      exact mul_nonneg (by linarith) (sq_nonneg _)
  have hcont_f : Continuous (fun s : ℝ => (psiLb3 T - psiLb3 s) * K s) :=
    (continuous_const.sub continuous_psiLb3').mul hK_cont
  have hcont_ind : Continuous (fun s : ℝ => -(psiLb3 T - psiLb3 s) * (K s * N2)) := by
    have heq : (fun s : ℝ => -(psiLb3 T - psiLb3 s) * (K s * N2)) =
        fun s : ℝ => (-N2) * ((psiLb3 T - psiLb3 s) * K s) := by ext s; ring
    rw [heq]; exact continuous_const.mul hcont_f
  have hint_ind : Integrable ((Icc (-T) T).indicator
      (fun s : ℝ => -(psiLb3 T - psiLb3 s) * (K s * N2))) :=
    (hcont_ind.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hmono_int := integral_mono hint_ind hdiff_int hlow_pt
  rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hmono_int
  have heven_int : ∫ s in (-T)..T, -(psiLb3 T - psiLb3 s) * (K s * N2) =
      -(2 * N2 * ∫ s in (0 : ℝ)..T, (psiLb3 T - psiLb3 s) * K s) := by
    have hcomp : ∫ s in (-T)..0, (psiLb3 T - psiLb3 s) * K s =
        ∫ s in (0 : ℝ)..T, (psiLb3 T - psiLb3 s) * K s := by
      have h := intervalIntegral.integral_comp_neg
        (f := fun s : ℝ => (psiLb3 T - psiLb3 s) * K s) (a := -T) (b := 0)
      simp only [neg_zero, neg_neg] at h
      have hf : (fun s : ℝ => (psiLb3 T - psiLb3 (-s)) * K (-s)) =
          fun s : ℝ => (psiLb3 T - psiLb3 s) * K s := by
        ext s; rw [hK_even s]; dsimp [psiLb3]; rw [neg_sq]
      rw [hf] at h; exact h
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hcont_f.intervalIntegrable (μ := volume) (-T) 0)
      (hcont_f.intervalIntegrable (μ := volume) 0 T)
    rw [show (fun s : ℝ => -(psiLb3 T - psiLb3 s) * (K s * N2)) =
          fun s : ℝ => (-N2) * ((psiLb3 T - psiLb3 s) * K s) by ext s; ring,
        intervalIntegral.integral_const_mul, ← hadd, hcomp]
    ring
  rw [heven_int] at hmono_int
  have hmul_pi := mul_le_mul_of_nonneg_left hmono_int (by positivity : 0 ≤ 1 / (2 * Real.pi))
  have htot : (1 / (2 * Real.pi)) * (∫ t : ℝ, psiArch t * ‖compactFourier L g t‖ ^ 2) =
      psiLb3 T * N2 + (1 / (2 * Real.pi)) * ∫ t : ℝ, (psiArch t - psiLb3 T) * ‖compactFourier L g t‖ ^ 2 := by
    rw [hsplit, mul_add, ← hplanch.2]; ring
  have hsimp : (1 / (2 * Real.pi)) * (-(2 * N2 * ∫ s in (0 : ℝ)..T, (psiLb3 T - psiLb3 s) * K s)) =
      -((1 / Real.pi) * ∫ s in (0 : ℝ)..T, (psiLb3 T - psiLb3 s) * K s) * N2 := by
    field_simp [ne_of_gt Real.pi_pos]
  rw [hsimp] at hmul_pi
  linarith

-- Rational log helpers for Theorem I.3 (prime-active L ≤ 3/4)

private lemma log_ge_of_exp_div4_lt' {x a : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) (_ha : 0 < a)
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

private lemma log_le_of_exp_taylor_ge {x a : ℝ} (hx0 : 0 ≤ x) (ha : 0 < a) (n : ℕ)
    (ht : a ≤ ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)) :
    Real.log a ≤ x := by
  have h1 := Real.sum_le_exp_of_nonneg hx0 n
  have h2 : a ≤ Real.exp x := le_trans ht h1
  have := Real.log_le_log ha h2
  rwa [Real.log_exp] at this

private lemma log_two_le_6932_div_10000 : Real.log 2 ≤ 6932 / 10000 := by
  apply log_le_of_exp_taylor_ge (by norm_num) (by norm_num) 7
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
  norm_num

private lemma log_two_ge_69314_div_100000 : (69314 / 100000 : ℝ) ≤ Real.log 2 := by
  apply log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by norm_num)
  norm_num

private lemma log_three_gt_three_quarters : (3 / 4 : ℝ) < Real.log 3 := by
  have hge : (1 : ℝ) ≤ Real.log 3 := by
    apply log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by norm_num)
    norm_num
  linarith

private lemma log_two_div_sqrt_two_le_491_div_1000 : Real.log 2 / Real.sqrt 2 ≤ 491 / 1000 := by
  have hsq : (1414 / 1000 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hlog : Real.log 2 ≤ 6932 / 10000 := log_two_le_6932_div_10000
  calc Real.log 2 / Real.sqrt 2
    _ ≤ (6932 / 10000 : ℝ) / (1414 / 1000 : ℝ) :=
        div_le_div₀ (by norm_num) hlog (by norm_num) hsq
    _ ≤ 491 / 1000 := by norm_num

private lemma subint_gap_le_of_le16' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 16)
    {K U : ℝ → ℝ} (hK : Continuous K) (hU : Continuous U)
    (hKU : ∀ t ∈ Icc a b, K t ≤ U t) (hUnn : ∀ t ∈ Icc a b, 0 ≤ U t) :
    ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
      (psiLb3 16 - psiLb3 a) * ∫ t in a..b, U t := by
  have hcontL : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 t) * K t) :=
    (continuous_const.sub continuous_psiLb3').mul hK
  have hcontR : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 a) * U t) :=
    continuous_const.mul hU
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab (hcontL.intervalIntegrable _ _)
    (hcontR.intervalIntegrable _ _) fun t ht => ?_
  have hmono1 : psiLb3 a ≤ psiLb3 t := psiLb3_mono_nonneg' ha ht.1
  have hmono2 : psiLb3 t ≤ psiLb3 16 := psiLb3_mono_nonneg' (le_trans ha ht.1) (le_trans ht.2 hb)
  have hgap : psiLb3 16 - psiLb3 t ≤ psiLb3 16 - psiLb3 a := by linarith
  have h1 : (psiLb3 16 - psiLb3 t) * K t ≤ (psiLb3 16 - psiLb3 t) * U t :=
    mul_le_mul_of_nonneg_left (hKU t ht) (sub_nonneg.mpr hmono2)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hgap (hUnn t ht))

private lemma psiLb3_16_ge_66_div_100 : (66 / 100 : ℝ) ≤ psiLb3 16 := by
  dsimp [psiLb3]
  have hC := archimedeanWeilConst_lt
  have hl : (195 / 100 : ℝ) ≤ Real.log (1 + 4 * (16 : ℝ) ^ 2 / 169) :=
    log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by positivity) (by norm_num)
  norm_num at hl ⊢
  linarith

private lemma psiLb3_16_sub_le_of_log_lo {a lo : ℝ}
    (hlog_lo : lo ≤ Real.log (1 + 4 * a ^ 2 / 169)) :
    psiLb3 16 - psiLb3 a ≤
      ((4 * (16 : ℝ) ^ 2) / (1 / 4 + 16 ^ 2) + ((4 / 5 : ℝ) * 16 ^ 2) / (25 / 4 + 16 ^ 2) +
       ((4 / 9 : ℝ) * 16 ^ 2) / (81 / 4 + 16 ^ 2) + (1 / 2 : ℝ) * (196 / 100)) -
      ((4 * a ^ 2) / (1 / 4 + a ^ 2) + ((4 / 5 : ℝ) * a ^ 2) / (25 / 4 + a ^ 2) +
       ((4 / 9 : ℝ) * a ^ 2) / (81 / 4 + a ^ 2) + (1 / 2 : ℝ) * lo) := by
  have hlog16 : Real.log (1 + 4 * (16 : ℝ) ^ 2 / 169) ≤ 196 / 100 := by
    apply log_le_of_exp_taylor_ge (by norm_num) (by positivity) 9
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  dsimp [psiLb3]
  linarith

/-- THEOREM I.3 (FIRST PRIME-ACTIVE CONTINUOUS ZERO-DISCRETIZATION ARITHMETIC WEIL
    POSITIVITY IN LEAN 4: `0 < L ≤ 3/4`, STRICTLY CROSSING `log 2` WITH `p = 2` ACTIVE!):
    For EVERY `0 < L ≤ 3 / 4` (including the prime-active window `log 2 < L ≤ 3/4`
    where `ArithmeticFunction.vonMangoldt 2 = log 2` contributes non-trivially to
    `weilPrime L g`) and EVERY continuous even function `g : ℝ → ℂ` on `[-L/2, L/2]`
    with 5 vanishing even moments (`∀ k < 5, ∫_{-L/2}^{L/2} u^(2k) * g(u) du = 0`)
    obeying Plancherel and Archimedean integrability:
      `(1 / 20) * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ weilTotal L g`. -/
theorem weilTotal_continuous_pos_prime_two_active_up_to_three_quarters
    {L : ℝ} (hL0 : 0 < L) (hL : L ≤ 3 / 4)
    {g : ℝ → ℂ} (hg : Continuous g) (heven : ∀ u, g (-u) = g u)
    (hmom : ∀ k : ℕ, k < 5 → ∫ u in (-L / 2)..(L / 2), ((u ^ (2 * k) : ℝ) : ℂ) * g u = 0)
    (hplanch : Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
      (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
        ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2)
    (hpsi_int : Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2)) :
    (1 / 20 : ℝ) * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- Step 1: Prime bound holds on ALL of `0 < L ≤ 3/4` (both `L ≤ log 2` and `log 2 < L ≤ 3/4`!)
  have hprime_le : weilPrime L g ≤ (491 / 1000 : ℝ) * N2 := by
    by_cases hle2 : L ≤ Real.log 2
    · rw [weilPrime_eq_zero_of_le_log_two hle2 g]; positivity
    · push Not at hle2
      have hlt3 : L < Real.log 3 := lt_of_le_of_lt hL log_three_gt_three_quarters
      have hbd := (abs_le.mp (weilPrime_single_prime_two_bound hle2 hlt3 hg)).2
      have hmul := mul_le_mul_of_nonneg_right log_two_div_sqrt_two_le_491_div_1000 hN2_nn
      linarith
  have hpole_nn : 0 ≤ weilPole L g := weilPole_even_nonneg L hg heven
  -- Step 2: Order-10 compact Fourier envelope `K(t) = min L (L^21 * t^20 / D5)`
  set D5 : ℝ := (((4 * 5 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (4 * 5) * (((2 * 5).factorial : ℝ) ^ 2))
  let K : ℝ → ℝ := fun t => min L (L ^ 21 * t ^ 20 / D5)
  have hK_cont : Continuous K :=
    continuous_const.min ((continuous_const.mul (continuous_pow 20)).div_const D5)
  have hK_even : ∀ t, K (-t) = K t := fun t => by
    dsimp [K]; rw [show (-t) ^ (20 : ℕ) = t ^ (20 : ℕ) by ring]
  have harch := arch_cutoff_T_ge_of_envelope (L := L) (T := 16) (by norm_num) hplanch hpsi_int
    hK_cont hK_even (fun t => compactFourier_even_moments_norm_sq_le (le_of_lt hL0) 5 hg heven hmom t)
  -- Step 3: Split `[0, 16]` into 5 panels: `[0, 10], [10, 12], [12, 27/2], [27/2, 29/2], [29/2, 16]`
  have hf_cont : Continuous (fun t : ℝ => (psiLb3 16 - psiLb3 t) * K t) :=
    (continuous_const.sub continuous_psiLb3').mul hK_cont
  have hsplit5 : ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t =
      (∫ t in (0 : ℝ)..10, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (10 : ℝ)..12, (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (12 : ℝ)..(27 / 2), (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (27 / 2 : ℝ)..(29 / 2), (psiLb3 16 - psiLb3 t) * K t) +
      (∫ t in (29 / 2 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 10) (hf_cont.intervalIntegrable (μ := volume) 10 12)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 12) (hf_cont.intervalIntegrable (μ := volume) 12 (27 / 2))
    have h3 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 (27 / 2)) (hf_cont.intervalIntegrable (μ := volume) (27 / 2) (29 / 2))
    have h4 := intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable (μ := volume) 0 (29 / 2)) (hf_cont.intervalIntegrable (μ := volume) (29 / 2) 16)
    linarith
  have hL21 : L ^ 21 ≤ (3 / 4 : ℝ) ^ 21 := pow_le_pow_left₀ (le_of_lt hL0) hL 21
  have hD5_pos : 0 < D5 := by dsimp [D5]; positivity
  have hlow_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 16 →
      ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
        (psiLb3 16 - psiLb3 a) * ((3 / 4 : ℝ) ^ 21 * (b ^ 21 - a ^ 21) / (21 * D5)) := by
    intro a b ha hab hb
    let U : ℝ → ℝ := fun t => (3 / 4 : ℝ) ^ 21 * t ^ 20 / D5
    have hU_cont : Continuous U := (continuous_const.mul (continuous_pow 20)).div_const D5
    have h := subint_gap_le_of_le16' (U := U) ha hab hb hK_cont hU_cont
      (fun t _ => le_trans (min_le_right _ _) (by
        dsimp [U]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL21 (by positivity)) (le_of_lt hD5_pos)))
      (fun t _ => by dsimp [U]; positivity)
    have hint : ∫ t in a..b, U t = (3 / 4 : ℝ) ^ 21 * (b ^ 21 - a ^ 21) / (21 * D5) := by
      have hfun : U = fun t : ℝ => ((3 / 4 : ℝ) ^ 21 / D5) * t ^ 20 := by ext t; dsimp [U]; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow]; ring
    rwa [hint] at h
  have hhi_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 16 →
      ∫ t in a..b, (psiLb3 16 - psiLb3 t) * K t ≤
        (psiLb3 16 - psiLb3 a) * ((3 / 4 : ℝ) * (b - a)) := by
    intro a b ha hab hb
    have h := subint_gap_le_of_le16' (U := fun _ : ℝ => (3 / 4 : ℝ)) ha hab hb hK_cont continuous_const
      (fun t _ => le_trans (min_le_left _ _) hL) (fun _ _ => by norm_num)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  -- Rational gap bounds at a = 0, 10, 12, 27/2, 29/2
  have hg0 : psiLb3 16 - psiLb3 0 ≤ 620 / 100 := by
    have h := psiLb3_16_sub_le_of_log_lo (a := 0) (lo := 0) (by norm_num)
    norm_num at h; linarith
  have hg10 : psiLb3 16 - psiLb3 10 ≤ 47 / 100 := by
    have hl : (121 / 100 : ℝ) ≤ Real.log (1 + 4 * (10 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_16_sub_le_of_log_lo hl
    norm_num at h; linarith
  have hg12 : psiLb3 16 - psiLb3 12 ≤ 30 / 100 := by
    have hl : (148 / 100 : ℝ) ≤ Real.log (1 + 4 * (12 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_16_sub_le_of_log_lo hl
    norm_num at h; linarith
  have hg135 : psiLb3 16 - psiLb3 (27 / 2) ≤ 19 / 100 := by
    have hl : (166 / 100 : ℝ) ≤ Real.log (1 + 4 * (27 / 2 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_16_sub_le_of_log_lo hl
    norm_num at h; linarith
  have hg145 : psiLb3 16 - psiLb3 (29 / 2) ≤ 12 / 100 := by
    have hl : (178 / 100 : ℝ) ≤ Real.log (1 + 4 * (29 / 2 : ℝ) ^ 2 / 169) :=
      log_ge_of_exp_div4_lt' (by norm_num) (by norm_num) (by positivity) (by norm_num)
    have h := psiLb3_16_sub_le_of_log_lo hl
    norm_num at h; linarith
  have hs0 := hlow_sub 0 10 (by norm_num) (by norm_num) (by norm_num)
  have hs1 := hlow_sub 10 12 (by norm_num) (by norm_num) (by norm_num)
  have hs2 := hlow_sub 12 (27 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hs3 := hhi_sub (27 / 2) (29 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hs4 := hhi_sub (29 / 2) 16 (by norm_num) (by norm_num) (by norm_num)
  have hD5_val : D5 = 289964795614986240000 := by
    dsimp [D5]; norm_num [Nat.factorial]
  rw [hD5_val] at hs0 hs1 hs2
  have hint_tot_le : ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t ≤ 36 / 100 := by
    rw [hsplit5]
    norm_num at hs0 hs1 hs2 hs3 hs4
    linarith
  have hpen_le : (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t) ≤ 115 / 1000 := by
    have hpi_lo : (31415 / 10000 : ℝ) < Real.pi := by have h := Real.pi_gt_d4; norm_num at h ⊢; linarith
    have hint_nn : 0 ≤ ∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t := by
      refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
      have hm := psiLb3_mono_nonneg' ht.1 ht.2
      have hKnn : 0 ≤ K t := le_min (le_of_lt hL0) (by positivity)
      exact mul_nonneg (sub_nonneg.mpr hm) hKnn
    have h1 : 1 / Real.pi ≤ 1 / (31415 / 10000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (le_of_lt hpi_lo)
    have h2 := mul_le_mul h1 hint_tot_le hint_nn (by positivity)
    have hnum : (1 / (31415 / 10000 : ℝ)) * (36 / 100) ≤ 115 / 1000 := by norm_num
    linarith
  have hpsi16 := psiLb3_16_ge_66_div_100
  have hcoeff : (1 / 20 : ℝ) ≤
      (psiLb3 16 - (1 / Real.pi) * (∫ t in (0 : ℝ)..16, (psiLb3 16 - psiLb3 t) * K t)) - (491 / 1000 : ℝ) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal
  linarith [harch, hpole_nn, hprime_le, hmul]

/-- Helper: `psiLb3 T → +∞` as `T → +∞`. -/
private lemma psiLb3_tendsto_atTop : Tendsto psiLb3 atTop atTop := by
  have hlog : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + 4 * t ^ 2 / 169)) atTop atTop := by
    have h1 : Tendsto (fun t : ℝ => 1 + 4 * t ^ 2 / 169) atTop atTop := by
      have hp : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
      have hm : Tendsto (fun t : ℝ => (4 / 169 : ℝ) * t ^ 2) atTop atTop :=
        hp.const_mul_atTop (by norm_num)
      exact ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop hm).congr fun t => by ring
    exact (Real.tendsto_log_atTop.comp h1).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono (fun t => ?_) (hlog.atTop_add (tendsto_const_nhds (x := -archimedeanWeilConst)))
  dsimp [psiLb3]
  have h0 : 0 ≤ (4 * t ^ 2) / (1 / 4 + t ^ 2) := by positivity
  have h1 : 0 ≤ ((4 / 5 : ℝ) * t ^ 2) / (25 / 4 + t ^ 2) := by positivity
  have h2 : 0 ≤ ((4 / 9 : ℝ) * t ^ 2) / (81 / 4 + t ^ 2) := by positivity
  linarith

/-- Helper: For any `a ≥ 0`, `a^n / n! → 0` as `n → ∞`. -/
private lemma tendsto_pow_div_factorial_zero (a : ℝ) :
    Tendsto (fun n : ℕ => a ^ n / (n.factorial : ℝ)) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial a).tendsto_atTop_zero

/-- THEOREM I.4 (UNIVERSAL COMPACTLY SUPPORTED FINITE-CODIMENSION ARITHMETIC WEIL POSITIVITY
    FOR EVERY HORIZON `L > 0` — COMPLETELY RESOLVING THE PALEY-WIENER OBSTRUCTION):
    For EVERY `L > 0` (arbitrarily large, with ALL active `vonMangoldt` primes `p^k ≤ e^L`)
    and EVERY target coercive margin `c > 0`, there exists an explicit finite codimension `m : ℕ`
    such that for EVERY compactly supported continuous function `g : ℝ → ℂ` on `[-L/2, L/2]`
    (NO parity restriction!) orthogonal to the finite-dimensional polynomial space
    `span {1, u, u^2, ..., u^(2m - 1)}` obeying Plancherel and Archimedean integrability:
      `c * ∫_{-L/2}^{L/2} ‖g(u)‖^2 du ≤ weilTotal L g`. -/
theorem weilTotal_compact_finite_codimension_pos_all_L {L : ℝ} (hL0 : 0 < L) {c : ℝ} (_hc : 0 < c) :
    ∃ m : ℕ, ∀ {g : ℝ → ℂ}, Continuous g →
      (∀ k : ℕ, k < 2 * m → ∫ u in (-L / 2)..(L / 2), ((u ^ k : ℝ) : ℂ) * g u = 0) →
      (Integrable (fun t : ℝ => ‖compactFourier L g t‖ ^ 2) ∧
        (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖compactFourier L g t‖ ^ 2 =
          ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) →
      Integrable (fun t : ℝ => psiArch t * ‖compactFourier L g t‖ ^ 2) →
      c * (∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2) ≤ weilTotal L g := by
  -- Step 1: Uniform pole & prime operator bounds depending ONLY on L
  set B_pole : ℝ := 2 * (Real.sinh (L / 2) - L / 2)
  set B_prime : ℝ := 2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
  -- Step 2: Pick cutoff T ≥ 1 such that `psiLb3 T ≥ c + B_pole + B_prime + 1`
  rcases Filter.eventually_atTop.mp
      (psiLb3_tendsto_atTop.eventually_ge_atTop (c + B_pole + B_prime + 1)) with ⟨T₀, hT₀⟩
  set T : ℝ := max T₀ 1
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_right T₀ 1)
  have hpsiT : c + B_pole + B_prime + 1 ≤ psiLb3 T := hT₀ T (le_max_left T₀ 1)
  -- Step 3: Pick `m : ℕ` so that `((T * L / 2)^(2m)/(2m)! + (T * L / 2)^(2m+1)/(2m+1)!)^2`
  -- makes the low-frequency penalty `(1/π) * ∫_0^T (psiLb3 T - psiLb3 t) * K_m(t) dt ≤ 1`!
  set a : ℝ := T * (L / 2)
  have ha_nn : 0 ≤ a := by positivity
  have hgap_nn : 0 ≤ psiLb3 T - psiLb3 0 :=
    sub_nonneg.mpr (psiLb3_mono_nonneg' (le_refl 0) (le_of_lt hT_pos))
  set C_pen : ℝ := (T / Real.pi) * (psiLb3 T - psiLb3 0) * L
  have hC_nn : 0 ≤ C_pen := by dsimp [C_pen]; positivity
  have hlim_even : Tendsto (fun m : ℕ => a ^ (2 * m) / ((2 * m).factorial : ℝ)) atTop (𝓝 0) :=
    (tendsto_pow_div_factorial_zero a).comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩)
  have hlim_odd : Tendsto (fun m : ℕ => a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) atTop (𝓝 0) :=
    (tendsto_pow_div_factorial_zero a).comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩)
  have hlim_sq : Tendsto (fun m : ℕ =>
      C_pen * (a ^ (2 * m) / ((2 * m).factorial : ℝ) +
               a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2) atTop (𝓝 0) := by
    have hsum := hlim_even.add hlim_odd
    simpa using (hsum.pow 2).const_mul C_pen
  rcases Filter.eventually_atTop.mp
      (hlim_sq.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))) with ⟨m, hm⟩
  have hm_bound : C_pen * (a ^ (2 * m) / ((2 * m).factorial : ℝ) +
      a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2 ≤ 1 := le_of_lt (hm m le_rfl)
  -- Step 4: For EVERY continuous `g` orthogonal to `{1, u, ..., u^(2m-1)}`, certify `c * N2 ≤ W_total L g`!
  refine ⟨m, fun {g} hg hmom hplanch hpsi_int => ?_⟩
  set N2 : ℝ := ∫ u in (-L / 2)..(L / 2), ‖g u‖ ^ 2
  have hN2_nn : 0 ≤ N2 := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  let K : ℝ → ℝ := fun t =>
    L * ((|t| * (L / 2)) ^ (2 * m) / ((2 * m).factorial : ℝ) +
         (|t| * (L / 2)) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2
  have hK_cont : Continuous K := by
    dsimp [K]
    exact continuous_const.mul
      ((((((continuous_abs.mul continuous_const).pow (2 * m)).div_const _).add
       (((continuous_abs.mul continuous_const).pow (2 * m + 1)).div_const _))).pow 2)
  have hK_even : ∀ t : ℝ, K (-t) = K t := fun t => by dsimp [K]; rw [abs_neg]
  have harch := arch_cutoff_T_ge_of_envelope (L := L) (T := T) (le_of_lt hT_pos) hplanch hpsi_int
    hK_cont hK_even (fun t => compactFourier_all_moments_norm_sq_le (le_of_lt hL0) m hg hmom t)
  -- Bound `(1/π) * ∫_0^T (psiLb3 T - psiLb3 t) * K t dt ≤ C_pen * (...)^2 ≤ 1`
  have hpen_le_one : (1 / Real.pi) * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t) ≤ 1 := by
    have hcontL : Continuous (fun t : ℝ => (psiLb3 T - psiLb3 t) * K t) :=
      (continuous_const.sub continuous_psiLb3').mul hK_cont
    have hpt : ∀ t ∈ Icc (0 : ℝ) T, (psiLb3 T - psiLb3 t) * K t ≤
        (psiLb3 T - psiLb3 0) * (L * (a ^ (2 * m) / ((2 * m).factorial : ℝ) +
          a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2) := by
      intro t ht
      have hgap_le : psiLb3 T - psiLb3 t ≤ psiLb3 T - psiLb3 0 := by
        linarith [psiLb3_mono_nonneg' (le_refl 0) ht.1]
      have hgap_t_nn : 0 ≤ psiLb3 T - psiLb3 t :=
        sub_nonneg.mpr (psiLb3_mono_nonneg' ht.1 ht.2)
      have ht_le : |t| * (L / 2) ≤ a := by
        rw [abs_of_nonneg ht.1]; dsimp [a]
        exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
      have hKt_le : K t ≤ L * (a ^ (2 * m) / ((2 * m).factorial : ℝ) +
          a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2 := by
        dsimp [K]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 2) (le_of_lt hL0)
        exact add_le_add
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht_le (2 * m)) (by positivity))
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht_le (2 * m + 1)) (by positivity))
      exact le_trans (mul_le_mul_of_nonneg_left hKt_le hgap_t_nn)
        (mul_le_mul_of_nonneg_right hgap_le (by positivity))
    have hint_le : ∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t ≤
        T * ((psiLb3 T - psiLb3 0) * (L * (a ^ (2 * m) / ((2 * m).factorial : ℝ) +
          a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2)) := by
      have h1 := intervalIntegral.integral_mono_on (le_of_lt hT_pos)
        (hcontL.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const hpt
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
      exact h1
    have hmul := mul_le_mul_of_nonneg_left hint_le (by positivity : 0 ≤ 1 / Real.pi)
    have hrew : (1 / Real.pi) * (T * ((psiLb3 T - psiLb3 0) * (L *
        (a ^ (2 * m) / ((2 * m).factorial : ℝ) + a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2))) =
        C_pen * (a ^ (2 * m) / ((2 * m).factorial : ℝ) + a ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) ^ 2 := by
      dsimp [C_pen]; ring
    linarith
  have hpole := weilPole_lower_bound_all (le_of_lt hL0) hg
  have hprime := (abs_le.mp (weilPrime_general_norm_bound hL0 hg)).2
  have hcoeff : c ≤ (psiLb3 T - (1 / Real.pi) * (∫ t in (0 : ℝ)..T, (psiLb3 T - psiLb3 t) * K t)) -
      B_pole - B_prime := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hN2_nn
  unfold weilTotal
  dsimp [B_pole, B_prime] at hmul
  linarith [harch, hpole, hprime, hmul]

/-- THEOREM I.5 (QUANTITATIVE CHEBYSHEV-WEIL FLUCTUATION TRANSFER INEQUALITY AT EXPONENT `Θ`):
    Building directly on Module #16's Exact Weil-Chebyshev Renormalization Identity, if the
    Chebyshev error obeys `|ψ(e^u) - e^u| ≤ M * e^(Θ * u)` on `[0, L]` (with `M ≥ 0`), then for
    every `C^1` autocorrelation function `h` on `[0, L]` with continuous derivative `h'`:
      `|2 ∫_0^L ((ψ(e^u) - e^u) / e^(u/2)) * (h'(u) - (1/2) h(u)) du|
        ≤ 2 * M * ∫_0^L e^((Θ - 1/2) * u) * |h'(u) - (1/2) h(u)| du`.
    At the critical RH exponent `Θ = 1/2`, the exponential growth factor `e^((Θ - 1/2) * u) = 1`
    vanishes identically, giving a horizon-uniform non-exponential `L^1` fluctuation bound! -/
theorem chebyshev_weil_fluctuation_transfer_bound {L M Θ : ℝ} (hL : 0 ≤ L) (_hM : 0 ≤ M)
    {h h' : ℝ → ℝ} (hh : ContinuousOn h (Icc 0 L)) (hh' : ContinuousOn h' (Icc 0 L))
    (hint : IntervalIntegrable
      (fun u : ℝ => ((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
        (h' u - (1 / 2 : ℝ) * h u)) volume 0 L)
    (hcheb : ∀ u ∈ Icc (0 : ℝ) L, |chebyshevPsi (Real.exp u) - Real.exp u| ≤ M * Real.exp (Θ * u)) :
    |2 * ∫ u in (0 : ℝ)..L,
        ((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
          (h' u - (1 / 2 : ℝ) * h u)| ≤
      2 * M * ∫ u in (0 : ℝ)..L,
        Real.exp ((Θ - 1 / 2) * u) * |h' u - (1 / 2 : ℝ) * h u| := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : |∫ u in (0 : ℝ)..L,
        ((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
          (h' u - (1 / 2 : ℝ) * h u)| ≤
      ∫ u in (0 : ℝ)..L,
        |((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
          (h' u - (1 / 2 : ℝ) * h u)| :=
    intervalIntegral.abs_integral_le_integral_abs hL
  have hcont_rhs : ContinuousOn
      (fun u : ℝ => M * (Real.exp ((Θ - 1 / 2) * u) * |h' u - (1 / 2 : ℝ) * h u|)) (Icc 0 L) :=
    continuousOn_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hh'.sub (continuousOn_const.mul hh)).abs)
  have hint_rhs : IntervalIntegrable
      (fun u : ℝ => M * (Real.exp ((Θ - 1 / 2) * u) * |h' u - (1 / 2 : ℝ) * h u|)) volume 0 L :=
    (hcont_rhs.mono (by rw [Set.uIcc_of_le hL])).intervalIntegrable
  have h2 : ∫ u in (0 : ℝ)..L,
        |((chebyshevPsi (Real.exp u) - Real.exp u) / Real.exp (u / 2)) *
          (h' u - (1 / 2 : ℝ) * h u)| ≤
      ∫ u in (0 : ℝ)..L, M * (Real.exp ((Θ - 1 / 2) * u) * |h' u - (1 / 2 : ℝ) * h u|) := by
    refine intervalIntegral.integral_mono_on hL hint.abs hint_rhs fun u hu => ?_
    rw [abs_mul, abs_div, abs_of_pos (Real.exp_pos (u / 2))]
    have hdiv : |chebyshevPsi (Real.exp u) - Real.exp u| / Real.exp (u / 2) ≤
        M * Real.exp ((Θ - 1 / 2) * u) := by
      have hstep : |chebyshevPsi (Real.exp u) - Real.exp u| / Real.exp (u / 2) ≤
          (M * Real.exp (Θ * u)) / Real.exp (u / 2) :=
        div_le_div_of_nonneg_right (hcheb u hu) (le_of_lt (Real.exp_pos (u / 2)))
      have hexp : Real.exp (Θ * u) / Real.exp (u / 2) = Real.exp ((Θ - 1 / 2) * u) := by
        rw [← Real.exp_sub]; congr 1; ring
      rw [mul_div_assoc, hexp] at hstep
      exact hstep
    calc |chebyshevPsi (Real.exp u) - Real.exp u| / Real.exp (u / 2) * |h' u - (1 / 2 : ℝ) * h u|
      _ ≤ (M * Real.exp ((Θ - 1 / 2) * u)) * |h' u - (1 / 2 : ℝ) * h u| :=
          mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
      _ = M * (Real.exp ((Θ - 1 / 2) * u) * |h' u - (1 / 2 : ℝ) * h u|) := by ring
  rw [intervalIntegral.integral_const_mul] at h2
  nlinarith

/-- Weighted prime-power Kuramoto phase-order parameter at horizon `L`:
    `K_L(t) = ∑_{2 ≤ n ≤ ⌊e^L⌋} (Λ(n) / √n) * exp(-i * t * log n)`. -/
noncomputable def primeKuramotoOrder (L t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ)))

/-- Total prime weight normalization `B_0(L) = ∑_{2 ≤ n ≤ ⌊e^L⌋} Λ(n) / √n`. -/
noncomputable def primeKuramotoWeight (L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp L)),
    ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)

/-- Normalized Kuramoto phase-coherence parameter `r_L(t) = ‖K_L(t)‖ / B_0(L)`. -/
noncomputable def primeKuramotoCoherence (L t : ℝ) : ℝ :=
  ‖primeKuramotoOrder L t‖ / primeKuramotoWeight L

/-- THEOREM I.6 (PRIME KURAMOTO PHASE-ORDER COHERENCE BOUNDS & ZERO-FREQUENCY SYNC PEAK):
    For EVERY `L ≥ log 2` and EVERY frequency `t : ℝ`:
    (1) `0 < primeKuramotoWeight L` (strictly positive prime weight once `p = 2` activates),
    (2) `0 ≤ primeKuramotoCoherence L t ≤ 1` and `|(primeKuramotoOrder L t).re| ≤ r_L(t) * B_0(L)`,
    (3) `primeKuramotoOrder L 0 = (B_0(L) : ℂ)` and `primeKuramotoCoherence L 0 = 1`
        (exact constructive prime phase synchronization at `t = 0`). -/
theorem primeKuramotoOrder_bounds_and_sync_zero {L : ℝ} (hL : Real.log 2 ≤ L) :
    0 < primeKuramotoWeight L ∧
    (∀ t : ℝ, 0 ≤ primeKuramotoCoherence L t ∧ primeKuramotoCoherence L t ≤ 1 ∧
      |(primeKuramotoOrder L t).re| ≤ primeKuramotoCoherence L t * primeKuramotoWeight L) ∧
    (primeKuramotoOrder L 0 = (primeKuramotoWeight L : ℂ) ∧ primeKuramotoCoherence L 0 = 1) := by
  have h2_mem : (2 : ℕ) ∈ Finset.Icc 2 (Nat.floor (Real.exp L)) := by
    rw [Finset.mem_Icc]
    refine ⟨le_rfl, (Nat.le_floor_iff (le_of_lt (Real.exp_pos L))).mpr ?_⟩
    calc ((2 : ℕ) : ℝ) = Real.exp (Real.log 2) := by push_cast; exact (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hw_pos : 0 < primeKuramotoWeight L := by
    dsimp [primeKuramotoWeight]
    refine Finset.sum_pos' (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      ⟨2, h2_mem, ?_⟩
    have hvm2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
      simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    rw [hvm2]
    exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have hsync0 : primeKuramotoOrder L 0 = (primeKuramotoWeight L : ℂ) := by
    dsimp [primeKuramotoOrder, primeKuramotoWeight]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => by simp
  have hcoh0 : primeKuramotoCoherence L 0 = 1 := by
    dsimp [primeKuramotoCoherence]
    rw [hsync0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw_pos, div_self (ne_of_gt hw_pos)]
  refine ⟨hw_pos, fun t => ?_, ⟨hsync0, hcoh0⟩⟩
  have hnorm_le : ‖primeKuramotoOrder L t‖ ≤ primeKuramotoWeight L := by
    dsimp [primeKuramotoOrder, primeKuramotoWeight]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
    have hunit : ‖Complex.exp (-Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ)))‖ = 1 := by
      have harg : -Complex.I * ((t : ℂ) * ((Real.log (n : ℝ) : ℝ) : ℂ)) =
          ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    rw [hunit, mul_one]
  refine ⟨div_nonneg (norm_nonneg _) (le_of_lt hw_pos),
    (div_le_one hw_pos).mpr hnorm_le, ?_⟩
  dsimp [primeKuramotoCoherence]
  rw [div_mul_cancel₀ _ (ne_of_gt hw_pos)]
  exact Complex.abs_re_le_norm _

-- ==============================================================================
-- PART II: ROUTE B — TIGHT EULER-MASCHERONI BOUND, REAL DIGAMMA INCREMENT,
--          SHARP EULER L-SERIES BOUNDS AT β = 4, 5, 6, AND 2.14x GLOBAL ALL-γ
--          EULER HALF-PLANE DESCENT FROM σ ≥ 15/2 DOWN TO σ ≥ 7/2 (Re(s) ≥ 4)
-- ==============================================================================

/-- Helper: Upper bound on `harmonic 64` in 4 fast 16-term chunks: `harmonic 64 ≤ 474391 / 100000`. -/
private lemma harmonic_64_le : ((harmonic 64 : ℚ) : ℝ) ≤ 474391 / 100000 := by
  have hrat : harmonic 64 ≤ (474391 / 100000 : ℚ) := by
    have hsplit : harmonic 64 =
        (∑ i ∈ Finset.range 16, ((i + 1 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 17 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 33 : ℚ)⁻¹)) +
        (∑ i ∈ Finset.range 16, ((i + 49 : ℚ)⁻¹)) := by
      unfold harmonic
      rw [show (64 : ℕ) = 48 + 16 by rfl, Finset.sum_range_add,
          show (48 : ℕ) = 32 + 16 by rfl, Finset.sum_range_add,
          show (32 : ℕ) = 16 + 16 by rfl, Finset.sum_range_add]
      congr 1
      · congr 1
        · congr 1
          · refine Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
          · refine Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
        · refine Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
      · refine Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
    have hc1 : ∑ i ∈ Finset.range 16, ((i + 1 : ℚ)⁻¹) ≤ 338073 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc2 : ∑ i ∈ Finset.range 16, ((i + 17 : ℚ)⁻¹) ≤ 67777 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc3 : ∑ i ∈ Finset.range 16, ((i + 33 : ℚ)⁻¹) ≤ 40031 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    have hc4 : ∑ i ∈ Finset.range 16, ((i + 49 : ℚ)⁻¹) ≤ 28510 / 100000 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
    rw [hsplit]; linarith
  have hcast : ((harmonic 64 : ℚ) : ℝ) ≤ ((474391 / 100000 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  push_cast at hcast
  exact hcast

/-- THEOREM II.1A (TIGHT RATIONAL UPPER BOUND ON EULER-MASCHERONI CONSTANT):
    `Real.eulerMascheroniConstant < 586 / 1000`, tightening Mathlib4's `< 2 / 3` by >8x! -/
theorem eulerMascheroniConstant_lt_586_div_1000 :
    Real.eulerMascheroniConstant < 586 / 1000 := by
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hseq64 : Real.eulerMascheroniSeq' 64 = ((harmonic 64 : ℚ) : ℝ) - Real.log ((64 : ℕ) : ℝ) := by
    dsimp [Real.eulerMascheroniSeq']
  rw [hseq64] at h1
  have hlog64 : Real.log ((64 : ℕ) : ℝ) = 6 * Real.log 2 := by
    rw [show ((64 : ℕ) : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [hlog64] at h1
  have hh64 := harmonic_64_le
  have hl2 := log_two_ge_69314_div_100000
  linarith

/-- Helper: Exact `Real.log (Real.Gamma t)` derivative equals `(Complex.digamma t).re` for `t > 0`. -/
private lemma hasDerivAt_log_real_Gamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log (Real.Gamma t)) (Complex.digamma (x : ℂ)).re x := by
  have hre : 0 < (x : ℂ).re := hx
  have hgnz : Complex.Gamma (x : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hdiffG : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    have hre_eq := congrArg Complex.re hm; simp at hre_eq; linarith
  have hcomp : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ)) (deriv Complex.Gamma (x : ℂ)) x :=
    hdiffG.hasDerivAt.comp_ofReal
  have hre_d : HasDerivAt (fun t : ℝ => (Complex.Gamma (t : ℂ)).re) (deriv Complex.Gamma (x : ℂ)).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hcomp
  have hloc : (fun t : ℝ => (Complex.Gamma (t : ℂ)).re) = fun t : ℝ => Real.Gamma t := by
    ext t; rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [hloc] at hre_d
  have hlog := hre_d.log (ne_of_gt (Real.Gamma_pos_of_pos hx))
  refine hlog.congr_deriv ?_
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]

/-- THEOREM II.1B (EXACT FINITE-SUM LOWER BOUND ON REAL DIGAMMA INCREMENTS):
    Directly from `Complex.GammaSeq_tendsto_Gamma`, for EVERY `0 < a ≤ b` and EVERY `K : ℕ`:
      `(Complex.digamma a).re + ∑ k ∈ Finset.range K, (b - a) / ((a + k) * (b + k)) ≤ (Complex.digamma b).re`. -/
theorem complex_digamma_real_diff_ge_finset {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (K : ℕ) :
    (Complex.digamma (a : ℂ)).re +
      ∑ k ∈ Finset.range K, (b - a) / ((a + (k : ℝ)) * (b + (k : ℝ))) ≤
      (Complex.digamma (b : ℂ)).re := by
  set δ : ℝ := b - a
  have hδ : 0 ≤ δ := sub_nonneg.mpr hab
  -- Prove `H(t) = log Γ(t + δ) - log Γ(t) - ∑_{k < K} log((t + k) / (t + δ + k))` is MonotoneOn (Ioi 0)
  -- Wait: simpler! `F(t) = log Γ(t + δ) - log Γ(t) + ∑_{k < K} log((t + δ + k) / (t + k))`!
  -- Check derivative of `log((t + δ + k)/(t + k))`: `1/(t+δ+k) - 1/(t+k) = -δ/((t+k)(t+δ+k))`!
  -- So `F'(t) = ψ(t + δ) - ψ(t) - ∑_{k < K} δ / ((t + k)(t + δ + k))`!
  -- Check monotonicity of `F` via GammaSeq:
  -- `Γ_n(t + δ) / Γ_n(t) * ∏_{k < K} ((t + δ + k) / (t + k)) = n^δ * ∏_{k = K}^{n} ((t + k) / (t + δ + k))`!
  -- Since `t ↦ (t + k) / (t + δ + k) = 1 - δ / (t + δ + k)` is INCREASING in `t > 0`, `F` is MonotoneOn (Ioi 0)!!
  let F : ℝ → ℝ := fun t =>
    Real.log (Real.Gamma (t + δ)) - Real.log (Real.Gamma t) +
      ∑ k ∈ Finset.range K, Real.log ((t + δ + (k : ℝ)) / (t + (k : ℝ)))
  have hF_mono : MonotoneOn F (Set.Ioi (0 : ℝ)) := by
    intro t₁ ht₁ t₂ ht₂ hle
    have ht1 : 0 < t₁ := ht₁
    have ht2 : 0 < t₂ := ht₂
    have hseq : ∀ n : ℕ, K ≤ n → 1 ≤ n →
        (‖Complex.GammaSeq ((t₁ + δ : ℝ) : ℂ) n‖ / ‖Complex.GammaSeq (t₁ : ℂ) n‖) *
          (∏ k ∈ Finset.range K, ((t₁ + δ + (k : ℝ)) / (t₁ + (k : ℝ)))) ≤
        (‖Complex.GammaSeq ((t₂ + δ : ℝ) : ℂ) n‖ / ‖Complex.GammaSeq (t₂ : ℂ) n‖) *
          (∏ k ∈ Finset.range K, ((t₂ + δ + (k : ℝ)) / (t₂ + (k : ℝ)))) := by
      intro n hKn hn1
      have hrat : ∀ t : ℝ, 0 < t →
          (‖Complex.GammaSeq ((t + δ : ℝ) : ℂ) n‖ / ‖Complex.GammaSeq (t : ℂ) n‖) *
            (∏ k ∈ Finset.range K, ((t + δ + (k : ℝ)) / (t + (k : ℝ)))) =
          (n : ℝ) ^ δ * ∏ k ∈ Finset.Ico K (n + 1), ((t + (k : ℝ)) / (t + δ + (k : ℝ))) := by
        intro t ht
        dsimp [Complex.GammaSeq]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hcp1 : ‖((n : ℂ) ^ ((t + δ : ℝ) : ℂ))‖ = (n : ℝ) ^ (t + δ) := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]; simp
        have hcp2 : ‖((n : ℂ) ^ ((t : ℝ) : ℂ))‖ = (n : ℝ) ^ t := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]; simp
        have hprod_norm : ∀ s : ℝ, 0 < s →
            ‖∏ j ∈ Finset.range (n + 1), (((s : ℝ) : ℂ) + (j : ℂ))‖ =
              ∏ j ∈ Finset.range (n + 1), (s + (j : ℝ)) := by
          intro s hs; rw [norm_prod]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity)]
        rw [norm_div, norm_div, norm_mul, norm_mul, hcp1, hcp2,
            hprod_norm (t + δ) (by linarith), hprod_norm t ht, Complex.norm_natCast]
        have hfac_ne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hpow_ne : (n : ℝ) ^ t ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn_pos t)
        have hpd1_ne : (∏ j ∈ Finset.range (n + 1), (t + δ + (j : ℝ))) ≠ 0 :=
          ne_of_gt (Finset.prod_pos fun j _ => by positivity)
        have hpd2_ne : (∏ j ∈ Finset.range (n + 1), (t + (j : ℝ))) ≠ 0 :=
          ne_of_gt (Finset.prod_pos fun j _ => by positivity)
        have hrpow : (n : ℝ) ^ (t + δ) = (n : ℝ) ^ t * (n : ℝ) ^ δ := Real.rpow_add hn_pos t δ
        have hratio_prod : (∏ j ∈ Finset.range (n + 1), (t + (j : ℝ))) /
            (∏ j ∈ Finset.range (n + 1), (t + δ + (j : ℝ))) =
            (∏ j ∈ Finset.range K, ((t + (j : ℝ)) / (t + δ + (j : ℝ)))) *
            (∏ j ∈ Finset.Ico K (n + 1), ((t + (j : ℝ)) / (t + δ + (j : ℝ)))) := by
          rw [← Finset.prod_div_distrib]
          have hdisj : Disjoint (Finset.range K) (Finset.Ico K (n + 1)) := by
            rw [Finset.disjoint_left]; intro k hk1 hk2
            rw [Finset.mem_range] at hk1; rw [Finset.mem_Ico] at hk2; omega
          have hunion : Finset.range K ∪ Finset.Ico K (n + 1) = Finset.range (n + 1) := by
            ext k; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
          rw [← hunion, Finset.prod_union hdisj]
        have hcancel : (∏ j ∈ Finset.range K, ((t + (j : ℝ)) / (t + δ + (j : ℝ)))) *
            (∏ j ∈ Finset.range K, ((t + δ + (j : ℝ)) / (t + (j : ℝ)))) = 1 := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_eq_one fun j _ => ?_
          have h1 : t + (j : ℝ) ≠ 0 := ne_of_gt (by positivity)
          have h2 : t + δ + (j : ℝ) ≠ 0 := ne_of_gt (by positivity)
          field_simp [h1, h2]
        have hstep1 : ((n : ℝ) ^ (t + δ) * (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), (t + δ + (j : ℝ))) /
            ((n : ℝ) ^ t * (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), (t + (j : ℝ))) =
            (n : ℝ) ^ δ * ((∏ j ∈ Finset.range (n + 1), (t + (j : ℝ))) /
              (∏ j ∈ Finset.range (n + 1), (t + δ + (j : ℝ)))) := by
          rw [hrpow]; field_simp [hfac_ne, hpow_ne, hpd1_ne, hpd2_ne]
        rw [hstep1, hratio_prod]
        calc (n : ℝ) ^ δ * ((∏ j ∈ Finset.range K, ((t + (j : ℝ)) / (t + δ + (j : ℝ)))) *
              (∏ j ∈ Finset.Ico K (n + 1), ((t + (j : ℝ)) / (t + δ + (j : ℝ))))) *
              (∏ k ∈ Finset.range K, ((t + δ + (k : ℝ)) / (t + (k : ℝ))))
          _ = (n : ℝ) ^ δ * ((∏ j ∈ Finset.range K, ((t + (j : ℝ)) / (t + δ + (j : ℝ)))) *
              (∏ k ∈ Finset.range K, ((t + δ + (k : ℝ)) / (t + (k : ℝ))))) *
              (∏ j ∈ Finset.Ico K (n + 1), ((t + (j : ℝ)) / (t + δ + (j : ℝ)))) := by ring
          _ = (n : ℝ) ^ δ * ∏ j ∈ Finset.Ico K (n + 1), ((t + (j : ℝ)) / (t + δ + (j : ℝ))) := by
              rw [hcancel, mul_one]
      rw [hrat t₁ ht1, hrat t₂ ht2]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) δ)
      have hterm : ∀ k : ℕ, (t₁ + (k : ℝ)) / (t₁ + δ + (k : ℝ)) ≤ (t₂ + (k : ℝ)) / (t₂ + δ + (k : ℝ)) := by
        intro k
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      induction (Finset.Ico K (n + 1)) using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.prod_insert hj]
        exact mul_le_mul (hterm j) ih (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    -- Pass to limit `n → ∞`
    have hgnz1 : Complex.Gamma (t₁ : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht1)
    have hgnz2 : Complex.Gamma (t₂ : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht2)
    have hlim1 := (((Complex.GammaSeq_tendsto_Gamma ((t₁ + δ : ℝ) : ℂ)).norm.div
        (Complex.GammaSeq_tendsto_Gamma (t₁ : ℂ)).norm (norm_ne_zero_iff.mpr hgnz1))).mul_const
        (∏ k ∈ Finset.range K, ((t₁ + δ + (k : ℝ)) / (t₁ + (k : ℝ))))
    have hlim2 := (((Complex.GammaSeq_tendsto_Gamma ((t₂ + δ : ℝ) : ℂ)).norm.div
        (Complex.GammaSeq_tendsto_Gamma (t₂ : ℂ)).norm (norm_ne_zero_iff.mpr hgnz2))).mul_const
        (∏ k ∈ Finset.range K, ((t₂ + δ + (k : ℝ)) / (t₂ + (k : ℝ))))
    have hineq := le_of_tendsto_of_tendsto hlim1 hlim2
      (Filter.eventually_atTop.mpr ⟨max K 1, fun n hn =>
        hseq n (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)⟩)
    have hnorm_G : ∀ s : ℝ, 0 < s → ‖Complex.Gamma (s : ℂ)‖ = Real.Gamma s := fun s hs => by
      rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos hs)]
    rw [hnorm_G (t₁ + δ) (by linarith), hnorm_G t₁ ht1,
        hnorm_G (t₂ + δ) (by linarith), hnorm_G t₂ ht2] at hineq
    have hprod_pos : ∀ t : ℝ, 0 < t → 0 < ∏ k ∈ Finset.range K, ((t + δ + (k : ℝ)) / (t + (k : ℝ))) :=
      fun t ht => Finset.prod_pos fun k _ => by positivity
    have hlog := Real.log_le_log
      (mul_pos (div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos ht1)) (hprod_pos t₁ ht1))
      hineq
    rw [Real.log_mul (ne_of_gt (div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos ht1)))
          (ne_of_gt (hprod_pos t₁ ht1)),
        Real.log_mul (ne_of_gt (div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos ht2)))
          (ne_of_gt (hprod_pos t₂ ht2)),
        Real.log_div (ne_of_gt (Real.Gamma_pos_of_pos (by linarith))) (ne_of_gt (Real.Gamma_pos_of_pos ht1)),
        Real.log_div (ne_of_gt (Real.Gamma_pos_of_pos (by linarith))) (ne_of_gt (Real.Gamma_pos_of_pos ht2)),
        Real.log_prod (fun k _ => by positivity), Real.log_prod (fun k _ => by positivity)] at hlog
    exact hlog
  -- Differentiate `F` at `a`!
  have hd_F : HasDerivAt F
      ((Complex.digamma (b : ℂ)).re - (Complex.digamma (a : ℂ)).re -
        ∑ k ∈ Finset.range K, (b - a) / ((a + (k : ℝ)) * (b + (k : ℝ)))) a := by
    have h1 : HasDerivAt (fun t : ℝ => Real.log (Real.Gamma (t + δ))) (Complex.digamma (b : ℂ)).re a := by
      have hshift : a + δ = b := by dsimp [δ]; ring
      have hd := (hasDerivAt_log_real_Gamma (x := a + δ) (by linarith)).comp a ((hasDerivAt_id' a).add_const δ)
      rw [hshift, mul_one] at hd; exact hd
    have h2 := hasDerivAt_log_real_Gamma ha
    have h3 : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range K, Real.log ((t + δ + (k : ℝ)) / (t + (k : ℝ))))
        (-(∑ k ∈ Finset.range K, (b - a) / ((a + (k : ℝ)) * (b + (k : ℝ))))) a := by
      rw [← Finset.sum_neg_distrib]
      refine HasDerivAt.fun_sum fun k _ => ?_
      have hloc : (fun t : ℝ => Real.log ((t + δ + (k : ℝ)) / (t + (k : ℝ)))) =ᶠ[𝓝 a]
          fun t => Real.log (t + δ + (k : ℝ)) - Real.log (t + (k : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show a ∈ Set.Ioi (0 : ℝ) from ha)] with t ht
        have ht0 : 0 < t := ht
        exact Real.log_div (by positivity) (by positivity)
      have ha1 : HasDerivAt (fun t : ℝ => Real.log (t + δ + (k : ℝ))) (1 / (a + δ + (k : ℝ))) a := by
        have hl : HasDerivAt (fun t : ℝ => t + δ + (k : ℝ)) 1 a :=
          ((hasDerivAt_id' a).add_const δ).add_const (k : ℝ)
        have hpos : 0 < a + δ + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
        exact (hl.log (ne_of_gt hpos)).congr_deriv (by ring)
      have ha2 : HasDerivAt (fun t : ℝ => Real.log (t + (k : ℝ))) (1 / (a + (k : ℝ))) a := by
        have hl : HasDerivAt (fun t : ℝ => t + (k : ℝ)) 1 a := (hasDerivAt_id' a).add_const (k : ℝ)
        have hpos : 0 < a + (k : ℝ) := by positivity
        exact (hl.log (ne_of_gt hpos)).congr_deriv (by ring)
      refine (ha1.sub ha2).congr_of_eventuallyEq hloc |>.congr_deriv ?_
      have hb_eq : a + δ = b := by dsimp [δ]; ring
      rw [hb_eq]
      have hne1 : a + (k : ℝ) ≠ 0 := ne_of_gt (by positivity)
      have hne2 : b + (k : ℝ) ≠ 0 := ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) k])
      field_simp [hne1, hne2]; ring
    exact ((h1.sub h2).add h3).congr_deriv (by ring)
  have hd_nn : 0 ≤ (Complex.digamma (b : ℂ)).re - (Complex.digamma (a : ℂ)).re -
      ∑ k ∈ Finset.range K, (b - a) / ((a + (k : ℝ)) * (b + (k : ℝ))) := by
    have htend := (hasDerivAt_iff_tendsto_slope.mp hd_F).mono_left
      (nhdsWithin_mono a (fun t (ht : t ∈ Set.Ioi a) => ne_of_gt ht))
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hgt : a < t := ht
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hF_mono ha (lt_trans ha hgt) (le_of_lt hgt))) (sub_nonneg.mpr (le_of_lt hgt))
  linarith

-- Exact digamma lower bounds at 2, 17/8, 9/4, 5/2, 3

private lemma digamma_re_two_ge : (414 / 1000 : ℝ) < (Complex.digamma ((2 : ℝ) : ℂ)).re := by
  have hnat := Complex.digamma_nat_add_one 1
  have h2 : ((1 : ℕ) : ℂ) + 1 = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2] at hnat; rw [hnat]
  have hh1 : (harmonic 1 : ℂ) = 1 := by simp [harmonic]
  rw [hh1]; simp
  linarith [eulerMascheroniConstant_lt_586_div_1000]

private lemma digamma_re_five_halves_ge : (694 / 1000 : ℝ) < (Complex.digamma ((5 / 2 : ℝ) : ℂ)).re := by
  have hrec := Complex.digamma_apply_add_nat (s := (1 / 2 : ℂ)) (fun m hm => by
    have hre := congrArg Complex.re hm; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) m]) 2
  have h52 : (1 / 2 : ℂ) + ((2 : ℕ) : ℂ) = ((5 / 2 : ℝ) : ℂ) := by norm_num
  rw [h52] at hrec; rw [hrec, Complex.digamma_one_half]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  have hre_log : (Complex.log 2).re = Real.log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num), Complex.ofReal_re]
  have hval : (-2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) +
      (0 + ((1 / 2 : ℂ) + (0 : ℕ))⁻¹ + ((1 / 2 : ℂ) + (1 : ℕ))⁻¹)).re =
      8 / 3 - 2 * Real.log 2 - Real.eulerMascheroniConstant := by
    have hsum : (0 : ℂ) + ((1 / 2 : ℂ) + (0 : ℕ))⁻¹ + ((1 / 2 : ℂ) + (1 : ℕ))⁻¹ = ((8 / 3 : ℝ) : ℂ) := by
      norm_num
    rw [hsum]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
               hre_log]; norm_num; ring
  rw [hval]
  linarith [log_two_le_6932_div_10000, eulerMascheroniConstant_lt_586_div_1000]

private lemma digamma_re_three_ge : (914 / 1000 : ℝ) < (Complex.digamma ((3 : ℝ) : ℂ)).re := by
  have hnat := Complex.digamma_nat_add_one 2
  have h3 : ((2 : ℕ) : ℂ) + 1 = ((3 : ℝ) : ℂ) := by norm_num
  rw [h3] at hnat; rw [hnat]
  have hh2 : (harmonic 2 : ℂ) = (3 / 2 : ℂ) := by simp [harmonic, Finset.sum_range_succ]; norm_num
  rw [hh2]; simp
  linarith [eulerMascheroniConstant_lt_586_div_1000]

private lemma digamma_re_seventeen_eighths_ge :
    (478 / 1000 : ℝ) < (Complex.digamma ((17 / 8 : ℝ) : ℂ)).re := by
  have h := complex_digamma_real_diff_ge_finset (a := 2) (b := 17 / 8) (by norm_num) (by norm_num) 8
  have hsum : (64 / 1000 : ℝ) ≤
      ∑ k ∈ Finset.range 8, (17 / 8 - 2 : ℝ) / ((2 + (k : ℝ)) * (17 / 8 + (k : ℝ))) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
  linarith [digamma_re_two_ge]

private lemma digamma_re_nine_fourths_ge :
    (537 / 1000 : ℝ) < (Complex.digamma ((9 / 4 : ℝ) : ℂ)).re := by
  have h := complex_digamma_real_diff_ge_finset (a := 2) (b := 9 / 4) (by norm_num) (by norm_num) 8
  have hsum : (123 / 1000 : ℝ) ≤
      ∑ k ∈ Finset.range 8, (9 / 4 - 2 : ℝ) / ((2 + (k : ℝ)) * (9 / 4 + (k : ℝ))) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num
  linarith [digamma_re_two_ge]

private lemma log_pi_lt_11448_div_10000 : Real.log Real.pi < 11448 / 10000 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have hpi : Real.pi < 31416 / 10000 := by have h := Real.pi_lt_d4; norm_num at h ⊢; linarith
  have hexp := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11448 / 10000 by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp
  norm_num at hexp
  linarith

-- Sharp uniform Euler-product bounds for β ≥ 4, β ≥ 5, β ≥ 6

/-- Helper: Rational upper bounds on `vonMangoldt n` for `n = 2..16` (exact 0 at composites 6,10,12,14,15). -/
private lemma vonMangoldt_ub_small (n : ℕ) :
    ArithmeticFunction.vonMangoldt n ≤
      if n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 then 6932 / 10000
      else if n = 3 ∨ n = 9 then 11 / 10
      else if n = 5 then 161 / 100
      else if n = 7 then 195 / 100
      else if n = 11 then 24 / 10
      else if n = 13 then 26 / 10
      else if n ≤ 16 then 0
      else (n : ℝ) := by
  have hlog3 : Real.log 3 ≤ 11 / 10 := by
    apply log_le_of_exp_taylor_ge (by norm_num) (by norm_num) 9
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
  have hlog5 : Real.log 5 ≤ 161 / 100 := by
    apply log_le_of_exp_taylor_ge (by norm_num) (by norm_num) 10
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
  have hlog7 : Real.log 7 ≤ 195 / 100 := by
    apply log_le_of_exp_taylor_ge (by norm_num) (by norm_num) 11
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
  have hlog11 : Real.log 11 ≤ 24 / 10 := by
    apply log_le_of_exp_taylor_ge (by norm_num) (by norm_num) 12
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
  have hlog13 : Real.log 13 ≤ 26 / 10 := by
    apply log_le_of_exp_taylor_ge (by norm_num) (by norm_num) 13
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
  have hnotpp : ∀ m : ℕ, ¬IsPrimePow m → ArithmeticFunction.vonMangoldt m = 0 :=
    fun m hm => ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm
  have hpp_pow : ∀ p k : ℕ, Nat.Prime p → k ≠ 0 →
      ArithmeticFunction.vonMangoldt (p ^ k) = Real.log (p : ℝ) := fun p k hp hk => by
    simpa using ArithmeticFunction.vonMangoldt_apply_pow hk |> fun h => h.trans (ArithmeticFunction.vonMangoldt_apply_prime hp)
  have hnot_comp : ∀ m a b : ℕ, 2 ≤ a → 2 ≤ b → Nat.Coprime a b → a * b = m → ¬IsPrimePow m := by
    intro m a b ha hb hcop hmul hpp
    rcases (isPrimePow_nat_iff m).mp hpp with ⟨p, k, hp, hk, hpk⟩
    have ha_dvd : a ∣ p ^ k := by rw [hpk, ← hmul]; exact dvd_mul_right a b
    have hb_dvd : b ∣ p ^ k := by rw [hpk, ← hmul]; exact dvd_mul_left b a
    have hpa : p ∣ a := by
      rcases (Nat.dvd_prime_pow hp).mp ha_dvd with ⟨i, _, hi⟩
      have hi0 : i ≠ 0 := by intro h0; subst h0; simp at hi; omega
      rw [hi]; exact dvd_pow_self p hi0
    have hpb : p ∣ b := by
      rcases (Nat.dvd_prime_pow hp).mp hb_dvd with ⟨i, _, hi⟩
      have hi0 : i ≠ 0 := by intro h0; subst h0; simp at hi; omega
      rw [hi]; exact dvd_pow_self p hi0
    have hp1 : p ∣ 1 := by rw [← hcop]; exact Nat.dvd_gcd hpa hpb
    exact hp.not_dvd_one hp1
  match n with
  | 0 => simp
  | 1 => simp [ArithmeticFunction.vonMangoldt_apply_one]
  | 2 =>
    have h := hpp_pow 2 1 Nat.prime_two (by norm_num); simp only [pow_one, Nat.cast_ofNat] at h
    simp [h, log_two_le_6932_div_10000]
  | 3 =>
    have h := hpp_pow 3 1 Nat.prime_three (by norm_num); simp only [pow_one, Nat.cast_ofNat] at h
    simp [h, hlog3]
  | 4 =>
    have h := hpp_pow 2 2 Nat.prime_two (by norm_num); norm_num at h
    simp [h, log_two_le_6932_div_10000]
  | 5 =>
    have h := hpp_pow 5 1 Nat.prime_five (by norm_num); simp only [pow_one, Nat.cast_ofNat] at h
    simp [h, hlog5]
  | 6 =>
    have h0 := hnotpp 6 (hnot_comp 6 2 3 (by norm_num) (by norm_num) (by decide) (by norm_num))
    simp [h0]
  | 7 =>
    have h := hpp_pow 7 1 (by decide : Nat.Prime 7) (by norm_num); simp only [pow_one, Nat.cast_ofNat] at h
    simp [h, hlog7]
  | 8 =>
    have h := hpp_pow 2 3 Nat.prime_two (by norm_num); norm_num at h
    simp [h, log_two_le_6932_div_10000]
  | 9 =>
    have h := hpp_pow 3 2 Nat.prime_three (by norm_num); norm_num at h
    simp [h, hlog3]
  | 10 =>
    have h0 := hnotpp 10 (hnot_comp 10 2 5 (by norm_num) (by norm_num) (by decide) (by norm_num))
    simp [h0]
  | 11 =>
    have h := hpp_pow 11 1 (by decide : Nat.Prime 11) (by norm_num); simp only [pow_one, Nat.cast_ofNat] at h
    simp [h, hlog11]
  | 12 =>
    have h0 := hnotpp 12 (hnot_comp 12 4 3 (by norm_num) (by norm_num) (by decide) (by norm_num))
    simp [h0]
  | 13 =>
    have h := hpp_pow 13 1 (by decide : Nat.Prime 13) (by norm_num); simp only [pow_one, Nat.cast_ofNat] at h
    simp [h, hlog13]
  | 14 =>
    have h0 := hnotpp 14 (hnot_comp 14 2 7 (by norm_num) (by norm_num) (by decide) (by norm_num))
    simp [h0]
  | 15 =>
    have h0 := hnotpp 15 (hnot_comp 15 3 5 (by norm_num) (by norm_num) (by decide) (by norm_num))
    simp [h0]
  | 16 =>
    have h := hpp_pow 2 4 Nat.prime_two (by norm_num); norm_num at h
    simp [h, log_two_le_6932_div_10000]
  | n + 17 =>
    have hgt : ¬(n + 17 ≤ 16) := by omega
    have hne : n + 17 ≠ 2 ∧ n + 17 ≠ 4 ∧ n + 17 ≠ 8 ∧ n + 17 ≠ 16 ∧
        n + 17 ≠ 3 ∧ n + 17 ≠ 9 ∧ n + 17 ≠ 5 ∧ n + 17 ≠ 7 ∧ n + 17 ≠ 11 ∧ n + 17 ≠ 13 := by omega
    simp only [hne, or_self, ↓reduceIte, hgt]
    have hpos : (0 : ℝ) < ((n + 17 : ℕ) : ℝ) := by positivity
    exact le_trans ArithmeticFunction.vonMangoldt_le_log (le_trans (Real.log_le_sub_one_of_pos hpos) (by linarith))

/-- Helper: Unified integer-power `LSeries` norm bound for `β ≥ d` (`d ≥ 4`), splitting `n ≤ 16`
    exactly and bounding `n ≥ 17` by `(1 / 17^(d - 3)) * (1/(n-1) - 1/n)` summing to `1 / (16 * 17^(d - 3))`. -/
private lemma vonMangoldt_lseries_norm_le_of_nat_le (d : ℕ) (hd : 4 ≤ d) {β : ℝ} (hβ : (d : ℝ) ≤ β) (γ : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤
      (6932 / 10000 : ℝ) * (1 / (2 : ℝ) ^ d + 1 / (4 : ℝ) ^ d + 1 / (8 : ℝ) ^ d + 1 / (16 : ℝ) ^ d) +
      (11 / 10 : ℝ) * (1 / (3 : ℝ) ^ d + 1 / (9 : ℝ) ^ d) +
      (161 / 100 : ℝ) / (5 : ℝ) ^ d + (195 / 100 : ℝ) / (7 : ℝ) ^ d +
      (24 / 10 : ℝ) / (11 : ℝ) ^ d + (26 / 10 : ℝ) / (13 : ℝ) ^ d +
      1 / (16 * (17 : ℝ) ^ (d - 3)) := by
  have hβ1 : 1 < β := by
    have hd4 : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rcases vonMangoldt_lseries_norm_le_tsum hβ1 γ with ⟨hsum, hnorm⟩
  refine le_trans hnorm ?_
  let Ctail : ℝ := 1 / (17 : ℝ) ^ (d - 3)
  let B : ℕ → ℝ := fun n =>
    if n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 then (6932 / 10000 : ℝ) / (n : ℝ) ^ d
    else if n = 3 ∨ n = 9 then (11 / 10 : ℝ) / (n : ℝ) ^ d
    else if n = 5 then (161 / 100 : ℝ) / (5 : ℝ) ^ d
    else if n = 7 then (195 / 100 : ℝ) / (7 : ℝ) ^ d
    else if n = 11 then (24 / 10 : ℝ) / (11 : ℝ) ^ d
    else if n = 13 then (26 / 10 : ℝ) / (13 : ℝ) ^ d
    else if n ≤ 16 then 0
    else Ctail * (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ))
  have htele : HasSum (fun k : ℕ => Ctail * (1 / ((k + 16 : ℕ) : ℝ) - 1 / ((k + 17 : ℕ) : ℝ)))
      (Ctail * (1 / 16 : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N,
          Ctail * (1 / ((k + 16 : ℕ) : ℝ) - 1 / ((k + 17 : ℕ) : ℝ)) =
          Ctail * (1 / 16 - 1 / ((N + 16 : ℕ) : ℝ)) := by
        intro N; rw [← Finset.mul_sum]; congr 1
        induction N with
        | zero => simp
        | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      simp_rw [hpart]
      have h0 : Tendsto (fun N : ℕ => 1 / ((N + 16 : ℕ) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 15) |> fun h =>
          h.congr (fun N => by dsimp [Function.comp_def]; push_cast; ring_nf)
      simpa using (tendsto_const_nhds.sub h0).const_mul Ctail
    · intro k
      have h1 : (0 : ℝ) < ((k + 16 : ℕ) : ℝ) := by positivity
      have h2 : ((k + 16 : ℕ) : ℝ) ≤ ((k + 17 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 16 ≤ k + 17)
      have h3 := one_div_le_one_div_of_le h1 h2
      have hCnn : 0 ≤ Ctail := by dsimp [Ctail]; positivity
      exact mul_nonneg hCnn (sub_nonneg.mpr h3)
  set S_head : ℝ :=
      (6932 / 10000 : ℝ) * (1 / (2 : ℝ) ^ d + 1 / (4 : ℝ) ^ d + 1 / (8 : ℝ) ^ d + 1 / (16 : ℝ) ^ d) +
      (11 / 10 : ℝ) * (1 / (3 : ℝ) ^ d + 1 / (9 : ℝ) ^ d) +
      (161 / 100 : ℝ) / (5 : ℝ) ^ d + (195 / 100 : ℝ) / (7 : ℝ) ^ d +
      (24 / 10 : ℝ) / (11 : ℝ) ^ d + (26 / 10 : ℝ) / (13 : ℝ) ^ d
  have hB_hasSum : HasSum B (S_head + 1 / (16 * (17 : ℝ) ^ (d - 3))) := by
    rw [← hasSum_nat_add_iff' 17]
    have hshift : (fun k : ℕ => B (k + 17)) =
        fun k => Ctail * (1 / ((k + 16 : ℕ) : ℝ) - 1 / ((k + 17 : ℕ) : ℝ)) := by
      ext k; dsimp [B]
    rw [hshift]
    have hhead : ∑ i ∈ Finset.range 17, B i = S_head := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, B, S_head]
      norm_num; ring
    rw [hhead]
    convert htele using 1
    dsimp [Ctail]; ring
  have hle_B : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β ≤ B n := by
    intro n
    have hvm := vonMangoldt_ub_small n
    by_cases h16 : n ≤ 16
    · by_cases h01 : n ≤ 1
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h01 with rfl | rfl
        · simp [B]
        · simp [B, ArithmeticFunction.vonMangoldt_apply_one]
      · have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        have hpow : (n : ℝ) ^ d ≤ (n : ℝ) ^ β := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hn_ge1 hβ
        have hpow_pos : (0 : ℝ) < (n : ℝ) ^ d := by positivity
        dsimp [B]
        by_cases h2 : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16
        · simp only [h2, ↓reduceIte] at hvm ⊢
          exact div_le_div₀ (by norm_num) hvm hpow_pos hpow
        · simp only [h2, ↓reduceIte] at hvm ⊢
          by_cases h3 : n = 3 ∨ n = 9
          · simp only [h3, ↓reduceIte] at hvm ⊢
            exact div_le_div₀ (by norm_num) hvm hpow_pos hpow
          · simp only [h3, ↓reduceIte] at hvm ⊢
            by_cases h5 : n = 5
            · subst h5; simp only [↓reduceIte] at hvm ⊢
              exact div_le_div₀ (by norm_num) hvm hpow_pos (by exact_mod_cast hpow)
            · simp only [h5, ↓reduceIte] at hvm ⊢
              by_cases h7 : n = 7
              · subst h7; simp only [↓reduceIte] at hvm ⊢
                exact div_le_div₀ (by norm_num) hvm hpow_pos (by exact_mod_cast hpow)
              · simp only [h7, ↓reduceIte] at hvm ⊢
                by_cases h11 : n = 11
                · subst h11; simp only [↓reduceIte] at hvm ⊢
                  exact div_le_div₀ (by norm_num) hvm hpow_pos (by exact_mod_cast hpow)
                · simp only [h11, ↓reduceIte] at hvm ⊢
                  by_cases h13 : n = 13
                  · subst h13; simp only [↓reduceIte] at hvm ⊢
                    exact div_le_div₀ (by norm_num) hvm hpow_pos (by exact_mod_cast hpow)
                  · simp only [h13, h16, ↓reduceIte] at hvm ⊢
                    exact div_nonpos_of_nonpos_of_nonneg hvm (Real.rpow_nonneg (Nat.cast_nonneg n) β)
    · have hn17 : 17 ≤ n := by omega
      have hne : n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 3 ∧ n ≠ 9 ∧ n ≠ 5 ∧ n ≠ 7 ∧ n ≠ 11 ∧ n ≠ 13 := by omega
      dsimp [B]
      simp only [hne, or_self, ↓reduceIte, h16] at hvm ⊢
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hpow_ge : (n : ℝ) ^ d ≤ (n : ℝ) ^ β := by
        rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn_ge1 hβ
      have hsub : 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) = 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        have hne1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
        rw [hcast]; field_simp [ne_of_gt hn_pos, show (n : ℝ) - 1 ≠ 0 by rw [← hcast]; exact hne1]; ring
      rw [hsub]
      have hnm1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
      have hden_ge : (17 : ℝ) ^ (d - 3) * (((n - 1 : ℕ) : ℝ) * (n : ℝ)) ≤ (n : ℝ) ^ (d - 1) := by
        have hn17_r : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn17
        have h1 : (17 : ℝ) ^ (d - 3) ≤ (n : ℝ) ^ (d - 3) := pow_le_pow_left₀ (by norm_num) hn17_r (d - 3)
        have hnm1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le n 1)
        have h2 : ((n - 1 : ℕ) : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have hmul := mul_le_mul h1 h2 (by positivity) (by positivity)
        have hexp : (n : ℝ) ^ (d - 3) * (n : ℝ) ^ 2 = (n : ℝ) ^ (d - 1) := by
          rw [← pow_add]; congr 1; omega
        linarith
      have hdiv_n : (n : ℝ) / (n : ℝ) ^ d = 1 / (n : ℝ) ^ (d - 1) := by
        have hd_eq : d = (d - 1) + 1 := by omega
        conv_lhs => rw [hd_eq, pow_succ]
        field_simp [ne_of_gt hn_pos]
      calc ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ β
        _ ≤ (n : ℝ) / (n : ℝ) ^ d := div_le_div₀ (le_of_lt hn_pos) hvm (by positivity) hpow_ge
        _ = 1 / (n : ℝ) ^ (d - 1) := hdiv_n
        _ ≤ 1 / ((17 : ℝ) ^ (d - 3) * (((n - 1 : ℕ) : ℝ) * (n : ℝ))) :=
            one_div_le_one_div_of_le (by positivity) hden_ge
        _ = Ctail * (1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ))) := by dsimp [Ctail]; ring
  rw [← hB_hasSum.tsum_eq]
  exact hsum.tsum_le_tsum hle_B hB_hasSum.summable

/-- THEOREM II.2 (SHARP UNIFORM EULER-PRODUCT `vonMangoldt` L-SERIES BOUNDS FOR `β ≥ 4, 5, 6`):
    For EVERY `γ : ℝ`:
    (1) `β ≥ 4 → ‖L(Λ, ⟨β, -γ⟩)‖ ≤ 68 / 1000`,
    (2) `β ≥ 5 → ‖L(Λ, ⟨β, -γ⟩)‖ ≤ 29 / 1000`,
    (3) `β ≥ 6 → ‖L(Λ, ⟨β, -γ⟩)‖ ≤ 14 / 1000`. -/
theorem vonMangoldt_lseries_norm_le_of_four_five_six_le :
    (∀ β γ : ℝ, 4 ≤ β → ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ 68 / 1000) ∧
    (∀ β γ : ℝ, 5 ≤ β → ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ 29 / 1000) ∧
    (∀ β γ : ℝ, 6 ≤ β → ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ 14 / 1000) := by
  refine ⟨fun β γ hβ => ?_, fun β γ hβ => ?_, fun β γ hβ => ?_⟩
  · have h := vonMangoldt_lseries_norm_le_of_nat_le 4 (by norm_num) (by norm_num; exact hβ) γ
    norm_num at h; linarith
  · have h := vonMangoldt_lseries_norm_le_of_nat_le 5 (by norm_num) (by norm_num; exact hβ) γ
    norm_num at h; linarith
  · have h := vonMangoldt_lseries_norm_le_of_nat_le 6 (by norm_num) (by norm_num; exact hβ) γ
    norm_num at h; linarith

-- Universal monotone slab-segment certifiers for Route B global descent to σ ≥ 7/2 (β ≥ 4)

/-- Helper: On `[b0, b1]` (`0 < b0 ≤ b1`), `x / (x^2 + g^2) ≥ min (b0 / (b0^2 + g^2)) (b1 / (b1^2 + g^2))`. -/
private lemma pole_ge_min_endpoints {b0 b1 x g : ℝ} (hb0 : 0 < b0) (hx0 : b0 ≤ x) (hx1 : x ≤ b1) :
    min (b0 / (b0 ^ 2 + g ^ 2)) (b1 / (b1 ^ 2 + g ^ 2)) ≤ x / (x ^ 2 + g ^ 2) := by
  have hx_pos : 0 < x := lt_of_lt_of_le hb0 hx0
  have hb1 : 0 < b1 := lt_of_lt_of_le hx_pos hx1
  by_cases hle : b0 * x ≤ g ^ 2
  · refine le_trans (min_le_left _ _) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · refine le_trans (min_le_right _ _) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : g ^ 2 ≤ b0 * x := by linarith
    have h2 : b0 * x ≤ b1 * x := mul_le_mul_of_nonneg_right (le_trans hx0 hx1) (le_of_lt hx_pos)
    nlinarith

/-- Helper: Monotone slab-segment step on `β ∈ [b0, b1]`, `|γ| ∈ [ga, gb]`. -/
private lemma euler_im_pos_of_slab_segment {b0 b1 ga gb psi_lb p_ub : ℝ} {M : ℕ}
    (hb0 : 1 < b0) (hga : 0 ≤ ga) (_hgb : ga ≤ gb)
    (hpsi_base : psi_lb ≤ (Complex.digamma ((b0 / 2 : ℝ) : ℂ)).re)
    (hp_base : ∀ β γ : ℝ, b0 ≤ β → β ≤ b1 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ p_ub)
    (hcert : (0 : ℝ) <
      min (b0 / (b0 ^ 2 + gb ^ 2)) (b1 / (b1 ^ 2 + gb ^ 2)) +
      min ((b0 - 1) / ((b0 - 1) ^ 2 + gb ^ 2)) ((b1 - 1) / ((b1 - 1) ^ 2 + gb ^ 2)) +
      (1 / 2 : ℝ) * (psi_lb +
        (∑ k ∈ Finset.range M, (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2))) -
        11448 / 10000) - p_ub)
    {σ γ : ℝ} (hβ0 : b0 ≤ 1 / 2 + σ) (hβ1 : 1 / 2 + σ ≤ b1)
    (hg0 : ga ≤ |γ|) (hg1 : |γ| ≤ gb) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  set β : ℝ := 1 / 2 + σ
  set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hβ_gt1 : 1 < β := lt_of_lt_of_le hb0 hβ0
  have hβ_pos : 0 < β := by linarith
  have hβm1_pos : 0 < β - 1 := by linarith
  have hb0_pos : 0 < b0 := by linarith
  have hb1_pos0 : 0 < b1 := by linarith
  have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; dsimp [β] at hβ_gt1; linarith
  have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
  dsimp only at hexp
  set s : ℂ := 1 / 2 - Complex.I * z
  have hs_eq : s = (⟨β, -γ⟩ : ℂ) := by dsimp [s, z, β]; apply Complex.ext <;> simp
  have him_eq : (xiResolvent z).im =
      (1 / s).re + (1 / (s - 1)).re - (1 / 2 : ℝ) * Real.log Real.pi +
        (1 / 2 : ℝ) * (Complex.digamma (s / 2)).re -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
    rw [hexp]
    have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
      rw [← Complex.ofReal_log (le_of_lt Real.pi_pos), Complex.ofReal_re]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
               Complex.sub_re, Complex.add_re, Complex.mul_re]
    norm_num [hlogpi]
  have hgsq_le : γ ^ 2 ≤ gb ^ 2 := by
    rw [← sq_abs γ]; exact pow_le_pow_left₀ (abs_nonneg γ) hg1 2
  have hgsq_ge : ga ^ 2 ≤ γ ^ 2 := by
    rw [← sq_abs γ]; exact pow_le_pow_left₀ hga hg0 2
  have hp1 : min (b0 / (b0 ^ 2 + gb ^ 2)) (b1 / (b1 ^ 2 + gb ^ 2)) ≤ (1 / s).re := by
    rw [hs_eq, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [neg_mul, mul_neg, neg_neg]
    have hden_pos : 0 < β * β + γ * γ := by nlinarith [sq_nonneg γ]
    have h1 : β / (β ^ 2 + gb ^ 2) ≤ β / (β * β + γ * γ) := by
      have : β * β + γ * γ ≤ β ^ 2 + gb ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (le_of_lt hβ_pos) hden_pos this
    exact le_trans (pole_ge_min_endpoints hb0_pos hβ0 hβ1) h1
  have hp2 : min ((b0 - 1) / ((b0 - 1) ^ 2 + gb ^ 2)) ((b1 - 1) / ((b1 - 1) ^ 2 + gb ^ 2)) ≤ (1 / (s - 1)).re := by
    have hs1 : s - 1 = (⟨β - 1, -γ⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs1, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [neg_mul, mul_neg, neg_neg]
    have hden_pos : 0 < (β - 1) * (β - 1) + γ * γ := by nlinarith [sq_nonneg γ]
    have h1 : (β - 1) / ((β - 1) ^ 2 + gb ^ 2) ≤ (β - 1) / ((β - 1) * (β - 1) + γ * γ) := by
      have : (β - 1) * (β - 1) + γ * γ ≤ (β - 1) ^ 2 + gb ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (le_of_lt hβm1_pos) hden_pos this
    exact le_trans (pole_ge_min_endpoints (by linarith) (by linarith) (by linarith)) h1
  have hdig : psi_lb +
      (∑ k ∈ Finset.range M, (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2))) ≤
      (Complex.digamma (s / 2)).re := by
    have hs2 : s / 2 = (⟨β / 2, -γ / 2⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs2]
    have h1 := complex_digamma_re_ge_real_add_finset (show (0 : ℝ) < β / 2 by linarith) (-γ / 2) M
    have h2 := complex_digamma_real_mono
      (show b0 / 2 ∈ Set.Ioi (0 : ℝ) by simp; linarith)
      (show β / 2 ∈ Set.Ioi (0 : ℝ) by simp; linarith) (by linarith)
    have hsum_le : ∑ k ∈ Finset.range M,
          (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) ≤
        ∑ k ∈ Finset.range M,
          (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hy_le : (ga / 2) ^ 2 ≤ (-γ / 2) ^ 2 := by nlinarith
      have hx_le : β / 2 + (k : ℝ) ≤ b1 / 2 + (k : ℝ) := by linarith
      have hx_pos : 0 < β / 2 + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hb1_pos : 0 < b1 / 2 + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hsq_le : (β / 2 + (k : ℝ)) ^ 2 ≤ (b1 / 2 + (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hx_pos) hx_le 2
      have hstep1 : (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) ≤
          (ga / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul hx_le (by linarith) (by positivity) (le_of_lt hb1_pos))
      have hstep2 : (ga / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) ≤
          (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hdiff_nn : 0 ≤ ((-γ / 2) ^ 2 - (ga / 2) ^ 2) * ((β / 2 + (k : ℝ)) * (β / 2 + (k : ℝ)) ^ 2) :=
          mul_nonneg (sub_nonneg.mpr hy_le) (by positivity)
        have hident : (-γ / 2) ^ 2 * ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) -
            (ga / 2) ^ 2 * ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) =
            ((-γ / 2) ^ 2 - (ga / 2) ^ 2) * ((β / 2 + (k : ℝ)) * (β / 2 + (k : ℝ)) ^ 2) := by ring
        linarith only [hdiff_nn, hident]
      exact le_trans hstep1 hstep2
    linarith only [hpsi_base, h1, h2, hsum_le]
  have hlser : (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤ p_ub := by
    rw [hs_eq]
    exact le_trans (Complex.re_le_norm _) (hp_base β γ hβ0 hβ1)
  have hpi := log_pi_lt_11448_div_10000
  linarith only [him_eq, hp1, hp2, hdig, hlser, hcert, hpi]

/-- Helper: Monotone slab-tail step on `β ∈ [b0, b1]`, `ga ≤ |γ|` (poles ≥ 0, digamma ≥ at `ga`). -/
private lemma euler_im_pos_of_slab_tail {b0 b1 ga psi_lb p_ub : ℝ} {M : ℕ}
    (hb0 : 1 < b0) (hga : 0 ≤ ga)
    (hpsi_base : psi_lb ≤ (Complex.digamma ((b0 / 2 : ℝ) : ℂ)).re)
    (hp_base : ∀ β γ : ℝ, b0 ≤ β → β ≤ b1 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ p_ub)
    (hcert : (0 : ℝ) <
      (1 / 2 : ℝ) * (psi_lb +
        (∑ k ∈ Finset.range M, (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2))) -
        11448 / 10000) - p_ub)
    {σ γ : ℝ} (hβ0 : b0 ≤ 1 / 2 + σ) (hβ1 : 1 / 2 + σ ≤ b1) (hg0 : ga ≤ |γ|) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  set β : ℝ := 1 / 2 + σ
  set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hβ_gt1 : 1 < β := lt_of_lt_of_le hb0 hβ0
  have hb1_pos0 : 0 < b1 := by linarith
  have hz_im : 1 / 2 < z.im := by dsimp [z]; simp; dsimp [β] at hβ_gt1; linarith
  have hexp := xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im hz_im
  dsimp only at hexp
  set s : ℂ := 1 / 2 - Complex.I * z
  have hs_eq : s = (⟨β, -γ⟩ : ℂ) := by dsimp [s, z, β]; apply Complex.ext <;> simp
  have him_eq : (xiResolvent z).im =
      (1 / s).re + (1 / (s - 1)).re - (1 / 2 : ℝ) * Real.log Real.pi +
        (1 / 2 : ℝ) * (Complex.digamma (s / 2)).re -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
    rw [hexp]
    have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
      rw [← Complex.ofReal_log (le_of_lt Real.pi_pos), Complex.ofReal_re]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
               Complex.sub_re, Complex.add_re, Complex.mul_re]
    norm_num [hlogpi]
  have hp1 : 0 < (1 / s).re := by
    rw [hs_eq, one_div, Complex.inv_re]
    have hns : 0 < Complex.normSq (⟨β, -γ⟩ : ℂ) :=
      Complex.normSq_pos.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    exact div_pos (by simp; linarith) hns
  have hp2 : 0 < (1 / (s - 1)).re := by
    have hs1 : s - 1 = (⟨β - 1, -γ⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs1, one_div, Complex.inv_re]
    have hns : 0 < Complex.normSq (⟨β - 1, -γ⟩ : ℂ) :=
      Complex.normSq_pos.mpr (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    exact div_pos (by simp; linarith) hns
  have hgsq_ge : ga ^ 2 ≤ γ ^ 2 := by
    rw [← sq_abs γ]; exact pow_le_pow_left₀ hga hg0 2
  have hdig : psi_lb +
      (∑ k ∈ Finset.range M, (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2))) ≤
      (Complex.digamma (s / 2)).re := by
    have hs2 : s / 2 = (⟨β / 2, -γ / 2⟩ : ℂ) := by rw [hs_eq]; apply Complex.ext <;> simp
    rw [hs2]
    have h1 := complex_digamma_re_ge_real_add_finset (show (0 : ℝ) < β / 2 by linarith) (-γ / 2) M
    have h2 := complex_digamma_real_mono
      (show b0 / 2 ∈ Set.Ioi (0 : ℝ) by simp; linarith)
      (show β / 2 ∈ Set.Ioi (0 : ℝ) by simp; linarith) (by linarith)
    have hsum_le : ∑ k ∈ Finset.range M,
          (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) ≤
        ∑ k ∈ Finset.range M,
          (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hy_le : (ga / 2) ^ 2 ≤ (-γ / 2) ^ 2 := by nlinarith
      have hx_le : β / 2 + (k : ℝ) ≤ b1 / 2 + (k : ℝ) := by linarith
      have hx_pos : 0 < β / 2 + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hb1_pos : 0 < b1 / 2 + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hsq_le : (β / 2 + (k : ℝ)) ^ 2 ≤ (b1 / 2 + (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hx_pos) hx_le 2
      have hstep1 : (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) ≤
          (ga / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul hx_le (by linarith) (by positivity) (le_of_lt hb1_pos))
      have hstep2 : (ga / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) ≤
          (-γ / 2) ^ 2 / ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hdiff_nn : 0 ≤ ((-γ / 2) ^ 2 - (ga / 2) ^ 2) * ((β / 2 + (k : ℝ)) * (β / 2 + (k : ℝ)) ^ 2) :=
          mul_nonneg (sub_nonneg.mpr hy_le) (by positivity)
        have hident : (-γ / 2) ^ 2 * ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2)) -
            (ga / 2) ^ 2 * ((β / 2 + (k : ℝ)) * ((β / 2 + (k : ℝ)) ^ 2 + (-γ / 2) ^ 2)) =
            ((-γ / 2) ^ 2 - (ga / 2) ^ 2) * ((β / 2 + (k : ℝ)) * (β / 2 + (k : ℝ)) ^ 2) := by ring
        linarith only [hdiff_nn, hident]
      exact le_trans hstep1 hstep2
    linarith only [hpsi_base, h1, h2, hsum_le]
  have hlser : (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤ p_ub := by
    rw [hs_eq]
    exact le_trans (Complex.re_le_norm _) (hp_base β γ hβ0 hβ1)
  have hpi := log_pi_lt_11448_div_10000
  linarith only [him_eq, hp1, hp2, hdig, hlser, hcert, hpi]

/-- Helper: Clean 2-branch step helper for covering `[ga, ∞)` by `[ga, gb]` plus `[gb, ∞)`. -/
private lemma slab_step {b0 b1 ga gb psi_lb p_ub : ℝ} {M : ℕ}
    (hb0 : 1 < b0) (hga : 0 ≤ ga) (hgb : ga ≤ gb)
    (hpsi_base : psi_lb ≤ (Complex.digamma ((b0 / 2 : ℝ) : ℂ)).re)
    (hp_base : ∀ β γ : ℝ, b0 ≤ β → β ≤ b1 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -γ⟩ : ℂ)‖ ≤ p_ub)
    {σ γ : ℝ} (hβ0 : b0 ≤ 1 / 2 + σ) (hβ1 : 1 / 2 + σ ≤ b1) (hlo : ga ≤ |γ|)
    (hcert : (0 : ℝ) <
      min (b0 / (b0 ^ 2 + gb ^ 2)) (b1 / (b1 ^ 2 + gb ^ 2)) +
      min ((b0 - 1) / ((b0 - 1) ^ 2 + gb ^ 2)) ((b1 - 1) / ((b1 - 1) ^ 2 + gb ^ 2)) +
      (1 / 2 : ℝ) * (psi_lb +
        (∑ k ∈ Finset.range M, (ga / 2) ^ 2 / ((b1 / 2 + (k : ℝ)) * ((b1 / 2 + (k : ℝ)) ^ 2 + (ga / 2) ^ 2))) -
        11448 / 10000) - p_ub)
    (hrest : gb ≤ |γ| → 0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  by_cases h : |γ| ≤ gb
  · exact euler_im_pos_of_slab_segment hb0 hga hgb hpsi_base hp_base hcert hβ0 hβ1 hlo h
  · exact hrest (le_of_not_ge h)

/-- Helper: Slab `[6, 8]` (2 segments, `M = 6`). -/
private lemma xiResolvent_im_pos_slab_6_8 {σ γ : ℝ} (h0 : 6 ≤ 1 / 2 + σ) (h1 : 1 / 2 + σ ≤ 8) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  have hpsi : (914 / 1000 : ℝ) ≤ (Complex.digamma ((6 / 2 : ℝ) : ℂ)).re := by
    rw [show (6 / 2 : ℝ) = 3 by norm_num]; exact le_of_lt digamma_re_three_ge
  have hp : ∀ β g : ℝ, 6 ≤ β → β ≤ 8 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -g⟩ : ℂ)‖ ≤ 14 / 1000 :=
    fun β g hβ _ => vonMangoldt_lseries_norm_le_of_four_five_six_le.2.2 β g hβ
  refine slab_step (M := 6) (ga := 0) (gb := 7) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 (abs_nonneg γ)
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h7 => ?_
  exact euler_im_pos_of_slab_tail (M := 6) (ga := 7) (by norm_num) (by norm_num) hpsi hp
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) h0 h1 h7

/-- Helper: Slab `[5, 6]` (4 segments, `M = 8`). -/
private lemma xiResolvent_im_pos_slab_5_6 {σ γ : ℝ} (h0 : 5 ≤ 1 / 2 + σ) (h1 : 1 / 2 + σ ≤ 6) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  have hpsi : (694 / 1000 : ℝ) ≤ (Complex.digamma ((5 / 2 : ℝ) : ℂ)).re :=
    le_of_lt digamma_re_five_halves_ge
  have hp : ∀ β g : ℝ, 5 ≤ β → β ≤ 6 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -g⟩ : ℂ)‖ ≤ 29 / 1000 :=
    fun β g hβ _ => vonMangoldt_lseries_norm_le_of_four_five_six_le.2.1 β g hβ
  refine slab_step (M := 8) (ga := 0) (gb := 7 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 (abs_nonneg γ)
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 8) (ga := 7 / 2) (gb := 11 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 8) (ga := 11 / 2) (gb := 19 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  exact euler_im_pos_of_slab_tail (M := 8) (ga := 19 / 2) (by norm_num) (by norm_num) hpsi hp
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) h0 h1 h

/-- Helper: Slab `[9/2, 5]` (11 segments, `M = 12`). -/
private lemma xiResolvent_im_pos_slab_45_50 {σ γ : ℝ} (h0 : 9 / 2 ≤ 1 / 2 + σ) (h1 : 1 / 2 + σ ≤ 5) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  have hpsi : (537 / 1000 : ℝ) ≤ (Complex.digamma (((9 / 2 : ℝ) / 2 : ℝ) : ℂ)).re := by
    rw [show (9 / 2 : ℝ) / 2 = 9 / 4 by norm_num]; exact le_of_lt digamma_re_nine_fourths_ge
  have hp : ∀ β g : ℝ, 9 / 2 ≤ β → β ≤ 5 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -g⟩ : ℂ)‖ ≤ 68 / 1000 :=
    fun β g hβ _ => vonMangoldt_lseries_norm_le_of_four_five_six_le.1 β g (by linarith)
  refine slab_step (M := 12) (ga := 0) (gb := 7 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 (abs_nonneg γ)
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 7 / 4) (gb := 5 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 5 / 2) (gb := 3) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 3) (gb := 7 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 7 / 2) (gb := 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 4) (gb := 9 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 9 / 2) (gb := 5) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 5) (gb := 23 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 23 / 4) (gb := 29 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 29 / 4) (gb := 59 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  exact euler_im_pos_of_slab_tail (M := 12) (ga := 59 / 4) (by norm_num) (by norm_num) hpsi hp
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) h0 h1 h

/-- Helper: Slab `[17/4, 9/2]` (10 segments, `M = 12`). -/
private lemma xiResolvent_im_pos_slab_425_450 {σ γ : ℝ} (h0 : 17 / 4 ≤ 1 / 2 + σ) (h1 : 1 / 2 + σ ≤ 9 / 2) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  have hpsi : (478 / 1000 : ℝ) ≤ (Complex.digamma (((17 / 4 : ℝ) / 2 : ℝ) : ℂ)).re := by
    rw [show (17 / 4 : ℝ) / 2 = 17 / 8 by norm_num]; exact le_of_lt digamma_re_seventeen_eighths_ge
  have hp : ∀ β g : ℝ, 17 / 4 ≤ β → β ≤ 9 / 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -g⟩ : ℂ)‖ ≤ 68 / 1000 :=
    fun β g hβ _ => vonMangoldt_lseries_norm_le_of_four_five_six_le.1 β g (by linarith)
  refine slab_step (M := 12) (ga := 0) (gb := 7 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 (abs_nonneg γ)
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 7 / 4) (gb := 5 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 5 / 2) (gb := 3) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 3) (gb := 7 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 7 / 2) (gb := 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 4) (gb := 9 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 9 / 2) (gb := 21 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 21 / 4) (gb := 13 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 13 / 2) (gb := 45 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  exact euler_im_pos_of_slab_tail (M := 12) (ga := 45 / 4) (by norm_num) (by norm_num) hpsi hp
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) h0 h1 h

/-- Helper: Slab `[4, 17/4]` (16 segments, `M = 12`). -/
private lemma xiResolvent_im_pos_slab_400_425 {σ γ : ℝ} (h0 : 4 ≤ 1 / 2 + σ) (h1 : 1 / 2 + σ ≤ 17 / 4) :
    0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
  have hpsi : (414 / 1000 : ℝ) ≤ (Complex.digamma (((4 : ℝ) / 2 : ℝ) : ℂ)).re := by
    rw [show (4 : ℝ) / 2 = 2 by norm_num]; exact le_of_lt digamma_re_two_ge
  have hp : ∀ β g : ℝ, 4 ≤ β → β ≤ 17 / 4 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (⟨β, -g⟩ : ℂ)‖ ≤ 68 / 1000 :=
    fun β g hβ _ => vonMangoldt_lseries_norm_le_of_four_five_six_le.1 β g hβ
  refine slab_step (M := 12) (ga := 0) (gb := 7 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 (abs_nonneg γ)
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 7 / 4) (gb := 9 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 9 / 4) (gb := 5 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 5 / 2) (gb := 11 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 11 / 4) (gb := 3) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 3) (gb := 13 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 13 / 4) (gb := 7 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 7 / 2) (gb := 15 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 15 / 4) (gb := 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 4) (gb := 17 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 17 / 4) (gb := 9 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 9 / 2) (gb := 5) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 5) (gb := 23 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 23 / 4) (gb := 29 / 4) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  refine slab_step (M := 12) (ga := 29 / 4) (gb := 41 / 2) (by norm_num) (by norm_num) (by norm_num) hpsi hp h0 h1 h
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) fun h => ?_
  exact euler_im_pos_of_slab_tail (M := 12) (ga := 41 / 2) (by norm_num) (by norm_num) hpsi hp
    (by simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; norm_num) h0 h1 h

/-- THEOREM II.3 (2.14x GLOBAL UNCONDITIONAL EULER HALF-PLANE DESCENT DOWN TO `σ ≥ 7 / 2`
    (`Re(s) ≥ 4`) FOR EVERY `γ ∈ ℝ`!):
    Slashing Module #16's global all-`γ` Euler half-plane threshold from `σ ≥ 15 / 2` (`Re s ≥ 8`)
    down by more than `2.14x` to `σ ≥ 7 / 2` (`Re s ≥ 4`), for EVERY `σ ≥ 7 / 2` and EVERY `γ : ℝ`:
    (1) `0 < (xiResolvent (γ + iσ)).im` (global Herglotz positivity on `Im z ≥ 7/2`),
    (2) `0 < deriv (fun s => xiNormSq s γ) σ` and `0 < xiLogForce σ γ` (global radial force),
    (3) `0 < (logDeriv (xiSchur σ) γ).im` (strictly positive de Branges equatorial phase velocity),
    (4) `‖xiSchur α (γ + iσ)‖ < 1` whenever `0 < α, 0 < σ, 7 / 2 ≤ |σ - α|`. -/
theorem xiResolvent_herglotz_global_euler_halfPlane_seven_halves :
    (∀ σ γ : ℝ, 7 / 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im) ∧
    (∀ α σ γ : ℝ, 0 < α → 0 < σ → 7 / 2 ≤ |σ - α| →
      ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ < 1) := by
  have hmain : ∀ σ γ : ℝ, 7 / 2 ≤ σ →
      0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im ∧
      0 < deriv (fun s : ℝ => xiNormSq s γ) σ ∧
      0 < xiLogForce σ γ ∧
      0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
    intro σ γ hσ
    have hR_pos : 0 < (xiResolvent ((γ : ℂ) + Complex.I * (σ : ℂ))).im := by
      by_cases h8 : 15 / 2 ≤ σ
      · exact (xiResolvent_herglotz_global_euler_halfPlane.1 σ γ h8).1
      · by_cases h6 : 6 ≤ 1 / 2 + σ
        · exact xiResolvent_im_pos_slab_6_8 h6 (by linarith)
        · by_cases h5 : 5 ≤ 1 / 2 + σ
          · exact xiResolvent_im_pos_slab_5_6 h5 (by linarith)
          · by_cases h45 : 9 / 2 ≤ 1 / 2 + σ
            · exact xiResolvent_im_pos_slab_45_50 h45 (by linarith)
            · by_cases h425 : 17 / 4 ≤ 1 / 2 + σ
              · exact xiResolvent_im_pos_slab_425_450 h425 (by linarith)
              · exact xiResolvent_im_pos_slab_400_425 (by linarith) (by linarith)
    have hxi_ne : riemannXi (((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ)) ≠ 0 :=
      riemannXi_ne_zero_of_one_le_re (by simp; linarith)
    have hV_pos : 0 < xiNormSq σ γ := by
      dsimp [xiNormSq]
      have harg : (⟨1 / 2 + σ, γ⟩ : ℂ) = ((1 / 2 + σ : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
        apply Complex.ext <;> simp
      rw [harg]
      exact sq_pos_of_pos (norm_pos_iff.mpr hxi_ne)
    have hlogF := xiResolvent_im_eq_logForce_half hxi_ne
    have hLF_pos : 0 < xiLogForce σ γ := by linarith [hlogF.2]
    have hF_pos : 0 < deriv (fun t : ℝ => xiNormSq t γ) σ := by
      rw [xiLogForce_eq_force_div_normSq hV_pos] at hLF_pos
      exact (div_pos_iff_of_pos_right hV_pos).mp hLF_pos
    have hE_ne : xiShiftE σ (γ : ℂ) ≠ 0 := by
      dsimp [xiShiftE]
      exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
    have hphase := xiSchur_boundary_logDeriv_eq_I_mul_logForce hE_ne
    have hph_pos : 0 < (logDeriv (xiSchur σ) (γ : ℂ)).im := by
      rw [hphase.2]; simp; exact hLF_pos
    exact ⟨hR_pos, hF_pos, hLF_pos, hph_pos⟩
  refine ⟨hmain, fun α σ γ hα hσ hge => ?_⟩
  have hmono : StrictMonoOn (fun s : ℝ => xiNormSq s γ) (Set.Ici (7 / 2 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (7 / 2 : ℝ))
      (fun s _ => (hasDerivAt_xiNormSq_sigma s γ).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ici] at hs
    exact (hmain s γ (le_of_lt hs)).2.1
  have hlt_arg : |σ - α| < σ + α := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hV_lt : xiNormSq |σ - α| γ < xiNormSq (σ + α) γ :=
    hmono hge (le_trans hge (le_of_lt hlt_arg)) hlt_arg
  have hE_ne : xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0 := by
    dsimp [xiShiftE]
    exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hrat := xiSchur_norm_sq_eq_xiNormSq_ratio α σ γ
  have hden_pos : 0 < xiNormSq (σ + α) γ := by
    rw [← hrat.2.1]; exact sq_pos_of_pos (norm_pos_iff.mpr hE_ne)
  have hsq_lt : ‖xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ))‖ ^ 2 < 1 := by
    rw [hrat.2.2 hE_ne, div_lt_one hden_pos]; exact hV_lt
  nlinarith [norm_nonneg (xiSchur α ((γ : ℂ) + Complex.I * (σ : ℂ)))]

-- ==============================================================================
-- PART III: ROUTE B — HOPF-BLOCH SPHERE S^3 -> S^2 EMBEDDING OF (E_α, E_α^#),
--           NORTHERN HEMISPHERE EQUIVALENCE TO RIEMANN HYPOTHESIS, ACCUMULATED
--           DE BRANGES PHASE MEMORY, AND EXACT POISSON-WINDING QUANTIZATION
-- ==============================================================================

/-- Hopf-Bloch `X`-coordinate of the Hermite-Biehler pair `(E_α(z), E_α^#(z))` on `S^2`. -/
noncomputable def hopfBlochX (α : ℝ) (z : ℂ) : ℝ :=
  (2 * (starRingEnd ℂ (xiShiftE α z) * xiShiftE_sharp α z).re) /
    (‖xiShiftE α z‖ ^ 2 + ‖xiShiftE_sharp α z‖ ^ 2)

/-- Hopf-Bloch `Y`-coordinate of the Hermite-Biehler pair `(E_α(z), E_α^#(z))` on `S^2`. -/
noncomputable def hopfBlochY (α : ℝ) (z : ℂ) : ℝ :=
  (2 * (starRingEnd ℂ (xiShiftE α z) * xiShiftE_sharp α z).im) /
    (‖xiShiftE α z‖ ^ 2 + ‖xiShiftE_sharp α z‖ ^ 2)

/-- Hopf-Bloch `Z`-coordinate (hemisphere height) of `(E_α(z), E_α^#(z))` on `S^2`. -/
noncomputable def hopfBlochZ (α : ℝ) (z : ℂ) : ℝ :=
  (‖xiShiftE α z‖ ^ 2 - ‖xiShiftE_sharp α z‖ ^ 2) /
    (‖xiShiftE α z‖ ^ 2 + ‖xiShiftE_sharp α z‖ ^ 2)

/-- THEOREM III.1 (EXACT HOPF-BLOCH UNIT SPHERE `S^2` AND REAL-AXIS EQUATOR IDENTITY):
    For EVERY `α : ℝ`:
    (1) At every `z : ℂ` with `(E_α(z), E_α^#(z)) ≠ (0, 0)`, the Hopf projection lies on
        the exact unit sphere `S^2 ⊂ ℝ^3`:
          `X_α(z)^2 + Y_α(z)^2 + Z_α(z)^2 = 1`.
    (2) On the real axis `γ : ℝ` (whenever `E_α(γ) ≠ 0`), the trajectory lies on the
        exact equator `S^1 ⊂ S^2`:
          `Z_α(γ) = 0` and `X_α(γ)^2 + Y_α(γ)^2 = 1`. -/
theorem hopfBloch_unit_sphere_and_equator (α : ℝ) :
    (∀ z : ℂ, xiShiftE α z ≠ 0 ∨ xiShiftE_sharp α z ≠ 0 →
      hopfBlochX α z ^ 2 + hopfBlochY α z ^ 2 + hopfBlochZ α z ^ 2 = 1) ∧
    (∀ γ : ℝ, xiShiftE α (γ : ℂ) ≠ 0 →
      hopfBlochZ α (γ : ℂ) = 0 ∧ hopfBlochX α (γ : ℂ) ^ 2 + hopfBlochY α (γ : ℂ) ^ 2 = 1) := by
  have hsphere : ∀ z : ℂ, xiShiftE α z ≠ 0 ∨ xiShiftE_sharp α z ≠ 0 →
      hopfBlochX α z ^ 2 + hopfBlochY α z ^ 2 + hopfBlochZ α z ^ 2 = 1 := by
    intro z hne
    set a := xiShiftE α z
    set b := xiShiftE_sharp α z
    have hden_pos : 0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      rcases hne with ha | hb
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr ha)) (sq_nonneg _)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hb))
    have hxy : (starRingEnd ℂ a * b).re ^ 2 + (starRingEnd ℂ a * b).im ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
      have h1 : (starRingEnd ℂ a * b).re ^ 2 + (starRingEnd ℂ a * b).im ^ 2 =
          ‖starRingEnd ℂ a * b‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [h1, norm_mul, Complex.norm_conj, mul_pow]
    have hden_ne : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≠ 0 := ne_of_gt hden_pos
    have hgoal : (2 * (starRingEnd ℂ a * b).re) ^ 2 + (2 * (starRingEnd ℂ a * b).im) ^ 2 +
        (‖a‖ ^ 2 - ‖b‖ ^ 2) ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 := by nlinarith [hxy]
    dsimp [hopfBlochX, hopfBlochY, hopfBlochZ]
    change (2 * (starRingEnd ℂ a * b).re / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
      (2 * (starRingEnd ℂ a * b).im / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
      ((‖a‖ ^ 2 - ‖b‖ ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 = 1
    rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, hgoal, div_self (pow_ne_zero 2 hden_ne)]
  refine ⟨hsphere, fun γ hne => ?_⟩
  have hconj : xiShiftE_sharp α (γ : ℂ) = starRingEnd ℂ (xiShiftE α (γ : ℂ)) := by
    have h := (xiShiftE_schwarz_and_boundary_unitary α).1 (γ : ℂ)
    simpa using h
  have hnorm_eq : ‖xiShiftE_sharp α (γ : ℂ)‖ = ‖xiShiftE α (γ : ℂ)‖ := by
    rw [hconj, Complex.norm_conj]
  have hZ0 : hopfBlochZ α (γ : ℂ) = 0 := by
    dsimp [hopfBlochZ]; rw [hnorm_eq, sub_self, zero_div]
  have hsph := hsphere (γ : ℂ) (Or.inl hne)
  rw [hZ0] at hsph
  exact ⟨hZ0, by linarith⟩

/-- THEOREM III.2 (EXACT NORTHERN HEMISPHERE ↔ HERMITE-BIEHLER SCHUR CONTRACTION ↔
    POTENTIAL GRADIENT IDENTITY):
    For EVERY `α, σ, γ : ℝ` with `E_α(γ + iσ) ≠ 0`:
    (1) `Z_α(γ + iσ) = (1 - ‖S_α(γ + iσ)‖^2) / (1 + ‖S_α(γ + iσ)‖^2)`,
    (2) `Z_α(γ + iσ) = (V(α + σ, γ) - V(α - σ, γ)) / (V(α + σ, γ) + V(α - σ, γ))`,
    (3) `0 < Z_α(γ + iσ) ↔ ‖S_α(γ + iσ)‖ < 1` and `0 < Z_α(γ + iσ) ↔ V(α - σ, γ) < V(α + σ, γ)`,
    (4) Whenever `E_α^#(γ + iσ) ≠ 0`: `(1 + Z_α) / (1 - Z_α) = V(α + σ, γ) / V(α - σ, γ)`. -/
theorem hopfBloch_northern_hemisphere_iff_schur_and_potential (α σ γ : ℝ)
    (hE : xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0) :
    let z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
    hopfBlochZ α z = (1 - ‖xiSchur α z‖ ^ 2) / (1 + ‖xiSchur α z‖ ^ 2) ∧
    hopfBlochZ α z = (xiNormSq (α + σ) γ - xiNormSq (α - σ) γ) /
      (xiNormSq (α + σ) γ + xiNormSq (α - σ) γ) ∧
    (0 < hopfBlochZ α z ↔ ‖xiSchur α z‖ < 1) ∧
    (0 < hopfBlochZ α z ↔ xiNormSq (α - σ) γ < xiNormSq (α + σ) γ) ∧
    (xiShiftE_sharp α z ≠ 0 →
      (1 + hopfBlochZ α z) / (1 - hopfBlochZ α z) = xiNormSq (α + σ) γ / xiNormSq (α - σ) γ) := by
  intro z
  have hpot := (xiShiftE_schwarz_and_boundary_unitary α).2.2.2 σ γ
  have hE_pos : 0 < ‖xiShiftE α z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hE)
  have hE_ne : ‖xiShiftE α z‖ ^ 2 ≠ 0 := ne_of_gt hE_pos
  have hS_sq : ‖xiSchur α z‖ ^ 2 = ‖xiShiftE_sharp α z‖ ^ 2 / ‖xiShiftE α z‖ ^ 2 := by
    dsimp [xiSchur]; rw [norm_div, div_pow]
  have hZ_schur : hopfBlochZ α z = (1 - ‖xiSchur α z‖ ^ 2) / (1 + ‖xiSchur α z‖ ^ 2) := by
    dsimp [hopfBlochZ]
    rw [hS_sq]
    have hden1 : ‖xiShiftE α z‖ ^ 2 + ‖xiShiftE_sharp α z‖ ^ 2 ≠ 0 := by positivity
    have hden2 : 1 + ‖xiShiftE_sharp α z‖ ^ 2 / ‖xiShiftE α z‖ ^ 2 ≠ 0 := by positivity
    have hnorm_ne : ‖xiShiftE α z‖ ≠ 0 := norm_ne_zero_iff.mpr hE
    field_simp [hnorm_ne, hden1, hden2]
  have hZ_pot : hopfBlochZ α z = (xiNormSq (α + σ) γ - xiNormSq (α - σ) γ) /
      (xiNormSq (α + σ) γ + xiNormSq (α - σ) γ) := by
    dsimp [hopfBlochZ]; rw [hpot.1, hpot.2]
  have hiff_schur : 0 < hopfBlochZ α z ↔ ‖xiSchur α z‖ < 1 := by
    rw [hZ_schur, div_pos_iff_of_pos_right (by positivity)]
    constructor
    · intro h; nlinarith [norm_nonneg (xiSchur α z)]
    · intro h; nlinarith [norm_nonneg (xiSchur α z)]
  have hiff_pot : 0 < hopfBlochZ α z ↔ xiNormSq (α - σ) γ < xiNormSq (α + σ) γ := by
    have hden_pos : 0 < xiNormSq (α + σ) γ + xiNormSq (α - σ) γ := by
      rw [← hpot.1, ← hpot.2]; positivity
    rw [hZ_pot, div_pos_iff_of_pos_right hden_pos]
    constructor <;> intro h <;> linarith
  refine ⟨hZ_schur, hZ_pot, hiff_schur, hiff_pot, fun hEs => ?_⟩
  have hEs_pos : 0 < xiNormSq (α - σ) γ := by
    rw [← hpot.2]; exact sq_pos_of_pos (norm_pos_iff.mpr hEs)
  have hden_pos : 0 < xiNormSq (α + σ) γ + xiNormSq (α - σ) γ := by
    rw [← hpot.1, ← hpot.2]; positivity
  rw [hZ_pot]
  have hden_ne : xiNormSq (α + σ) γ + xiNormSq (α - σ) γ ≠ 0 := ne_of_gt hden_pos
  have hEs_ne : xiNormSq (α - σ) γ ≠ 0 := ne_of_gt hEs_pos
  have hsub_ne : 1 - (xiNormSq (α + σ) γ - xiNormSq (α - σ) γ) /
      (xiNormSq (α + σ) γ + xiNormSq (α - σ) γ) ≠ 0 := by
    have heq : 1 - (xiNormSq (α + σ) γ - xiNormSq (α - σ) γ) /
        (xiNormSq (α + σ) γ + xiNormSq (α - σ) γ) =
        2 * xiNormSq (α - σ) γ / (xiNormSq (α + σ) γ + xiNormSq (α - σ) γ) := by
      field_simp [hden_ne]; ring
    rw [heq]; exact div_ne_zero (mul_ne_zero (by norm_num) hEs_ne) hden_ne
  field_simp [hden_ne, hEs_ne, hsub_ne]; ring

/-- THEOREM III.3A (GLOBAL HOPF-BLOCH NORTHERN HEMISPHERE REDUCTION TO MATHLIB4's `RiemannHypothesis`):
    If for every `α ∈ (0, 1/2)` and every upper half-plane point `z ∈ ℍ`, the Hopf-Bloch
    projection of `(E_α(z), E_α^#(z))` is strictly confined to the Open Northern Hemisphere
    `0 < hopfBlochZ α z` of `S^2`, then Mathlib4's official `RiemannHypothesis` holds! -/
theorem riemannHypothesis_of_hopfBloch_northern_hemisphere
    (hNorth : ∀ α : ℝ, 0 < α → α < 1 / 2 →
      ∀ z : ℂ, 0 < z.im → 0 < hopfBlochZ α z) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hermiteBiehler_all
  intro α hα0 hα1 σ γ hσ
  set z : ℂ := (γ : ℂ) + Complex.I * (σ : ℂ)
  have hz : 0 < z.im := by dsimp [z]; simp; exact hσ
  have hZ := hNorth α hα0 hα1 z hz
  dsimp [hopfBlochZ] at hZ
  have hden_pos : 0 < ‖xiShiftE α z‖ ^ 2 + ‖xiShiftE_sharp α z‖ ^ 2 := by
    by_contra hle
    push Not at hle
    have h0 : ‖xiShiftE α z‖ ^ 2 + ‖xiShiftE_sharp α z‖ ^ 2 = 0 :=
      le_antisymm hle (by positivity)
    rw [h0, div_zero] at hZ
    linarith
  have hnum_pos : 0 < ‖xiShiftE α z‖ ^ 2 - ‖xiShiftE_sharp α z‖ ^ 2 :=
    (div_pos_iff_of_pos_right hden_pos).mp hZ
  nlinarith [norm_nonneg (xiShiftE α z), norm_nonneg (xiShiftE_sharp α z)]

/-- THEOREM III.3B (UNCONDITIONAL NORTHERN HEMISPHERE CONFINEMENT ON THE DESCENDED EULER
    HALF-PLANE `7/2 ≤ |σ - α|` FOR ALL `γ ∈ ℝ`!):
    Directly from Theorem II.3 and Theorem III.2, for EVERY `α > 0`, `σ > 0`, and `γ ∈ ℝ`
    with `7 / 2 ≤ |σ - α|`:
      `0 < hopfBlochZ α (γ + iσ)`. -/
theorem hopfBloch_northern_hemisphere_unconditional_euler_seven_halves
    {α σ γ : ℝ} (hα : 0 < α) (hσ : 0 < σ) (hge : 7 / 2 ≤ |σ - α|) :
    0 < hopfBlochZ α ((γ : ℂ) + Complex.I * (σ : ℂ)) := by
  have hE : xiShiftE α ((γ : ℂ) + Complex.I * (σ : ℂ)) ≠ 0 := by
    dsimp [xiShiftE]
    have hsum : 7 / 2 ≤ σ + α := by
      rcases le_total α σ with h | h
      · rw [abs_of_nonneg (by linarith)] at hge; linarith
      · rw [abs_of_nonpos (by linarith)] at hge; linarith
    exact riemannXi_ne_zero_of_one_le_re (by simp; linarith)
  have hschur := xiResolvent_herglotz_global_euler_halfPlane_seven_halves.2 α σ γ hα hσ hge
  exact (hopfBloch_northern_hemisphere_iff_schur_and_potential α σ γ hE).2.2.1.mpr hschur

/-- Accumulated de Branges equatorial phase memory on `[γ₁, γ₂]` at level `α`:
    `ΔΦ_α(γ₁, γ₂) = ∫_{γ₁}^{γ₂} 2 * Im(R_ξ(t + iα)) dt`. -/
noncomputable def deBrangesPhaseMemory (α γ₁ γ₂ : ℝ) : ℝ :=
  ∫ t in γ₁..γ₂, 2 * (xiResolvent ((t : ℂ) + Complex.I * (α : ℂ))).im

/-- Helper: Continuity of `t ↦ (xiResolvent (t + iα)).im` on any region where `Re(1/2 + α) ≥ 1`. -/
private lemma continuous_xiResolvent_im_of_half_lt {α : ℝ} (hα : 1 / 2 < α) :
    Continuous (fun t : ℝ => (xiResolvent ((t : ℂ) + Complex.I * (α : ℂ))).im) := by
  have hdiff_all : ∀ t : ℝ, ContinuousAt (fun x : ℝ => (xiResolvent ((x : ℂ) + Complex.I * (α : ℂ))).im) t := by
    intro t
    have hxi_ne' : riemannXi (1 / 2 - Complex.I * ((t : ℂ) + Complex.I * (α : ℂ))) ≠ 0 := by
      have hre : 1 ≤ (1 / 2 - Complex.I * ((t : ℂ) + Complex.I * (α : ℂ))).re := by simp; linarith
      exact riemannXi_ne_zero_of_one_le_re hre
    have hmap : Continuous (fun x : ℝ => 1 / 2 - Complex.I * ((x : ℂ) + Complex.I * (α : ℂ))) :=
      continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.add continuous_const))
    have hxi_diff : Differentiable ℂ riemannXi := riemannXi_entire
    have hderiv_cont : Continuous (deriv riemannXi) := differentiable_deriv_riemannXi.continuous
    have hres_cont : ContinuousAt (fun x : ℝ => xiResolvent ((x : ℂ) + Complex.I * (α : ℂ))) t := by
      dsimp [xiResolvent, logDeriv]
      exact continuousAt_const.mul
        ((hderiv_cont.comp hmap).continuousAt.div (hxi_diff.continuous.comp hmap).continuousAt hxi_ne')
    exact Complex.continuous_im.continuousAt.comp hres_cont
  exact continuous_iff_continuousAt.mpr hdiff_all

/-- THEOREM III.4A (STRICTLY POSITIVE ACCUMULATED DE BRANGES PHASE MEMORY ON ALL OF `ℝ` FOR `α ≥ 7/2`):
    For EVERY `α ≥ 7 / 2` and EVERY `γ₁ < γ₂`:
      `0 < deBrangesPhaseMemory α γ₁ γ₂ = ∫_{γ₁}^{γ₂} 2 * Im R_ξ(t + iα) dt`,
    certifying strictly monotone forward equatorial phase accumulation with zero retrograde phase slips. -/
theorem deBrangesPhaseMemory_pos_unconditional_euler_seven_halves {α γ₁ γ₂ : ℝ}
    (hα : 7 / 2 ≤ α) (hγ : γ₁ < γ₂) :
    0 < deBrangesPhaseMemory α γ₁ γ₂ := by
  dsimp [deBrangesPhaseMemory]
  have hcont : Continuous (fun t : ℝ => 2 * (xiResolvent ((t : ℂ) + Complex.I * (α : ℂ))).im) :=
    continuous_const.mul (continuous_xiResolvent_im_of_half_lt (by linarith))
  exact intervalIntegral.integral_pos hγ hcont.continuousOn
    (fun t _ => le_of_lt (mul_pos (by norm_num) (xiResolvent_herglotz_global_euler_halfPlane_seven_halves.1 α t hα).1))
    ⟨γ₁, Set.left_mem_Icc.mpr (le_of_lt hγ),
      mul_pos (by norm_num) (xiResolvent_herglotz_global_euler_halfPlane_seven_halves.1 α γ₁ hα).1⟩

/-- Helper: Exact Poisson kernel integral `∫_{-∞}^{∞} η / ((t - γ)^2 + η^2) dt = π` for `η > 0`. -/
private lemma integral_poisson_kernel_eq_pi (γ : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun t : ℝ => η / ((t - γ) ^ 2 + η ^ 2)) ∧
    ∫ t : ℝ, η / ((t - γ) ^ 2 + η ^ 2) = Real.pi := by
  have hbase : ∫ x : ℝ, (1 + x ^ 2)⁻¹ = Real.pi := integral_univ_inv_one_add_sq
  have hint_base : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hrew : (fun t : ℝ => η / ((t - γ) ^ 2 + η ^ 2)) =
      fun t => η⁻¹ * (1 + (η⁻¹ * (t - γ)) ^ 2)⁻¹ := by
    ext t
    have hη_ne : η ≠ 0 := ne_of_gt hη
    have hden : (t - γ) ^ 2 + η ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hden2 : 1 + (η⁻¹ * (t - γ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hη_ne, hden, hden2]; ring
  have hint1 : Integrable (fun t : ℝ => (1 + (η⁻¹ * t) ^ 2)⁻¹) :=
    hint_base.comp_mul_left' (inv_ne_zero (ne_of_gt hη))
  have hint2 : Integrable (fun t : ℝ => (1 + (η⁻¹ * (t - γ)) ^ 2)⁻¹) :=
    hint1.comp_sub_right γ
  have hint3 : Integrable (fun t : ℝ => η / ((t - γ) ^ 2 + η ^ 2)) := by
    rw [hrew]; exact hint2.const_mul η⁻¹
  refine ⟨hint3, ?_⟩
  rw [hrew, integral_const_mul, integral_sub_right_eq_self (fun t : ℝ => (1 + (η⁻¹ * t) ^ 2)⁻¹) γ,
      Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) η⁻¹, hbase,
      inv_inv, abs_of_pos hη, smul_eq_mul]
  field_simp [ne_of_gt hη]

/-- Helper: Integrability of a finite sum of integrable real functions. -/
private lemma integrable_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i)) :
    Integrable (fun t : ℝ => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact integrable_zero _ _ _
  | insert k t hk ih =>
    have hr : (fun u : ℝ => ∑ i ∈ insert k t, f i u) = fun u => f k u + ∑ i ∈ t, f i u := by
      ext u; exact Finset.sum_insert hk
    rw [hr]
    exact (hf k (Finset.mem_insert_self k t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Helper: Bochner integral of a finite sum of integrable real functions. -/
private lemma bochner_integral_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i)) :
    ∫ t : ℝ, (∑ i ∈ s, f i t) = ∑ i ∈ s, ∫ t : ℝ, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hrew : (fun t : ℝ => ∑ i ∈ insert a s, f i t) = fun t => f a t + ∑ i ∈ s, f i t := by
      ext t; exact Finset.sum_insert ha
    have hsum_int : Integrable (fun t : ℝ => ∑ i ∈ s, f i t) :=
      integrable_finset_sum' s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [hrew, integral_add (hf a (Finset.mem_insert_self a s)) hsum_int,
        Finset.sum_insert ha, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- THEOREM III.4B (EXACT TOPOLOGICAL POISSON-WINDING QUANTIZATION FOR ANY FINITE UPPER
    HALF-PLANE ZERO SPECTRUM):
    For EVERY `N : ℕ` and EVERY collection of `N` upper half-plane poles/zeros
    `γ_j + i η_j` (`0 < η_j`), the total normalized Poisson phase integral over `ℝ`
    is EXACTLY quantized to the integer zero count `N`:
      `(1 / π) * ∫_{-∞}^{∞} (∑ j : Fin N, η_j / ((t - γ_j)^2 + η_j^2)) dt = (N : ℝ)`. -/
theorem poisson_winding_number_quantization {N : ℕ} (γ η : Fin N → ℝ) (hη : ∀ j, 0 < η j) :
    (1 / Real.pi) * ∫ t : ℝ, (∑ j : Fin N, η j / ((t - γ j) ^ 2 + (η j) ^ 2)) = (N : ℝ) := by
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      Integrable (fun t : ℝ => η j / ((t - γ j) ^ 2 + (η j) ^ 2)) :=
    fun j _ => (integral_poisson_kernel_eq_pi (γ j) (hη j)).1
  rw [bochner_integral_finset_sum Finset.univ hint]
  have hsum : ∑ j : Fin N, ∫ t : ℝ, η j / ((t - γ j) ^ 2 + (η j) ^ 2) = (N : ℝ) * Real.pi := by
    have hpt : ∀ j : Fin N, ∫ t : ℝ, η j / ((t - γ j) ^ 2 + (η j) ^ 2) = Real.pi :=
      fun j => (integral_poisson_kernel_eq_pi (γ j) (hη j)).2
    simp_rw [hpt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  field_simp [ne_of_gt Real.pi_pos]

end CompactMomentWeilAndHopfBlochEulerDescent
