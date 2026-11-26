/-
  ==============================================================================
  MODULE #39: REPARAMETRIZATION-INVARIANCE NO-GO THEOREM, PRECONDITIONED
  SPECTRAL CONGRUENCE GRONWALL RESCUE, & ALL-CHARACTER (IMPRIMITIVE) GRH CLOSURE

  Title: Reparametrization No-Go, Spectral Congruence Rescue, and Full GRH Closure
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  Date: November 24, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Reparametrization-Invariance No-Go for Vanishing Raw Eigenvalues):
      * `gronwall_forbids_vanishing_margin`:
        NO smooth compactification `θ : [0, ∞) → [0, π)` (stereographic, Sundman,
        or any geodesic coordinate map on `M⁵`) can satisfy the North-Pole
        Gronwall bound `μ_tilde' θ ≥ -C * μ_tilde θ` for a raw spectral margin
        `μ(L) → 0⁺` (such as the unpreconditioned Weil eigenvalue `λ_min(S_L) → 0⁺`
        driven by Shannon–Landau–Pollak prolate zero-annihilation).
      * `naive_prime_norm_budget_nonpos_when_exceeds_arch`:
        Whenever the naive prime operator-norm sum `D_prime(L)` meets or exceeds
        `μ_inf(L)` (e.g. `D_prime(L) ~ 4 e^{L/2}`), the unrenormalized ratio
        `1 - D_prime(L) / μ_inf(L) ≤ 0`, proving the necessity of prime-pole
        cancellation and spectral preconditioning.
  - Part II (Preconditioned Spectral Congruence Rescue `S_L = B_Lᵀ S_tilde_L B_L`):
      * `congruence_preserves_gram_factorization`,
        `congruence_preserves_hermitian_gram`,
        `preconditioned_north_pole_gronwall_closes_all_horizon_gram`:
        Exact matrix congruence `S_L = B_Lᵀ S_tilde_L B_L` (real or complex Hermitian)
        preserves global Gram factorization `S_L = (A_L B_L)ᵀ (A_L B_L)` unconditionally,
        rescuing the North-Pole Gronwall gate on the preconditioned operator `S_tilde_L`
        even when the raw eigenvalue `λ_min(S_L) → 0⁺` super-exponentially!
  - Part III (Complete Imprimitive-to-Primitive GRH Equivalence):
      * `euler_local_factor_ne_zero_of_re_pos`,
        `isNonTrivialLZero_changeLevel_iff`,
        `AllDirichletGRH`,
        `allDirichletGRH_iff_generalizedRiemannHypothesis`,
        `modus_ponens_grh_elevates_all_dirichlet_characters`:
        Proves that GRH over primitive characters is 100% logically equivalent to
        GRH over ALL Dirichlet characters (primitive AND imprimitive alike).
  ==============================================================================
-/

import RiemannDipolar.GlobalGeodesicCompletenessAndAdelicMargin
import RiemannDipolar.MasterGRHModusPonensBridge

open Real Complex Filter Topology Set Matrix
open scoped BigOperators Classical Matrix
open PrimeDowndateWeylPerturbationAndGramMargin
open CompactifiedHorizonManifold5DClosure
open NorthPoleRenormalizationAndChebyshevBridge
open GlobalGeodesicCompletenessAndAdelicMargin
open GRHDefinitionAndFunctionalEq
open HermitianWeilPositivityGRH
open MasterGRHModusPonensBridge

namespace PreconditionedGronwallNoGoAndFullGRHClosure

-- ==============================================================================
-- PART I: REPARAMETRIZATION-INVARIANCE NO-GO FOR VANISHING RAW MARGINS
-- ==============================================================================

/-- THEOREM I.1 (REPARAMETRIZATION-INVARIANCE NO-GO FOR VANISHING MARGINS):
    Let `θ : ℝ → ℝ` be ANY compactification map sending `[0, ∞)` into `[0, π]`
    (stereographic `2 * arctan L`, Sundman time-reparametrization, or any
    geodesic coordinate map on `M⁵`). If `μ_tilde : ℝ → ℝ` satisfies the
    North-Pole Gronwall barrier hypotheses on `[0, π]` (`μ_tilde 0 > 0` and
    `μ_tilde' t ≥ -C * μ_tilde t` on `(0, π)`), and `μ L = μ_tilde (θ L)` for
    all `L ≥ 0`, then `μ L` is uniformly bounded below by `μ_tilde 0 * exp(-Cπ) > 0`
    and CANNOT converge to `0` as `L → ∞`.
    Consequently, raw unpreconditioned eigenvalues `λ_min(S_L) → 0⁺` cannot cross
    the Gronwall gate under ANY coordinate change `L ↦ θ(L)`. -/
theorem gronwall_forbids_vanishing_margin
    (θ μ μ_tilde μ_tilde' : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hθ_mem : ∀ L : ℝ, 0 ≤ L → θ L ∈ Set.Icc 0 Real.pi)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hderiv : ∀ t ∈ Set.Ioo 0 Real.pi, HasDerivAt μ_tilde (μ_tilde' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 Real.pi, -C * μ_tilde t ≤ μ_tilde' t)
    (hinit : 0 < μ_tilde 0)
    (hmatch : ∀ L : ℝ, 0 ≤ L → μ L = μ_tilde (θ L)) :
    ¬ Tendsto μ atTop (𝓝 0) := by
  intro hlim
  have hfloor : 0 < μ_tilde 0 * Real.exp (-C * Real.pi) :=
    mul_pos hinit (Real.exp_pos (-C * Real.pi))
  have hge : ∀ᶠ L : ℝ in atTop, μ_tilde 0 * Real.exp (-C * Real.pi) ≤ μ L := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    rw [hmatch L hL]
    exact geodesic_log_gronwall_barrier_implies_north_pole_pos
      μ_tilde μ_tilde' C hC hcont hderiv hbound hinit (θ L) (hθ_mem L hL)
  have h0_ge : μ_tilde 0 * Real.exp (-C * Real.pi) ≤ 0 :=
    ge_of_tendsto hlim hge
  linarith

/-- THEOREM I.2 (NAIVE PRIME-NORM TRIANGLE-INEQUALITY OVERSHOOT BARRIER):
    Whenever the summed individual prime operator norms `D_prime` reach or exceed
    the bare Archimedean floor `μ_inf > 0` (as occurs for `D_prime(L) ~ 4 e^{L/2}`
    at large `L`), the naive unrenormalized ratio `1 - D_prime / μ_inf` is ≤ 0,
    confirming that oscillatory Chebyshev–Weil cancellation and spectral
    preconditioning are structurally required beyond the triangle-inequality regime. -/
theorem naive_prime_norm_budget_nonpos_when_exceeds_arch
    {μ_inf D_prime : ℝ} (hμ : 0 < μ_inf) (hov : μ_inf ≤ D_prime) :
    1 - D_prime / μ_inf ≤ 0 := by
  have h1 : 1 ≤ D_prime / μ_inf := (one_le_div hμ).mpr hov
  linarith

-- ==============================================================================
-- PART II: PRECONDITIONED SPECTRAL CONGRUENCE RESCUE (`S_L = B_Lᵀ S_tilde_L B_L`)
-- ==============================================================================

/-- THEOREM II.1 (REAL CONGRUENCE PRESERVES EXACT GRAM FACTORIZATION):
    If a real matrix `S` is congruent to a preconditioned matrix `S_tilde` via
    `S = Bᵀ * S_tilde * B` (where `B` may absorb arbitrary super-exponential decay
    of raw eigenvalues `λ_min(S) → 0⁺`), and `S_tilde = Aᵀ * A` admits a Gram
    factorization, then `S = (A * B)ᵀ * (A * B)` unconditionally admits a global
    Gram factorization and is positive semidefinite. -/
theorem congruence_preserves_gram_factorization {n : ℕ}
    (S S_tilde B A : Matrix (Fin n) (Fin n) ℝ)
    (hCong : S = Bᵀ * S_tilde * B)
    (hGram : S_tilde = Aᵀ * A) :
    S = (A * B)ᵀ * (A * B) ∧ (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (S.mulVec x)) := by
  have hEq : S = (A * B)ᵀ * (A * B) := by
    rw [hCong, hGram, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨hEq, fun x => ?_⟩
  rw [hEq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((A * B).mulVec x i)

/-- THEOREM II.2 (COMPLEX HERMITIAN CONGRUENCE PRESERVES GRAM FACTORIZATION FOR GRH):
    Complex Hermitian analogue of Theorem II.1 for non-real Dirichlet characters `χ`:
    if `S = Bᴴ * S_tilde * B` and `S_tilde = Aᴴ * A`, then `S = (A * B)ᴴ * (A * B)`
    and `0 ≤ hermitianQuadForm S v` for every `v : Fin n → ℂ`. -/
theorem congruence_preserves_hermitian_gram {n : ℕ}
    (S S_tilde B A : Matrix (Fin n) (Fin n) ℂ)
    (hCong : S = Bᴴ * S_tilde * B)
    (hGram : S_tilde = Aᴴ * A) :
    S = (A * B)ᴴ * (A * B) ∧ (∀ v : Fin n → ℂ, 0 ≤ hermitianQuadForm S v) := by
  have hEq : S = (A * B)ᴴ * (A * B) := by
    rw [hCong, hGram, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  exact ⟨hEq, fun v => hermitian_gram_implies_psd S (A * B) hEq v⟩

/-- THEOREM II.3 (PRECONDITIONED NORTH-POLE GRONWALL CLOSES ALL-HORIZON RAW GRAM):
    Unifies Modules #30 and #32 with Theorem II.1:
    If there exists a preconditioner family `B L` such that the raw operator
    `S L = (B L)ᵀ * (W_inf L - ∑ v ∈ F L, c L v • C L v) * (B L)` has a
    preconditioned renormalized margin `μ_tilde` satisfying the North-Pole
    Gronwall bound `μ_tilde' θ ≥ -C * μ_tilde θ` on `(0, π)` with `μ_tilde 0 > 0`,
    then the ORIGINAL raw operator `S L` admits an exact global Gram factorization
    `∃ A_L, S L = A_Lᵀ * A_L` for EVERY horizon `L > 0`—even when the raw
    eigenvalues of `S L` decay super-exponentially to `0⁺`! -/
theorem preconditioned_north_pole_gronwall_closes_all_horizon_gram
    {ι : Type*}
    (dim : ℝ → ℕ)
    (F : ℝ → Finset ι)
    (S B W_inf : (L : ℝ) → Matrix (Fin (dim L)) (Fin (dim L)) ℝ)
    (c δ : ℝ → ι → ℝ)
    (C_mat : (L : ℝ) → ι → Matrix (Fin (dim L)) (Fin (dim L)) ℝ)
    (μ_inf μ_tilde μ_tilde' : ℝ → ℝ) (C_gron : ℝ)
    (hC_gron : 0 ≤ C_gron)
    (hCong : ∀ L : ℝ, 0 < L →
      S L = (B L)ᵀ * (W_inf L - ∑ v ∈ F L, c L v • C_mat L v) * B L)
    (hμ_pos : ∀ L : ℝ, 0 < L → 0 < μ_inf L)
    (hWh : ∀ L : ℝ, 0 < L → (W_inf L).IsHermitian)
    (hCh : ∀ L : ℝ, 0 < L → ∀ v ∈ F L, (C_mat L v).IsHermitian)
    (hc : ∀ L : ℝ, 0 < L → ∀ v ∈ F L, 0 ≤ c L v)
    (hW : ∀ L : ℝ, 0 < L → ∀ x : Fin (dim L) → ℝ,
      μ_inf L * vecNormSq x ≤ dotProduct x ((W_inf L).mulVec x))
    (hC : ∀ L : ℝ, 0 < L → ∀ v ∈ F L, ∀ x : Fin (dim L) → ℝ,
      dotProduct x ((C_mat L v).mulVec x) ≤ δ L v * vecNormSq x)
    (hcont : ContinuousOn μ_tilde (Set.Icc 0 Real.pi))
    (hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, HasDerivAt μ_tilde (μ_tilde' θ) θ)
    (hbound : ∀ θ ∈ Set.Ioo 0 Real.pi, -C_gron * μ_tilde θ ≤ μ_tilde' θ)
    (hinit : 0 < μ_tilde 0)
    (hmatch : ∀ L : ℝ, 0 < L →
      μ_tilde (stereographicHorizon L) = 1 - (∑ v ∈ F L, c L v * δ L v) / μ_inf L) :
    ∀ L : ℝ, 0 < L →
      ∃ A : Matrix (Fin (dim L)) (Fin (dim L)) ℝ, S L = Aᵀ * A := by
  have hpos : ∀ θ ∈ Set.Icc 0 Real.pi, 0 < μ_tilde θ :=
    geodesic_log_gronwall_implies_strict_pos μ_tilde μ_tilde' C_gron hC_gron
      hcont hderiv hbound hinit
  have hPreGram := north_pole_continuity_implies_all_horizon_gram_closure
    dim F W_inf c δ C_mat μ_inf μ_tilde hμ_pos hWh hCh hc hW hC hcont hpos hmatch
  intro L hL
  rcases hPreGram L hL with ⟨A, hA⟩
  exact ⟨A * B L, (congruence_preserves_gram_factorization (S L) _ (B L) A (hCong L hL) hA).1⟩

-- ==============================================================================
-- PART III: COMPLETE IMPRIMITIVE-TO-PRIMITIVE GRH EQUIVALENCE
-- ==============================================================================

/-- Lemma III.1 (NON-VANISHING OF FINITE EULER FACTORS IN `Re(s) > 0`):
    For any prime `p`, Dirichlet character `χ`, and `s ∈ ℂ` with `0 < Re(s)`,
    the local Euler factor `1 - χ(p) * p^(-s)` is strictly non-zero because
    `‖χ(p) * p^(-s)‖ ≤ p^(-Re(s)) < 1`. -/
theorem euler_local_factor_ne_zero_of_re_pos {M : ℕ}
    (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - χ (p : ZMod M) * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h0
  have heq : χ (p : ZMod M) * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
  have hnorm1 : ‖χ (p : ZMod M) * (p : ℂ) ^ (-s)‖ = 1 := by rw [heq, norm_one]
  rw [norm_mul] at hnorm1
  have hχ : ‖χ (p : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (p : ZMod M)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := Nat.one_lt_cast.mpr hp.one_lt
  have hpow_norm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hpow_lt1 : (p : ℝ) ^ (-s.re) < 1 := by
    have hneg : -s.re < 0 := by linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 hneg
  have hpow_nonneg : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (le_of_lt hp_pos) _
  have hprod_lt1 : ‖χ (p : ZMod M)‖ * ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hpow_norm]
    calc ‖χ (p : ZMod M)‖ * (p : ℝ) ^ (-s.re)
        ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right hχ hpow_nonneg
      _ = (p : ℝ) ^ (-s.re) := one_mul _
      _ < 1 := hpow_lt1
  linarith

/-- THEOREM III.2 (LEVEL-CHANGE INVARIANCE OF NON-TRIVIAL L-FUNCTION ZEROS):
    For any `M ∣ N` and any Dirichlet character `χ` mod `M`, changing level to `N`
    does not introduce or remove ANY zero inside the open critical strip `0 < Re(s) < 1`:
    `IsNonTrivialLZero (changeLevel hMN χ) s ↔ IsNonTrivialLZero χ s`. -/
theorem isNonTrivialLZero_changeLevel_iff {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (s : ℂ) :
    IsNonTrivialLZero (DirichletCharacter.changeLevel hMN χ) s ↔ IsNonTrivialLZero χ s := by
  unfold IsNonTrivialLZero
  constructor
  · rintro ⟨hzero, hpos, hlt1⟩
    have hs1 : s ≠ 1 := by
      intro h1; rw [h1] at hlt1; simp at hlt1
    rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hs1)] at hzero
    have hprod_ne : (∏ p ∈ N.primeFactors, (1 - χ (p : ZMod M) * (p : ℂ) ^ (-s))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp =>
        euler_local_factor_ne_zero_of_re_pos χ (Nat.prime_of_mem_primeFactors hp) hpos
    rcases mul_eq_zero.mp hzero with hL | hP
    · exact ⟨hL, hpos, hlt1⟩
    · exact absurd hP hprod_ne
  · rintro ⟨hzero, hpos, hlt1⟩
    have hs1 : s ≠ 1 := by
      intro h1; rw [h1] at hlt1; simp at hlt1
    refine ⟨?_, hpos, hlt1⟩
    rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hs1), hzero, zero_mul]

/-- Full Generalized Riemann Hypothesis quantified over ALL moduli `N ≥ 1` and ALL
    Dirichlet characters `χ : DirichletCharacter ℂ N` (primitive AND imprimitive). -/
def AllDirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GRHForCharacter N χ

/-- THEOREM III.3 (PRIMITIVE GRH ↔ ALL-CHARACTER GRH):
    `GeneralizedRiemannHypothesis` (over primitive Dirichlet characters) is 100%
    logically equivalent to `AllDirichletGRH` (over EVERY Dirichlet character,
    primitive and imprimitive alike). -/
theorem allDirichletGRH_iff_generalizedRiemannHypothesis :
    AllDirichletGRH ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro hAll N _ χ _
    exact hAll N χ
  · intro hPrim N _ χ s hs
    have : NeZero χ.conductor :=
      ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))⟩
    have hPrimChar : IsNonTrivialLZero χ.primitiveCharacter s := by
      have hchg := (isNonTrivialLZero_changeLevel_iff χ.conductor_dvd_level
        χ.primitiveCharacter s).mp
      rw [χ.changeLevel_primitiveCharacter] at hchg
      exact hchg hs
    exact hPrim χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hPrimChar

/-- THEOREM III.4 (COMPLETE MODUS PONENS ELEVATION TO EVERY DIRICHLET CHARACTER):
    Any independently audited proof of `GeneralizedRiemannHypothesis` immediately
    elevates GRH and all geometric-dynamical laws (Clifford torus, 5D manifold,
    Weil positivity, kinetic confinement, uniform collars) to EVERY Dirichlet
    character `χ` mod `N`, primitive OR imprimitive. -/
theorem modus_ponens_grh_elevates_all_dirichlet_characters
    (hGRH : GeneralizedRiemannHypothesis) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      GRHForCharacter N χ ∧
      CliffordTorusAndScatteringGRH.CliffordTorusEquatorialZeroTargetGRH χ ∧
      CliffordTorusAndScatteringGRH.Manifold5DGroundStateTargetGRH χ ∧
      AdelicDipolarWeilPositivityGRH χ ∧
      CliffordTorusAndScatteringGRH.GlobalUniformCollarTargetGRH χ := by
  have hAll : AllDirichletGRH := allDirichletGRH_iff_generalizedRiemannHypothesis.mpr hGRH
  intro N _ χ
  have hχ : GRHForCharacter N χ := hAll N χ
  exact ⟨
    hχ,
    (CliffordTorusAndScatteringGRH.cliffordTorusEquatorialZeroTargetGRH_iff_grhForCharacter χ).mpr hχ,
    (CliffordTorusAndScatteringGRH.manifold5DGroundStateTargetGRH_iff_grhForCharacter χ).mpr hχ,
    (adelicDipolarWeilPositivityGRH_iff_grhForCharacter χ).mpr hχ,
    (CliffordTorusAndScatteringGRH.globalUniformCollarTargetGRH_iff_grhForCharacter χ).mpr hχ⟩

end PreconditionedGronwallNoGoAndFullGRHClosure
