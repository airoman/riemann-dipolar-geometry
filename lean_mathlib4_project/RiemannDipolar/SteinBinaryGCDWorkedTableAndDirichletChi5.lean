/-
  ==============================================================================
  MODULE #42: STEIN'S BINARY GCD SIEVE, KERNEL-VERIFIED WORKED TABLE (N = 2..23),
  TOTAL BASIN EUCLIDEAN ENERGY `g(g-1)(2g-1)/3`, PENTAGONAL `2 cos(π/5) = φ`,
  & PRIMITIVE REAL QUADRATIC GOLDEN CHARACTER `χ₅` (`L(1, χ₅) ≠ 0`)

  Title: Algorithmic Sieve Foundations, Worked Lattice Certification, Total Basin
         Energy, and Golden Quadratic Dirichlet L-Function Binding
  Author: Mariano Martín Ramírez Tamayo (Independent Researcher)
  ORCID: https://orcid.org/0009-0005-6194-1845
  Date: November 25, 2026

  SUMMARY OF MACHINE-VERIFIED RESULTS (0 sorry, 0 custom axioms):
  - Part I (Stein's Binary GCD Recurrences & Square-Root Coprimality Sieve):
      * `stein_gcd_even_even`, `stein_gcd_even_odd`,
        `stein_gcd_odd_even`, `stein_gcd_odd_odd_le`:
        Exact division-free bit-shift and odd-subtraction recurrences of Stein's
        Binary GCD algorithm (1967).
      * `stein_coprime_sieve_iff_prime`:
        `2 ≤ M → (Nat.Prime M ↔ ∀ q ∈ Finset.Icc 2 (Nat.sqrt M), Nat.Coprime M q)`.
  - Part II (Kernel-Verified Worked Dipolar Lattice Table for `N = 2..23`):
      * `DipolarTableEntry`, `IsValidDipolarRow`, `workedTable2to23`,
        `workedTable2to23_all_valid`, `workedTable_twin_and_goldbach_certified`:
        Certifies all 22 rows (`N = 2..23`) of the worked table—consecutive
        bounding primes `p_prev ≤ N ≤ p_next`, composite interior, exact `(k_r, k_i)`,
        `D(N) = k_i - k_r`, `E(N) = k_r² + k_i²`, Twin Prime ground states `E = 2`
        at `N ∈ {4, 6, 12, 18}`, and composite Goldbach midpoints `D = 0` at
        `N ∈ {4, 6, 9, 12, 15, 18, 21}`.
  - Part III (Exact Total Basin Euclidean Energy Law):
      * `two_mul_euclideanEnergy_eq_defect_sq_add_gap_sq`:
        `2 * (k_r² + k_i²) = (k_i - k_r)² + (k_r + k_i)²`.
      * `dipolar_total_basin_energy_identity`:
        `3 * ∑_{k=1}^{g-1} (k² + (g - k)²) = g * (g - 1) * (2g - 1)`.
      * `dipolar_total_basin_energy_eq_two_iff_twin_prime`:
        Across `g ≥ 2`, total composite basin energy equals `2` iff `g = 2`.
  - Part IV (Pentagonal `2 cos(π/5) = φ`, Regulator `ln φ > 0`, & Primitive `χ₅`):
      * `two_mul_cos_pi_div_five_eq_goldenRatio`: `2 * Real.cos (π / 5) = φ`.
      * `goldenRatio_unit_and_regulator_pos`: `φ * (φ - 1) = 1 ∧ 0 < Real.log φ`.
      * `chi5`, `chi5_values`, `chi5_ne_one_sq_even_primitive`,
        `chi5_LFunction_ne_zero_of_one_le_re`, `chi5_LFunction_one_ne_zero`,
        `grh_implies_chi5_critical_line`:
        Constructs the concrete real quadratic Legendre–Dirichlet character `χ₅`
        modulo `5` associated with `ℚ(√5)` (`ℤ[φ]`), proves `χ₅ ≠ 1`, `χ₅² = 1`,
        `χ₅.Even`, `χ₅.IsPrimitive`, `L(1, χ₅) ≠ 0`, and direct GRH binding.
  ==============================================================================
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import RiemannDipolar.GoldenRatioSpiralAndIcosianManifold5D
import RiemannDipolar.QuasiperiodicOrderZeroLyapunovAndQuadrupoleMoments

open Real Complex Filter Topology Set
open scoped BigOperators Classical
open GRHDefinitionAndFunctionalEq
open QuasiperiodicOrderZeroLyapunovAndQuadrupoleMoments

namespace SteinBinaryGCDWorkedTableAndDirichletChi5

-- ==============================================================================
-- PART I: STEIN'S BINARY GCD RECURRENCES & SQUARE-ROOT COPRIMALITY SIEVE
-- ==============================================================================

/-- THEOREM I.1a (STEIN EVEN–EVEN BIT-SHIFT RECURRENCE):
    `gcd(2a, 2b) = 2 * gcd(a, b)` for all `a, b : ℕ`. -/
theorem stein_gcd_even_even (a b : ℕ) :
    Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b :=
  Nat.gcd_mul_left 2 a b

/-- THEOREM I.1b (STEIN EVEN–ODD BIT-SHIFT RECURRENCE):
    Since `2` and `2b + 1` are coprime, `gcd(2a, 2b + 1) = gcd(a, 2b + 1)`. -/
theorem stein_gcd_even_odd (a b : ℕ) :
    Nat.gcd (2 * a) (2 * b + 1) = Nat.gcd a (2 * b + 1) := by
  have hcop : Nat.Coprime 2 (2 * b + 1) :=
    Nat.coprime_two_left.mpr ⟨b, rfl⟩
  exact hcop.gcd_mul_left_cancel a

/-- THEOREM I.1c (STEIN ODD–EVEN BIT-SHIFT RECURRENCE):
    Symmetrically, `gcd(2a + 1, 2b) = gcd(2a + 1, b)`. -/
theorem stein_gcd_odd_even (a b : ℕ) :
    Nat.gcd (2 * a + 1) (2 * b) = Nat.gcd (2 * a + 1) b := by
  rw [Nat.gcd_comm, stein_gcd_even_odd b a, Nat.gcd_comm]

/-- THEOREM I.1d (STEIN ODD–ODD SUBTRACTION & SHIFT RECURRENCE):
    For `a ≤ b`, subtracting two odd integers `(2b + 1) - (2a + 1) = 2(b - a)` and
    shifting out the factor of `2` preserves the GCD identically:
      `gcd(2a + 1, 2b + 1) = gcd(b - a, 2a + 1)`. -/
theorem stein_gcd_odd_odd_le {a b : ℕ} (hab : a ≤ b) :
    Nat.gcd (2 * a + 1) (2 * b + 1) = Nat.gcd (b - a) (2 * a + 1) := by
  have hsplit : 2 * b + 1 = 2 * (b - a) + (2 * a + 1) := by omega
  rw [hsplit, Nat.gcd_add_self_right, Nat.gcd_comm, stein_gcd_even_odd (b - a) a]

/-- THEOREM I.2 (EXACT SQUARE-ROOT COPRIMALITY SIEVE):
    For every integer `M ≥ 2`, `M` is prime (`Nat.Prime M`) if and only if
    `gcd(M, q) = 1` (`Nat.Coprime M q`) for every integer `2 ≤ q ≤ ⌊√M⌋`. -/
theorem stein_coprime_sieve_iff_prime {M : ℕ} (hM : 2 ≤ M) :
    Nat.Prime M ↔ ∀ q ∈ Finset.Icc 2 (Nat.sqrt M), Nat.Coprime M q := by
  constructor
  · intro hP q hq
    rw [Finset.mem_Icc] at hq
    have hq_sq : q * q ≤ M := Nat.le_sqrt.mp hq.2
    have hq_lt : q < M := by nlinarith
    exact Nat.coprime_of_lt_prime (by omega) hq_lt hP
  · intro hcop
    by_contra hnotP
    have hM1 : M ≠ 1 := by omega
    have hp_prime : Nat.Prime M.minFac := Nat.minFac_prime hM1
    have hp_ge2 : 2 ≤ M.minFac := hp_prime.two_le
    have hp_dvd : M.minFac ∣ M := Nat.minFac_dvd M
    have hp_le_sqrt : M.minFac ≤ Nat.sqrt M := by
      rw [Nat.le_sqrt]
      simpa [sq] using Nat.minFac_sq_le_self (by omega) hnotP
    have hmem : M.minFac ∈ Finset.Icc 2 (Nat.sqrt M) :=
      Finset.mem_Icc.mpr ⟨hp_ge2, hp_le_sqrt⟩
    have h1 : Nat.gcd M M.minFac = 1 := hcop M.minFac hmem
    have h2 : Nat.gcd M M.minFac = M.minFac := Nat.gcd_eq_right hp_dvd
    omega

-- ==============================================================================
-- PART II: KERNEL-VERIFIED WORKED DIPOLAR LATTICE TABLE (`N = 2..23`)
-- ==============================================================================

/-- Row specification of the Past–Future Dipolar Prime Lattice Table. -/
structure DipolarTableEntry where
  N : ℕ
  p_prev : ℕ
  p_next : ℕ
  kr : ℕ
  ki : ℕ
  D : ℤ
  E : ℕ
  deriving DecidableEq, Repr

/-- Exact mathematical validity predicate for a row `(N, p_prev, p_next, k_r, k_i, D, E)`:
    `p_prev` and `p_next` are consecutive primes bounding `N`, with exact past/future
    distances `k_r, k_i`, dipolar defect `D = k_i - k_r`, and Euclidean energy `E = k_r² + k_i²`. -/
def IsValidDipolarRow (r : DipolarTableEntry) : Prop :=
  Nat.Prime r.p_prev ∧
  Nat.Prime r.p_next ∧
  r.p_prev ≤ r.N ∧
  r.N ≤ r.p_next ∧
  (∀ m ∈ Finset.Ioo r.p_prev r.p_next, ¬Nat.Prime m) ∧
  r.kr = r.N - r.p_prev ∧
  r.ki = r.p_next - r.N ∧
  r.D = (r.ki : ℤ) - (r.kr : ℤ) ∧
  r.E = r.kr ^ 2 + r.ki ^ 2

instance : DecidablePred IsValidDipolarRow := fun r => by
  unfold IsValidDipolarRow
  infer_instance

/-- Complete 22-row Worked Table (`N = 2..23`) appearing in §2 of the papers and `README.md`. -/
def workedTable2to23 : List DipolarTableEntry :=
  [ ⟨2,  2,  2,  0, 0,  0, 0⟩
  , ⟨3,  3,  3,  0, 0,  0, 0⟩
  , ⟨4,  3,  5,  1, 1,  0, 2⟩
  , ⟨5,  5,  5,  0, 0,  0, 0⟩
  , ⟨6,  5,  7,  1, 1,  0, 2⟩
  , ⟨7,  7,  7,  0, 0,  0, 0⟩
  , ⟨8,  7,  11, 1, 3,  2, 10⟩
  , ⟨9,  7,  11, 2, 2,  0, 8⟩
  , ⟨10, 7,  11, 3, 1, -2, 10⟩
  , ⟨11, 11, 11, 0, 0,  0, 0⟩
  , ⟨12, 11, 13, 1, 1,  0, 2⟩
  , ⟨13, 13, 13, 0, 0,  0, 0⟩
  , ⟨14, 13, 17, 1, 3,  2, 10⟩
  , ⟨15, 13, 17, 2, 2,  0, 8⟩
  , ⟨16, 13, 17, 3, 1, -2, 10⟩
  , ⟨17, 17, 17, 0, 0,  0, 0⟩
  , ⟨18, 17, 19, 1, 1,  0, 2⟩
  , ⟨19, 19, 19, 0, 0,  0, 0⟩
  , ⟨20, 19, 23, 1, 3,  2, 10⟩
  , ⟨21, 19, 23, 2, 2,  0, 8⟩
  , ⟨22, 19, 23, 3, 1, -2, 10⟩
  , ⟨23, 23, 23, 0, 0,  0, 0⟩
  ]

/-- THEOREM II.1 (KERNEL CERTIFICATION OF ALL 22 WORKED-TABLE ROWS `N = 2..23`):
    Every row in `workedTable2to23` covers `N = 2..23` in exact order and satisfies
    `IsValidDipolarRow`, with total dipolar defect across `N = 2..23` vanishing (`∑ D = 0`). -/
theorem workedTable2to23_all_valid :
    workedTable2to23.map DipolarTableEntry.N = List.range' 2 22 ∧
    (∀ r ∈ workedTable2to23, IsValidDipolarRow r) ∧
    (workedTable2to23.map DipolarTableEntry.D).sum = 0 := by
  decide

/-- THEOREM II.2 (EXACT TWIN-PRIME & GOLDBACH CLASSIFICATION ON `N = 2..23`):
    Among all rows in `N = 2..23`:
    - Twin Prime ground states (`E = 2`) occur at `N = [4, 6, 12, 18]`;
    - Composite Goldbach centers (`E > 0 ∧ D = 0`) occur at `N = [4, 6, 9, 12, 15, 18, 21]`. -/
theorem workedTable_twin_and_goldbach_certified :
    (workedTable2to23.filter (fun r => r.E == 2)).map DipolarTableEntry.N =
      [4, 6, 12, 18] ∧
    (workedTable2to23.filter (fun r => decide (0 < r.E ∧ r.D = 0))).map DipolarTableEntry.N =
      [4, 6, 9, 12, 15, 18, 21] := by
  decide

-- ==============================================================================
-- PART III: EXACT TOTAL BASIN EUCLIDEAN ENERGY LAW `3 * ∑ E(N) = g(g - 1)(2g - 1)`
-- ==============================================================================

/-- Pointwise parallelogram decomposition linking Euclidean energy `E = k_r² + k_i²`,
    dipolar defect `D = k_i - k_r`, and inter-prime gap `g = k_r + k_i`:
      `2 * (k_r² + k_i²) = (k_i - k_r)² + (k_r + k_i)²`. -/
theorem two_mul_euclideanEnergy_eq_defect_sq_add_gap_sq (kr ki : ℤ) :
    2 * (kr ^ 2 + ki ^ 2) = (ki - kr) ^ 2 + (kr + ki) ^ 2 := by
  ring

/-- THEOREM III.1 (EXACT CLOSED-FORM TOTAL BASIN EUCLIDEAN ENERGY):
    Across every inter-prime gap `g = p_{m+1} - p_m`, summing the Euclidean energy
    `E(p_m + k) = k² + (g - k)²` over all `g - 1` interior composites `1 ≤ k < g`
    obeys the exact closed-form cubic law:
      `3 * ∑_{k=1}^{g-1} (k² + (g - k)²) = g * (g - 1) * (2g - 1)`. -/
theorem dipolar_total_basin_energy_identity (g : ℕ) :
    3 * (∑ k ∈ Finset.Ico 1 g, ((k : ℤ) ^ 2 + ((g : ℤ) - (k : ℤ)) ^ 2)) =
      (g : ℤ) * ((g : ℤ) - 1) * (2 * (g : ℤ) - 1) := by
  rcases g with _ | n
  · simp
  · have hquad := dipolar_gap_quadrupole_identity (n + 1)
    have hpar : 2 * (∑ k ∈ Finset.Ico 1 (n + 1),
          ((k : ℤ) ^ 2 + (((n + 1 : ℕ) : ℤ) - (k : ℤ)) ^ 2)) =
        (∑ k ∈ Finset.Ico 1 (n + 1), (((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ)) ^ 2) +
          (∑ _k ∈ Finset.Ico 1 (n + 1), (((n + 1 : ℕ) : ℤ)) ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hconst : ∑ _k ∈ Finset.Ico 1 (n + 1), (((n + 1 : ℕ) : ℤ)) ^ 2 =
        (n : ℤ) * (((n + 1 : ℕ) : ℤ)) ^ 2 := by
      simp
    have h6 : 6 * (∑ k ∈ Finset.Ico 1 (n + 1),
          ((k : ℤ) ^ 2 + (((n + 1 : ℕ) : ℤ) - (k : ℤ)) ^ 2)) =
        2 * (((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - 1) *
          (2 * ((n + 1 : ℕ) : ℤ) - 1)) := by
      calc 6 * (∑ k ∈ Finset.Ico 1 (n + 1),
              ((k : ℤ) ^ 2 + (((n + 1 : ℕ) : ℤ) - (k : ℤ)) ^ 2))
        _ = 3 * (2 * (∑ k ∈ Finset.Ico 1 (n + 1),
              ((k : ℤ) ^ 2 + (((n + 1 : ℕ) : ℤ) - (k : ℤ)) ^ 2))) := by ring
        _ = 3 * (∑ k ∈ Finset.Ico 1 (n + 1), (((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ)) ^ 2) +
              3 * ((n : ℤ) * (((n + 1 : ℕ) : ℤ)) ^ 2) := by
            rw [hpar, hconst]; ring
        _ = (((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - 1) * (((n + 1 : ℕ) : ℤ) - 2)) +
              3 * ((n : ℤ) * (((n + 1 : ℕ) : ℤ)) ^ 2) := by rw [hquad]
        _ = 2 * (((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - 1) *
              (2 * ((n + 1 : ℕ) : ℤ) - 1)) := by push_cast; ring
    linarith

/-- THEOREM III.2 (MINIMAL TOTAL BASIN ENERGY `∑ E = 2` CHARACTERIZES TWIN PRIMES):
    Across all composite inter-prime gaps `g ≥ 2`, the total Euclidean energy summed
    over the entire composite basin equals `2` IF AND ONLY IF `g = 2` (Twin Primes). -/
theorem dipolar_total_basin_energy_eq_two_iff_twin_prime {g : ℕ} (hg : 2 ≤ g) :
    (∑ k ∈ Finset.Ico 1 g, ((k : ℤ) ^ 2 + ((g : ℤ) - (k : ℤ)) ^ 2)) = 2 ↔ g = 2 := by
  have htot := dipolar_total_basin_energy_identity g
  constructor
  · intro h2
    rw [h2] at htot
    by_contra hne
    have hg3 : (3 : ℤ) ≤ (g : ℤ) := by omega
    have hprod1 : (6 : ℤ) ≤ (g : ℤ) * ((g : ℤ) - 1) := by nlinarith
    have hprod2 : (5 : ℤ) ≤ 2 * (g : ℤ) - 1 := by omega
    nlinarith
  · rintro rfl
    decide

-- ==============================================================================
-- PART IV: PENTAGONAL `2 cos(π/5) = φ`, REGULATOR `ln φ > 0`, & PRIMITIVE `χ₅`
-- ==============================================================================

/-- THEOREM IV.1 (EXACT ICOSAHEDRAL PENTAGONAL IDENTITY `2 * cos(π / 5) = φ`):
    Certifies Remark 5.2(iii): `Real.goldenRatio` equals `2 * Real.cos (π / 5)`. -/
theorem two_mul_cos_pi_div_five_eq_goldenRatio :
    2 * Real.cos (Real.pi / 5) = Real.goldenRatio := by
  set θ : ℝ := Real.pi / 5
  have hpi : 0 < Real.pi := Real.pi_pos
  have hθ_pos : 0 < θ := by positivity
  have hθ_lt_half : θ < Real.pi / 2 := by
    show Real.pi / 5 < Real.pi / 2
    linarith
  have hθ_lt_pi : θ < Real.pi := by
    show Real.pi / 5 < Real.pi
    linarith
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt_half⟩
  have h2_eq_3 : Real.sin (2 * θ) = Real.sin (3 * θ) := by
    have hsupp : 3 * θ = Real.pi - 2 * θ := by
      show 3 * (Real.pi / 5) = Real.pi - 2 * (Real.pi / 5)
      ring
    rw [hsupp, Real.sin_pi_sub]
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hsin3 : Real.sin (3 * θ) = Real.sin θ * (4 * Real.cos θ ^ 2 - 1) := by
    have hsplit : 3 * θ = 2 * θ + θ := by ring
    rw [hsplit, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
    ring
  rw [hsin2, hsin3] at h2_eq_3
  have hquad_cos : 4 * Real.cos θ ^ 2 - 2 * Real.cos θ - 1 = 0 := by
    have hmul : Real.sin θ * (4 * Real.cos θ ^ 2 - 2 * Real.cos θ - 1) = 0 := by
      linarith
    rcases mul_eq_zero.mp hmul with h0 | hq
    · linarith
    · exact hq
  set x : ℝ := 2 * Real.cos θ
  have hx_quad : x ^ 2 - x - 1 = 0 := by
    show (2 * Real.cos θ) ^ 2 - 2 * Real.cos θ - 1 = 0
    linarith
  have hφ_quad : Real.goldenRatio ^ 2 - Real.goldenRatio - 1 = 0 := by
    linarith [Real.goldenRatio_sq]
  have hfac : (x - Real.goldenRatio) * (x + Real.goldenRatio - 1) = 0 := by
    linarith
  have hφ_gt_one : 1 < Real.goldenRatio := one_lt_goldenRatio
  have hx_pos : 0 < x := by positivity
  rcases mul_eq_zero.mp hfac with h_eq | h_sum
  · linarith
  · exfalso; linarith

/-- THEOREM IV.2 (FUNDAMENTAL UNIT NORM `-1` & STRICTLY POSITIVE REGULATOR `ln φ > 0`):
    Certifies Remark 5.2(iv): `φ` satisfies `φ * (φ - 1) = 1` (`N_{ℚ(√5)/ℚ}(φ) = -1`)
    and has strictly positive Dirichlet regulator `Reg(ℚ(√5)) = ln φ > 0`. -/
theorem goldenRatio_unit_and_regulator_pos :
    Real.goldenRatio * (Real.goldenRatio - 1) = 1 ∧
    0 < Real.log Real.goldenRatio := by
  refine ⟨?_, Real.log_pos one_lt_goldenRatio⟩
  linarith [Real.goldenRatio_sq]

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Concrete real quadratic Legendre–Dirichlet character `χ₅ : DirichletCharacter ℂ 5`
    associated with the golden quadratic field `ℚ(√5)` (`ℤ[φ]`, discriminant `5`). -/
noncomputable def chi5 : DirichletCharacter ℂ 5 :=
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

/-- Helper evaluating `quadraticChar (ZMod 5)` on all five residue classes mod `5`. -/
theorem quadraticChar_zmod5_values :
    quadraticChar (ZMod 5) 0 = 0 ∧
    quadraticChar (ZMod 5) 1 = 1 ∧
    quadraticChar (ZMod 5) 2 = -1 ∧
    quadraticChar (ZMod 5) 3 = -1 ∧
    quadraticChar (ZMod 5) 4 = 1 := by
  decide

/-- THEOREM IV.3 (EXACT RESIDUE VALUES OF `χ₅` ENCODING PRIME SPLITTING IN `ℤ[φ]`):
    `χ₅(0) = 0` (ramified at `5`), `χ₅(±1) = +1` (split primes `p ≡ ±1 mod 5`),
    and `χ₅(±2) = -1` (inert primes `p ≡ ±2 mod 5`). -/
theorem chi5_values :
    chi5 0 = 0 ∧
    chi5 1 = 1 ∧
    chi5 2 = -1 ∧
    chi5 3 = -1 ∧
    chi5 4 = 1 := by
  rcases quadraticChar_zmod5_values with ⟨h0, h1, h2, h3, h4⟩
  dsimp [chi5]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h4]

/-- THEOREM IV.4 (`χ₅` IS NON-TRIVIAL, REAL QUADRATIC, EVEN, AND PRIMITIVE OF CONDUCTOR `5`):
    Proves `χ₅ ≠ 1`, `χ₅² = 1`, `χ₅(-1) = 1` (`Even`), and `χ₅.IsPrimitive`. -/
theorem chi5_ne_one_sq_even_primitive :
    chi5 ≠ 1 ∧ chi5 ^ 2 = 1 ∧ chi5.Even ∧ chi5.IsPrimitive := by
  rcases chi5_values with ⟨_, h1, h2, _, h4⟩
  have hne1 : chi5 ≠ 1 := by
    intro heq
    have hu2 : IsUnit (2 : ZMod 5) := by decide
    have h2_one : chi5 2 = 1 := by
      rw [heq]
      exact MulChar.one_apply hu2
    rw [h2] at h2_one
    norm_num at h2_one
  have hsq : chi5 ^ 2 = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have hq : quadraticChar (ZMod 5) (u : ZMod 5) ^ 2 = 1 :=
      quadraticChar_sq_one u.ne_zero
    simp only [chi5, MulChar.ringHomComp_apply, Int.coe_castRingHom]
    exact_mod_cast hq
  have heven : DirichletCharacter.Even chi5 := by
    show chi5 (-1) = 1
    have hneg1 : (-1 : ZMod 5) = (4 : ZMod 5) := by decide
    rw [hneg1]
    exact h4
  have hprim : chi5.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    have hdvd : chi5.conductor ∣ 5 := DirichletCharacter.conductor_dvd_level chi5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with hc1 | hc5
    · exfalso
      exact hne1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc1)
    · exact hc5
  exact ⟨hne1, hsq, heven, hprim⟩

/-- THEOREM IV.5 (NON-VANISHING OF `L(s, χ₅)` ON `Re(s) ≥ 1` & AT `s = 1`):
    In particular `L(1, χ₅) ≠ 0`, certifying the analytic non-vanishing side of
    Dirichlet's Class Number Formula for `ℚ(√5)` (`L(1, χ₅) = 2 ln φ / √5 ≠ 0`). -/
theorem chi5_LFunction_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction chi5 s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re chi5
    (Or.inl chi5_ne_one_sq_even_primitive.1) hs

/-- Corollary IV.5a: `L(1, χ₅) ≠ 0` directly on Mathlib4's `DirichletCharacter.LFunction`. -/
theorem chi5_LFunction_one_ne_zero :
    DirichletCharacter.LFunction chi5 1 ≠ 0 :=
  chi5_LFunction_ne_zero_of_one_le_re (by simp)

/-- THEOREM IV.6 (DIRECT GRH SPECIALIZATION TO THE GOLDEN QUADRATIC L-FUNCTION `L(s, χ₅)`):
    Under `GeneralizedRiemannHypothesis`, every non-trivial zero of `L(s, χ₅)` lies
    identically on the critical line `Re(s) = 1/2` (and hence on the Clifford equator). -/
theorem grh_implies_chi5_critical_line (hGRH : GeneralizedRiemannHypothesis) :
    GRHForCharacter 5 chi5 :=
  hGRH 5 chi5 chi5_ne_one_sq_even_primitive.2.2.2

end SteinBinaryGCDWorkedTableAndDirichletChi5
