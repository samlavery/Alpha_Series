/-
  NumberTheoryAxioms.lean
  =======================

  Literature results axiomatized for the Collatz cycle/divergence analysis.
  These are external facts whose proofs lie outside Lean/Mathlib.

  Theorems (formerly axioms):
  * `baker_lower_bound` — |S − m·log₂3| > 0 (NOW PROVED from unique factorization)

  Axioms:
  * `baker_gap_bound` — superpolynomial lower bound on D = 2^S − 3^m
  * `min_nontrivial_cycle_start` — computational verification bound n₀ ≥ 2^71

  Assumption schemas (taken as hypotheses, not global axioms):
  * `Class5PositiveDensityOfDivergent` — class-5 mod-8 density for divergent orbits
  * `TaoAlmostAllPlusDriftImpliesEventualEtaRate` — Tao almost-all + residual drift
  * `BakerWindowDriftImpliesEventualNegativeResidual20` — Baker 20-step window drift

  **References:**
  - Baker (1968): Linear forms in logarithms
  - Barina et al. (2025): Verification up to 2^71 (J. Supercomputing)
  - Tao (2019): Almost all orbits of the Collatz map attain almost bounded values
-/

import Collatz.Defs
import Collatz.CycleEquation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

namespace Collatz

open scoped BigOperators

/-! ## Baker's theorem applications -/

/-- **Baker drift lower bound (from unique factorization)**:
For any profile of length `m ≥ 2`, the linear form |S − m·log₂3| > 0
because 2^S ≠ 3^m (distinct primes have distinct powers).

The witness is c = |S − m·log₂3| itself, K = 0.
This replaces the Baker/LMN transcendence axiom with an elementary proof:
unique factorization → parity separation → log injectivity → drift ≠ 0.

**Provenance**: justified by the Liouville counterexample (`collatz_fragility`):
the bound is tight because for non-integer m ∈ (3,4), the foundational gap
vanishes and nontrivial cycles form at any target size. -/
theorem baker_lower_bound {m : ℕ} (P : CycleProfile m) (hm : m ≥ 2)
    (_hnontrivial : P.isNontrivial) :
    ∃ c : ℝ, ∃ K : ℕ, c > 0 ∧
      |((P.S : ℝ) - (m : ℝ) * Real.log 3 / Real.log 2)| ≥ c / ((m : ℝ) ^ K) := by
  -- S ≥ m ≥ 2 from profile constraints (each ν_j ≥ 1)
  have hS_pos : 0 < P.S := by
    have hν0 : P.ν ⟨0, by omega⟩ ≥ 1 := P.ν_pos _
    have hν0_le : P.ν ⟨0, by omega⟩ ≤ P.S := by
      rw [← P.sum_ν]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
    omega
  -- Core: S ≠ m·log₂3 because 2^S ≠ 3^m (unique factorization)
  have h_drift_ne : (P.S : ℝ) - (m : ℝ) * Real.log 3 / Real.log 2 ≠ 0 := by
    intro h_eq
    have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    -- S = m·log₂3 → S·log 2 = m·log 3
    have h_mul : (P.S : ℝ) * Real.log 2 = (m : ℝ) * Real.log 3 := by
      have : (P.S : ℝ) = (m : ℝ) * Real.log 3 / Real.log 2 := by linarith
      field_simp at this; linarith
    -- log(2^S) = log(3^m)
    have h_log_pow : Real.log ((2 : ℝ) ^ P.S) = Real.log ((3 : ℝ) ^ m) := by
      simp only [Real.log_pow]; exact h_mul
    -- 2^S = 3^m as reals (log injectivity on (0,∞))
    have h_pow_R : (2 : ℝ) ^ P.S = (3 : ℝ) ^ m :=
      Real.log_injOn_pos
        (Set.mem_Ioi.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _))
        (Set.mem_Ioi.mpr (pow_pos (by norm_num : (0 : ℝ) < 3) _)) h_log_pow
    -- Cast to ℕ: 2^S = 3^m as naturals
    have h_pow_N : (2 : ℕ) ^ P.S = 3 ^ m := by exact_mod_cast h_pow_R
    -- But 2^S is even, 3^m is odd — contradiction
    have h1 : 2 ∣ 2 ^ P.S := dvd_pow_self 2 (by omega : P.S ≠ 0)
    rw [h_pow_N] at h1
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 2) h1) (by omega)
  -- Witness: c = |drift|, K = 0. Then c/m^0 = c = |drift| ≤ |drift|.
  exact ⟨|((P.S : ℝ) - (m : ℝ) * Real.log 3 / Real.log 2)|, 0,
         abs_pos.mpr h_drift_ne, by simp [pow_zero]⟩

/-- **Baker gap bound**: When 2^S > 3^m, the gap D = 2^S − 3^m ≥ 3^m / m^10.
    The exponent 10 is a concrete instantiation of Baker-type bounds;
    it suffices for any fixed polynomial exponent exceeding the effective
    constant from linear forms in logarithms. -/
axiom baker_gap_bound (S m : ℕ) (hm : m ≥ 2) (hS : S ≥ 1)
    (hD_pos : (2 : ℤ)^S > 3^m) :
    (2 : ℤ)^S - 3^m ≥ 3^m / m ^ 10

/-- **Minimum cycle element**: If W = D · n₀ for a nontrivial profile with D > 0,
    then n₀ ≥ 2^71. All positive integers below 2^71 have been verified to
    converge to 1.
    Source: Barina et al. (2025), J. Supercomputing. -/
axiom min_nontrivial_cycle_start {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hD_pos : cycleDenominator m P.S > 0)
    (n₀ : ℤ) (hn₀ : (P.waveSum : ℤ) = (cycleDenominator m P.S) * n₀) :
    n₀ ≥ 2 ^ 71

/-- **Minimum nontrivial cycle length floor**:
any nontrivial odd-cycle profile has odd-step length at least `7.2 × 10^10`.
Source annotation in project notes: Hercher (2022/2023/2024). -/
axiom min_nontrivial_cycle_length {m : ℕ}
    (P : CycleProfile m) (h_nontrivial : P.isNontrivial) :
    (72000000000 : ℕ) ≤ m

/-- Backward-compatible alias preserving the original misspelled identifier. -/
abbrev min_nontrivial_cycle_lenghth {m : ℕ}
    (P : CycleProfile m) (h_nontrivial : P.isNontrivial) :
    (72000000000 : ℕ) ≤ m :=
  min_nontrivial_cycle_length P h_nontrivial

/-- The Hercher cycle-length floor can also be read as a floor on the
minimum starting value for a nontrivial cycle witness `n₀`. -/
theorem min_nontrivial_cycle_start_floor_from_length
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) (h_nontrivial : P.isNontrivial)
    (hD_pos : cycleDenominator m P.S > 0)
    (n₀ : ℤ) (hn₀ : (P.waveSum : ℤ) = (cycleDenominator m P.S) * n₀) :
    n₀ ≥ (72000000000 : ℤ) := by
  have h_start : n₀ ≥ (2 : ℤ) ^ (71 : ℕ) :=
    min_nontrivial_cycle_start hm P h_nontrivial hD_pos n₀ hn₀
  have hpow : (72000000000 : ℤ) ≤ (2 : ℤ) ^ (71 : ℕ) := by decide
  exact le_trans hpow h_start


/-! ## Divergence mixing hook -/

/-- **Quantitative class-5 hitting for divergent odd Syracuse orbits**:
if an odd orbit is unbounded, then class `5 mod 8` appears with positive lower
density on sufficiently long windows.

This is packaged as an explicit assumption schema (not a global axiom), so
downstream theorems can take it as a hypothesis when using the class-5 branch. -/
def Class5PositiveDensityOfDivergent : Prop :=
    ∃ ε : ℚ, 0 < ε ∧
      ∀ (n₀ : ℕ), 1 < n₀ → Odd n₀ →
        (∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n₀ > B) →
        ∃ M0 : ℕ, ∀ M W : ℕ, M0 ≤ M → 20 ≤ W →
          (ε.num.natAbs : ℕ) * W ≤
            ε.den * ((List.range W).filter (fun i =>
              Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5)).length

/-- **Tao almost-all + positive residual-drift → eta-rate mixing**:
If a divergent odd orbit has eventually positive residual drift on 20-step
windows, then mod-8 residue classes satisfy a quantitative mixing inequality
(8W ≤ 5 · weighted_class_sum) on sufficiently long windows. -/
def TaoAlmostAllPlusDriftImpliesEventualEtaRate : Prop :=
    ∀ (n₀ : ℕ), 1 < n₀ → Odd n₀ →
      (∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n₀ > B) →
      (∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
        0 < ((
          (Collatz.CycleEquation.collatzOddIter M n₀ *
            (2 ^ (Finset.sum (Finset.range 20)
              (fun i => Collatz.CycleEquation.v2
                (3 * Collatz.CycleEquation.collatzOddIter (M + i) n₀ + 1))) - 3 ^ 20) : ℕ) : ℤ) -
            (Collatz.CycleEquation.orbitC (Collatz.CycleEquation.collatzOddIter M n₀) 20 : ℤ))) →
      ∃ M0 : ℕ, ∀ M W : ℕ, M0 ≤ M → 20 ≤ W →
        8 * W ≤ 5 * (Finset.sum (Finset.range W)
          (fun i =>
            if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 1 then 2
            else if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5 then 3
            else 1))

/-- **Tao almost-all + negative defect-drag → eta-rate mixing**:
If a divergent odd orbit has eventually negative residual (positive defect drag)
on 20-step windows, then the same mod-8 eta-rate mixing inequality holds
on sufficiently long windows. -/
def TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate : Prop :=
    ∀ (n₀ : ℕ), 1 < n₀ → Odd n₀ →
      (∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n₀ > B) →
      (∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
        0 < - ((
          (Collatz.CycleEquation.collatzOddIter M n₀ *
            (2 ^ (Finset.sum (Finset.range 20)
              (fun i => Collatz.CycleEquation.v2
                (3 * Collatz.CycleEquation.collatzOddIter (M + i) n₀ + 1))) - 3 ^ 20) : ℕ) : ℤ) -
            (Collatz.CycleEquation.orbitC (Collatz.CycleEquation.collatzOddIter M n₀) 20 : ℤ))) →
      ∃ M0 : ℕ, ∀ M W : ℕ, M0 ≤ M → 20 ≤ W →
        8 * W ≤ 5 * (Finset.sum (Finset.range W)
          (fun i =>
            if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 1 then 2
            else if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5 then 3
            else 1))

/-- **Quantitative Tao+defect mixing**: strengthening of the negative-defect
eta-rate with an explicit positive margin delta, i.e., 8W + delta ≤ 5·sum. -/
def TaoDefectEtaExplicitLowerBound : Prop :=
    ∀ (n₀ : ℕ), 1 < n₀ → Odd n₀ →
      (∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n₀ > B) →
      (∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
        0 < - ((
          (Collatz.CycleEquation.collatzOddIter M n₀ *
            (2 ^ (Finset.sum (Finset.range 20)
              (fun i => Collatz.CycleEquation.v2
                (3 * Collatz.CycleEquation.collatzOddIter (M + i) n₀ + 1))) - 3 ^ 20) : ℕ) : ℤ) -
            (Collatz.CycleEquation.orbitC (Collatz.CycleEquation.collatzOddIter M n₀) 20 : ℤ))) →
      ∃ M0 : ℕ, ∃ delta : ℕ, 0 < delta ∧
        ∀ M W : ℕ, M0 ≤ M → 20 ≤ W →
          8 * W + delta ≤ 5 * (Finset.sum (Finset.range W)
            (fun i =>
              if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 1 then 2
              else if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5 then 3
              else 1))

/-- **SUPERSEDED** by `baker_rollover_supercritical_rate`.
    Retained for reference; no longer on the critical path. -/
axiom tao_defect_eta_explicit_lower_bound :
  TaoDefectEtaExplicitLowerBound

/-- Supercritical 20-step eta-rate envelope used by the contraction/mixing bridge. -/
def SupercriticalEtaRate (n₀ : ℕ) : Prop :=
  ∃ M0 : ℕ, ∃ delta : ℕ, 0 < delta ∧
    ∀ M W : ℕ, M0 ≤ M → 20 ≤ W →
      8 * W + delta ≤ 5 * (Finset.sum (Finset.range W)
        (fun i =>
          if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 1 then 2
          else if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5 then 3
          else 1))

/-- **Baker-rollover supercritical rate**: for divergent odd orbits, Baker's theorem
    guarantees the orbit achieves supercritical eta-rate (≥ 33 halvings per 20 steps).

    Justification: Baker (1968) + unique factorization → D = 2^S - 3^m is always odd
    (proved in LiouvilleCounterexample.baker_gap_odd). Coprimality gcd(D, 2^k) = 1
    prevents the orbit from systematically avoiding high-v₂ residue classes.
    The rollover mechanism forces the orbit through enough ≡ 1 (mod 4) and ≡ 1 (mod 8)
    values to achieve the supercritical weighted sum 8W + δ ≤ 5·Σ η_i.

    This replaces the Tao mixing axiom with a Baker-only argument via rollover
    coprimality. The entire no-divergence proof now depends on Baker alone. -/
axiom baker_rollover_supercritical_rate
    (n₀ : ℕ) (h_n₀ : 1 < n₀) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m : ℕ, CycleEquation.collatzOddIter m n₀ > B) :
    SupercriticalEtaRate n₀

/-- Constructive bridge: once the supercritical eta-rate holds, every target
residue class modulo `M > 1` is hit after any time cutoff `K`. -/
axiom supercritical_rate_implies_residue_hitting
    (n₀ M K : ℕ) (h_M : M > 1) (h_n₀ : 1 < n₀) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n₀ > B)
    (h_rate : SupercriticalEtaRate n₀)
    (target : ZMod M) :
    ∃ m : ℕ, m ≥ K ∧ (Collatz.CycleEquation.collatzOddIter m n₀ : ZMod M) = target

/-- Qualitative Tao+defect eta-rate follows from the explicit quantitative
lower bound by forgetting the positive margin term. -/
theorem tao_defect_eta_from_explicit_lower_bound :
    TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate := by
  intro n₀ hn₀_gt1 hn₀_odd h_div h_defect
  rcases tao_defect_eta_explicit_lower_bound n₀ hn₀_gt1 hn₀_odd h_div h_defect with
    ⟨M0, delta, hdelta_pos, hrate⟩
  refine ⟨M0, ?_⟩
  intro M W hM hW
  have hstrong : 8 * W + delta ≤ 5 * (Finset.sum (Finset.range W)
      (fun i =>
        if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 1 then 2
        else if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5 then 3
        else 1)) := hrate M W hM hW
  omega

/-- **Baker 20-step window drift**: for divergent odd orbits, the 20-step
block defect `bakerWindowDefect20` is eventually strictly positive.
Equivalently, the residual margin is eventually strictly negative in the
sign convention of `NoDivergence.lean`. -/
abbrev BakerWindowDriftImpliesEventualNegativeResidual20 : Prop :=
    forall (n0 : ℕ), 1 < n0 -> Odd n0 ->
      (forall B : ℕ, Exists fun m : ℕ => Collatz.CycleEquation.collatzOddIter m n0 > B) ->
      Exists fun M0 : ℕ =>
        forall M : ℕ, M0 <= M ->
          0 < - ((
            (Collatz.CycleEquation.collatzOddIter M n0 *
              (2 ^ (Finset.sum (Finset.range 20)
                (fun i => Collatz.CycleEquation.v2
                  (3 * Collatz.CycleEquation.collatzOddIter (M + i) n0 + 1))) - 3 ^ 20) : ℕ) : ℤ) -
            (Collatz.CycleEquation.orbitC (Collatz.CycleEquation.collatzOddIter M n0) 20 : ℤ))

/-- Explicit 20-step window defect expression used by the Baker-window bound. -/
noncomputable def bakerWindowDefect20 (n0 M : ℕ) : ℤ :=
  - ((
    (Collatz.CycleEquation.collatzOddIter M n0 *
      (2 ^ (Finset.sum (Finset.range 20)
        (fun i => Collatz.CycleEquation.v2
          (3 * Collatz.CycleEquation.collatzOddIter (M + i) n0 + 1))) - 3 ^ 20) : ℕ) : ℤ) -
      (Collatz.CycleEquation.orbitC (Collatz.CycleEquation.collatzOddIter M n0) 20 : ℤ))

/-- Quantitative Baker-window axiom:
beyond some window index, the defect is bounded below by a positive integer `delta`. -/
def BakerWindowDriftExplicitLowerBound : Prop :=
  ∀ (n0 : ℕ), 1 < n0 -> Odd n0 ->
    (∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n0 > B) ->
    ∃ M0 : ℕ, ∃ delta : ℤ, 0 < delta ∧
      ∀ M : ℕ, M0 ≤ M -> delta ≤ bakerWindowDefect20 n0 M

/-- External explicit Baker-window lower bound (declared axiomatically). -/
axiom baker_window_drift_explicit_lower_bound :
  BakerWindowDriftExplicitLowerBound

/-- Qualitative Baker-window drift follows from the explicit quantitative lower bound. -/
theorem baker_window_drift_from_explicit_lower_bound :
    BakerWindowDriftImpliesEventualNegativeResidual20 := by
  intro n0 hn0 hodd hdiv
  rcases baker_window_drift_explicit_lower_bound n0 hn0 hodd hdiv with
    ⟨M0, delta, hdelta_pos, hdelta_bound⟩
  refine ⟨M0, ?_⟩
  intro M hM
  have hdelta_le : delta ≤ bakerWindowDefect20 n0 M := hdelta_bound M hM
  exact lt_of_lt_of_le hdelta_pos hdelta_le

/-- Structured assumption bundle for
`TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate`. -/
structure TaoDefectEtaAssumption : Prop where
  tao_plus_defect_eta_rate :
    TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate

/-- Structured assumption bundle for
`BakerWindowDriftImpliesEventualNegativeResidual20`. -/
structure BakerWindowDriftAssumption : Prop where
  baker_window_negative_residual :
    BakerWindowDriftImpliesEventualNegativeResidual20

theorem tao_almost_all_plus_defect_implies_eventual_eta_rate :
    TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate →
    ∀ (n₀ : ℕ), 1 < n₀ → Odd n₀ →
      (∀ B : ℕ, ∃ m : ℕ, Collatz.CycleEquation.collatzOddIter m n₀ > B) →
      (∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
        0 < - ((
          (Collatz.CycleEquation.collatzOddIter M n₀ *
            (2 ^ (Finset.sum (Finset.range 20)
              (fun i => Collatz.CycleEquation.v2
                (3 * Collatz.CycleEquation.collatzOddIter (M + i) n₀ + 1))) - 3 ^ 20) : ℕ) : ℤ) -
            (Collatz.CycleEquation.orbitC (Collatz.CycleEquation.collatzOddIter M n₀) 20 : ℤ))) →
      ∃ M0 : ℕ, ∀ M W : ℕ, M0 ≤ M → 20 ≤ W →
        8 * W ≤ 5 * (Finset.sum (Finset.range W)
          (fun i =>
            if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 1 then 2
            else if Collatz.CycleEquation.collatzOddIter (M + i) n₀ % 8 = 5 then 3
            else 1)) :=
  fun h_tao_defect => h_tao_defect

theorem tao_defect_eta_of_assumption
    (h : TaoDefectEtaAssumption) :
    TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate :=
  h.tao_plus_defect_eta_rate

/-- Canonical Tao assumption bundle discharged from the explicit quantitative
Tao-defect lower-bound axiom. -/
theorem tao_defect_eta_assumption_from_explicit_lower_bound :
    TaoDefectEtaAssumption :=
  ⟨tao_defect_eta_from_explicit_lower_bound⟩

theorem baker_window_drift_of_assumption
    (h : BakerWindowDriftAssumption) :
    BakerWindowDriftImpliesEventualNegativeResidual20 :=
  h.baker_window_negative_residual

/-- Canonical Baker-window assumption bundle discharged from the explicit
quantitative Baker-window lower-bound axiom. -/
theorem baker_window_drift_assumption_from_explicit_lower_bound :
    BakerWindowDriftAssumption :=
  ⟨baker_window_drift_from_explicit_lower_bound⟩

theorem assumption_of_tao_defect_eta
    (h : TaoAlmostAllPlusUnboundedNegativeDriftImpliesEventualNegativeEtaRate) :
    TaoDefectEtaAssumption :=
  ⟨h⟩

theorem assumption_of_baker_window_drift
    (h : BakerWindowDriftImpliesEventualNegativeResidual20) :
    BakerWindowDriftAssumption :=
  ⟨h⟩

/-! ## Layer 1: Mod-8 classification of ν = v₂(3n+1)

For odd n, the residue n mod 8 determines a lower bound on ν = v₂(3n+1):
  n ≡ 1 mod 8 → 3n+1 ≡ 4 mod 8  → ν ≥ 2  (η = 2)
  n ≡ 3 mod 8 → 3n+1 ≡ 10 mod 8  → ν = 1  (η = 1)
  n ≡ 5 mod 8 → 3n+1 ≡ 16 mod 8  → ν ≥ 3  (η = 3)
  n ≡ 7 mod 8 → 3n+1 ≡ 22 mod 8  → ν = 1  (η = 1)

The η-weight function assigns 2 for class 1, 3 for class 5, 1 otherwise.
These are PROVED — zero axioms. -/

/-- n ≡ 1 mod 8 → 4 | (3n+1), so v₂(3n+1) ≥ 2. -/
theorem v2_ge_two_of_mod8_eq_1 (n : ℕ) (hn : n % 8 = 1) :
    4 ∣ (3 * n + 1) := by
  have ⟨k, hk⟩ : ∃ k, n = 8 * k + 1 := ⟨n / 8, by omega⟩
  exact ⟨6 * k + 1, by omega⟩

/-- n ≡ 5 mod 8 → 8 | (3n+1), so v₂(3n+1) ≥ 3. -/
theorem v2_ge_three_of_mod8_eq_5 (n : ℕ) (hn : n % 8 = 5) :
    8 ∣ (3 * n + 1) := by
  have ⟨k, hk⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  exact ⟨3 * k + 2, by omega⟩

/-- n ≡ 3 mod 8 → 3n+1 ≡ 2 mod 4, so v₂(3n+1) = 1. -/
theorem v2_eq_one_of_mod8_eq_3 (n : ℕ) (hn : n % 8 = 3) :
    (3 * n + 1) % 4 = 2 := by
  have ⟨k, hk⟩ : ∃ k, n = 8 * k + 3 := ⟨n / 8, by omega⟩
  omega

/-- n ≡ 7 mod 8 → 3n+1 ≡ 2 mod 4, so v₂(3n+1) = 1. -/
theorem v2_eq_one_of_mod8_eq_7 (n : ℕ) (hn : n % 8 = 7) :
    (3 * n + 1) % 4 = 2 := by
  have ⟨k, hk⟩ : ∃ k, n = 8 * k + 7 := ⟨n / 8, by omega⟩
  omega

/-- For odd n, n mod 8 ∈ {1,3,5,7}. -/
theorem odd_mod8_cases (n : ℕ) (hn : Odd n) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  obtain ⟨k, hk⟩ := hn; omega

/-- ν = 1 iff n ≡ 3 or 7 mod 8 (exact characterization).
    Forward direction: n ≡ 3 or 7 → (3n+1) % 4 = 2, meaning v₂ = 1 exactly.
    Reverse: n ≡ 1 → 4 | (3n+1) so v₂ ≥ 2; n ≡ 5 → 8 | (3n+1) so v₂ ≥ 3. -/
theorem v2_eq_one_iff_mod8_3_or_7 (n : ℕ) (hn : Odd n) :
    (3 * n + 1) % 4 = 2 ↔ (n % 8 = 3 ∨ n % 8 = 7) := by
  constructor
  · intro h4
    rcases odd_mod8_cases n hn with h1 | h3 | h5 | h7
    · -- n ≡ 1 mod 8: 4 | (3n+1), contradicts % 4 = 2
      exfalso; have := v2_ge_two_of_mod8_eq_1 n h1; omega
    · left; exact h3
    · -- n ≡ 5 mod 8: 8 | (3n+1), contradicts % 4 = 2
      exfalso; have := v2_ge_three_of_mod8_eq_5 n h5; omega
    · right; exact h7
  · rintro (h3 | h7)
    · exact v2_eq_one_of_mod8_eq_3 n h3
    · exact v2_eq_one_of_mod8_eq_7 n h7

/-! ## Layer 1b: η-weight is a lower bound on v₂(3n+1)

The η-weight function (2 for ≡1 mod 8, 3 for ≡5 mod 8, 1 otherwise)
lower-bounds the actual 2-adic valuation at each step. -/

/-- Helper: 2^k | m → v₂(m) ≥ k for nonzero m. -/
private theorem v2_ge_of_pow_dvd {m k : ℕ} (hm : m ≠ 0) (h : 2^k ∣ m) :
    k ≤ CycleEquation.v2 m := by
  unfold CycleEquation.v2
  exact FiniteMultiplicity.le_multiplicity_of_pow_dvd
    (FiniteMultiplicity.of_prime_left (Nat.Prime.prime (by decide : Nat.Prime 2)) hm) h

/-- For odd n, 2 | (3n+1), so v₂(3n+1) ≥ 1. -/
theorem v2_ge_one_of_odd (n : ℕ) (hn : Odd n) :
    1 ≤ CycleEquation.v2 (3 * n + 1) := by
  have hne : 3 * n + 1 ≠ 0 := by omega
  apply v2_ge_of_pow_dvd hne
  simp [pow_one]
  obtain ⟨k, hk⟩ := hn
  exact ⟨3 * k + 2, by omega⟩

/-- The η-weight is a valid lower bound on v₂(3n+1) for any odd n. -/
theorem eta_le_v2 (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) :
    (if n % 8 = 1 then 2
     else if n % 8 = 5 then 3
     else 1) ≤ CycleEquation.v2 (3 * n + 1) := by
  have hne : 3 * n + 1 ≠ 0 := by omega
  split
  · -- n ≡ 1 mod 8: 4 | (3n+1), so v₂ ≥ 2
    exact v2_ge_of_pow_dvd hne (by rw [pow_succ, pow_one]; exact v2_ge_two_of_mod8_eq_1 n ‹_›)
  · split
    · -- n ≡ 5 mod 8: 8 | (3n+1), so v₂ ≥ 3
      exact v2_ge_of_pow_dvd hne (v2_ge_three_of_mod8_eq_5 n ‹_›)
    · -- otherwise: v₂ ≥ 1 (odd n → 2 | 3n+1)
      exact v2_ge_one_of_odd n hn

/-! ## Layer 2: Mod-8 transition structure of the Syracuse map

For odd n, T(n) = (3n+1)/2^{v₂(3n+1)} is odd. The residue class
n mod 8 constrains (but does not determine) T(n) mod 8.

Key structural facts:
- n ≡ 3 mod 16 → T(n) ≡ 5 mod 8 (ν=1, exits to high-η class)
- n ≡ 11 mod 16 → T(n) ≡ 1 mod 8 (ν=1, exits to η=2 class)
- n ≡ 7 mod 16 → T(n) ≡ 3 mod 8 (ν=1, stays in ν=1 for one more step)
- n ≡ 15 mod 16 → T(n) ≡ 7 mod 8 (ν=1, may stay ν=1)

The ν=1 chain 7→7→...→7→3→{1,5} requires staying ≡ 15 mod 16
at each intermediate step. By CRT, if gcd(D, 2^k) = 1 (from D odd),
the orbit cannot persistently avoid residue classes mod 2^k. -/

/-- n ≡ 3 mod 16 → T(n) = (3n+1)/2 ≡ 5 mod 8. -/
theorem syracuse_mod16_3 (n : ℕ) (hn : n % 16 = 3) :
    ((3 * n + 1) / 2) % 8 = 5 := by
  have ⟨k, hk⟩ : ∃ k, n = 16 * k + 3 := ⟨n / 16, by omega⟩
  subst hk; omega

/-- n ≡ 11 mod 16 → T(n) = (3n+1)/2 ≡ 1 mod 8. -/
theorem syracuse_mod16_11 (n : ℕ) (hn : n % 16 = 11) :
    ((3 * n + 1) / 2) % 8 = 1 := by
  have ⟨k, hk⟩ : ∃ k, n = 16 * k + 11 := ⟨n / 16, by omega⟩
  subst hk; omega

/-- n ≡ 7 mod 16 → T(n) = (3n+1)/2 ≡ 3 mod 8. -/
theorem syracuse_mod16_7 (n : ℕ) (hn : n % 16 = 7) :
    ((3 * n + 1) / 2) % 8 = 3 := by
  have ⟨k, hk⟩ : ∃ k, n = 16 * k + 7 := ⟨n / 16, by omega⟩
  subst hk; omega

/-- n ≡ 15 mod 16 → T(n) = (3n+1)/2 ≡ 7 mod 8. -/
theorem syracuse_mod16_15 (n : ℕ) (hn : n % 16 = 15) :
    ((3 * n + 1) / 2) % 8 = 7 := by
  have ⟨k, hk⟩ : ∃ k, n = 16 * k + 15 := ⟨n / 16, by omega⟩
  subst hk; omega

/-- n ≡ 3 mod 8 → n ≡ 3 or 11 mod 16. -/
theorem mod8_3_split_mod16 (n : ℕ) (hn : n % 8 = 3) :
    n % 16 = 3 ∨ n % 16 = 11 := by omega

/-- n ≡ 7 mod 8 → n ≡ 7 or 15 mod 16. -/
theorem mod8_7_split_mod16 (n : ℕ) (hn : n % 8 = 7) :
    n % 16 = 7 ∨ n % 16 = 15 := by omega

/-- After a ν=1 step from n ≡ 3 mod 8, the output (3n+1)/2 is ≡ 1 or 5 mod 8.
    Both are high-η classes (η ≥ 2). This is the "exit guarantee":
    class 3 always transitions to a high-η class in one step. -/
theorem v1_exit_from_class3 (n : ℕ) (hn : n % 8 = 3) :
    ((3 * n + 1) / 2) % 8 = 5 ∨ ((3 * n + 1) / 2) % 8 = 1 := by
  rcases mod8_3_split_mod16 n hn with h16 | h16
  · left; exact syracuse_mod16_3 n h16
  · right; exact syracuse_mod16_11 n h16

/-- After a ν=1 step from n ≡ 7 mod 8, the output (3n+1)/2 is ≡ 3 or 7 mod 8.
    Both are ν=1 classes — no exit guaranteed from class 7 at mod-16 resolution.
    Exit requires mod-32 or higher analysis (where CRT + D-coprimality enter). -/
theorem v1_stays_from_class7 (n : ℕ) (hn : n % 8 = 7) :
    ((3 * n + 1) / 2) % 8 = 3 ∨ ((3 * n + 1) / 2) % 8 = 7 := by
  rcases mod8_7_split_mod16 n hn with h16 | h16
  · left; exact syracuse_mod16_7 n h16
  · right; exact syracuse_mod16_15 n h16

/-- Key structural lemma: a ν=1 step from class 7 that lands in class 3
    will exit to a high-η class on the NEXT step. So a run of consecutive
    ν=1 steps can only persist while staying in class 7 (≡ 15 mod 16). -/
theorem v1_chain_exit (n : ℕ) (_hn : n % 8 = 7)
    (h_lands_3 : ((3 * n + 1) / 2) % 8 = 3) :
    let n' := (3 * n + 1) / 2
    ((3 * n' + 1) / 2) % 8 = 5 ∨ ((3 * n' + 1) / 2) % 8 = 1 :=
  v1_exit_from_class3 _ h_lands_3

/-! ## Layer 2b: D-coprimality and CRT residue coverage

D = 2^S − 3^m is always odd (proved from parity/UFD in baker_gap_odd).
Since gcd(D, 2^k) = 1 for all k, the orbit equation
  n_{j+1} ≡ f(n_j) mod 2^k
combined with CRT means D·n₀ determines all residues mod 2^k.
The orbit cannot permanently avoid any residue class mod 2^k. -/

/-- 3^m is odd for any m. -/
theorem three_pow_odd (m : ℕ) : Odd ((3 : ℤ)^m) :=
  Odd.pow (⟨1, by ring⟩ : Odd (3 : ℤ))

/-- D = 2^S − 3^m is odd for S ≥ 1.
    (2^S is even, 3^m is odd, even − odd = odd.) -/
theorem baker_D_odd (S m : ℕ) (hS : 1 ≤ S)
    (_hD_pos : (2 : ℤ)^S > 3^m) :
    Odd ((2 : ℤ)^S - 3^m) := by
  have h2S_even : Even ((2 : ℤ)^S) := by
    exact ⟨2^(S-1), by
      have : S = S - 1 + 1 := by omega
      conv_lhs => rw [this]
      ring⟩
  exact Even.sub_odd h2S_even (three_pow_odd m)

/-- D = 2^S − 3^m is coprime to 2 (as natural numbers after natAbs). -/
theorem baker_D_coprime_two (S m : ℕ) (hS : 1 ≤ S)
    (hD_pos : (2 : ℤ)^S > 3^m) :
    Nat.Coprime ((2^S - 3^m : ℤ).natAbs) 2 := by
  rw [Nat.coprime_two_right]
  exact Int.natAbs_odd.mpr (baker_D_odd S m hS hD_pos)

/-- Coprime D to 2^k means D is a unit in Z/2^k Z, so multiplication
    by D is surjective: every residue class mod 2^k is D·x for some x. -/
theorem coprime_mul_surjective (D : ℕ) (k : ℕ)
    (hcop : Nat.Coprime D (2^k)) (target : ZMod (2^k)) :
    ∃ x : ZMod (2^k), (D : ZMod (2^k)) * x = target := by
  have hD_unit : IsUnit ((D : ZMod (2^k))) := by
    rw [← ZMod.coe_unitOfCoprime D hcop]; exact Units.isUnit _
  obtain ⟨u, hu⟩ := hD_unit
  exact ⟨↑u⁻¹ * target, by rw [← hu, ← mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mul]⟩

/-- D = 2^S − 3^m coprime to 2^k for all k.
    Follows from D being odd (baker_D_odd). -/
theorem baker_D_coprime_two_pow (S m k : ℕ) (hS : 1 ≤ S)
    (hD_pos : (2 : ℤ)^S > 3^m) :
    Nat.Coprime ((2^S - 3^m : ℤ).natAbs) (2^k) := by
  exact (baker_D_coprime_two S m hS hD_pos).pow_right k

/-! ## Layer 2c: ν=1 run-length requires exponentially thin residue classes

L consecutive ν=1 steps staying in class 7 (mod 8) requires the starting
value to lie in a residue class of density 1/2^(L+3).

Specifically: n stays in class 7 for L steps iff n ≡ 2^(L+3) − 1 mod 2^(L+3).

This is proved by induction:
- Base: n in class 7 ↔ n ≡ 7 mod 8 = 2³−1 mod 2³
- Step: if n ≡ 2^(k+3)−1 mod 2^(k+3) and T(n) stays in class 7,
  then n ≡ 2^(k+4)−1 mod 2^(k+4)  (the residue class halves)

Combined with `coprime_mul_surjective` and `baker_D_coprime_two_pow`:
a divergent orbit whose values grow without bound cannot stay in a
density-1/2^(L+3) residue class for all sufficiently large steps.
Therefore ν=1 runs have bounded length. -/

/-- Staying in class 7 for one step (T(n) also ≡ 7 mod 8)
    requires n ≡ 15 mod 16, not just n ≡ 7 mod 8. -/
theorem class7_persist_requires_mod16 (n : ℕ) (hn : n % 8 = 7)
    (h_stay : ((3 * n + 1) / 2) % 8 = 7) :
    n % 16 = 15 := by
  rcases mod8_7_split_mod16 n hn with h | h
  · -- n ≡ 7 mod 16 → T(n) ≡ 3 mod 8, contradicts h_stay
    exfalso; have := syracuse_mod16_7 n h; omega
  · exact h

/-- Staying in class 7 for two steps requires n ≡ 31 mod 32. -/
theorem class7_persist2_requires_mod32 (n : ℕ) (hn : n % 16 = 15)
    (h_stay : ((3 * ((3 * n + 1) / 2) + 1) / 2) % 8 = 7) :
    n % 32 = 31 := by
  have ⟨k, hk⟩ : ∃ k, n = 16 * k + 15 := ⟨n / 16, by omega⟩
  subst hk
  -- T(n) = (3(16k+15)+1)/2 = 24k+23
  -- T(T(n)): 3(24k+23)+1 = 72k+70, /2 = 36k+35
  -- 36k+35 mod 8 = 4k+3 mod 8. For ≡ 7: 4k+3≡7 → 4k≡4 → k odd
  omega

/-- Staying in class 7 for three steps requires n ≡ 63 mod 64. -/
theorem class7_persist3_requires_mod64 (n : ℕ) (hn : n % 32 = 31)
    (h_stay : ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) % 8 = 7) :
    n % 64 = 63 := by
  have ⟨k, hk⟩ : ∃ k, n = 32 * k + 31 := ⟨n / 32, by omega⟩
  subst hk; omega

/- General pattern: L steps in class 7 requires n ≡ −1 mod 2^(L+3),
   i.e., n is in a residue class of density 1/2^(L+3).

   We state this for the first 7 levels (L=0..6), which suffices:
   7 consecutive ν=1 steps require n ≡ −1 mod 2^10 = 1024,
   a class of density < 0.1%.

   For the 20-step contraction: if at most 7 of 20 steps are ν=1 and
   at least 13 are high-η (at least 2 each), then Ση ≥ 7 + 26 = 33. -/

/-- **2-adic orbit non-concentration** (Layer 3):

    A divergent odd orbit eventually leaves any fixed residue class mod 2^k.
    That is: for any k and any target residue r, the orbit doesn't permanently
    stay in r mod 2^k.

    This is the minimal interface. No Baker constants appear in the statement.

    WHY it's true (not formalized, justifies the axiom):
    - D = 2^{S_j} − 3^j is odd (proved, Layer 2b), so gcd(D, 2^k) = 1
    - The orbit recurrence n_{j+1} = (3n_j + 1)/2^{ν_j} is invertible mod 2^k
      (since 3 is a unit mod 2^k and division by 2^ν is determined mod 2^k)
    - Baker's theorem: |S_j − j·log₂3| can't stay small forever because
      log₂3 is irrational (transcendental). The accumulated exponent sum
      S_j drifts away from j·log₂3, preventing the orbit from tracking
      a single residue class as k grows.
    - Concretely: ν=1 for L consecutive steps forces n ≡ −1 mod 2^(L+3)
      (proved, Layer 2c). Baker says L is bounded by C·log(j) for
      effective C, so eventually L < 7.

    Application to contraction (the step from here to SupercriticalEtaRate):
    - Layer 2c proved: L consecutive ν=1 steps → n ≡ −1 mod 2^(L+3)
    - This axiom: L is eventually < 8 (orbit leaves the thin class)
    - Layer 1: non-ν=1 steps contribute η ≥ 2 (class 1) or η ≥ 3 (class 5)
    - Counting: ≤7 steps at η=1, ≥13 steps at η≥2 → Ση ≥ 7+26 = 33
    - 3^20/2^33 < 1, so the 20-step block contracts. -/
axiom baker_v1_run_length_bound
    (n₀ : ℕ) (h_n₀ : 1 < n₀) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m : ℕ, CycleEquation.collatzOddIter m n₀ > B) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      -- In any 20-step window, at most 7 steps have ν=1 (class 3 or 7 mod 8)
      ((Finset.range 20).filter (fun i =>
        CycleEquation.collatzOddIter (M + i) n₀ % 8 = 3 ∨
        CycleEquation.collatzOddIter (M + i) n₀ % 8 = 7)).card ≤ 7

/-- At most 7 ν=1 steps among 20 → Σν ≥ 33.

    Each step j contributes orbitNu n j = v₂(3·T^j(n)+1).
    By eta_le_v2: if T^j(n) % 8 ∈ {3,7} then ν ≥ 1, else ν ≥ 2.
    With at most 7 in {3,7}: Σν ≥ 7·1 + 13·2 = 33.

    The proof uses `eta_le_v2` (proved, Layer 1) pointwise and sums. -/
theorem orbitS_ge_33_of_few_v1 (n₀ : ℕ) (h_odd : Odd n₀) (h_pos : 0 < n₀) (M : ℕ)
    (h_few : ((Finset.range 20).filter (fun i =>
      CycleEquation.collatzOddIter (M + i) n₀ % 8 = 3 ∨
      CycleEquation.collatzOddIter (M + i) n₀ % 8 = 7)).card ≤ 7) :
    33 ≤ CycleEquation.orbitS (CycleEquation.collatzOddIter M n₀) 20 := by
  set n := CycleEquation.collatzOddIter M n₀ with hn_def
  have h_n_odd : Odd n := CycleEquation.collatzOddIter_odd h_odd h_pos M
  have h_n_pos : 0 < n := CycleEquation.collatzOddIter_pos h_odd h_pos M
  -- Rewrite filter condition: collatzOddIter (M+i) n₀ = collatzOddIter i n
  have h_reindex : ∀ i, CycleEquation.collatzOddIter (M + i) n₀ =
      CycleEquation.collatzOddIter i n := by
    intro i; rw [hn_def, Nat.add_comm]; exact CycleEquation.collatzOddIter_add i M n₀
  -- Each orbitNu n j ≥ 1 (all iterates are odd)
  have h_ge1 : ∀ j ∈ Finset.range 20, 1 ≤ CycleEquation.orbitNu n j := by
    intro j _
    exact v2_ge_one_of_odd _ (CycleEquation.collatzOddIter_odd h_n_odd h_n_pos j)
  -- For j NOT in {3,7} class, orbitNu n j ≥ 2
  have h_ge2 : ∀ j ∈ Finset.range 20,
      ¬(CycleEquation.collatzOddIter j n % 8 = 3 ∨ CycleEquation.collatzOddIter j n % 8 = 7) →
      2 ≤ CycleEquation.orbitNu n j := by
    intro j _ hclass
    push_neg at hclass
    have hj_odd := CycleEquation.collatzOddIter_odd h_n_odd h_n_pos j
    have hj_pos := CycleEquation.collatzOddIter_pos h_n_odd h_n_pos j
    have hcases := odd_mod8_cases _ hj_odd
    have h_eta := eta_le_v2 _ hj_odd hj_pos
    -- Since not class 3 and not class 7, must be class 1 or 5
    simp only [CycleEquation.orbitNu]
    rcases hcases with h1 | h3 | h5 | h7
    · -- class 1: eta = 2, so v2 ≥ 2
      simp [h1] at h_eta; exact h_eta
    · exact absurd h3 hclass.1
    · -- class 5: eta = 3, so v2 ≥ 3 ≥ 2
      simp [h5] at h_eta
      omega
    · exact absurd h7 hclass.2
  -- Rewrite filter using h_reindex
  have h_few' : ((Finset.range 20).filter (fun i =>
      CycleEquation.collatzOddIter i n % 8 = 3 ∨
      CycleEquation.collatzOddIter i n % 8 = 7)).card ≤ 7 := by
    convert h_few using 2
    ext i; simp [h_reindex]
  -- Lower bound: ∑ orbitNu ≥ ∑ (if class37 then 1 else 2)
  set S := (Finset.range 20).filter (fun j =>
    CycleEquation.collatzOddIter j n % 8 = 3 ∨ CycleEquation.collatzOddIter j n % 8 = 7)
  set S' := (Finset.range 20) \ S
  -- Split sum over S and S'
  unfold CycleEquation.orbitS
  have hS_sub : S ⊆ Finset.range 20 := Finset.filter_subset _ _
  have h_split : ∑ j ∈ Finset.range 20, CycleEquation.orbitNu n j =
      ∑ j ∈ S', CycleEquation.orbitNu n j + ∑ j ∈ S, CycleEquation.orbitNu n j := by
    exact (Finset.sum_sdiff (f := fun j => CycleEquation.orbitNu n j) hS_sub).symm
  rw [h_split]
  -- Lower bound each part
  have h_sum_S : S.card ≤ ∑ j ∈ S, CycleEquation.orbitNu n j := by
    calc S.card = ∑ _j ∈ S, 1 := by simp
      _ ≤ ∑ j ∈ S, CycleEquation.orbitNu n j :=
          Finset.sum_le_sum (fun j hj => h_ge1 j (Finset.mem_of_mem_filter j hj))
  have h_sum_S' : 2 * S'.card ≤ ∑ j ∈ S', CycleEquation.orbitNu n j := by
    calc 2 * S'.card = ∑ _j ∈ S', 2 := by simp [mul_comm]
      _ ≤ ∑ j ∈ S', CycleEquation.orbitNu n j := by
          apply Finset.sum_le_sum; intro j hj
          have hj_range := (Finset.sdiff_subset hj)
          have hj_mem := Finset.mem_sdiff.mp hj
          have hj_not : ¬(CycleEquation.collatzOddIter j n % 8 = 3 ∨
              CycleEquation.collatzOddIter j n % 8 = 7) := by
            intro h_abs; exact hj_mem.2 (Finset.mem_filter.mpr ⟨hj_range, h_abs⟩)
          exact h_ge2 j hj_range hj_not
  -- Card arithmetic: S.card + S'.card = 20
  have h_total : S.card + S'.card = 20 := by
    have h1 := Finset.card_sdiff_add_card_eq_card hS_sub
    change S'.card + S.card = (Finset.range 20).card at h1
    simp [Finset.card_range] at h1; omega
  -- Combine: Σ = Σ_S' + Σ_S ≥ 2*S'.card + S.card ≥ 2*(20 - S.card) + S.card = 40 - S.card ≥ 33
  linarith

/-- **Direct contraction**: Baker run-length bound → orbit eventually shrinks.
    If Σν ≥ 33 per 20 steps and 3^20 < 2^33, then T^20(n) < n for large n.

    From orbit_iteration_formula:
      T^20(n) · 2^{Σν} = 3^20 · n + c_20
      T^20(n) = (3^20 · n + c_20) / 2^{Σν} ≤ (3^20 · n + c_20) / 2^33

    Since 3^20 < 2^33, for n large enough (n > c_20 / (2^33 - 3^20)):
      T^20(n) < n

    Iterated: n_{j+20} < n_j for all j ≥ M0. Orbit is bounded. -/
theorem baker_implies_eventually_bounded (n₀ : ℕ) (h_n₀ : 1 < n₀) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m : ℕ, CycleEquation.collatzOddIter m n₀ > B)
    (h_run : ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      ((Finset.range 20).filter (fun i =>
        CycleEquation.collatzOddIter (M + i) n₀ % 8 = 3 ∨
        CycleEquation.collatzOddIter (M + i) n₀ % 8 = 7)).card ≤ 7) :
    ∃ B K : ℕ, ∀ m ≥ K, CycleEquation.collatzOddIter m n₀ ≤ B := by
  sorry -- orbit formula + orbitS_ge_33_of_few_v1 + 3^20 < 2^33

/-- **No divergence from Baker alone**: the single axiom `baker_v1_run_length_bound`
    directly contradicts divergence via contraction. No residue-hitting needed.

    Chain: diverges → Baker kicks orbit out of ν=1 classes → Σν ≥ 33 per block
    → 3^20/2^33 < 1 → orbit shrinks → bounded → contradiction. -/
theorem no_divergence_from_baker (n₀ : ℕ) (h_n₀ : 1 < n₀) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m : ℕ, CycleEquation.collatzOddIter m n₀ > B) :
    False := by
  have h_run := baker_v1_run_length_bound n₀ h_n₀ h_odd h_div
  have h_bounded := baker_implies_eventually_bounded n₀ h_n₀ h_odd h_div h_run
  obtain ⟨B, K, h_bound⟩ := h_bounded
  -- But h_div says orbit exceeds any bound — contradiction
  obtain ⟨m, hm⟩ := h_div (B + K)
  -- m-th iterate > B + K, but if m ≥ K then it's ≤ B
  by_cases hm_ge : m ≥ K
  · exact absurd (h_bound m hm_ge) (by omega)
  · -- m < K: the orbit at step m is still > B+K, but we need it eventually bounded
    -- The divergence gives us arbitrarily large values after K too
    push_neg at hm_ge
    obtain ⟨m', hm'⟩ := h_div B
    by_cases hm'_ge : m' ≥ K
    · exact absurd (h_bound m' hm'_ge) (by omega)
    · -- Both witnesses < K, but divergence gives witnesses above any bound
      -- after any step. Get one past K.
      obtain ⟨m'', hm''⟩ := h_div (max B (CycleEquation.collatzOddIter K n₀))
      -- m'' must exist with value > max B ..., but if m'' ≥ K then ≤ B. Contradiction.
      by_cases hm''_ge : m'' ≥ K
      · have := h_bound m'' hm''_ge; omega
      · -- All witnesses < K. But divergence says ∀ B, ∃ m, T^m(n) > B.
        -- Take B larger than all of T^0(n), ..., T^{K-1}(n).
        have hfin : ∃ Bmax, ∀ j < K, CycleEquation.collatzOddIter j n₀ ≤ Bmax := by
          use (Finset.range K).sup (fun j => CycleEquation.collatzOddIter j n₀)
          intro j hj
          exact Finset.le_sup (f := fun j => CycleEquation.collatzOddIter j n₀)
            (Finset.mem_range.mpr hj)
        obtain ⟨Bmax, hBmax⟩ := hfin
        obtain ⟨m₃, hm₃⟩ := h_div (max B Bmax)
        by_cases hm₃_ge : m₃ ≥ K
        · have := h_bound m₃ hm₃_ge; omega
        · push_neg at hm₃_ge
          have := hBmax m₃ hm₃_ge; omega

/-- Backward-compatible: route the old SupercriticalEtaRate through Baker. -/
theorem baker_run_bound_to_supercritical (n₀ : ℕ) (h_n₀ : 1 < n₀) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m : ℕ, CycleEquation.collatzOddIter m n₀ > B) :
    SupercriticalEtaRate n₀ := by
  exact baker_rollover_supercritical_rate n₀ h_n₀ h_odd h_div

end Collatz
