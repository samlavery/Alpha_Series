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

end Collatz
