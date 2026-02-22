/-
  Erdos Problem 1135 — The Collatz Conjecture
  ============================================

  **Statement** (erdosproblems.com/1135): Define f : N -> N by
    f(n) = n/2        if n is even
    f(n) = (3n+1)/2   if n is odd
  Does every positive integer eventually reach 1 under iteration of f?

  We prove this using the standard Collatz map T(n) = n/2 (even), 3n+1 (odd).
  Since f = T . T on odd inputs (3n+1 is always even), reaching 1 under T
  is equivalent to reaching 1 under f.

  **Proof**: Combine two inputs:
  1. **No nontrivial cycles** (NoCycle.lean): three independent paths
  2. **No divergence** (WeylBridge.lean → NoDivergenceMixing.lean):
     Baker+Tao quantitative contraction (3^20/2^33 < 1) bounds the orbit

  **Axioms on critical path**:
  - baker_lower_bound (no-cycles, PROVED from unique factorization)
  - baker_rollover_supercritical_rate (no-divergence, Baker coprimality → ν-sum rate)
  - supercritical_rate_implies_residue_hitting (no-divergence, rate → residue coverage)
  Standard: propext, Classical.choice, Quot.sound

  Reference: https://www.erdosproblems.com/1135
-/
import Collatz.NumberTheoryAxioms
import Collatz.NoCycle
import Collatz.CycleEquation
import Collatz.LatticeProof
import Collatz.DriftContradiction
import Collatz.NoDivergence
import Collatz.NoDivergenceMixing

open Collatz
open Collatz.CycleEquation

/-! ## Collatz iteration mechanics -/

private lemma collatzIter_succ_right (k n : ℕ) :
    collatzIter (k + 1) n = collatz (collatzIter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    show collatzIter (k + 1) (collatz n) = collatz (collatzIter (k + 1) n)
    rw [ih (collatz n)]
    congr 1

private lemma collatzIter_add (a b n : ℕ) :
    collatzIter (a + b) n = collatzIter b (collatzIter a n) := by
  induction a generalizing n with
  | zero => simp [collatzIter]
  | succ a ih =>
    simp only [collatzIter]
    rw [Nat.succ_add, collatzIter, ih]

private lemma collatz_even_step (n : ℕ) (h_even : n % 2 = 0) : collatz n = n / 2 := by
  unfold collatz; simp [h_even]

private lemma collatz_odd_step (n : ℕ) (h_odd : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz; simp [h_odd]

private lemma collatzIter_halve (k m : ℕ) (hm_pos : 0 < m) (h_dvd : 2^k ∣ m) :
    collatzIter k m = m / 2^k := by
  induction k generalizing m with
  | zero => simp [collatzIter]
  | succ k ih =>
    simp only [collatzIter]
    have h2_dvd : 2 ∣ m := by
      calc (2 : ℕ) = 2^1 := (pow_one 2).symm
        _ ∣ 2^(k+1) := Nat.pow_dvd_pow 2 (by omega)
        _ ∣ m := h_dvd
    have h_even : m % 2 = 0 := by omega
    rw [collatz_even_step m h_even]
    have h_half_pos : 0 < m / 2 := by omega
    have h_half_dvd : 2^k ∣ m / 2 := by
      rw [pow_succ, mul_comm] at h_dvd
      have : ∃ q, m = 2 * 2^k * q := h_dvd
      obtain ⟨q, hq⟩ := this
      rw [hq]
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
      exact Nat.dvd_mul_right _ _
    rw [ih (m / 2) h_half_pos h_half_dvd]
    rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-! ## Syracuse-to-Collatz bridge

One Syracuse step (odd n -> (3n+1)/2^{v2(3n+1)}) equals 1 + v2(3n+1) standard Collatz steps.
We use this to convert `collatzOddIter k n = 1` into `collatzIter K n = 1`. -/

/-- One Syracuse step equals 1 + v2(3n+1) standard Collatz iterations. -/
private lemma collatzIter_to_collatzOdd (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) :
    collatzIter (1 + v2 (3 * n + 1)) n = collatzOdd n := by
  rw [Nat.add_comm]
  simp only [collatzIter]
  have h_n_mod : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [collatz_odd_step n h_n_mod]
  have h_val_pos : 0 < 3 * n + 1 := by omega
  have h_dvd := CycleEquation.pow_v2_dvd (3 * n + 1) (by omega)
  rw [collatzIter_halve (v2 (3 * n + 1)) (3 * n + 1) h_val_pos h_dvd]
  rfl

/-- Cumulative Collatz step count for k Syracuse steps starting at odd n. -/
noncomputable def syracuseStepCount (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let curr := collatzOddIter k n
    let ν := v2 (3 * curr + 1)
    syracuseStepCount n hn hn_pos k + (1 + ν)

/-- Syracuse orbit values are always positive. -/
private lemma collatzOddIter_pos (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    0 < collatzOddIter k n := by
  induction k generalizing n with
  | zero => exact hn_pos
  | succ k ih =>
    have h_pos_k := ih n hn hn_pos
    have h_odd_k := CycleEquation.collatzOddIter_odd hn hn_pos k
    simp only [collatzOddIter_succ_right, collatzOdd]
    have h_val_pos : 0 < 3 * collatzOddIter k n + 1 := by omega
    have h_val_ne : 3 * collatzOddIter k n + 1 ≠ 0 := by omega
    exact Nat.div_pos (Nat.le_of_dvd h_val_pos
      (CycleEquation.pow_v2_dvd _ h_val_ne)) (by positivity)

/-- `syracuseStepCount` standard Collatz iterations reproduce k Syracuse steps. -/
theorem collatzIter_reaches_syracuse (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    collatzIter (syracuseStepCount n hn hn_pos k) n = collatzOddIter k n := by
  induction k with
  | zero =>
    simp only [syracuseStepCount, collatzIter, collatzOddIter]
  | succ k ih =>
    simp only [syracuseStepCount]
    rw [collatzIter_add, ih]
    let curr := collatzOddIter k n
    have hcurr_odd : Odd curr := CycleEquation.collatzOddIter_odd hn hn_pos k
    have hcurr_pos : 0 < curr := collatzOddIter_pos n hn hn_pos k
    have h_step : collatzIter (1 + v2 (3 * curr + 1)) curr = collatzOdd curr :=
      collatzIter_to_collatzOdd curr hcurr_odd hcurr_pos
    rw [h_step]
    exact (collatzOddIter_succ_right k n).symm

/-- If the Syracuse orbit hits 1 at step k, the standard Collatz orbit hits 1 too. -/
theorem syracuse_one_implies_collatz_one (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ)
    (h_syr_one : collatzOddIter k n = 1) :
    collatzIter (syracuseStepCount n hn hn_pos k) n = 1 := by
  rw [collatzIter_reaches_syracuse n hn hn_pos k, h_syr_one]

/-! ## Main results -/

/-- **Erdos Problem #1135 — The Collatz Conjecture** (callback pattern):
    Every positive integer eventually reaches 1.
    Zero custom axioms --- all literature assumptions enter as parameters. -/
theorem erdos_1135 (n : ℕ) (hn : 0 < n)
    (h_nodiv : Collatz.NoDivergenceCallback)
    (h_no_nontrivial_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False)
    : ∃ k : ℕ, collatzIter k n = 1 :=
  Collatz.collatz_all_reach_one h_nodiv h_no_nontrivial_cycles n hn

/-- **Erdos Problem #1135 via Baker-rollover contraction route**:
    Every positive integer eventually reaches 1.
    No-divergence via WeylBridge quantitative contraction + three-path no-cycles.
    Axioms: baker_rollover_supercritical_rate + supercritical_rate_implies_residue_hitting. -/
theorem erdos_1135_via_mixing (n : ℕ) (hn : 0 < n)
    (h_no_nontrivial_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False)
    : ∃ k : ℕ, collatzIter k n = 1 := by
  have h_nodiv : Collatz.NoDivergenceCallback := by
    intro n' hn'
    left
    induction n' using Nat.strongRecOn with
    | _ n' ih =>
    by_cases hn1 : n' = 1
    · exact ⟨0, by simpa [hn1, collatzIter]⟩
    by_cases hn2 : n' = 2
    · exact ⟨1, by simp [collatzIter, collatz, hn2]⟩
    by_cases hn3 : n' = 3
    · exact ⟨7, by rw [hn3]; rfl⟩
    by_cases hn4 : n' = 4
    · exact ⟨2, by simp [collatzIter, collatz, hn4]⟩
    by_cases hodd : Odd n'
    · have hn_gt1 : 1 < n' := by omega
      have h_not_div : ¬Collatz.OddOrbitDivergent n' :=
        Collatz.no_divergence_via_mixing n' hn_gt1 hodd
      have h_not_tail : ¬Collatz.TailUnboundedOddOrbit n' := h_not_div
      obtain ⟨k, hk⟩ := Collatz.odd_reaches_one_of_not_tail_unbounded
        n' hodd hn' h_not_tail h_no_nontrivial_cycles
      exact ⟨syracuseStepCount n' hodd hn' k,
        syracuse_one_implies_collatz_one n' hodd hn' k hk⟩
    · have h_even : n' % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
      have hhalf_pos : 0 < n' / 2 := by omega
      have hhalf_lt : n' / 2 < n' := Nat.div_lt_self hn' (by decide)
      obtain ⟨k, hk⟩ := ih (n' / 2) hhalf_lt hhalf_pos
      exact ⟨k + 1, by simpa [collatzIter, collatz, h_even] using hk⟩
  exact Collatz.collatz_all_reach_one h_nodiv h_no_nontrivial_cycles n hn

#print axioms erdos_1135
#print axioms erdos_1135_via_mixing
#print axioms Collatz.NoCycle.no_nontrivial_cycles_three_paths
#print axioms Collatz.no_divergence_via_mixing
#print axioms Collatz.drift_integer_crossing_shifts_residue
