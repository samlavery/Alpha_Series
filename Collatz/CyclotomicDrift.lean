/-
  CyclotomicDrift.lean — Path 3: Cyclotomic rigidity via prime projection and CRT
  =================================================================================

  Proves: No nontrivial CycleProfile is realizable, using the cyclotomic
  rigidity path (algebraic number theory in ℤ[ζ_d]).

  ## Core mechanism:

  1. **Weight extraction**: From a CycleProfile P with S = 2m, extract
     `weightsForFour : Fin m → ℕ` (each entry is a power of 2, bounded ≤ 3).

  2. **Prime-quotient CRT decomposition**: For squarefree m, project weights
     onto prime-quotient slices via `PrimeQuotientCRT.sliceFW`. Nontrivial
     profiles force at least one prime slice to be nonconstant.

  3. **Cyclotomic divisibility**: D | W lifts to (4-3ζ_q) | B in ℤ[ζ_q]
     via `CyclotomicBridge.OKD_divisibility_from_waveSum_divisibility`.
     The 4-adic cascade then forces all entries of a bounded nonconstant
     slice to be equal — contradiction.

  4. **Assembly**: The `squarefree_slice_remainder_contradiction` theorem
     combines steps 1-3. Offset witness iteration propagates the
     contradiction across all slice offsets.
-/
import Collatz.Defs
import Collatz.CyclotomicBridge
import Collatz.PrimeQuotientCRT
import Collatz.NumberTheoryAxioms
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Basic

open Collatz
open scoped BigOperators

namespace Collatz.CyclotomicDrift

set_option linter.unusedVariables false

/-! ## Partial sum infrastructure -/

lemma partialSum_zero {m : ℕ} (hm : 0 < m) (P : CycleProfile m) :
    P.partialSum ⟨0, hm⟩ = 0 := by
  unfold CycleProfile.partialSum
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi
  exact absurd hi (by omega)

lemma partialSum_one {m : ℕ} (hm : 1 < m) (P : CycleProfile m) :
    P.partialSum ⟨1, by omega⟩ = P.ν ⟨0, by omega⟩ := by
  unfold CycleProfile.partialSum
  have h_filter : Finset.univ.filter (fun x : Fin m => x < ⟨1, by omega⟩) =
      {⟨0, by omega⟩} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Fin.lt_def]
    constructor
    · intro h; exact Fin.ext (show x.val = 0 by omega)
    · intro h; subst h; show (0 : ℕ) < 1; omega
  rw [h_filter, Finset.sum_singleton]

/-- Cardinality of `{i | i < j}` in `Fin m` is `j`. -/
private lemma filter_lt_card {m : ℕ} (j : Fin m) :
    (Finset.univ.filter (fun x : Fin m => x < j)).card = j.val := by
  have h_eq : Finset.univ.filter (fun x : Fin m => x < j) = Finset.Iio j := by
    ext x
    simp [Finset.mem_Iio]
  rw [h_eq, Fin.card_Iio]

/-- Monotone lower bound from positivity: `S_j ≥ j`. -/
lemma partialSum_ge_index {m : ℕ} (P : CycleProfile m) (j : Fin m) :
    j.val ≤ P.partialSum j := by
  unfold CycleProfile.partialSum
  calc
    j.val = ∑ _i ∈ Finset.univ.filter (fun x : Fin m => x < j), (1 : ℕ) := by
      simp [filter_lt_card]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun x : Fin m => x < j), P.ν i := by
      apply Finset.sum_le_sum
      intro i hi
      exact P.ν_pos i

/-! ## A+B decomposition -/

/-- A = 3^{m-1} · (1 + 3n₀), the j=0 term merged with n₀·3^m. -/
def termA (m : ℕ) (n₀ : ℤ) : ℤ := 3 ^ (m - 1) * (1 + 3 * n₀)

/-- B = Σ_{j≥1} 3^{m-1-j} · 2^{S_j}, the tail terms. -/
noncomputable def termB {m : ℕ} (P : CycleProfile m) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => 1 ≤ j.val),
    (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j)

/-- E = A + B: the orbit quantity decomposes. -/
theorem E_eq_A_plus_B {m : ℕ} (hm : 2 ≤ m) (P : CycleProfile m) (n₀ : ℤ) :
    (P.waveSum : ℤ) + n₀ * 3 ^ m = termA m n₀ + termB P := by
  unfold CycleProfile.waveSum termA termB
  push_cast
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  have h_ps0 : P.partialSum (0 : Fin (m' + 1)) = 0 :=
    partialSum_zero (by omega) P
  simp only [Fin.val_zero, h_ps0, pow_zero, mul_one]
  norm_num [Nat.add_sub_cancel]
  have h_filter : ∑ j ∈ Finset.univ.filter (fun j : Fin (m' + 1) => 1 ≤ j.val),
      (3 : ℤ) ^ (m' - j.val) * 2 ^ P.partialSum j =
      ∑ i : Fin m', (3 : ℤ) ^ (m' - (i.val + 1)) * 2 ^ P.partialSum i.succ := by
    have h_eq : Finset.univ.filter (fun j : Fin (m' + 1) => 1 ≤ j.val) =
        Finset.univ.image Fin.succ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h_j
        have hj_lt : j.val < m' + 1 := j.isLt
        use ⟨j.val - 1, by omega⟩
        simp only [Fin.ext_iff, Fin.val_succ]; omega
      · rintro ⟨i, -, rfl⟩; exact Nat.succ_pos i.val
    rw [h_eq, Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)]
    apply Finset.sum_congr rfl; intro i _; simp [Fin.val_succ]
  rw [h_filter]; ring

/-! ## 2-adic valuation infrastructure -/

private lemma termA_dvd_iff {m : ℕ} (hm : m ≥ 2) (n₀ : ℤ) (hn₀_pos : n₀ > 0)
    (k : ℕ) : (2 : ℤ) ^ k ∣ termA m n₀ ↔ (2 : ℤ) ^ k ∣ (1 + 3 * n₀) := by
  unfold termA
  have h23 : IsCoprime (2 : ℤ) 3 := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl]
    exact_mod_cast (by decide : Nat.Coprime 2 3).isCoprime
  have h_coprime : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ (m - 1)) :=
    h23.pow_left.pow_right
  constructor
  · intro ⟨c, hc⟩; exact h_coprime.dvd_of_dvd_mul_right ⟨c, by linarith⟩
  · intro h; exact dvd_mul_of_dvd_right h _

/-- ν₀ < S when m ≥ 2. -/
private lemma nu0_lt_S {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) :
    P.ν ⟨0, by omega⟩ < P.S := by
  have h1 := P.ν_pos ⟨1, by omega⟩
  have hle : P.ν ⟨0, by omega⟩ + P.ν ⟨1, by omega⟩ ≤ P.S := by
    rw [← P.sum_ν]
    calc P.ν ⟨0, by omega⟩ + P.ν ⟨1, by omega⟩
        = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin m)).sum P.ν := by
          rw [Finset.sum_pair (Fin.ne_of_val_ne (by norm_num))]
      _ ≤ Finset.univ.sum P.ν :=
          Finset.sum_le_sum_of_subset (fun x _ => Finset.mem_univ x)
  linarith

/-- For j ≥ 2: partialSum j ≥ ν₀ + 1. -/
private lemma partialSum_ge_two {m : ℕ} (hm : 2 ≤ m) (P : CycleProfile m)
    (j : Fin m) (hj : 2 ≤ j.val) :
    P.partialSum j ≥ P.ν ⟨0, by omega⟩ + 1 := by
  unfold CycleProfile.partialSum
  calc ∑ i ∈ Finset.univ.filter (fun x : Fin m => x < j), P.ν i
      ≥ P.ν ⟨0, by omega⟩ + P.ν ⟨1, by omega⟩ := by
        calc ∑ i ∈ Finset.univ.filter (fun x : Fin m => x < j), P.ν i
            ≥ ∑ i ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin m)), P.ν i := by
              apply Finset.sum_le_sum_of_subset
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
              rcases hx with rfl | rfl
              · show (0 : ℕ) < j.val; omega
              · show (1 : ℕ) < j.val; omega
          _ = P.ν ⟨0, by omega⟩ + P.ν ⟨1, by omega⟩ := by
              rw [Finset.sum_pair (Fin.ne_of_val_ne (by norm_num))]
    _ ≥ P.ν ⟨0, by omega⟩ + 1 := by linarith [P.ν_pos ⟨1, by omega⟩]

/-- 2^{ν₀} | termB P -/
private lemma two_pow_nu0_dvd_termB {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) :
    (2 : ℤ) ^ (P.ν ⟨0, by omega⟩) ∣ termB P := by
  unfold termB
  apply Finset.dvd_sum
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  apply dvd_mul_of_dvd_right; apply pow_dvd_pow
  unfold CycleProfile.partialSum
  calc P.ν ⟨0, by omega⟩
      = ({⟨0, by omega⟩} : Finset (Fin m)).sum P.ν := by simp
    _ ≤ (Finset.univ.filter (fun x : Fin m => x < j)).sum P.ν := by
        apply Finset.sum_le_sum_of_subset
        intro x hx; simp only [Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
        subst hx; show (0 : ℕ) < j.val; omega

/-- 2^{ν₀+1} ∤ termB P (the j=1 term has v₂ = ν₀ exactly) -/
private lemma not_two_pow_nu0_succ_dvd_termB {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) :
    ¬(2 : ℤ) ^ (P.ν ⟨0, by omega⟩ + 1) ∣ termB P := by
  set ν₀ := P.ν ⟨0, by omega⟩
  intro h_dvd
  have h_ps1 : P.partialSum ⟨1, by omega⟩ = ν₀ := partialSum_one (by omega) P
  have h_tail_dvd : ∀ j ∈ Finset.univ.filter (fun j : Fin m => 2 ≤ j.val),
      (2 : ℤ) ^ (ν₀ + 1) ∣ (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    apply dvd_mul_of_dvd_right; apply pow_dvd_pow
    exact partialSum_ge_two hm P j hj
  have h_tail_sum_dvd : (2 : ℤ) ^ (ν₀ + 1) ∣
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 ≤ j.val),
        (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) :=
    Finset.dvd_sum h_tail_dvd
  have h_split : termB P = (3 : ℤ) ^ (m - 1 - 1) * 2 ^ ν₀ +
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => 2 ≤ j.val),
        (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) := by
    unfold termB
    have h_partition : Finset.univ.filter (fun j : Fin m => 1 ≤ j.val) =
        {⟨1, by omega⟩} ∪ Finset.univ.filter (fun j : Fin m => 2 ≤ j.val) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_singleton, Fin.ext_iff]
      constructor
      · intro h; by_cases hj : j.val = 1
        · left; omega
        · right; omega
      · rintro (h | h) <;> omega
    have h_disj : Disjoint ({⟨1, by omega⟩} : Finset (Fin m))
        (Finset.univ.filter (fun j : Fin m => 2 ≤ j.val)) := by
      simp only [Finset.disjoint_singleton_left, Finset.mem_filter,
        Finset.mem_univ, true_and, not_le]; omega
    rw [h_partition, Finset.sum_union h_disj, Finset.sum_singleton, h_ps1]
  rw [h_split] at h_dvd
  have h_term1_dvd : (2 : ℤ) ^ (ν₀ + 1) ∣ (3 : ℤ) ^ (m - 1 - 1) * 2 ^ ν₀ := by
    have := dvd_sub h_dvd h_tail_sum_dvd; rwa [add_sub_cancel_right] at this
  rw [pow_succ] at h_term1_dvd
  have h_dvd2 : (2 : ℤ) ∣ (3 : ℤ) ^ (m - 1 - 1) := by
    have h2_ne : (2 : ℤ) ^ ν₀ ≠ 0 := by positivity
    rw [show (3 : ℤ) ^ (m - 1 - 1) * 2 ^ ν₀ = 2 ^ ν₀ * 3 ^ (m - 1 - 1) from by ring]
      at h_term1_dvd
    exact (mul_dvd_mul_iff_left h2_ne).mp h_term1_dvd
  have h_odd : ¬(2 : ℤ) ∣ (3 : ℤ) ^ (m - 1 - 1) := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl,
      ← Int.natCast_pow, Int.natCast_dvd_natCast]
    intro h; have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 2) h; omega
  exact h_odd h_dvd2

/-! ## Forced alignment: membership forces K = ν₀ -/

private lemma padicVal_dvd (n₀ : ℤ) (hn₀_pos : n₀ > 0) :
    (2 : ℤ) ^ padicValInt 2 (1 + 3 * n₀) ∣ (1 + 3 * n₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact padicValInt_dvd (1 + 3 * n₀)

private lemma padicVal_not_dvd_succ (n₀ : ℤ) (hn₀_pos : n₀ > 0) :
    ¬(2 : ℤ) ^ (padicValInt 2 (1 + 3 * n₀) + 1) ∣ (1 + 3 * n₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro h
  have h' : (↑(2 : ℕ) : ℤ) ^ (padicValInt 2 (1 + 3 * n₀) + 1) ∣ (1 + 3 * n₀) := by
    exact_mod_cast h
  rw [padicValInt_dvd_iff] at h'
  rcases h' with h_zero | h_le <;> omega

/-- Distinct case: K ≠ ν₀ ⟹ 2^S ∤ (A+B) -/
theorem v2_bound_distinct_case {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m) (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (hK_ne : padicValInt 2 (1 + 3 * n₀) ≠ P.ν ⟨0, by omega⟩) :
    ¬((2 : ℤ) ^ P.S ∣ (termA m n₀ + termB P)) := by
  set K := padicValInt 2 (1 + 3 * n₀)
  set ν₀ := P.ν ⟨0, by omega⟩
  intro h_dvd
  rcases Nat.lt_or_gt_of_ne hK_ne with hK_lt | hK_gt
  · have hA_not : ¬(2 : ℤ) ^ (K + 1) ∣ termA m n₀ := by
      rw [termA_dvd_iff hm n₀ hn₀_pos]; exact padicVal_not_dvd_succ n₀ hn₀_pos
    have hB_dvd : (2 : ℤ) ^ (K + 1) ∣ termB P := by
      calc (2 : ℤ) ^ (K + 1) ∣ (2 : ℤ) ^ ν₀ := pow_dvd_pow 2 (by omega)
        _ ∣ termB P := two_pow_nu0_dvd_termB hm P
    have h_le : K + 1 ≤ P.S := by have := nu0_lt_S hm P; omega
    have h_dvd_K1 : (2 : ℤ) ^ (K + 1) ∣ (termA m n₀ + termB P) :=
      dvd_trans (pow_dvd_pow 2 h_le) h_dvd
    exact absurd h_dvd_K1 (by
      intro h; exact hA_not (by have := dvd_sub h hB_dvd; rwa [add_sub_cancel_right] at this))
  · have hA_dvd : (2 : ℤ) ^ (ν₀ + 1) ∣ termA m n₀ := by
      rw [termA_dvd_iff hm n₀ hn₀_pos]
      exact dvd_trans (pow_dvd_pow 2 (by omega : ν₀ + 1 ≤ K)) (padicVal_dvd n₀ hn₀_pos)
    have hB_not : ¬(2 : ℤ) ^ (ν₀ + 1) ∣ termB P :=
      not_two_pow_nu0_succ_dvd_termB hm P
    have h_le : ν₀ + 1 ≤ P.S := by have := nu0_lt_S hm P; omega
    have h_dvd_nu1 : (2 : ℤ) ^ (ν₀ + 1) ∣ (termA m n₀ + termB P) :=
      dvd_trans (pow_dvd_pow 2 h_le) h_dvd
    exact absurd (by have := dvd_sub h_dvd_nu1 hA_dvd; rwa [add_sub_cancel_left] at this) hB_not

/-- Forced alignment: membership forces K = ν₀. -/
theorem forced_alignment {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m) (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (hAB_eq : termA m n₀ + termB P = n₀ * 2 ^ P.S)
    (hD_pos : cycleDenominator m P.S > 0) :
    padicValInt 2 (1 + 3 * n₀) = P.ν ⟨0, by omega⟩ := by
  by_contra hK_ne
  have h_dvd : (2 : ℤ) ^ P.S ∣ (termA m n₀ + termB P) := ⟨n₀, by linarith⟩
  exact absurd h_dvd (v2_bound_distinct_case hm P n₀ hn₀_pos hn₀_odd hK_ne)

/-! ## Rational loop map — ℚ-lattice trajectory

  The rational loop map T(x) = (3^m · x + W) / 2^S on ℚ has unique
  fixed point x* = W/D. Starting from any n₀ ∈ ℤ:

    q_L = x* + a^L · (n₀ - x*),   a = 3^m / 2^S

  When D ∤ W, x* ∉ ℤ, so the rational orbit drifts away from ℤ.
  Once dist(q_L, ℤ) > 1/2, the integer shadow z_L = ⌊q_L⌉ jumps,
  contradicting a stable integer loop. -/

/-- The rational one-loop map: T(x) = (3^m · x + W) / 2^S. -/
noncomputable def rationalStep {m : ℕ} (P : CycleProfile m) (x : ℚ) : ℚ :=
  (3 ^ m * x + P.waveSum) / 2 ^ P.S

/-- Iteration of the rational loop map. -/
noncomputable def rationalIter {m : ℕ} (P : CycleProfile m) : ℕ → ℚ → ℚ
  | 0, x => x
  | L + 1, x => rationalIter P L (rationalStep P x)

/-- The fixed point of the rational loop map: x* = W / D. -/
noncomputable def fixedPoint {m : ℕ} (P : CycleProfile m) : ℚ :=
  (P.waveSum : ℚ) / (cycleDenominator m P.S : ℚ)

/-- **Rational loop closure**: if n₀ is a fixed point of T in ℤ (i.e. T(n₀) = n₀),
    then n₀ = W/D, hence D | W.

    This is the integrality bridge: a "stable integer loop" forces D | W. -/
theorem rational_loop_forces_divisibility {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (hD_pos : cycleDenominator m P.S > 0)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0)
    (h_fixed : rationalStep P (n₀ : ℚ) = (n₀ : ℚ)) :
    (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ) := by
  -- T(n₀) = n₀ means (3^m · n₀ + W) / 2^S = n₀
  -- So 3^m · n₀ + W = n₀ · 2^S
  -- So W = n₀ · (2^S - 3^m) = n₀ · D
  unfold rationalStep at h_fixed
  have h2S_pos : (2 : ℚ) ^ P.S > 0 := by positivity
  have h2S_ne : (2 : ℚ) ^ P.S ≠ 0 := ne_of_gt h2S_pos
  rw [div_eq_iff h2S_ne] at h_fixed
  -- h_fixed : 3^m * n₀ + W = n₀ * 2^S  (in ℚ)
  -- So W = n₀ · D (in ℚ), hence in ℤ
  have h_int : (P.waveSum : ℤ) = n₀ * cycleDenominator m P.S := by
    have h_eq : (P.waveSum : ℚ) = (n₀ : ℚ) * ((2 : ℚ) ^ P.S - 3 ^ m) := by
      linarith
    have h_cast : (P.waveSum : ℚ) = ((n₀ * cycleDenominator m P.S : ℤ) : ℚ) := by
      rw [h_eq]; push_cast; unfold cycleDenominator; push_cast; ring
    exact_mod_cast h_cast
  exact ⟨n₀, by rw [h_int]; ring⟩

/-- **Non-integer fixed point implies orbit drift**: when D ∤ W, the fixed point
    x* = W/D is not an integer, so no integer can be a fixed point of T.

    This is the contrapositive of rational_loop_forces_divisibility:
    D ∤ W ⟹ ∀ n₀ ∈ ℤ, T(n₀) ≠ n₀. The rational orbit drifts — no
    stable integer loop exists. -/
theorem no_integer_fixed_point {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (hD_pos : cycleDenominator m P.S > 0)
    (h_not_dvd : ¬(cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) :
    rationalStep P (n₀ : ℚ) ≠ (n₀ : ℚ) := by
  intro h_fixed
  exact h_not_dvd (rational_loop_forces_divisibility hm P hD_pos n₀ hn₀_pos h_fixed)

/-! ## Cyclotomic bridge fragments from D ∣ W

These lemmas isolate arithmetic steps needed by the full rigidity bridge. -/

/-- Irrational-profile view of a cycle profile: same discrete data (`ν`, `S`),
plus real drift witness `drift = S - m*log₂(3)` and irrationality. -/
structure IrrationalCycleProfile (m : ℕ) where
  ν : Fin m → ℕ
  ν_pos : ∀ j, ν j ≥ 1
  S : ℕ
  sum_ν : ∑ j : Fin m, ν j = S
  drift : ℝ
  drift_def : drift = S - m * Real.logb 2 3
  drift_irrational : Irrational drift

namespace IrrationalCycleProfile

variable {m : ℕ}

/-- Forget the real drift witness and recover the integer cycle profile. -/
def toIntegerProfile (Q : IrrationalCycleProfile m) : CycleProfile m where
  ν := Q.ν
  ν_pos := Q.ν_pos
  S := Q.S
  sum_ν := Q.sum_ν

/-- Bridge predicate: integer profile and irrational profile share the same
discrete cycle data (`ν`, `S`). -/
def Compatible (P : CycleProfile m) (Q : IrrationalCycleProfile m) : Prop :=
  P = Q.toIntegerProfile

lemma compatible_S_eq {P : CycleProfile m} {Q : IrrationalCycleProfile m}
    (h : Compatible P Q) : P.S = Q.S := by
  simpa [Compatible, toIntegerProfile] using congrArg CycleProfile.S h

lemma compatible_nu_eq {P : CycleProfile m} {Q : IrrationalCycleProfile m}
    (h : Compatible P Q) : P.ν = Q.ν := by
  simpa [Compatible, toIntegerProfile] using congrArg CycleProfile.ν h

lemma drift_ne_zero (Q : IrrationalCycleProfile m) : Q.drift ≠ 0 := by
  intro h0
  exact Q.drift_irrational ⟨0, by simpa [h0]⟩

end IrrationalCycleProfile

/-! ## Dual profile view: integer (`ℕ`) profile vs irrational (`ℝ`) profile -/

/-- Integer-side cycle profile wrapper. -/
structure NatCycleProfile (m : ℕ) where
  profile : CycleProfile m

/-- Real-side cycle profile wrapper (same discrete data + irrational drift). -/
structure RealCycleProfile (m : ℕ) where
  profile : IrrationalCycleProfile m

namespace DualProfiles

variable {m d : ℕ}

/-- Compatibility between nat and real profile views:
they encode the same discrete cycle data (`ν`, `S`). -/
def Compatible (PN : NatCycleProfile m) (PR : RealCycleProfile m) : Prop :=
  IrrationalCycleProfile.Compatible PN.profile PR.profile

/-- Folded weights induced by the integer profile. -/
noncomputable def foldedWeightsNat (PN : NatCycleProfile m) (d : ℕ) : Fin d → ℕ :=
  Collatz.foldedWeights d PN.profile.ν

/-- Drift-updated folded weights induced by the real profile at loop `L`. -/
noncomputable def foldedWeightsRealDrift
    (PN : NatCycleProfile m) (PR : RealCycleProfile m) (d : ℕ) (L : ℕ) : Fin d → ℕ :=
  Collatz.CyclotomicBridge.driftUpdatedFoldedWeights d (foldedWeightsNat PN d) PR.profile.drift L

/-- Real-profile divisibility holds at every loop index. -/
def RealDivHolds (PN : NatCycleProfile m) (PR : RealCycleProfile m) (d : ℕ) : Prop :=
  ∀ L : ℕ, (4 ^ d - 3 ^ d : ℤ) ∣
    Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L)

lemma realDivHolds_implies_tail
    (PN : NatCycleProfile m) (PR : RealCycleProfile m) (d : ℕ)
    (h_real_all : RealDivHolds PN PR d) :
    ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      (4 ^ d - 3 ^ d : ℤ) ∣
        Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L) := by
  refine ⟨0, ?_⟩
  intro L _
  exact h_real_all L

/-- If drift is zero, the real-profile folded divisibility condition is
stable across loops: holding at one loop index implies holding at all loop
indices. -/
theorem realDivHolds_from_once_of_zero_drift
    (PN : NatCycleProfile m) (PR : RealCycleProfile m) (d : ℕ)
    (h_drift_zero : PR.profile.drift = 0)
    (h_real_at0 : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d 0)) :
    RealDivHolds PN PR d := by
  have h_real_at0' : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d
        (Collatz.CyclotomicBridge.driftUpdatedFoldedWeights d (foldedWeightsNat PN d) 0 0) := by
    simpa [foldedWeightsRealDrift, h_drift_zero] using h_real_at0
  have h_all0 :
      ∀ L : ℕ, (4 ^ d - 3 ^ d : ℤ) ∣
        Collatz.CyclotomicBridge.evalSum43' d
          (Collatz.CyclotomicBridge.driftUpdatedFoldedWeights d (foldedWeightsNat PN d) 0 L) :=
    Collatz.CyclotomicBridge.divisibility_holds_forever_of_zero_drift
      d (foldedWeightsNat PN d) 0 h_real_at0'
  intro L
  simpa [foldedWeightsRealDrift, h_drift_zero] using h_all0 L

/-- With a nat profile and its real/irrational companion, folded-weight
divisibility constraints eventually separate: they cannot both satisfy the
same cyclotomic divisibility requirement forever. -/
theorem eventually_not_both_divisible_nat_vs_real
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (_hcompat : Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, foldedWeightsNat PN d r = foldedWeightsNat PN d s) :
    ∃ L : ℕ,
      ¬(((4 ^ d - 3 ^ d : ℤ) ∣ Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsNat PN d)) ∧
        ((4 ^ d - 3 ^ d : ℤ) ∣
          Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L))) := by
  have h_drift_ne : PR.profile.drift ≠ 0 := IrrationalCycleProfile.drift_ne_zero PR.profile
  simpa [foldedWeightsRealDrift, foldedWeightsNat]
    using Collatz.CyclotomicBridge.eventually_not_both_divisible_from_drift_update_of_ne_zero
      d hd hd_ge_2 (foldedWeightsNat PN d) PR.profile.drift h_fwint_bdd h_fwint_uniform h_drift_ne

/-- Inductive eventual-separation form: if rounded accumulated drift is
eventually nonzero from some threshold `L0`, then from `L0` onward the nat
and real folded profiles cannot both satisfy the same divisibility condition. -/
theorem eventually_not_both_divisible_nat_vs_real_induction
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (_hcompat : Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, foldedWeightsNat PN d r = foldedWeightsNat PN d s)
    (h_eventual_round_ne_zero : ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      round ((L : ℝ) * PR.profile.drift) ≠ 0) :
    ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      ¬(((4 ^ d - 3 ^ d : ℤ) ∣ Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsNat PN d)) ∧
        ((4 ^ d - 3 ^ d : ℤ) ∣
          Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L))) := by
  rcases h_eventual_round_ne_zero with ⟨L0, hL0⟩
  refine ⟨L0, ?_⟩
  intro L h_ge
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h_ge
  subst hk
  induction k with
  | zero =>
      have h_round : round (((L0 : ℕ) : ℝ) * PR.profile.drift) ≠ 0 := hL0 L0 (le_rfl)
      simpa [foldedWeightsRealDrift] using
        Collatz.CyclotomicBridge.not_both_divisible_from_drift_update_at_L
          d hd hd_ge_2 (foldedWeightsNat PN d) PR.profile.drift L0
          h_fwint_bdd h_fwint_uniform h_round
  | succ k _ =>
      have h_round : round (((L0 + k.succ : ℕ) : ℝ) * PR.profile.drift) ≠ 0 :=
        hL0 (L0 + k.succ) (Nat.le_add_right _ _)
      simpa [foldedWeightsRealDrift] using
        Collatz.CyclotomicBridge.not_both_divisible_from_drift_update_at_L
          d hd hd_ge_2 (foldedWeightsNat PN d) PR.profile.drift (L0 + k.succ)
          h_fwint_bdd h_fwint_uniform h_round

/-- "Only one profile" divisibility corollary.
If the nat-profile folded weights satisfy the cyclotomic divisibility condition,
then beyond the drift threshold the real/irrational folded profile cannot satisfy
that same divisibility condition. -/
theorem eventually_only_nat_profile_divisible
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (_hcompat : Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, foldedWeightsNat PN d r = foldedWeightsNat PN d s)
    (h_eventual_round_ne_zero : ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      round ((L : ℝ) * PR.profile.drift) ≠ 0)
    (h_int_div : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsNat PN d)) :
    ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      ¬((4 ^ d - 3 ^ d : ℤ) ∣
        Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L)) := by
  rcases eventually_not_both_divisible_nat_vs_real_induction
      (m := m) (d := d) PN PR _hcompat hd hd_ge_2 h_fwint_bdd h_fwint_uniform
      h_eventual_round_ne_zero with ⟨L0, hsep⟩
  refine ⟨L0, ?_⟩
  intro L hL h_real_div
  have h_not_both := hsep L hL
  exact h_not_both ⟨h_int_div, h_real_div⟩

/-- Real-profile validity is compatible with eventual failure of integer-side
divisibility for the drift-updated folded weights.

Interpretation:
- The real profile remains a valid real-dynamics object (its drift identity holds).
- Meanwhile, under nonzero accumulated drift and integer-side divisibility on the
  nat profile, the real drift-updated folded weights eventually fail the same
  integer/cyclotomic divisibility requirement. -/
theorem real_profile_valid_while_integer_divisibility_eventually_fails
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (_hcompat : Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, foldedWeightsNat PN d r = foldedWeightsNat PN d s)
    (h_eventual_round_ne_zero : ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      round ((L : ℝ) * PR.profile.drift) ≠ 0)
    (h_int_div : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsNat PN d)) :
    (PR.profile.drift = PR.profile.S - m * Real.logb 2 3) ∧
    (∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      ¬((4 ^ d - 3 ^ d : ℤ) ∣
        Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L))) := by
  refine ⟨PR.profile.drift_def, ?_⟩
  exact eventually_only_nat_profile_divisible (m := m) (d := d) PN PR _hcompat hd hd_ge_2
    h_fwint_bdd h_fwint_uniform h_eventual_round_ne_zero h_int_div

/-- Bridge theorem: if nat-profile divisibility holds and real-profile
divisibility is assumed to hold for all loops, then eventual nonzero rounded
drift yields a contradiction (cannot hold for both). -/
theorem bridge_not_both_from_real_holds_all
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (hcompat : Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, foldedWeightsNat PN d r = foldedWeightsNat PN d s)
    (h_eventual_round_ne_zero : ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      round ((L : ℝ) * PR.profile.drift) ≠ 0)
    (h_int_div : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsNat PN d))
    (h_real_all : RealDivHolds PN PR d) :
    False := by
  obtain ⟨L0, hsep⟩ := eventually_not_both_divisible_nat_vs_real_induction
    (m := m) (d := d) PN PR hcompat hd hd_ge_2 h_fwint_bdd h_fwint_uniform
    h_eventual_round_ne_zero
  have h_not_both := hsep L0 (le_rfl)
  have h_real_L0 : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsRealDrift PN PR d L0) :=
    h_real_all L0
  exact h_not_both ⟨h_int_div, h_real_L0⟩

/-- Same bridge without requiring an explicit eventual-round hypothesis:
irrational drift already implies nonzero drift, which gives the threshold. -/
theorem bridge_not_both_from_real_holds_all_of_drift
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (hcompat : Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, foldedWeightsNat PN d r = foldedWeightsNat PN d s)
    (h_int_div : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (foldedWeightsNat PN d))
    (h_real_all : RealDivHolds PN PR d) :
    False := by
  have h_drift_ne : PR.profile.drift ≠ 0 := IrrationalCycleProfile.drift_ne_zero PR.profile
  obtain ⟨L0, hL0⟩ :=
    Collatz.CyclotomicBridge.eventually_round_mul_ne_zero_of_ne_zero PR.profile.drift h_drift_ne
  exact bridge_not_both_from_real_holds_all (m := m) (d := d)
    PN PR hcompat hd hd_ge_2 h_fwint_bdd h_fwint_uniform ⟨L0, hL0⟩ h_int_div h_real_all

end DualProfiles

/-- Replacement-attempt bridge: if nat/real dual profiles are compatible and
the integer folded weights keep divisibility while real drift-updated folded
weights also keep divisibility beyond some threshold, this contradicts the
induction-based separation theorem. -/
theorem dual_profile_divisibility_contradiction
    {m d : ℕ}
    (PN : NatCycleProfile m) (PR : RealCycleProfile m)
    (hcompat : DualProfiles.Compatible PN PR)
    (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (h_fwint_bdd : ∀ r : Fin d, DualProfiles.foldedWeightsNat PN d r ≤ 2)
    (h_fwint_uniform : ∀ r s : Fin d, DualProfiles.foldedWeightsNat PN d r =
      DualProfiles.foldedWeightsNat PN d s)
    (h_eventual_round_ne_zero : ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      round ((L : ℝ) * PR.profile.drift) ≠ 0)
    (h_int_div : (4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (DualProfiles.foldedWeightsNat PN d))
    (h_real_div_tail : ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      (4 ^ d - 3 ^ d : ℤ) ∣
        Collatz.CyclotomicBridge.evalSum43' d (DualProfiles.foldedWeightsRealDrift PN PR d L)) :
    False := by
  rcases h_real_div_tail with ⟨L1, hL1⟩
  rcases DualProfiles.eventually_not_both_divisible_nat_vs_real_induction
      (m := m) (d := d) PN PR hcompat hd hd_ge_2 h_fwint_bdd h_fwint_uniform
      h_eventual_round_ne_zero with ⟨L0, hsep⟩
  let L := max L0 L1
  have hL0 : L ≥ L0 := le_max_left _ _
  have hL1' : L ≥ L1 := le_max_right _ _
  have h_not_both := hsep L hL0
  have h_both : ((4 ^ d - 3 ^ d : ℤ) ∣
      Collatz.CyclotomicBridge.evalSum43' d (DualProfiles.foldedWeightsNat PN d)) ∧
      ((4 ^ d - 3 ^ d : ℤ) ∣
        Collatz.CyclotomicBridge.evalSum43' d (DualProfiles.foldedWeightsRealDrift PN PR d L)) :=
    ⟨h_int_div, hL1 L hL1'⟩
  exact h_not_both h_both

/-- If `S = 2m`, then `D = 2^S - 3^m` is exactly `4^m - 3^m`, so every
`Φ_d(4,3)` with `d ∣ m` divides `D`. -/
lemma cyclotomicBivar_dvd_cycleDenominator_of_S_eq_two_mul
    {m d : ℕ} (P : CycleProfile m)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m)
    (hS : P.S = 2 * m) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ cycleDenominator m P.S := by
  rw [hS, cycleDenominator]
  have hpow : ((2 : ℤ) ^ (2 * m)) = (4 : ℤ) ^ m := by
    rw [pow_mul]
    norm_num
  rw [hpow]
  exact Collatz.CyclotomicBridge.cyclotomicBivar_dvd_pow_sub_general (d := d) (m := m)
    hd_pos hd_dvd

/-- Any divisor of `D` is also a divisor of `W` once `D ∣ W` is known. -/
lemma divisor_of_cycleDenominator_dvd_waveSum
    {m : ℕ} (P : CycleProfile m) (z : ℤ)
    (hzD : z ∣ cycleDenominator m P.S)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)) :
    z ∣ (P.waveSum : ℤ) :=
  dvd_trans hzD h_dvd

/-- Any cyclotomic divisor of `D` is also a divisor of `W` once `D ∣ W` is known. -/
lemma cyclotomicBivar_dvd_waveSum_of_dvd_cycleDenominator
    {m d : ℕ} (P : CycleProfile m)
    (hPhiD : (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ cycleDenominator m P.S)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ) :=
  divisor_of_cycleDenominator_dvd_waveSum P _ hPhiD h_dvd

/-- Packaged form: under `S = 2m`, `D ∣ W` implies `Φ_d(4,3) ∣ W` for each `d ∣ m`. -/
lemma cyclotomicBivar_dvd_waveSum_of_S_eq_two_mul
    {m d : ℕ} (P : CycleProfile m)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ) := by
  exact cyclotomicBivar_dvd_waveSum_of_dvd_cycleDenominator P
    (cyclotomicBivar_dvd_cycleDenominator_of_S_eq_two_mul P hd_pos hd_dvd hS)
    h_dvd

/-- **Bridge (waveSumPoly form).**
If `Φ_d(4,3)` divides `W` and `W` is realized as `waveSumPoly m weights 4`,
then the cyclotomic OKD divisibility holds for the folded weights `FW`.

This isolates the exact conversion step needed for the rigidity cascade. -/
lemma OKD_divisibility_from_waveSum_dvd
    {m d : ℕ} [NeZero d] (P : CycleProfile m)
    (hd_ge_2 : d ≥ 2) (hm_pos : 0 < m) (hd_dvd : d ∣ m)
    (weights : Fin m → ℕ)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m, if (j : ℕ) % d = r.val then weights j else 0)
    (h_waveSumPoly_eq : Collatz.CyclotomicBridge.waveSumPoly m weights 4 = (P.waveSum : ℤ))
    (h_cyc_dvd : (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ)) :
    Collatz.CyclotomicBridge.fourSubThreeO d ∣ Collatz.CyclotomicBridge.balanceSumO d FW := by
  have h_cyc_dvd' :
      (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣
        Collatz.CyclotomicBridge.waveSumPoly m weights 4 := by
    simpa [h_waveSumPoly_eq]
      using h_cyc_dvd
  exact Collatz.CyclotomicBridge.OKD_divisibility_from_waveSum_divisibility
    (d := d) hd_ge_2 (m := m) hm_pos hd_dvd weights FW h_FW_def h_cyc_dvd'

/-- Generic wave-sum bridge:
if weights satisfy `weights j * x^j = 2^(S_j)`, then
`waveSumPoly m weights x = waveSum`. -/
lemma waveSumPoly_eq_waveSum_of_weight_pow
    {m : ℕ} (P : CycleProfile m)
    (x : ℤ)
    (weights : Fin m → ℕ)
    (h_weight :
      ∀ j : Fin m,
        ((weights j : ℤ) * x ^ j.val) = (2 : ℤ) ^ (P.partialSum j)) :
    Collatz.CyclotomicBridge.waveSumPoly m weights x = (P.waveSum : ℤ) := by
  unfold Collatz.CyclotomicBridge.waveSumPoly CycleProfile.waveSum
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have hw := h_weight j
  calc
    (3 : ℤ) ^ (m - 1 - j.val) * (weights j : ℤ) * x ^ j.val
        = (3 : ℤ) ^ (m - 1 - j.val) * ((weights j : ℤ) * x ^ j.val) := by ring
    _ = (3 : ℤ) ^ (m - 1 - j.val) * (2 : ℤ) ^ (P.partialSum j) := by rw [hw]

/-- If weights satisfy `weights j * 4^j = 2^(S_j)`, then
`waveSumPoly m weights 4 = waveSum`. -/
lemma waveSumPoly_eq_waveSum_of_weight_four_pow
    {m : ℕ} (P : CycleProfile m)
    (weights : Fin m → ℕ)
    (h_weight :
      ∀ j : Fin m,
        ((weights j : ℤ) * 4 ^ j.val) = (2 : ℤ) ^ (P.partialSum j)) :
    Collatz.CyclotomicBridge.waveSumPoly m weights 4 = (P.waveSum : ℤ) :=
  waveSumPoly_eq_waveSum_of_weight_pow P 4 weights h_weight

/-- Profile-induced weights for the `x=4` wave polynomial, assuming
`2*j ≤ S_j` so the exponent remains in `ℕ`. -/
def weightsForFour {m : ℕ} (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) : Fin m → ℕ :=
  fun j => 2 ^ (P.partialSum j - 2 * j.val)

/-- Generalized profile-induced weights for `x = 2^q` wave polynomials,
assuming `q*j ≤ S_j` so exponents remain in `ℕ`. This is the base needed for
critical-ratio (`S/m ≈ log₂ 3`) refactors where `q` is not fixed to `2`. -/
def weightsForBase {m : ℕ} (P : CycleProfile m) (q : ℕ)
    (h_geqj : ∀ j : Fin m, q * j.val ≤ P.partialSum j) : Fin m → ℕ :=
  fun j => 2 ^ (P.partialSum j - q * j.val)

/-- The defining identity for `weightsForFour`: `w_j * 4^j = 2^{S_j}`. -/
lemma weightsForFour_mul_four_pow
    {m : ℕ} (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    ∀ j : Fin m,
      (((weightsForFour P h_ge2j j : ℕ) : ℤ) * 4 ^ j.val) = (2 : ℤ) ^ (P.partialSum j) := by
  intro j
  have hsplit : (P.partialSum j - 2 * j.val) + 2 * j.val = P.partialSum j :=
    Nat.sub_add_cancel (h_ge2j j)
  calc
    (((weightsForFour P h_ge2j j : ℕ) : ℤ) * 4 ^ j.val)
        = ((2 : ℤ) ^ (P.partialSum j - 2 * j.val)) * 4 ^ j.val := by
            simp [weightsForFour]
    _ = ((2 : ℤ) ^ (P.partialSum j - 2 * j.val)) * (2 : ℤ) ^ (2 * j.val) := by
          rw [show (4 : ℤ) = 2 ^ (2 : ℕ) by norm_num, pow_mul]
    _ = (2 : ℤ) ^ ((P.partialSum j - 2 * j.val) + 2 * j.val) := by
          rw [← pow_add]
    _ = (2 : ℤ) ^ (P.partialSum j) := by simpa [hsplit]

/-- Generalized defining identity for `weightsForBase`: `w_j * (2^q)^j = 2^{S_j}`. -/
lemma weightsForBase_mul_base_pow
    {m : ℕ} (P : CycleProfile m) (q : ℕ)
    (h_geqj : ∀ j : Fin m, q * j.val ≤ P.partialSum j) :
    ∀ j : Fin m,
      (((weightsForBase P q h_geqj j : ℕ) : ℤ) * ((2 : ℤ) ^ q) ^ j.val) =
        (2 : ℤ) ^ (P.partialSum j) := by
  intro j
  have hsplit : (P.partialSum j - q * j.val) + q * j.val = P.partialSum j :=
    Nat.sub_add_cancel (h_geqj j)
  calc
    (((weightsForBase P q h_geqj j : ℕ) : ℤ) * ((2 : ℤ) ^ q) ^ j.val)
        = ((2 : ℤ) ^ (P.partialSum j - q * j.val)) * ((2 : ℤ) ^ q) ^ j.val := by
            simp [weightsForBase]
    _ = ((2 : ℤ) ^ (P.partialSum j - q * j.val)) * (2 : ℤ) ^ (q * j.val) := by
          rw [pow_mul]
    _ = (2 : ℤ) ^ ((P.partialSum j - q * j.val) + q * j.val) := by
          rw [← pow_add]
    _ = (2 : ℤ) ^ (P.partialSum j) := by simpa [hsplit]

/-- `waveSumPoly` realization from the profile-induced four-weights. -/
lemma waveSumPoly_eq_waveSum_weightsForFour
    {m : ℕ} (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    Collatz.CyclotomicBridge.waveSumPoly m (weightsForFour P h_ge2j) 4 = (P.waveSum : ℤ) := by
  exact waveSumPoly_eq_waveSum_of_weight_four_pow P (weightsForFour P h_ge2j)
    (weightsForFour_mul_four_pow P h_ge2j)

/-- Generalized wave-sum realization:
`waveSumPoly m (weightsForBase q) (2^q) = waveSum`. -/
lemma waveSumPoly_eq_waveSum_weightsForBase
    {m : ℕ} (P : CycleProfile m) (q : ℕ)
    (h_geqj : ∀ j : Fin m, q * j.val ≤ P.partialSum j) :
    Collatz.CyclotomicBridge.waveSumPoly m (weightsForBase P q h_geqj) ((2 : ℤ) ^ q) =
      (P.waveSum : ℤ) := by
  exact waveSumPoly_eq_waveSum_of_weight_pow P ((2 : ℤ) ^ q) (weightsForBase P q h_geqj)
    (weightsForBase_mul_base_pow P q h_geqj)

/-- Quotient-base realization with `q = S/m` (when used with appropriate
lower-bound hypotheses on partial sums). This is the algebraic entry point for
critical-ratio refactors that avoid fixing `q = 2`. -/
lemma waveSumPoly_eq_waveSum_weightsForQuotient
    {m : ℕ} (P : CycleProfile m)
    (h_geqj : ∀ j : Fin m, (P.S / m) * j.val ≤ P.partialSum j) :
    Collatz.CyclotomicBridge.waveSumPoly m
      (weightsForBase P (P.S / m) h_geqj) ((2 : ℤ) ^ (P.S / m)) =
      (P.waveSum : ℤ) :=
  waveSumPoly_eq_waveSum_weightsForBase P (P.S / m) h_geqj

/-- `waveSumPoly` at base `x` is exactly `evalSumXY` with `(x,3)`. -/
lemma waveSumPoly_eq_evalSumXY
    (m : ℕ) (weights : Fin m → ℕ) (x : ℤ) :
    Collatz.CyclotomicBridge.waveSumPoly m weights x =
      Collatz.CyclotomicBridge.evalSumXY m weights x 3 := by
  unfold Collatz.CyclotomicBridge.waveSumPoly Collatz.CyclotomicBridge.evalSumXY
  congr 1
  ext j
  ring

/-- **Prime-step rigidity from the bridge.**
Given a wave-sum polynomial representation at `x = 4`, cyclotomic divisibility of
that value lifts to `OKD`, and prime-case evaluation rigidity forces the folded
weights to be uniform. -/
theorem folded_weights_uniform_from_wave_bridge_prime
    {m d : ℕ} [Fact (Nat.Prime d)] [NeZero d]
    (P : CycleProfile m)
    (hd_ge_2 : d ≥ 2) (hm_pos : 0 < m) (hd_dvd : d ∣ m)
    (weights : Fin m → ℕ)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m, if (j : ℕ) % d = r.val then weights j else 0)
    (h_waveSumPoly_eq : Collatz.CyclotomicBridge.waveSumPoly m weights 4 = (P.waveSum : ℤ))
    (h_cyc_dvd : (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ))
    (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N) :
    ∀ r s : Fin d, FW r = FW s := by
  have h_OKD_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO d ∣
        Collatz.CyclotomicBridge.balanceSumO d FW :=
    OKD_divisibility_from_waveSum_dvd (P := P) (d := d) hd_ge_2 hm_pos hd_dvd
      weights FW h_FW_def h_waveSumPoly_eq h_cyc_dvd
  exact Collatz.CyclotomicBridge.folded_weights_all_equal_prime
    (d := d) (hd_prime := Fact.out) FW N hN h_bdd h_OKD_dvd

/-- Prime-step rigidity specialized to profile-induced four-weights.
This removes manual `weights` construction from the bridge application. -/
theorem folded_weights_uniform_for_profile_four_weights_prime
    {m d : ℕ} [Fact (Nat.Prime d)] [NeZero d]
    (P : CycleProfile m)
    (hd_ge_2 : d ≥ 2) (hm_pos : 0 < m) (hd_dvd : d ∣ m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m,
      if (j : ℕ) % d = r.val then weightsForFour P h_ge2j j else 0)
    (h_cyc_dvd : (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ))
    (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N) :
    ∀ r s : Fin d, FW r = FW s := by
  exact folded_weights_uniform_from_wave_bridge_prime (P := P) (d := d)
    hd_ge_2 hm_pos hd_dvd
    (weightsForFour P h_ge2j) FW h_FW_def
    (waveSumPoly_eq_waveSum_weightsForFour P h_ge2j)
    h_cyc_dvd N hN h_bdd

/-- Bridge theorem (no rigidity axiom): if `D ∣ W`, `S = 2m`, and `d` is prime,
then the `d`-folded profile-induced four-weights are uniform (under the usual
small-bound hypothesis used by prime evaluation rigidity). -/
theorem folded_weights_uniform_from_cycle_divisibility_prime
    {m d : ℕ} [Fact (Nat.Prime d)] [NeZero d]
    (P : CycleProfile m)
    (hd_ge_2 : d ≥ 2) (hm_pos : 0 < m) (hd_dvd : d ∣ m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m,
      if (j : ℕ) % d = r.val then weightsForFour P h_ge2j j else 0)
    (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N) :
    ∀ r s : Fin d, FW r = FW s := by
  have hd_pos : 0 < d := by omega
  have h_cyc_dvd :
      (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ) :=
    cyclotomicBivar_dvd_waveSum_of_S_eq_two_mul P hd_pos hd_dvd hS h_dvd
  exact folded_weights_uniform_for_profile_four_weights_prime (P := P) (d := d)
    hd_ge_2 hm_pos hd_dvd h_ge2j FW h_FW_def h_cyc_dvd N hN h_bdd

/-- Project-facing replacement for the axiomized rigidity step at a fixed prime
divisor: from cycle divisibility plus the constructed four-weights, obtain
prime folded-weight uniformity without using `cyclotomic_rigidity_axiom`. -/
theorem cyclotomic_rigidity_replacement_prime
    {m d : ℕ} [Fact (Nat.Prime d)] [NeZero d]
    (P : CycleProfile m)
    (hd_ge_2 : d ≥ 2) (hm_pos : 0 < m) (hd_dvd : d ∣ m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m,
      if (j : ℕ) % d = r.val then weightsForFour P h_ge2j j else 0)
    (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N) :
    ∀ r s : Fin d, FW r = FW s :=
  folded_weights_uniform_from_cycle_divisibility_prime
    (P := P) (d := d) hd_ge_2 hm_pos hd_dvd hS h_dvd h_ge2j FW h_FW_def N hN h_bdd

/-- Prime projection rigidity (projection form).
For a prime divisor `q ∣ m`, divisibility `D ∣ W` plus the constructed
four-weight projection forces uniform `q`-folded weights. -/
theorem prime_projection_rigidity
    {m q : ℕ} [Fact (Nat.Prime q)] [NeZero q]
    (P : CycleProfile m)
    (hq_ge_2 : q ≥ 2) (hm_pos : 0 < m) (hq_dvd : q ∣ m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (FW : Fin q → ℕ)
    (h_FW_def : ∀ r : Fin q, FW r = ∑ j : Fin m,
      if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0)
    (h_bdd : ∀ r : Fin q, FW r ≤ 3) :
    ∀ r s : Fin q, FW r = FW s := by
  exact folded_weights_uniform_from_cycle_divisibility_prime
    (P := P) (d := q) hq_ge_2 hm_pos hq_dvd hS h_dvd h_ge2j FW h_FW_def
    3 (by norm_num) h_bdd

/-- Step-2 descent theorem (constructive): from global cycle divisibility
`D ∣ W` and critical-line data `S = 2m`, every prime-divisor folded profile
inherits cyclotomic divisibility in `OKD q`.

This isolates the divisibility-transfer part of the prime-projection/CRT bridge. -/
theorem prime_projection_folded_OKD_divisibility
    {m q : ℕ} [Fact (Nat.Prime q)] [NeZero q]
    (P : CycleProfile m)
    (hq_ge_2 : q ≥ 2) (hm_pos : 0 < m) (hq_dvd : q ∣ m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    let FW : Fin q → ℕ :=
      fun r => ∑ j : Fin m, if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0
    Collatz.CyclotomicBridge.fourSubThreeO q ∣
      Collatz.CyclotomicBridge.balanceSumO q FW := by
  intro FW
  have h_cyc_dvd :
      (Collatz.CyclotomicBridge.cyclotomicBivar q 4 3 : ℤ) ∣ (P.waveSum : ℤ) := by
    exact cyclotomicBivar_dvd_waveSum_of_S_eq_two_mul
      (P := P) (d := q) (Nat.Prime.pos (Fact.out : Nat.Prime q)) hq_dvd hS h_dvd
  have h_FW_def :
      ∀ r : Fin q,
        FW r = ∑ j : Fin m, if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0 := by
    intro r
    rfl
  exact OKD_divisibility_from_waveSum_dvd
    (P := P) (d := q) hq_ge_2 hm_pos hq_dvd
    (weightsForFour P h_ge2j) FW h_FW_def
    (waveSumPoly_eq_waveSum_weightsForFour P h_ge2j)
    h_cyc_dvd

/-- Same replacement theorem, explicitly through nat/real profile compatibility.
This is the bridge variant when `S = 2m` is supplied on the irrational side. -/
theorem cyclotomic_rigidity_replacement_prime_via_irrational
    {m d : ℕ} [Fact (Nat.Prime d)] [NeZero d]
    (P : CycleProfile m) (Q : IrrationalCycleProfile m)
    (hcompat : IrrationalCycleProfile.Compatible P Q)
    (hd_ge_2 : d ≥ 2) (hm_pos : 0 < m) (hd_dvd : d ∣ m)
    (hS_irr : Q.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m,
      if (j : ℕ) % d = r.val then weightsForFour P h_ge2j j else 0)
    (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N) :
    ∀ r s : Fin d, FW r = FW s := by
  have hS_int : P.S = 2 * m := by
    calc
      P.S = Q.S := IrrationalCycleProfile.compatible_S_eq hcompat
      _ = 2 * m := hS_irr
  exact folded_weights_uniform_from_cycle_divisibility_prime
    (P := P) (d := d) hd_ge_2 hm_pos hd_dvd hS_int h_dvd h_ge2j FW h_FW_def N hN h_bdd

private lemma folded_mod_self_eq
    {m : ℕ} (w : Fin m → ℕ) :
    (fun r : Fin m => ∑ j : Fin m, if (j : ℕ) % m = r.val then w j else 0) = w := by
  classical
  funext r
  have hmod : ∀ j : Fin m, ((j : ℕ) % m = r.val) ↔ j = r := by
    intro j
    constructor
    · intro hj
      have h1 : (j : ℕ) = r.val := by simpa [Nat.mod_eq_of_lt j.2] using hj
      exact Fin.ext (by simpa using h1)
    · intro hj
      simpa [hj, Nat.mod_eq_of_lt r.2]
  calc
    (∑ j : Fin m, if (j : ℕ) % m = r.val then w j else 0)
        = ∑ j : Fin m, if j = r then w j else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [hmod j]
    _ = w r := by
        simpa using (Finset.sum_ite_eq' (s := Finset.univ) (a := r) (b := fun j : Fin m => w j))

private lemma partialSum_succ_eq_add_nu
    {m : ℕ} (P : CycleProfile m)
    (j : ℕ) (hj : j < m) (hj1 : j + 1 < m) :
    P.partialSum ⟨j + 1, hj1⟩ = P.partialSum ⟨j, hj⟩ + P.ν ⟨j, hj⟩ := by
  unfold CycleProfile.partialSum
  have h_filter_eq : (Finset.univ.filter (fun x : Fin m => x < ⟨j + 1, hj1⟩)) =
      (Finset.univ.filter (fun x : Fin m => x < ⟨j, hj⟩)) ∪ {⟨j, hj⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
    omega
  rw [h_filter_eq, Finset.sum_union]
  · simp
  · rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, not_lt]
    omega

private lemma nu_constant_of_uniform_weightsForFour_prime
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_uniform : ∀ j k : Fin m, weightsForFour P h_ge2j j = weightsForFour P h_ge2j k) :
    ∀ j k : Fin m, P.ν j = P.ν k := by
  have hm_pos : 0 < m := Nat.Prime.pos Fact.out
  let w : Fin m → ℕ := weightsForFour P h_ge2j
  have hw0 : w ⟨0, hm_pos⟩ = 1 := by
    simpa [w, weightsForFour] using congrArg (fun t => (2 : ℕ) ^ t) (partialSum_zero hm_pos P)
  have hw_all_one : ∀ j : Fin m, w j = 1 := by
    intro j
    calc
      w j = w ⟨0, hm_pos⟩ := h_uniform j ⟨0, hm_pos⟩
      _ = 1 := hw0
  have hps_eq_two_mul : ∀ j : Fin m, P.partialSum j = 2 * j.val := by
    intro j
    have hpow : 2 ^ (P.partialSum j - 2 * j.val) = 1 := by
      simpa [w, weightsForFour] using hw_all_one j
    have hsub0 : P.partialSum j - 2 * j.val = 0 := by
      exact (Nat.pow_right_injective (a := 2) (by decide : 2 ≤ 2)) (by simpa using hpow)
    have hle : P.partialSum j ≤ 2 * j.val := Nat.sub_eq_zero_iff_le.mp hsub0
    exact le_antisymm hle (h_ge2j j)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hnu_castSucc : ∀ i : Fin m', P.ν i.castSucc = 2 := by
    intro i
    have hi1 : i.castSucc.val + 1 < m' + 1 := by
      simpa using Nat.succ_lt_succ i.isLt
    have hi_lt : i.val < m' + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self _)
    have hsucc := partialSum_succ_eq_add_nu P i.val hi_lt hi1
    have hps_succ : P.partialSum i.succ = 2 * i.succ.val := hps_eq_two_mul i.succ
    have hps_cast : P.partialSum i.castSucc = 2 * i.castSucc.val := hps_eq_two_mul i.castSucc
    have hEq : 2 * (i.val + 1) = 2 * i.val + P.ν i.castSucc := by
      calc
        2 * (i.val + 1) = P.partialSum i.succ := by
          simpa [Fin.val_succ] using hps_succ.symm
        _ = P.partialSum i.castSucc + P.ν i.castSucc := hsucc
        _ = 2 * i.val + P.ν i.castSucc := by
          simpa [Fin.val_castSucc] using congrArg (fun t => t + P.ν i.castSucc) hps_cast
    have : P.ν i.castSucc = 2 := by
      omega
    simpa [Fin.val_succ, Fin.val_castSucc] using this
  have hnu_last : P.ν (Fin.last m') = 2 := by
    have hsum_univ : (∑ j : Fin (m' + 1), P.ν j) = 2 * (m' + 1) := by
      simpa [hS] using P.sum_ν
    rw [Fin.sum_univ_castSucc] at hsum_univ
    have hsum_castSucc : (∑ i : Fin m', P.ν i.castSucc) = m' * 2 := by
      calc
        (∑ i : Fin m', P.ν i.castSucc)
            = (∑ i : Fin m', 2) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                exact hnu_castSucc i
        _ = m' * 2 := by simp [Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]
    rw [hsum_castSucc] at hsum_univ
    omega
  have hnu_all_two : ∀ j : Fin (m' + 1), P.ν j = 2 := by
    intro j
    refine Fin.lastCases ?hLast ?hSucc j
    · exact hnu_last
    · intro i
      exact hnu_castSucc i
  intro j k
  simpa [hnu_all_two j, hnu_all_two k]

/-- Uniform `weightsForFour` force constant `ν` under the critical-line side
conditions (no primality assumption on `m`). -/
private lemma nu_constant_of_uniform_weightsForFour
    {m : ℕ}
    (hm : m ≥ 2) (P : CycleProfile m)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_uniform : ∀ j k : Fin m, weightsForFour P h_ge2j j = weightsForFour P h_ge2j k) :
    ∀ j k : Fin m, P.ν j = P.ν k := by
  have hm_pos : 0 < m := by omega
  let w : Fin m → ℕ := weightsForFour P h_ge2j
  have hw0 : w ⟨0, hm_pos⟩ = 1 := by
    simpa [w, weightsForFour] using congrArg (fun t => (2 : ℕ) ^ t) (partialSum_zero hm_pos P)
  have hw_all_one : ∀ j : Fin m, w j = 1 := by
    intro j
    calc
      w j = w ⟨0, hm_pos⟩ := h_uniform j ⟨0, hm_pos⟩
      _ = 1 := hw0
  have hps_eq_two_mul : ∀ j : Fin m, P.partialSum j = 2 * j.val := by
    intro j
    have hpow : 2 ^ (P.partialSum j - 2 * j.val) = 1 := by
      simpa [w, weightsForFour] using hw_all_one j
    have hsub0 : P.partialSum j - 2 * j.val = 0 := by
      exact (Nat.pow_right_injective (a := 2) (by decide : 2 ≤ 2)) (by simpa using hpow)
    have hle : P.partialSum j ≤ 2 * j.val := Nat.sub_eq_zero_iff_le.mp hsub0
    exact le_antisymm hle (h_ge2j j)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hnu_castSucc : ∀ i : Fin m', P.ν i.castSucc = 2 := by
    intro i
    have hi1 : i.castSucc.val + 1 < m' + 1 := by
      simpa using Nat.succ_lt_succ i.isLt
    have hi_lt : i.val < m' + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self _)
    have hsucc := partialSum_succ_eq_add_nu P i.val hi_lt hi1
    have hps_succ : P.partialSum i.succ = 2 * i.succ.val := hps_eq_two_mul i.succ
    have hps_cast : P.partialSum i.castSucc = 2 * i.castSucc.val := hps_eq_two_mul i.castSucc
    have hEq : 2 * (i.val + 1) = 2 * i.val + P.ν i.castSucc := by
      calc
        2 * (i.val + 1) = P.partialSum i.succ := by
          simpa [Fin.val_succ] using hps_succ.symm
        _ = P.partialSum i.castSucc + P.ν i.castSucc := hsucc
        _ = 2 * i.val + P.ν i.castSucc := by
          simpa [Fin.val_castSucc] using congrArg (fun t => t + P.ν i.castSucc) hps_cast
    have : P.ν i.castSucc = 2 := by
      omega
    simpa [Fin.val_succ, Fin.val_castSucc] using this
  have hnu_last : P.ν (Fin.last m') = 2 := by
    have hsum_univ : (∑ j : Fin (m' + 1), P.ν j) = 2 * (m' + 1) := by
      simpa [hS] using P.sum_ν
    rw [Fin.sum_univ_castSucc] at hsum_univ
    have hsum_castSucc : (∑ i : Fin m', P.ν i.castSucc) = m' * 2 := by
      calc
        (∑ i : Fin m', P.ν i.castSucc)
            = (∑ i : Fin m', 2) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                exact hnu_castSucc i
        _ = m' * 2 := by simp [Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]
    rw [hsum_castSucc] at hsum_univ
    omega
  have hnu_all_two : ∀ j : Fin (m' + 1), P.ν j = 2 := by
    intro j
    refine Fin.lastCases ?hLast ?hSucc j
    · exact hnu_last
    · intro i
      exact hnu_castSucc i
  intro j k
  simpa [hnu_all_two j, hnu_all_two k]

/-- Under the critical-line side condition, nontriviality forces
`weightsForFour` to be nonconstant. -/
private lemma weightsForFour_nonconst_of_nontrivial
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    ∃ i j : Fin m, weightsForFour P h_ge2j i ≠ weightsForFour P h_ge2j j := by
  by_contra h_const
  push_neg at h_const
  have hν_const : ∀ j k : Fin m, P.ν j = P.ν k :=
    nu_constant_of_uniform_weightsForFour hm P hS h_ge2j h_const
  rcases h_nontrivial with ⟨j, k, hjk⟩
  exact hjk (hν_const j k)

/-- CRT-periodicity dichotomy for the four-weight profile under critical-line
side conditions: either some prime quotient modulus is non-periodic, or all
prime quotient moduli are periodic. -/
theorem weightsForFour_prime_quotient_periodicity_dichotomy
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    (∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧
      ¬ Collatz.PrimeQuotientCRT.periodic_mod m (m / q) (weightsForFour P h_ge2j)) ∨
    (∀ q : ℕ, Nat.Prime q → q ∣ m →
      Collatz.PrimeQuotientCRT.periodic_mod m (m / q) (weightsForFour P h_ge2j)) := by
  have h_nonconst_w : ∃ i j : Fin m,
      weightsForFour P h_ge2j i ≠ weightsForFour P h_ge2j j :=
    weightsForFour_nonconst_of_nontrivial hm P h_nontrivial hS h_ge2j
  have hNeZero : NeZero m := ⟨Nat.ne_of_gt (by omega)⟩
  letI : NeZero m := hNeZero
  exact Collatz.PrimeQuotientCRT.exists_prime_nonconstant_slice_or_all_periodic
    m hm (weightsForFour P h_ge2j) h_nonconst_w

/-- Under prime-slice divisibility contraction, the non-periodic branch in the
prime-quotient dichotomy is impossible for nontrivial profiles on the critical
line with bounded four-weights. Hence all prime quotients must be periodic.

This theorem isolates the remaining non-squarefree blocker branch. -/
theorem all_prime_quotients_periodic_of_contract
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    ∀ q : ℕ, Nat.Prime q → q ∣ m →
      Collatz.PrimeQuotientCRT.periodic_mod m (m / q) (weightsForFour P h_ge2j) := by
  have h_dichotomy :=
    weightsForFour_prime_quotient_periodicity_dichotomy
      (m := m) hm P h_nontrivial hS h_ge2j
  rcases h_dichotomy with h_nonper | h_allper
  · rcases h_nonper with ⟨q, hq_prime, hq_dvd, h_not_per⟩
    let t : ℕ := m / q
    have hmqt : m = q * t := by
      exact (Nat.mul_div_cancel' hq_dvd).symm
    have ht_pos : 0 < t := by
      have hm_pos : 0 < m := by omega
      have hq_le_m : q ≤ m := Nat.le_of_dvd hm_pos hq_dvd
      exact Nat.div_pos hq_le_m hq_prime.pos
    have h_slice_nonconst :=
      Collatz.PrimeQuotientCRT.exists_nontrivial_slice_of_not_periodic
        m q t hmqt ht_pos (weightsForFour P h_ge2j) h_not_per
    rcases h_slice_nonconst with ⟨s, r₁, r₂, hne⟩
    letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
    letI : NeZero q := ⟨hq_prime.ne_zero⟩
    let SW : Fin q → ℕ :=
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)
    have h_slice_dvd :
        Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q SW := by
      simpa [SW] using h_contract q t hmqt s
    have h_bdd_SW : ∀ r : Fin q, SW r ≤ 3 := by
      intro r
      have hidx : s.val + t * r.val < m := by
        have h1 : s.val + t * r.val < t + t * r.val :=
          Nat.add_lt_add_right s.isLt (t * r.val)
        have h2 : t + t * r.val = t * (r.val + 1) := by
          calc
            t + t * r.val = t * r.val + t := by ac_rfl
            _ = t * r.val + t * 1 := by simp
            _ = t * (r.val + 1) := by
              simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        have h3 : r.val + 1 ≤ q := Nat.succ_le_of_lt r.isLt
        have h4 : t * (r.val + 1) ≤ t * q := Nat.mul_le_mul_left t h3
        have hlt : s.val + t * r.val < t * q := by
          exact lt_of_lt_of_le (by simpa [h2] using h1) (by simpa [h2] using h4)
        simpa [hmqt, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
      have hslice :
          SW r = weightsForFour P h_ge2j ⟨s.val + t * r.val, hidx⟩ := by
        simp [SW, Collatz.PrimeQuotientCRT.sliceFW, hidx]
      calc
        SW r = weightsForFour P h_ge2j ⟨s.val + t * r.val, hidx⟩ := hslice
        _ ≤ 3 := h_wbdd ⟨s.val + t * r.val, hidx⟩
    have h_nonconst_SW : ∃ a b : Fin q, SW a ≠ SW b := ⟨r₁, r₂, by simpa [SW] using hne⟩
    have h_uniform_SW : ∀ a b : Fin q, SW a = SW b :=
      Collatz.CyclotomicBridge.folded_weights_all_equal_prime
        (d := q) hq_prime SW 3 (by norm_num) h_bdd_SW h_slice_dvd
    rcases h_nonconst_SW with ⟨a, b, hab⟩
    exact False.elim (hab (h_uniform_SW a b))
  · exact h_allper

/-- If all prime-quotient moduli are periodic, then the weight function has a
proper period `t < m` (take `t = m / q` for any prime `q ∣ m`). -/
theorem exists_proper_period_of_all_prime_quotients_periodic
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2)
    (FW : Fin m → ℕ)
    (h_allper : ∀ q : ℕ, Nat.Prime q → q ∣ m →
      Collatz.PrimeQuotientCRT.periodic_mod m (m / q) FW) :
    ∃ t : ℕ, t < m ∧ Collatz.PrimeQuotientCRT.periodic_mod m t FW := by
  have hm_ne_one : m ≠ 1 := by omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hm_ne_one
  let t : ℕ := m / q
  have hm_pos : 0 < m := by omega
  have hq_gt_one : 1 < q := Nat.Prime.one_lt hq_prime
  have ht_lt_m : t < m := by
    simpa [t] using (Nat.div_lt_self hm_pos hq_gt_one)
  refine ⟨t, ht_lt_m, ?_⟩
  simpa [t] using h_allper q hq_prime hq_dvd

/-- Contractive prime-slice divisibility implies a proper period collapse for
`weightsForFour` in the remaining all-periodic branch. This theorem packages
the exact target needed for the final non-squarefree contradiction step. -/
theorem weightsForFour_proper_period_of_contract
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    ∃ t : ℕ, t < m ∧
      Collatz.PrimeQuotientCRT.periodic_mod m t (weightsForFour P h_ge2j) := by
  have h_allper :
      ∀ q : ℕ, Nat.Prime q → q ∣ m →
        Collatz.PrimeQuotientCRT.periodic_mod m (m / q) (weightsForFour P h_ge2j) :=
    all_prime_quotients_periodic_of_contract
      (m := m) hm P h_nontrivial hS h_ge2j h_wbdd h_contract
  exact exists_proper_period_of_all_prime_quotients_periodic
    (m := m) hm (weightsForFour P h_ge2j) h_allper

/-- Descent package for the remaining all-periodic branch:
under contractive prime-slice divisibility, `weightsForFour` admits a strict
proper period `t` that also divides `m`. -/
theorem weightsForFour_periodic_descent_data_of_contract
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    ∃ t : ℕ, t ∣ m ∧ 1 ≤ t ∧ t < m ∧
      Collatz.PrimeQuotientCRT.periodic_mod m t (weightsForFour P h_ge2j) := by
  have hm_ne_one : m ≠ 1 := by omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hm_ne_one
  let t : ℕ := m / q
  have hm_pos : 0 < m := by omega
  have hq_pos : 0 < q := hq_prime.pos
  have hq_gt_one : 1 < q := Nat.Prime.one_lt hq_prime
  have hmqt : m = q * t := by
    exact (Nat.mul_div_cancel' hq_dvd).symm
  have ht_pos : 0 < t := by
    have hq_le_m : q ≤ m := Nat.le_of_dvd hm_pos hq_dvd
    exact Nat.div_pos hq_le_m hq_pos
  have ht_lt : t < m := by
    simpa [t] using (Nat.div_lt_self hm_pos hq_gt_one)
  have hper : Collatz.PrimeQuotientCRT.periodic_mod m t (weightsForFour P h_ge2j) := by
    have h_allper :
        ∀ q : ℕ, Nat.Prime q → q ∣ m →
          Collatz.PrimeQuotientCRT.periodic_mod m (m / q) (weightsForFour P h_ge2j) :=
      all_prime_quotients_periodic_of_contract
        (m := m) hm P h_nontrivial hS h_ge2j h_wbdd h_contract
    simpa [t] using h_allper q hq_prime hq_dvd
  have ht_dvd : t ∣ m := ⟨q, by simpa [t, Nat.mul_comm] using hmqt⟩
  exact ⟨t, ht_dvd, Nat.succ_le_of_lt ht_pos, ht_lt, hper⟩

/-- Squarefree specialization: nontriviality on the critical line forces a
prime quotient modulus where `weightsForFour` is non-periodic. -/
theorem weightsForFour_exists_prime_nonperiodic_squarefree
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧
      ¬ Collatz.PrimeQuotientCRT.periodic_mod m (m / q) (weightsForFour P h_ge2j) := by
  have h_nonconst_w : ∃ i j : Fin m,
      weightsForFour P h_ge2j i ≠ weightsForFour P h_ge2j j :=
    weightsForFour_nonconst_of_nontrivial hm P h_nontrivial hS h_ge2j
  have hm1 : 1 < m := by omega
  have h_gcd :
      Collatz.PrimeQuotientCRT.gcdList (Collatz.PrimeQuotientCRT.primeQuotients m) = 1 :=
    Collatz.PrimeQuotientCRT.gcdList_primeQuotients_eq_one_of_squarefree hm1 hsf
  exact Collatz.PrimeQuotientCRT.exists_prime_not_periodic_of_nonconst
    m (weightsForFour P h_ge2j) h_nonconst_w h_gcd

/-- Squarefree branch, explicit nonconstant prime-quotient slice witness for
`weightsForFour`. This is the concrete witness object needed by slice-based
projection/CRT descent arguments. -/
theorem weightsForFour_exists_nonconstant_prime_quotient_slice_squarefree
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧
      ∃ t : ℕ, ∃ hmqt : m = q * t,
      ∃ s : Fin t, ∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂ := by
  rcases weightsForFour_exists_prime_nonperiodic_squarefree
      (m := m) hm hsf P h_nontrivial hS h_ge2j with
    ⟨q, hq_prime, hq_dvd, h_not_per⟩
  let t := m / q
  have hmqt : m = q * t := by
    exact (Nat.mul_div_cancel' hq_dvd).symm
  have ht_pos : 0 < t := by
    have hm_pos : 0 < m := by omega
    have hq_le_m : q ≤ m := Nat.le_of_dvd hm_pos hq_dvd
    exact Nat.div_pos hq_le_m hq_prime.pos
  have h_slice := Collatz.PrimeQuotientCRT.exists_nontrivial_slice_of_not_periodic
    m q t hmqt ht_pos (weightsForFour P h_ge2j) h_not_per
  rcases h_slice with ⟨s, r₁, r₂, hslice⟩
  refine ⟨q, hq_prime, hq_dvd, t, hmqt, s, r₁, r₂, ?_⟩
  simpa [hmqt] using hslice

/-- Step-3 packaging theorem (squarefree branch):
combine a nonconstant prime-quotient slice witness with the step-2 OKD
divisibility descent to obtain a prime-length replacement-data package.

The only remaining input is the local slice-to-profile conversion
(`h_slice_to_profile`), which upgrades a nonconstant divisible slice to a
`CycleProfile q` meeting the replacement side conditions. -/
theorem prime_projection_bridge_data_squarefree_from_slice_descent
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t) (r₁ r₂ : Fin q)
        (h_slice_nonconst :
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (weightsForFour P h_ge2j) r₂)
        (h_OKD_dvd :
          let FW : Fin q → ℕ :=
            fun r => ∑ j : Fin m,
              if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q FW),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  rcases h_realizable with ⟨_hD_pos, h_dvd⟩
  rcases weightsForFour_exists_nonconstant_prime_quotient_slice_squarefree
      (m := m) hm hsf P h_nontrivial hS h_ge2j with
    ⟨q, hq_prime, hq_dvd, t, hmqt, s, r₁, r₂, h_slice_nonconst⟩
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  letI : NeZero q := ⟨hq_prime.ne_zero⟩
  have hq_ge2 : q ≥ 2 := Nat.Prime.two_le hq_prime
  have hm_pos : 0 < m := by omega
  have h_OKD_dvd :
      let FW : Fin q → ℕ :=
        fun r => ∑ j : Fin m,
          if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q FW :=
    prime_projection_folded_OKD_divisibility
      (P := P) hq_ge2 hm_pos hq_dvd hS h_dvd h_ge2j
  rcases h_slice_to_profile q t hq_dvd hmqt s r₁ r₂ h_slice_nonconst h_OKD_dvd with
    ⟨P', hP'_nontrivial, hP'_realizable, hP'_S, hP'_pack⟩
  exact ⟨q, ⟨hq_prime⟩, ⟨hq_prime.ne_zero⟩, hq_dvd,
    P', hP'_nontrivial, hP'_realizable, hP'_S, hP'_pack⟩

/-- Squarefree constructive package alias for the prime-replacement bridge.
This is the no-axiom packaging route once `h_slice_to_profile` is supplied. -/
theorem prime_projection_crt_package_squarefree_from_slice
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t) (r₁ r₂ : Fin q)
        (h_slice_nonconst :
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (weightsForFour P h_ge2j) r₂)
        (h_OKD_dvd :
          let FW : Fin q → ℕ :=
            fun r => ∑ j : Fin m,
              if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q FW),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  exact prime_projection_bridge_data_squarefree_from_slice_descent
    hm hsf P h_nontrivial h_realizable hS h_ge2j h_slice_to_profile

/-- Squarefree constructive contradiction route:
if the local slice-to-profile converter is available, nontrivial realizability
is impossible without invoking `prime_projection_crt_on_divisor`. -/
theorem nontrivial_not_realizable_squarefree_from_slice
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t) (r₁ r₂ : Fin q)
        (h_slice_nonconst :
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (weightsForFour P h_ge2j) r₂)
        (h_OKD_dvd :
          let FW : Fin q → ℕ :=
            fun r => ∑ j : Fin m,
              if (j : ℕ) % q = r.val then weightsForFour P h_ge2j j else 0
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q FW),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  rcases prime_projection_crt_package_squarefree_from_slice
      (m := m) hm hsf P h_nontrivial h_realizable hS h_ge2j h_slice_to_profile with
    ⟨m', hPrime, hNeZero, _hmdvd, P', hP'⟩
  letI : Fact (Nat.Prime m') := hPrime
  letI : NeZero m' := hNeZero
  have hm' : m' ≥ 2 := Nat.Prime.two_le (Fact.out : Nat.Prime m')
  rcases hP' with ⟨hP'_nontrivial, hP'_realizable, hP'_S, h_ge2j', h_wbdd'⟩
  have h_dvd' : (cycleDenominator m' P'.S : ℤ) ∣ (P'.waveSum : ℤ) := hP'_realizable.2
  let w : Fin m' → ℕ := weightsForFour P' h_ge2j'
  let FW : Fin m' → ℕ := fun r => ∑ j : Fin m', if (j : ℕ) % m' = r.val then w j else 0
  have h_FW_def : ∀ r : Fin m', FW r = ∑ j : Fin m',
      if (j : ℕ) % m' = r.val then weightsForFour P' h_ge2j' j else 0 := by
    intro r
    rfl
  have h_bdd_FW : ∀ r : Fin m', FW r ≤ 3 := by
    intro r
    simpa [FW, w, folded_mod_self_eq] using h_wbdd' r
  have h_unif_FW : ∀ r s : Fin m', FW r = FW s :=
    prime_projection_rigidity
      (m := m') (q := m') (P := P') hm'
      (Nat.Prime.pos (Fact.out : Nat.Prime m')) (dvd_refl m')
      hP'_S h_dvd' h_ge2j' FW h_FW_def h_bdd_FW
  have h_unif_w : ∀ j k : Fin m', weightsForFour P' h_ge2j' j = weightsForFour P' h_ge2j' k := by
    intro j k
    simpa [FW, w, folded_mod_self_eq] using h_unif_FW j k
  have hν_const : ∀ j k : Fin m', P'.ν j = P'.ν k :=
    nu_constant_of_uniform_weightsForFour_prime
      (m := m') hm' P' hP'_S h_ge2j' h_unif_w
  rcases hP'_nontrivial with ⟨j, k, hjk⟩
  exact hjk (hν_const j k)

/-- Generic prime-slice extraction under a contraction hypothesis.
Given any witness of a nonconstant prime quotient slice, contraction provides
divisibility on that same slice. -/
theorem projected_divisibility_prime_slice_exists
    (m : ℕ) [NeZero m]
    (FW : Fin m → ℕ)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s FW))
    (h_nontrivial_slice_exists :
      ∃ (q t : ℕ) (hmqt : m = q * t),
        Nat.Prime q ∧ 0 < t ∧
          ∃ s : Fin t, ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s FW r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s FW r₂) :
    ∃ (q t : ℕ) (hmqt : m = q * t) (hq_prime : Nat.Prime q) (hq_nz : NeZero q),
      ∃ s : Fin t,
        (Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s FW)) ∧
        ∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s FW r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s FW r₂ := by
  rcases h_nontrivial_slice_exists with ⟨q, t, hmqt, hq_prime, _ht_pos, s, r₁, r₂, hne⟩
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  letI : NeZero q := ⟨hq_prime.ne_zero⟩
  refine ⟨q, t, hmqt, hq_prime, ⟨hq_prime.ne_zero⟩, s, ?_, r₁, r₂, hne⟩
  exact h_contract q t hmqt s

/-- Squarefree slice extraction under a contraction hypothesis:
if prime-quotient slices inherit divisibility (`h_contract`), then a
nonconstant divisible prime slice exists for `weightsForFour`. -/
theorem squarefree_nonconstant_divisible_prime_slice_of_contract
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧
      ∃ t : ℕ, ∃ hmqt : m = q * t,
      ∃ s : Fin t, ∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂ := by
  have h_nontrivial_slice_exists :
      ∃ (q t : ℕ) (hmqt : m = q * t),
        Nat.Prime q ∧ 0 < t ∧
          ∃ s : Fin t, ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂ := by
    rcases weightsForFour_exists_nonconstant_prime_quotient_slice_squarefree
        (m := m) hm hsf P h_nontrivial hS h_ge2j with
      ⟨q, hq_prime, _hq_dvd, t, hmqt, s, r₁, r₂, h_slice_nonconst⟩
    have ht_pos : 0 < t := by
      have hm_pos : 0 < m := by omega
      have hqt_pos : 0 < q * t := by simpa [hmqt] using hm_pos
      by_contra ht0
      have : q * t = 0 := by simpa [Nat.eq_zero_of_not_pos ht0]
      exact (Nat.ne_of_gt hqt_pos) this
    exact ⟨q, t, hmqt, hq_prime, ht_pos, s, r₁, r₂, h_slice_nonconst⟩
  rcases projected_divisibility_prime_slice_exists m (weightsForFour P h_ge2j)
      h_contract h_nontrivial_slice_exists with
    ⟨q, t, hmqt, hq_prime, _hq_nz, s, _h_slice_dvd, r₁, r₂, h_slice_nonconst⟩
  have hq_dvd : q ∣ m := by
    refine ⟨t, ?_⟩
    simpa [Nat.mul_comm] using hmqt
  exact ⟨q, hq_prime, hq_dvd, t, hmqt, s, r₁, r₂, h_slice_nonconst⟩

/-- Prime-divisor forward remainder contradiction (squarefree route):
if a nonconstant prime slice is forced and every prime slice inherits
`(4 - 3ζ_q) | balance`, then boundedness (`weightsForFour ≤ 3`) makes that
slice uniform by prime rigidity, contradiction. -/
theorem squarefree_slice_remainder_contradiction
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    False := by
  rcases squarefree_nonconstant_divisible_prime_slice_of_contract
      (m := m) hm hsf P h_nontrivial hS h_ge2j h_contract with
    ⟨q, hq_prime, _hq_dvd, t, hmqt, s, r₁, r₂, h_slice_nonconst⟩
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  letI : NeZero q := ⟨hq_prime.ne_zero⟩
  let SW : Fin q → ℕ := Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)
  have h_slice_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q SW := by
    simpa [SW] using h_contract q t hmqt s
  have h_bdd_SW : ∀ r : Fin q, SW r ≤ 3 := by
    intro r
    have hidx : s.val + t * r.val < m := by
      have h1 : s.val + t * r.val < t + t * r.val :=
        Nat.add_lt_add_right s.isLt (t * r.val)
      have h2 : t + t * r.val = t * (r.val + 1) := by
        calc
          t + t * r.val = t * r.val + t := by ac_rfl
          _ = t * r.val + t * 1 := by simp
          _ = t * (r.val + 1) := by
            simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h3 : r.val + 1 ≤ q := Nat.succ_le_of_lt r.isLt
      have h4 : t * (r.val + 1) ≤ t * q := Nat.mul_le_mul_left t h3
      have hlt : s.val + t * r.val < t * q := by
        exact lt_of_lt_of_le (by simpa [h2] using h1) (by simpa [h2] using h4)
      simpa [hmqt, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
    have hSW_eq :
        SW r = weightsForFour P h_ge2j ⟨s.val + t * r.val, hidx⟩ := by
      simp [SW, Collatz.PrimeQuotientCRT.sliceFW, hidx]
    calc
      SW r = weightsForFour P h_ge2j ⟨s.val + t * r.val, hidx⟩ := hSW_eq
      _ ≤ 3 := h_wbdd ⟨s.val + t * r.val, hidx⟩
  have h_uniform_SW : ∀ u v : Fin q, SW u = SW v :=
    Collatz.CyclotomicBridge.folded_weights_all_equal_prime
      (d := q) hq_prime SW 3 (by norm_num) h_bdd_SW h_slice_dvd
  have h_nonconst_SW : SW r₁ ≠ SW r₂ := by
    simpa [SW] using h_slice_nonconst
  exact h_nonconst_SW (h_uniform_SW r₁ r₂)

/-- Boundedness transfer: if `weightsForFour P ≤ 3`, every prime slice
`sliceFW` is also bounded by `3`. -/
lemma sliceFW_bdd_of_weightsForFour_bdd
    {m q t : ℕ} [NeZero m]
    (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (hmqt : m = q * t)
    (s : Fin t) :
    ∀ r : Fin q,
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r ≤ 3 := by
  intro r
  have hidx : s.val + t * r.val < m := by
    have h1 : s.val + t * r.val < t + t * r.val :=
      Nat.add_lt_add_right s.isLt (t * r.val)
    have h2 : t + t * r.val = t * (r.val + 1) := by
      calc
        t + t * r.val = t * r.val + t := by ac_rfl
        _ = t * r.val + t * 1 := by simp
        _ = t * (r.val + 1) := by
          simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h3 : r.val + 1 ≤ q := Nat.succ_le_of_lt r.isLt
    have h4 : t * (r.val + 1) ≤ t * q := Nat.mul_le_mul_left t h3
    have hlt : s.val + t * r.val < t * q := by
      exact lt_of_lt_of_le (by simpa [h2] using h1) (by simpa [h2] using h4)
    simpa [hmqt, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
  have hslice :
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r =
        weightsForFour P h_ge2j ⟨s.val + t * r.val, hidx⟩ := by
    simp [Collatz.PrimeQuotientCRT.sliceFW, hidx]
  calc
    Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r
        = weightsForFour P h_ge2j ⟨s.val + t * r.val, hidx⟩ := hslice
    _ ≤ 3 := h_wbdd ⟨s.val + t * r.val, hidx⟩

/-- Each prime-quotient slice entry coming from `weightsForFour` is a power of `2`.
This is the basic integrality shape needed for slice renormalization. -/
lemma sliceFW_is_two_power_of_weightsForFour
    {m q t : ℕ} [NeZero m]
    (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (hmqt : m = q * t)
    (s : Fin t) :
    ∀ r : Fin q, ∃ e : ℕ,
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r = 2 ^ e := by
  intro r
  have hidx : s.val + t * r.val < m := by
    have h1 : s.val + t * r.val < t + t * r.val :=
      Nat.add_lt_add_right s.isLt (t * r.val)
    have h2 : t + t * r.val = t * (r.val + 1) := by
      calc
        t + t * r.val = t * r.val + t := by ac_rfl
        _ = t * r.val + t * 1 := by simp
        _ = t * (r.val + 1) := by
          simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h3 : r.val + 1 ≤ q := Nat.succ_le_of_lt r.isLt
    have h4 : t * (r.val + 1) ≤ t * q := Nat.mul_le_mul_left t h3
    have hlt : s.val + t * r.val < t * q := by
      exact lt_of_lt_of_le (by simpa [h2] using h1) (by simpa [h2] using h4)
    simpa [hmqt, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
  refine ⟨P.partialSum ⟨s.val + t * r.val, hidx⟩ - 2 * (s.val + t * r.val), ?_⟩
  simp [Collatz.PrimeQuotientCRT.sliceFW, weightsForFour, hidx]

private lemma two_pow_le_three_cases (e : ℕ) (h : 2 ^ e ≤ 3) :
    e = 0 ∨ e = 1 := by
  by_cases h0 : e = 0
  · exact Or.inl h0
  · by_cases h1 : e = 1
    · exact Or.inr h1
    · have he2 : 2 ≤ e := by omega
      have hge4 : 4 ≤ 2 ^ e := by
        rcases Nat.exists_eq_add_of_le he2 with ⟨k, hk⟩
        rw [hk, Nat.pow_add]
        have hkpow : 1 ≤ 2 ^ k := by
          exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
        nlinarith
      omega

/-- A bounded (`≤ 3`) two-power slice entry is forced to be `1` or `2`.
This is the binary value lemma used in renormalized slice constructions. -/
lemma sliceFW_eq_one_or_two_of_bdd
    {m q t : ℕ} [NeZero m]
    (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (hmqt : m = q * t)
    (s : Fin t)
    (h_bdd : ∀ r : Fin q,
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r ≤ 3) :
    ∀ r : Fin q,
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r = 1 ∨
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r = 2 := by
  intro r
  rcases sliceFW_is_two_power_of_weightsForFour (P := P) h_ge2j hmqt s r with ⟨e, heq⟩
  have hpow_bdd : 2 ^ e ≤ 3 := by simpa [heq] using h_bdd r
  rcases two_pow_le_three_cases e hpow_bdd with h0 | h1
  · left
    simpa [heq, h0]
  · right
    simpa [heq, h1]

/-- Prime-slice integer remainder after rolling `m` forward to a prime quotient `q`.
This is the concrete "check the remainder" observable for the slice. -/
noncomputable def primeSliceEvalRemainder
    (q : ℕ) [NeZero q] (SW : Fin q → ℕ) : ℤ :=
  Collatz.CyclotomicBridge.evalSum43' q SW % ((4 : ℤ) ^ q - 3 ^ q)

/-- If the prime slice satisfies cyclotomic divisibility in `OKD q`,
its rolled-forward integer remainder is zero. -/
lemma primeSliceEvalRemainder_eq_zero_of_slice_dvd
    (q : ℕ) [NeZero q] [Fact (Nat.Prime q)]
    (SW : Fin q → ℕ)
    (h_slice_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q SW) :
    primeSliceEvalRemainder q SW = 0 := by
  unfold primeSliceEvalRemainder
  have h_dvd_int :
      ((4 : ℤ) ^ q - 3 ^ q) ∣ Collatz.CyclotomicBridge.evalSum43' q SW :=
    Collatz.CyclotomicBridge.divisibility_transfer_from_OKD_prime q
      (Fact.out : Nat.Prime q) SW h_slice_dvd
  exact Int.emod_eq_zero_of_dvd h_dvd_int

/-- If a prime slice is bounded by `3` and nonconstant, its rolled-forward
integer remainder is nonzero. -/
lemma primeSliceEvalRemainder_ne_zero_of_slice_nonconstant
    (q : ℕ) [NeZero q]
    (SW : Fin q → ℕ)
    (h_bdd : ∀ r : Fin q, SW r ≤ 3)
    (h_nonconst : ∃ r₁ r₂ : Fin q, SW r₁ ≠ SW r₂) :
    primeSliceEvalRemainder q SW ≠ 0 := by
  unfold primeSliceEvalRemainder
  have h_not_dvd :
      ¬(((4 : ℤ) ^ q - 3 ^ q) ∣ Collatz.CyclotomicBridge.evalSum43' q SW) :=
    Collatz.CyclotomicBridge.nonuniform_folded_weights_not_divisible q
      (Nat.pos_of_ne_zero (NeZero.ne q)) SW 3 (by norm_num) h_bdd h_nonconst
  intro hrem0
  have h_dvd : ((4 : ℤ) ^ q - 3 ^ q) ∣ Collatz.CyclotomicBridge.evalSum43' q SW :=
    Int.dvd_of_emod_eq_zero hrem0
  exact h_not_dvd h_dvd

/-- Forward-to-prime remainder contradiction on a concrete prime slice:
the same slice cannot be both divisible in `OKD q` and nonconstant under
the bounded four-weight window. -/
theorem prime_slice_remainder_contradiction
    (q : ℕ) [NeZero q] [Fact (Nat.Prime q)]
    (SW : Fin q → ℕ)
    (h_bdd : ∀ r : Fin q, SW r ≤ 3)
    (h_slice_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q SW)
    (h_nonconst : ∃ r₁ r₂ : Fin q, SW r₁ ≠ SW r₂) :
    False := by
  have h0 :
      primeSliceEvalRemainder q SW = 0 :=
    primeSliceEvalRemainder_eq_zero_of_slice_dvd q SW h_slice_dvd
  have hne0 :
      primeSliceEvalRemainder q SW ≠ 0 :=
    primeSliceEvalRemainder_ne_zero_of_slice_nonconstant q SW h_bdd h_nonconst
  exact hne0 h0

/-- Local roll-forward contradiction (no global contract hypothesis):
if one prime slice is both divisible in `OKD q` and nonconstant (under
the standard `weightsForFour ≤ 3` window), the profile is impossible. -/
theorem nontrivial_not_realizable_from_prime_slice_remainder
    {m q t : ℕ} [NeZero m] [Fact (Nat.Prime q)] [NeZero q]
    (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (hmqt : m = q * t)
    (s : Fin t)
    (h_slice_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
    (h_slice_nonconst :
      ∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂) :
    False := by
  let SW : Fin q → ℕ :=
    Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)
  have h_bdd_SW : ∀ r : Fin q, SW r ≤ 3 := by
    intro r
    simpa [SW] using sliceFW_bdd_of_weightsForFour_bdd
      (P := P) h_ge2j h_wbdd hmqt s r
  have h_slice_dvd' :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q SW := by
    simpa [SW] using h_slice_dvd
  have h_nonconst_SW : ∃ a b : Fin q, SW a ≠ SW b := by
    simpa [SW] using h_slice_nonconst
  exact prime_slice_remainder_contradiction q SW h_bdd_SW h_slice_dvd' h_nonconst_SW

/-- Profile-attached prime-offset slice witness.
This packages the "roll `m` forward to a prime quotient and inspect one offset"
view without changing `CycleProfile` globally. -/
structure PrimeOffsetSliceWitness
    {m : ℕ} [NeZero m] (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j) : Type where
  q : ℕ
  t : ℕ
  hmqt : m = q * t
  hq_prime : Nat.Prime q
  s : Fin t
  h_slice_dvd :
    letI : NeZero q := ⟨hq_prime.ne_zero⟩
    Collatz.CyclotomicBridge.fourSubThreeO q ∣
      Collatz.CyclotomicBridge.balanceSumO q
        (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))
  h_slice_nonconst :
    ∃ r₁ r₂ : Fin q,
      Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂

/-- One loop-step on offsets: `s ↦ s+1 (mod t)`. -/
def advanceOffset {t : ℕ} (s : Fin t) : Fin t :=
  ⟨(s.val + 1) % t, Nat.mod_lt _ (Nat.zero_lt_of_lt s.isLt)⟩

/-- Iterate the loop-step `L` times. -/
def iterateOffset {t : ℕ} (s : Fin t) : ℕ → Fin t
  | 0 => s
  | L + 1 => advanceOffset (iterateOffset s L)

/-- If the prime-slice witness is stable under one loop-step, it is stable
under any number of loops (induction on `L`). -/
theorem prime_offset_witness_iterate
    {m : ℕ} [NeZero m] (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (hmqt : m = q * t)
    (h_step :
      ∀ s : Fin t,
        (Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) ∧
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂) →
        (Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j))) ∧
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
            (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j) r₂))
    (s0 : Fin t)
    (h0 :
      (Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s0 (weightsForFour P h_ge2j))) ∧
      (∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s0 (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s0 (weightsForFour P h_ge2j) r₂)) :
    ∀ L : ℕ,
      (Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (iterateOffset s0 L)
            (weightsForFour P h_ge2j))) ∧
      (∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (iterateOffset s0 L)
          (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (iterateOffset s0 L)
            (weightsForFour P h_ge2j) r₂) := by
  intro L
  induction L with
  | zero =>
      simpa [iterateOffset] using h0
  | succ L ih =>
      simpa [iterateOffset] using h_step (iterateOffset s0 L) ih

/-- Build the one-step combined propagation rule from separate divisibility
and nonconst propagation rules. -/
theorem prime_offset_step_from_components
    {m : ℕ} [NeZero m] (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (hmqt : m = q * t)
    (h_step_dvd :
      ∀ s : Fin t,
        Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)) →
        Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j)))
    (h_step_nonconst :
      ∀ s : Fin t,
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂) →
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
            (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j) r₂)) :
    ∀ s : Fin t,
      (Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) ∧
      (∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂) →
      (Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
            (weightsForFour P h_ge2j))) ∧
      (∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
          (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
            (weightsForFour P h_ge2j) r₂) := by
  intro s hs
  exact ⟨h_step_dvd s hs.1, h_step_nonconst s hs.2⟩

/-- Loop induction using component one-step propagation rules. -/
theorem prime_offset_witness_iterate_from_components
    {m : ℕ} [NeZero m] (P : CycleProfile m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
    (hmqt : m = q * t)
    (h_step_dvd :
      ∀ s : Fin t,
        Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)) →
        Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j)))
    (h_step_nonconst :
      ∀ s : Fin t,
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂) →
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
            (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j) r₂))
    (s0 : Fin t)
    (h0 :
      (Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s0 (weightsForFour P h_ge2j))) ∧
      (∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s0 (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s0 (weightsForFour P h_ge2j) r₂)) :
    ∀ L : ℕ,
      (Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (iterateOffset s0 L)
            (weightsForFour P h_ge2j))) ∧
      (∃ r₁ r₂ : Fin q,
        Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (iterateOffset s0 L)
          (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (iterateOffset s0 L)
            (weightsForFour P h_ge2j) r₂) := by
  have h_step :
      ∀ s : Fin t,
        (Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) ∧
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂) →
        (Collatz.CyclotomicBridge.fourSubThreeO q ∣
          Collatz.CyclotomicBridge.balanceSumO q
            (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j))) ∧
        (∃ r₁ r₂ : Fin q,
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
            (weightsForFour P h_ge2j) r₁ ≠
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (advanceOffset s)
              (weightsForFour P h_ge2j) r₂) :=
    prime_offset_step_from_components
      (P := P) h_ge2j q t hmqt h_step_dvd h_step_nonconst
  exact prime_offset_witness_iterate
    (P := P) h_ge2j q t hmqt h_step s0 h0

/-- Offset-counter realizability transport:
if realizability holds at one offset and each offset-step preserves
realizability, then it holds along all iterates of `advanceOffset`. -/
theorem realizable_along_offset_counter
    {t q : ℕ}
    (Pq : Fin t → CycleProfile q)
    (s0 : Fin t)
    (h0 : (Pq s0).isRealizable)
    (hstep : ∀ s : Fin t, (Pq s).isRealizable → (Pq (advanceOffset s)).isRealizable) :
    ∀ L : ℕ, (Pq (iterateOffset s0 L)).isRealizable := by
  intro L
  induction L with
  | zero =>
      simpa [iterateOffset] using h0
  | succ L ih =>
      simpa [iterateOffset] using hstep (iterateOffset s0 L) ih

/-- Counter-style realizability induction over "advance length by one step".
If realizability holds at the base index and each extra-step check preserves
realizability, then all advanced indices are realizable. -/
theorem realizable_along_advance_counter
    (m : ℕ)
    (Q : ∀ L : ℕ, CycleProfile (m + L))
    (h0 : (Q 0).isRealizable)
    (hstep : ∀ L : ℕ, (Q L).isRealizable → (Q (L + 1)).isRealizable) :
    ∀ L : ℕ, (Q L).isRealizable := by
  intro L
  induction L with
  | zero =>
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h0
  | succ L ih =>
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep L ih

/-- Convert a profile-attached prime-offset witness into prime-replacement
bridge data, given a local slice-to-profile converter. -/
theorem prime_projection_bridge_data_of_offset_witness
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  let q := h_wit.q
  let t := h_wit.t
  have hq_prime : Nat.Prime q := by simpa [q] using h_wit.hq_prime
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  letI : NeZero q := ⟨hq_prime.ne_zero⟩
  have hmqt : m = q * t := by simpa [q, t] using h_wit.hmqt
  have hq_dvd : q ∣ m := ⟨t, hmqt⟩
  rcases h_slice_to_profile q t hq_dvd hmqt h_wit.s h_wit.h_slice_dvd h_wit.h_slice_nonconst with
    ⟨P', hP'_nontrivial, hP'_realizable, hP'_S, hP'_pack⟩
  exact ⟨q, ⟨hq_prime⟩, ⟨hq_prime.ne_zero⟩, hq_dvd,
    P', hP'_nontrivial, hP'_realizable, hP'_S, hP'_pack⟩

/-- Constructive replacement package for prime-projection/CRT:
if a profile-attached prime-offset witness is available, and a local
slice-to-profile converter is available, we can build the full prime package
without `prime_projection_crt_on_divisor`. -/
theorem prime_projection_crt_package_from_offset_witness
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  exact prime_projection_bridge_data_of_offset_witness
    (hm := hm) (P := P) h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile

/-- Squarefree nontrivial profiles are impossible from the prime-slice
roll-forward remainder check, assuming slice divisibility contraction. -/
theorem nontrivial_not_realizable_squarefree_via_remainder
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    False := by
  rcases squarefree_nonconstant_divisible_prime_slice_of_contract
      (m := m) hm hsf P h_nontrivial hS h_ge2j h_contract with
    ⟨q, hq_prime, _hq_dvd, t, hmqt, s, r₁, r₂, h_slice_nonconst⟩
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  letI : NeZero q := ⟨hq_prime.ne_zero⟩
  have h_slice_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)) := by
    simpa using h_contract q t hmqt s
  exact nontrivial_not_realizable_from_prime_slice_remainder
    (P := P) h_ge2j h_wbdd hmqt s h_slice_dvd ⟨r₁, r₂, h_slice_nonconst⟩

/-- Contract-only squarefree contradiction wrapper.
Unlike `nontrivial_not_realizable_squarefree_constructive`, this route does
not require a slice-to-profile converter. -/
theorem nontrivial_not_realizable_squarefree_contract_only
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j))) :
    False := by
  exact nontrivial_not_realizable_squarefree_via_remainder
    hm hsf P h_nontrivial hS h_ge2j h_wbdd h_contract

/-- Squarefree constructive bridge package in the slice-divisibility form.
This is the contractive version of the squarefree route. -/
theorem prime_projection_bridge_data_squarefree_from_contract
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t) (r₁ r₂ : Fin q)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  rcases h_realizable with ⟨_hD_pos, _h_dvd⟩
  rcases squarefree_nonconstant_divisible_prime_slice_of_contract
      (m := m) hm hsf P h_nontrivial hS h_ge2j h_contract with
    ⟨q, hq_prime, hq_dvd, t, hmqt, s, r₁, r₂, h_slice_nonconst⟩
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  letI : NeZero q := ⟨hq_prime.ne_zero⟩
  have h_slice_dvd :
      Collatz.CyclotomicBridge.fourSubThreeO q ∣
        Collatz.CyclotomicBridge.balanceSumO q
          (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)) :=
    h_contract q t hmqt s
  rcases h_slice_to_profile q t hq_dvd hmqt s r₁ r₂ h_slice_dvd h_slice_nonconst with
    ⟨P', hP'_nontrivial, hP'_realizable, hP'_S, hP'_pack⟩
  exact ⟨q, ⟨hq_prime⟩, ⟨hq_prime.ne_zero⟩, hq_dvd,
    P', hP'_nontrivial, hP'_realizable, hP'_S, hP'_pack⟩

/-- Constructive squarefree replacement package for the prime-projection bridge.
This avoids `prime_projection_crt_on_divisor` when both:
1. slice divisibility contraction is available, and
2. a slice-to-profile converter is available. -/
theorem prime_projection_crt_package_squarefree_constructive
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t) (r₁ r₂ : Fin q)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  exact prime_projection_bridge_data_squarefree_from_contract
    hm hsf P h_nontrivial h_realizable hS h_ge2j h_contract h_slice_to_profile

/-- Constructive squarefree contradiction route that entirely bypasses
`prime_projection_crt_on_divisor`. -/
theorem nontrivial_not_realizable_squarefree_constructive
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_contract :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q] (hmqt : m = q * t),
        ∀ s : Fin t,
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t) (r₁ r₂ : Fin q)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  rcases prime_projection_crt_package_squarefree_constructive
      hm hsf P h_nontrivial h_realizable hS h_ge2j h_contract h_slice_to_profile with
    ⟨m', hPrime, hNeZero, _hmdvd, P', hP'⟩
  letI : Fact (Nat.Prime m') := hPrime
  letI : NeZero m' := hNeZero
  have hm' : m' ≥ 2 := Nat.Prime.two_le (Fact.out : Nat.Prime m')
  rcases hP' with ⟨hP'_nontrivial, hP'_realizable, hP'_S, h_ge2j', h_wbdd'⟩
  have h_dvd' : (cycleDenominator m' P'.S : ℤ) ∣ (P'.waveSum : ℤ) := hP'_realizable.2
  let w : Fin m' → ℕ := weightsForFour P' h_ge2j'
  let FW : Fin m' → ℕ := fun r => ∑ j : Fin m', if (j : ℕ) % m' = r.val then w j else 0
  have h_FW_def : ∀ r : Fin m', FW r = ∑ j : Fin m',
      if (j : ℕ) % m' = r.val then weightsForFour P' h_ge2j' j else 0 := by
    intro r
    rfl
  have h_bdd_FW : ∀ r : Fin m', FW r ≤ 3 := by
    intro r
    simpa [FW, w, folded_mod_self_eq] using h_wbdd' r
  have h_unif_FW : ∀ r s : Fin m', FW r = FW s :=
    prime_projection_rigidity
      (m := m') (q := m') (P := P') hm'
      (Nat.Prime.pos (Fact.out : Nat.Prime m')) (dvd_refl m')
      hP'_S h_dvd' h_ge2j' FW h_FW_def h_bdd_FW
  have h_unif_w : ∀ j k : Fin m', weightsForFour P' h_ge2j' j = weightsForFour P' h_ge2j' k := by
    intro j k
    simpa [FW, w, folded_mod_self_eq] using h_unif_FW j k
  have hν_const : ∀ j k : Fin m', P'.ν j = P'.ν k :=
    nu_constant_of_uniform_weightsForFour_prime
      (m := m') hm' P' hP'_S h_ge2j' h_unif_w
  rcases hP'_nontrivial with ⟨j, k, hjk⟩
  exact hjk (hν_const j k)

/-- Axiom-free prime-step replacement with an explicit reflection hypothesis:
if equal folded profile-induced four-weights force equal `ν`, then `D ∣ W`
forces a constant valuation profile (prime-length case). -/
theorem divisibility_forces_constant_profile_prime_replacement
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3) :
    ∀ j k : Fin m, P.ν j = P.ν k := by
  have hm_pos : 0 < m := Nat.Prime.pos Fact.out
  let w : Fin m → ℕ := weightsForFour P h_ge2j
  let FW : Fin m → ℕ := fun r => ∑ j : Fin m, if (j : ℕ) % m = r.val then w j else 0
  have h_FW_def : ∀ r : Fin m, FW r = ∑ j : Fin m, if (j : ℕ) % m = r.val then w j else 0 := by
    intro r
    rfl
  have h_FW_eq : FW = w := folded_mod_self_eq w
  have h_bdd_FW : ∀ r : Fin m, FW r ≤ 3 := by
    intro r
    simpa [h_FW_eq, w] using h_wbdd r
  have h_unif_FW :
      ∀ r s : Fin m, FW r = FW s :=
    cyclotomic_rigidity_replacement_prime
      (P := P) (d := m) hm hm_pos (dvd_refl m) hS h_dvd h_ge2j FW h_FW_def
      3 (by norm_num) h_bdd_FW
  have h_unif_w : ∀ r s : Fin m, w r = w s := by
    intro r s
    simpa [h_FW_eq] using h_unif_FW r s
  exact nu_constant_of_uniform_weightsForFour_prime hm P hS h_ge2j
    (by
      intro j k
      simpa [w] using h_unif_w j k)

/-- Prime projection rigidity at the self modulus (`q = m`):
under the prime replacement hypotheses, `weightsForFour` is uniform. -/
theorem prime_projection_rigidity_self_uniform_weightsForFour
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3) :
    ∀ j k : Fin m, weightsForFour P h_ge2j j = weightsForFour P h_ge2j k := by
  have hm_pos : 0 < m := Nat.Prime.pos Fact.out
  let w : Fin m → ℕ := weightsForFour P h_ge2j
  let FW : Fin m → ℕ := fun r => ∑ j : Fin m, if (j : ℕ) % m = r.val then w j else 0
  have h_FW_def : ∀ r : Fin m, FW r = ∑ j : Fin m, if (j : ℕ) % m = r.val then w j else 0 := by
    intro r
    rfl
  have h_FW_eq : FW = w := folded_mod_self_eq w
  have h_bdd_FW : ∀ r : Fin m, FW r ≤ 3 := by
    intro r
    simpa [h_FW_eq, w] using h_wbdd r
  have h_unif_FW :
      ∀ r s : Fin m, FW r = FW s :=
    prime_projection_rigidity (m := m) (q := m) (P := P)
      hm hm_pos (dvd_refl m) hS h_dvd h_ge2j FW h_FW_def h_bdd_FW
  intro j k
  simpa [h_FW_eq, w] using h_unif_FW j k

/-- Prime-length rigidity corollary via prime projection:
`D ∣ W` forces the valuation profile to be constant (under the standard
prime replacement side conditions). -/
theorem prime_projection_rigidity_implies_nu_constant_prime
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (hS : P.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ))
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3) :
    ∀ j k : Fin m, P.ν j = P.ν k := by
  have h_unif_w :
      ∀ j k : Fin m, weightsForFour P h_ge2j j = weightsForFour P h_ge2j k :=
    prime_projection_rigidity_self_uniform_weightsForFour
      hm P hS h_dvd h_ge2j h_wbdd
  exact nu_constant_of_uniform_weightsForFour_prime hm P hS h_ge2j h_unif_w

/-- Axiom-free nontriviality contradiction in the prime-length replacement regime. -/
theorem nontrivial_not_realizable_prime_replacement
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3) :
    False := by
  have h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ) := h_realizable.2
  have h_all_eq :
      ∀ j k : Fin m, P.ν j = P.ν k :=
    divisibility_forces_constant_profile_prime_replacement hm P h_dvd hS h_ge2j h_wbdd
  rcases h_nontrivial with ⟨j, k, hjk⟩
  exact hjk (h_all_eq j k)

/-- Constructive contradiction route from the offset witness bridge.
This bypasses `prime_projection_crt_on_divisor` when the two local bridge
ingredients are supplied. -/
theorem nontrivial_not_realizable_via_offset_witness_bridge
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  rcases prime_projection_crt_package_from_offset_witness
      (hm := hm) (P := P) h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile with
    ⟨m', hPrime, hNeZero, _hmdvd, P', hP'⟩
  letI : Fact (Nat.Prime m') := hPrime
  letI : NeZero m' := hNeZero
  have hm' : m' ≥ 2 := Nat.Prime.two_le (Fact.out : Nat.Prime m')
  rcases hP' with ⟨hP'_nontrivial, hP'_realizable, hP'_S, h_ge2j', h_wbdd'⟩
  exact nontrivial_not_realizable_prime_replacement
    hm' P' hP'_nontrivial hP'_realizable hP'_S h_ge2j' h_wbdd'

/-- Residue-class projection of `ν` from length `m` to length `m'` by summing
entries with the same index modulo `m'`. -/
noncomputable def residueProjectedNu
    {m m' : ℕ} (P : CycleProfile m) : Fin m' → ℕ :=
  fun r => ∑ j : Fin m, if (j : ℕ) % m' = r.val then P.ν j else 0

private lemma residueProjectedNu_pos
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m) :
    ∀ r : Fin m', residueProjectedNu P r ≥ 1 := by
  intro r
  have hm_pos : 0 < m := by omega
  have hm'_le_m : m' ≤ m := Nat.le_of_dvd hm_pos hmdvd
  let j0 : Fin m := ⟨r.val, lt_of_lt_of_le r.isLt hm'_le_m⟩
  have h_j0_mod : (j0 : ℕ) % m' = r.val := by
    simpa [j0] using (Nat.mod_eq_of_lt r.isLt)
  unfold residueProjectedNu
  calc
    (∑ j : Fin m, if (j : ℕ) % m' = r.val then P.ν j else 0)
        ≥ (if (j0 : ℕ) % m' = r.val then P.ν j0 else 0) := by
          let f : Fin m → ℕ := fun j =>
            if (j : ℕ) % m' = r.val then P.ν j else 0
          have hsingle : f j0 ≤ ∑ j : Fin m, f j :=
            Finset.single_le_sum
              (fun i _ => Nat.zero_le (f i))
              (by exact Finset.mem_univ j0)
          simpa [f] using hsingle
    _ = P.ν j0 := by simp [h_j0_mod]
    _ ≥ 1 := P.ν_pos j0

/-- Concrete residue projection to a profile of length `m'`.
This is a fully constructive projection object (no axioms). -/
noncomputable def residueProjectedProfile
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m) : CycleProfile m' where
  ν := residueProjectedNu P
  ν_pos := residueProjectedNu_pos hm P hmdvd
  S := ∑ r : Fin m', residueProjectedNu P r
  sum_ν := rfl

lemma residueProjectedProfile_S_ge_length
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m) :
    m' ≤ (residueProjectedProfile hm P hmdvd).S := by
  let P' : CycleProfile m' := residueProjectedProfile hm P hmdvd
  calc
    m' = ∑ _r : Fin m', (1 : ℕ) := by simp
    _ ≤ ∑ r : Fin m', P'.ν r := by
      exact Finset.sum_le_sum (fun r _ => P'.ν_pos r)
    _ = P'.S := P'.sum_ν

private lemma sum_residue_indicator
    {m m' : ℕ} (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (j : Fin m) :
    (∑ r : Fin m', if (j : ℕ) % m' = r.val then P.ν j else 0) = P.ν j := by
  classical
  have hm'_pos : 0 < m' := Nat.Prime.pos (Fact.out : Nat.Prime m')
  let r0 : Fin m' := ⟨(j : ℕ) % m', Nat.mod_lt _ hm'_pos⟩
  have hr0 : (j : ℕ) % m' = r0.val := by simp [r0]
  have hmod : ∀ r : Fin m', ((j : ℕ) % m' = r.val) ↔ r = r0 := by
    intro r
    constructor
    · intro h
      apply Fin.ext
      calc
        r.val = (j : ℕ) % m' := h.symm
        _ = r0.val := hr0
    · intro h
      simpa [h] using hr0
  calc
    (∑ r : Fin m', if (j : ℕ) % m' = r.val then P.ν j else 0)
        = ∑ r : Fin m', if r = r0 then P.ν j else 0 := by
            refine Finset.sum_congr rfl ?_
            intro r _
            simp [hmod r]
    _ = P.ν j := by
        simpa using (Finset.sum_ite_eq' (s := Finset.univ) (a := r0) (b := fun _ : Fin m' => P.ν j))

/-- The residue projection preserves the total valuation sum `S`. -/
lemma residueProjectedProfile_S_eq
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m) :
    (residueProjectedProfile hm P hmdvd).S = P.S := by
  unfold residueProjectedProfile
  simp [residueProjectedNu, Finset.sum_comm, sum_residue_indicator, P.sum_ν]

/-- The residue projection keeps the total valuation sum `S`.
So if the projected profile sits on the critical line `S' = 2*m'`, then the
original profile must satisfy `S = 2*m'` as well. -/
lemma residueProjectedProfile_criticalLine_lifts
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m)
    (hS' : (residueProjectedProfile hm P hmdvd).S = 2 * m') :
    P.S = 2 * m' := by
  calc
    P.S = (residueProjectedProfile hm P hmdvd).S := by
      symm
      exact residueProjectedProfile_S_eq (m := m) (m' := m') hm P hmdvd
    _ = 2 * m' := hS'

/-- In the critical-line regime `P.S = 2*m`, a residue-sum projection to a
proper divisor cannot itself land on `S' = 2*m'` unless `m' = m`.
This isolates why CRT/quotient-descent is needed beyond raw residue summation. -/
lemma residueProjectedProfile_criticalLine_forces_same_length
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m)
    (hS : P.S = 2 * m)
    (hS' : (residueProjectedProfile hm P hmdvd).S = 2 * m') :
    m = m' := by
  have h_from_proj : P.S = 2 * m' :=
    residueProjectedProfile_criticalLine_lifts (m := m) (m' := m') hm P hmdvd hS'
  rw [hS] at h_from_proj
  omega

lemma residueProjectedNu_self
    {m : ℕ} (P : CycleProfile m) :
    residueProjectedNu (m' := m) P = P.ν := by
  simpa [residueProjectedNu] using folded_mod_self_eq (m := m) P.ν

lemma residueProjectedProfile_self_nu
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m] :
    (residueProjectedProfile (m' := m) hm P (dvd_refl m)).ν = P.ν := by
  simpa [residueProjectedProfile, residueProjectedNu_self]

lemma residueProjectedProfile_self_S
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m] :
    (residueProjectedProfile (m' := m) hm P (dvd_refl m)).S = P.S := by
  exact residueProjectedProfile_S_eq (m := m) (m' := m) hm P (dvd_refl m)

lemma residueProjectedProfile_self_isNontrivial
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m]
    (h_nontrivial : P.isNontrivial) :
    (residueProjectedProfile (m' := m) hm P (dvd_refl m)).isNontrivial := by
  rcases h_nontrivial with ⟨j, k, hjk⟩
  refine ⟨j, k, ?_⟩
  simpa [residueProjectedProfile_self_nu (hm := hm) (P := P)] using hjk

lemma residueProjectedProfile_self_partialSum
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m] :
    (residueProjectedProfile (m' := m) hm P (dvd_refl m)).partialSum = P.partialSum := by
  funext j
  unfold CycleProfile.partialSum
  simp [residueProjectedProfile_self_nu (hm := hm) (P := P)]

lemma residueProjectedProfile_self_waveSum
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m] :
    (residueProjectedProfile (m' := m) hm P (dvd_refl m)).waveSum = P.waveSum := by
  unfold CycleProfile.waveSum
  simp [residueProjectedProfile_self_partialSum (hm := hm) (P := P)]

lemma residueProjectedProfile_self_isRealizable
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m]
    (h_realizable : P.isRealizable) :
    (residueProjectedProfile (m' := m) hm P (dvd_refl m)).isRealizable := by
  rcases h_realizable with ⟨hD_pos, hD_dvd⟩
  refine ⟨?_, ?_⟩
  · simpa [residueProjectedProfile_self_S (hm := hm) (P := P)] using hD_pos
  · simpa [residueProjectedProfile_self_S (hm := hm) (P := P),
      residueProjectedProfile_self_waveSum (hm := hm) (P := P)] using hD_dvd

/-- Single CRT-on-divisor projection primitive:
for a chosen prime divisor `m' ∣ m`, extract projected prime-length profile
data already upgraded with the critical-line and weight bounds. -/
def PrimeProjectionCRTData
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable) : Prop :=
  ∃ P' : CycleProfile m',
    P'.isNontrivial ∧
    P'.isRealizable ∧
    P'.S = 2 * m' ∧
    (∃ h_ge2j : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
      ∀ j : Fin m', weightsForFour P' h_ge2j j ≤ 3)

/-- Side-condition package used by the prime-length constructive replacement
route (`m' = m`). -/
structure PrimeReplacementSideConditions
    {m : ℕ} (P : CycleProfile m) : Prop where
  hS : P.S = 2 * m
  h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j
  h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3

/-- Full CRT-data package is constructively available in the self-prime case
once the prime-replacement side conditions are provided explicitly. -/
theorem prime_projection_crt_data_self_of_side_conditions
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m]
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForFour P h_ge2j j ≤ 3) :
    PrimeProjectionCRTData (m := m) (m' := m) hm P (dvd_refl m) h_nontrivial h_realizable := by
  refine ⟨residueProjectedProfile (m' := m) hm P (dvd_refl m), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact residueProjectedProfile_self_isNontrivial (hm := hm) (P := P) h_nontrivial
  · exact residueProjectedProfile_self_isRealizable (hm := hm) (P := P) h_realizable
  · simpa [residueProjectedProfile_self_S (hm := hm) (P := P)] using hS
  · refine ⟨(fun j => by
      simpa [residueProjectedProfile_self_partialSum (hm := hm) (P := P)] using h_ge2j j), ?_⟩
    intro j
    simpa [weightsForFour, residueProjectedProfile_self_partialSum (hm := hm) (P := P)]
      using h_wbdd j

/-- Packaged-side-condition variant of the constructive prime self-case bridge. -/
theorem prime_projection_crt_data_self_of_pack
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m]
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (hpack : PrimeReplacementSideConditions P) :
    PrimeProjectionCRTData (m := m) (m' := m) hm P (dvd_refl m) h_nontrivial h_realizable := by
  exact prime_projection_crt_data_self_of_side_conditions
    (hm := hm) (P := P) h_nontrivial h_realizable
    hpack.hS hpack.h_ge2j hpack.h_wbdd

/-- Constructor helper: if explicit projected data is available,
it directly discharges the CRT-on-divisor package. -/
theorem prime_projection_crt_on_divisor_from_data
    {m m' : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m')] [NeZero m']
    (hmdvd : m' ∣ m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (hproj : PrimeProjectionCRTData hm P hmdvd h_nontrivial h_realizable) :
    ∃ P' : CycleProfile m',
      P'.isNontrivial ∧
      P'.isRealizable ∧
      P'.S = 2 * m' ∧
      (∃ h_ge2j : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
        ∀ j : Fin m', weightsForFour P' h_ge2j j ≤ 3) :=
  hproj

/-- If `m ∣ S`, write `S = q*m`; then `D = (2^q)^m - 3^m`, so each
`Φ_d(2^q,3)` with `d ∣ m` divides `D`. -/
lemma cyclotomicBivar_dvd_cycleDenominator_of_m_dvd_S
    {m d : ℕ} (P : CycleProfile m)
    (hm_pos : 0 < m)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m)
    (hSm : m ∣ P.S) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d ((2 : ℤ) ^ (P.S / m)) 3 : ℤ) ∣
      cycleDenominator m P.S := by
  obtain ⟨q, hq⟩ := hSm
  have hq' : P.S = q * m := by
    simpa [Nat.mul_comm] using hq
  rw [hq', cycleDenominator]
  have hqm_div : (q * m) / m = q := by
    simpa [Nat.mul_comm] using (Nat.mul_div_right q hm_pos)
  rw [hqm_div]
  rw [pow_mul]
  exact Collatz.CyclotomicBridge.cyclotomicBivar_dvd_pow_sub_general_xy
    ((2 : ℤ) ^ q) 3 hd_pos hd_dvd

/-- Divisibility transfer to `W` in the `m ∣ S` setting. -/
lemma cyclotomicBivar_dvd_waveSum_of_m_dvd_S
    {m d : ℕ} (P : CycleProfile m)
    (hm_pos : 0 < m)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m)
    (hSm : m ∣ P.S)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d ((2 : ℤ) ^ (P.S / m)) 3 : ℤ) ∣
      (P.waveSum : ℤ) := by
  exact divisor_of_cycleDenominator_dvd_waveSum P _
    (cyclotomicBivar_dvd_cycleDenominator_of_m_dvd_S P hm_pos hd_pos hd_dvd hSm)
    h_dvd

/-- Same packaged divisibility, but explicitly bridged through an irrational
profile carrying the same `ν,S` data. -/
lemma cyclotomicBivar_dvd_waveSum_via_profile_bridge_of_S_eq_two_mul
    {m d : ℕ} (P : CycleProfile m) (Q : IrrationalCycleProfile m)
    (hcompat : IrrationalCycleProfile.Compatible P Q)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m)
    (hS_irr : Q.S = 2 * m)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d 4 3 : ℤ) ∣ (P.waveSum : ℤ) := by
  have hS_int : P.S = 2 * m := by
    calc
      P.S = Q.S := IrrationalCycleProfile.compatible_S_eq hcompat
      _ = 2 * m := hS_irr
  exact cyclotomicBivar_dvd_waveSum_of_S_eq_two_mul P hd_pos hd_dvd hS_int h_dvd

/-- `m ∣ S` version, explicitly bridged through an irrational profile carrying
the same discrete cycle data. -/
lemma cyclotomicBivar_dvd_waveSum_via_profile_bridge_of_m_dvd_S
    {m d : ℕ} (P : CycleProfile m) (Q : IrrationalCycleProfile m)
    (hcompat : IrrationalCycleProfile.Compatible P Q)
    (hm_pos : 0 < m)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m)
    (hSm_irr : m ∣ Q.S)
    (h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)) :
    (Collatz.CyclotomicBridge.cyclotomicBivar d ((2 : ℤ) ^ (P.S / m)) 3 : ℤ) ∣
      (P.waveSum : ℤ) := by
  have hSm_int : m ∣ P.S := by
    rw [IrrationalCycleProfile.compatible_S_eq hcompat]
    exact hSm_irr
  exact cyclotomicBivar_dvd_waveSum_of_m_dvd_S P hm_pos hd_pos hd_dvd hSm_int h_dvd


/-! ## Orbit infrastructure -/

/-- W = n₀ · D from A + B = n₀ · 2^S. -/
private lemma orbit_gives_W_eq {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    (n₀ : ℤ) (hAB_eq : termA m n₀ + termB P = n₀ * 2 ^ P.S) :
    (P.waveSum : ℤ) = n₀ * cycleDenominator m P.S := by
  have := E_eq_A_plus_B hm P n₀
  unfold cycleDenominator; linarith

/-- D is odd. -/
private lemma cycleDenominator_odd {m S : ℕ} (hD_pos : cycleDenominator m S > 0) :
    ¬(2 : ℤ) ∣ cycleDenominator m S := by
  unfold cycleDenominator; intro ⟨k, hk⟩
  have h3_odd : ¬(2 : ℤ) ∣ 3 ^ m := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl,
      ← Int.natCast_pow, Int.natCast_dvd_natCast]
    exact fun h => by have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 2) h; omega
  have hS_pos : S ≥ 1 := by
    by_contra h; push_neg at h; interval_cases S
    unfold cycleDenominator at hD_pos; simp at hD_pos
    have : (3 : ℤ) ^ m ≥ 1 := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 3); linarith
  have h2_dvd_2S : (2 : ℤ) ∣ 2 ^ S := dvd_pow_self 2 (by omega)
  obtain ⟨j, hj⟩ := h2_dvd_2S
  exact h3_odd ⟨j - k, by linarith⟩

/-- W is odd. -/
private lemma waveSum_odd {m : ℕ} (hm : m ≥ 1) (P : CycleProfile m) :
    ¬(2 : ℤ) ∣ (P.waveSum : ℤ) := by
  intro ⟨q, hq⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold CycleProfile.waveSum at hq; push_cast at hq
  rw [Fin.sum_univ_succ] at hq
  have h_ps0 : P.partialSum (0 : Fin (m' + 1)) = 0 :=
    partialSum_zero (by omega) P
  rw [h_ps0, pow_zero, mul_one] at hq
  simp only [Fin.val_zero, Nat.sub_zero] at hq
  set rest := ∑ i : Fin m', (3 : ℤ) ^ (m' - (i.succ : Fin (m' + 1)).val) *
      2 ^ P.partialSum i.succ
  have h_rest_even : (2 : ℤ) ∣ rest := by
    apply Finset.dvd_sum; intro j _
    apply dvd_mul_of_dvd_right; apply dvd_pow_self 2
    have hps_ge : P.partialSum (Fin.succ j) ≥ P.ν ⟨0, by omega⟩ := by
      unfold CycleProfile.partialSum
      apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
      exact Nat.succ_pos j.val
    have := P.ν_pos ⟨0, by omega⟩; omega
  obtain ⟨r, hr⟩ := h_rest_even
  have h3_odd : ¬(2 : ℤ) ∣ (3 : ℤ) ^ m' := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl,
      ← Int.natCast_pow, Int.natCast_dvd_natCast]
    exact fun h => by have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 2) h; omega
  exact h3_odd ⟨q - r, by linarith⟩

/-- Legacy control package in quotient-base form.
`q` is explicit (`q = S/m`), so this is compatible with the intended
general `2/3`-adic refactor even though the current closure still routes
through the `x = 4` evaluator. -/
private structure LegacyQuotientWeightControl {m : ℕ} (P : CycleProfile m) : Type where
  q : ℕ
  h_qdef : q = P.S / m
  hSm : m ∣ P.S
  h_geqj : ∀ j : Fin m, q * j.val ≤ P.partialSum j
  h_wbdd : ∀ j : Fin m, weightsForBase P q h_geqj j ≤ 3
  h_base_four : ((2 : ℤ) ^ q) = 4

private lemma prime_side_conditions_of_legacy_control
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    (h_ctrl : LegacyQuotientWeightControl P) :
    PrimeReplacementSideConditions P := by
  have hm_pos : 0 < m := by omega
  have h_q_nat : (2 : ℕ) ^ h_ctrl.q = 4 := by
    exact_mod_cast h_ctrl.h_base_four
  have hq_eq_two : h_ctrl.q = 2 := by
    have hpow : (2 : ℕ) ^ h_ctrl.q = (2 : ℕ) ^ 2 := by simpa using h_q_nat
    exact Nat.pow_right_injective (a := 2) (by decide : 2 ≤ 2) hpow
  have hS_eq : P.S = 2 * m := by
    rcases h_ctrl.hSm with ⟨t, ht⟩
    have ht' : P.S = t * m := by simpa [Nat.mul_comm] using ht
    have hdiv : P.S / m = t := by
      rw [ht']
      simpa [Nat.mul_comm] using (Nat.mul_div_right t hm_pos)
    have ht_two : t = 2 := by
      have hqt : h_ctrl.q = t := by rw [h_ctrl.h_qdef, hdiv]
      exact hqt.symm.trans hq_eq_two
    rw [ht', ht_two]
  refine ⟨hS_eq, ?_, ?_⟩
  · intro j
    simpa [hq_eq_two] using h_ctrl.h_geqj j
  · intro j
    simpa [hq_eq_two, weightsForBase, weightsForFour] using h_ctrl.h_wbdd j

private theorem prime_projection_crt_data_self_of_legacy_control
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    [Fact (Nat.Prime m)] [NeZero m]
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ctrl : LegacyQuotientWeightControl P) :
    PrimeProjectionCRTData (m := m) (m' := m) hm P (dvd_refl m) h_nontrivial h_realizable := by
  exact prime_projection_crt_data_self_of_pack
    (hm := hm) (P := P) h_nontrivial h_realizable
    (prime_side_conditions_of_legacy_control hm P h_ctrl)

/-- Legacy `q = 2` closure block, factored out:
from `D ∣ W` plus the `S=2m`/partial-sum/weight bounds side conditions,
derive profile constancy and contradict nontriviality. -/
private theorem contradiction_from_legacy_quotient_weight_control {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (q : ℕ)
    (h_qdef : q = P.S / m)
    (hSm : m ∣ P.S)
    (h_geqj : ∀ j : Fin m, q * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, weightsForBase P q h_geqj j ≤ 3)
    (h_base_four : ((2 : ℤ) ^ q) = 4)
    (h_eval_dvd : ((4 : ℤ) ^ m - 3 ^ m) ∣
      Collatz.CyclotomicBridge.evalSum43' m (weightsForBase P q h_geqj)) : False := by
  have hm_pos : 0 < m := by omega
  have h_q_nat : (2 : ℕ) ^ q = 4 := by
    exact_mod_cast h_base_four
  have hq_eq_two : q = 2 := by
    have hpow : (2 : ℕ) ^ q = (2 : ℕ) ^ 2 := by simpa using h_q_nat
    exact Nat.pow_right_injective (a := 2) (by decide : 2 ≤ 2) hpow
  have hS_eq : P.S = 2 * m := by
    rcases hSm with ⟨t, ht⟩
    have ht' : P.S = t * m := by simpa [Nat.mul_comm] using ht
    have hdiv : P.S / m = t := by
      rw [ht']
      simpa [Nat.mul_comm] using (Nat.mul_div_right t hm_pos)
    have ht_two : t = 2 := by
      have hqt : q = t := by rw [h_qdef, hdiv]
      exact hqt.symm.trans hq_eq_two
    rw [ht', ht_two]
  -- Specialize quotient-base weights to the `q=2` evaluator.
  let w := weightsForBase P q h_geqj
  have h_eval_dvd' : ((4 : ℤ) ^ m - 3 ^ m) ∣ Collatz.CyclotomicBridge.evalSum43' m w := by
    simpa [w] using h_eval_dvd
  have h_wbdd_base : ∀ j : Fin m, w j ≤ 3 := by
    intro j
    simpa [w] using h_wbdd j
  -- 4-adic cascade: weights ≤ 3 + divisibility → all weights equal (ANY m).
  have h_unif : ∀ r s : Fin m, w r = w s :=
    Collatz.CyclotomicBridge.folded_weights_all_equal_from_int_dvd m (by omega)
      w 3 (by norm_num) h_wbdd_base h_eval_dvd'
  -- Uniform weights → all ν = 2
  have hw0 : w (⟨0, hm_pos⟩ : Fin m) = 1 := by
    simpa [w, hq_eq_two, weightsForBase] using
      congrArg (fun t => (2 : ℕ) ^ t) (partialSum_zero hm_pos P)
  have hw1 : ∀ j : Fin m, w j = 1 := fun j => by
    have := h_unif j ⟨0, hm_pos⟩; rw [hw0] at this; exact this
  have h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j := by
    intro j
    simpa [hq_eq_two] using h_geqj j
  have hps_eq : ∀ j : Fin m, P.partialSum j = 2 * j.val := by
    intro j
    have hpow : 2 ^ (P.partialSum j - 2 * j.val) = 1 := by
      simpa [w, hq_eq_two, weightsForBase] using hw1 j
    have hsub0 : P.partialSum j - 2 * j.val = 0 :=
      Nat.pow_right_injective (a := 2) (by decide : 2 ≤ 2) (by simpa using hpow)
    exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hsub0) (h_ge2j j)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hnu_castSucc : ∀ i : Fin m', P.ν i.castSucc = 2 := by
    intro i
    have hi1 : i.castSucc.val + 1 < m' + 1 := by simp
    have hi_lt : i.val < m' + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self _)
    have hsucc := partialSum_succ_eq_add_nu P i.val hi_lt hi1
    have hps_succ := hps_eq ⟨i.val + 1, hi1⟩
    have hps_cast := hps_eq i.castSucc
    have hEq : 2 * (i.val + 1) = 2 * i.val + P.ν i.castSucc := by
      calc
        2 * (i.val + 1) = P.partialSum ⟨i.val + 1, hi1⟩ := by
          simpa [Fin.val_mk] using hps_succ.symm
        _ = P.partialSum ⟨i.val, hi_lt⟩ + P.ν ⟨i.val, hi_lt⟩ := hsucc
        _ = 2 * i.val + P.ν i.castSucc := by
          have hfin : (⟨i.val, hi_lt⟩ : Fin (m' + 1)) = i.castSucc := Fin.ext (by simp)
          rw [hfin, hps_cast, Fin.val_castSucc]
    omega
  have hnu_last : P.ν (Fin.last m') = 2 := by
    have hsum_univ : (∑ j : Fin (m' + 1), P.ν j) = 2 * (m' + 1) := by
      simpa [hS_eq] using P.sum_ν
    rw [Fin.sum_univ_castSucc] at hsum_univ
    have hsum_rest : (∑ i : Fin m', P.ν i.castSucc) = m' * 2 := by
      calc (∑ i : Fin m', P.ν i.castSucc)
          = (∑ i : Fin m', 2) := Finset.sum_congr rfl (fun i _ => hnu_castSucc i)
        _ = m' * 2 := by simp [Finset.card_univ]
    omega
  have hnu_all_two : ∀ j : Fin (m' + 1), P.ν j = 2 := by
    intro j; exact Fin.lastCases hnu_last hnu_castSucc j
  have h_all_eq : ∀ j k : Fin (m' + 1), P.ν j = P.ν k := by
    intro j k
    simp [hnu_all_two j, hnu_all_two k]
  obtain ⟨j, k, hjk⟩ := h_nontrivial
  exact hjk (h_all_eq j k)

/-- Constructive divisor-based reduction interface via offset-witness bridge.
This version bypasses `prime_projection_crt_on_divisor`. -/
theorem reduce_to_prime_divisor_profile_data_constructive
    {m : ℕ} [NeZero m] (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ∣ m) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  exact prime_projection_crt_package_from_offset_witness
    (hm := hm) (P := P) h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile

/-- Constructive packaging lemma for compatibility with prime-replacement consumers.
Bypasses `prime_projection_crt_on_divisor` when given offset-witness bridge data. -/
theorem zsigmondy_prime_replacement_data_constructive
    {m : ℕ} [NeZero m] (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    ∃ (m' : ℕ), Fact (Nat.Prime m') ∧ NeZero m' ∧
      (m' ≥ 2) ∧
      (∃ P' : CycleProfile m',
        P'.isNontrivial ∧
        P'.isRealizable ∧
        P'.S = 2 * m' ∧
        (∃ h_ge2j' : ∀ j : Fin m', 2 * j.val ≤ P'.partialSum j,
          ∀ j : Fin m', weightsForFour P' h_ge2j' j ≤ 3)) := by
  rcases reduce_to_prime_divisor_profile_data_constructive
      (hm := hm) (P := P) h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile with
    ⟨m', hPrime, hNeZero, _hmdvd, hP'⟩
  have hm'_ge2 : m' ≥ 2 := Nat.Prime.two_le (Fact.out : Nat.Prime m')
  exact ⟨m', hPrime, hNeZero, hm'_ge2, hP'⟩

/-- Constructive Zsigmondy/prime-replacement contradiction route.
This is the no-axiom replacement path for `nontrivial_not_realizable_zsigmondy`
once offset-witness bridge inputs are supplied. -/
theorem nontrivial_not_realizable_zsigmondy_constructive
    {m : ℕ} [NeZero m] (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial) (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s (weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  rcases zsigmondy_prime_replacement_data_constructive
      (hm := hm) (P := P) h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile with
    ⟨m', hPrime, hNeZero, hm', P', hP'⟩
  letI : Fact (Nat.Prime m') := hPrime
  letI : NeZero m' := hNeZero
  rcases hP' with ⟨hP'_nontrivial, hP'_realizable, hP'_S, h_ge2j', h_wbdd'⟩
  exact nontrivial_not_realizable_prime_replacement
    hm' P' hP'_nontrivial hP'_realizable hP'_S h_ge2j' h_wbdd'

end Collatz.CyclotomicDrift
