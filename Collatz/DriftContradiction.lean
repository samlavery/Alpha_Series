/-
  DriftContradiction.lean — Path 1: Baker drift excludes nontrivial cycles
  =========================================================================

  **Theorem** (`fixed_profile_impossible`):
  No nontrivial realizable cycle can have a fixed halving profile.

  **Proof outline**:
  1. A fixed profile P with period m gives n₀ = W/D > 0.
  2. One cycle scales the orbit by 3^m / 2^S = 2^{−ε},
     where ε = S − m·log₂3 is the Baker drift.
  3. L repetitions scale by 2^{−Lε}.
  4. Baker's theorem on linear forms in logarithms: |ε| ≥ c / m^K > 0
     for nontrivial P (not all νⱼ equal).
  5. Choose L = ⌈m^K / c⌉ so that |Lε| ≥ 1.
  6. Then n₀ · 2^{−Lε} ≠ n₀, contradicting orbit closure.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Collatz.Defs
import Collatz.NumberTheoryAxioms

open scoped BigOperators

namespace Collatz

/-! ## Drift and scaling definitions -/

/-- Baker drift: ε = S - m·log₂(3) -/
noncomputable def base2_offset {m : ℕ} (P : CycleProfile m) : ℝ :=
  (P.S : ℝ) - (m : ℝ) * Real.log 3 / Real.log 2

/-- Accumulated offset after L cycles: L·ε -/
noncomputable def accumulated_offset {m : ℕ} (P : CycleProfile m) (L : ℕ) : ℝ :=
  (L : ℝ) * base2_offset P

/-- Cycle scaling factor: 3^m / 2^S -/
noncomputable def cycle_scaling_factor {m : ℕ} (P : CycleProfile m) : ℝ :=
  (3 : ℝ) ^ m / (2 : ℝ) ^ P.S

/-! ## Core lemmas and axioms -/

/-- 3 = 2^(log₂3). -/
lemma three_eq_two_rpow_log : (3 : ℝ) = (2 : ℝ) ^ (Real.log 3 / Real.log 2) := by
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h3_pos : (0 : ℝ) < 3 := by norm_num
  have h_log2_ne : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h2_pos (by norm_num)
  rw [Real.rpow_def_of_pos h2_pos]
  rw [mul_div_cancel₀ _ h_log2_ne]
  exact (Real.exp_log h3_pos).symm

/-- 3^m/2^S = 2^{-ε}. -/
lemma scaling_factor_eq_two_pow_neg_offset {m : ℕ} (P : CycleProfile m) :
  cycle_scaling_factor P = (2 : ℝ) ^ (-base2_offset P) := by
  rw [cycle_scaling_factor, base2_offset]
  conv_lhs => arg 1; arg 1; rw [three_eq_two_rpow_log]
  rw [show ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) ^ m =
            ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) ^ (m : ℝ) from (Real.rpow_natCast _ _).symm]
  rw [show (2 : ℝ) ^ P.S = (2 : ℝ) ^ (P.S : ℝ) from (Real.rpow_natCast _ _).symm]
  have h_mul : ((2 : ℝ) ^ (Real.log 3 / Real.log 2)) ^ (m : ℝ) =
               (2 : ℝ) ^ ((Real.log 3 / Real.log 2) * (m : ℝ)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h_mul]
  rw [div_eq_mul_inv]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- L cycles scale by 2^{-Lε}. -/
lemma orbit_scaling_after_L_cycles {m : ℕ} (P : CycleProfile m) (L : ℕ) :
  (cycle_scaling_factor P) ^ L = (2 : ℝ) ^ (-accumulated_offset P L) := by
  rw [scaling_factor_eq_two_pow_neg_offset, accumulated_offset]
  rw [← Real.rpow_natCast]
  have h : ((2 : ℝ) ^ (-base2_offset P)) ^ (L : ℝ) = (2 : ℝ) ^ (-base2_offset P * (L : ℝ)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h]
  ring_nf

/-- When |Lε| ≥ 1, the orbit cannot return to n₀. -/
lemma orbit_cannot_close {m : ℕ} (P : CycleProfile m) (L : ℕ)
    (h_offset : |accumulated_offset P L| ≥ 1) (n₀ : ℝ) (hn₀ : n₀ > 0) :
    n₀ * (2 : ℝ) ^ (-accumulated_offset P L) ≠ n₀ := by
  intro h_eq
  have h_scale : (2 : ℝ) ^ (-accumulated_offset P L) = 1 := by
    have : n₀ * (2 : ℝ) ^ (-accumulated_offset P L) = n₀ * 1 := by
      rw [h_eq]; ring
    linarith [mul_left_cancel₀ (ne_of_gt hn₀) this]
  have h_exp_zero : -accumulated_offset P L = 0 := by
    have h_eq : (2 : ℝ) ^ (-accumulated_offset P L) = (2 : ℝ) ^ (0 : ℝ) := by simp [h_scale]
    have h2_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have h2_gt_one : (1 : ℝ) < 2 := by norm_num
    by_contra h_ne
    cases' (ne_iff_lt_or_gt.mp h_ne) with h_lt h_gt
    · have : (2 : ℝ) ^ (-accumulated_offset P L) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt h2_gt_one h_lt
      linarith [this, h_eq]
    · have : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ (-accumulated_offset P L) :=
        Real.rpow_lt_rpow_of_exponent_lt h2_gt_one h_gt
      linarith [this, h_eq]
  have h_offset_zero : accumulated_offset P L = 0 := by linarith
  have : |accumulated_offset P L| = 0 := by simp [h_offset_zero]
  linarith

/-- For nontrivial profiles, there exists L with |Lε| ≥ 1. -/
lemma exists_offset_ge_one {m : ℕ} (P : CycleProfile m) (hm : m ≥ 2)
    (hnontrivial : P.isNontrivial) :
    ∃ L : ℕ, |accumulated_offset P L| ≥ 1 := by
  obtain ⟨c, K, hc⟩ := baker_lower_bound P hm hnontrivial
  have hc_pos : c > 0 := hc.1
  have hc_bound : |base2_offset P| ≥ c / ((m : ℝ) ^ K) := by
    simpa [base2_offset] using hc.2
  have hm_pos : (m : ℝ) > 0 := by positivity
  have hmK_pos : ((m : ℝ) ^ K) > 0 := by positivity
  set L := Nat.ceil (((m : ℝ) ^ K) / c) + 1 with hL_def
  use L
  have hL_pos : (L : ℝ) > 0 := by positivity
  have hL_bound : (L : ℝ) ≥ ((m : ℝ) ^ K) / c := by
    have : (Nat.ceil (((m : ℝ) ^ K) / c) : ℝ) ≥ ((m : ℝ) ^ K) / c :=
      Nat.le_ceil (((m : ℝ) ^ K) / c)
    simp [hL_def]
    linarith
  have h1 : |accumulated_offset P L| = |(L : ℝ) * base2_offset P| := by rw [accumulated_offset]
  have h2 : |(L : ℝ) * base2_offset P| = (L : ℝ) * |base2_offset P| := by
    rw [abs_mul]
    simp [abs_of_pos hL_pos]
  have h3 : (L : ℝ) * |base2_offset P| ≥ (((m : ℝ) ^ K) / c) * |base2_offset P| := by
    apply mul_le_mul_of_nonneg_right hL_bound
    exact abs_nonneg _
  have h4 : (((m : ℝ) ^ K) / c) * |base2_offset P| ≥
      (((m : ℝ) ^ K) / c) * (c / ((m : ℝ) ^ K)) := by
    apply mul_le_mul_of_nonneg_left hc_bound
    apply div_nonneg
    · exact le_of_lt hmK_pos
    · exact le_of_lt hc_pos
  have h5 : (((m : ℝ) ^ K) / c) * (c / ((m : ℝ) ^ K)) = 1 := by
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have hmK_ne : (m : ℝ) ^ K ≠ 0 := ne_of_gt hmK_pos
    field_simp [hc_ne, hmK_ne]
  show |accumulated_offset P L| ≥ 1
  calc |accumulated_offset P L|
      = |(L : ℝ) * base2_offset P| := h1
    _ = (L : ℝ) * |base2_offset P| := h2
    _ ≥ (((m : ℝ) ^ K) / c) * |base2_offset P| := h3
    _ ≥ (((m : ℝ) ^ K) / c) * (c / ((m : ℝ) ^ K)) := h4
    _ = 1 := h5

/-- Stronger drift growth form: beyond a threshold, every loop has
`|L·ε| ≥ 1`. -/
lemma eventually_offset_ge_one {m : ℕ} (P : CycleProfile m) (hm : m ≥ 2)
    (hnontrivial : P.isNontrivial) :
    ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 → |accumulated_offset P L| ≥ 1 := by
  obtain ⟨c, K, hc⟩ := baker_lower_bound P hm hnontrivial
  have hc_pos : c > 0 := hc.1
  have hc_bound : |base2_offset P| ≥ c / ((m : ℝ) ^ K) := by
    simpa [base2_offset] using hc.2
  have hmK_pos : 0 < ((m : ℝ) ^ K) := by positivity
  let L0 : ℕ := Nat.ceil (((m : ℝ) ^ K) / c)
  refine ⟨L0, ?_⟩
  intro L hL_ge
  have hcm_nonneg : 0 ≤ c / ((m : ℝ) ^ K) := by
    apply div_nonneg
    · exact le_of_lt hc_pos
    · exact le_of_lt hmK_pos
  have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
  have hL_lower : (((m : ℝ) ^ K) / c) ≤ (L : ℝ) := by
    have hceil : (((m : ℝ) ^ K) / c) ≤ (L0 : ℝ) := Nat.le_ceil (((m : ℝ) ^ K) / c)
    exact le_trans hceil (by exact_mod_cast hL_ge)
  calc
    |accumulated_offset P L|
        = |(L : ℝ) * base2_offset P| := by rfl
    _ = (L : ℝ) * |base2_offset P| := by
        rw [abs_mul, abs_of_nonneg hL_nonneg]
    _ ≥ (L : ℝ) * (c / ((m : ℝ) ^ K)) := by
        exact mul_le_mul_of_nonneg_left hc_bound hL_nonneg
    _ ≥ (((m : ℝ) ^ K) / c) * (c / ((m : ℝ) ^ K)) := by
        exact mul_le_mul_of_nonneg_right hL_lower hcm_nonneg
    _ = 1 := by
        have hc_ne : c ≠ 0 := ne_of_gt hc_pos
        have hmK_ne : ((m : ℝ) ^ K) ≠ 0 := ne_of_gt hmK_pos
        field_simp [hc_ne, hmK_ne]

end Collatz

namespace Collatz.DriftContradiction

open Collatz

variable {m : ℕ} (P : CycleProfile m)

/-! ## The fixed profile assumption -/

/-- A fixed-profile cycle: the profile P is realizable and nontrivial, and there
exists an anchored orbit that returns to n₀ after L repetitions of P
(i.e., n₀ · (3^m/2^S)^L = n₀). -/
def FixedProfileCycle (P : CycleProfile m) : Prop :=
  P.isRealizable ∧ P.isNontrivial ∧
  (∃ A : AnchoredCycleProfile m, A.profile = P ∧
    ∃ L : ℕ, L > 0 ∧
      (A.n0 : ℝ) * (cycle_scaling_factor P) ^ L = (A.n0 : ℝ))

/-! ## The orbit-drift connection -/

/-- One cycle with profile P scales by 3^m / 2^S. -/
lemma one_cycle_scaling :
    Collatz.cycle_scaling_factor P = (3 : ℝ) ^ m / (2 : ℝ) ^ P.S := by
  rfl

/-- The scaling factor equals 2^{-ε} where ε = S - m·log₂(3). -/
lemma scaling_is_drift_exponent :
    Collatz.cycle_scaling_factor P =
    (2 : ℝ) ^ (-(Collatz.base2_offset P)) := by
  exact Collatz.scaling_factor_eq_two_pow_neg_offset P

/-- L cycles with fixed profile P scale by (3^m/2^S)^L = 2^{-Lε}. -/
lemma L_cycles_scaling (L : ℕ) :
    (Collatz.cycle_scaling_factor P) ^ L =
    (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) := by
  exact Collatz.orbit_scaling_after_L_cycles P L

/-- Quantified drift progression: each loop adds one copy of `ε = base2_offset`. -/
lemma accumulated_offset_succ (L : ℕ) :
    Collatz.accumulated_offset P (L + 1) =
      Collatz.accumulated_offset P L + Collatz.base2_offset P := by
  simp [Collatz.accumulated_offset, Nat.cast_add, add_mul]

/-- Closed form of loop-by-loop drift accumulation. -/
lemma accumulated_offset_eq_mul (L : ℕ) :
    Collatz.accumulated_offset P L = (L : ℝ) * Collatz.base2_offset P := by
  rfl

/-! ## The contradiction -/

/-- After L cycles, orbit position is n₀ · 2^{-Lε}. -/
lemma orbit_position_after_L_cycles (L : ℕ) (n₀ : ℝ) :
    n₀ * (Collatz.cycle_scaling_factor P) ^ L =
    n₀ * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) := by
  congr 1
  exact L_cycles_scaling P L

/-- When |Lε| ≥ 1, orbit cannot return: n₀ · 2^{-Lε} ≠ n₀. -/
lemma drift_prevents_return (L : ℕ) (n₀ : ℝ) (hn₀ : n₀ > 0)
    (h_drift : |Collatz.accumulated_offset P L| ≥ 1) :
    n₀ * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) ≠ n₀ := by
  exact Collatz.orbit_cannot_close P L h_drift n₀ hn₀

/-- Fixed-profile map must change value for some loop count.
For nontrivial `P`, Baker drift gives an `L` with nonzero accumulated offset,
so `n₀ * (cycle_scaling_factor P)^L ≠ n₀` for every `n₀ > 0`. -/
theorem fixed_profile_must_change
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (n₀ : ℝ) (hn₀ : n₀ > 0) :
    ∃ L : ℕ, n₀ * (Collatz.cycle_scaling_factor P) ^ L ≠ n₀ := by
  rcases Collatz.exists_offset_ge_one P hm h_nontrivial with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  rw [L_cycles_scaling]
  exact drift_prevents_return (P := P) L n₀ hn₀ hL

/-! ## Integer/real bridge -/

/-- Bridge lemma: if an integer-profile closure gives exact return after `L`
steps, the corresponding real drift exponent is forced to zero. -/
lemma integer_closure_forces_zero_accumulated_offset
    (L : ℕ) (n₀ : ℝ) (hn₀ : n₀ > 0)
    (h_returns : n₀ * (Collatz.cycle_scaling_factor P) ^ L = n₀) :
    Collatz.accumulated_offset P L = 0 := by
  have h_scale_one : (Collatz.cycle_scaling_factor P) ^ L = 1 := by
    have hn₀_ne : n₀ ≠ 0 := ne_of_gt hn₀
    have h_eq : n₀ * (Collatz.cycle_scaling_factor P) ^ L = n₀ * 1 := by
      simpa using h_returns
    exact mul_left_cancel₀ hn₀_ne h_eq
  rw [L_cycles_scaling] at h_scale_one
  have h_pow_eq :
      (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = (2 : ℝ) ^ (0 : ℝ) := by
    simpa using h_scale_one
  have h2_gt_one : (1 : ℝ) < 2 := by norm_num
  have h_exp_eq : -(Collatz.accumulated_offset P L) = 0 := by
    by_contra h_ne
    rcases (ne_iff_lt_or_gt.mp h_ne) with h_lt | h_gt
    · have : (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt h2_gt_one h_lt
      linarith [this, h_pow_eq]
    · have : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) :=
        Real.rpow_lt_rpow_of_exponent_lt h2_gt_one h_gt
      linarith [this, h_pow_eq]
  linarith

/-- If a positive-length return occurs for a fixed profile, then the one-loop
drift `ε` must be zero. -/
lemma integer_closure_forces_zero_base_offset
    (L : ℕ) (hL_pos : L > 0) (n₀ : ℝ) (hn₀ : n₀ > 0)
    (h_returns : n₀ * (Collatz.cycle_scaling_factor P) ^ L = n₀) :
    Collatz.base2_offset P = 0 := by
  have h_off_zero : Collatz.accumulated_offset P L = 0 :=
    integer_closure_forces_zero_accumulated_offset (P := P) L n₀ hn₀ h_returns
  rw [Collatz.accumulated_offset] at h_off_zero
  have hL_ne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL_pos)
  exact (mul_eq_zero.mp h_off_zero).resolve_left hL_ne

/-- A fixed-profile positive-length return collapses the entire accumulated
drift sequence to zero at every loop count. -/
lemma integer_closure_forces_all_offsets_zero
    (L : ℕ) (hL_pos : L > 0) (n₀ : ℝ) (hn₀ : n₀ > 0)
    (h_returns : n₀ * (Collatz.cycle_scaling_factor P) ^ L = n₀) :
    ∀ t : ℕ, Collatz.accumulated_offset P t = 0 := by
  have h_base_zero : Collatz.base2_offset P = 0 :=
    integer_closure_forces_zero_base_offset (P := P) L hL_pos n₀ hn₀ h_returns
  intro t
  simp [Collatz.accumulated_offset, h_base_zero]

/-- If integer-profile closure holds (n₀ · scaling^L = n₀), then
n₀ · 2^{−Lε} = n₀ as well (since accumulated offset is 0). -/
lemma integer_profile_to_real_profile_bridge
    (L : ℕ) (n₀ : ℝ) (hn₀ : n₀ > 0)
    (h_returns : n₀ * (Collatz.cycle_scaling_factor P) ^ L = n₀) :
    n₀ * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = n₀ := by
  have h_zero :=
    integer_closure_forces_zero_accumulated_offset (P := P) L n₀ hn₀ h_returns
  rw [h_zero]
  ring

/-! ## The main theorem: fixed-profile cycles are impossible -/

/-- **Path 1 main result**: No nontrivial realizable cycle can have a fixed profile.
    Closure forces ε = 0, but Baker's theorem gives |ε| > 0 for nontrivial profiles. -/
theorem fixed_profile_impossible
    (hm : m ≥ 2) (P : CycleProfile m)
    (h_fixed : FixedProfileCycle P) :
    False := by
  have h_realizable := h_fixed.1
  have h_nontrivial := h_fixed.2.1
  obtain ⟨A, hA_profile, h_closure⟩ := h_fixed.2.2

  obtain ⟨L, hL_pos, h_returns⟩ := h_closure

  have h_scaling_one : (cycle_scaling_factor P) ^ L = 1 := by
    have h_n0_posR : (A.n0 : ℝ) > 0 := by exact_mod_cast A.n0_pos
    have hA_nonzero : (A.n0 : ℝ) ≠ 0 := ne_of_gt h_n0_posR
    have h_eq : (A.n0 : ℝ) * (cycle_scaling_factor P) ^ L = (A.n0 : ℝ) * 1 := by
      simpa using h_returns
    exact mul_left_cancel₀ hA_nonzero h_eq

  rw [L_cycles_scaling] at h_scaling_one

  have h_n0_posR : (A.n0 : ℝ) > 0 := by exact_mod_cast A.n0_pos
  have h_all_zero : ∀ t : ℕ, Collatz.accumulated_offset P t = 0 :=
    integer_closure_forces_all_offsets_zero (P := P) L hL_pos (A.n0 : ℝ) h_n0_posR h_returns
  rcases Collatz.exists_offset_ge_one P hm h_nontrivial with ⟨t, ht⟩
  have h_abs_zero : |Collatz.accumulated_offset P t| = 0 := by simp [h_all_zero t]
  linarith [ht, h_abs_zero]

/-! ## Corollary -/

/-- Negated form of `fixed_profile_impossible`: ¬FixedProfileCycle P. -/
theorem no_nontrivial_cycles (hm : m ≥ 2) (P : CycleProfile m) :
    ¬FixedProfileCycle P := by
  intro h
  exact fixed_profile_impossible hm P h

end Collatz.DriftContradiction
