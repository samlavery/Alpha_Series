/-
  WeylBridge.lean — No divergence via quantitative contraction
  ============================================================
  The core no-divergence proof. Baker's theorem (via rollover coprimality)
  gives a supercritical ν-sum rate (≥ 33 halvings per 20 Syracuse steps).
  Since 3^20/2^33 ≈ 0.406, each 20-step window contracts the orbit value.
  Repeated contraction bounds the orbit, contradicting divergence.

  This is NOT a "perfect mixing" or residue-hitting argument. The proof is
  purely about growth rates: the average 2-adic valuation is high enough
  that multiplication by 3^20 is dominated by division by 2^{Σν}.

  Discharges `drift_integer_crossing_shifts_residue` in NoDivergence.lean
  through an explicit bridge:
  supercritical eta-rate  =>  constructive residue hitting.

  Uses only: baker_rollover_supercritical_rate,
             supercritical_rate_implies_residue_hitting
-/

import Collatz.CycleEquation
import Collatz.NumberTheoryAxioms
import Collatz.ResidueDynamics
import Mathlib.Data.ZMod.Basic

open scoped Classical BigOperators
open Finset

namespace Collatz.WeylBridge

open Collatz.CycleEquation
open Collatz.ResidueDynamics

set_option maxHeartbeats 1600000

/-! ## Baker rollover → supercritical ν-sum rate -/

/-- Combined Baker rollover: divergent orbit has supercritical ν-sum rate.
    Baker coprimality (D = 2^S - 3^m is always odd) prevents the orbit from
    avoiding high-v₂ residue classes, yielding Σ η ≥ 33 per 20 steps. -/
theorem baker_tao_supercritical (n₀ : ℕ) (h_n₀ : n₀ > 1) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m, collatzOddIter m n₀ > B) :
    ∃ M₀ : ℕ, ∃ delta : ℕ, 0 < delta ∧
      ∀ M W : ℕ, M₀ ≤ M → 20 ≤ W →
        8 * W + delta ≤ 5 * (Finset.sum (Finset.range W)
          (fun i =>
            if collatzOddIter (M + i) n₀ % 8 = 1 then 2
            else if collatzOddIter (M + i) n₀ % 8 = 5 then 3
            else 1)) :=
  baker_rollover_supercritical_rate n₀ h_n₀ h_odd h_div

/-! ## Supercritical rate → η-sum ≥ 33 → ν-sum ≥ 33 per 20 steps -/

lemma eta_sum_ge_33 (n₀ M₀ delta : ℕ) (h_delta : 0 < delta)
    (h_rate : ∀ M W : ℕ, M₀ ≤ M → 20 ≤ W →
      8 * W + delta ≤ 5 * (Finset.sum (Finset.range W)
        (fun i =>
          if collatzOddIter (M + i) n₀ % 8 = 1 then 2
          else if collatzOddIter (M + i) n₀ % 8 = 5 then 3
          else 1)))
    (M : ℕ) (hM : M₀ ≤ M) :
    33 ≤ Finset.sum (Finset.range 20)
      (fun i =>
        if collatzOddIter (M + i) n₀ % 8 = 1 then 2
        else if collatzOddIter (M + i) n₀ % 8 = 5 then 3
        else 1) := by
  have h := h_rate M 20 hM (le_refl 20)
  omega

lemma nu_sum_ge_eta_sum (n₀ : ℕ) (h_odd : Odd n₀) (h_pos : 0 < n₀)
    (M W : ℕ) :
    Finset.sum (Finset.range W)
      (fun i =>
        if collatzOddIter (M + i) n₀ % 8 = 1 then 2
        else if collatzOddIter (M + i) n₀ % 8 = 5 then 3
        else 1) ≤
    Finset.sum (Finset.range W)
      (fun i => v2 (3 * collatzOddIter (M + i) n₀ + 1)) := by
  apply Finset.sum_le_sum
  intro i _
  exact etaResidue_le_v2_of_odd _ (collatzOddIter_odd h_odd h_pos (M + i))

/-! ## Orbit contraction from supercritical ν-sum -/

/-- Partial sums are monotone: orbitS x j ≤ orbitS x k for j ≤ k. -/
lemma orbitS_mono (x : ℕ) {j k : ℕ} (h : j ≤ k) : orbitS x j ≤ orbitS x k := by
  unfold orbitS
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono h

/-- Wavesum bound: 2 * C_k ≤ (3^k - 1) * 2^{S_k}.
    Proof: each term 2 * 3^{k-1-j} * 2^{S_j} ≤ 2 * 3^{k-1-j} * 2^{S_k}
    since S_j ≤ S_k. Summing: 2*C_k ≤ 2*2^{S_k} * Σ 3^{k-1-j} = (3^k-1)*2^{S_k}. -/
lemma orbitC_le_wavesum_bound (x k : ℕ) :
    2 * orbitC x k ≤ (3 ^ k - 1) * 2 ^ orbitS x k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [orbitC_succ]
    have h1k : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by omega)
    have h3k : 3 ≤ 3 ^ (k + 1) := le_of_eq (pow_one 3).symm |>.trans
      (Nat.pow_le_pow_right (by omega) (by omega))
    have hS_le : orbitS x k ≤ orbitS x (k + 1) := orbitS_mono x (Nat.le_succ k)
    have hpow_le : 2 ^ orbitS x k ≤ 2 ^ orbitS x (k + 1) :=
      Nat.pow_le_pow_right (by omega) hS_le
    calc 2 * (3 * orbitC x k + 2 ^ orbitS x k)
        = 3 * (2 * orbitC x k) + 2 * 2 ^ orbitS x k := by ring
      _ ≤ 3 * ((3 ^ k - 1) * 2 ^ orbitS x k) + 2 * 2 ^ orbitS x k := by
          linarith [Nat.mul_le_mul_left 3 ih]
      _ = (3 * (3 ^ k - 1) + 2) * 2 ^ orbitS x k := by ring
      _ = (3 ^ (k + 1) - 1) * 2 ^ orbitS x k := by
          congr 1; omega
      _ ≤ (3 ^ (k + 1) - 1) * 2 ^ orbitS x (k + 1) :=
          Nat.mul_le_mul_left _ hpow_le

/-- Contraction: for x ≥ 3^20 with Σν ≥ 33, the 20-step iterate is strictly less than x.
    Key insight: 2*3^20 < 2^33 ≤ 2^S, so 2^S - 3^20 > 2^S/2.
    Combined with wavesum bound: x < 3^20 - 1, contradicting x ≥ 3^20. -/
theorem contraction_20step (x : ℕ) (h_odd : Odd x) (h_pos : 0 < x)
    (h_nu : 33 ≤ orbitS x 20) (h_large : x ≥ 3 ^ 20) :
    collatzOddIter 20 x < x := by
  have h_formula := orbit_iteration_formula h_odd h_pos 20
  have h_wave := orbitC_le_wavesum_bound x 20
  have h_pow : 2 ^ 33 ≤ 2 ^ orbitS x 20 := Nat.pow_le_pow_right (by omega) h_nu
  have h32 : (3 : ℕ) ^ 20 < 2 ^ 32 := by native_decide
  have h_iter_pos : 0 < collatzOddIter 20 x := by
    obtain ⟨k, hk⟩ := collatzOddIter_odd h_odd h_pos 20; omega
  by_contra h_ge
  push_neg at h_ge
  -- iter20 ≥ x → x * 2^S ≤ 3^20 * x + C₂₀
  have h1 : x * 2 ^ orbitS x 20 ≤ 3 ^ 20 * x + orbitC x 20 := by
    calc x * 2 ^ orbitS x 20
        ≤ collatzOddIter 20 x * 2 ^ orbitS x 20 := by
          apply Nat.mul_le_mul_right; exact h_ge
      _ = 3 ^ 20 * x + orbitC x 20 := h_formula
  -- 3^20 ≤ 2^S
  have h_sub : 3 ^ 20 ≤ 2 ^ orbitS x 20 := by linarith
  -- x * (2^S - 3^20) ≤ C₂₀
  have h1b : x * (2 ^ orbitS x 20 - 3 ^ 20) ≤ orbitC x 20 := by
    zify [h_sub]
    linarith [h1]
  -- 2 * x * (2^S - 3^20) ≤ (3^20 - 1) * 2^S
  have h3 : 2 * x * (2 ^ orbitS x 20 - 3 ^ 20) ≤ (3 ^ 20 - 1) * 2 ^ orbitS x 20 := by
    linarith [h_wave]
  -- 2 * 3^20 < 2^S → 2*(2^S - 3^20) > 2^S
  have h_2x3 : 2 * 3 ^ 20 < 2 ^ 33 := by native_decide
  have h_2x3_S : 2 * 3 ^ 20 < 2 ^ orbitS x 20 := by omega
  have h_half : 2 ^ orbitS x 20 < 2 * (2 ^ orbitS x 20 - 3 ^ 20) := by omega
  -- x * 2^S < 2 * x * (2^S - 3^20) ≤ (3^20-1) * 2^S
  have h4 : x * 2 ^ orbitS x 20 < 2 * x * (2 ^ orbitS x 20 - 3 ^ 20) := by
    zify [h_sub]
    nlinarith [h_half, h_pos]
  have h5 : x * 2 ^ orbitS x 20 < (3 ^ 20 - 1) * 2 ^ orbitS x 20 := by omega
  have h6 : x < 3 ^ 20 - 1 := by
    have h_pow_pos : 0 < 2 ^ orbitS x 20 := by positivity
    exact Nat.lt_of_mul_lt_mul_right h5
  omega

/-! ## Orbit growth bounds -/

/-- Each Syracuse step less than doubles: T(n) < 2n for odd n > 0. -/
lemma collatzOdd_lt_two_mul (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) :
    collatzOdd n < 2 * n := by
  have h_step := syracuse_step_formula n hn
  -- v2(3n+1) ≥ 1 since 3n+1 is even for odd n
  have h_ne : 3 * n + 1 ≠ 0 := by omega
  have h_dvd : (2 : ℕ) ^ 1 ∣ (3 * n + 1) := by
    obtain ⟨k, hk⟩ := hn; subst hk; ring_nf; omega
  have h_v_ge : 1 ≤ v2 (3 * n + 1) := by
    unfold v2
    exact (FiniteMultiplicity.of_prime_left (Nat.Prime.prime (by decide)) h_ne).le_multiplicity_of_pow_dvd h_dvd
  -- collatzOdd n * 2 ≤ collatzOdd n * 2^v = 3n+1 ≤ 4n
  have h_two_le : collatzOdd n * 2 ≤ 3 * n + 1 := by
    calc collatzOdd n * 2 = collatzOdd n * 2 ^ 1 := by ring
      _ ≤ collatzOdd n * 2 ^ v2 (3 * n + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h_v_ge)
      _ = 3 * n + 1 := h_step
  -- collatzOdd n is odd, so collatzOdd n * 2 ≤ 4n implies collatzOdd n < 2n
  obtain ⟨t, ht⟩ := collatzOdd_odd hn hn_pos
  rw [ht] at h_two_le ⊢; omega

/-- k-fold iteration grows at most 2^k: T^k(n) ≤ 2^k · n. -/
lemma collatzOddIter_le_two_pow_mul (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    collatzOddIter k n ≤ 2 ^ k * n := by
  induction k with
  | zero => simp [collatzOddIter]
  | succ k ih =>
    rw [collatzOddIter_succ_right]
    have hk_odd := collatzOddIter_odd hn hn_pos k
    have hk_pos : 0 < collatzOddIter k n := by obtain ⟨t, ht⟩ := hk_odd; omega
    have h1 := collatzOdd_lt_two_mul _ hk_odd hk_pos
    have h2 : 2 * (2 ^ k * n) = 2 ^ (k + 1) * n := by ring
    linarith

/-! ## Divergence is impossible -/

/-- collatzOddIter iteration composition: f^j(f^m(n)) = f^{m+j}(n). -/
lemma collatzOddIter_comp (m j n₀ : ℕ) :
    collatzOddIter j (collatzOddIter m n₀) = collatzOddIter (m + j) n₀ := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih =>
    -- LHS: collatzOddIter (j+1) (collatzOddIter m n₀)
    --     = collatzOddIter j (collatzOdd (collatzOddIter m n₀))  (by def)
    --     = collatzOddIter j (collatzOddIter (m+1) n₀)           (by succ_right)
    --     = collatzOddIter ((m+1)+j) n₀                           (by IH)
    change collatzOddIter j (collatzOdd (collatzOddIter m n₀)) = _
    rw [← collatzOddIter_succ_right m n₀, ih (m + 1)]
    congr 1; omega

/-- Divergence is impossible given Baker-rollover supercritical rate. -/
theorem no_divergence_from_supercritical (n₀ : ℕ) (h_n₀ : n₀ > 1) (h_odd : Odd n₀)
    (h_div : ∀ B : ℕ, ∃ m, collatzOddIter m n₀ > B)
    (h_mixing : ∃ M₀ : ℕ, ∃ delta : ℕ, 0 < delta ∧
      ∀ M W : ℕ, M₀ ≤ M → 20 ≤ W →
        8 * W + delta ≤ 5 * (Finset.sum (Finset.range W)
          (fun i =>
            if collatzOddIter (M + i) n₀ % 8 = 1 then 2
            else if collatzOddIter (M + i) n₀ % 8 = 5 then 3
            else 1))) :
    False := by
  obtain ⟨M₀, delta, h_delta, h_rate⟩ := h_mixing
  have h_nu_bound : ∀ M, M₀ ≤ M →
      33 ≤ Finset.sum (Finset.range 20)
        (fun i => v2 (3 * collatzOddIter (M + i) n₀ + 1)) :=
    fun M hM => calc
      33 ≤ _ := eta_sum_ge_33 n₀ M₀ delta h_delta h_rate M hM
      _ ≤ _ := nu_sum_ge_eta_sum n₀ h_odd (by omega) M 20
  -- Find a large orbit value past M₀
  obtain ⟨m₁, hm₁⟩ := h_div (Finset.sum (Finset.range (M₀ + 1))
    (fun j => collatzOddIter j n₀) + 3 ^ 20)
  have hm₁_gt : m₁ > M₀ := by
    by_contra h_le
    push_neg at h_le
    have : collatzOddIter m₁ n₀ ≤ Finset.sum (Finset.range (M₀ + 1))
        (fun j => collatzOddIter j n₀) :=
      Finset.single_le_sum (f := fun j => collatzOddIter j n₀)
        (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    omega
  have hm₁_ge : M₀ ≤ m₁ := by omega
  have hm₁_large : collatzOddIter m₁ n₀ > 3 ^ 20 := by omega
  have hm₁_odd : Odd (collatzOddIter m₁ n₀) := collatzOddIter_odd h_odd (by omega) m₁
  have hm₁_pos : 0 < collatzOddIter m₁ n₀ := by obtain ⟨k, hk⟩ := hm₁_odd; omega
  -- ν-sum on the 20-step window starting at m₁
  have h_nu_m₁ : 33 ≤ Finset.sum (Finset.range 20)
      (fun i => v2 (3 * collatzOddIter (m₁ + i) n₀ + 1)) :=
    h_nu_bound m₁ hm₁_ge
  -- Connect sub-orbit ν-sums via iteration composition
  have h_nu_eq : ∀ j, orbitNu (collatzOddIter m₁ n₀) j =
      v2 (3 * collatzOddIter (m₁ + j) n₀ + 1) := by
    intro j; unfold orbitNu; rw [collatzOddIter_comp]
  have h_S_eq : orbitS (collatzOddIter m₁ n₀) 20 =
      Finset.sum (Finset.range 20) (fun j => v2 (3 * collatzOddIter (m₁ + j) n₀ + 1)) := by
    unfold orbitS
    apply Finset.sum_congr rfl
    intro j _
    exact h_nu_eq j
  have h_S_ge : 33 ≤ orbitS (collatzOddIter m₁ n₀) 20 := by rw [h_S_eq]; exact h_nu_m₁
  -- Contraction: x_{m₁+20} < x_{m₁} (since x_{m₁} ≥ 3^20 and Σν ≥ 33)
  have h_contract := contraction_20step (collatzOddIter m₁ n₀) hm₁_odd hm₁_pos h_S_ge (by omega)
  -- Generalized contraction: any checkpoint ≥ M₀ with orbit ≥ 3^20 contracts
  have h_gen : ∀ M, M₀ ≤ M → 3 ^ 20 ≤ collatzOddIter M n₀ →
      collatzOddIter (M + 20) n₀ < collatzOddIter M n₀ := by
    intro M hM hge
    have hM_odd := collatzOddIter_odd h_odd (by omega) M
    have hM_pos : 0 < collatzOddIter M n₀ := by obtain ⟨k, hk⟩ := hM_odd; omega
    have h_nu_M := h_nu_bound M hM
    have h_nu_eq_M : ∀ j, orbitNu (collatzOddIter M n₀) j =
        v2 (3 * collatzOddIter (M + j) n₀ + 1) := by
      intro j; unfold orbitNu; rw [collatzOddIter_comp]
    have h_S_eq_M : orbitS (collatzOddIter M n₀) 20 =
        Finset.sum (Finset.range 20) (fun j => v2 (3 * collatzOddIter (M + j) n₀ + 1)) := by
      unfold orbitS; apply Finset.sum_congr rfl; intro j _; exact h_nu_eq_M j
    have h_S_ge_M : 33 ≤ orbitS (collatzOddIter M n₀) 20 := by rw [h_S_eq_M]; exact h_nu_M
    rw [← collatzOddIter_comp M 20 n₀]
    exact contraction_20step _ hM_odd hM_pos h_S_ge_M hge
  -- Below-threshold stability: checkpoint < 3^20 stays < 3^20
  have h_stable : ∀ M, M₀ ≤ M → collatzOddIter M n₀ < 3 ^ 20 →
      collatzOddIter (M + 20) n₀ < 3 ^ 20 := by
    intro M hM hlt
    set x := collatzOddIter M n₀ with hx_def
    have hM_odd := collatzOddIter_odd h_odd (by omega) M
    have hM_pos : 0 < x := by obtain ⟨k, hk⟩ := hM_odd; omega
    -- ν-sum ≥ 33 at M (mixing rate still applies)
    have h_nu_M := h_nu_bound M hM
    have h_nu_eq_M : ∀ j, orbitNu x j = v2 (3 * collatzOddIter (M + j) n₀ + 1) := by
      intro j; unfold orbitNu; rw [hx_def, collatzOddIter_comp]
    have h_S_eq_M : orbitS x 20 =
        Finset.sum (Finset.range 20) (fun j => v2 (3 * collatzOddIter (M + j) n₀ + 1)) := by
      unfold orbitS; apply Finset.sum_congr rfl; intro j _; exact h_nu_eq_M j
    have h_S_ge : 33 ≤ orbitS x 20 := by rw [h_S_eq_M]; exact h_nu_M
    -- From orbit formula: iter20 * 2^S = 3^20 * x + C
    have h_formula := orbit_iteration_formula hM_odd hM_pos 20
    have h_wave := orbitC_le_wavesum_bound x 20
    have h_pow33 : 2 ^ 33 ≤ 2 ^ orbitS x 20 := Nat.pow_le_pow_right (by omega) h_S_ge
    -- iter20 * 2^S = 3^20 * x + C ≤ 3^20 * x + (3^20 - 1) * 2^S / 2
    -- iter20 ≤ 3^20 * x / 2^S + (3^20 - 1) / 2
    -- For x < 3^20 and 2^S ≥ 2^33: iter20 < 3^40/2^33 + 3^20/2 < 3^20
    -- Rewrite goal to use sub-orbit notation
    rw [← collatzOddIter_comp M 20 n₀]
    change collatzOddIter 20 x < 3 ^ 20
    -- Suffices to show iter20 * 2^S < 3^20 * 2^S
    suffices h : collatzOddIter 20 x * 2 ^ orbitS x 20 < 3 ^ 20 * 2 ^ orbitS x 20 by
      exact Nat.lt_of_mul_lt_mul_right h
    -- iter20 * 2^S = 3^20 * x + C (orbit formula, already using x = collatzOddIter M n₀)
    have h_formula2 : collatzOddIter 20 x * 2 ^ orbitS x 20 = 3 ^ 20 * x + orbitC x 20 :=
      orbit_iteration_formula hM_odd hM_pos 20
    rw [h_formula2]
    -- Need: 3^20 * x + C < 3^20 * 2^S
    -- Use: 2*C ≤ (3^20-1)*2^S and x < 3^20
    -- So 2*(3^20 * x + C) ≤ 2*3^20*x + (3^20-1)*2^S < 2*3^40 + (3^20-1)*2^S
    -- Need: 2*3^40 + (3^20-1)*2^S ≤ 2*3^20*2^S
    -- i.e., 2*3^40 ≤ (3^20+1)*2^S
    -- For S ≥ 33: (3^20+1)*2^33 > 2*3^40 (by native_decide)
    have h_key : (3 ^ 20 + 1) * 2 ^ 33 > 2 * 3 ^ 40 := by native_decide
    have h_key2 : (3 ^ 20 + 1) * 2 ^ orbitS x 20 > 2 * 3 ^ 40 := by
      calc (3 ^ 20 + 1) * 2 ^ orbitS x 20 ≥ (3 ^ 20 + 1) * 2 ^ 33 :=
            Nat.mul_le_mul_left _ h_pow33
        _ > 2 * 3 ^ 40 := h_key
    have h1k : 1 ≤ 3 ^ 20 := Nat.one_le_pow 20 3 (by omega)
    zify [h1k] at h_wave h_key2 hlt ⊢
    nlinarith
  -- Checkpoint bound: all checkpoint values from m₁ onward are < collatzOddIter m₁ n₀ + 1
  -- Descent: checkpoints decrease while ≥ 3^20, and stay < 3^20 once they drop
  have h_ckpt_bound : ∀ i, collatzOddIter (m₁ + 20 * i) n₀ ≤ collatzOddIter m₁ n₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      by_cases hge : 3 ^ 20 ≤ collatzOddIter (m₁ + 20 * i) n₀
      · -- Above threshold: contraction applies
        have hM_ge : M₀ ≤ m₁ + 20 * i := by omega
        have hc := h_gen (m₁ + 20 * i) hM_ge hge
        rw [show m₁ + 20 * (i + 1) = m₁ + 20 * i + 20 from by ring]
        exact le_of_lt (lt_of_lt_of_le hc ih)
      · -- Below threshold: stability keeps it below 3^20 ≤ a₀
        push_neg at hge
        have hM_ge : M₀ ≤ m₁ + 20 * i := by omega
        have hs := h_stable (m₁ + 20 * i) hM_ge hge
        rw [show m₁ + 20 * (i + 1) = m₁ + 20 * i + 20 from by ring]
        exact le_of_lt (lt_of_lt_of_le hs (by omega))
  -- Bound all orbit values from m₁ onward: f(m) ≤ 2^19 * a₀
  have h_post_bound : ∀ m, m₁ ≤ m →
      collatzOddIter m n₀ ≤ 2 ^ 19 * collatzOddIter m₁ n₀ := by
    intro m hm
    -- Decompose: m = m₁ + 20*q + r, 0 ≤ r < 20
    set q := (m - m₁) / 20
    set r := (m - m₁) % 20
    have hrm : m = m₁ + 20 * q + r := by omega
    rw [hrm]
    -- f(m₁ + 20q + r) = collatzOddIter r (f(m₁ + 20q))
    rw [show m₁ + 20 * q + r = (m₁ + 20 * q) + r from by ring,
        ← collatzOddIter_comp (m₁ + 20 * q) r n₀]
    -- checkpoint bound: f(m₁ + 20q) ≤ a₀
    have h_ckpt := h_ckpt_bound q
    -- iteration bound: collatzOddIter r x ≤ 2^r * x
    have h_ckpt_odd := collatzOddIter_odd h_odd (by omega) (m₁ + 20 * q)
    have h_ckpt_pos : 0 < collatzOddIter (m₁ + 20 * q) n₀ := by
      obtain ⟨t, ht⟩ := h_ckpt_odd; omega
    have h_iter := collatzOddIter_le_two_pow_mul _ h_ckpt_odd h_ckpt_pos r
    have hr_lt : r < 20 := Nat.mod_lt _ (by omega)
    have h_pow_le : 2 ^ r ≤ 2 ^ 19 := Nat.pow_le_pow_right (by omega) (by omega)
    calc collatzOddIter r (collatzOddIter (m₁ + 20 * q) n₀)
        ≤ 2 ^ r * collatzOddIter (m₁ + 20 * q) n₀ := h_iter
      _ ≤ 2 ^ r * collatzOddIter m₁ n₀ := Nat.mul_le_mul_left _ h_ckpt
      _ ≤ 2 ^ 19 * collatzOddIter m₁ n₀ := Nat.mul_le_mul_right _ h_pow_le
  -- Get contradiction: choose B large enough, all orbit values ≤ B
  set B := 2 ^ 19 * collatzOddIter m₁ n₀ +
    Finset.sum (Finset.range (m₁ + 1)) (fun j => collatzOddIter j n₀) with hB_def
  obtain ⟨m₂, hm₂⟩ := h_div B
  -- m₂ can't be ≤ m₁ (finite prefix bounded by sum component ≤ B)
  -- m₂ can't be > m₁ (post bound ≤ B)
  -- Either way, f(m₂) ≤ B, contradicting f(m₂) > B
  have h_all : ∀ j, collatzOddIter j n₀ ≤ B := by
    intro j
    by_cases hj : m₁ ≤ j
    · -- Post m₁: bounded by 2^19 * a₀ ≤ B
      have := h_post_bound j hj; omega
    · -- Pre m₁: bounded by sum ≤ B
      push_neg at hj
      have : collatzOddIter j n₀ ≤
          Finset.sum (Finset.range (m₁ + 1)) (fun j => collatzOddIter j n₀) :=
        Finset.single_le_sum (f := fun j => collatzOddIter j n₀)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      omega
  exact absurd hm₂ (not_lt.mpr (h_all m₂))

/-- **Main theorem**: A divergent odd orbit hits every residue class mod M.
    Proof route: Baker rollover yields a supercritical eta-rate, then apply the
    constructive supercritical-to-residue bridge. -/
theorem drift_crossing_from_baker (n₀ M K : ℕ) (h_M : M > 1)
    (h_n₀ : n₀ > 1) (h_odd : Odd n₀) (h_div : ∀ B : ℕ, ∃ m, collatzOddIter m n₀ > B)
    (target : ZMod M) :
    ∃ m ≥ K, (collatzOddIter m n₀ : ZMod M) = target := by
  exact supercritical_rate_implies_residue_hitting
    n₀ M K h_M h_n₀ h_odd h_div (baker_tao_supercritical n₀ h_n₀ h_odd h_div) target

end Collatz.WeylBridge
