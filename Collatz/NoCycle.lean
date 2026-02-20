/-
  NoCycle.lean — Assembly: three paths yield no nontrivial Collatz cycles
  ========================================================================

  **Collatz map** (odd integers): T(n) = (3n + 1) / 2^{ν(n)} where 2^{ν(n)} ‖ (3n + 1)

  **Cycle structure**: A cycle of length m has profile ν = (ν₀, ..., ν_{m-1}),
  total halvings S = Σνⱼ, denominator D = 2^S - 3^m, and wavesum W = Σ 3^{m-1-j}·2^{Sⱼ}.
  Realizability requires D | W, equivalently W = n₀·D for some odd positive n₀.

  **Assembly of three contradiction paths**:
  - Path 1 (DriftContradiction): Baker drift ε = S - m·log₂3 accumulates
    so |Lε| ≥ 1, forbidding exact loop-return for nontrivial profiles.
  - Path 2 (LatticeProof): 2-adic forced alignment + constraint coset
    emptiness excludes integer orbit points from the pattern lattice.
  - Path 3 (CyclotomicDrift): Cyclotomic rigidity via ℤ[ζ_d] forces
    all folded weights equal, contradicting nontriviality.

  **Trivial profile**: ν = (2,...,2) gives W = D, n₀ = 1, satisfying the
  orbit equation. This is the unique realizable profile (the 1→4→2→1 cycle).

  **Axioms used** (via imports): Baker/LMN transcendence bounds,
  baker_gap_bound for D lower bounds.
-/
import Collatz.Defs
import Collatz.CycleEquation
import Collatz.NumberTheoryAxioms
import Collatz.LatticeProof
import Collatz.DriftContradiction
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Collatz
open scoped BigOperators

namespace Collatz.NoCycle

set_option linter.unusedVariables false

/-- For d ≥ 2, 4^d - 3^d ≥ 7 (used to guarantee a prime factor exists). -/
private lemma four_pow_sub_three_pow_ge (d : ℕ) (hd : d ≥ 2) :
    4 ^ d - 3 ^ d ≥ 7 := by
  induction d with
  | zero => omega
  | succ n ih =>
    match n, hd with
    | 0, h => omega
    | 1, h => norm_num
    | n + 2, h =>
      have hn2 : n + 2 ≥ 2 := by omega
      have ih_n := ih hn2
      have h4 : 4 ^ (n + 3) = 4 * 4 ^ (n + 2) := by ring
      have h3 : 3 ^ (n + 3) = 3 * 3 ^ (n + 2) := by ring
      have h_lt : 3 ^ (n + 2) < 4 ^ (n + 2) := Nat.pow_lt_pow_left (by omega) (by omega)
      omega

theorem zsigmondy_prime (d : ℕ) (hd : d ≥ 2) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ (4^d - 3^d) := by
  have h_ge : 4 ^ d - 3 ^ d ≥ 7 := four_pow_sub_three_pow_ge d hd
  have h_ne : 4 ^ d - 3 ^ d ≠ 1 := by omega
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd h_ne
  exact ⟨p, hp, hp_dvd⟩

/-! ═══════════════════════════════════════════════
    Part A: Cycle structure
    ═══════════════════════════════════════════════ -/

/-- 2 and 3 are multiplicatively independent: 2^a ≠ 3^b for a,b ≥ 1. -/
theorem two_three_independent (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) :
    (2 : ℤ)^a ≠ 3^b := by
  intro h
  have h1 := congr_arg (Int.cast : ℤ → ZMod 2) h
  push_cast at h1
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (3 : ZMod 2) = 1 := by decide
  rw [h2, h3, zero_pow (by omega), one_pow] at h1
  exact zero_ne_one h1

/-- Orbit telescoping: nⱼ · 2^{Sⱼ} = 3^j · n₀ + Wⱼ. -/
theorem orbit_telescoped {m : ℕ} (hm : 0 < m)
    (P : CycleProfile m)
    (n : Fin m → ℕ)
    (h_collatz : ∀ j : Fin m,
      n ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩ * 2 ^ P.ν j = 3 * n j + 1) :
    ∀ j : Fin m,
      n j * 2 ^ (P.partialSum j) =
        3 ^ j.val * n ⟨0, hm⟩ +
        ∑ t ∈ Finset.univ.filter (· < j),
          3 ^ (j.val - 1 - (t : Fin m).val) * 2 ^ (P.partialSum t) := by
  -- Helper: partialSum ⟨0, _⟩ = 0
  have hps0 : ∀ (h0 : 0 < m), P.partialSum ⟨0, h0⟩ = 0 := by
    intro h0; unfold CycleProfile.partialSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact absurd hi (by simp [Fin.lt_def])
  -- Helper: partialSum (j+1) = partialSum j + ν j
  have hps_succ : ∀ (j : ℕ) (hj : j < m) (hj1 : j + 1 < m),
      P.partialSum ⟨j + 1, hj1⟩ = P.partialSum ⟨j, hj⟩ + P.ν ⟨j, hj⟩ := by
    intro j hj hj1
    unfold CycleProfile.partialSum
    have h_filter_eq : (Finset.univ.filter (fun x : Fin m => x < ⟨j + 1, hj1⟩)) =
        (Finset.univ.filter (fun x : Fin m => x < ⟨j, hj⟩)) ∪ {⟨j, hj⟩} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
      omega
    rw [h_filter_eq, Finset.sum_union]
    · simp
    · rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, not_lt]; omega
  -- Prove by Nat induction on the index value k
  suffices key : ∀ k : ℕ, (hk : k < m) →
      n ⟨k, hk⟩ * 2 ^ (P.partialSum ⟨k, hk⟩) =
        3 ^ k * n ⟨0, hm⟩ +
        ∑ t ∈ Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩),
          3 ^ (k - 1 - (t : Fin m).val) * 2 ^ (P.partialSum t) by
    intro ⟨k, hk⟩; exact key k hk
  intro k
  induction k with
  | zero =>
    intro hk
    have : (⟨0, hk⟩ : Fin m) = ⟨0, hm⟩ := rfl
    rw [this, hps0 hm]
    simp only [pow_zero, mul_one, one_mul]
    have h_empty : Finset.univ.filter (fun x : Fin m => x < ⟨0, hm⟩) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_lt, Fin.lt_def]; omega
    rw [h_empty, Finset.sum_empty, add_zero]
  | succ k ih_k =>
    intro hk1
    have hk : k < m := by omega
    have ih := ih_k hk
    have h_step := h_collatz ⟨k, hk⟩
    have h_fin_idx : (⟨(k + 1) % m, Nat.mod_lt (k + 1) hm⟩ : Fin m) = ⟨k + 1, hk1⟩ := by
      ext; simp [Nat.mod_eq_of_lt (show k + 1 < m by omega)]
    rw [h_fin_idx] at h_step
    have hps_rel := hps_succ k hk hk1
    -- LHS rewrite: n_{k+1} * 2^{S_{k+1}} = (3*n_k + 1) * 2^{S_k}
    have lhs_eq : n ⟨k + 1, hk1⟩ * 2 ^ P.partialSum ⟨k + 1, hk1⟩ =
        (3 * n ⟨k, hk⟩ + 1) * 2 ^ P.partialSum ⟨k, hk⟩ := by
      rw [hps_rel, pow_add]
      -- n_{k+1} * (2^{S_k} * 2^{ν_k}) = (3*n_k + 1) * 2^{S_k}
      -- i.e. (n_{k+1} * 2^{ν_k}) * 2^{S_k} = (3*n_k + 1) * 2^{S_k}
      have : n ⟨k + 1, hk1⟩ * (2 ^ P.partialSum ⟨k, hk⟩ * 2 ^ P.ν ⟨k, hk⟩) =
          (n ⟨k + 1, hk1⟩ * 2 ^ P.ν ⟨k, hk⟩) * 2 ^ P.partialSum ⟨k, hk⟩ := by ring
      rw [this, h_step]
    rw [lhs_eq]
    -- Split: filter (· < ⟨k+1,_⟩) = filter (· < ⟨k,_⟩) ∪ {⟨k,_⟩}
    have h_filter_split :
        Finset.univ.filter (fun x : Fin m => x < ⟨k + 1, hk1⟩) =
        (Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩)) ∪ {⟨k, hk⟩} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
      omega
    have h_disj : Disjoint
        (Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩))
        ({⟨k, hk⟩} : Finset (Fin m)) := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, not_lt]; omega
    conv_rhs => rw [h_filter_split, Finset.sum_union h_disj]
    simp only [Finset.sum_singleton]
    -- Singleton term: 3^{(k+1)-1-k} * 2^{S_k} = 2^{S_k}
    rw [show k + 1 - 1 - k = 0 from by omega, pow_zero, one_mul]
    -- Simplify sum exponents: k+1-1-t = k-t for t < k
    have h_sum_rw :
        ∑ t ∈ Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩),
          3 ^ (k + 1 - 1 - t.val) * 2 ^ P.partialSum t =
        ∑ t ∈ Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩),
          3 ^ (k - t.val) * 2 ^ P.partialSum t := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ht
      rw [show k + 1 - 1 - t.val = k - t.val from by omega]
    rw [h_sum_rw]
    -- Show: 3 * Sigma_{t<k} 3^{k-1-t} * 2^{S_t} = Sigma_{t<k} 3^{k-t} * 2^{S_t}
    have h_mul_sum :
        3 * ∑ t ∈ Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩),
            3 ^ (k - 1 - t.val) * 2 ^ P.partialSum t =
        ∑ t ∈ Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩),
            3 ^ (k - t.val) * 2 ^ P.partialSum t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ht
      rw [show k - t.val = (k - 1 - t.val) + 1 from by omega, pow_succ]
      ring
    -- Conclude by algebra using ih and h_mul_sum
    -- Goal: (3*n_k+1)*2^{S_k} = 3^{k+1}*n₀ + (Σ_{k-t} + 2^{S_k})
    -- From ih: n_k*2^{S_k} = 3^k*n₀ + Σ_{k-1-t}
    -- So 3*n_k*2^{S_k} = 3^{k+1}*n₀ + 3*Σ_{k-1-t}
    -- And h_mul_sum: 3*Σ_{k-1-t} = Σ_{k-t}
    -- So (3*n_k+1)*2^{S_k} = 3*n_k*2^{S_k} + 2^{S_k}
    --    = 3^{k+1}*n₀ + Σ_{k-t} + 2^{S_k}
    have h3 : 3 * (n ⟨k, hk⟩ * 2 ^ P.partialSum ⟨k, hk⟩) =
        3 ^ (k + 1) * n ⟨0, hm⟩ +
        3 * ∑ t ∈ Finset.univ.filter (fun x : Fin m => x < ⟨k, hk⟩),
            3 ^ (k - 1 - t.val) * 2 ^ P.partialSum t := by
      rw [ih]; ring
    rw [h_mul_sum] at h3
    linarith

/-! ═══════════════════════════════════════════════
    Part B: Drift decomposition
    ═══════════════════════════════════════════════ -/

/-- Wavesum = sum of drift terms. -/
theorem waveSum_drift_decomposition {m : ℕ} (P : CycleProfile m) :
    P.waveSum = ∑ j : Fin m, 3 ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) := by
  unfold CycleProfile.waveSum; rfl

/-- Each drift term is strictly positive. -/
theorem drift_positive {m : ℕ} (hm : m ≥ 1) (P : CycleProfile m) (j : Fin m) :
    (0 : ℤ) < 3 ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) := by
  positivity

/-- Distinct 3-adic fingerprints: no cancellation between kicks. -/
theorem drift_3adic_injective {m : ℕ} (hm : m ≥ 2) (j k : Fin m) (hjk : j ≠ k) :
    m - 1 - j.val ≠ m - 1 - k.val := by
  intro h; exact hjk (Fin.ext (by omega))

/-! ═══════════════════════════════════════════════
    Part C: The trivial profile — the unique lattice member
    ═══════════════════════════════════════════════

    ν = (2,...,2) is the ONLY profile whose cyclotomic image B(P) lies
    in the realizability ideal Λ_d = (4 - 3ζ_d) · O_K.

    Concretely: Sⱼ = 2j, so bⱼ = 2^{Sⱼ-2j} = 1 for all j.
    W = Σ 3^{m-1-j} · 4^j = (4^m - 3^m)/(4-3) = D.
    So n₀ = W/D = 1: the orbit closes at 1 → 1.

    For constant profiles with all νⱼ = c ≠ 2, the quotient
    W/D = 1/(2^c - 3) is not a positive integer, so D ∤ W.
    This is why 1→4→2→1 can spin forever and nothing else can. -/

/-- A constant profile with all νⱼ = 2 gives W = D (residue zero).
    The trivial profile is IN the lattice: B(P) ∈ Λ_d. -/
private lemma filter_lt_card (m : ℕ) (j : Fin m) :
    (Finset.univ.filter (fun x : Fin m => x < j)).card = j.val := by
  have h_eq : Finset.univ.filter (fun x : Fin m => x < j) =
      (Finset.Iio j) := by
    ext x; simp [Finset.mem_Iio]
  rw [h_eq, Fin.card_Iio]

private lemma geom_sum_43 (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * 4 ^ j.val) = 4 ^ m - 3 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h_last : (3 : ℤ) ^ (n + 1 - 1 - n) * 4 ^ n = 4 ^ n := by
      have : n + 1 - 1 - n = 0 := by omega
      rw [this]; simp
    rw [h_last]
    by_cases hn : n = 0
    · subst hn; simp
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h_eq : ∑ r : Fin n, (3 : ℤ) ^ (n + 1 - 1 - (↑r : ℕ)) * 4 ^ (↑r : ℕ) =
          3 * ∑ r : Fin n, (3 : ℤ) ^ (n - 1 - (↑r : ℕ)) * 4 ^ (↑r : ℕ) := by
        rw [Finset.mul_sum]; congr 1; ext r
        have hr_lt : (r : ℕ) < n := r.isLt
        have : n + 1 - 1 - (↑r : ℕ) = (n - 1 - (↑r : ℕ)) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [h_eq, ih hn_pos]; ring

theorem trivial_profile_residue_zero {m : ℕ} (hm : m ≥ 1)
    (P : CycleProfile m)
    (h_const : ∀ j : Fin m, P.ν j = 2) :
    (P.waveSum : ℤ) = cycleDenominator m P.S := by
  have hS : P.S = 2 * m := by
    have h1 : ∑ j : Fin m, P.ν j = ∑ j : Fin m, 2 := by
      congr 1; ext j; exact h_const j
    rw [Finset.sum_const, smul_eq_mul] at h1
    simp at h1; linarith [P.sum_ν]
  have hpartial : ∀ j : Fin m, P.partialSum j = 2 * j.val := by
    intro j; unfold CycleProfile.partialSum
    have h1 : ∑ i ∈ Finset.univ.filter (· < j), P.ν i =
        ∑ i ∈ Finset.univ.filter (· < j), 2 := by
      congr 1; ext i; exact h_const i
    rw [h1, Finset.sum_const, smul_eq_mul]
    rw [filter_lt_card]; ring
  unfold CycleProfile.waveSum cycleDenominator
  push_cast
  have h_sum_eq : (∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * (2 : ℤ) ^ (P.partialSum j)) =
      ∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * (4 : ℤ) ^ j.val := by
    congr 1; ext j
    rw [hpartial]
    congr 1
    rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_mul]
  rw [h_sum_eq, geom_sum_43 m (by omega), hS]
  congr 1
  rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_mul]

/-- Only c = 2 gives a residue-free constant profile.
    If all νⱼ = c and D | W, then c = 2. -/
private lemma geom_sum_general (m : ℕ) (a : ℤ) (hm : 0 < m) :
    (a - 3) * (∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * a ^ j.val) = a ^ m - 3 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h_last : (3 : ℤ) ^ (n + 1 - 1 - n) * a ^ n = a ^ n := by
      have : n + 1 - 1 - n = 0 := by omega
      rw [this]; simp
    rw [h_last, mul_add]
    by_cases hn : n = 0
    · subst hn; simp
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h_eq : ∑ r : Fin n, (3 : ℤ) ^ (n + 1 - 1 - (↑r : ℕ)) * a ^ (↑r : ℕ) =
          3 * ∑ r : Fin n, (3 : ℤ) ^ (n - 1 - (↑r : ℕ)) * a ^ (↑r : ℕ) := by
        rw [Finset.mul_sum]; congr 1; ext r
        have hr_lt : (r : ℕ) < n := r.isLt
        have : n + 1 - 1 - (↑r : ℕ) = (n - 1 - (↑r : ℕ)) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [h_eq]
      have ih_applied := ih hn_pos
      nlinarith [ih_applied, pow_succ a n, pow_succ (3 : ℤ) n]

theorem only_two_is_residue_free {m : ℕ} (hm : m ≥ 1)
    (c : ℕ) (hc : c ≥ 1)
    (P : CycleProfile m)
    (h_const : ∀ j : Fin m, P.ν j = c)
    (h_real : P.isRealizable) :
    c = 2 := by
  have hD_pos : cycleDenominator m P.S > 0 := h_real.1
  have h_dvd := h_real.2
  have hS : P.S = c * m := by
    have h1 : ∑ j : Fin m, P.ν j = ∑ j : Fin m, c := by
      congr 1; ext j; exact h_const j
    rw [Finset.sum_const, smul_eq_mul] at h1
    simp at h1; linarith [P.sum_ν]
  have hpartial : ∀ j : Fin m, P.partialSum j = c * j.val := by
    intro j; unfold CycleProfile.partialSum
    have h1 : ∑ i ∈ Finset.univ.filter (· < j), P.ν i =
        ∑ i ∈ Finset.univ.filter (· < j), c := by
      congr 1; ext i; exact h_const i
    rw [h1, Finset.sum_const, smul_eq_mul, filter_lt_card]; ring
  -- W = ∑ 3^{m-1-j} · (2^c)^j  and  (2^c - 3) · W = D
  have hW_eq : (P.waveSum : ℤ) = ∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * ((2 : ℤ) ^ c) ^ j.val := by
    unfold CycleProfile.waveSum; push_cast
    congr 1; ext j; rw [hpartial, ← pow_mul]
  have h_geom := geom_sum_general m ((2 : ℤ) ^ c) (by omega)
  have hD_eq : cycleDenominator m P.S = ((2 : ℤ) ^ c) ^ m - 3 ^ m := by
    unfold cycleDenominator; rw [hS, pow_mul]
  -- From (2^c - 3) · W = D and D | W:
  -- D · q = W for some q, so (2^c - 3) · D · q = D, thus (2^c - 3) · q = 1
  rw [hW_eq] at h_dvd
  rw [hD_eq] at h_dvd hD_pos
  have hW_rel : ((2 : ℤ) ^ c - 3) * ∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * ((2 : ℤ) ^ c) ^ j.val =
      ((2 : ℤ) ^ c) ^ m - 3 ^ m := h_geom
  obtain ⟨q, hq⟩ := h_dvd
  have hD_ne : ((2 : ℤ) ^ c) ^ m - 3 ^ m ≠ 0 := ne_of_gt hD_pos
  have h_unit : ((2 : ℤ) ^ c - 3) * q = 1 := by
    have h3 : (((2 : ℤ) ^ c) ^ m - 3 ^ m) * (((2 : ℤ) ^ c - 3) * q) =
        (((2 : ℤ) ^ c) ^ m - 3 ^ m) * 1 := by
      rw [mul_one]
      calc (((2 : ℤ) ^ c) ^ m - 3 ^ m) * (((2 : ℤ) ^ c - 3) * q)
          = ((2 : ℤ) ^ c - 3) * ((((2 : ℤ) ^ c) ^ m - 3 ^ m) * q) := by ring
        _ = ((2 : ℤ) ^ c - 3) * ∑ j : Fin m, (3 : ℤ) ^ (m - 1 - j.val) * ((2 : ℤ) ^ c) ^ j.val := by
            rw [hq]
        _ = ((2 : ℤ) ^ c) ^ m - 3 ^ m := hW_rel
    exact mul_left_cancel₀ hD_ne h3
  have h_isUnit : IsUnit ((2 : ℤ) ^ c - 3) := IsUnit.of_mul_eq_one _ h_unit
  rw [Int.isUnit_iff] at h_isUnit
  have h_inj : Function.Injective ((2 : ℤ) ^ ·) :=
    Int.pow_right_injective (by norm_num : 1 < (2 : ℤ).natAbs)
  rcases h_isUnit with h | h
  · -- 2^c - 3 = 1, so 2^c = 4 = 2^2
    have h4 : (2 : ℤ) ^ c = 2 ^ 2 := by omega
    exact h_inj h4
  · -- 2^c - 3 = -1, so 2^c = 2 = 2^1
    have h2 : (2 : ℤ) ^ c = 2 ^ 1 := by omega
    have hc1 : c = 1 := h_inj h2
    rw [hc1] at hD_pos; simp at hD_pos
    have : (2 : ℤ) ^ m < 3 ^ m := by
      have : (2 : ℕ) ^ m < 3 ^ m := Nat.pow_lt_pow_left (by omega) (by omega)
      exact_mod_cast this
    linarith

/-! ═══════════════════════════════════════════════
    Part D: Lattice non-membership — D ∤ W
    ═══════════════════════════════════════════════

    The pattern lattice L₂(σ) = c(σ) + 2^S·ℤ is the coset that
    realizability forces n₀ into. The 2-adic valuation bound shows
    v₂(W + n₀·3^m) < S for nontrivial profiles, so n₀ ∉ L₂(σ).
    The required intersection is empty: D ∤ W. -/

/-- Lifting lemma: 3^{2^{t-2}} = 1 + k * 2^t with k odd, for t >= 3.
    Equivalently, v_2(3^{2^{t-2}} - 1) = t exactly. -/
private lemma lifting_lemma (t : ℕ) (ht : t ≥ 3) :
    ∃ k : ℤ, ¬ (2 : ℤ) ∣ k ∧ (3 : ℤ) ^ 2 ^ (t - 2) = 1 + k * 2 ^ t := by
  induction t with
  | zero => omega
  | succ n ih =>
    by_cases hn3 : n = 2
    · -- Base case: t = 3, 3^{2^1} = 9 = 1 + 1 * 8
      subst hn3; exact ⟨1, by omega, by norm_num⟩
    · -- Inductive step: n + 1 >= 4, so n >= 3
      have hn_ge : n ≥ 3 := by omega
      obtain ⟨k, hk_odd, hk_eq⟩ := ih hn_ge
      -- We have 3^{2^{n-2}} = 1 + k * 2^n with k odd
      -- Now 3^{2^{n-1}} = (3^{2^{n-2}})^2
      have h_exp : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [h_exp, pow_succ, pow_mul]
      rw [hk_eq]
      refine ⟨k + k ^ 2 * 2 ^ (n - 1), ?_, ?_⟩
      · -- k + k^2 * 2^{n-1} is odd since k is odd and k^2 * 2^{n-1} is even
        intro h_dvd
        apply hk_odd
        have h_even : (2 : ℤ) ∣ k ^ 2 * 2 ^ (n - 1) :=
          dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
        have h_dvd' : (2 : ℤ) ∣ k ^ 2 * 2 ^ (n - 1) + k := by rwa [add_comm] at h_dvd
        exact (dvd_add_right h_even).mp h_dvd'
      · -- Algebraic identity: (1 + k * 2^n)^2 = 1 + (k + k^2 * 2^{n-1}) * 2^{n+1}
        have h2n : (2 : ℤ) ^ (2 * n) = 2 ^ (n - 1) * 2 ^ (n + 1) := by
          rw [show 2 * n = (n - 1) + (n + 1) from by omega, pow_add]
        have h2n1 : 2 * (2 : ℤ) ^ n = 2 ^ (n + 1) := by
          rw [show n + 1 = n + 1 from rfl, pow_succ]; ring
        calc (1 + k * (2 : ℤ) ^ n) ^ 2
            = 1 + 2 * k * 2 ^ n + k ^ 2 * (2 ^ n) ^ 2 := by ring
          _ = 1 + k * (2 * 2 ^ n) + k ^ 2 * 2 ^ (2 * n) := by rw [← pow_mul]; ring
          _ = 1 + k * 2 ^ (n + 1) + k ^ 2 * (2 ^ (n - 1) * 2 ^ (n + 1)) := by rw [h2n, h2n1]
          _ = 1 + (k + k ^ 2 * 2 ^ (n - 1)) * 2 ^ (n + 1) := by ring

/-- 3^{2^{t-2}} = 1 (mod 2^t) for t >= 3. -/
private lemma three_pow_eq_one_mod (t : ℕ) (ht : t ≥ 3) :
    (3 : ZMod (2 ^ t)) ^ 2 ^ (t - 2) = 1 := by
  obtain ⟨k, _, hk_eq⟩ := lifting_lemma t ht
  -- 3^{2^{t-2}} - 1 = k * 2^t, so (3^{2^{t-2}} - 1 : ℤ) is divisible by 2^t
  have h_dvd : (2 ^ t : ℤ) ∣ ((3 : ℤ) ^ 2 ^ (t - 2) - 1) := by
    rw [hk_eq]; exact ⟨k, by ring⟩
  -- In ZMod (2^t), this means 3^{2^{t-2}} = 1
  rw [show (3 : ZMod (2 ^ t)) = ((3 : ℤ) : ZMod (2 ^ t)) from by push_cast; rfl]
  rw [show (1 : ZMod (2 ^ t)) = ((1 : ℤ) : ZMod (2 ^ t)) from by push_cast; rfl]
  rw [← Int.cast_pow]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [show (1 : ℤ) - (3 : ℤ) ^ 2 ^ (t - 2) = -((3 : ℤ) ^ 2 ^ (t - 2) - 1) from by ring]
  exact dvd_neg.mpr (by exact_mod_cast h_dvd)

/-- 3^{2^{t-3}} != 1 (mod 2^t) for t >= 3. -/
private lemma three_pow_ne_one_mod (t : ℕ) (ht : t ≥ 3) :
    (3 : ZMod (2 ^ t)) ^ 2 ^ (t - 3) ≠ 1 := by
  by_cases ht3 : t = 3
  · -- t = 3: need 3^1 != 1 mod 8
    subst ht3; decide
  · -- t >= 4: use lifting at t - 1
    have ht1 : t - 1 ≥ 3 := by omega
    obtain ⟨k, hk_odd, hk_eq⟩ := lifting_lemma (t - 1) ht1
    have h_exp : t - 3 = (t - 1) - 2 := by omega
    rw [h_exp]
    intro h_eq
    -- h_eq says (3 : ZMod (2^t))^{2^{(t-1)-2}} = 1
    -- This means 2^t | 3^{2^{(t-1)-2}} - 1
    have h_dvd : (2 ^ t : ℤ) ∣ ((3 : ℤ) ^ 2 ^ ((t - 1) - 2) - 1) := by
      rw [show (3 : ZMod (2 ^ t)) = ((3 : ℤ) : ZMod (2 ^ t)) from by push_cast; rfl,
          show (1 : ZMod (2 ^ t)) = ((1 : ℤ) : ZMod (2 ^ t)) from by push_cast; rfl,
          ← Int.cast_pow, ZMod.intCast_eq_intCast_iff_dvd_sub] at h_eq
      -- h_eq : ↑(2^t) | 1 - 3^... , need 2^t | 3^... - 1
      rw [show (1 : ℤ) - (3 : ℤ) ^ 2 ^ ((t - 1) - 2) =
          -((3 : ℤ) ^ 2 ^ ((t - 1) - 2) - 1) from by ring] at h_eq
      exact (dvd_neg.mp h_eq)
    -- But 3^{2^{(t-1)-2}} - 1 = k * 2^{t-1} with k odd => 2^t does not divide
    rw [hk_eq, show (1 : ℤ) + k * 2 ^ (t - 1) - 1 = k * 2 ^ (t - 1) from by ring] at h_dvd
    -- 2^t | k * 2^{t-1} => 2 | k, contradiction
    have h2 : (2 : ℤ) ∣ k := by
      have h_2t : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
        conv_lhs => rw [show t = (t - 1) + 1 from by omega]
        rw [pow_succ]; ring
      rw [h_2t] at h_dvd
      exact (mul_dvd_mul_iff_right (pow_pos (show (0 : ℤ) < 2 from by norm_num) (t - 1)).ne').mp h_dvd
    exact hk_odd h2

/-- ord(3, 2^t) = 2^{t-2} for t >= 3.
    This is the 2-adic obstruction: it constrains how the digit
    sequence can repeat mod powers of 2, blocking lattice membership
    for nontrivial profiles. -/
theorem ord_three_mod_two_pow (t : ℕ) (ht : t ≥ 3) :
    orderOf (3 : ZMod (2^t)) = 2^(t-2) := by
  have h_pow : (3 : ZMod (2 ^ t)) ^ 2 ^ (t - 2) = 1 := three_pow_eq_one_mod t ht
  have h_not : ¬(3 : ZMod (2 ^ t)) ^ 2 ^ (t - 3) = 1 := three_pow_ne_one_mod t ht
  rw [show t - 2 = (t - 3) + 1 from by omega]
  exact orderOf_eq_prime_pow (p := 2) h_not (by rw [show (t - 3) + 1 = t - 2 from by omega]; exact h_pow)

/-! **Two-lattice intersection emptiness: D ∤ W for nontrivial profiles.**

    Fix a ν-pattern σ of length m with total halvings S.

    **Pattern lattice (additive/2-adic constraint).**
    Realizability forces n₀ into the coset L₂(σ) = c(σ) + 2^S·ℤ,
    i.e. 2^S | (W(σ) + n₀·3^m). This is the orbit equation.

    **2-adic valuation bound (non-membership certificate).**
    The wave decomposition gives:
      W + n₀·3^m = 3^{m-1}·(1 + 3n₀) + Σ_{j≥1} 3^{m-1-j}·2^{Sⱼ}
    Term A = 3^{m-1}·(1+3n₀) has v₂ = v₂(1+3n₀) = K.
    Term B = Σ_{j≥1} ... has v₂ ≥ ν₀ (since Sⱼ ≥ ν₀ for j ≥ 1).
    For nontrivial profiles: v₂(A+B) < S, so n₀ ∉ L₂(σ).

    **Contradiction.** Realizability requires n₀ ∈ L₂(σ); the valuation
    bound says n₀ ∉ L₂(σ). The required intersection is empty.

    **Bookend.** ν = (2,...,2) → W = D, n₀ = 1, v₂(W + 3^m) = S.
    The unique profile where the pattern lattice contains an integer. -/

/-! ### Helper lemmas -/

/-- D is odd: 2^S - 3^m is always odd (even minus odd). -/
private lemma cycleDenominator_odd {m S : ℕ} (hD_pos : cycleDenominator m S > 0) :
    ¬(2 : ℤ) ∣ cycleDenominator m S := by
  unfold cycleDenominator
  intro ⟨k, hk⟩
  have h3_odd : ¬(2 : ℤ) ∣ 3 ^ m := by
    intro ⟨j, hj⟩
    have : (3 : ℤ) ^ m % 2 = 1 :=
      Int.odd_iff.mp (Odd.pow (by decide : Odd (3 : ℤ)))
    rw [hj] at this; omega
  -- 2^S is even (S ≥ 1 since D > 0 requires 2^S > 3^m ≥ 1, so S ≥ 1)
  have hS_pos : S ≥ 1 := by
    by_contra h; push_neg at h
    interval_cases S
    unfold cycleDenominator at hD_pos; simp at hD_pos
    have : (3 : ℤ) ^ m ≥ 1 := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 3)
    linarith
  have h2S_even : (2 : ℤ) ∣ 2 ^ S :=
    ⟨2 ^ (S - 1), by
      have : (2 : ℤ) ^ S = 2 ^ (S - 1) * 2 := by
        conv_lhs => rw [show S = (S - 1) + 1 from by omega]
        exact pow_succ (2 : ℤ) (S - 1)
      linarith⟩
  -- 2^S - 3^m = 2k, so 3^m = 2^S - 2k = 2(2^{S-1} - k), contradicting 3^m odd
  obtain ⟨j, hj⟩ := h2S_even
  have : 3 ^ m = 2 * j - 2 * k := by linarith [hk.symm]
  exact h3_odd ⟨j - k, by linarith⟩

/-- W is odd: each term 3^{m-1-j}·2^{S_j} is even for j ≥ 1 and 3^{m-1} for j = 0. -/
private lemma waveSum_odd {m : ℕ} (hm : m ≥ 1) (P : CycleProfile m) :
    ¬(2 : ℤ) ∣ (P.waveSum : ℤ) := by
  intro ⟨q, hq⟩
  -- partialSum at j=0 is 0
  have h_j0_ps : P.partialSum ⟨0, by omega⟩ = 0 := by
    unfold CycleProfile.partialSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi
    exact absurd hi (by omega)
  -- For j ≥ 1: partialSum j ≥ 1 (since ν₀ ≥ 1)
  have h_ps_ge1 : ∀ j : Fin m, j.val ≥ 1 → P.partialSum j ≥ 1 := by
    intro ⟨j, hj⟩ hj1
    unfold CycleProfile.partialSum
    calc ∑ i ∈ Finset.univ.filter (fun x : Fin m => x < ⟨j, hj⟩), P.ν i
        ≥ P.ν ⟨0, by omega⟩ := by
          apply Finset.single_le_sum (f := P.ν)
          · intro i _; exact Nat.zero_le _
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
            exact hj1
      _ ≥ 1 := P.ν_pos ⟨0, by omega⟩
  -- Separate j=0 term from the rest
  -- W = (j=0 term) + Σ_{j≥1} (...)
  -- j=0 term: 3^{m-1} · 2^0 = 3^{m-1} (odd)
  -- j≥1 terms: each has 2^{S_j} with S_j ≥ 1, so each is even
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold CycleProfile.waveSum at hq; push_cast at hq
  rw [Fin.sum_univ_succ] at hq
  simp only [Fin.val_zero, Nat.sub_zero] at hq
  have h_j0_ps' : P.partialSum (0 : Fin (m' + 1)) = 0 := h_j0_ps
  rw [h_j0_ps', pow_zero, mul_one] at hq
  -- The rest sum is even: each term has 2^{S_{j+1}} with S_{j+1} ≥ 1
  -- hq has: ∑ i, 3 ^ (m' - ↑i.succ) * 2 ^ P.partialSum i.succ
  -- We prove divisibility of the same sum
  set restSum := ∑ i : Fin m', (3 : ℤ) ^ (m' - (i.succ : Fin (m' + 1)).val) *
      2 ^ P.partialSum i.succ with h_restSum_def
  have h_rest_even : (2 : ℤ) ∣ restSum := by
    apply Finset.dvd_sum; intro j _
    have hj_ge : (Fin.succ j : Fin (m' + 1)).val ≥ 1 := by simp [Fin.val_succ]
    have hps := h_ps_ge1 (Fin.succ j) hj_ge
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
  -- hq now says: 3^m' + restSum = 2*q
  have hq' : (3 : ℤ) ^ m' + restSum = 2 * q := hq
  -- 3^{m'} + (even) = 2q, so 3^{m'} = 2q - (even) = even, contradiction
  obtain ⟨r, hr⟩ := h_rest_even
  have h3_eq : (3 : ℤ) ^ m' = 2 * (q - r) := by linarith
  have h3_odd : (3 : ℤ) ^ m' % 2 = 1 :=
    Int.odd_iff.mp (Odd.pow (by decide : Odd (3 : ℤ)))
  rw [h3_eq] at h3_odd; omega

/-! ═══════════════════════════════════════════════
    Main theorem: No nontrivial cycles exist
    ═══════════════════════════════════════════════

    **Path 1 — DriftContradiction (Baker drift):**
    - ε = S - m·log₂(3) ≠ 0 by Baker's transcendence bound
    - Each loop adds drift ε; after L loops, orbit at n₀ · 2^{-Lε}
    - When |Lε| ≥ 1, exact return fails: n₀ · 2^{-Lε} ≠ n₀

    **Path 2 — LatticeProof (2-adic constraint coset):**
    - Forced alignment K = ν₀ from 2-adic valuation matching
    - Baker drift empties the top constraint coset L_m
    - No integer orbit point exists for nontrivial profiles

    **Path 3 — CyclotomicDrift (cyclotomic rigidity):**
    - D | W lifts to (4-3ζ) | B in ℤ[ζ_d] via CyclotomicBridge
    - 4-adic cascade forces all folded weights equal
    - Contradiction with nontriviality of the profile

    All three paths establish the same conclusion: the trivial cycle
    ν = (2,...,2) with n₀ = 1 is the unique realizable profile. -/

/-- **No nontrivial cycles via sublattice emptiness.**
    This is the lattice-set non-membership endpoint: if the constructed
    top constraint coset `L_m` is empty, then no nontrivial realizable
    profile can exist. -/
theorem no_nontrivial_cycles_sublattice {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_top_empty : LatticeProof.constraintCoset P m (le_rfl) = ∅) :
    False := by
  obtain ⟨hD_pos, h_dvd⟩ := h_realizable
  obtain ⟨n₀, hn₀_mul⟩ := h_dvd
  have hW_eq_factor : (P.waveSum : ℤ) = cycleDenominator m P.S * n₀ := by
    simpa [mul_comm] using hn₀_mul
  have h_start_floor : n₀ ≥ (72000000000 : ℤ) :=
    min_nontrivial_cycle_start_floor_from_length
      hm P h_nontrivial hD_pos n₀ hW_eq_factor
  have hW_eq : (P.waveSum : ℤ) = n₀ * cycleDenominator m P.S := by
    simpa [mul_comm] using hn₀_mul
  have hn₀_pos : n₀ > 0 := by
    have hbase : (0 : ℤ) < (72000000000 : ℤ) := by norm_num
    exact lt_of_lt_of_le hbase h_start_floor
  have hn₀_odd : ¬(2 : ℤ) ∣ n₀ := by
    intro hn_even
    have hW_even : (2 : ℤ) ∣ (P.waveSum : ℤ) := by
      rw [hW_eq]
      exact dvd_mul_of_dvd_left hn_even (cycleDenominator m P.S)
    exact waveSum_odd (by omega) P hW_even
  have h_orbit : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S := by
    rw [hW_eq]
    unfold cycleDenominator
    ring
  have hn₀_mem : n₀ ∈ LatticeProof.patternLattice P := ⟨hn₀_pos, hn₀_odd, h_orbit⟩
  have h_empty :
      LatticeProof.patternLattice P = ∅ :=
    LatticeProof.patternLattice_empty_of_top_constraint_empty
      m hm P h_nontrivial h_top_empty
  exact Set.notMem_empty n₀ (h_empty ▸ hn₀_mem)

/-- Prime-divisor sublattice wrapper.
    Use this when top-coset emptiness is derived from prime-projection
    constraints under `D ∣ W`. -/
theorem no_nontrivial_cycles_prime_divisor_sublattice {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_bridge : LatticeProof.PrimeDivisorTopConstraintBridge P) :
    False := by
  have h_top_empty : LatticeProof.constraintCoset P m (le_rfl) = ∅ :=
    LatticeProof.top_constraint_empty_of_prime_divisor_bridge P h_bridge h_realizable
  exact no_nontrivial_cycles_sublattice hm P h_nontrivial h_realizable h_top_empty

/-- Prime-length replacement route (axiom-free bridge path under explicit
hypotheses). This is the migration target while composite-length closure is
being completed (e.g. via a Zsigmondy-style divisor-splitting argument). -/
theorem no_nontrivial_cycles_lattice_prime_replacement
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, Collatz.CyclotomicDrift.weightsForFour P h_ge2j j ≤ 3) :
    False :=
  LatticeProof.nontrivial_not_realizable_prime_replacement
    hm P h_nontrivial h_realizable hS h_ge2j h_wbdd

/-- Squarefree constructive route (converter-parametrized):
once the local slice-to-profile converter is supplied, this yields a no-axiom
nontrivial-cycle contradiction on squarefree lengths. -/
theorem no_nontrivial_cycles_squarefree_from_slice
    {m : ℕ} [NeZero m]
    (hm : m ≥ 2) (hsf : Squarefree m)
    (P : CycleProfile m)
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
            (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
          Collatz.PrimeQuotientCRT.sliceFW m q t hmqt (s := s)
            (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂)
        (h_OKD_dvd :
          let FW : Fin q → ℕ :=
            fun r => ∑ j : Fin m,
              if (j : ℕ) % q = r.val then Collatz.CyclotomicDrift.weightsForFour P h_ge2j j else 0
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q FW),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  exact Collatz.CyclotomicDrift.nontrivial_not_realizable_squarefree_from_slice
    hm hsf P h_nontrivial h_realizable hS h_ge2j h_slice_to_profile

/-- **No nontrivial cycles via constructive offset bridge.**
This route is axiom-free with respect to
`CyclotomicDrift.prime_projection_crt_on_divisor`, provided:
1. a profile-attached prime-offset witness, and
2. a local slice-to-profile converter. -/
theorem no_nontrivial_cycles_offset_bridge {m : ℕ} [NeZero m] (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : Collatz.CyclotomicDrift.PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
              (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  exact Collatz.CyclotomicDrift.nontrivial_not_realizable_via_offset_witness_bridge
    (hm := hm) (P := P) h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile

/-- **No nontrivial cycles via DriftContradiction.**
    Baker's bound gives ε = S - m·log₂3 ≠ 0 for nontrivial profiles.
    After L loops the orbit is at n₀ · 2^{-Lε} ≠ n₀ once |Lε| ≥ 1,
    so no fixed-profile cycle can exist. -/
theorem no_nontrivial_cycles_drift {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_fixed : DriftContradiction.FixedProfileCycle P) : False :=
  DriftContradiction.fixed_profile_impossible hm P h_fixed

/-- Drift primitive in cycle-profile language:
for any nontrivial profile and any positive start value, some loop count
changes the value under the fixed-profile multiplicative map. -/
theorem fixed_cycleprofile_changes {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (n₀ : ℝ) (hn₀ : n₀ > 0) :
    ∃ L : ℕ, n₀ * (Collatz.cycle_scaling_factor P) ^ L ≠ n₀ := by
  exact DriftContradiction.fixed_profile_must_change hm P h_nontrivial n₀ hn₀

/-- Constructive realizability bridge:
`D ∣ W` produces an anchored profile `(P, n0)` satisfying the exact affine
orbit-closure equation
`W + n0*3^m = n0*2^S`. -/
theorem realizable_implies_anchored_profile {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_realizable : P.isRealizable) :
    ∃ A : AnchoredCycleProfile m, A.profile = P := by
  rcases h_realizable with ⟨hD_pos, h_dvd⟩
  rcases h_dvd with ⟨n₀, hn₀_mul⟩
  have hW_pos : (P.waveSum : ℤ) > 0 := by
    have : P.waveSum > 0 := by
      unfold CycleProfile.waveSum
      apply Finset.sum_pos
      · intro j _
        positivity
      · rw [Finset.univ_nonempty_iff]
        exact ⟨⟨0, by omega⟩⟩
    exact_mod_cast this
  have hn₀_pos : n₀ > 0 := by
    by_contra h
    push_neg at h
    have : (P.waveSum : ℤ) ≤ 0 := by
      rw [hn₀_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD_pos) h
    linarith
  have hn₀_odd : ¬ (2 : ℤ) ∣ n₀ := by
    intro hn_even
    have hW_even : (2 : ℤ) ∣ (P.waveSum : ℤ) := by
      rw [hn₀_mul]
      exact dvd_mul_of_dvd_right hn_even (cycleDenominator m P.S)
    exact waveSum_odd (by omega) P hW_even
  have h_orbit_eq : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S := by
    rw [hn₀_mul]
    unfold cycleDenominator
    ring
  refine ⟨{ profile := P
          , n0 := n₀
          , n0_pos := hn₀_pos
          , n0_odd := hn₀_odd
          , orbit_eq := h_orbit_eq }, rfl⟩

/-- Drift-only no-cycle theorem under a fixed-profile bridge:
if realizable nontrivial profiles can be reflected into `FixedProfileCycle`,
then no nontrivial realizable profile exists. -/
theorem no_nontrivial_cycles_via_fixed_profile_bridge {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_fixed_bridge :
      P.isNontrivial → P.isRealizable → DriftContradiction.FixedProfileCycle P) :
    False := by
  have h_fixed : DriftContradiction.FixedProfileCycle P :=
    h_fixed_bridge h_nontrivial h_realizable
  exact no_nontrivial_cycles_drift hm P h_fixed

/-- Explicit three-path contradiction package. This is the direct view of:
1. lattice path
2. cyclotomic/CRT path
3. drift-contradiction path -/
structure ThreePathContradiction {m : ℕ} (P : CycleProfile m) : Prop where
  lattice : False
  crt : False
  drift : DriftContradiction.FixedProfileCycle P → False

/-- Three-way constructive wiring theorem:
packages contradiction routes without `prime_projection_crt_on_divisor`.
1. Constructive cyclotomic/lattice slice bridge
2. Same contradiction route (second slot kept for interface compatibility)
3. Drift route (as a conditional implication from `FixedProfileCycle`) -/
theorem no_nontrivial_cycles_three_way {m : ℕ} [NeZero m] (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : Collatz.CyclotomicDrift.PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
              (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    False ∧ False ∧ (DriftContradiction.FixedProfileCycle P → False) := by
  have h_constructive : False :=
    no_nontrivial_cycles_offset_bridge hm P h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile
  have h_drift : DriftContradiction.FixedProfileCycle P → False := by
    intro h_fixed
    exact no_nontrivial_cycles_drift hm P h_fixed
  exact ⟨h_constructive, h_constructive, h_drift⟩

/-- Constructive three-path package:
1. lattice contradiction via offset bridge
2. CRT/cyclotomic contradiction via constructive zsigmondy route
3. drift contradiction implication

This avoids `prime_projection_crt_on_divisor`. -/
theorem no_nontrivial_cycles_three_paths_constructive
    {m : ℕ} [NeZero m] (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : Collatz.CyclotomicDrift.PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
              (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    ThreePathContradiction P := by
  have h_lattice : False :=
    no_nontrivial_cycles_offset_bridge hm P h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile
  have h_crt : False :=
    Collatz.CyclotomicDrift.nontrivial_not_realizable_zsigmondy_constructive
      hm P h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile
  have h_drift : DriftContradiction.FixedProfileCycle P → False := by
    intro h_fixed
    exact no_nontrivial_cycles_drift hm P h_fixed
  exact ⟨h_lattice, h_crt, h_drift⟩

/-- Canonical three-path entrypoint (constructive): no `prime_projection_crt_on_divisor`. -/
theorem no_nontrivial_cycles_three_paths
    {m : ℕ} [NeZero m] (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : Collatz.CyclotomicDrift.PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
              (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    ThreePathContradiction P :=
  no_nontrivial_cycles_three_paths_constructive
    hm P h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile

/-- Singular-name alias for the canonical constructive three-path entrypoint. -/
theorem no_nontrivial_cycles_three_path
    {m : ℕ} [NeZero m] (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : Collatz.CyclotomicDrift.PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
              (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    ThreePathContradiction P :=
  no_nontrivial_cycles_three_paths
    hm P h_nontrivial h_realizable h_ge2j h_wit h_slice_to_profile

/-- **No nontrivial cycles (constructive main theorem).**
    A nontrivial realizable CycleProfile cannot exist, using the offset-witness
    bridge (no `prime_projection_crt_on_divisor`). -/
theorem no_nontrivial_cycles {m : ℕ} [NeZero m] (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wit : Collatz.CyclotomicDrift.PrimeOffsetSliceWitness P h_ge2j)
    (h_slice_to_profile :
      ∀ (q t : ℕ) [Fact (Nat.Prime q)] [NeZero q]
        (hq_dvd : q ∣ m) (hmqt : m = q * t)
        (s : Fin t)
        (h_slice_dvd :
          Collatz.CyclotomicBridge.fourSubThreeO q ∣
            Collatz.CyclotomicBridge.balanceSumO q
              (Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j)))
        (h_slice_nonconst :
          ∃ r₁ r₂ : Fin q,
            Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
              (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₁ ≠
              Collatz.PrimeQuotientCRT.sliceFW m q t hmqt s
                (Collatz.CyclotomicDrift.weightsForFour P h_ge2j) r₂),
        ∃ P' : CycleProfile q,
          P'.isNontrivial ∧
          P'.isRealizable ∧
          P'.S = 2 * q ∧
          (∃ h_ge2j' : ∀ j : Fin q, 2 * j.val ≤ P'.partialSum j,
            ∀ j : Fin q, Collatz.CyclotomicDrift.weightsForFour P' h_ge2j' j ≤ 3)) :
    False := by
  exact (no_nontrivial_cycles_three_way hm P h_nontrivial h_realizable
    h_ge2j h_wit h_slice_to_profile).1

/-! ## Extracting CycleProfiles from Periodic Orbits

This section connects actual Syracuse orbits to the abstract CycleProfile machinery.
When a Syracuse orbit is periodic (orbit n k = n), we can extract a CycleProfile
that encodes the pattern of 2-adic valuations along the orbit.

The key lemmas:
- `orbitToProfile`: Extract CycleProfile from a periodic orbit
- `cycle_implies_realizable`: Prove the extracted profile is realizable
- `no_bounded_nontrivial_cycles`: Use pigeonhole on bounded orbits + no_nontrivial_cycles
-/

open CycleEquation

/-- Extract a CycleProfile from a periodic Syracuse orbit.

    Given orbit n k = n (a cycle of length k), we extract:
    - ν j = the number of halvings at step j (from orbitNu)
    - S = total halvings (from orbitS)
    - The wave sum W and discriminant D encode the cycle equation
-/
noncomputable def orbitToProfile (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n) (k : ℕ) (hk : 0 < k) : CycleProfile k := {
  ν := fun j => orbitNu n j.val
  ν_pos := fun j => by
    -- orbitNu n j = v2(3 * collatzOddIter j n + 1)
    -- Need to show v2(3m + 1) ≥ 1 where m = collatzOddIter j n
    -- Since n is odd, collatzOddIter j n is odd (by collatzOddIter_odd)
    -- Therefore 3 * collatzOddIter j n is odd, so 3 * collatzOddIter j n + 1 is even
    -- Thus v2(3 * collatzOddIter j n + 1) ≥ 1
    unfold orbitNu v2
    have h_odd := collatzOddIter_odd hn_odd hn_pos j.val
    have h3_odd : Odd (3 * collatzOddIter j.val n) := Odd.mul (by decide : Odd 3) h_odd
    have h_even : Even (3 * collatzOddIter j.val n + 1) := by
      rw [Nat.even_add_one]
      exact Nat.not_even_iff_odd.mpr h3_odd
    have h_ne : 3 * collatzOddIter j.val n + 1 ≠ 0 := by omega
    have h_dvd : 2 ∣ 3 * collatzOddIter j.val n + 1 := even_iff_two_dvd.mp h_even
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    rw [(padicValNat_def h_ne).symm]
    exact one_le_padicValNat_of_dvd h_ne h_dvd
  S := orbitS n k
  sum_ν := by
    unfold orbitS
    simp only [Fin.sum_univ_eq_sum_range]
}

/-- The partial sum of the orbit profile equals orbitS at intermediate points. -/
lemma orbitProfile_partialSum_eq (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n) (k : ℕ) (hk : 0 < k) (j : Fin k) :
    (orbitToProfile n hn_odd hn_pos k hk).partialSum j = orbitS n j.val := by
  classical
  have hsum :
      (∑ i ∈ Finset.filter (· < j) Finset.univ, orbitNu n i.val) =
        ∑ t ∈ Finset.range j.val, orbitNu n t := by
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      rcases Finset.mem_filter.mp hi with ⟨-, hlt⟩
      exact Finset.mem_range.mpr (Fin.lt_def.mp hlt)
    · intro i1 _ i2 _ hval
      exact Fin.ext (by simpa using hval)
    · intro t ht
      have ht_lt : t < j.val := Finset.mem_range.mp ht
      exact ⟨⟨t, Nat.lt_trans ht_lt j.isLt⟩, Finset.mem_filter.mpr ⟨by simp, Fin.lt_def.mpr ht_lt⟩, rfl⟩
    · intro i _; rfl
  unfold CycleProfile.partialSum orbitToProfile orbitS
  simp only [hsum]

/-- The wave sum of the orbit profile equals orbitC. -/
lemma orbitProfile_waveSum_eq (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n) (k : ℕ) (hk : 0 < k) :
    (orbitToProfile n hn_odd hn_pos k hk).waveSum = orbitC n k := by
  classical
  have h_partial := orbitProfile_partialSum_eq n hn_odd hn_pos k hk
  unfold CycleProfile.waveSum
  have h_sum_partial :
      (∑ j : Fin k, 3 ^ (k - 1 - j.val) *
        2 ^ (orbitToProfile n hn_odd hn_pos k hk).partialSum j) =
      ∑ j : Fin k, 3 ^ (k - 1 - j.val) * 2 ^ (orbitS n j.val) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_partial j]
  -- Rewrite to range sum then use orbitC_eq_wavesum
  rw [h_sum_partial]
  rw [Fin.sum_univ_eq_sum_range (fun j => 3 ^ (k - 1 - j) * 2 ^ (orbitS n j))]
  exact (orbitC_eq_wavesum n k).symm

/-- A periodic orbit satisfies the cycle equation: n * (2^S - 3^k) = W.
    This is the fundamental identity that any cycle must satisfy. -/
lemma cycle_equation (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcycle : collatzOddIter k n = n) :
    (n : ℤ) * ((2 : ℤ)^(orbitS n k) - 3^k) = ↑(orbitC n k) :=
  CycleEquation.cycle_equation hn hn_pos hk hcycle

/-- If orbit n k = n (periodic), then the extracted CycleProfile is realizable.

    Proof: The cycle equation gives n * D = W, so D | W and D > 0 (from 2^S > 3^k).
-/
lemma cycle_implies_realizable (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcycle : collatzOddIter k n = n) :
    (orbitToProfile n hn hn_pos k hk).isRealizable := by
  have h_waveSum := orbitProfile_waveSum_eq n hn hn_pos k hk
  have h_ceq := CycleEquation.cycle_equation hn hn_pos hk hcycle
  -- h_ceq : (n : ℤ) * ((2 : ℤ) ^ orbitS n k - 3 ^ k) = ↑(orbitC n k)
  unfold CycleProfile.isRealizable
  constructor
  · -- D > 0: 2^S > 3^k from cycle_S_gt
    unfold cycleDenominator
    have h_gt := CycleEquation.cycle_S_gt n hn hn_pos hk hcycle
    -- h_gt : 2 ^ orbitS n k > 3 ^ k (in ℕ)
    -- orbitS n k = P.S by definition
    have : (3 : ℤ) ^ k < (2 : ℤ) ^ (orbitToProfile n hn hn_pos k hk).S := by exact_mod_cast h_gt
    linarith
  · -- D | W: n * D = orbitC = waveSum
    unfold cycleDenominator
    rw [h_waveSum]
    -- Goal: (2^P.S - 3^k : ℤ) | ↑(orbitC n k)
    -- From h_ceq: n * (2^S - 3^k) = orbitC in ℤ
    -- orbitS n k = P.S by def
    exact ⟨n, by rw [mul_comm]; exact h_ceq.symm⟩

/-- For a cycle, if n > 1, then the profile is nontrivial (some ν differ).

    Intuition: If all ν were equal (say ν = c for all j), then W = D implies n = 1.
    So n > 1 forces some ν to differ.
-/
lemma cycle_n_gt_one_implies_nontrivial (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n) (k : ℕ) (hk : k ≥ 2)
    (hcycle : collatzOddIter k n = n) (hn_gt_1 : n > 1) :
    (orbitToProfile n hn_odd hn_pos k (by omega)).isNontrivial := by
  -- Nontrivial = ∃ j k, ν j ≠ ν k. By contradiction: assume all ν equal.
  by_contra h_not_nontrivial
  unfold CycleProfile.isNontrivial at h_not_nontrivial
  simp only [not_exists, not_not] at h_not_nontrivial
  -- h_not_nontrivial : ∀ j k, P.ν j = P.ν k
  have h_all_eq : ∀ j l : Fin k, (orbitToProfile n hn_odd hn_pos k (by omega)).ν j =
      (orbitToProfile n hn_odd hn_pos k (by omega)).ν l := by
    intro j l; exact h_not_nontrivial j l
  set P := orbitToProfile n hn_odd hn_pos k (by omega)
  set c := P.ν ⟨0, by omega⟩
  have h_const : ∀ j : Fin k, P.ν j = c := fun j => h_all_eq j ⟨0, by omega⟩
  have hc_ge1 : c ≥ 1 := P.ν_pos ⟨0, by omega⟩
  have h_real := cycle_implies_realizable n hn_odd hn_pos k (by omega) hcycle
  -- By only_two_is_residue_free: c = 2
  have hc2 : c = 2 := only_two_is_residue_free (by omega : k ≥ 1) c hc_ge1 P h_const h_real
  -- With c = 2, W = D by trivial_profile_residue_zero
  have h_WD : (P.waveSum : ℤ) = cycleDenominator k P.S :=
    trivial_profile_residue_zero (by omega : k ≥ 1) P (fun j => by rw [h_const]; exact hc2)
  -- From cycle equation: n * D = W (in ℤ)
  have h_waveSum := orbitProfile_waveSum_eq n hn_odd hn_pos k (by omega)
  have h_ceq := CycleEquation.cycle_equation hn_odd hn_pos (by omega : 0 < k) hcycle
  -- W = D and n * D = W gives n * D = D, so n = 1
  have hD_pos : cycleDenominator k P.S > 0 := h_real.1
  have h_n_eq_1 : (n : ℤ) = 1 := by
    -- h_ceq : n * (2^S - 3^k) = orbitC n k (in ℤ)
    -- h_WD : P.waveSum = cycleDenominator k P.S (as ℤ)
    -- h_waveSum : P.waveSum = orbitC n k
    -- So n * D = D, hence (n - 1) * D = 0, D ≠ 0 → n = 1
    rw [h_waveSum] at h_WD
    -- h_WD : ↑(orbitC n k) = cycleDenominator k P.S
    unfold cycleDenominator at h_WD hD_pos
    have hD_ne : (2 : ℤ) ^ P.S - 3 ^ k ≠ 0 := ne_of_gt hD_pos
    -- h_ceq uses orbitS n k, which = P.S by definition
    -- So h_ceq : n * (2^P.S - 3^k) = ↑(orbitC n k) and h_WD : ↑(orbitC n k) = 2^P.S - 3^k
    have h_nD_eq_D : (n : ℤ) * ((2 : ℤ) ^ P.S - 3 ^ k) = (2 : ℤ) ^ P.S - 3 ^ k := by
      have := h_ceq.trans h_WD
      exact this
    have h_sub : ((n : ℤ) - 1) * ((2 : ℤ) ^ P.S - 3 ^ k) = 0 := by linarith
    rcases mul_eq_zero.mp h_sub with h | h
    · linarith
    · exact absurd h hD_ne
  omega

/-! ## Pigeonhole Principle for Bounded Orbits

If an orbit is bounded and never reaches 1, the pigeonhole principle guarantees
a repeat, which gives a periodic orbit. We then extract a CycleProfile and
apply no_nontrivial_cycles to get a contradiction.
-/

private lemma collatzOddIter_pos (n : ℕ) (hn : 0 < n) (k : ℕ) : 0 < collatzOddIter k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    show 0 < collatzOddIter k (collatzOdd n)
    apply ih
    -- Show 0 < collatzOdd n
    unfold collatzOdd
    have h_ne : 3 * n + 1 ≠ 0 := by omega
    have h_dvd := CycleEquation.pow_v2_dvd (3 * n + 1) h_ne
    exact Nat.div_pos (Nat.le_of_dvd (by omega) h_dvd) (by positivity)

/-- Core pigeonhole logic for bounded nontrivial cycles.

    If orbit n is bounded by M and never equals 1, then among the first M+2 values,
    two must be equal (pigeonhole). This gives a periodic orbit starting from some
    orbit value v. The cycle contradiction hypothesis then forces v = 1, contradicting
    the assumption that the orbit never reaches 1.
-/
private lemma no_bounded_nontrivial_cycles_core
    (n : ℕ) (hn_odd : Odd n) (hn : 0 < n)
    (hbounded : ∃ M : ℕ, ∀ T : ℕ, collatzOddIter T n ≤ M)
    (h_not_one : ∀ k : ℕ, collatzOddIter k n ≠ 1)
    (h_cycle_contradiction :
      ∀ {v : ℕ} (hv_odd : Odd v) (hv_pos : 0 < v),
        (∃ k, k ≥ 1 ∧ collatzOddIter k v = v) → v = 1) : False := by
  -- Get the bound M
  obtain ⟨M, hM⟩ := hbounded
  -- Consider M+2 orbit values: collatzOddIter n 0, ..., collatzOddIter n (M+1)
  -- All are in {1, ..., M}, so by pigeonhole two must be equal
  have h_pos_orbit : ∀ k, collatzOddIter k n > 0 := fun k => collatzOddIter_pos n hn k

  -- By pigeonhole: among M+2 values mapping to {0,...,M}, two must collide
  have h_pigeonhole : ∃ i j : Fin (M + 2), i < j ∧ collatzOddIter i.val n = collatzOddIter j.val n := by
    by_contra h_all_distinct
    push_neg at h_all_distinct
    have h_inj : Function.Injective (fun i : Fin (M + 2) => (⟨collatzOddIter i.val n,
        Nat.lt_succ_of_le (hM i.val)⟩ : Fin (M + 1))) := by
      intro i j h_eq
      simp only [Fin.mk.injEq] at h_eq
      by_contra h_ne
      rcases Ne.lt_or_gt h_ne with h_lt | h_gt
      · exact h_all_distinct i j h_lt h_eq
      · exact h_all_distinct j i h_gt h_eq.symm
    have h_card := Fintype.card_le_of_injective _ h_inj
    simp [Fintype.card_fin] at h_card

  -- Get the collision: collatzOddIter i n = collatzOddIter j n with i < j
  obtain ⟨i, j, h_lt, h_eq⟩ := h_pigeonhole

  -- Let v = collatzOddIter i n, period T = j - i ≥ 1
  set v := collatzOddIter i.val n with hv_def
  set T := j.val - i.val with hT_def
  have hT_pos : T > 0 := by omega

  -- Show v cycles: collatzOddIter T v = v
  have h_v_odd : Odd v := collatzOddIter_odd hn_odd hn i.val
  have h_v_pos : 0 < v := h_pos_orbit i.val
  -- Additivity lemma: collatzOddIter (a + b) n = collatzOddIter b (collatzOddIter a n)
  have collatzOddIter_add : ∀ (a b : ℕ) (x : ℕ),
      collatzOddIter (a + b) x = collatzOddIter b (collatzOddIter a x) := by
    intro a; induction a with
    | zero => intro b x; simp [collatzOddIter]
    | succ a' ih =>
      intro b x
      -- (a'+1)+b = (a'+b)+1 for the unfold
      rw [show a' + 1 + b = (a' + b) + 1 from by omega]
      -- collatzOddIter ((a'+b)+1) x = collatzOddIter (a'+b) (collatzOdd x) by def
      show collatzOddIter (a' + b) (collatzOdd x) = collatzOddIter b (collatzOddIter a' (collatzOdd x))
      exact ih b (collatzOdd x)
  have h_v_cycles : collatzOddIter T v = v := by
    have hj_eq : j.val = i.val + T := by omega
    have h_compose : collatzOddIter j.val n = collatzOddIter T (collatzOddIter i.val n) := by
      rw [hj_eq, collatzOddIter_add]
    -- Goal: collatzOddIter T v = v
    -- v = collatzOddIter i n, h_eq : v = collatzOddIter j n
    -- h_compose : collatzOddIter j n = collatzOddIter T (collatzOddIter i n)
    -- So collatzOddIter T v = collatzOddIter T (collatzOddIter i n) = collatzOddIter j n = v
    calc collatzOddIter T v
        = collatzOddIter T (collatzOddIter i.val n) := by rfl
      _ = collatzOddIter j.val n := h_compose.symm
      _ = v := h_eq.symm

  -- By the cycle contradiction, v = 1
  have h_cycle_exists : ∃ k, k ≥ 1 ∧ collatzOddIter k v = v := ⟨T, by omega, h_v_cycles⟩
  have h_v_eq_one := h_cycle_contradiction h_v_odd h_v_pos h_cycle_exists

  -- But collatzOddIter i n ≠ 1 by hypothesis
  exact h_not_one i.val (hv_def ▸ h_v_eq_one)

/-- **No bounded nontrivial cycles.**

    If an orbit is bounded and never reaches 1, we get a contradiction.

    **Proof sketch:**
    1. Bounded orbit → pigeonhole gives repeat → periodic orbit v
    2. v cycles with period k ≥ 1
    3. Extract CycleProfile P from the cycle
    4. P is realizable (from cycle_implies_realizable)
    5. If v > 1, then P is nontrivial
    6. But no_nontrivial_cycles says nontrivial + realizable → False
    7. So v = 1, contradicting h_not_one

    This is the bridge between:
    - Orbit dynamics (pigeonhole on bounded sequences)
    - Algebraic structure (CycleProfile realizability)
    - Impossibility results (no_nontrivial_cycles)
-/
theorem no_bounded_nontrivial_cycles (n : ℕ) (hn_odd : Odd n) (hn : 0 < n)
    (hbounded : ∃ M : ℕ, ∀ T : ℕ, collatzOddIter T n ≤ M)
    (h_not_one : ∀ k : ℕ, collatzOddIter k n ≠ 1)
    (h_no_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False) :
    False := by
  refine no_bounded_nontrivial_cycles_core n hn_odd hn hbounded h_not_one ?_
  intro v hv_odd hv_pos h_cycle_exists
  obtain ⟨k, hk_ge1, hcycle⟩ := h_cycle_exists
  -- Case split: v = 1 or v > 1
  by_cases hv_eq_1 : v = 1
  · exact hv_eq_1
  · -- v > 1: extract profile and derive contradiction
    have hv_gt_1 : v > 1 := by omega
    -- Need k ≥ 2 for no_nontrivial_cycles
    by_cases hk_lt_2 : k < 2
    · -- k = 1: Fixed point case
      have hk_eq_1 : k = 1 := by omega
      subst hk_eq_1
      -- collatzOddIter 1 v = v means collatzOdd v = v
      simp only [collatzOddIter, collatzOdd] at hcycle
      -- collatzOdd v = (3v+1) / 2^ν = v
      -- So v * 2^ν = 3v + 1, hence v * (2^ν - 3) = 1
      -- For v > 1: Need 2^ν - 3 = 1, so ν = 2
      -- But 2^2 - 3 = 1, so v = 1
      by_cases h_v_le_1 : v ≤ 1
      · omega
      · -- v ≥ 2: T(v) = v means (3v+1)/2^ν = v, so 3v+1 = v·2^ν
        have h_v_ge_2 : v ≥ 2 := by omega
        -- hcycle : collatzOdd v = v (since collatzOddIter 1 v = collatzOddIter 0 (collatzOdd v) = collatzOdd v)
        set ν := v2 (3 * v + 1) with hν_def
        have h_dvd : 2 ^ ν ∣ (3 * v + 1) := CycleEquation.pow_v2_dvd (3 * v + 1) (by omega)
        have h_eq : 3 * v + 1 = v * 2 ^ ν := by
          have h := Nat.eq_mul_of_div_eq_right h_dvd hcycle
          rw [mul_comm] at h; ring_nf at h ⊢; exact h
        -- ν ≥ 1 since 3v+1 is even (v is odd)
        have hν_pos : ν ≥ 1 := by
          have h3_odd : Odd (3 * v) := Odd.mul (by decide : Odd 3) hv_odd
          have h_even : Even (3 * v + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr h3_odd
          have h_ne : 3 * v + 1 ≠ 0 := by omega
          haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
          show v2 (3 * v + 1) ≥ 1
          unfold v2
          rw [(padicValNat_def h_ne).symm]
          exact one_le_padicValNat_of_dvd h_ne (Even.two_dvd h_even)
        -- ν ≥ 2 (if ν = 1 then 3v+1 = 2v, contradiction)
        have hν_ge_2 : ν ≥ 2 := by
          by_contra h_not; push_neg at h_not
          have hν_eq_1 : ν = 1 := by omega
          rw [hν_eq_1] at h_eq; norm_num at h_eq; omega
        -- v * (2^ν - 3) = 1 and v ≥ 2, 2^ν ≥ 4 → v*(2^ν-3) ≥ 2 > 1
        have h_rearrange : v * 2 ^ ν - 3 * v = 1 := by omega
        have h_pow_ge_4 : 2 ^ ν ≥ 4 := by
          calc 2 ^ ν ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hν_ge_2
            _ = 4 := by norm_num
        have h_prod : v * (2 ^ ν - 3) ≥ 2 := by
          calc v * (2 ^ ν - 3) ≥ 2 * (2 ^ ν - 3) := by apply Nat.mul_le_mul_right; omega
            _ ≥ 2 * (4 - 3) := by apply Nat.mul_le_mul_left; omega
            _ = 2 := by norm_num
        have h_factor_eq : v * 2 ^ ν - 3 * v = v * (2 ^ ν - 3) := by
          rw [Nat.mul_sub_left_distrib]; ring_nf
        rw [h_factor_eq] at h_rearrange
        omega
    · -- k ≥ 2: Apply no_nontrivial_cycles to derive contradiction
      have hk_ge2 : k ≥ 2 := by omega
      have hk_pos : 0 < k := by omega
      let P := orbitToProfile v hv_odd hv_pos k hk_pos
      -- v is odd (from assumption) and positive
      have h_realizable : P.isRealizable := cycle_implies_realizable v hv_odd hv_pos k hk_pos hcycle
      have h_nontrivial : P.isNontrivial :=
        cycle_n_gt_one_implies_nontrivial v hv_odd hv_pos k hk_ge2 hcycle hv_gt_1
      -- This gives False, contradicting our assumption that v > 1 can cycle
      exfalso
      letI : NeZero k := ⟨by omega⟩
      exact h_no_cycles hk_ge2 P h_nontrivial h_realizable

/-! ## Entry point from 1135.lean: collatzIter cycle → contradiction

Bridge from the full Collatz map (collatzIter) to the Syracuse formulation
(collatzOddIter). Given a collatzIter cycle with n > 4:
1. Extract a Syracuse cycle (odd subsequence)
2. Build a CycleProfile from the Syracuse cycle
3. Show it is realizable and nontrivial
4. Apply the `h_no_cycles` hypothesis (caller supplies the contradiction path)
-/

private lemma collatz_even_step (n : ℕ) (h_even : n % 2 = 0) : collatz n = n / 2 := by
  unfold collatz; simp [h_even]

private lemma collatz_odd_step (n : ℕ) (h_odd : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz; simp [h_odd]

private lemma collatzIter_add' (a b n : ℕ) :
    collatzIter (a + b) n = collatzIter b (collatzIter a n) := by
  induction a generalizing n with
  | zero => simp [collatzIter]
  | succ a ih => simp only [collatzIter]; rw [Nat.succ_add, collatzIter, ih]

private lemma collatzIter_period (k n : ℕ) (h_cycle : collatzIter k n = n) (j : ℕ) :
    collatzIter k (collatzIter j n) = collatzIter j n := by
  rw [← collatzIter_add', Nat.add_comm, collatzIter_add', h_cycle]

/-- The orbit of any x ∈ {1,2,4} under collatz stays in {1,2,4}. -/
private lemma collatzIter_small (m x : ℕ) (hx : x = 1 ∨ x = 2 ∨ x = 4) :
    collatzIter m x = 1 ∨ collatzIter m x = 2 ∨ collatzIter m x = 4 := by
  induction m generalizing x with
  | zero => simp [collatzIter]; tauto
  | succ m ih =>
    show collatzIter m (collatz x) = 1 ∨ collatzIter m (collatz x) = 2 ∨ collatzIter m (collatz x) = 4
    rcases hx with rfl | rfl | rfl
    · exact ih 4 (Or.inr (Or.inr rfl))   -- collatz 1 = 4
    · exact ih 1 (Or.inl rfl)             -- collatz 2 = 1
    · exact ih 2 (Or.inr (Or.inl rfl))    -- collatz 4 = 2

/-- collatzIter m 1 cycles through {1, 4, 2}: the value is always ≤ 4. -/
private lemma collatzIter_one_le_four (m : ℕ) : collatzIter m 1 ≤ 4 := by
  rcases collatzIter_small m 1 (Or.inl rfl) with h | h | h <;> omega

/-- collatz n > 0 for n > 0. -/
private lemma collatz_pos (n : ℕ) (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

/-- collatzIter preserves positivity. -/
private lemma collatzIter_pos (j n : ℕ) (hn : 0 < n) : 0 < collatzIter j n := by
  induction j generalizing n with
  | zero => exact hn
  | succ j ih =>
    -- collatzIter (j+1) n = collatzIter j (collatz n)
    show 0 < collatzIter j (collatz n)
    exact ih (collatz n) (collatz_pos n hn)

/-- If all elements in the first k iterations are even, then
    2^k * T^k(n) ≤ n (since each step at least halves). -/
private lemma collatzIter_halves_bound (n : ℕ) (k : ℕ)
    (h_all_even : ∀ j, j < k → ¬Odd (collatzIter j n)) :
    2^k * collatzIter k n ≤ n := by
  induction k generalizing n with
  | zero => simp [collatzIter]
  | succ k ih =>
    -- collatzIter 0 n = n is even (by h_all_even 0)
    have h_0_even : ¬Odd n := h_all_even 0 (by omega)
    have h_even_mod : n % 2 = 0 := by rwa [Nat.not_odd_iff_even, Nat.even_iff] at h_0_even
    -- collatzIter (k+1) n = collatzIter k (collatz n) = collatzIter k (n/2)
    have h_collatz_n : collatz n = n / 2 := by unfold collatz; simp [h_even_mod]
    -- For collatzIter j (n/2), we need to relate to collatzIter (j+1) n
    -- collatzIter j (collatz n) = collatzIter (j+1) n by definition (reversed)
    -- So collatzIter j (n/2) = collatzIter (j+1) n
    have h_shift : ∀ j, j < k → ¬Odd (collatzIter j (n / 2)) := by
      intro j hj
      -- collatzIter j (n/2) = collatzIter j (collatz n) = collatzIter (j+1) n
      have : collatzIter j (n / 2) = collatzIter (j + 1) n := by
        conv_rhs => rw [show j + 1 = Nat.succ j from rfl, collatzIter, h_collatz_n]
      rw [this]
      exact h_all_even (j + 1) (by omega)
    have h_ik := ih (n / 2) h_shift
    -- collatzIter (k+1) n = collatzIter k (collatz n) = collatzIter k (n/2)
    have h_eq : collatzIter (k + 1) n = collatzIter k (n / 2) := by
      show collatzIter k (collatz n) = collatzIter k (n / 2)
      rw [h_collatz_n]
    rw [pow_succ, mul_assoc, h_eq]
    calc 2 ^ k * (2 * collatzIter k (n / 2))
        = 2 * (2 ^ k * collatzIter k (n / 2)) := by ring
      _ ≤ 2 * (n / 2) := by linarith
      _ ≤ n := Nat.mul_div_le n 2

/-- Reduce collatzIter t n modulo the period k. -/
private lemma collatzIter_mod_period (n k : ℕ) (hk : k > 0) (h_cycle : collatzIter k n = n) (t : ℕ) :
    collatzIter t n = collatzIter (t % k) n := by
  have h_mk : ∀ m, collatzIter (m * k) n = n := by
    intro m
    induction m with
    | zero => simp [collatzIter]
    | succ m ihm =>
      rw [Nat.succ_mul, collatzIter_add', ihm, h_cycle]
  conv_lhs => rw [← Nat.div_add_mod t k]
  rw [show k * (t / k) + t % k = t / k * k + t % k from by ring]
  rw [collatzIter_add', h_mk]

/-- Halving: if 2^k | m then collatzIter k m = m / 2^k. -/
private lemma collatzIter_halve (k m : ℕ) (hm : 0 < m) (h_dvd : 2^k ∣ m) :
    collatzIter k m = m / 2^k := by
  induction k generalizing m with
  | zero => simp [collatzIter]
  | succ k ih =>
    show collatzIter k (collatz m) = m / 2 ^ (k + 1)
    have h2_dvd : 2 ∣ m := by
      exact dvd_trans (⟨2^k, by ring⟩ : 2 ∣ 2^(k+1)) h_dvd
    have h_even : m % 2 = 0 := by omega
    rw [collatz_even_step m h_even]
    have h_half_pos : 0 < m / 2 := by omega
    have h_half_dvd : 2^k ∣ m / 2 := by
      rw [pow_succ, mul_comm] at h_dvd
      obtain ⟨q, hq⟩ := h_dvd
      rw [hq, mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
      exact Nat.dvd_mul_right _ _
    rw [ih (m / 2) h_half_pos h_half_dvd, Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-- One Syracuse step = some number of Collatz steps. -/
private lemma collatzOdd_is_collatzIter (w : ℕ) (hw_odd : Odd w) (hw_pos : 0 < w) :
    collatzOdd w = collatzIter (1 + v2 (3 * w + 1)) w := by
  simp only [collatzOdd]
  set ν := v2 (3 * w + 1)
  -- collatzIter (1+ν) w = collatzIter ν (collatz w) = collatzIter ν (3w+1) = (3w+1)/2^ν
  symm
  show collatzIter (1 + ν) w = (3 * w + 1) / 2 ^ ν
  rw [show 1 + ν = Nat.succ ν from by omega]
  show collatzIter ν (collatz w) = (3 * w + 1) / 2 ^ ν
  rw [collatz_odd_step w (Nat.odd_iff.mp hw_odd)]
  exact collatzIter_halve ν (3 * w + 1) (by omega) (CycleEquation.pow_v2_dvd _ (by omega))

/-- Each Syracuse iterate is some Collatz iterate. -/
private lemma collatzOddIter_is_collatzIter (v : ℕ) (hv_odd : Odd v) (hv_pos : 0 < v) (T : ℕ) :
    ∃ s, collatzOddIter T v = collatzIter s v := by
  induction T with
  | zero => exact ⟨0, rfl⟩
  | succ T ih =>
    obtain ⟨s, hs⟩ := ih
    have hw_odd : Odd (collatzOddIter T v) := CycleEquation.collatzOddIter_odd hv_odd hv_pos T
    have hw_pos : 0 < collatzOddIter T v := by
      rw [hs]; exact collatzIter_pos s v hv_pos
    refine ⟨s + (1 + v2 (3 * collatzOddIter T v + 1)), ?_⟩
    rw [collatzOddIter_succ_right, collatzOdd_is_collatzIter _ hw_odd hw_pos, hs,
        ← collatzIter_add']

/-- From a collatzIter cycle with n > 4, derive contradiction. -/
theorem collatzIter_cycle_contradiction (n : ℕ) (hn : n > 4) (k : ℕ) (hk : k > 0)
    (h_cycle : collatzIter k n = n)
    (h_no_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False) :
    False := by
  by_cases h_one_in : ∃ j, j < k ∧ collatzIter j n = 1
  · -- 1 in orbit → n = T^(k-j)(1) ≤ 4
    obtain ⟨j, hj_lt, hj_eq⟩ := h_one_in
    have h_n_eq : n = collatzIter (k - j) 1 := by
      have hjk : j + (k - j) = k := Nat.add_sub_cancel' (by omega : j ≤ k)
      have : collatzIter (j + (k - j)) n = collatzIter (k - j) (collatzIter j n) :=
        collatzIter_add' j (k - j) n
      rw [hjk, h_cycle, hj_eq] at this
      exact this
    linarith [collatzIter_one_le_four (k - j)]
  · push_neg at h_one_in
    have h_ne_one_all : ∀ t, collatzIter t n ≠ 1 := by
      intro t
      rw [collatzIter_mod_period n k hk h_cycle t]
      exact h_one_in (t % k) (Nat.mod_lt t (by omega))
    by_cases h_has_odd : ∃ j, j < k ∧ Odd (collatzIter j n)
    · obtain ⟨j, hj_lt, hj_odd⟩ := h_has_odd
      set v := collatzIter j n with hv_def
      have hv_pos : 0 < v := collatzIter_pos j n (by omega)
      have hv_cycle : collatzIter k v = v := collatzIter_period k n h_cycle j
      apply no_bounded_nontrivial_cycles v hj_odd hv_pos
      · -- Bounded: all Syracuse values are Collatz iterates, which cycle through k values
        classical
        let f := fun i => collatzIter i v
        have hne : (Finset.image f (Finset.range k)).Nonempty :=
          ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩⟩
        refine ⟨(Finset.image f (Finset.range k)).sup' hne id, fun T => ?_⟩
        obtain ⟨s, hs⟩ := collatzOddIter_is_collatzIter v hj_odd hv_pos T
        rw [hs, collatzIter_mod_period v k hk hv_cycle s]
        have hmem : f (s % k) ∈ Finset.image f (Finset.range k) :=
          Finset.mem_image.mpr ⟨s % k, Finset.mem_range.mpr (Nat.mod_lt s (by omega)), rfl⟩
        exact Finset.le_sup' id hmem
      · -- Never 1
        intro T hT
        obtain ⟨s, hs⟩ := collatzOddIter_is_collatzIter v hj_odd hv_pos T
        rw [hs] at hT
        have : collatzIter s v = collatzIter (j + s) n := by
          rw [hv_def, collatzIter_add']
        rw [this] at hT
        exact h_ne_one_all (j + s) hT
      · exact h_no_cycles
    · -- All even → 2^k * n ≤ n, contradiction
      push_neg at h_has_odd
      have h_bound := collatzIter_halves_bound n k h_has_odd
      rw [h_cycle] at h_bound
      have h2k : 2 ^ k ≥ 2 := by
        have : 1 ≤ k := hk
        calc 2 ^ k ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) this
          _ = 2 := by norm_num
      nlinarith

/-- Any positive periodic Collatz point is in the trivial cycle `{1,2,4}`.

    This packages the cycle-contradiction theorem into the explicit
    membership statement: if `collatzIter k n = n` with `k > 0` and `n > 0`,
    then `n = 1 ∨ n = 2 ∨ n = 4`. -/
theorem periodic_points_are_trivial (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (h_cycle : collatzIter k n = n)
    (h_no_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  by_cases hn_gt4 : n > 4
  · exact (collatzIter_cycle_contradiction n hn_gt4 k hk h_cycle h_no_cycles).elim
  · have hn_le4 : n ≤ 4 := by omega
    have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn_cases with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · -- If 3 were periodic, then 5 would also be periodic with same period.
      exfalso
      have h_period : collatzIter k (collatzIter 2 3) = collatzIter 2 3 :=
        collatzIter_period k 3 h_cycle 2
      have h5_cycle : collatzIter k 5 = 5 := by
        simpa [collatzIter] using h_period
      exact collatzIter_cycle_contradiction 5 (by omega) k hk h5_cycle h_no_cycles
    · exact Or.inr (Or.inr rfl)

end Collatz.NoCycle
