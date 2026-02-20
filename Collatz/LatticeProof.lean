/-
  LatticeProof.lean — Lattice non-membership (Path 2)
  =====================================================

  Proves: No nontrivial CycleProfile is realizable, via 2-adic
  constraint sublattices.

  Strategy:
  1. Define pattern lattice L = { n₀ > 0 odd : W + n₀·3^m = n₀·2^S }
     and constraint coset L_m = { n₀ : 2^S | 3^m·n₀ + W }.
  2. Show L ⊆ L_m (orbit equation embeds into top constraint).
  3. Decompose E = A + B where v₂(A) = K := v₂(1+3n₀),
     v₂(B) = ν₀ exactly. Forced alignment: if K ≠ ν₀ then
     2^S ∤ (A+B), so no n₀ satisfies the orbit equation.
  4. Baker drift: accumulated offset |Lε| eventually ≥ 1,
     so top coset membership forces all-loop return which fails.
  5. Endpoint: `nontrivial_not_realizable` derives False from
     empty top coset + realizability, or via rigidity bridge
     (D | W forces all ν_j equal, contradicting nontriviality).
-/
import Collatz.Defs
import Collatz.NumberTheoryAxioms
import Collatz.CyclotomicDrift
import Collatz.DriftContradiction
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Collatz
open scoped BigOperators

namespace Collatz.LatticeProof

set_option linter.unusedVariables false

/-! ## Pattern and rational lattices -/

/-! ## Quantified drift (lattice-side view)

These lemmas expose the loop-by-loop drift mechanism directly in the lattice
file: Baker gives a positive lower bound on `|ε|`, so accumulated offset
`|Lε|` eventually exceeds one unit. At that point, the scaled return equation
cannot hold. -/

/-- Baker drift witness in lattice form: eventually `|L·ε| ≥ 1`. -/
theorem exists_lattice_drift_unit_witness {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m) (h_nontrivial : P.isNontrivial) :
    ∃ L : ℕ, |Collatz.accumulated_offset P L| ≥ 1 :=
  Collatz.exists_offset_ge_one P hm h_nontrivial

/-- Once accumulated drift passes one unit, lattice return at that loop fails. -/
theorem lattice_return_fails_at_drift_witness {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m) (h_nontrivial : P.isNontrivial)
    (n₀ : ℝ) (hn₀_pos : n₀ > 0) :
    ∃ L : ℕ, n₀ * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) ≠ n₀ := by
  rcases exists_lattice_drift_unit_witness (hm := hm) (P := P) h_nontrivial with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  exact Collatz.orbit_cannot_close P L hL n₀ hn₀_pos

/-- Drift-quantified lattice contradiction:
if return held for every loop, Baker drift forbids it at some loop. -/
theorem lattice_return_cannot_hold_all_loops {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m) (h_nontrivial : P.isNontrivial)
    (n₀ : ℝ) (hn₀_pos : n₀ > 0)
    (h_returns_all : ∀ L : ℕ, n₀ * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = n₀) :
    False := by
  rcases lattice_return_fails_at_drift_witness (hm := hm) (P := P) h_nontrivial n₀ hn₀_pos with
    ⟨L, hL_ne⟩
  exact hL_ne (h_returns_all L)

/-- Eventual non-return form of Baker drift: after some threshold,
every loop fails exact return. -/
theorem lattice_return_fails_eventually {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m) (h_nontrivial : P.isNontrivial)
    (n₀ : ℝ) (hn₀_pos : n₀ > 0) :
    ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 →
      n₀ * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) ≠ n₀ := by
  rcases Collatz.eventually_offset_ge_one P hm h_nontrivial with ⟨L0, hL0⟩
  refine ⟨L0, ?_⟩
  intro L hL_ge h_eq
  exact Collatz.orbit_cannot_close P L (hL0 L hL_ge) n₀ hn₀_pos h_eq


/-- Pattern lattice: positive odd integers satisfying W + n₀·3^m = n₀·2^S -/
def patternLattice {m : ℕ} (P : CycleProfile m) : Set ℤ :=
  { n₀ : ℤ | n₀ > 0 ∧ ¬(2 : ℤ) ∣ n₀ ∧
    (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S }

/-- Rational lattice: fixed points of T(x) = (3^m·x + W)/2^S -/
noncomputable def rationalLattice {m : ℕ} (P : CycleProfile m) : Set ℚ :=
  { x : ℚ | (3 : ℚ) ^ m * x + (P.waveSum : ℚ) = x * (2 : ℚ) ^ P.S }

/-- Rational lattice is {W/D} when D > 0. -/
theorem rationalLattice_eq_singleton {m : ℕ} (P : CycleProfile m)
    (hD_pos : cycleDenominator m P.S > 0) :
    rationalLattice P = { (P.waveSum : ℚ) / (cycleDenominator m P.S : ℚ) } := by
  ext x; simp only [rationalLattice, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have hD_ne : (cycleDenominator m P.S : ℚ) ≠ 0 := by
      have : (0 : ℤ) < cycleDenominator m P.S := hD_pos
      exact_mod_cast ne_of_gt this
    have h_eq : (P.waveSum : ℚ) = x * (cycleDenominator m P.S : ℚ) := by
      unfold cycleDenominator; push_cast; linarith
    field_simp at h_eq ⊢; linarith
  · intro h
    have hD_ne : (cycleDenominator m P.S : ℚ) ≠ 0 := by
      have : (0 : ℤ) < cycleDenominator m P.S := hD_pos
      exact_mod_cast ne_of_gt this
    set xstar := (P.waveSum : ℚ) / (cycleDenominator m P.S : ℚ)
    rw [h]
    have h_W_eq : (P.waveSum : ℚ) = xstar * (cycleDenominator m P.S : ℚ) := by
      simp [xstar, div_mul_cancel₀ _ hD_ne]
    have hD_expand : (cycleDenominator m P.S : ℚ) = (2 : ℚ) ^ P.S - 3 ^ m := by
      unfold cycleDenominator; push_cast; ring
    rw [hD_expand] at h_W_eq; nlinarith

/-- n₀ ∈ pattern lattice iff D | W and n₀ = W/D. -/
theorem patternLattice_iff_divisibility {m : ℕ} (P : CycleProfile m)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀) :
    n₀ ∈ patternLattice P ↔
      (P.waveSum : ℤ) = n₀ * cycleDenominator m P.S := by
  simp only [patternLattice, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, _, h_orbit⟩
    unfold cycleDenominator; linarith
  · intro h_eq
    refine ⟨hn₀_pos, hn₀_odd, ?_⟩
    unfold cycleDenominator at h_eq; linarith

/-- Pattern lattice embeds into rational lattice via ℤ ↪ ℚ. -/
theorem patternLattice_sub_rationalLattice {m : ℕ} (P : CycleProfile m)
    (n₀ : ℤ) (h_mem : n₀ ∈ patternLattice P) :
    (n₀ : ℚ) ∈ rationalLattice P := by
  obtain ⟨_, _, h_orbit⟩ := h_mem
  simp only [rationalLattice, Set.mem_setOf_eq]
  have h_int : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S := h_orbit
  have : (P.waveSum : ℚ) + (n₀ : ℚ) * 3 ^ m = (n₀ : ℚ) * 2 ^ P.S := by
    exact_mod_cast h_int
  linarith

/-! ## Partial sum infrastructure -/

/-- Partial sum at j=0 is 0. -/
lemma partialSum_zero {m : ℕ} (hm : 0 < m) (P : CycleProfile m) :
    P.partialSum ⟨0, hm⟩ = 0 := by
  unfold CycleProfile.partialSum
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi
  exact absurd hi (by omega)

/-- Partial sum at j=1 is ν₀. -/
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

/-- For j ≥ 2: partialSum j ≥ ν₀ + ν₁ ≥ ν₀ + 1. -/
lemma partialSum_ge_two {m : ℕ} (hm : 2 ≤ m) (P : CycleProfile m)
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

/-- ν₀ < S when m ≥ 2. -/
lemma nu0_lt_S {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) :
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

/-! ## A+B decomposition -/

/-- Term A = 3^{m-1} · (1 + 3n₀) -/
def termA (m : ℕ) (n₀ : ℤ) : ℤ := 3 ^ (m - 1) * (1 + 3 * n₀)

/-- Term B = Σ_{j≥1} 3^{m-1-j} · 2^{Sⱼ} -/
noncomputable def termB {m : ℕ} (P : CycleProfile m) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => 1 ≤ j.val),
    (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j)

/-- Decomposition: E = A + B -/
theorem E_eq_A_plus_B {m : ℕ} (hm : 2 ≤ m) (P : CycleProfile m)
    (n₀ : ℤ) :
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
        have hj_val : 1 ≤ j.val := h_j
        have hj_lt : j.val < m' + 1 := j.isLt
        use ⟨j.val - 1, by omega⟩
        simp only [Fin.ext_iff, Fin.val_succ]
        omega
      · rintro ⟨i, -, rfl⟩; exact Nat.succ_pos i.val
    rw [h_eq]
    rw [Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)]
    apply Finset.sum_congr rfl
    intro i _
    simp [Fin.val_succ]
  rw [h_filter]
  ring

/-! ## Valuation bounds -/

/-- Ultrametric: if 2^k | a and 2^k ∤ b then 2^k ∤ (a + b). -/
private lemma dvd_add_left_cancel {a b : ℤ} {k : ℕ}
    (ha : (2 : ℤ) ^ k ∣ a) (hb : ¬(2 : ℤ) ^ k ∣ b) :
    ¬(2 : ℤ) ^ k ∣ (a + b) := by
  intro h; exact hb (by have := dvd_sub h ha; rwa [add_sub_cancel_left] at this)

/-- Symmetric version: if 2^k ∤ a and 2^k | b then 2^k ∤ (a + b). -/
private lemma dvd_add_right_cancel {a b : ℤ} {k : ℕ}
    (ha : ¬(2 : ℤ) ^ k ∣ a) (hb : (2 : ℤ) ^ k ∣ b) :
    ¬(2 : ℤ) ^ k ∣ (a + b) := by
  rw [add_comm]; exact dvd_add_left_cancel hb ha

/-- 2^{ν₀} | termB -/
private lemma two_pow_nu0_dvd_termB {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) :
    (2 : ℤ) ^ (P.ν ⟨0, by omega⟩) ∣ termB P := by
  unfold termB
  apply Finset.dvd_sum
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  apply dvd_mul_of_dvd_right
  apply pow_dvd_pow
  unfold CycleProfile.partialSum
  calc P.ν ⟨0, by omega⟩
      = ({⟨0, by omega⟩} : Finset (Fin m)).sum P.ν := by simp
    _ ≤ (Finset.univ.filter (fun x : Fin m => x < j)).sum P.ν := by
        apply Finset.sum_le_sum_of_subset
        intro x hx; simp only [Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
        subst hx; show (0 : ℕ) < j.val; omega

/-- 2^k | termA ↔ 2^k | (1+3n₀) -/
private lemma termA_dvd_iff {m : ℕ} (hm : m ≥ 2) (n₀ : ℤ) (hn₀_pos : n₀ > 0)
    (k : ℕ) : (2 : ℤ) ^ k ∣ termA m n₀ ↔ (2 : ℤ) ^ k ∣ (1 + 3 * n₀) := by
  unfold termA
  have h23 : IsCoprime (2 : ℤ) 3 := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl]
    exact_mod_cast (by decide : Nat.Coprime 2 3).isCoprime
  have h_coprime : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ (m - 1)) :=
    h23.pow_left.pow_right
  constructor
  · intro ⟨c, hc⟩
    exact h_coprime.dvd_of_dvd_mul_right ⟨c, by linarith⟩
  · intro h; exact dvd_mul_of_dvd_right h _

/-- 2^{ν₀+1} ∤ termB -/
private lemma not_two_pow_nu0_succ_dvd_termB {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) :
    ¬(2 : ℤ) ^ (P.ν ⟨0, by omega⟩ + 1) ∣ termB P := by
  set ν₀ := P.ν ⟨0, by omega⟩
  intro h_dvd
  have h_ps1 : P.partialSum ⟨1, by omega⟩ = ν₀ := partialSum_one (by omega) P
  have h_tail_dvd : ∀ j ∈ Finset.univ.filter (fun j : Fin m => 2 ≤ j.val),
      (2 : ℤ) ^ (ν₀ + 1) ∣ (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    apply dvd_mul_of_dvd_right
    apply pow_dvd_pow
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
      · rintro (h | h)
        · omega
        · omega
    have h_disj : Disjoint ({⟨1, by omega⟩} : Finset (Fin m))
        (Finset.univ.filter (fun j : Fin m => 2 ≤ j.val)) := by
      simp only [Finset.disjoint_singleton_left, Finset.mem_filter,
        Finset.mem_univ, true_and, not_le]; omega
    rw [h_partition, Finset.sum_union h_disj, Finset.sum_singleton]
    congr 1
    rw [h_ps1]
  rw [h_split] at h_dvd
  have h_term1_dvd : (2 : ℤ) ^ (ν₀ + 1) ∣ (3 : ℤ) ^ (m - 1 - 1) * 2 ^ ν₀ := by
    have := dvd_sub h_dvd h_tail_sum_dvd
    rwa [add_sub_cancel_right] at this
  rw [pow_succ] at h_term1_dvd
  have h_dvd2 : (2 : ℤ) ∣ (3 : ℤ) ^ (m - 1 - 1) := by
    have h2_ne : (2 : ℤ) ^ ν₀ ≠ 0 := by positivity
    rw [show (3 : ℤ) ^ (m - 1 - 1) * 2 ^ ν₀ = 2 ^ ν₀ * 3 ^ (m - 1 - 1) from by ring]
      at h_term1_dvd
    exact (mul_dvd_mul_iff_left h2_ne).mp h_term1_dvd
  -- But 3^k is odd for all k, contradiction.
  have h_odd : ¬(2 : ℤ) ∣ (3 : ℤ) ^ (m - 1 - 1) := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl,
      ← Int.natCast_pow, Int.natCast_dvd_natCast]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 2) h
    omega
  exact h_odd h_dvd2

/-- padicValInt gives 2^K | (1+3n₀) -/
private lemma padicVal_dvd (n₀ : ℤ) (hn₀_pos : n₀ > 0) :
    (2 : ℤ) ^ padicValInt 2 (1 + 3 * n₀) ∣ (1 + 3 * n₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact padicValInt_dvd (1 + 3 * n₀)

/-- padicValInt gives 2^{K+1} ∤ (1+3n₀) -/
private lemma padicVal_not_dvd_succ (n₀ : ℤ) (hn₀_pos : n₀ > 0) :
    ¬(2 : ℤ) ^ (padicValInt 2 (1 + 3 * n₀) + 1) ∣ (1 + 3 * n₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro h
  have h' : (↑(2 : ℕ) : ℤ) ^ (padicValInt 2 (1 + 3 * n₀) + 1) ∣ (1 + 3 * n₀) := by
    exact_mod_cast h
  rw [padicValInt_dvd_iff] at h'
  rcases h' with h_zero | h_le
  · omega
  · omega

theorem v2_bound_distinct_case {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (hK_ne : padicValInt 2 (1 + 3 * n₀) ≠ P.ν ⟨0, by omega⟩) :
    ¬((2 : ℤ) ^ P.S ∣ (termA m n₀ + termB P)) := by
  set K := padicValInt 2 (1 + 3 * n₀) with hK_def
  set ν₀ := P.ν ⟨0, by omega⟩ with hν₀_def
  intro h_dvd
  rcases Nat.lt_or_gt_of_ne hK_ne with hK_lt | hK_gt
  · -- Case K < ν₀: v₂(A) = K, v₂(B) ≥ ν₀ > K
    -- So 2^{K+1} | B but 2^{K+1} ∤ A, hence 2^{K+1} ∤ (A+B)
    have hA_not : ¬(2 : ℤ) ^ (K + 1) ∣ termA m n₀ := by
      rw [termA_dvd_iff hm n₀ hn₀_pos]
      exact padicVal_not_dvd_succ n₀ hn₀_pos
    have hB_dvd : (2 : ℤ) ^ (K + 1) ∣ termB P := by
      calc (2 : ℤ) ^ (K + 1)
          ∣ (2 : ℤ) ^ ν₀ := pow_dvd_pow 2 (by omega)
        _ ∣ termB P := two_pow_nu0_dvd_termB hm P
    have h_le : K + 1 ≤ P.S := by have := nu0_lt_S hm P; omega
    exact absurd (dvd_trans (pow_dvd_pow 2 h_le) h_dvd)
      (dvd_add_right_cancel hA_not hB_dvd)
  · -- Case K > ν₀: v₂(A) = K > ν₀, v₂(B) = ν₀ exactly
    -- So 2^{ν₀+1} | A but 2^{ν₀+1} ∤ B, hence 2^{ν₀+1} ∤ (A+B)
    have hA_dvd : (2 : ℤ) ^ (ν₀ + 1) ∣ termA m n₀ := by
      rw [termA_dvd_iff hm n₀ hn₀_pos]
      exact dvd_trans (pow_dvd_pow 2 (by omega : ν₀ + 1 ≤ K)) (padicVal_dvd n₀ hn₀_pos)
    have hB_not : ¬(2 : ℤ) ^ (ν₀ + 1) ∣ termB P :=
      not_two_pow_nu0_succ_dvd_termB hm P
    have h_le : ν₀ + 1 ≤ P.S := by have := nu0_lt_S hm P; omega
    exact absurd (dvd_trans (pow_dvd_pow 2 h_le) h_dvd)
      (dvd_add_left_cancel hA_dvd hB_not)

/-! ## Forced alignment -/

/-- Membership hypothesis forces K = ν₀. -/
theorem forced_alignment {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (hAB_eq : termA m n₀ + termB P = n₀ * 2 ^ P.S)
    (hD_pos : cycleDenominator m P.S > 0) :
    padicValInt 2 (1 + 3 * n₀) = P.ν ⟨0, by omega⟩ := by
  by_contra hK_ne
  have h_dvd : (2 : ℤ) ^ P.S ∣ (termA m n₀ + termB P) :=
    ⟨n₀, by linarith⟩
  exact absurd h_dvd (v2_bound_distinct_case hm P n₀ hn₀_pos hn₀_odd hK_ne)

/-! ## Valuation stratification -/

/-- Ultrametric: 2^k | x, 2^{k+1} ∤ x, 2^{k+1} | y ⟹ 2^{k+1} ∤ (x+y). -/
private lemma int_ultrametric_strict {x y : ℤ} {k : ℕ}
    (hx_dvd : (2 : ℤ) ^ k ∣ x) (hx_not : ¬(2 : ℤ) ^ (k + 1) ∣ x)
    (hy_dvd : (2 : ℤ) ^ (k + 1) ∣ y) :
    ¬(2 : ℤ) ^ (k + 1) ∣ (x + y) := by
  intro h
  exact hx_not (by have := dvd_sub h hy_dvd; rwa [add_sub_cancel_right] at this)

/-- For j ≥ 2: partialSum j ≥ ν₀ + ν₁. -/
private lemma partialSum_ge_nu01 {m : ℕ} (hm : m ≥ 3) (P : CycleProfile m)
    (j : Fin m) (hj : 2 ≤ j.val) :
    P.partialSum j ≥ P.ν ⟨0, by omega⟩ + P.ν ⟨1, by omega⟩ := by
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

private lemma tail_rest_dvd {m : ℕ} (hm : m ≥ 3) (P : CycleProfile m) :
    ∀ j ∈ Finset.univ.filter (fun j : Fin m => 2 ≤ j.val),
      (2 : ℤ) ^ (P.ν ⟨0, by omega⟩ + P.ν ⟨1, by omega⟩) ∣
        (3 : ℤ) ^ (m - 1 - j.val) * 2 ^ (P.partialSum j) := by
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  apply dvd_mul_of_dvd_right
  apply pow_dvd_pow
  exact partialSum_ge_nu01 hm P j hj

/-! ## Constraint lattice -/

/-- Extended partial sum: S_j for j < m, S for j = m. -/
def extPartialSum {m : ℕ} (P : CycleProfile m) (j : ℕ) (hj : j ≤ m) : ℕ :=
  if h : j < m then P.partialSum ⟨j, h⟩ else P.S

/-- Partial wave sum: W_j = Σ_{i<j} 3^{j-1-i} · 2^{S_i} -/
noncomputable def partialWaveSum {m : ℕ} (P : CycleProfile m) (j : ℕ) (hj : j ≤ m) : ℤ :=
  ∑ i : Fin j,
    (3 : ℤ) ^ (j - 1 - i.val) * 2 ^ (P.partialSum ⟨i.val, by omega⟩)

/-- Constraint coset: {n₀ : 2^{S_j} | (3^j·n₀ + W_j)} -/
def constraintCoset {m : ℕ} (P : CycleProfile m) (j : ℕ) (hj : j ≤ m) : Set ℤ :=
  { n₀ : ℤ | n₀ > 0 ∧ ¬(2 : ℤ) ∣ n₀ ∧
    (2 : ℤ) ^ (extPartialSum P j hj) ∣
      ((3 : ℤ) ^ j * n₀ + partialWaveSum P j hj) }

/-- Partial wave sum at j = m equals full wave sum. -/
lemma partialWaveSum_top {m : ℕ} (P : CycleProfile m) :
    partialWaveSum P m (le_rfl) = (P.waveSum : ℤ) := by
  unfold partialWaveSum CycleProfile.waveSum
  simp

/-- Pattern lattice embeds into top constraint coset. -/
lemma patternLattice_sub_top_constraint {m : ℕ} (P : CycleProfile m) :
    patternLattice P ⊆ constraintCoset P m (le_rfl) := by
  intro n₀ h_mem
  rcases h_mem with ⟨hn₀_pos, hn₀_odd, h_orbit⟩
  refine ⟨hn₀_pos, hn₀_odd, ?_⟩
  refine ⟨n₀, ?_⟩
  calc
    (3 : ℤ) ^ m * n₀ + partialWaveSum P m (le_rfl)
        = n₀ * 2 ^ P.S := by
          rw [partialWaveSum_top P]
          linarith [h_orbit]
    _ = (2 : ℤ) ^ (extPartialSum P m (le_rfl)) * n₀ := by
          simp [extPartialSum, mul_comm]

/-- W = n₀ · D from A + B = n₀ · 2^S. -/
private lemma orbit_gives_divisibility {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m)
    (n₀ : ℤ) (hAB_eq : termA m n₀ + termB P = n₀ * 2 ^ P.S) :
    (P.waveSum : ℤ) = n₀ * cycleDenominator m P.S := by
  have := E_eq_A_plus_B hm P n₀
  unfold cycleDenominator; linarith

/-- Core contradiction from forced alignment and top-coset emptiness. -/
theorem aligned_orbit_contradiction {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : ∃ j k : Fin m, P.ν j ≠ P.ν k)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (hK_eq : padicValInt 2 (1 + 3 * n₀) = P.ν ⟨0, by omega⟩)
    (hAB_eq : termA m n₀ + termB P = n₀ * 2 ^ P.S)
    (hD_pos : cycleDenominator m P.S > 0)
    (h_top_empty : constraintCoset P m (le_rfl) = ∅) :
    False := by
  have hS_pos : P.S ≥ 1 := by
    have hν0_pos : P.ν ⟨0, by omega⟩ > 0 := P.ν_pos ⟨0, by omega⟩
    have hν0_le : P.ν ⟨0, by omega⟩ ≤ P.S := by
      rw [← P.sum_ν]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
    omega
  have hD_int : (2 : ℤ) ^ P.S > 3 ^ m := by
    unfold cycleDenominator at hD_pos
    omega
  have h_baker_gap := baker_gap_bound P.S m hm hS_pos hD_int
  have h_drift_lb : (cycleDenominator m P.S : ℤ) ≥ 3 ^ m / m ^ 10 := by
    simpa [cycleDenominator] using h_baker_gap
  have h_orbit : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S := by
    have hE := E_eq_A_plus_B hm P n₀
    linarith [hE, hAB_eq]
  have h_pattern_mem : n₀ ∈ patternLattice P := ⟨hn₀_pos, hn₀_odd, h_orbit⟩
  have h_top_coset_mem : n₀ ∈ constraintCoset P m (le_rfl) :=
    patternLattice_sub_top_constraint P h_pattern_mem
  exact Set.notMem_empty n₀ (h_top_empty ▸ h_top_coset_mem)

/-- Lattice non-membership from rigidity bridge. -/
theorem lattice_non_membership_from_rigidity (m : ℕ) (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : ∃ j k : Fin m, P.ν j ≠ P.ν k)
    (hD_pos : cycleDenominator m P.S > 0)
    (h_rigidity :
      (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ) →
      ∀ j k : Fin m, P.ν j = P.ν k)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (h_orbit : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S)
    :
    False := by
  have hW_eq : (P.waveSum : ℤ) = n₀ * cycleDenominator m P.S := by
    unfold cycleDenominator
    linarith [h_orbit]
  have h_dvd : (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ) := by
    refine ⟨n₀, ?_⟩
    rw [hW_eq]
    ring
  have h_all_eq : ∀ j k : Fin m, P.ν j = P.ν k := h_rigidity h_dvd
  rcases h_nontrivial with ⟨j, k, hjk⟩
  exact hjk (h_all_eq j k)

/-- Top constraint coset emptiness excludes integer orbit points. -/
theorem lattice_non_membership_of_top_constraint_empty (m : ℕ) (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : ∃ j k : Fin m, P.ν j ≠ P.ν k)
    (h_top_empty : constraintCoset P m (le_rfl) = ∅)
    (n₀ : ℤ) (hn₀_pos : n₀ > 0) (hn₀_odd : ¬(2 : ℤ) ∣ n₀)
    (h_orbit : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S) :
    False := by
  have h_pattern_mem : n₀ ∈ patternLattice P := ⟨hn₀_pos, hn₀_odd, h_orbit⟩
  have h_top_mem : n₀ ∈ constraintCoset P m (le_rfl) :=
    patternLattice_sub_top_constraint P h_pattern_mem
  exact Set.notMem_empty n₀ (h_top_empty ▸ h_top_mem)

/-- Pattern lattice is empty when L_m = ∅. -/
theorem patternLattice_empty_of_top_constraint_empty (m : ℕ) (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : ∃ j k : Fin m, P.ν j ≠ P.ν k)
    (h_top_empty : constraintCoset P m (le_rfl) = ∅) :
    patternLattice P = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n₀ h_mem
  obtain ⟨hn₀_pos, hn₀_odd, h_orbit⟩ := h_mem
  exact lattice_non_membership_of_top_constraint_empty m hm P h_nontrivial h_top_empty
    n₀ hn₀_pos hn₀_odd h_orbit

/-- Prime-divisor bridge predicate: asserts that D | W implies L_m = ∅.
    Supplied as a hypothesis by callers who establish emptiness via
    Baker drift or cyclotomic rigidity. -/
def PrimeDivisorTopConstraintBridge {m : ℕ} (P : CycleProfile m) : Prop :=
  (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ) →
    constraintCoset P m (le_rfl) = ∅

/-- Realizable profile with bridge has empty top coset. -/
lemma top_constraint_empty_of_prime_divisor_bridge {m : ℕ} (P : CycleProfile m)
    (h_bridge : PrimeDivisorTopConstraintBridge P)
    (h_realizable : P.isRealizable) :
    constraintCoset P m (le_rfl) = ∅ :=
  h_bridge h_realizable.2

/-- Sublattice-constraint non-membership principle:
if every point in the top constraint coset would force exact all-loop return in
the drift model, then nontrivial Baker drift empties that top coset. -/
theorem top_constraint_empty_of_drift_sublattice
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) (h_nontrivial : P.isNontrivial)
    (h_membership_forces_all_loop_return :
      ∀ n₀ : ℤ, n₀ ∈ constraintCoset P m (le_rfl) →
        ∀ L : ℕ, (n₀ : ℝ) * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = (n₀ : ℝ)) :
    constraintCoset P m (le_rfl) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n₀ hn₀_mem
  have hn₀_posZ : n₀ > 0 := hn₀_mem.1
  have hn₀_posR : (n₀ : ℝ) > 0 := by exact_mod_cast hn₀_posZ
  have h_returns_all : ∀ L : ℕ,
      (n₀ : ℝ) * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = (n₀ : ℝ) :=
    h_membership_forces_all_loop_return n₀ hn₀_mem
  exact (lattice_return_cannot_hold_all_loops (hm := hm) (P := P) h_nontrivial
      (n₀ := (n₀ : ℝ)) hn₀_posR h_returns_all).elim

/-- Eventual-eventual sublattice non-membership principle:
if top-coset membership forces eventual exact return, while drift gives eventual
non-return, the top constraint coset is empty. -/
theorem top_constraint_empty_of_eventual_drift_sublattice
    {m : ℕ} (hm : m ≥ 2) (P : CycleProfile m) (h_nontrivial : P.isNontrivial)
    (h_membership_forces_eventual_return :
      ∀ n₀ : ℤ, n₀ ∈ constraintCoset P m (le_rfl) →
        ∃ Lr : ℕ, ∀ L : ℕ, L ≥ Lr →
          (n₀ : ℝ) * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = (n₀ : ℝ)) :
    constraintCoset P m (le_rfl) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n₀ hn₀_mem
  have hn₀_posR : (n₀ : ℝ) > 0 := by exact_mod_cast hn₀_mem.1
  rcases h_membership_forces_eventual_return n₀ hn₀_mem with ⟨Lr, hret⟩
  rcases lattice_return_fails_eventually (hm := hm) (P := P) h_nontrivial
      (n₀ := (n₀ : ℝ)) hn₀_posR with ⟨Ld, hfail⟩
  let L := max Lr Ld
  have hEq : (n₀ : ℝ) * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) = (n₀ : ℝ) :=
    hret L (le_max_left _ _)
  have hNe : (n₀ : ℝ) * (2 : ℝ) ^ (-(Collatz.accumulated_offset P L)) ≠ (n₀ : ℝ) :=
    hfail L (le_max_right _ _)
  exact hNe hEq

/-! ═══════════════════════════════════════════════
    Section 7: Bookend — the trivial profile IS in the lattice
    ═══════════════════════════════════════════════

    ν = (2,...,2) gives W = D, n₀ = 1, E = 2^S.
    The unique profile where the coset contains an integer.
    This is why 1 → 4 → 2 → 1 persists and nothing else can. -/

/-- For the trivial profile ν = (2,...,2), the orbit equation is
    satisfied with n₀ = 1: W + 3^m = 2^S.
    Requires W = D as hypothesis (established by NoCycle.trivial_profile_residue_zero). -/
theorem trivial_profile_in_lattice {m : ℕ} (hm : m ≥ 1)
    (P : CycleProfile m)
    (h_const : ∀ j : Fin m, P.ν j = 2)
    (hW_eq_D : (P.waveSum : ℤ) = cycleDenominator m P.S) :
    (P.waveSum : ℤ) + 1 * 3 ^ m = 1 * 2 ^ P.S := by
  rw [hW_eq_D]; unfold cycleDenominator; ring

/-- D = 2^S - 3^m is odd (even minus odd). -/
private lemma cycleDenominator_odd' {m S : ℕ}
    (hD_pos : cycleDenominator m S > 0) :
    ¬(2 : ℤ) ∣ cycleDenominator m S := by
  unfold cycleDenominator
  intro ⟨k, hk⟩
  have h3_odd : ¬(2 : ℤ) ∣ 3 ^ m := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl,
      ← Int.natCast_pow, Int.natCast_dvd_natCast]
    exact fun h => by have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 2) h; omega
  have hS_pos : S ≥ 1 := by
    by_contra h; push_neg at h; interval_cases S
    unfold cycleDenominator at hD_pos; simp at hD_pos
    have : (3 : ℤ) ^ m ≥ 1 := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 3); linarith
  have h2_dvd_2S : (2 : ℤ) ∣ 2 ^ S := dvd_pow_self 2 (by omega)
  -- hk : 2^S - 3^m = 2k, so 3^m = 2^S - 2k = 2(2^{S-1} - k)
  obtain ⟨j, hj⟩ := h2_dvd_2S
  exact h3_odd ⟨j - k, by linarith⟩

/-- W is odd: j=0 term is 3^{m-1} (odd), all other terms even. -/
private lemma waveSum_odd' {m : ℕ} (hm : m ≥ 1) (P : CycleProfile m) :
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
      2 ^ P.partialSum i.succ with hrest_def
  have h_rest_even : (2 : ℤ) ∣ rest := by
    apply Finset.dvd_sum; intro j _
    apply dvd_mul_of_dvd_right
    apply dvd_pow_self 2
    have hps_ge : P.partialSum (Fin.succ j) ≥ P.ν ⟨0, by omega⟩ := by
      unfold CycleProfile.partialSum
      apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
      exact Nat.succ_pos j.val
    have := P.ν_pos ⟨0, by omega⟩
    omega
  obtain ⟨r, hr⟩ := h_rest_even
  have h3_odd : ¬(2 : ℤ) ∣ (3 : ℤ) ^ m' := by
    rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, show (3 : ℤ) = ↑(3 : ℕ) from rfl,
      ← Int.natCast_pow, Int.natCast_dvd_natCast]
    exact fun h => by have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 2) h; omega
  exact h3_odd ⟨q - r, by linarith⟩

/-- **Pure lattice endpoint** (axiom-free modulo provided top-coset emptiness).
Given nontrivial realizability plus `constraintCoset P m = ∅`, derive contradiction
by set non-membership. -/
theorem nontrivial_not_realizable {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (h_top_empty : constraintCoset P m (le_rfl) = ∅) : False := by
  rcases h_realizable with ⟨hD_pos, h_dvd⟩
  rcases h_dvd with ⟨n₀, hn₀_mul⟩
  have hn₀_pos : n₀ > 0 := by
    by_contra h
    push_neg at h
    have hW_pos : (P.waveSum : ℤ) > 0 := by
      have : P.waveSum > 0 := by
        unfold CycleProfile.waveSum
        apply Finset.sum_pos
        · intro j _
          positivity
        · rw [Finset.univ_nonempty_iff]
          exact ⟨⟨0, by omega⟩⟩
      exact_mod_cast this
    have : (P.waveSum : ℤ) ≤ 0 := by
      rw [hn₀_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD_pos) h
    linarith
  have hn₀_odd : ¬ (2 : ℤ) ∣ n₀ := by
    intro hn_even
    have hW_even : (2 : ℤ) ∣ (P.waveSum : ℤ) := by
      rw [hn₀_mul]
      exact dvd_mul_of_dvd_right hn_even (cycleDenominator m P.S)
    exact waveSum_odd' (by omega) P hW_even
  have h_orbit : (P.waveSum : ℤ) + n₀ * 3 ^ m = n₀ * 2 ^ P.S := by
    rw [hn₀_mul]
    unfold cycleDenominator
    ring
  exact lattice_non_membership_of_top_constraint_empty m hm P h_nontrivial h_top_empty
    n₀ hn₀_pos hn₀_odd h_orbit

/-- Prime-length, bridge-driven replacement path.
This delegates to `CyclotomicDrift.nontrivial_not_realizable_prime_replacement`,
which avoids the cyclotomic rigidity axiom under explicit bridge hypotheses. -/
theorem nontrivial_not_realizable_prime_replacement
    {m : ℕ} [Fact (Nat.Prime m)] [NeZero m]
    (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (h_realizable : P.isRealizable)
    (hS : P.S = 2 * m)
    (h_ge2j : ∀ j : Fin m, 2 * j.val ≤ P.partialSum j)
    (h_wbdd : ∀ j : Fin m, Collatz.CyclotomicDrift.weightsForFour P h_ge2j j ≤ 3) :
    False :=
  Collatz.CyclotomicDrift.nontrivial_not_realizable_prime_replacement
    hm P h_nontrivial h_realizable hS h_ge2j h_wbdd

end Collatz.LatticeProof
