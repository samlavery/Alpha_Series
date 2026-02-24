/-
  CycleEquation.lean — The orbit telescoping equation
  ====================================================

  Derives the Syracuse iteration formula and proves the cycle equation:
    n₀ · (2^S − 3^m) = c_m
  where c_m is the path constant (shown equal to the wavesum representation).

  Key results:
  * `orbit_iteration_formula`: T^k(n) · 2^{S_k} = 3^k · n + c_k
  * `orbitC_eq_wavesum`: c_k = ∑_{j<k} 3^{k−1−j} · 2^{S_j}
  * `cycle_equation`: n · (2^S − 3^m) = c_m  for period-m orbits
-/
import Collatz.Defs

open Collatz
open scoped BigOperators

namespace Collatz.CycleEquation

set_option linter.unusedVariables false

/-! ## Orbit definitions -/

/-- 2-adic valuation: the largest power of 2 dividing n. -/
noncomputable def v2 (n : ℕ) : ℕ := multiplicity 2 n

/-- Odd Syracuse map: T(n) = (3n+1) / 2^{ν₂(3n+1)}, maps odd → odd. -/
noncomputable def collatzOdd (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ v2 (3 * n + 1)

/-- k-fold iteration of the odd Syracuse map. -/
noncomputable def collatzOddIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzOddIter k (collatzOdd n)

/-- Halvings at step j: ν_j = ν₂(3 · T^j(n) + 1). -/
noncomputable def orbitNu (n : ℕ) (j : ℕ) : ℕ :=
  v2 (3 * collatzOddIter j n + 1)

/-! ## Iteration commutativity -/

/-- Iteration formula commutes: T^{k+1}(n) = T(T^k(n)). -/
lemma collatzOddIter_succ_right (k n : ℕ) :
    collatzOddIter (k + 1) n = collatzOdd (collatzOddIter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    show collatzOddIter (k + 1) (collatzOdd n) = collatzOdd (collatzOddIter (k + 1) n)
    rw [ih (collatzOdd n)]
    congr 1

/-- Iteration composition: T^{a+b}(n) = T^a(T^b(n)). -/
lemma collatzOddIter_add (a b n : ℕ) :
    collatzOddIter (a + b) n = collatzOddIter a (collatzOddIter b n) := by
  induction a generalizing n with
  | zero => simp [collatzOddIter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 from by omega]
    rw [collatzOddIter_succ_right, collatzOddIter_succ_right]
    congr 1
    exact ih n

/-! ## 2-adic valuation properties -/

lemma pow_v2_dvd (m : ℕ) (hm : m ≠ 0) : 2 ^ v2 m ∣ m :=
  pow_multiplicity_dvd 2 m

private lemma not_pow_v2_succ_dvd (m : ℕ) (hm : m ≠ 0) : ¬ 2 ^ (v2 m + 1) ∣ m := by
  apply not_pow_dvd_of_emultiplicity_lt
  unfold v2
  have hfin : FiniteMultiplicity (2 : ℕ) m :=
    FiniteMultiplicity.of_prime_left (Nat.Prime.prime (by decide : Nat.Prime 2)) hm
  rw [hfin.emultiplicity_eq_multiplicity]
  exact_mod_cast Nat.lt_succ_of_le (le_refl (multiplicity 2 m))

/-- Syracuse step formula: T(n) · 2^{ν₂(3n+1)} = 3n + 1 -/
lemma syracuse_step_formula (n : ℕ) (hn : Odd n) :
    collatzOdd n * 2 ^ v2 (3 * n + 1) = 3 * n + 1 := by
  unfold collatzOdd
  have h_ne : 3 * n + 1 ≠ 0 := by omega
  exact Nat.div_mul_cancel (pow_v2_dvd _ h_ne)

/-- Orbit step formula: T^{j+1}(n) · 2^{ν_j} = 3 · T^j(n) + 1 -/
lemma orbit_step (n : ℕ) (hn : Odd n) (j : ℕ)
    (h_odd : Odd (collatzOddIter j n)) :
    collatzOddIter (j + 1) n * 2 ^ orbitNu n j =
      3 * collatzOddIter j n + 1 := by
  rw [collatzOddIter_succ_right]
  unfold orbitNu
  exact syracuse_step_formula (collatzOddIter j n) h_odd

/-! ## Oddness preservation

The odd Syracuse map preserves oddness: if n is odd and positive,
then T(n) is odd. This extends by induction to all iterates T^k(n). -/

lemma collatzOdd_odd {n : ℕ} (hn : Odd n) (hn_pos : 0 < n) :
    Odd (collatzOdd n) := by
  have h_step := syracuse_step_formula n hn
  by_contra h_not_odd
  rw [Nat.not_odd_iff_even] at h_not_odd
  obtain ⟨r, hr⟩ := h_not_odd
  have h_ne : 3 * n + 1 ≠ 0 := by omega
  have h_div2 : 2 ^ (v2 (3 * n + 1) + 1) ∣ (3 * n + 1) := by
    use r
    rw [pow_succ, mul_assoc]
    linarith [show collatzOdd n * 2 ^ v2 (3 * n + 1) = 2 * r * 2 ^ v2 (3 * n + 1) from by rw [hr]; ring]
  exact not_pow_v2_succ_dvd _ h_ne h_div2

lemma collatzOddIter_odd {n : ℕ} (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    Odd (collatzOddIter k n) := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    show Odd (collatzOddIter k (collatzOdd n))
    have h_odd_T := collatzOdd_odd hn hn_pos
    have h_pos_T : 0 < collatzOdd n := by
      unfold collatzOdd
      have h_ne : 3 * n + 1 ≠ 0 := by omega
      have h_dvd := pow_v2_dvd (3 * n + 1) h_ne
      exact Nat.div_pos (Nat.le_of_dvd (by omega) h_dvd) (by positivity)
    exact ih h_odd_T h_pos_T

lemma collatzOddIter_pos {n : ℕ} (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    0 < collatzOddIter k n := by
  have := collatzOddIter_odd hn hn_pos k
  obtain ⟨r, hr⟩ := this
  omega

/-! ## Orbit partial sums and path constant -/

/-- Partial sum S_k = Σ_{j=0}^{k-1} ν_j -/
noncomputable def orbitS (n : ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, orbitNu n j

@[simp] lemma orbitS_zero (n : ℕ) : orbitS n 0 = 0 := by
  unfold orbitS; simp

lemma orbitS_succ (n : ℕ) (k : ℕ) :
    orbitS n (k + 1) = orbitS n k + orbitNu n k := by
  unfold orbitS
  rw [Finset.sum_range_succ]

/-- Path constant: c_0 = 0, c_{k+1} = 3c_k + 2^{S_k} -/
noncomputable def orbitC (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * orbitC n k + 2 ^ orbitS n k

@[simp] lemma orbitC_zero (n : ℕ) : orbitC n 0 = 0 := rfl

lemma orbitC_succ (n : ℕ) (k : ℕ) :
    orbitC n (k + 1) = 3 * orbitC n k + 2 ^ orbitS n k := rfl

/-! ## The iteration formula -/

/-- Orbit iteration formula: T^k(n) · 2^{S_k} = 3^k · n + c_k -/
theorem orbit_iteration_formula {n : ℕ} (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    collatzOddIter k n * 2 ^ orbitS n k = 3 ^ k * n + orbitC n k := by
  induction k with
  | zero =>
    simp [collatzOddIter, orbitS_zero, orbitC_zero]
  | succ k ih =>
    rw [orbitS_succ, pow_add]
    have h_odd_k := collatzOddIter_odd hn hn_pos k
    calc collatzOddIter (k + 1) n * (2 ^ orbitS n k * 2 ^ orbitNu n k)
        = collatzOddIter (k + 1) n * 2 ^ orbitNu n k * 2 ^ orbitS n k := by ring
      _ = (3 * collatzOddIter k n + 1) * 2 ^ orbitS n k := by
          rw [orbit_step n hn k h_odd_k]
      _ = 3 * collatzOddIter k n * 2 ^ orbitS n k + 2 ^ orbitS n k := by ring
      _ = 3 * (collatzOddIter k n * 2 ^ orbitS n k) + 2 ^ orbitS n k := by ring
      _ = 3 * (3 ^ k * n + orbitC n k) + 2 ^ orbitS n k := by rw [ih]
      _ = 3 ^ (k + 1) * n + (3 * orbitC n k + 2 ^ orbitS n k) := by ring
      _ = 3 ^ (k + 1) * n + orbitC n (k + 1) := by rw [← orbitC_succ]

/-! ## Wavesum representation -/

/-- Path constant equals wavesum: c_k = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{S_j} -/
theorem orbitC_eq_wavesum (n : ℕ) (k : ℕ) :
    orbitC n k = ∑ j ∈ Finset.range k, 3 ^ (k - 1 - j) * 2 ^ orbitS n j := by
  induction k with
  | zero => simp [orbitC_zero]
  | succ k ih =>
    rw [orbitC_succ, ih, Finset.sum_range_succ]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show k + 1 - 1 - j = (k - 1 - j) + 1 from by omega, pow_succ]
      ring
    · rw [show k + 1 - 1 - k = 0 from by omega, pow_zero, one_mul]

/-! ## The cycle equation

Setting k = m and using the periodicity condition T^m(n) = n in the
iteration formula yields the fundamental cycle equation. -/

/-- Cycle equation: n · (2^S − 3^m) = c_m for periodic orbits of odd-step period m. -/
theorem cycle_equation {n : ℕ} (hn : Odd n) (hn_pos : 0 < n) {m : ℕ} (hm : 0 < m)
    (h_cycle : collatzOddIter m n = n) :
    (n : ℤ) * ((2 : ℤ) ^ orbitS n m - 3 ^ m) = ↑(orbitC n m) := by
  have h_iter := orbit_iteration_formula hn hn_pos m
  rw [h_cycle] at h_iter
  have h_iter' : (n : ℤ) * 2 ^ orbitS n m = 3 ^ m * n + ↑(orbitC n m) := by
    exact_mod_cast h_iter
  linarith

/-- Path constant is positive for m ≥ 1. -/
lemma orbitC_pos (n : ℕ) {m : ℕ} (hm : 0 < m) : 0 < orbitC n m := by
  cases m with
  | zero => omega
  | succ k =>
    rw [orbitC_succ]
    have : 0 < 2 ^ orbitS n k := by positivity
    omega

/-- For periodic orbits, 2^{S_m} > 3^m (equivalently, D > 0). Follows from
c_m > 0 and the cycle equation n · D = c_m with n > 0. -/
theorem cycle_S_gt (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) {m : ℕ} (hm : 0 < m)
    (h_cycle : collatzOddIter m n = n) :
    2 ^ orbitS n m > 3 ^ m := by
  have h_iter := orbit_iteration_formula hn hn_pos m
  rw [h_cycle] at h_iter
  have h_c_pos := orbitC_pos n hm
  nlinarith

end Collatz.CycleEquation
