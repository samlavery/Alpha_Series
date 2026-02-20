import Collatz.CycleEquation

namespace Collatz.ResidueDynamics

open Collatz.CycleEquation

/-- Residue-based lower envelope for `v2 (3n+1)`. -/
def etaResidue (n : ℕ) : ℕ :=
  if n % 8 = 1 then 2 else if n % 8 = 5 then 3 else 1

/-- For odd `n`, the residue envelope is bounded by the exact valuation. -/
theorem etaResidue_le_v2_of_odd (n : ℕ) (hn : Odd n) :
    etaResidue n ≤ v2 (3 * n + 1) := by
  unfold etaResidue
  have hfin : FiniteMultiplicity (2 : ℕ) (3 * n + 1) := by
    exact (Nat.finiteMultiplicity_iff).2 ⟨by decide, by omega⟩
  by_cases h1 : n % 8 = 1
  · simp [h1]
    have h4 : (4 : ℕ) ∣ 3 * n + 1 := by omega
    have hpow : (2 : ℕ) ^ 2 ∣ 3 * n + 1 := by simpa using h4
    unfold v2
    exact hfin.le_multiplicity_of_pow_dvd hpow
  · by_cases h5 : n % 8 = 5
    · simp [h5]
      have h8 : (8 : ℕ) ∣ 3 * n + 1 := by omega
      have hpow : (2 : ℕ) ^ 3 ∣ 3 * n + 1 := by simpa using h8
      unfold v2
      exact hfin.le_multiplicity_of_pow_dvd hpow
    · simp [h1, h5]
      have h2 : (2 : ℕ) ∣ 3 * n + 1 := by
        obtain ⟨k, hk⟩ := hn
        subst hk
        omega
      have hpow : (2 : ℕ) ^ 1 ∣ 3 * n + 1 := by simpa using h2
      unfold v2
      exact hfin.le_multiplicity_of_pow_dvd hpow

end Collatz.ResidueDynamics
