/-
  Defs.lean — Core definitions
  =============================

  Pure data and exact algebra. Definitions only.

  Convention: S = ∑ νⱼ is the total halvings.
  Critical ratio: S/m ≈ log₂(3) ≈ 1.585.
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace Collatz

/-! ## Cycle denominator -/

/-- Cycle denominator: D = 2^S − 3^m -/
def cycleDenominator (m S : ℕ) : ℤ := (2 : ℤ) ^ S - 3 ^ m

/-! ## Profile -/

/-- Cycle profile: ν j is the halvings at step j, S = ∑ νⱼ. -/
structure CycleProfile (m : ℕ) where
  ν : Fin m → ℕ
  ν_pos : ∀ j, ν j ≥ 1
  S : ℕ
  sum_ν : ∑ j : Fin m, ν j = S

namespace CycleProfile

variable {m : ℕ} (P : CycleProfile m)

/-- Partial sum: S_j = ν₀ + ⋯ + ν_{j−1} -/
def partialSum (j : Fin m) : ℕ :=
  ∑ i ∈ Finset.univ.filter (· < j), P.ν i

/-- Wave sum: W = ∑_j 3^{m−1−j} · 2^{S_j} -/
def waveSum : ℕ :=
  ∑ j : Fin m, 3 ^ (m - 1 - j.val) * 2 ^ (P.partialSum j)

/-- Excess: E = W − D -/
def excess : ℤ := (P.waveSum : ℤ) - cycleDenominator m P.S

/-- Profile is realizable if D > 0 and D | W. -/
def isRealizable : Prop :=
  cycleDenominator m P.S > 0 ∧ (cycleDenominator m P.S : ℤ) ∣ (P.waveSum : ℤ)

/-- Profile is nontrivial if some νⱼ values differ (not all halvings equal). -/
def isNontrivial : Prop := ∃ j k : Fin m, P.ν j ≠ P.ν k

end CycleProfile

/-! ## Anchored profile -/

/-- An anchored cycle profile includes a base profile together with a chosen
starting integer `n₀` satisfying the orbit-closure equation. This is the
data-level object when you want profile identity to depend on `n₀`. -/
structure AnchoredCycleProfile (m : ℕ) where
  profile : CycleProfile m
  n0 : ℤ
  n0_pos : n0 > 0
  n0_odd : ¬(2 : ℤ) ∣ n0
  orbit_eq : (profile.waveSum : ℤ) + n0 * 3 ^ m = n0 * 2 ^ profile.S

namespace AnchoredCycleProfile

variable {m : ℕ}

/-- Forget the anchor and recover the underlying cycle profile. -/
def toCycleProfile (A : AnchoredCycleProfile m) : CycleProfile m := A.profile

/-- If anchored profiles have different `n₀`, they are different objects. -/
theorem ne_of_n0_ne {A B : AnchoredCycleProfile m} (h : A.n0 ≠ B.n0) : A ≠ B := by
  intro hEq
  exact h (by simpa [hEq])

end AnchoredCycleProfile

/-! ## Evaluation sum -/

/-- Evaluation sum: ∑_r w_r · 4^r · 3^{d−1−r} -/
def evalSum43 (d : ℕ) (w : Fin d → ℕ) : ℤ :=
  ∑ r : Fin d, (w r : ℤ) * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))

/-! ## Folded weights -/

/-- Fold a weight function by residue class mod d. -/
def foldedWeights {m : ℕ} (d : ℕ) (w : Fin m → ℕ) : Fin d → ℕ :=
  fun r => ∑ j : Fin m, if (j : ℕ) % d = r.val then w j else 0

/-! ## Collatz map -/

/-- Standard Collatz map: even → n/2, odd → 3n+1. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- k-fold iteration of the Collatz map. -/
def collatzIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzIter k (collatz n)

end Collatz
