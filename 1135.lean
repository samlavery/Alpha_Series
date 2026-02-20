import Collatz.«1135»

/-- Erdos Problem 1135 endpoint routed through `Collatz.«1135»`. -/
theorem collatz_1135 (n : ℕ) (hn : 0 < n)
    (h_no_nontrivial_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : Collatz.CycleProfile m) → P.isNontrivial → P.isRealizable → False)
    : ∃ k : ℕ, Collatz.collatzIter k n = 1 :=
  erdos_1135_via_mixing n hn h_no_nontrivial_cycles

#print axioms collatz_1135
