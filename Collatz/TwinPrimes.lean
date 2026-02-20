import Collatz.PrimeGapBridge

/-- Twin-primes endpoint routed through `PrimeGapBridge`. -/
theorem twin_primes
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p :=
  PrimeGapBridge.twin_primes hcoord

#print axioms twin_primes
