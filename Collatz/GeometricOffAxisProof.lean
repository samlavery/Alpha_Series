import Collatz.AFECoordinationConstructive

namespace EntangledPair

/-- Off-axis strip nonvanishing follows from RH. -/
theorem off_axis_strip_nonvanishing_of_rh
    (hRH : RiemannHypothesis) :
    OffAxisStripNonvanishingHypothesis := by
  intro s hσ hσ1 hsIm hzero
  have htrivial : ¬∃ n : ℕ, s = -2 * (↑n + 1) := by
    intro h
    rcases h with ⟨n, hn⟩
    have hre : s.re = (-2 * (↑n + 1 : ℂ)).re := congrArg Complex.re hn
    simp at hre
    linarith
  have hone : s ≠ 1 := by
    intro hs1
    have hre : s.re = 1 := congrArg Complex.re hs1
    linarith
  have hre_half : s.re = 1 / 2 := hRH s hzero htrivial hone
  linarith

/-- Geometric off-axis coordination follows from RH via the constructive AFE lift. -/
theorem geometric_off_axis_coordination_of_rh
    (hRH : RiemannHypothesis) :
    GeometricOffAxisCoordinationHypothesis :=
  AFECoordinationConstructive.geometric_off_axis_coordination_of_off_axis_nonvanishing
    (off_axis_strip_nonvanishing_of_rh hRH)

/-- Geometric off-axis coordination from off-axis strip nonvanishing
    (EMD-based constructive lift). -/
theorem geometric_off_axis_coordination_of_off_axis_nonvanishing
    (hoff : OffAxisStripNonvanishingHypothesis) :
    GeometricOffAxisCoordinationHypothesis :=
  AFECoordinationConstructive.geometric_off_axis_coordination_of_off_axis_nonvanishing
    hoff

end EntangledPair

#print axioms EntangledPair.off_axis_strip_nonvanishing_of_rh
#print axioms EntangledPair.geometric_off_axis_coordination_of_rh
#print axioms EntangledPair.geometric_off_axis_coordination_of_off_axis_nonvanishing
