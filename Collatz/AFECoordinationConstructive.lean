import Collatz.AFEInfrastructure

namespace AFECoordinationConstructive

/-- Pointwise AFE certificate from off-axis nonvanishing in the strip. -/
theorem afe_certificate_at_of_nonvanishing
    (s : ℂ) (hσ : 1 / 2 < s.re) (hσ1 : s.re < 1) (ht : s.im ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    EntangledPair.AFECertificateAt s := by
  rcases AFEInfrastructure.afe_coordination_of_ne_zero
      s.re hσ hσ1 s.im ht hζ with
    ⟨χ_val, X, hX, hdom, herr⟩
  refine ⟨χ_val, X, ‖EntangledPair.S s X‖ - ‖χ_val * EntangledPair.S (1 - s) X‖,
    hX, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- Off-axis strip nonvanishing yields a full off-axis AFE certificate family. -/
theorem afe_certificate_family_of_off_axis_nonvanishing
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    EntangledPair.AFECertificateFamily := by
  intro s hσ hσ1 ht
  exact afe_certificate_at_of_nonvanishing s hσ hσ1 ht (hoff s hσ hσ1 ht)

/-- If off-axis strip nonvanishing is available, then `afe_coordination`
is constructively derivable (no Euler-product bridge needed here). -/
theorem afe_coordination_of_off_axis_nonvanishing
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    ∀ (σ : ℝ), 1 / 2 < σ → σ < 1 →
    ∀ (t : ℝ), t ≠ 0 →
      ∃ (χ_val : ℂ) (X : ℕ), 1 ≤ X ∧
        ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ < ‖EntangledPair.S ⟨σ, t⟩ X‖ ∧
        ‖riemannZeta ⟨σ, t⟩ - EntangledPair.E ⟨σ, t⟩ χ_val X‖ <
          ‖EntangledPair.S ⟨σ, t⟩ X‖ - ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ := by
  intro σ hσ hσ1 t ht
  let s : ℂ := ⟨σ, t⟩
  rcases afe_certificate_family_of_off_axis_nonvanishing hoff s hσ hσ1 ht with
    ⟨χ_val, X, c, hX, _hc, hdom, herr⟩
  refine ⟨χ_val, X, hX, ?_, ?_⟩
  · linarith
  · linarith

/-- Off-axis strip nonvanishing yields the geometric same-`X` coordination
hypothesis (dominance + error gap witness). -/
theorem geometric_off_axis_coordination_of_off_axis_nonvanishing
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    EntangledPair.GeometricOffAxisCoordinationHypothesis := by
  intro σ hσ hσ1 t ht
  let s : ℂ := ⟨σ, t⟩
  rcases afe_certificate_at_of_nonvanishing s hσ hσ1 ht (hoff s hσ hσ1 ht) with
    ⟨χ_val, X, c, hX, hc, hdom, herr⟩
  refine ⟨χ_val, X, c, hX, hc, ?_, ?_⟩
  · simpa [Complex.eta s] using hdom
  · simpa [Complex.eta s] using herr

end AFECoordinationConstructive
