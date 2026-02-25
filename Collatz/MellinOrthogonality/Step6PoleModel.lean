import Collatz.MellinOrthogonality.Step6Residue

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Off-line pole model in the contour strip: `p` lies strictly between
two contour lines and carries a nonzero simple-pole residue term for the
spectral integrand. -/
structure OffLinePoleModel (g : ℂ → ℂ) (σ σ' : ℝ) (p A : ℂ) : Prop where
  hσp : σ < p.re ∧ p.re < σ'
  hOffLine : p.re ≠ (1 / 2 : ℝ)
  hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p
  hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0
  hgStrip : HolomorphicOn g (stripMinusPole σ σ' p)
  hDecay : HorizontalDecay g σ σ'
  hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I)
  hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)
  hNear :
    (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
      (1 : ℂ → ℂ)
  hA : A ≠ 0

theorem vertical_diff_ne_zero_of_offLinePoleModel
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hmodel : OffLinePoleModel g σ σ' p A) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ ≠ 0 :=
  vertical_diff_ne_zero_of_simplePole_of_strip
    (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
    hmodel.hσp hmodel.hOneStrip hmodel.hNonzeroStrip hmodel.hgStrip hmodel.hDecay
    hmodel.hLeft hmodel.hRight hmodel.hNear hmodel.hA

end MellinOrthogonality
