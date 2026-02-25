import Collatz.MellinOrthogonality.Step6PoleModel

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

theorem spectralIntegrand_principalPart_of_zetaLogDeriv_principalPart
    {g : ℂ → ℂ} {p : ℂ}
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hZetaNear :
      (zetaLogDeriv - (fun s : ℂ => (s - p)⁻¹)) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ)) :
    (spectralIntegrand g - (fun s : ℂ => g p / (s - p))) =O[nhdsWithin p {p}ᶜ]
      (1 : ℂ → ℂ) := by
  rcases hgNear with ⟨U, hU, hgU⟩
  have hNearOne :
      (zetaLogDeriv - (fun s : ℂ => (1 : ℂ) * (s - p)⁻¹)) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ) := by
    simpa using hZetaNear
  have hmult :
      (zetaLogDeriv * g - (fun s : ℂ => (1 : ℂ) * g p * (s - p)⁻¹))
        =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) :=
    ResidueMult (f := zetaLogDeriv) (g := g) (p := p) (U := U) hgU hU hNearOne
  simpa [spectralIntegrand, div_eq_mul_inv] using hmult

theorem vertical_diff_ne_zero_of_zetaLogDeriv_principalPart
    {g : ℂ → ℂ} {σ σ' : ℝ} {p : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hZetaNear :
      (zetaLogDeriv - (fun s : ℂ => (s - p)⁻¹)) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ))
    (hgp : g p ≠ 0) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ ≠ 0 := by
  have hNear :
      (spectralIntegrand g - (fun s : ℂ => g p / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ) :=
    spectralIntegrand_principalPart_of_zetaLogDeriv_principalPart
      (g := g) (p := p) hgNear hZetaNear
  exact vertical_diff_ne_zero_of_simplePole_of_strip
    (g := g) (σ := σ) (σ' := σ') (p := p) (A := g p)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hNear hgp

end MellinOrthogonality
