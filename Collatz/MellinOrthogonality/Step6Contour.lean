import Collatz.MellinOrthogonality.Step5Decay

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

theorem contour_shift_zero_tails_spectralIntegrand
    {g : ℂ → ℂ} {σ σ' T : ℝ}
    (hσ : σ ≤ σ')
    (hOneUpper : (1 : ℂ) ∉ upperStrip σ σ' T)
    (hOneLower : (1 : ℂ) ∉ lowerStrip σ σ' T)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ -
      RectangleIntegral (spectralIntegrand g) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 := by
  exact contour_shift_zero_tails
    (step5Context_of_decay hσ hOneUpper hOneLower hNonzeroUpper hNonzeroLower
      hgUpper hgLower hDecay hLeft hRight)

theorem contour_shift_to_small_square_spectralIntegrand
    {g : ℂ → ℂ} {σ σ' : ℝ} {p : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)) :
    ∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0),
      VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ =
        RectangleIntegral (spectralIntegrand g) (-c - c * I + p) (c + c * I + p) := by
  have hStrip :
      HolomorphicOn (spectralIntegrand g) (Icc σ σ' ×ℂ univ \ {p}) := by
    simpa [stripMinusPole] using
      spectralIntegrand_holoOn_stripMinusPole_of_nonzero hOneStrip hNonzeroStrip hgStrip
  exact contour_shift_to_small_square hσp hStrip
    (by simpa [horizontalIntegral] using hDecay.top)
    (by simpa [horizontalIntegral] using hDecay.bot)
    hLeft hRight

theorem contour_shift_zero_tails_invSqKernel_of_gt_one
    {σ σ' T : ℝ}
    (hσσ' : σ ≤ σ')
    (hσ : 1 < σ)
    (hT : 0 < T)
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I)) :
    VerticalIntegral (spectralIntegrand invSqKernel) σ' -
      VerticalIntegral (spectralIntegrand invSqKernel) σ -
      RectangleIntegral (spectralIntegrand invSqKernel) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 := by
  refine contour_shift_zero_tails_spectralIntegrand
    (g := invSqKernel)
    hσσ'
    (one_not_mem_upperStrip_of_pos hT)
    (one_not_mem_lowerStrip_of_pos hT)
    (zeta_nonzero_on_upperStrip_of_one_le (le_of_lt hσ))
    (zeta_nonzero_on_lowerStrip_of_one_le (le_of_lt hσ))
    (invSqKernel_holoOn (neg_one_not_mem_upperStrip_of_one_lt_left hσ))
    (invSqKernel_holoOn (neg_one_not_mem_lowerStrip_of_one_lt_left hσ))
    (horizontalDecay_of_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσ)
    hLeft hRight

end MellinOrthogonality
