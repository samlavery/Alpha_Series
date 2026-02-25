import PrimeNumberTheoremAnd.PerronFormula

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Step-5 interface for a contour-shift integrand. These are exactly the
inputs needed by PNT+'s U-integral vanishing lemmas. -/
structure Step5Context (f : ℂ → ℂ) (σ σ' T : ℝ) : Prop where
  hσ : σ ≤ σ'
  hUpperHol : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ T ≤ z.im}
  hLowerHol : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ -T}
  hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in σ..σ', f (↑x + ↑y * I)) atTop (nhds 0)
  hBot : Tendsto (fun y : ℝ => ∫ x : ℝ in σ..σ', f (↑x + ↑y * I)) atBot (nhds 0)
  hLeft : Integrable fun y : ℝ => f (↑σ + ↑y * I)
  hRight : Integrable fun y : ℝ => f (↑σ' + ↑y * I)

/-- The upper U-tail vanishes from Step-5 hypotheses. -/
theorem upperU_zero {f : ℂ → ℂ} {σ σ' T : ℝ}
    (hctx : Step5Context f σ σ' T) :
    UpperUIntegral f σ σ' T = 0 :=
  Perron.HolomorphicOn.upperUIntegral_eq_zero
    hctx.hσ hctx.hUpperHol hctx.hTop hctx.hLeft hctx.hRight

/-- The lower U-tail vanishes from Step-5 hypotheses. -/
theorem lowerU_zero {f : ℂ → ℂ} {σ σ' T : ℝ}
    (hctx : Step5Context f σ σ' T) :
    LowerUIntegral f σ σ' T = 0 :=
  Perron.HolomorphicOn.lowerUIntegral_eq_zero
    hctx.hσ hctx.hLowerHol hctx.hBot hctx.hLeft hctx.hRight

/-- Contour-shift identity (PNT+), expressed in Step-5 form. -/
theorem contour_shift_identity {f : ℂ → ℂ} {σ σ' T : ℝ}
    (hctx : Step5Context f σ σ' T) :
    VerticalIntegral f σ' - VerticalIntegral f σ -
      RectangleIntegral f (↑σ - I * ↑T) (↑σ' + I * ↑T) =
    UpperUIntegral f σ σ' T - LowerUIntegral f σ σ' T :=
  DiffVertRect_eq_UpperLowerUs hctx.hLeft hctx.hRight

/-- Single-pole contour pull: the vertical-integral difference equals the
small-square contour around the pole (eventually as square radius `c → 0+`). -/
theorem contour_shift_to_small_square {f : ℂ → ℂ} {σ σ' : ℝ} {p : ℂ}
    (hσ : σ < p.re ∧ p.re < σ')
    (hf : HolomorphicOn f (Icc σ σ' ×ℂ univ \ {p}))
    (hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in σ..σ', f (↑x + ↑y * I)) atTop (nhds 0))
    (hBot : Tendsto (fun y : ℝ => ∫ x : ℝ in σ..σ', f (↑x + ↑y * I)) atBot (nhds 0))
    (hLeft : Integrable fun y : ℝ => f (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => f (↑σ' + ↑y * I)) :
    ∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0),
      VerticalIntegral f σ' - VerticalIntegral f σ =
        RectangleIntegral f (-c - c * I + p) (c + c * I + p) :=
  verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    hσ hf hBot hTop hLeft hRight

/-- After Step 5, contour-shift reduces to a zero-tail equation. -/
theorem contour_shift_zero_tails {f : ℂ → ℂ} {σ σ' T : ℝ}
    (hctx : Step5Context f σ σ' T) :
    VerticalIntegral f σ' - VerticalIntegral f σ -
      RectangleIntegral f (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 := by
  calc
    VerticalIntegral f σ' - VerticalIntegral f σ -
        RectangleIntegral f (↑σ - I * ↑T) (↑σ' + I * ↑T)
      = UpperUIntegral f σ σ' T - LowerUIntegral f σ σ' T := contour_shift_identity hctx
    _ = 0 := by simp [upperU_zero hctx, lowerU_zero hctx]

end MellinOrthogonality
