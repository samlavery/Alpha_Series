import Collatz.MellinOrthogonality.Step6Contour

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

theorem aestronglyMeasurable_vertical_spectralIntegrand_invSqKernel_of_gt_one
    {x : ℝ} (hx : 1 < x) :
    AEStronglyMeasurable (fun y : ℝ => spectralIntegrand invSqKernel (↑x + ↑y * I)) volume := by
  have hcontLine : Continuous (fun y : ℝ => (↑x : ℂ) + ↑y * I) := by
    exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hne_one : ∀ y : ℝ, (↑x : ℂ) + ↑y * I ≠ 1 := by
    intro y h
    have hre : ((↑x : ℂ) + ↑y * I).re = 1 := by simp [h]
    have : x = 1 := by simpa using hre
    linarith
  have hzeta_ne : ∀ y : ℝ, riemannZeta ((↑x : ℂ) + ↑y * I) ≠ 0 := by
    intro y
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hx.le)
  have hcontDeriv : Continuous (fun y : ℝ => deriv riemannZeta ((↑x : ℂ) + ↑y * I)) := by
    refine (continuous_iff_continuousAt).2 ?_
    intro y
    have hline_at : ContinuousAt (fun t : ℝ => (↑x : ℂ) + ↑t * I) y := hcontLine.continuousAt
    have hderiv_at :
        DifferentiableAt ℂ (fun s : ℂ => deriv riemannZeta s) ((↑x : ℂ) + ↑y * I) :=
      differentiableAt_deriv_riemannZeta (s := (↑x : ℂ) + ↑y * I) (hne_one y)
    simpa [Function.comp] using
      (ContinuousAt.comp (f := fun t : ℝ => (↑x : ℂ) + ↑t * I) (x := y)
        hderiv_at.continuousAt hline_at)
  have hcontZeta : Continuous (fun y : ℝ => riemannZeta ((↑x : ℂ) + ↑y * I)) := by
    refine (continuous_iff_continuousAt).2 ?_
    intro y
    have hline_at : ContinuousAt (fun t : ℝ => (↑x : ℂ) + ↑t * I) y := hcontLine.continuousAt
    have hzeta_at :
        DifferentiableAt ℂ riemannZeta ((↑x : ℂ) + ↑y * I) :=
      differentiableAt_riemannZeta (s := (↑x : ℂ) + ↑y * I) (hne_one y)
    simpa [Function.comp] using
      (ContinuousAt.comp (f := fun t : ℝ => (↑x : ℂ) + ↑t * I) (x := y)
        hzeta_at.continuousAt hline_at)
  have hcontLogDeriv : Continuous (fun y : ℝ => zetaLogDeriv ((↑x : ℂ) + ↑y * I)) := by
    simpa [zetaLogDeriv] using (Continuous.div hcontDeriv hcontZeta hzeta_ne)
  have hshift_ne : ∀ y : ℝ, ((↑x : ℂ) + ↑y * I) + 1 ≠ 0 := by
    intro y h
    have hre : (((↑x : ℂ) + ↑y * I) + 1).re = 0 := by simp [h]
    have hxeq0 : x + 1 = 0 := by simpa using hre
    have hxeq : x = -1 := by linarith [hxeq0]
    have hfalse : ¬ (1 < x) := by linarith [hxeq]
    exact hfalse hx
  have hcontKernel : Continuous (fun y : ℝ => invSqKernel ((↑x : ℂ) + ↑y * I)) := by
    have hcontInv : Continuous (fun y : ℝ => ((((↑x : ℂ) + ↑y * I) + 1) : ℂ)⁻¹) :=
      Continuous.inv₀ (by continuity) hshift_ne
    simpa [invSqKernel] using hcontInv.pow 2
  exact (hcontLogDeriv.mul hcontKernel).aestronglyMeasurable

theorem integrable_vertical_spectralIntegrand_invSqKernel_of_gt_one
    {x : ℝ} (hx : 1 < x) :
    Integrable (fun y : ℝ => spectralIntegrand invSqKernel (↑x + ↑y * I)) volume := by
  have hmeas :
      AEStronglyMeasurable (fun y : ℝ => spectralIntegrand invSqKernel (↑x + ↑y * I)) volume :=
    aestronglyMeasurable_vertical_spectralIntegrand_invSqKernel_of_gt_one hx
  have hbound : ∀ y : ℝ,
      ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ ≤ ‖zetaLogDeriv x‖ / (1 + y ^ 2) := by
    intro y
    calc
      ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖
          = ‖zetaLogDeriv (↑x + ↑y * I)‖ * ‖invSqKernel (↑x + ↑y * I)‖ := by
            simp [spectralIntegrand]
      _ ≤ ‖zetaLogDeriv x‖ * ‖invSqKernel (↑x + ↑y * I)‖ := by
            gcongr
            exact zetaLogDeriv_bound_on_vertical_ge_one hx (le_rfl)
      _ ≤ ‖zetaLogDeriv x‖ * (1 / (1 + y ^ 2)) := by
            gcongr
            have hx0 : 0 ≤ x := by linarith [hx]
            exact invSqKernel_norm_le_one_div_one_add_sq hx0
      _ = ‖zetaLogDeriv x‖ / (1 + y ^ 2) := by
            simp [div_eq_mul_inv]
  have hbase : Integrable (fun y : ℝ => 1 / (1 + y ^ 2)) volume :=
    Perron.Integrable.one_div_const_add_sq 1 (by positivity)
  have hdom : Integrable (fun y : ℝ => ‖zetaLogDeriv x‖ / (1 + y ^ 2)) volume := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbase.const_mul ‖zetaLogDeriv x‖
  exact Integrable.mono' hdom hmeas (Filter.Eventually.of_forall hbound)

theorem integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one
    {σ σ' : ℝ} (hσσ' : σ ≤ σ') (hσ : 1 < σ) :
    Integrable (fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I)) volume ∧
    Integrable (fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I)) volume := by
  refine ⟨integrable_vertical_spectralIntegrand_invSqKernel_of_gt_one hσ, ?_⟩
  exact integrable_vertical_spectralIntegrand_invSqKernel_of_gt_one (lt_of_lt_of_le hσ hσσ')

theorem contour_shift_zero_tails_invSqKernel_of_gt_one_closed
    {σ σ' T : ℝ}
    (hσσ' : σ ≤ σ')
    (hσ : 1 < σ)
    (hT : 0 < T) :
    VerticalIntegral (spectralIntegrand invSqKernel) σ' -
      VerticalIntegral (spectralIntegrand invSqKernel) σ -
      RectangleIntegral (spectralIntegrand invSqKernel) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 := by
  rcases integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσ with ⟨hLeft, hRight⟩
  exact contour_shift_zero_tails_invSqKernel_of_gt_one hσσ' hσ hT hLeft hRight

end MellinOrthogonality
