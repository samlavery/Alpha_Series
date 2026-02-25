import Collatz.MellinOrthogonality.Step6Integrand

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Horizontal segment integral for the contour integrand on height `y`. -/
noncomputable def horizontalIntegral (g : ℂ → ℂ) (σ σ' : ℝ) (y : ℝ) : ℂ :=
  ∫ x : ℝ in σ..σ', spectralIntegrand g (↑x + ↑y * I)

/-- Step-5 decay obligations for the top and bottom horizontal edges. -/
structure HorizontalDecay (g : ℂ → ℂ) (σ σ' : ℝ) : Prop where
  top : Tendsto (horizontalIntegral g σ σ') atTop (nhds 0)
  bot : Tendsto (horizontalIntegral g σ σ') atBot (nhds 0)

theorem tendsto_const_div_one_add_sq_atTop_zero (C : ℝ) :
    Tendsto (fun y : ℝ => C / (1 + y ^ 2)) atTop (nhds 0) := by
  have hnorm : Tendsto (fun y : ℝ => ‖y‖) atTop atTop := tendsto_norm_atTop_atTop
  have habs : Tendsto (fun y : ℝ => |y|) atTop atTop := by
    simpa [Real.norm_eq_abs] using hnorm
  have hsq_abs : Tendsto (fun y : ℝ => |y| ^ (2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp habs
  have hsq : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := by
    refine hsq_abs.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    simp [abs_of_nonneg hy]
  have hden : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop hsq
  have hinv : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop hden
  simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)

theorem tendsto_const_div_one_add_sq_atBot_zero (C : ℝ) :
    Tendsto (fun y : ℝ => C / (1 + y ^ 2)) atBot (nhds 0) := by
  have hTop := tendsto_const_div_one_add_sq_atTop_zero C
  have hComp : Tendsto (fun y : ℝ => C / (1 + (-y) ^ 2)) atBot (nhds 0) :=
    hTop.comp Filter.tendsto_neg_atBot_atTop
  simpa [pow_two] using hComp

theorem horizontalDecay_of_norm_le_const_inv_one_add_sq
    {g : ℂ → ℂ} {σ σ' C : ℝ}
    (hbound : ∀ y : ℝ, ‖horizontalIntegral g σ σ' y‖ ≤ C / (1 + y ^ 2)) :
    HorizontalDecay g σ σ' := by
  have hTopBound : Tendsto (fun y : ℝ => C / (1 + y ^ 2)) atTop (nhds 0) :=
    tendsto_const_div_one_add_sq_atTop_zero C
  have hBotBound : Tendsto (fun y : ℝ => C / (1 + y ^ 2)) atBot (nhds 0) :=
    tendsto_const_div_one_add_sq_atBot_zero C
  have hNormTop : Tendsto (fun y : ℝ => ‖horizontalIntegral g σ σ' y‖) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTopBound ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · filter_upwards using hbound
  have hNormBot : Tendsto (fun y : ℝ => ‖horizontalIntegral g σ σ' y‖) atBot (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBotBound ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · filter_upwards using hbound
  refine ⟨?_, ?_⟩
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormTop
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormBot

theorem horizontalDecay_of_spectralIntegrand_invSqKernel_pointwise
    {σ σ' K : ℝ}
    (hK : 0 ≤ K)
    (hLogDeriv :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ K)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    HorizontalDecay invSqKernel σ σ' := by
  have hbound : ∀ y : ℝ,
      ‖horizontalIntegral invSqKernel σ σ' y‖ ≤ (K * |σ' - σ|) / (1 + y ^ 2) := by
    intro y
    have hpoint : ∀ x ∈ Set.uIoc σ σ', ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ ≤
        K * (1 / (1 + y ^ 2)) := by
      intro x hx
      calc
        ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖
            = ‖zetaLogDeriv (↑x + ↑y * I)‖ * ‖invSqKernel (↑x + ↑y * I)‖ := by
              simp [spectralIntegrand]
        _ ≤ K * ‖invSqKernel (↑x + ↑y * I)‖ := by
              gcongr
              exact hLogDeriv y x hx
        _ ≤ K * (1 / (1 + y ^ 2)) := by
              gcongr
              exact hKernel y x hx
    calc
      ‖horizontalIntegral invSqKernel σ σ' y‖
          ≤ (K * (1 / (1 + y ^ 2))) * |σ' - σ| := by
            simpa [horizontalIntegral] using
              intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := σ')
                (C := K * (1 / (1 + y ^ 2))) hpoint
      _ = (K * |σ' - σ|) / (1 + y ^ 2) := by
            rw [div_eq_mul_inv]
            ring_nf
  exact horizontalDecay_of_norm_le_const_inv_one_add_sq hbound

theorem horizontalDecay_of_spectralIntegrand_invSqKernel_of_vertical_logDeriv_bound
    {σ σ' : ℝ}
    (hσσ' : σ ≤ σ')
    (hσ : 1 < σ)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    HorizontalDecay invSqKernel σ σ' := by
  refine horizontalDecay_of_spectralIntegrand_invSqKernel_pointwise
    (K := ‖zetaLogDeriv σ‖) (by positivity) ?_ hKernel
  intro y x hx
  have hxIoc : x ∈ Set.Ioc σ σ' := by
    simpa [Set.uIoc_of_le hσσ'] using hx
  exact zetaLogDeriv_bound_on_vertical_ge_one hσ (le_of_lt hxIoc.1)

theorem horizontalDecay_of_spectralIntegrand_invSqKernel_of_gt_one
    {σ σ' : ℝ}
    (hσσ' : σ ≤ σ')
    (hσ : 1 < σ) :
    HorizontalDecay invSqKernel σ σ' := by
  have hσ0 : 0 ≤ σ := by linarith
  refine horizontalDecay_of_spectralIntegrand_invSqKernel_of_vertical_logDeriv_bound
    hσσ' hσ ?_
  intro y x hx
  exact invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx

theorem step5Context_of_decay
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
    Step5Context (spectralIntegrand g) σ σ' T := by
  refine step5Context_of_spectralIntegrand
    hσ hOneUpper hOneLower hNonzeroUpper hNonzeroLower hgUpper hgLower ?_ ?_ hLeft hRight
  · simpa [horizontalIntegral] using hDecay.top
  · simpa [horizontalIntegral] using hDecay.bot

end MellinOrthogonality
