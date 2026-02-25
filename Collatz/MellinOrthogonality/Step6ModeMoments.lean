import Collatz.MellinOrthogonality.Step6Final

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Rotated-strip mode-moment data for a witness `f`: a raw mode moment `M`,
a contour-side expression `C`, and vanishing of `C`.  This is the concrete
shape expected from contour-shift execution in the rotated strip. -/
structure RotatedStripModeMomentData
    (γ : ℕ → ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) where
  M : ℕ → ℂ
  C : ℕ → ℂ
  hMomentEq : ∀ n : ℕ, onLineModeMoment γ f n = M n
  hContourEq : ∀ n : ℕ, M n = C n
  hContourZero : ∀ n : ℕ, C n = 0

def rotatedStripModeMomentData_of_equations
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)} {M C : ℕ → ℂ}
    (hMomentEq : ∀ n : ℕ, onLineModeMoment γ f n = M n)
    (hContourEq : ∀ n : ℕ, M n = C n)
    (hContourZero : ∀ n : ℕ, C n = 0) :
    RotatedStripModeMomentData γ f where
  M := M
  C := C
  hMomentEq := hMomentEq
  hContourEq := hContourEq
  hContourZero := hContourZero

/-- Canonical contour expression for the `n`-th mode as a vertical-integral
difference between the two contour lines. -/
noncomputable def modeVerticalDiff
    (F : ℕ → ℂ → ℂ) (σ σ' : ℝ) (n : ℕ) : ℂ :=
  VerticalIntegral (F n) σ' - VerticalIntegral (F n) σ

/-- Rotated-strip exponential mode twist at frequency `ξ`. -/
noncomputable def modeTwist (ξ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-((ξ : ℂ) * s))

/-- Contour integrand for a single on-line mode. -/
noncomputable def onLineModeContourIntegrand (g : ℂ → ℂ) (ξ : ℝ) (s : ℂ) : ℂ :=
  spectralIntegrand g s * modeTwist ξ s

/-- Family of contour integrands indexed by on-line frequencies `γ n`. -/
noncomputable def onLineModeContourFamily (g : ℂ → ℂ) (γ : ℕ → ℝ) :
    ℕ → ℂ → ℂ :=
  fun n : ℕ => onLineModeContourIntegrand g (γ n)

/-- Weighted horizontal segment integral used for rotated-strip mode tails. -/
noncomputable def weightedHorizontalIntegral
    (g : ℂ → ℂ) (ξ σ σ' : ℝ) (y : ℝ) : ℂ :=
  ∫ x : ℝ in σ..σ',
    Complex.exp (-((ξ : ℂ) * (x : ℂ))) * spectralIntegrand g (↑x + ↑y * I)

/-- Top/bottom decay package for weighted horizontal mode tails. -/
structure WeightedHorizontalDecay (g : ℂ → ℂ) (ξ σ σ' : ℝ) : Prop where
  top : Tendsto (weightedHorizontalIntegral g ξ σ σ') atTop (nhds 0)
  bot : Tendsto (weightedHorizontalIntegral g ξ σ σ') atBot (nhds 0)

theorem weightedHorizontalDecay_of_norm_le_of_tendsto
    {g : ℂ → ℂ} {ξ σ σ' : ℝ} {B : ℝ → ℝ}
    (hbound : ∀ y : ℝ, ‖weightedHorizontalIntegral g ξ σ σ' y‖ ≤ B y)
    (hTopB : Tendsto B atTop (nhds 0))
    (hBotB : Tendsto B atBot (nhds 0)) :
    WeightedHorizontalDecay g ξ σ σ' := by
  have hNormTop :
      Tendsto (fun y : ℝ => ‖weightedHorizontalIntegral g ξ σ σ' y‖) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTopB ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · filter_upwards using hbound
  have hNormBot :
      Tendsto (fun y : ℝ => ‖weightedHorizontalIntegral g ξ σ σ' y‖) atBot (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBotB ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · filter_upwards using hbound
  refine ⟨?_, ?_⟩
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormTop
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormBot

theorem weightedHorizontalDecay_of_eventually_norm_le_of_tendsto
    {g : ℂ → ℂ} {ξ σ σ' : ℝ} {B : ℝ → ℝ}
    (hTopBound :
      ∀ᶠ y : ℝ in atTop, ‖weightedHorizontalIntegral g ξ σ σ' y‖ ≤ B y)
    (hBotBound :
      ∀ᶠ y : ℝ in atBot, ‖weightedHorizontalIntegral g ξ σ σ' y‖ ≤ B y)
    (hTopB : Tendsto B atTop (nhds 0))
    (hBotB : Tendsto B atBot (nhds 0)) :
    WeightedHorizontalDecay g ξ σ σ' := by
  have hNormTop :
      Tendsto (fun y : ℝ => ‖weightedHorizontalIntegral g ξ σ σ' y‖) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTopB ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · exact hTopBound
  have hNormBot :
      Tendsto (fun y : ℝ => ‖weightedHorizontalIntegral g ξ σ σ' y‖) atBot (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBotB ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · exact hBotBound
  refine ⟨?_, ?_⟩
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormTop
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormBot

theorem weightedHorizontalDecay_of_norm_le_const_inv_one_add_sq
    {g : ℂ → ℂ} {ξ σ σ' C : ℝ}
    (hbound : ∀ y : ℝ,
      ‖weightedHorizontalIntegral g ξ σ σ' y‖ ≤ C / (1 + y ^ 2)) :
    WeightedHorizontalDecay g ξ σ σ' := by
  have hTopBound : Tendsto (fun y : ℝ => C / (1 + y ^ 2)) atTop (nhds 0) :=
    tendsto_const_div_one_add_sq_atTop_zero C
  have hBotBound : Tendsto (fun y : ℝ => C / (1 + y ^ 2)) atBot (nhds 0) :=
    tendsto_const_div_one_add_sq_atBot_zero C
  have hNormTop :
      Tendsto (fun y : ℝ => ‖weightedHorizontalIntegral g ξ σ σ' y‖) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTopBound ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · filter_upwards using hbound
  have hNormBot :
      Tendsto (fun y : ℝ => ‖weightedHorizontalIntegral g ξ σ σ' y‖) atBot (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBotBound ?_ ?_
    · filter_upwards using fun _ => norm_nonneg _
    · filter_upwards using hbound
  refine ⟨?_, ?_⟩
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormTop
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormBot

theorem weightedHorizontalDecay_of_pointwise_norm_le_const_inv_one_add_sq
    {g : ℂ → ℂ} {ξ σ σ' C : ℝ}
    (hpoint :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ))) * spectralIntegrand g (↑x + ↑y * I)‖
          ≤ C / (1 + y ^ 2)) :
    WeightedHorizontalDecay g ξ σ σ' := by
  have hbound : ∀ y : ℝ,
      ‖weightedHorizontalIntegral g ξ σ σ' y‖ ≤ (C * |σ' - σ|) / (1 + y ^ 2) := by
    intro y
    calc
      ‖weightedHorizontalIntegral g ξ σ σ' y‖
          ≤ (C / (1 + y ^ 2)) * |σ' - σ| := by
            simpa [weightedHorizontalIntegral] using
              intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := σ')
                (C := C / (1 + y ^ 2))
                (fun x hx => hpoint y x hx)
      _ = (C * |σ' - σ|) / (1 + y ^ 2) := by
            rw [div_eq_mul_inv]
            ring_nf
  exact weightedHorizontalDecay_of_norm_le_const_inv_one_add_sq hbound

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_pointwise
    {ξ σ σ' K W : ℝ}
    (hW : 0 ≤ W)
    (hK : 0 ≤ K)
    (hWeight :
      ∀ (x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ ≤ W)
    (hLogDeriv :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ K)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  refine weightedHorizontalDecay_of_pointwise_norm_le_const_inv_one_add_sq
    (g := invSqKernel) (ξ := ξ) (σ := σ) (σ' := σ') (C := W * K) ?_
  intro y x hx
  calc
    ‖Complex.exp (-((ξ : ℂ) * (x : ℂ))) * spectralIntegrand invSqKernel (↑x + ↑y * I)‖
        = ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ *
            ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ := by
              simp [norm_mul]
    _ ≤ W * ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ := by
          gcongr
          exact hWeight x hx
    _ = W * (‖zetaLogDeriv (↑x + ↑y * I)‖ * ‖invSqKernel (↑x + ↑y * I)‖) := by
          simp [spectralIntegrand, mul_assoc]
    _ ≤ W * (K * ‖invSqKernel (↑x + ↑y * I)‖) := by
          gcongr
          exact hLogDeriv y x hx
    _ ≤ W * (K * (1 / (1 + y ^ 2))) := by
          gcongr
          exact hKernel y x hx
    _ = (W * K) / (1 + y ^ 2) := by
          rw [div_eq_mul_inv]
          ring_nf

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope
    {ξ σ σ' W : ℝ} {L : ℝ → ℝ}
    (hW : 0 ≤ W)
    (hLnonneg : ∀ y : ℝ, 0 ≤ L y)
    (hWeight :
      ∀ (x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ ≤ W)
    (hLogDeriv :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2))
    (hTop :
      Tendsto (fun y : ℝ =>
        (W * |σ' - σ|) * (L y / (1 + y ^ 2))) atTop (nhds 0))
    (hBot :
      Tendsto (fun y : ℝ =>
        (W * |σ' - σ|) * (L y / (1 + y ^ 2))) atBot (nhds 0)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  have hbound :
      ∀ y : ℝ,
        (∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y) →
        ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖
          ≤ (W * |σ' - σ|) * (L y / (1 + y ^ 2)) := by
    intro y
    intro hLogDerivY
    have hpoint :
      ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ))) *
            spectralIntegrand invSqKernel (↑x + ↑y * I)‖
          ≤ W * (L y / (1 + y ^ 2)) := by
        intro x hx
        calc
          ‖Complex.exp (-((ξ : ℂ) * (x : ℂ))) * spectralIntegrand invSqKernel (↑x + ↑y * I)‖
              = ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ *
                  ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ := by
                    simp [norm_mul]
          _ ≤ W * ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ := by
                gcongr
                exact hWeight x hx
          _ = W * (‖zetaLogDeriv (↑x + ↑y * I)‖ * ‖invSqKernel (↑x + ↑y * I)‖) := by
                simp [spectralIntegrand]
          _ ≤ W * (L y * ‖invSqKernel (↑x + ↑y * I)‖) := by
                gcongr
                exact hLogDerivY x hx
          _ ≤ W * (L y * (1 / (1 + y ^ 2))) := by
                have hmul :
                    L y * ‖invSqKernel (↑x + ↑y * I)‖ ≤
                      L y * (1 / (1 + y ^ 2)) :=
                  mul_le_mul_of_nonneg_left (hKernel y x hx) (hLnonneg y)
                exact mul_le_mul_of_nonneg_left hmul hW
          _ = W * (L y / (1 + y ^ 2)) := by ring
    calc
        ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖
            ≤ (W * (L y / (1 + y ^ 2))) * |σ' - σ| := by
              simpa [weightedHorizontalIntegral] using
                intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := σ')
                  (C := W * (L y / (1 + y ^ 2)))
                  (fun x hx => hpoint x hx)
        _ = (W * |σ' - σ|) * (L y / (1 + y ^ 2)) := by ring
  have hboundAll : ∀ y : ℝ,
      ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖
        ≤ (W * |σ' - σ|) * (L y / (1 + y ^ 2)) := by
    intro y
    exact hbound y (fun x hx => hLogDeriv y x hx)
  exact weightedHorizontalDecay_of_norm_le_of_tendsto hboundAll hTop hBot

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_eventually
    {ξ σ σ' W : ℝ} {L : ℝ → ℝ}
    (hW : 0 ≤ W)
    (hLnonneg : ∀ y : ℝ, 0 ≤ L y)
    (hWeight :
      ∀ (x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ ≤ W)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2))
    (hTopRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atTop (nhds 0))
    (hBotRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atBot (nhds 0)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  have hbound :
      ∀ y : ℝ,
        (∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y) →
        ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖
          ≤ (W * |σ' - σ|) * (L y / (1 + y ^ 2)) := by
    intro y hLogDerivY
    have hpoint :
      ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ))) *
            spectralIntegrand invSqKernel (↑x + ↑y * I)‖
          ≤ W * (L y / (1 + y ^ 2)) := by
        intro x hx
        calc
          ‖Complex.exp (-((ξ : ℂ) * (x : ℂ))) * spectralIntegrand invSqKernel (↑x + ↑y * I)‖
              = ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ *
                  ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ := by
                    simp [norm_mul]
          _ ≤ W * ‖spectralIntegrand invSqKernel (↑x + ↑y * I)‖ := by
                gcongr
                exact hWeight x hx
          _ = W * (‖zetaLogDeriv (↑x + ↑y * I)‖ * ‖invSqKernel (↑x + ↑y * I)‖) := by
                simp [spectralIntegrand]
          _ ≤ W * (L y * ‖invSqKernel (↑x + ↑y * I)‖) := by
                gcongr
                exact hLogDerivY x hx
          _ ≤ W * (L y * (1 / (1 + y ^ 2))) := by
                have hmul :
                    L y * ‖invSqKernel (↑x + ↑y * I)‖ ≤
                      L y * (1 / (1 + y ^ 2)) :=
                  mul_le_mul_of_nonneg_left (hKernel y x hx) (hLnonneg y)
                exact mul_le_mul_of_nonneg_left hmul hW
          _ = W * (L y / (1 + y ^ 2)) := by ring
    calc
      ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖
          ≤ (W * (L y / (1 + y ^ 2))) * |σ' - σ| := by
            simpa [weightedHorizontalIntegral] using
              intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := σ')
                (C := W * (L y / (1 + y ^ 2)))
                (fun x hx => hpoint x hx)
      _ = (W * |σ' - σ|) * (L y / (1 + y ^ 2)) := by ring
  have hTopBound :
      ∀ᶠ y : ℝ in atTop,
        ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖ ≤
          (W * |σ' - σ|) * (L y / (1 + y ^ 2)) :=
    hLogDerivTop.mono (fun y hy => hbound y hy)
  have hBotBound :
      ∀ᶠ y : ℝ in atBot,
        ‖weightedHorizontalIntegral invSqKernel ξ σ σ' y‖ ≤
          (W * |σ' - σ|) * (L y / (1 + y ^ 2)) :=
    hLogDerivBot.mono (fun y hy => hbound y hy)
  have hTop :
      Tendsto (fun y : ℝ => (W * |σ' - σ|) * (L y / (1 + y ^ 2))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hTopRatio)
  have hBot :
      Tendsto (fun y : ℝ => (W * |σ' - σ|) * (L y / (1 + y ^ 2))) atBot (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hBotRatio)
  exact weightedHorizontalDecay_of_eventually_norm_le_of_tendsto
    hTopBound hBotBound hTop hBot

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio
    {ξ σ σ' W : ℝ} {L : ℝ → ℝ}
    (hW : 0 ≤ W)
    (hLnonneg : ∀ y : ℝ, 0 ≤ L y)
    (hWeight :
      ∀ (x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ ≤ W)
    (hLogDeriv :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2))
    (hTopRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atTop (nhds 0))
    (hBotRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atBot (nhds 0)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  have hTop :
      Tendsto (fun y : ℝ => (W * |σ' - σ|) * (L y / (1 + y ^ 2))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hTopRatio)
  have hBot :
      Tendsto (fun y : ℝ => (W * |σ' - σ|) * (L y / (1 + y ^ 2))) atBot (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hBotRatio)
  exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope
    (ξ := ξ) (σ := σ) (σ' := σ') (W := W) (L := L)
    hW hLnonneg hWeight hLogDeriv hKernel hTop hBot

theorem modeWeight_norm_bound_on_uIoc
    {ξ σ σ' : ℝ} {x : ℝ} (hx : x ∈ Set.uIoc σ σ') :
    ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ ≤
      Real.exp (|ξ| * max |σ| |σ'|) := by
  have hx' : x ∈ Set.uIcc σ σ' := Set.uIoc_subset_uIcc hx
  rcases hx' with ⟨hx1, hx2⟩
  let M : ℝ := max |σ| |σ'|
  have hminLower : -M ≤ min σ σ' := by
    refine le_min ?_ ?_
    · exact (neg_le_neg (le_max_left |σ| |σ'|)).trans (neg_abs_le σ)
    · exact (neg_le_neg (le_max_right |σ| |σ'|)).trans (neg_abs_le σ')
  have hmaxUpper : max σ σ' ≤ M := by
    refine max_le ?_ ?_
    · exact (le_abs_self σ).trans (le_max_left |σ| |σ'|)
    · exact (le_abs_self σ').trans (le_max_right |σ| |σ'|)
  have hxab : |x| ≤ M := by
    exact (abs_le).2 ⟨le_trans hminLower hx1, le_trans hx2 hmaxUpper⟩
  have hlin : -(ξ * x) ≤ |ξ| * max |σ| |σ'| := by
    calc
      -(ξ * x) ≤ |ξ * x| := neg_le_abs (ξ * x)
      _ = |ξ| * |x| := abs_mul ξ x
      _ ≤ |ξ| * max |σ| |σ'| := by
            gcongr
  calc
    ‖Complex.exp (-((ξ : ℂ) * (x : ℂ)))‖ = Real.exp (-(ξ * x)) := by
      simp [Complex.norm_exp]
    _ ≤ Real.exp (|ξ| * max |σ| |σ'|) := by
      exact Real.exp_le_exp.mpr hlin

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_autoWeight
    {ξ σ σ' : ℝ} {L : ℝ → ℝ}
    (hLnonneg : ∀ y : ℝ, 0 ≤ L y)
    (hLogDeriv :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2))
    (hTopRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atTop (nhds 0))
    (hBotRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atBot (nhds 0)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  refine weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio
    (ξ := ξ) (σ := σ) (σ' := σ')
    (W := Real.exp (|ξ| * max |σ| |σ'|)) (L := L)
    (by positivity) hLnonneg ?_ hLogDeriv hKernel hTopRatio hBotRatio
  intro x hx
  exact modeWeight_norm_bound_on_uIoc (ξ := ξ) (σ := σ) (σ' := σ') hx

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_autoWeight_eventually
    {ξ σ σ' : ℝ} {L : ℝ → ℝ}
    (hLnonneg : ∀ y : ℝ, 0 ≤ L y)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2))
    (hTopRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atTop (nhds 0))
    (hBotRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atBot (nhds 0)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  refine weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_eventually
    (ξ := ξ) (σ := σ) (σ' := σ')
    (W := Real.exp (|ξ| * max |σ| |σ'|)) (L := L)
    (by positivity) hLnonneg ?_ hLogDerivTop hLogDerivBot hKernel hTopRatio hBotRatio
  intro x hx
  exact modeWeight_norm_bound_on_uIoc (ξ := ξ) (σ := σ) (σ' := σ') hx

private theorem logSq_ratio_le_scaled_shiftRatio (y : ℝ) :
    (Real.log (2 + |y|)) ^ 2 / (1 + y ^ 2) ≤
      9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2) := by
  have hnum_nonneg : 0 ≤ (Real.log (2 + |y|)) ^ 2 := by positivity
  have hdiv :
      (1 : ℝ) / (1 + y ^ 2) ≤ (9 : ℝ) / (2 + |y|) ^ 2 := by
    have hcmp : (2 + |y|) ^ 2 ≤ 9 * (1 + y ^ 2) := by
      calc
        (2 + |y|) ^ 2 ≤ 9 * (1 + |y| ^ 2) := by nlinarith [abs_nonneg y]
        _ = 9 * (1 + y ^ 2) := by simpa [sq]
    have hcmp' : (2 + |y|) ^ 2 / 9 ≤ 1 + y ^ 2 := by
      nlinarith [hcmp]
    have hpos : 0 < (2 + |y|) ^ 2 / 9 := by positivity
    have hinv : (1 : ℝ) / (1 + y ^ 2) ≤ 1 / ((2 + |y|) ^ 2 / 9) :=
      one_div_le_one_div_of_le hpos hcmp'
    have hrewrite : (1 : ℝ) / ((2 + |y|) ^ 2 / 9) = (9 : ℝ) / (2 + |y|) ^ 2 := by
      field_simp [pow_two]
    simpa [hrewrite] using hinv
  calc
    (Real.log (2 + |y|)) ^ 2 / (1 + y ^ 2)
        = (Real.log (2 + |y|)) ^ 2 * ((1 : ℝ) / (1 + y ^ 2)) := by ring
    _ ≤ (Real.log (2 + |y|)) ^ 2 * ((9 : ℝ) / (2 + |y|) ^ 2) := by
          gcongr
    _ = 9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2) := by ring

private theorem tendsto_logSq_shiftRatio_atTop :
    Tendsto (fun y : ℝ => (Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2) atTop (nhds 0) := by
  have hshift :
      Tendsto (fun y : ℝ => 2 + |y|) atTop atTop := by
    simpa using (tendsto_const_nhds.add_atTop tendsto_abs_atTop_atTop)
  have hPowDiv :
      Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x) atTop (nhds 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop (a := 1) (b := 0) (n := 2) one_ne_zero)
  have hInv :
      Tendsto (fun y : ℝ => (1 : ℝ) / (2 + |y|)) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hMul :
      Tendsto
        (fun y : ℝ =>
          (Real.log (2 + |y|) ^ (2 : ℕ) / (2 + |y|)) * ((1 : ℝ) / (2 + |y|)))
        atTop (nhds 0) :=
    by
      simpa [Function.comp] using (hPowDiv.comp hshift).mul hInv
  refine hMul.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hy : (2 + |y|) ≠ 0 := by positivity
  field_simp [pow_two, hy]

private theorem tendsto_logSq_shiftRatio_atBot :
    Tendsto (fun y : ℝ => (Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2) atBot (nhds 0) := by
  have hshift :
      Tendsto (fun y : ℝ => 2 + |y|) atBot atTop := by
    simpa using (tendsto_const_nhds.add_atTop tendsto_abs_atBot_atTop)
  have hPowDiv :
      Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x) atTop (nhds 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop (a := 1) (b := 0) (n := 2) one_ne_zero)
  have hInv :
      Tendsto (fun y : ℝ => (1 : ℝ) / (2 + |y|)) atBot (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hMul :
      Tendsto
        (fun y : ℝ =>
          (Real.log (2 + |y|) ^ (2 : ℕ) / (2 + |y|)) * ((1 : ℝ) / (2 + |y|)))
        atBot (nhds 0) :=
    by
      simpa [Function.comp] using (hPowDiv.comp hshift).mul hInv
  refine hMul.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hy : (2 + |y|) ≠ 0 := by positivity
  field_simp [pow_two, hy]

theorem tendsto_logSqEnvelope_ratio_atTop {C : ℝ} (hCnonneg : 0 ≤ C) :
    Tendsto
      (fun y : ℝ => (C * (Real.log (2 + |y|)) ^ 2) / (1 + y ^ 2))
      atTop (nhds 0) := by
  have hUpper :
      ∀ y : ℝ,
        (C * (Real.log (2 + |y|)) ^ 2) / (1 + y ^ 2) ≤
          C * (9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2)) := by
    intro y
    have hbase := logSq_ratio_le_scaled_shiftRatio y
    have hmul :
        C * ((Real.log (2 + |y|)) ^ 2 / (1 + y ^ 2))
          ≤ C * (9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hbase hCnonneg
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have hTopUpper :
      Tendsto
        (fun y : ℝ => C * (9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2)))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul tendsto_logSq_shiftRatio_atTop))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTopUpper ?_ ?_
  · exact Filter.Eventually.of_forall (fun y => by positivity)
  · exact Filter.Eventually.of_forall hUpper

theorem tendsto_logSqEnvelope_ratio_atBot {C : ℝ} (hCnonneg : 0 ≤ C) :
    Tendsto
      (fun y : ℝ => (C * (Real.log (2 + |y|)) ^ 2) / (1 + y ^ 2))
      atBot (nhds 0) := by
  have hUpper :
      ∀ y : ℝ,
        (C * (Real.log (2 + |y|)) ^ 2) / (1 + y ^ 2) ≤
          C * (9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2)) := by
    intro y
    have hbase := logSq_ratio_le_scaled_shiftRatio y
    have hmul :
        C * ((Real.log (2 + |y|)) ^ 2 / (1 + y ^ 2))
          ≤ C * (9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hbase hCnonneg
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have hBotUpper :
      Tendsto
        (fun y : ℝ => C * (9 * ((Real.log (2 + |y|)) ^ 2 / (2 + |y|) ^ 2)))
        atBot (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul tendsto_logSq_shiftRatio_atBot))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBotUpper ?_ ?_
  · exact Filter.Eventually.of_forall (fun y => by positivity)
  · exact Filter.Eventually.of_forall hUpper

private theorem logPowNine_ratio_le_scaled_shiftRatio (y : ℝ) :
    (Real.log (2 + |y|)) ^ 9 / (1 + y ^ 2) ≤
      9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2) := by
  have hlog_nonneg : 0 ≤ Real.log (2 + |y|) := by
    refine Real.log_nonneg ?_
    linarith [abs_nonneg y]
  have hnum_nonneg : 0 ≤ (Real.log (2 + |y|)) ^ 9 := by
    exact pow_nonneg hlog_nonneg 9
  have hdiv :
      (1 : ℝ) / (1 + y ^ 2) ≤ (9 : ℝ) / (2 + |y|) ^ 2 := by
    have hcmp : (2 + |y|) ^ 2 ≤ 9 * (1 + y ^ 2) := by
      calc
        (2 + |y|) ^ 2 ≤ 9 * (1 + |y| ^ 2) := by nlinarith [abs_nonneg y]
        _ = 9 * (1 + y ^ 2) := by simpa [sq]
    have hcmp' : (2 + |y|) ^ 2 / 9 ≤ 1 + y ^ 2 := by
      nlinarith [hcmp]
    have hpos : 0 < (2 + |y|) ^ 2 / 9 := by positivity
    have hinv : (1 : ℝ) / (1 + y ^ 2) ≤ 1 / ((2 + |y|) ^ 2 / 9) :=
      one_div_le_one_div_of_le hpos hcmp'
    have hrewrite : (1 : ℝ) / ((2 + |y|) ^ 2 / 9) = (9 : ℝ) / (2 + |y|) ^ 2 := by
      field_simp [pow_two]
    simpa [hrewrite] using hinv
  calc
    (Real.log (2 + |y|)) ^ 9 / (1 + y ^ 2)
        = (Real.log (2 + |y|)) ^ 9 * ((1 : ℝ) / (1 + y ^ 2)) := by ring
    _ ≤ (Real.log (2 + |y|)) ^ 9 * ((9 : ℝ) / (2 + |y|) ^ 2) := by
          gcongr
    _ = 9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2) := by ring

private theorem tendsto_logPowNine_shiftRatio_atTop :
    Tendsto (fun y : ℝ => (Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2) atTop (nhds 0) := by
  have hshift :
      Tendsto (fun y : ℝ => 2 + |y|) atTop atTop := by
    simpa using (tendsto_const_nhds.add_atTop tendsto_abs_atTop_atTop)
  have hPowDiv :
      Tendsto (fun x : ℝ => Real.log x ^ (9 : ℕ) / x) atTop (nhds 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop (a := 1) (b := 0) (n := 9) one_ne_zero)
  have hInv :
      Tendsto (fun y : ℝ => (1 : ℝ) / (2 + |y|)) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hMul :
      Tendsto
        (fun y : ℝ =>
          (Real.log (2 + |y|) ^ (9 : ℕ) / (2 + |y|)) * ((1 : ℝ) / (2 + |y|)))
        atTop (nhds 0) :=
    by
      simpa [Function.comp] using (hPowDiv.comp hshift).mul hInv
  refine hMul.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hy : (2 + |y|) ≠ 0 := by positivity
  field_simp [pow_two, hy]

private theorem tendsto_logPowNine_shiftRatio_atBot :
    Tendsto (fun y : ℝ => (Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2) atBot (nhds 0) := by
  have hshift :
      Tendsto (fun y : ℝ => 2 + |y|) atBot atTop := by
    simpa using (tendsto_const_nhds.add_atTop tendsto_abs_atBot_atTop)
  have hPowDiv :
      Tendsto (fun x : ℝ => Real.log x ^ (9 : ℕ) / x) atTop (nhds 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop (a := 1) (b := 0) (n := 9) one_ne_zero)
  have hInv :
      Tendsto (fun y : ℝ => (1 : ℝ) / (2 + |y|)) atBot (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hMul :
      Tendsto
        (fun y : ℝ =>
          (Real.log (2 + |y|) ^ (9 : ℕ) / (2 + |y|)) * ((1 : ℝ) / (2 + |y|)))
        atBot (nhds 0) :=
    by
      simpa [Function.comp] using (hPowDiv.comp hshift).mul hInv
  refine hMul.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hy : (2 + |y|) ≠ 0 := by positivity
  field_simp [pow_two, hy]

theorem tendsto_logPowNineEnvelope_ratio_atTop {C : ℝ} (hCnonneg : 0 ≤ C) :
    Tendsto
      (fun y : ℝ => (C * (Real.log (2 + |y|)) ^ 9) / (1 + y ^ 2))
      atTop (nhds 0) := by
  have hUpper :
      ∀ y : ℝ,
        (C * (Real.log (2 + |y|)) ^ 9) / (1 + y ^ 2) ≤
          C * (9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2)) := by
    intro y
    have hbase := logPowNine_ratio_le_scaled_shiftRatio y
    have hmul :
        C * ((Real.log (2 + |y|)) ^ 9 / (1 + y ^ 2))
          ≤ C * (9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hbase hCnonneg
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have hTopUpper :
      Tendsto
        (fun y : ℝ => C * (9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2)))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul tendsto_logPowNine_shiftRatio_atTop))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTopUpper ?_ ?_
  · exact Filter.Eventually.of_forall (fun y => by
      have hlog_nonneg : 0 ≤ Real.log (2 + |y|) := by
        refine Real.log_nonneg ?_
        linarith [abs_nonneg y]
      have hpow_nonneg : 0 ≤ (Real.log (2 + |y|)) ^ 9 := pow_nonneg hlog_nonneg 9
      have hnum_nonneg : 0 ≤ C * (Real.log (2 + |y|)) ^ 9 := mul_nonneg hCnonneg hpow_nonneg
      exact div_nonneg hnum_nonneg (by positivity))
  · exact Filter.Eventually.of_forall hUpper

theorem tendsto_logPowNineEnvelope_ratio_atBot {C : ℝ} (hCnonneg : 0 ≤ C) :
    Tendsto
      (fun y : ℝ => (C * (Real.log (2 + |y|)) ^ 9) / (1 + y ^ 2))
      atBot (nhds 0) := by
  have hUpper :
      ∀ y : ℝ,
        (C * (Real.log (2 + |y|)) ^ 9) / (1 + y ^ 2) ≤
          C * (9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2)) := by
    intro y
    have hbase := logPowNine_ratio_le_scaled_shiftRatio y
    have hmul :
        C * ((Real.log (2 + |y|)) ^ 9 / (1 + y ^ 2))
          ≤ C * (9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hbase hCnonneg
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have hBotUpper :
      Tendsto
        (fun y : ℝ => C * (9 * ((Real.log (2 + |y|)) ^ 9 / (2 + |y|) ^ 2)))
        atBot (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.mul tendsto_logPowNine_shiftRatio_atBot))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBotUpper ?_ ?_
  · exact Filter.Eventually.of_forall (fun y => by
      have hlog_nonneg : 0 ≤ Real.log (2 + |y|) := by
        refine Real.log_nonneg ?_
        linarith [abs_nonneg y]
      have hpow_nonneg : 0 ≤ (Real.log (2 + |y|)) ^ 9 := pow_nonneg hlog_nonneg 9
      have hnum_nonneg : 0 ≤ C * (Real.log (2 + |y|)) ^ 9 := mul_nonneg hCnonneg hpow_nonneg
      exact div_nonneg hnum_nonneg (by positivity))
  · exact Filter.Eventually.of_forall hUpper

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logPowNineEnvelope_eventually
    {ξ σ σ' C : ℝ}
    (hCnonneg : 0 ≤ C)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  refine weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_autoWeight_eventually
    (ξ := ξ) (σ := σ) (σ' := σ')
    (L := fun y : ℝ => C * (Real.log (2 + |y|)) ^ 9)
    ?_ hLogDerivTop hLogDerivBot hKernel
    (tendsto_logPowNineEnvelope_ratio_atTop hCnonneg)
    (tendsto_logPowNineEnvelope_ratio_atBot hCnonneg)
  intro y
  have hlog_nonneg : 0 ≤ Real.log (2 + |y|) := by
    refine Real.log_nonneg ?_
    linarith [abs_nonneg y]
  exact mul_nonneg hCnonneg (pow_nonneg hlog_nonneg 9)

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logPowNineEnvelope_of_absLarge
    {ξ σ σ' C Y : ℝ}
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  have hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9 := by
    have hAbsTop : ∀ᶠ y : ℝ in atTop, Y ≤ |y| :=
      tendsto_abs_atTop_atTop.eventually (eventually_ge_atTop Y)
    filter_upwards [hAbsTop] with y hy
    intro x hx
    exact hLogDerivAbs y x hy hx
  have hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9 := by
    have hAbsBot : ∀ᶠ y : ℝ in atBot, Y ≤ |y| :=
      tendsto_abs_atBot_atTop.eventually (eventually_ge_atTop Y)
    filter_upwards [hAbsBot] with y hy
    intro x hx
    exact hLogDerivAbs y x hy hx
  exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logPowNineEnvelope_eventually
    (ξ := ξ) (σ := σ) (σ' := σ') (C := C)
    hCnonneg hLogDerivTop hLogDerivBot hKernel

theorem logDerivAbs_logPowNineEnvelope_of_nearOneWindow
    {σ σ' A C Y : ℝ}
    (hCnonneg : 0 ≤ C)
    (hY3 : 3 < Y)
    (hLogDerivUnif :
      ∀ (x t : ℝ), 3 < |t| →
        x ∈ Set.Ici (1 - A / Real.log |t| ^ 9) →
          ‖zetaLogDeriv (↑x + ↑t * I)‖ ≤ C * Real.log |t| ^ 9)
    (hWindow :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        x ∈ Set.Ici (1 - A / Real.log |y| ^ 9)) :
    ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
      ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9 := by
  intro y x hy hx
  have hy3 : 3 < |y| := lt_of_lt_of_le hY3 hy
  have hbase :
      ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * Real.log |y| ^ 9 :=
    hLogDerivUnif x y hy3 (hWindow y x hy hx)
  have hy_pos : 0 < |y| := lt_trans (by norm_num) hy3
  have hlog_mono : Real.log |y| ≤ Real.log (2 + |y|) := by
    refine Real.log_le_log ?_ ?_
    · exact hy_pos
    · linarith [abs_nonneg y]
  have hlog_nonneg : 0 ≤ Real.log |y| := by
    refine Real.log_nonneg ?_
    linarith [hy3]
  have hpow :
      Real.log |y| ^ 9 ≤ Real.log (2 + |y|) ^ 9 :=
    pow_le_pow_left₀ hlog_nonneg hlog_mono 9
  have hmul :
      C * Real.log |y| ^ 9 ≤ C * Real.log (2 + |y|) ^ 9 :=
    mul_le_mul_of_nonneg_left hpow hCnonneg
  exact hbase.trans hmul

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_eventually
    {ξ σ σ' C : ℝ}
    (hCnonneg : 0 ≤ C)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  refine weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_autoWeight_eventually
    (ξ := ξ) (σ := σ) (σ' := σ')
    (L := fun y : ℝ => C * (Real.log (2 + |y|)) ^ 2)
    ?_ hLogDerivTop hLogDerivBot hKernel
    (tendsto_logSqEnvelope_ratio_atTop hCnonneg)
    (tendsto_logSqEnvelope_ratio_atBot hCnonneg)
  intro y
  positivity

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge
    {ξ σ σ' C Y : ℝ}
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  have hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2 := by
    have hAbsTop : ∀ᶠ y : ℝ in atTop, Y ≤ |y| :=
      tendsto_abs_atTop_atTop.eventually (eventually_ge_atTop Y)
    filter_upwards [hAbsTop] with y hy
    intro x hx
    exact hLogDerivAbs y x hy hx
  have hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2 := by
    have hAbsBot : ∀ᶠ y : ℝ in atBot, Y ≤ |y| :=
      tendsto_abs_atBot_atTop.eventually (eventually_ge_atTop Y)
    filter_upwards [hAbsBot] with y hy
    intro x hx
    exact hLogDerivAbs y x hy hx
  exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_eventually
    (ξ := ξ) (σ := σ) (σ' := σ') (C := C)
    hCnonneg hLogDerivTop hLogDerivBot hKernel

/-- Packaged absolute-tail log-squared envelope data for `‖ζ'/ζ‖` on a strip. -/
structure InvSqLogSqEnvelopeAbsLargeData (σ σ' : ℝ) where
  C : ℝ
  Y : ℝ
  hCnonneg : 0 ≤ C
  hLogDerivAbs :
    ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
      ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge_data
    {ξ σ σ' : ℝ}
    (hEnv : InvSqLogSqEnvelopeAbsLargeData σ σ')
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge
    (ξ := ξ) (σ := σ) (σ' := σ') (C := hEnv.C) (Y := hEnv.Y)
    hEnv.hCnonneg hEnv.hLogDerivAbs hKernel

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge_data_autoKernel
    {ξ σ σ' : ℝ}
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hEnv : InvSqLogSqEnvelopeAbsLargeData σ σ') :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge_data
    (ξ := ξ) (σ := σ) (σ' := σ') hEnv
    (fun y x hx => invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx)

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_pointwise_autoWeight
    {ξ σ σ' K : ℝ}
    (hK : 0 ≤ K)
    (hLogDeriv :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ K)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  refine weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_pointwise
    (ξ := ξ) (σ := σ) (σ' := σ') (K := K)
    (W := Real.exp (|ξ| * max |σ| |σ'|))
    (by positivity) hK ?_ hLogDeriv hKernel
  intro x hx
  exact modeWeight_norm_bound_on_uIoc (ξ := ξ) (σ := σ) (σ' := σ') hx

theorem weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_vertical_logDeriv_bound
    {ξ σ σ' : ℝ}
    (hσσ' : σ ≤ σ')
    (hσ : 1 < σ) :
    WeightedHorizontalDecay invSqKernel ξ σ σ' := by
  have hσ0 : 0 ≤ σ := by linarith
  refine weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_pointwise_autoWeight
    (ξ := ξ) (σ := σ) (σ' := σ') (K := ‖zetaLogDeriv σ‖) (by positivity) ?_ ?_
  · intro y x hx
    have hxIoc : x ∈ Set.Ioc σ σ' := by
      simpa [Set.uIoc_of_le hσσ'] using hx
    exact zetaLogDeriv_bound_on_vertical_ge_one hσ (le_of_lt hxIoc.1)
  · intro y x hx
    exact invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx

theorem modeTwist_zero :
    modeTwist 0 = (fun _ : ℂ => (1 : ℂ)) := by
  funext s
  simp [modeTwist]

theorem onLineModeContourIntegrand_zero (g : ℂ → ℂ) :
    onLineModeContourIntegrand g 0 = spectralIntegrand g := by
  funext s
  simp [onLineModeContourIntegrand, modeTwist]

theorem onLineModeContourFamily_eq_spectralIntegrand_of_modeZero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {n : ℕ} (hγ : γ n = 0) :
    onLineModeContourFamily g γ n = spectralIntegrand g := by
  ext s
  simp [onLineModeContourFamily, onLineModeContourIntegrand, modeTwist, hγ]

theorem step5Context_onLineModeContourFamily_of_modeZero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ σ' T : ℝ} {n : ℕ}
    (hγ : γ n = 0)
    (hctx : Step5Context (spectralIntegrand g) σ σ' T) :
    Step5Context (onLineModeContourFamily g γ n) σ σ' T := by
  simpa [onLineModeContourFamily_eq_spectralIntegrand_of_modeZero
    (g := g) (γ := γ) (n := n) hγ] using hctx

theorem onLineModeMoment_unitIntervalWitness_eq_setIntegral
    {γ : ℕ → ℝ} {w : ℂ} (n : ℕ) :
    onLineModeMoment γ (unitIntervalWitness w) n =
      ∫ t : ℝ in Set.Icc (0 : ℝ) 1, w * onLineMode (γ n) t := by
  have hcoe :
      (fun t : ℝ =>
        ((unitIntervalWitness w : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
        =ᵐ[volume]
      (fun t : ℝ => (Set.Icc (0 : ℝ) 1).indicator (fun _ : ℝ => w) t) := by
    simpa [unitIntervalWitness] using
      (indicatorConstLp_coeFn (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))
        (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
        (hμs := (measure_Icc_lt_top (a := (0 : ℝ)) (b := 1)
          (μ := (volume : Measure ℝ))).ne)
        (c := w))
  have hcoeeq :
      (fun t : ℝ => ((unitIntervalWitness w : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t *
        onLineMode (γ n) t)
        =ᵐ[volume]
      (fun t : ℝ =>
        (Set.Icc (0 : ℝ) 1).indicator (fun _ : ℝ => w) t * onLineMode (γ n) t) := by
    filter_upwards [hcoe] with t ht
    simp [ht]
  have hind :
      (fun t : ℝ =>
        (Set.Icc (0 : ℝ) 1).indicator (fun _ : ℝ => w) t * onLineMode (γ n) t)
        =
      (fun t : ℝ =>
        (Set.Icc (0 : ℝ) 1).indicator (fun t : ℝ => w * onLineMode (γ n) t) t) := by
    funext t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1 <;> simp [ht]
  calc
    onLineModeMoment γ (unitIntervalWitness w) n
        = ∫ t : ℝ,
            ((unitIntervalWitness w : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t *
              onLineMode (γ n) t ∂volume := rfl
    _ = ∫ t : ℝ,
          (Set.Icc (0 : ℝ) 1).indicator (fun _ : ℝ => w) t * onLineMode (γ n) t ∂volume := by
          exact integral_congr_ae hcoeeq
    _ = ∫ t : ℝ,
          (Set.Icc (0 : ℝ) 1).indicator (fun t : ℝ => w * onLineMode (γ n) t) t ∂volume := by
          rw [hind]
    _ = ∫ t : ℝ in Set.Icc (0 : ℝ) 1, w * onLineMode (γ n) t ∂volume := by
          simpa using integral_indicator (μ := (volume : Measure ℝ))
            (s := Set.Icc (0 : ℝ) 1) (f := fun t : ℝ => w * onLineMode (γ n) t) measurableSet_Icc

theorem onLineModeMoment_unitIntervalWitness_eq_mul_setIntegral
    {γ : ℕ → ℝ} {w : ℂ} (n : ℕ) :
    onLineModeMoment γ (unitIntervalWitness w) n =
      w * ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t := by
  rw [onLineModeMoment_unitIntervalWitness_eq_setIntegral (γ := γ) (w := w) n]
  exact integral_const_mul (r := w) (f := fun t : ℝ => onLineMode (γ n) t)
    (μ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

theorem modeVerticalDiff_eq_of_unitInterval_modeIdentity
    {γ : ℕ → ℝ} {w : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ}
    (hModeIdentity :
      ∀ n : ℕ,
        w * ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n) :
    ∀ n : ℕ,
      onLineModeMoment γ (unitIntervalWitness w) n =
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
  intro n
  calc
    onLineModeMoment γ (unitIntervalWitness w) n
        = w * ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t :=
          onLineModeMoment_unitIntervalWitness_eq_mul_setIntegral (γ := γ) (w := w) n
    _ = modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := hModeIdentity n

theorem modeVerticalDiff_eq_of_unitInterval_modeIdentity_inv
    {γ : ℕ → ℝ} {w : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ}
    (hw : w ≠ 0)
    (hModeIdentity :
      ∀ n : ℕ,
        ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          w⁻¹ * modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n) :
    ∀ n : ℕ,
      onLineModeMoment γ (unitIntervalWitness w) n =
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
  intro n
  calc
    onLineModeMoment γ (unitIntervalWitness w) n
        = w * ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t :=
          onLineModeMoment_unitIntervalWitness_eq_mul_setIntegral (γ := γ) (w := w) n
    _ = w * (w⁻¹ * modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n) := by
          simp [hModeIdentity n]
    _ = modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
          simp [hw]

theorem setIntegral_onLineMode_Icc_eq_intervalIntegral (ξ : ℝ) :
    ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode ξ t =
      ∫ t : ℝ in (0 : ℝ)..1, onLineMode ξ t := by
  rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
    (f := fun t : ℝ => onLineMode ξ t) (a := (0 : ℝ)) (b := 1) (by norm_num)]
  exact integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ))
    (f := fun t : ℝ => onLineMode ξ t) (x := (0 : ℝ)) (y := 1)

theorem intervalIntegral_onLineMode_eq_div_of_ne_zero (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∫ t : ℝ in (0 : ℝ)..1, onLineMode ξ t =
      (Complex.exp (-((ξ : ℂ) * I)) - 1) / (-((ξ : ℂ) * I)) := by
  have hc : (-((ξ : ℂ) * I)) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact mul_ne_zero (by exact_mod_cast hξ) Complex.I_ne_zero
  have harg :
      (fun t : ℝ => onLineMode ξ t) =
        (fun t : ℝ => Complex.exp ((-((ξ : ℂ) * I)) * t)) := by
    funext t
    simp [onLineMode, mul_left_comm, mul_comm]
  calc
    ∫ t : ℝ in (0 : ℝ)..1, onLineMode ξ t
        = ∫ t : ℝ in (0 : ℝ)..1, Complex.exp ((-((ξ : ℂ) * I)) * t) := by
            simp [harg]
    _ = (Complex.exp (((-((ξ : ℂ) * I)) * (1 : ℝ))) -
          Complex.exp (((-((ξ : ℂ) * I)) * (0 : ℝ)))) / (-((ξ : ℂ) * I)) := by
          simpa using
            (integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) (c := -((ξ : ℂ) * I)) hc)
    _ = (Complex.exp (-((ξ : ℂ) * I)) - 1) / (-((ξ : ℂ) * I)) := by
          simp

theorem setIntegral_onLineMode_Icc_eq_div_of_ne_zero (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode ξ t =
      (Complex.exp (-((ξ : ℂ) * I)) - 1) / (-((ξ : ℂ) * I)) := by
  rw [setIntegral_onLineMode_Icc_eq_intervalIntegral (ξ := ξ)]
  exact intervalIntegral_onLineMode_eq_div_of_ne_zero ξ hξ

theorem setIntegral_onLineMode_Icc_zero :
    ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode 0 t = 1 := by
  simp [onLineMode]

/-- Closed form for `∫_{0}^{1} onLineMode ξ` with explicit zero-frequency branch. -/
noncomputable def unitIntervalModeFactor (ξ : ℝ) : ℂ :=
  if _hξ : ξ = 0 then 1
  else (Complex.exp (-((ξ : ℂ) * I)) - 1) / (-((ξ : ℂ) * I))

theorem setIntegral_onLineMode_Icc_eq_unitIntervalModeFactor (ξ : ℝ) :
    ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode ξ t = unitIntervalModeFactor ξ := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [unitIntervalModeFactor, setIntegral_onLineMode_Icc_zero]
  · simp [unitIntervalModeFactor, hξ, setIntegral_onLineMode_Icc_eq_div_of_ne_zero]

theorem onLineModeMoment_unitIntervalWitness_eq_of_modeZero
    {γ : ℕ → ℝ} {w : ℂ} {n : ℕ} (hγ : γ n = 0) :
    onLineModeMoment γ (unitIntervalWitness w) n = w := by
  rw [onLineModeMoment_unitIntervalWitness_eq_mul_setIntegral (γ := γ) (w := w) n, hγ]
  simp [setIntegral_onLineMode_Icc_zero]

theorem onLineModeMoment_unitIntervalWitness_eq_mul_exp_div_of_modeNeZero
    {γ : ℕ → ℝ} {w : ℂ} {n : ℕ} (hγ : γ n ≠ 0) :
    onLineModeMoment γ (unitIntervalWitness w) n =
      w * ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))) := by
  rw [onLineModeMoment_unitIntervalWitness_eq_mul_setIntegral (γ := γ) (w := w) n]
  congr 1
  exact setIntegral_onLineMode_Icc_eq_div_of_ne_zero (ξ := γ n) hγ

theorem onLineModeMoment_unitIntervalWitness_eq_mul_unitIntervalModeFactor
    {γ : ℕ → ℝ} {w : ℂ} (n : ℕ) :
    onLineModeMoment γ (unitIntervalWitness w) n =
      w * unitIntervalModeFactor (γ n) := by
  rw [onLineModeMoment_unitIntervalWitness_eq_mul_setIntegral (γ := γ) (w := w) n]
  congr 1
  exact setIntegral_onLineMode_Icc_eq_unitIntervalModeFactor (ξ := γ n)

theorem modeVerticalDiff_eq_of_contourExpFormula
    {γ : ℕ → ℝ} {w : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ}
    (hγ : ∀ n : ℕ, γ n ≠ 0)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          w * ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I)))) :
    ∀ n : ℕ,
      onLineModeMoment γ (unitIntervalWitness w) n =
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
  intro n
  calc
    onLineModeMoment γ (unitIntervalWitness w) n
        = w * ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))) :=
          onLineModeMoment_unitIntervalWitness_eq_mul_exp_div_of_modeNeZero
            (γ := γ) (w := w) (n := n) (hγ n)
    _ = modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
          symm
          exact hContourFormula n

theorem modeVerticalDiff_eq_of_contourUnitIntervalFormula
    {γ : ℕ → ℝ} {w : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ}
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          w * unitIntervalModeFactor (γ n)) :
    ∀ n : ℕ,
      onLineModeMoment γ (unitIntervalWitness w) n =
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
  intro n
  calc
    onLineModeMoment γ (unitIntervalWitness w) n
        = w * unitIntervalModeFactor (γ n) :=
          onLineModeMoment_unitIntervalWitness_eq_mul_unitIntervalModeFactor
            (γ := γ) (w := w) n
    _ = modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
          symm
          exact hContourFormula n

theorem modeTwist_eval_re_add_im_mul_I (ξ σ y : ℝ) :
    modeTwist ξ (↑σ + ↑y * I) =
      Complex.exp (-((ξ : ℂ) * (σ : ℂ))) * onLineMode ξ y := by
  unfold modeTwist onLineMode
  have hexp :
      -((ξ : ℂ) * (↑σ + ↑y * I))
        = -((ξ : ℂ) * (σ : ℂ)) + (-((ξ : ℂ) * (y : ℂ) * I)) := by
    ring
  rw [hexp, Complex.exp_add]
  ring_nf

theorem onLineModeContourFamily_eval_re_add_im_mul_I
    (g : ℂ → ℂ) (γ : ℕ → ℝ) (n : ℕ) (σ y : ℝ) :
    onLineModeContourFamily g γ n (↑σ + ↑y * I) =
      Complex.exp (-(((γ n) : ℂ) * (σ : ℂ))) *
        (spectralIntegrand g (↑σ + ↑y * I) * onLineMode (γ n) y) := by
  calc
    onLineModeContourFamily g γ n (↑σ + ↑y * I)
        = spectralIntegrand g (↑σ + ↑y * I) * modeTwist (γ n) (↑σ + ↑y * I) := by
            rfl
    _ = spectralIntegrand g (↑σ + ↑y * I) *
          (Complex.exp (-(((γ n) : ℂ) * (σ : ℂ))) * onLineMode (γ n) y) := by
          rw [modeTwist_eval_re_add_im_mul_I (ξ := γ n) (σ := σ) (y := y)]
    _ = Complex.exp (-(((γ n) : ℂ) * (σ : ℂ))) *
          (spectralIntegrand g (↑σ + ↑y * I) * onLineMode (γ n) y) := by
          ring_nf

theorem norm_onLineMode_eq_one (ξ t : ℝ) :
    ‖onLineMode ξ t‖ = 1 := by
  simp [onLineMode, Complex.norm_exp]

theorem integrable_mul_onLineMode_of_integrable
    (ξ : ℝ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun y : ℝ => f y * onLineMode ξ y) := by
  have hcontArg : Continuous (fun y : ℝ => -((ξ : ℂ) * (y : ℂ) * I)) := by
    exact ((continuous_const.mul continuous_ofReal).mul continuous_const).neg
  have hcont : Continuous (fun y : ℝ => onLineMode ξ y) := by
    simpa [onLineMode] using (Complex.continuous_exp.comp hcontArg)
  refine Integrable.mul_bdd (c := (1 : ℝ)) hf hcont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun y => by
    simpa [norm_onLineMode_eq_one (ξ := ξ) (t := y)])

theorem integrable_left_onLineModeContourFamily_of_integrable_left
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ : ℝ} (n : ℕ)
    (hleft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I)) :
    Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)) := by
  have hmul :
      Integrable (fun y : ℝ =>
        spectralIntegrand g (↑σ + ↑y * I) * onLineMode (γ n) y) :=
    integrable_mul_onLineMode_of_integrable (ξ := γ n) hleft
  have hconst :
      Integrable (fun y : ℝ =>
        Complex.exp (-(((γ n) : ℂ) * (σ : ℂ))) *
          (spectralIntegrand g (↑σ + ↑y * I) * onLineMode (γ n) y)) :=
    Integrable.const_mul hmul (Complex.exp (-(((γ n) : ℂ) * (σ : ℂ))))
  simpa [onLineModeContourFamily_eval_re_add_im_mul_I]
    using hconst

theorem integrable_right_onLineModeContourFamily_of_integrable_right
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ' : ℝ} (n : ℕ)
    (hright : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)) :
    Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I)) := by
  have hmul :
      Integrable (fun y : ℝ =>
        spectralIntegrand g (↑σ' + ↑y * I) * onLineMode (γ n) y) :=
    integrable_mul_onLineMode_of_integrable (ξ := γ n) hright
  have hconst :
      Integrable (fun y : ℝ =>
        Complex.exp (-(((γ n) : ℂ) * (σ' : ℂ))) *
          (spectralIntegrand g (↑σ' + ↑y * I) * onLineMode (γ n) y)) :=
    Integrable.const_mul hmul (Complex.exp (-(((γ n) : ℂ) * (σ' : ℂ))))
  simpa [onLineModeContourFamily_eval_re_add_im_mul_I]
    using hconst

theorem horizontalIntegral_onLineModeContourFamily_eq_onLineMode_mul_weighted
    (g : ℂ → ℂ) (γ : ℕ → ℝ) (n : ℕ) (σ σ' y : ℝ) :
    (∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) =
      onLineMode (γ n) y *
        (∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) := by
  have hpoint :
      ∀ x : ℝ,
        onLineModeContourFamily g γ n (↑x + ↑y * I)
          = onLineMode (γ n) y *
              (Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
                spectralIntegrand g (↑x + ↑y * I)) := by
    intro x
    calc
      onLineModeContourFamily g γ n (↑x + ↑y * I)
          = Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
              (spectralIntegrand g (↑x + ↑y * I) * onLineMode (γ n) y) :=
            onLineModeContourFamily_eval_re_add_im_mul_I g γ n x y
      _ = onLineMode (γ n) y *
            (Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
              spectralIntegrand g (↑x + ↑y * I)) := by
            ring_nf
  have hEqFun :
      (fun x : ℝ => onLineModeContourFamily g γ n (↑x + ↑y * I))
        =
      (fun x : ℝ =>
        onLineMode (γ n) y *
          (Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I))) := by
    funext x
    exact hpoint x
  rw [hEqFun]
  simpa using intervalIntegral.integral_const_mul
      (a := σ) (b := σ') (r := onLineMode (γ n) y)
      (f := fun x : ℝ =>
        Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) * spectralIntegrand g (↑x + ↑y * I))

theorem tendsto_mul_onLineMode_of_tendsto_zero
    (ξ : ℝ) {l : Filter ℝ} {F : ℝ → ℂ}
    (hF : Tendsto F l (nhds 0)) :
    Tendsto (fun y : ℝ => onLineMode ξ y * F y) l (nhds 0) := by
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
  have hnormF : Tendsto (fun y : ℝ => ‖F y‖) l (nhds 0) := by
    simpa using hF.norm
  have hnormMode : Tendsto (fun y : ℝ => ‖onLineMode ξ y‖) l (nhds (1 : ℝ)) := by
    simpa [norm_onLineMode_eq_one (ξ := ξ)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds (1 : ℝ)))
  have hmul :
      Tendsto (fun y : ℝ => ‖onLineMode ξ y‖ * ‖F y‖) l (nhds ((1 : ℝ) * 0)) :=
    hnormMode.mul hnormF
  simpa [norm_mul] using hmul

theorem top_onLineModeContourFamily_of_weightedTop
    (g : ℂ → ℂ) (γ : ℕ → ℝ) (n : ℕ) (σ σ' : ℝ)
    (hTopW :
      Tendsto
        (fun y : ℝ =>
          ∫ x : ℝ in σ..σ',
            Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
              spectralIntegrand g (↑x + ↑y * I))
        atTop (nhds 0)) :
    Tendsto (fun y : ℝ =>
      ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I))
      atTop (nhds 0) := by
  have hEq :
      (fun y : ℝ => ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I))
        =
      (fun y : ℝ =>
        onLineMode (γ n) y *
          (∫ x : ℝ in σ..σ',
            Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
              spectralIntegrand g (↑x + ↑y * I))) := by
    funext y
    exact horizontalIntegral_onLineModeContourFamily_eq_onLineMode_mul_weighted
      g γ n σ σ' y
  rw [hEq]
  exact tendsto_mul_onLineMode_of_tendsto_zero (ξ := γ n) hTopW

theorem bot_onLineModeContourFamily_of_weightedBot
    (g : ℂ → ℂ) (γ : ℕ → ℝ) (n : ℕ) (σ σ' : ℝ)
    (hBotW :
      Tendsto
        (fun y : ℝ =>
          ∫ x : ℝ in σ..σ',
            Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
              spectralIntegrand g (↑x + ↑y * I))
        atBot (nhds 0)) :
    Tendsto (fun y : ℝ =>
      ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I))
      atBot (nhds 0) := by
  have hEq :
      (fun y : ℝ => ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I))
        =
      (fun y : ℝ =>
        onLineMode (γ n) y *
          (∫ x : ℝ in σ..σ',
            Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
              spectralIntegrand g (↑x + ↑y * I))) := by
    funext y
    exact horizontalIntegral_onLineModeContourFamily_eq_onLineMode_mul_weighted
      g γ n σ σ' y
  rw [hEq]
  exact tendsto_mul_onLineMode_of_tendsto_zero (ξ := γ n) hBotW

theorem modeTwist_holomorphicOn (ξ : ℝ) (U : Set ℂ) :
    HolomorphicOn (modeTwist ξ) U := by
  have hlin : Differentiable ℂ (fun s : ℂ => -((ξ : ℂ) * s)) := by
    simpa using (differentiable_id.const_mul (ξ : ℂ)).neg
  simpa [modeTwist] using (hlin.cexp).differentiableOn

theorem onLineModeContourIntegrand_holomorphicOn
    {g : ℂ → ℂ} {ξ : ℝ} {U : Set ℂ}
    (hSpec : HolomorphicOn (spectralIntegrand g) U) :
    HolomorphicOn (onLineModeContourIntegrand g ξ) U := by
  simpa [onLineModeContourIntegrand] using hSpec.mul (modeTwist_holomorphicOn ξ U)

theorem onLineModeContourFamily_holomorphicOn
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {U : Set ℂ}
    (hSpec : HolomorphicOn (spectralIntegrand g) U) :
    ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) U := by
  intro n
  exact onLineModeContourIntegrand_holomorphicOn (g := g) (ξ := γ n) hSpec

theorem onLineModeContourFamily_holoOn_of_nonzero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {S : Set ℂ}
    (hOne : (1 : ℂ) ∉ S)
    (hNonzero : ∀ s ∈ S, riemannZeta s ≠ 0)
    (hg : HolomorphicOn g S) :
    ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) S :=
  onLineModeContourFamily_holomorphicOn
    (g := g) (γ := γ) (U := S)
    (spectralIntegrand_holoOn_of_nonzero hOne hNonzero hg)

theorem onLineModeContourFamily_holoOn_stripMinusPole_of_nonzero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ σ' : ℝ} {p : ℂ}
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p)) :
    ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) (stripMinusPole σ σ' p) := by
  exact onLineModeContourFamily_holoOn_of_nonzero
    (g := g) (γ := γ) (S := stripMinusPole σ σ' p)
    hOneStrip hNonzeroStrip hgStrip

theorem onLineModeContourFamily_holoOn_upperStrip_of_nonzero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ σ' T : ℝ}
    (hOneUpper : (1 : ℂ) ∉ upperStrip σ σ' T)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T)) :
    ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) (upperStrip σ σ' T) :=
  onLineModeContourFamily_holoOn_of_nonzero
    (g := g) (γ := γ) (S := upperStrip σ σ' T)
    hOneUpper hNonzeroUpper hgUpper

theorem onLineModeContourFamily_holoOn_lowerStrip_of_nonzero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ σ' T : ℝ}
    (hOneLower : (1 : ℂ) ∉ lowerStrip σ σ' T)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T)) :
    ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) (lowerStrip σ σ' T) :=
  onLineModeContourFamily_holoOn_of_nonzero
    (g := g) (γ := γ) (S := lowerStrip σ σ' T)
    hOneLower hNonzeroLower hgLower

theorem rectangle_zero_onLineModeContourFamily_of_holomorphicOn
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ σ' T : ℝ} {U : Set ℂ}
    (hhol : ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) U)
    (hsub : (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ U) :
    ∀ n : ℕ,
      RectangleIntegral (onLineModeContourFamily g γ n)
        (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 := by
  intro n
  exact (hhol n).vanishesOnRectangle hsub

theorem rectangle_zero_onLineModeContourFamily_of_nonzero
    {g : ℂ → ℂ} {γ : ℕ → ℝ} {σ σ' T : ℝ} {S : Set ℂ}
    (hOne : (1 : ℂ) ∉ S)
    (hNonzero : ∀ s ∈ S, riemannZeta s ≠ 0)
    (hg : HolomorphicOn g S)
    (hsub : (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ S) :
    ∀ n : ℕ,
      RectangleIntegral (onLineModeContourFamily g γ n)
        (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 :=
  rectangle_zero_onLineModeContourFamily_of_holomorphicOn
    (g := g) (γ := γ) (σ := σ) (σ' := σ') (T := T) (U := S)
    (onLineModeContourFamily_holoOn_of_nonzero
      (g := g) (γ := γ) (S := S) hOne hNonzero hg)
    hsub

theorem rectangle_subset_stripMinusPole_of_not_mem
    {σ σ' T : ℝ} {p : ℂ}
    (hσσ' : σ ≤ σ')
    (hp :
      p ∉ (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T)) :
    (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ stripMinusPole σ σ' p := by
  intro z hz
  refine ⟨?_, ?_⟩
  · refine ⟨?_, trivial⟩
    have hzre : z.re ∈ Set.uIcc σ σ' := by
      simpa using hz.1
    simpa [Set.uIcc_of_le hσσ'] using hzre
  · intro hzp
    exact hp (hzp ▸ hz)

theorem not_mem_verticalRectangle_of_im_outside
    {σ σ' T : ℝ} {p : ℂ}
    (hT : 0 ≤ T)
    (hpim : p.im < -T ∨ T < p.im) :
    p ∉ (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) := by
  intro hp
  have hnegTleT : -T ≤ T := by linarith
  have him : p.im ∈ Set.Icc (-T) T := by
    simpa [Rectangle, hnegTleT] using hp.2
  rcases hpim with hpim | hpim
  · exact (not_le.mpr hpim) him.1
  · exact (not_le.mpr hpim) him.2

theorem rectangle_subset_stripMinusPole_of_im_outside
    {σ σ' T : ℝ} {p : ℂ}
    (hσσ' : σ ≤ σ')
    (hT : 0 ≤ T)
    (hpim : p.im < -T ∨ T < p.im) :
    (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ stripMinusPole σ σ' p :=
  rectangle_subset_stripMinusPole_of_not_mem hσσ'
    (not_mem_verticalRectangle_of_im_outside (σ := σ) (σ' := σ') (T := T) (p := p) hT hpim)

theorem step5Context_family_of_data
    {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hσσ' : σ ≤ σ')
    (hUpperHol : ∀ n : ℕ, HolomorphicOn (F n) (upperStrip σ σ' T))
    (hLowerHol : ∀ n : ℕ, HolomorphicOn (F n) (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ => ∫ x : ℝ in σ..σ', F n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ => ∫ x : ℝ in σ..σ', F n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeft : ∀ n : ℕ, Integrable (fun y : ℝ => F n (↑σ + ↑y * I)))
    (hRight : ∀ n : ℕ, Integrable (fun y : ℝ => F n (↑σ' + ↑y * I))) :
    ∀ n : ℕ, Step5Context (F n) σ σ' T := by
  intro n
  refine ⟨hσσ', ?_, ?_, hTop n, hBot n, hLeft n, hRight n⟩
  · simpa [upperStrip] using hUpperHol n
  · simpa [lowerStrip] using hLowerHol n

theorem contour_verticalDiff_zero_of_step5_and_rectangle_zero
    {F : ℂ → ℂ} {σ σ' T : ℝ}
    (hctx : Step5Context F σ σ' T)
    (hrect0 : RectangleIntegral F (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    VerticalIntegral F σ' - VerticalIntegral F σ = 0 := by
  have hshift :
      VerticalIntegral F σ' - VerticalIntegral F σ -
        RectangleIntegral F (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 :=
    contour_shift_zero_tails hctx
  have hEqRect :
      VerticalIntegral F σ' - VerticalIntegral F σ =
        RectangleIntegral F (↑σ - I * ↑T) (↑σ' + I * ↑T) :=
    sub_eq_zero.mp hshift
  simpa [hrect0] using hEqRect

theorem contour_family_zero_of_step5_and_rectangle_zero
    {C : ℕ → ℂ} {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hCdef : ∀ n : ℕ, C n = VerticalIntegral (F n) σ' - VerticalIntegral (F n) σ)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    ∀ n : ℕ, C n = 0 := by
  intro n
  rw [hCdef n]
  exact contour_verticalDiff_zero_of_step5_and_rectangle_zero (hctx n) (hrect0 n)

theorem modeVerticalDiff_zero_of_step5_and_rectangle_zero
    {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    ∀ n : ℕ, modeVerticalDiff F σ σ' n = 0 := by
  intro n
  exact contour_verticalDiff_zero_of_step5_and_rectangle_zero (hctx n) (hrect0 n)

theorem rectangle_family_zero_of_holomorphicOn
    {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ} {U : Set ℂ}
    (hhol : ∀ n : ℕ, HolomorphicOn (F n) U)
    (hsub : (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ U) :
    ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0 := by
  intro n
  exact (hhol n).vanishesOnRectangle hsub

theorem contour_family_zero_of_constant_step5_and_rectangle_zero
    {C : ℕ → ℂ} {F : ℂ → ℂ} {σ σ' T : ℝ}
    (hCdef : ∀ n : ℕ, C n = VerticalIntegral F σ' - VerticalIntegral F σ)
    (hctx : Step5Context F σ σ' T)
    (hrect0 : RectangleIntegral F (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    ∀ n : ℕ, C n = 0 := by
  refine contour_family_zero_of_step5_and_rectangle_zero
    (C := C) (F := fun _ : ℕ => F) (σ := σ) (σ' := σ') (T := T) hCdef ?_ ?_
  · intro n
    simpa using hctx
  · intro n
    simpa using hrect0

def rotatedStripModeMomentData_of_step5_family
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    {M C : ℕ → ℂ} {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hMomentEq : ∀ n : ℕ, onLineModeMoment γ f n = M n)
    (hContourEq : ∀ n : ℕ, M n = C n)
    (hCdef : ∀ n : ℕ, C n = VerticalIntegral (F n) σ' - VerticalIntegral (F n) σ)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    RotatedStripModeMomentData γ f :=
  rotatedStripModeMomentData_of_equations
    (γ := γ) (f := f) (M := M) (C := C)
    hMomentEq hContourEq
    (contour_family_zero_of_step5_and_rectangle_zero hCdef hctx hrect0)

noncomputable def rotatedStripModeMomentData_of_step5_modeVerticalDiff
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    {M : ℕ → ℂ} {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hMomentEq : ∀ n : ℕ, onLineModeMoment γ f n = M n)
    (hContourEq : ∀ n : ℕ, M n = modeVerticalDiff F σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    RotatedStripModeMomentData γ f :=
  rotatedStripModeMomentData_of_equations
    (γ := γ) (f := f) (M := M) (C := modeVerticalDiff F σ σ')
    hMomentEq hContourEq
    (modeVerticalDiff_zero_of_step5_and_rectangle_zero hctx hrect0)

theorem contourModeMomentModel_of_momentVertical_and_step5_family
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hMomentVertical : ∀ n : ℕ, onLineModeMoment γ f n = modeVerticalDiff F σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    ContourModeMomentModel γ f :=
  contourModeMomentModel_of_modeEquations
    (γ := γ) (f := f) (M := modeVerticalDiff F σ σ')
    hMomentVertical (modeVerticalDiff_zero_of_step5_and_rectangle_zero hctx hrect0)

theorem orthogonalToOnLineModes_of_momentVertical_and_step5_family
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hMomentVertical : ∀ n : ℕ, onLineModeMoment γ f n = modeVerticalDiff F σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    OrthogonalToOnLineModes γ f :=
  orthogonalToOnLineModes_of_contourModeMomentModel
    (contourModeMomentModel_of_momentVertical_and_step5_family
      (γ := γ) (f := f) (F := F) (σ := σ) (σ' := σ') (T := T)
      hMomentVertical hctx hrect0)

theorem mellinGoal_of_nonzeroLp_and_momentVertical_and_step5_family
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    {F : ℕ → ℂ → ℂ} {σ σ' T : ℝ}
    (hne : f ≠ 0)
    (hMomentVertical : ∀ n : ℕ, onLineModeMoment γ f n = modeVerticalDiff F σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_nonzeroLp_and_contourModel hne
    (contourModeMomentModel_of_momentVertical_and_step5_family
      (γ := γ) (f := f) (F := F) (σ := σ) (σ' := σ') (T := T)
      hMomentVertical hctx hrect0)

theorem contourModeMomentModel_of_rotatedStripModeMomentData
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hmode : RotatedStripModeMomentData γ f) :
    ContourModeMomentModel γ f :=
  contourModeMomentModel_of_momentEq_and_contourEq
    (γ := γ) (f := f) (M := hmode.M) (C := hmode.C)
    hmode.hMomentEq hmode.hContourEq hmode.hContourZero

theorem orthogonalToOnLineModes_of_rotatedStripModeMomentData
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hmode : RotatedStripModeMomentData γ f) :
    OrthogonalToOnLineModes γ f :=
  orthogonalToOnLineModes_of_contourModeMomentModel
    (contourModeMomentModel_of_rotatedStripModeMomentData hmode)

def offLineStep6ContourMomentPackage_of_rotatedStripModeMomentData
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hmode :
      RotatedStripModeMomentData γ
        (unitIntervalWitness (spectralAmplitude g σ σ'))) :
    OffLineStep6ContourMomentPackage γ ρ :=
  offLineStep6ContourMomentPackage_of_modeEquations
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (A := A) (M := hmode.C)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    (fun n => (hmode.hMomentEq n).trans (hmode.hContourEq n))
    hmode.hContourZero

theorem mellinGoal_of_invZetaSimplePole_with_rotatedStripModeMomentData
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hmode :
      RotatedStripModeMomentData γ
        (unitIntervalWitness (spectralAmplitude g σ σ'))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_offLineStep6ContourMomentPackage
    (offLineStep6ContourMomentPackage_of_rotatedStripModeMomentData
      (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (A := A)
      hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel hmode)

theorem mellinGoal_of_invZetaSimplePole_with_rotatedStripModeEquations
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ} {A : ℂ}
    {M C : ℕ → ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentEq :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n = M n)
    (hContourEq : ∀ n : ℕ, M n = C n)
    (hContourZero : ∀ n : ℕ, C n = 0) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_rotatedStripModeMomentData
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    (rotatedStripModeMomentData_of_equations
      (γ := γ)
      (f := unitIntervalWitness (spectralAmplitude g σ σ'))
      (M := M) (C := C)
      hMomentEq hContourEq hContourZero)

theorem mellinGoal_of_invZetaSimplePole_with_step5_mode_family
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    {M C : ℕ → ℂ} {F : ℕ → ℂ → ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentEq :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n = M n)
    (hContourEq : ∀ n : ℕ, M n = C n)
    (hCdef : ∀ n : ℕ, C n = VerticalIntegral (F n) σ' - VerticalIntegral (F n) σ)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_rotatedStripModeMomentData
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    (rotatedStripModeMomentData_of_step5_family
      (γ := γ)
      (f := unitIntervalWitness (spectralAmplitude g σ σ'))
      (M := M) (C := C) (F := F) (σ := σ) (σ' := σ') (T := T)
      hMomentEq hContourEq hCdef hctx hrect0)

theorem mellinGoal_of_invZetaSimplePole_with_step5_modeVerticalDiff
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    {F : ℕ → ℂ → ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff F σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hrect0 :
      ∀ n : ℕ, RectangleIntegral (F n) (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_rotatedStripModeMomentData
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    (rotatedStripModeMomentData_of_step5_modeVerticalDiff
      (γ := γ)
      (f := unitIntervalWitness (spectralAmplitude g σ σ'))
      (M := modeVerticalDiff F σ σ') (F := F) (σ := σ) (σ' := σ') (T := T)
      hMomentVertical (fun _ => rfl) hctx hrect0)

theorem mellinGoal_of_invZetaSimplePole_with_step5_modeVerticalDiff_and_holomorphicRect
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    {F : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff F σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (F n) σ σ' T)
    (hhol : ∀ n : ℕ, HolomorphicOn (F n) U)
    (hsub : (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ U) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_modeVerticalDiff
    (γ := γ) (ρ := ρ) (g := g) (F := F) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hMomentVertical hctx (rectangle_family_zero_of_holomorphicOn hhol hsub)

theorem mellinGoal_of_invZetaSimplePole_with_constant_step5_modeVerticalDiff
    {γ : ℕ → ℝ} {ρ : ℂ} {g F : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          (VerticalIntegral F σ' - VerticalIntegral F σ))
    (hctx : Step5Context F σ σ' T)
    (hrect0 : RectangleIntegral F (↑σ - I * ↑T) (↑σ' + I * ↑T) = 0) :
    MellinOrthogonalityGoal γ := by
  refine mellinGoal_of_invZetaSimplePole_with_step5_modeVerticalDiff
    (γ := γ) (ρ := ρ) (g := g) (F := fun _ : ℕ => F) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    ?_ ?_ ?_
  · intro n
    simpa [modeVerticalDiff] using hMomentVertical n
  · intro n
    simpa using hctx
  · intro n
    simpa using hrect0

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ} {U : Set ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (onLineModeContourFamily g γ n) σ σ' T)
    (hhol : ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) U)
    (hsub : (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ U) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_modeVerticalDiff_and_holomorphicRect
    (γ := γ) (ρ := ρ) (g := g) (F := onLineModeContourFamily g γ)
    (σ := σ) (σ' := σ') (T := T) (A := A) (U := U)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hMomentVertical hctx hhol hsub

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (onLineModeContourFamily g γ n) σ σ' T)
    (hsub :
      (↑σ - I * ↑T).Rectangle (↑σ' + I * ↑T) ⊆ stripMinusPole σ σ' ρ) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    (U := stripMinusPole σ σ' ρ)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hMomentVertical hctx
    (onLineModeContourFamily_holoOn_stripMinusPole_of_nonzero
      (g := g) (γ := γ) (σ := σ) (σ' := σ') (p := ρ)
      hOneStrip hNonzeroStrip hgStrip)
    hsub

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole_imOutside
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (onLineModeContourFamily g γ n) σ σ' T) :
    MellinOrthogonalityGoal γ := by
  have hσσ' : σ ≤ σ' := by linarith [hσp.1, hσp.2]
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hMomentVertical hctx
    (rectangle_subset_stripMinusPole_of_im_outside
      (σ := σ) (σ' := σ') (T := T) (p := ρ) hσσ' hT hImOutside)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole_imOutside_of_modeIdentity
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude g σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (onLineModeContourFamily g γ n) σ σ' T) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole_imOutside
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hImOutside
    (modeVerticalDiff_eq_of_unitInterval_modeIdentity
      (γ := γ) (w := spectralAmplitude g σ σ') (g := g) (σ := σ) (σ' := σ')
      hModeIdentity)
    hctx

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole_imOutside_of_modeIdentity_inv
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          (spectralAmplitude g σ σ')⁻¹ *
            modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hctx : ∀ n : ℕ, Step5Context (onLineModeContourFamily g γ n) σ σ' T) :
    MellinOrthogonalityGoal γ := by
  have hAmpNe : spectralAmplitude g σ σ' ≠ 0 :=
    spectralAmplitude_ne_zero_of_invZetaSimplePole
      (g := g) (σ := σ) (σ' := σ') (p := ρ) (A := A)
      hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole_imOutside
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hImOutside
    (modeVerticalDiff_eq_of_unitInterval_modeIdentity_inv
      (γ := γ) (w := spectralAmplitude g σ σ') (g := g) (σ := σ) (σ' := σ')
      hAmpNe hModeIdentity)
    hctx

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hUpperHol :
      ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) (upperStrip σ σ' T))
    (hLowerHol :
      ∀ n : ℕ, HolomorphicOn (onLineModeContourFamily g γ n) (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeftMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)))
    (hRightMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_of_stripMinusPole_imOutside
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hImOutside hMomentVertical
    (step5Context_family_of_data
      (F := onLineModeContourFamily g γ) (σ := σ) (σ' := σ') (T := T)
      (by linarith [hσp.1, hσp.2]) hUpperHol hLowerHol hTop hBot hLeftMode hRightMode)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hOneUpper : (1 : ℂ) ∉ upperStrip σ σ' T)
    (hOneLower : (1 : ℂ) ∉ lowerStrip σ σ' T)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeftMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)))
    (hRightMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hImOutside hMomentVertical
    (onLineModeContourFamily_holoOn_upperStrip_of_nonzero
      (g := g) (γ := γ) (σ := σ) (σ' := σ') (T := T)
      hOneUpper hNonzeroUpper hgUpper)
    (onLineModeContourFamily_holoOn_lowerStrip_of_nonzero
      (g := g) (γ := γ) (σ := σ) (σ' := σ') (T := T)
      hOneLower hNonzeroLower hgLower)
    hTop hBot hLeftMode hRightMode

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hMomentVertical :
      ∀ n : ℕ,
        onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeftMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)))
    (hRightMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hImOutside hMomentVertical
    (one_not_mem_upperStrip_of_pos (σ := σ) (σ' := σ') (T := T) hTpos)
    (one_not_mem_lowerStrip_of_pos (σ := σ) (σ' := σ') (T := T) hTpos)
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot hLeftMode hRightMode

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude g σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeftMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)))
    (hRightMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside
    (modeVerticalDiff_eq_of_unitInterval_modeIdentity
      (γ := γ) (w := spectralAmplitude g σ σ') (g := g) (σ := σ) (σ' := σ')
      hModeIdentity)
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot hLeftMode hRightMode

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude g σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot
    (fun n => integrable_left_onLineModeContourFamily_of_integrable_left (g := g) (γ := γ)
      (σ := σ) n hLeft)
    (fun n => integrable_right_onLineModeContourFamily_of_integrable_right (g := g) (γ := γ)
      (σ' := σ') n hRight)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hγ : ∀ n : ℕ, γ n ≠ 0)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' *
            ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeftMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)))
    (hRightMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside
    (modeVerticalDiff_eq_of_contourExpFormula
      (γ := γ) (w := spectralAmplitude g σ σ') (g := g) (σ := σ) (σ' := σ')
      hγ hContourFormula)
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot hLeftMode hRightMode

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_autoVertical
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hγ : ∀ n : ℕ, γ n ≠ 0)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' *
            ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hγ hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot
    (fun n => integrable_left_onLineModeContourFamily_of_integrable_left (g := g) (γ := γ)
      (σ := σ) n hLeft)
    (fun n => integrable_right_onLineModeContourFamily_of_integrable_right (g := g) (γ := γ)
      (σ' := σ') n hRight)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0))
    (hLeftMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ + ↑y * I)))
    (hRightMode :
      ∀ n : ℕ, Integrable (fun y : ℝ => onLineModeContourFamily g γ n (↑σ' + ↑y * I))) :
    MellinOrthogonalityGoal γ := by
  have hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude g σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
    intro n
    calc
      spectralAmplitude g σ σ' * ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t
          = spectralAmplitude g σ σ' * unitIntervalModeFactor (γ n) := by
              congr 1
              exact setIntegral_onLineMode_Icc_eq_unitIntervalModeFactor (ξ := γ n)
      _ = modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n := by
            symm
            exact hContourFormula n
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot hLeftMode hRightMode

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atTop (nhds 0))
    (hBot :
      ∀ n : ℕ,
        Tendsto (fun y : ℝ =>
          ∫ x : ℝ in σ..σ', onLineModeContourFamily g γ n (↑x + ↑y * I)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hTop hBot
    (fun n => integrable_left_onLineModeContourFamily_of_integrable_left (g := g) (γ := γ)
      (σ := σ) n hLeft)
    (fun n => integrable_right_onLineModeContourFamily_of_integrable_right (g := g) (γ := γ)
      (σ' := σ') n hRight)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedTails
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTopW :
      ∀ n : ℕ, Tendsto (fun y : ℝ =>
        ∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) atTop (nhds 0))
    (hBotW :
      ∀ n : ℕ, Tendsto (fun y : ℝ =>
        ∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun n => top_onLineModeContourFamily_of_weightedTop g γ n σ σ' (hTopW n))
    (fun n => bot_onLineModeContourFamily_of_weightedBot g γ n σ σ' (hBotW n))

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedDecay
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay g (γ n) σ σ') :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedTails
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun n => (hWeightedDecay n).top)
    (fun n => (hWeightedDecay n).bot)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedTails
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude g σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTopW :
      ∀ n : ℕ, Tendsto (fun y : ℝ =>
        ∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) atTop (nhds 0))
    (hBotW :
      ∀ n : ℕ, Tendsto (fun y : ℝ =>
        ∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun n => top_onLineModeContourFamily_of_weightedTop g γ n σ σ' (hTopW n))
    (fun n => bot_onLineModeContourFamily_of_weightedBot g γ n σ σ' (hBotW n))

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedDecay
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude g σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay g (γ n) σ σ') :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedTails
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun n => (hWeightedDecay n).top)
    (fun n => (hWeightedDecay n).bot)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_autoVertical_of_weightedTails
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hγ : ∀ n : ℕ, γ n ≠ 0)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' *
            ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTopW :
      ∀ n : ℕ, Tendsto (fun y : ℝ =>
        ∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) atTop (nhds 0))
    (hBotW :
      ∀ n : ℕ, Tendsto (fun y : ℝ =>
        ∫ x : ℝ in σ..σ',
          Complex.exp (-(((γ n) : ℂ) * (x : ℂ))) *
            spectralIntegrand g (↑x + ↑y * I)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_autoVertical
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hγ hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun n => top_onLineModeContourFamily_of_weightedTop g γ n σ σ' (hTopW n))
    (fun n => bot_onLineModeContourFamily_of_weightedBot g γ n σ σ' (hBotW n))

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_autoVertical_of_weightedDecay
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn g U0)
    (hgp : g ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hγ : ∀ n : ℕ, γ n ≠ 0)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily g γ) σ σ' n =
          spectralAmplitude g σ σ' *
            ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay g (γ n) σ σ') :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_autoVertical_of_weightedTails
    (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hγ hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun n => (hWeightedDecay n).top)
    (fun n => (hWeightedDecay n).bot)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_eventualEnvelope
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {L : ℝ → ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hLnonneg : ∀ y : ℝ, 0 ≤ L y)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ L y)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2))
    (hTopRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atTop (nhds 0))
    (hBotRatio :
      Tendsto (fun y : ℝ => L y / (1 + y ^ 2)) atBot (nhds 0)) :
    MellinOrthogonalityGoal γ := by
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_envelope_ratio_autoWeight_eventually
      (ξ := γ n) (σ := σ) (σ' := σ') (L := L)
      hLnonneg hLogDerivTop hLogDerivBot hKernel hTopRatio hBotRatio
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logSqEnvelope
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    MellinOrthogonalityGoal γ := by
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_eventualEnvelope
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A)
    (L := fun y : ℝ => C * (Real.log (2 + |y|)) ^ 2)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    (fun y => by positivity)
    hLogDerivTop hLogDerivBot hKernel
    (tendsto_logSqEnvelope_ratio_atTop hCnonneg)
    (tendsto_logSqEnvelope_ratio_atBot hCnonneg)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logSqEnvelope_absLarge
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    MellinOrthogonalityGoal γ := by
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge
      (ξ := γ n) (σ := σ) (σ' := σ') (C := C) (Y := Y)
      hCnonneg hLogDerivAbs hKernel
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logSqEnvelope_absLarge_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2) :
    MellinOrthogonalityGoal γ := by
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logSqEnvelope_absLarge
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A) (C := C) (Y := Y)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    hCnonneg hLogDerivAbs
    (fun y x hx => invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logSqEnvelope_absLargeData_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hEnv : InvSqLogSqEnvelopeAbsLargeData σ σ') :
    MellinOrthogonalityGoal γ := by
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logSqEnvelope_absLarge_autoKernel
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A)
    (C := hEnv.C) (Y := hEnv.Y)
    hσp hσσ' hσ0 hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hEnv.hCnonneg hEnv.hLogDerivAbs

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logSqEnvelope
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivTop :
      ∀ᶠ y : ℝ in atTop,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hLogDerivBot :
      ∀ᶠ y : ℝ in atBot,
        ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
          ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    MellinOrthogonalityGoal γ := by
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_eventually
      (ξ := γ n) (σ := σ) (σ' := σ') (C := C)
      hCnonneg hLogDerivTop hLogDerivBot hKernel
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logSqEnvelope_absLarge
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2)
    (hKernel :
      ∀ (y x : ℝ), x ∈ Set.uIoc σ σ' →
        ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2)) :
    MellinOrthogonalityGoal γ := by
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logSqEnvelope_of_absLarge
      (ξ := γ n) (σ := σ) (σ' := σ') (C := C) (Y := Y)
      hCnonneg hLogDerivAbs hKernel
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logSqEnvelope_absLarge_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 2) :
    MellinOrthogonalityGoal γ := by
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logSqEnvelope_absLarge
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A) (C := C) (Y := Y)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower
    hCnonneg hLogDerivAbs
    (fun y x hx => invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx)

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logSqEnvelope_absLargeData_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hEnv : InvSqLogSqEnvelopeAbsLargeData σ σ') :
    MellinOrthogonalityGoal γ := by
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logSqEnvelope_absLarge_autoKernel
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A)
    (C := hEnv.C) (Y := hEnv.Y)
    hσp hσσ' hσ0 hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hEnv.hCnonneg hEnv.hLogDerivAbs

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logPowNineEnvelope_absLarge_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9) :
    MellinOrthogonalityGoal γ := by
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logPowNineEnvelope_of_absLarge
      (ξ := γ n) (σ := σ) (σ' := σ') (C := C) (Y := Y)
      hCnonneg hLogDerivAbs
      (fun y x hx => invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx)
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logPowNineEnvelope_nearOneWindow_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {Aw C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hY3 : 3 < Y)
    (hLogDerivUnif :
      ∀ (x t : ℝ), 3 < |t| →
        x ∈ Set.Ici (1 - Aw / Real.log |t| ^ 9) →
          ‖zetaLogDeriv (↑x + ↑t * I)‖ ≤ C * Real.log |t| ^ 9)
    (hWindow :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        x ∈ Set.Ici (1 - Aw / Real.log |y| ^ 9)) :
    MellinOrthogonalityGoal γ := by
  have hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9 :=
    logDerivAbs_logPowNineEnvelope_of_nearOneWindow
      (σ := σ) (σ' := σ') (A := Aw) (C := C) (Y := Y)
      hCnonneg hY3 hLogDerivUnif hWindow
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_logPowNineEnvelope_absLarge_autoKernel
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A) (C := C) (Y := Y)
    hσp hσσ' hσ0 hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hCnonneg hLogDerivAbs

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logPowNineEnvelope_absLarge_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9) :
    MellinOrthogonalityGoal γ := by
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_logPowNineEnvelope_of_absLarge
      (ξ := γ n) (σ := σ) (σ' := σ') (C := C) (Y := Y)
      hCnonneg hLogDerivAbs
      (fun y x hx => invSqKernel_bound_on_uIoc_of_nonneg_left (y := y) hσσ' hσ0 x hx)
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logPowNineEnvelope_nearOneWindow_autoKernel
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ} {Aw C Y : ℝ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ0 : 0 ≤ σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hDecay : HorizontalDecay invSqKernel σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T))
    (hCnonneg : 0 ≤ C)
    (hY3 : 3 < Y)
    (hLogDerivUnif :
      ∀ (x t : ℝ), 3 < |t| →
        x ∈ Set.Ici (1 - Aw / Real.log |t| ^ 9) →
          ‖zetaLogDeriv (↑x + ↑t * I)‖ ≤ C * Real.log |t| ^ 9)
    (hWindow :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        x ∈ Set.Ici (1 - Aw / Real.log |y| ^ 9)) :
    MellinOrthogonalityGoal γ := by
  have hLogDerivAbs :
      ∀ (y x : ℝ), Y ≤ |y| → x ∈ Set.uIoc σ σ' →
        ‖zetaLogDeriv (↑x + ↑y * I)‖ ≤ C * (Real.log (2 + |y|)) ^ 9 :=
    logDerivAbs_logPowNineEnvelope_of_nearOneWindow
      (σ := σ) (σ' := σ') (A := Aw) (C := C) (Y := Y)
      hCnonneg hY3 hLogDerivUnif hWindow
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_logPowNineEnvelope_absLarge_autoKernel
    (γ := γ) (ρ := ρ) (σ := σ) (σ' := σ') (T := T) (A := A) (C := C) (Y := Y)
    hσp hσσ' hσ0 hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hCnonneg hLogDerivAbs

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_invSqKernel_of_gt_one
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσgt : 1 < σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hModeIdentity :
      ∀ n : ℕ,
        spectralAmplitude invSqKernel σ σ' *
            ∫ t : ℝ in Set.Icc (0 : ℝ) 1, onLineMode (γ n) t =
          modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T)) :
    MellinOrthogonalityGoal γ := by
  have hσσ' : σ ≤ σ' := by linarith [hσp.1, hσp.2]
  have hDecay : HorizontalDecay invSqKernel σ σ' :=
    horizontalDecay_of_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσgt
  rcases integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσgt
    with ⟨hLeft, hRight⟩
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_vertical_logDeriv_bound
      (ξ := γ n) hσσ' hσgt
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_modeIdentity_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hModeIdentity
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_invSqKernel_of_gt_one
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσgt : 1 < σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hγ : ∀ n : ℕ, γ n ≠ 0)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' *
            ((Complex.exp (-((γ n : ℂ) * I)) - 1) / (-((γ n : ℂ) * I))))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T)) :
    MellinOrthogonalityGoal γ := by
  have hσσ' : σ ≤ σ' := by linarith [hσp.1, hσp.2]
  have hDecay : HorizontalDecay invSqKernel σ σ' :=
    horizontalDecay_of_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσgt
  rcases integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσgt
    with ⟨hLeft, hRight⟩
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_vertical_logDeriv_bound
      (ξ := γ n) hσσ' hσgt
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourExpFormula_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hγ hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

theorem mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_invSqKernel_of_gt_one
    {γ : ℕ → ℝ} {ρ : ℂ} {σ σ' T : ℝ} {A : ℂ}
    (hσp : σ < ρ.re ∧ ρ.re < σ')
    (hσgt : 1 < σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' ρ))
    (hgNear : ∃ U0 : Set ℂ, U0 ∈ nhds ρ ∧ HolomorphicOn invSqKernel U0)
    (hgp : invSqKernel ρ ≠ 0)
    (hInvModel : InvZetaSimplePoleModel ρ A)
    (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hImOutside : ρ.im < -T ∨ T < ρ.im)
    (hContourFormula :
      ∀ n : ℕ,
        modeVerticalDiff (onLineModeContourFamily invSqKernel γ) σ σ' n =
          spectralAmplitude invSqKernel σ σ' * unitIntervalModeFactor (γ n))
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn invSqKernel (upperStrip σ σ' T))
    (hgLower : HolomorphicOn invSqKernel (lowerStrip σ σ' T)) :
    MellinOrthogonalityGoal γ := by
  have hσσ' : σ ≤ σ' := by linarith [hσp.1, hσp.2]
  have hDecay : HorizontalDecay invSqKernel σ σ' :=
    horizontalDecay_of_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσgt
  rcases integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσgt
    with ⟨hLeft, hRight⟩
  have hWeightedDecay : ∀ n : ℕ, WeightedHorizontalDecay invSqKernel (γ n) σ σ' := by
    intro n
    exact weightedHorizontalDecay_of_spectralIntegrand_invSqKernel_of_vertical_logDeriv_bound
      (ξ := γ n) hσσ' hσgt
  exact mellinGoal_of_invZetaSimplePole_with_step5_onLineModeContourFamily_data_of_nonzero_of_posT_of_contourUnitIntervalFormula_autoVertical_of_weightedDecay
    (γ := γ) (ρ := ρ) (g := invSqKernel) (σ := σ) (σ' := σ') (T := T) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    hT hTpos hImOutside hContourFormula
    hNonzeroUpper hNonzeroLower hgUpper hgLower hWeightedDecay

end MellinOrthogonality
