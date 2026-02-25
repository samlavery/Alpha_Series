import Collatz.MellinOrthogonality.Step6InvZetaModel

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Spectral amplitude from a two-line contour difference. -/
noncomputable def spectralAmplitude (g : ℂ → ℂ) (σ σ' : ℝ) : ℂ :=
  VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ

/-- Concrete `Lp` witness built from a scalar by placing it on `[0,1]`. -/
noncomputable def unitIntervalWitness (w : ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    measurableSet_Icc (by
      exact (measure_Icc_lt_top (a := (0 : ℝ)) (b := 1) (μ := (volume : Measure ℝ))).ne) w

theorem unitIntervalWitness_ne_zero {w : ℂ} (hw : w ≠ 0) :
    unitIntervalWitness w ≠ 0 := by
  have hp0 : (2 : ENNReal) ≠ 0 := by norm_num
  have hptop : (2 : ENNReal) ≠ ⊤ := by norm_num
  have hμ : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) ≠ (⊤ : ENNReal) :=
    (measure_Icc_lt_top (a := (0 : ℝ)) (b := 1) (μ := (volume : Measure ℝ))).ne
  have hnorm :
      ‖unitIntervalWitness w‖ = ‖w‖ * (volume : Measure ℝ).real (Set.Icc (0 : ℝ) 1) ^
        (1 / (2 : ENNReal).toReal) := by
    simpa [unitIntervalWitness] using
      (norm_indicatorConstLp (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))
        (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc) (hμs := hμ) (c := w) hp0 hptop)
  have hvol : (volume : Measure ℝ).real (Set.Icc (0 : ℝ) 1) = 1 := by
    simp [Real.volume_real_Icc_of_le (a := (0 : ℝ)) (b := 1) zero_le_one]
  have hnorm_ne : ‖unitIntervalWitness w‖ ≠ 0 := by
    rw [hnorm, hvol]
    exact mul_ne_zero (norm_ne_zero_iff.mpr hw) (by norm_num)
  intro hzero
  exact hnorm_ne (by simp [hzero])

theorem spectralAmplitude_ne_zero_of_invZetaSimplePole
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hgp : g p ≠ 0)
    (hInvModel : InvZetaSimplePoleModel p A) :
    spectralAmplitude g σ σ' ≠ 0 := by
  simpa [spectralAmplitude] using vertical_diff_ne_zero_of_invZetaSimplePole
    (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel

/-- Bundled nonzero spectral amplitude witness (scalar stage before `Lp` witness). -/
noncomputable def spectralAmplitudeWitness
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hgp : g p ≠ 0)
    (hInvModel : InvZetaSimplePoleModel p A) :
    {w : ℂ // w ≠ 0} :=
  ⟨spectralAmplitude g σ σ',
    spectralAmplitude_ne_zero_of_invZetaSimplePole
      (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
      hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel⟩

theorem exists_nonzero_lpWitness_of_invZetaSimplePole
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hgp : g p ≠ 0)
    (hInvModel : InvZetaSimplePoleModel p A) :
    ∃ f : Lp ℂ 2 (volume : Measure ℝ), f ≠ 0 := by
  refine ⟨unitIntervalWitness (spectralAmplitude g σ σ'), ?_⟩
  apply unitIntervalWitness_ne_zero
  exact spectralAmplitude_ne_zero_of_invZetaSimplePole
    (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel

end MellinOrthogonality
