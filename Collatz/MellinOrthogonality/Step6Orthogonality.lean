import Collatz.MellinOrthogonality.Step6Witness
import Collatz.MellinOrthogonality.Step6Skeleton

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- On-line oscillatory mode at frequency `ξ`. -/
noncomputable def onLineMode (ξ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-ξ * (t : ℂ) * I)

/-- The `n`-th on-line mode moment of `f`. -/
noncomputable def onLineModeMoment
    (γ : ℕ → ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) : ℂ :=
  ∫ t : ℝ, (f : ℝ → ℂ) t * onLineMode (γ n) t ∂volume

/-- Orthogonality of an `Lp` element to all on-line modes indexed by `γ`. -/
def OrthogonalToOnLineModes (γ : ℕ → ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∀ n : ℕ, onLineModeMoment γ f n = 0

/-- Contour-side encoding of on-line mode moments for `f`.  The intent is to
instantiate `M` by contour-shift expressions and then prove `M n = 0`. -/
def ContourModeMomentModel
    (γ : ℕ → ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  ∃ M : ℕ → ℂ, (∀ n : ℕ, onLineModeMoment γ f n = M n) ∧ (∀ n : ℕ, M n = 0)

theorem orthogonalToOnLineModes_of_contourModeMomentModel
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hmodel : ContourModeMomentModel γ f) :
    OrthogonalToOnLineModes γ f := by
  rcases hmodel with ⟨M, hmoment, hzero⟩
  intro n
  calc
    onLineModeMoment γ f n = M n := hmoment n
    _ = 0 := hzero n

theorem contourModeMomentModel_of_zero_moments
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hzero : ∀ n : ℕ, onLineModeMoment γ f n = 0) :
    ContourModeMomentModel γ f := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro n
    exact hzero n
  · intro n
    rfl

theorem contourModeMomentModel_of_modeEquations
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)} {M : ℕ → ℂ}
    (hMomentEq : ∀ n : ℕ, onLineModeMoment γ f n = M n)
    (hMomentZero : ∀ n : ℕ, M n = 0) :
    ContourModeMomentModel γ f :=
  ⟨M, hMomentEq, hMomentZero⟩

theorem contourModeMomentModel_of_momentEq_and_contourEq
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    {M C : ℕ → ℂ}
    (hMomentEq : ∀ n : ℕ, onLineModeMoment γ f n = M n)
    (hContourEq : ∀ n : ℕ, M n = C n)
    (hContourZero : ∀ n : ℕ, C n = 0) :
    ContourModeMomentModel γ f :=
  contourModeMomentModel_of_modeEquations hMomentEq
    (fun n => (hContourEq n).trans (hContourZero n))

theorem mellinGoal_of_nonzeroLp_and_orthogonality
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hne : f ≠ 0)
    (horth : OrthogonalToOnLineModes γ f) :
    MellinOrthogonalityGoal γ := by
  refine ⟨f, hne, ?_⟩
  intro n
  simpa [OrthogonalToOnLineModes, onLineModeMoment, onLineMode] using horth n

theorem mellinGoal_of_nonzeroLp_and_contourModel
    {γ : ℕ → ℝ} {f : Lp ℂ 2 (volume : Measure ℝ)}
    (hne : f ≠ 0)
    (hmodel : ContourModeMomentModel γ f) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_nonzeroLp_and_orthogonality hne
    (orthogonalToOnLineModes_of_contourModeMomentModel hmodel)

theorem mellinGoal_of_invZetaSimplePole_with_modeOrthogonality
    {γ : ℕ → ℝ} {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hgp : g p ≠ 0)
    (hInvModel : InvZetaSimplePoleModel p A)
    (horth :
      OrthogonalToOnLineModes γ (unitIntervalWitness (spectralAmplitude g σ σ'))) :
    MellinOrthogonalityGoal γ := by
  refine ⟨unitIntervalWitness (spectralAmplitude g σ σ'), ?_, ?_⟩
  · apply unitIntervalWitness_ne_zero
    exact spectralAmplitude_ne_zero_of_invZetaSimplePole
      (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
      hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
  · intro n
    simpa [OrthogonalToOnLineModes, onLineModeMoment, onLineMode] using horth n

theorem mellinGoal_of_invZetaSimplePole_with_modeContourModel
    {γ : ℕ → ℝ} {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hgNear : ∃ U : Set ℂ, U ∈ nhds p ∧ HolomorphicOn g U)
    (hgp : g p ≠ 0)
    (hInvModel : InvZetaSimplePoleModel p A)
    (hmodel :
      ContourModeMomentModel γ
        (unitIntervalWitness (spectralAmplitude g σ σ'))) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_modeOrthogonality
    (γ := γ) (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
    (orthogonalToOnLineModes_of_contourModeMomentModel hmodel)

end MellinOrthogonality
