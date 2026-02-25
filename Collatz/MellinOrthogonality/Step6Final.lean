import Collatz.MellinOrthogonality.Step6Orthogonality

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Packaged Step-6 input for one off-line zero candidate: contour strip data,
local inverse-zeta simple-pole model, and contour-derived mode moment model
for the resulting `Lp` witness. -/
structure OffLineStep6Package (γ : ℕ → ℝ) (ρ : ℂ) where
  g : ℂ → ℂ
  σ : ℝ
  σ' : ℝ
  A : ℂ
  hσp : σ < ρ.re ∧ ρ.re < σ'
  hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ
  hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0
  hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ)
  hDecay : HorizontalDecay g σ σ'
  hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I)
  hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)
  hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U
  hgp : g ρ ≠ 0
  hInvModel : InvZetaSimplePoleModel ρ A
  hmodeModel :
    ContourModeMomentModel γ
      (unitIntervalWitness (spectralAmplitude g σ σ'))

/-- Stronger Step-6 package where mode orthogonality is supplied as explicit
moment identities (`moment = M`) plus contour vanishing equations (`M = 0`),
rather than directly as an orthogonality predicate.  This is the concrete
target shape for rotated-strip contour-shift execution. -/
structure OffLineStep6ContourMomentPackage (γ : ℕ → ℝ) (ρ : ℂ) where
  g : ℂ → ℂ
  σ : ℝ
  σ' : ℝ
  A : ℂ
  hσp : σ < ρ.re ∧ ρ.re < σ'
  hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' ρ
  hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' ρ, riemannZeta s ≠ 0
  hgStrip : HolomorphicOn g (stripMinusPole σ σ' ρ)
  hDecay : HorizontalDecay g σ σ'
  hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I)
  hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)
  hgNear : ∃ U : Set ℂ, U ∈ nhds ρ ∧ HolomorphicOn g U
  hgp : g ρ ≠ 0
  hInvModel : InvZetaSimplePoleModel ρ A
  M : ℕ → ℂ
  hMomentEq :
    ∀ n : ℕ,
      onLineModeMoment γ (unitIntervalWitness (spectralAmplitude g σ σ')) n = M n
  hMomentZero : ∀ n : ℕ, M n = 0

def OffLineStep6ContourMomentPackage.toOffLineStep6Package
    {γ : ℕ → ℝ} {ρ : ℂ}
    (hpack : OffLineStep6ContourMomentPackage γ ρ) :
    OffLineStep6Package γ ρ where
  g := hpack.g
  σ := hpack.σ
  σ' := hpack.σ'
  A := hpack.A
  hσp := hpack.hσp
  hOneStrip := hpack.hOneStrip
  hNonzeroStrip := hpack.hNonzeroStrip
  hgStrip := hpack.hgStrip
  hDecay := hpack.hDecay
  hLeft := hpack.hLeft
  hRight := hpack.hRight
  hgNear := hpack.hgNear
  hgp := hpack.hgp
  hInvModel := hpack.hInvModel
  hmodeModel := ⟨hpack.M, hpack.hMomentEq, hpack.hMomentZero⟩

def offLineStep6ContourMomentPackage_of_modeEquations
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ} {A : ℂ}
    {M : ℕ → ℂ}
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
    (hMomentZero : ∀ n : ℕ, M n = 0) :
    OffLineStep6ContourMomentPackage γ ρ where
  g := g
  σ := σ
  σ' := σ'
  A := A
  hσp := hσp
  hOneStrip := hOneStrip
  hNonzeroStrip := hNonzeroStrip
  hgStrip := hgStrip
  hDecay := hDecay
  hLeft := hLeft
  hRight := hRight
  hgNear := hgNear
  hgp := hgp
  hInvModel := hInvModel
  M := M
  hMomentEq := hMomentEq
  hMomentZero := hMomentZero

theorem mellinGoal_of_offLineStep6Package
    {γ : ℕ → ℝ} {ρ : ℂ}
    (hpack : OffLineStep6Package γ ρ) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_invZetaSimplePole_with_modeContourModel
    (γ := γ) (g := hpack.g) (σ := hpack.σ) (σ' := hpack.σ')
    (p := ρ) (A := hpack.A)
    hpack.hσp hpack.hOneStrip hpack.hNonzeroStrip hpack.hgStrip hpack.hDecay
    hpack.hLeft hpack.hRight hpack.hgNear hpack.hgp hpack.hInvModel hpack.hmodeModel

theorem mellinOrthogonalityAssembler_of_offLineStep6Package
    (hpack :
      ∀ (γ : ℕ → ℝ) (ρ : ℂ),
        riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ (1 / 2 : ℝ) →
        OffLineStep6Package γ ρ) :
    MellinOrthogonalityAssembler := by
  intro γ ρ hζ hlo hhi hoff
  exact mellinGoal_of_offLineStep6Package (hpack γ ρ hζ hlo hhi hoff)

theorem mellinGoal_of_offLineStep6ContourMomentPackage
    {γ : ℕ → ℝ} {ρ : ℂ}
    (hpack : OffLineStep6ContourMomentPackage γ ρ) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_offLineStep6Package hpack.toOffLineStep6Package

theorem mellinGoal_of_invZetaSimplePole_with_modeEquations
    {γ : ℕ → ℝ} {ρ : ℂ} {g : ℂ → ℂ} {σ σ' : ℝ} {A : ℂ}
    {M : ℕ → ℂ}
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
    (hMomentZero : ∀ n : ℕ, M n = 0) :
    MellinOrthogonalityGoal γ :=
  mellinGoal_of_offLineStep6ContourMomentPackage
    (offLineStep6ContourMomentPackage_of_modeEquations
      (γ := γ) (ρ := ρ) (g := g) (σ := σ) (σ' := σ') (A := A) (M := M)
      hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear hgp hInvModel
      hMomentEq hMomentZero)

theorem mellinOrthogonalityAssembler_of_offLineStep6ContourMomentPackage
    (hpack :
      ∀ (γ : ℕ → ℝ) (ρ : ℂ),
        riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ (1 / 2 : ℝ) →
        OffLineStep6ContourMomentPackage γ ρ) :
    MellinOrthogonalityAssembler := by
  intro γ ρ hζ hlo hhi hoff
  exact mellinGoal_of_offLineStep6ContourMomentPackage (hpack γ ρ hζ hlo hhi hoff)

end MellinOrthogonality
