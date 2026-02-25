import Collatz.MellinOrthogonality.Step5

open Complex MeasureTheory

namespace MellinOrthogonality

/-- Target statement replacing `PNTBridge.mellin_contour_orthogonality`. -/
def MellinOrthogonalityGoal (γ : ℕ → ℝ) : Prop :=
  ∃ f : Lp ℂ 2 (volume : Measure ℝ), f ≠ 0 ∧
    ∀ n : ℕ, ∫ t : ℝ, (f : ℝ → ℂ) t * Complex.exp (-(γ n) * ↑t * I) ∂volume = 0

/-- Step-6 assembly endpoint: once this is proved, the Mellin contour axiom
can be removed from the PNT bridge. -/
def MellinOrthogonalityAssembler : Prop :=
  ∀ (γ : ℕ → ℝ) (ρ : ℂ),
    riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ (1 / 2 : ℝ) →
    MellinOrthogonalityGoal γ

/-- Direct replacement form for the old axiom signature. -/
theorem mellin_contour_orthogonality_target
    (hstep6 : MellinOrthogonalityAssembler) :
    ∀ (γ : ℕ → ℝ) (ρ : ℂ),
      riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ (1 / 2 : ℝ) →
      MellinOrthogonalityGoal γ :=
  hstep6

/-- `explicit_formula_from_pnt_bridge` rewritten with Step-6 as an input
parameter rather than as a global axiom. -/
theorem explicit_formula_from_step6
    (beurling_malliavin_completeness :
      ∀ (γ : ℕ → ℝ)
        (_ :
          ∀ C : ℝ, ∃ T₀ : ℝ, ∀ T > T₀,
            C <
              (Finset.filter (fun n => |γ n| ≤ T)
                (Finset.range (Nat.succ ⌈T⌉₊))).card / T),
        ∀ f : Lp ℂ 2 (volume : Measure ℝ),
          (∀ n : ℕ,
            ∫ t : ℝ, (f : ℝ → ℂ) t * Complex.exp (-(γ n) * ↑t * I) ∂volume = 0) →
            f = 0)
    (hstep6 : MellinOrthogonalityAssembler)
    (γ : ℕ → ℝ)
    (hdensity :
      ∀ C : ℝ, ∃ T₀ : ℝ, ∀ T > T₀,
        C <
          (Finset.filter (fun n => |γ n| ≤ T)
            (Finset.range (Nat.succ ⌈T⌉₊))).card / T) :
    ∀ (ρ : ℂ), riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2 := by
  intro ρ hζ hlo hhi
  by_contra hoff
  obtain ⟨f, hne, horth⟩ := hstep6 γ ρ hζ hlo hhi hoff
  exact hne (beurling_malliavin_completeness γ hdensity f horth)

end MellinOrthogonality
