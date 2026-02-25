import Collatz.MellinOrthogonality.Step6PrincipalPart

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Raw local simple-pole data for `1/ζ` near `p`; nonvanishing on the punctured
neighborhood is not required at this stage. -/
structure InvZetaSimplePoleData (p A : ℂ) where
  U : Set ℂ
  hU : U ∈ nhds p
  hOne : (1 : ℂ) ∉ U
  hA : A ≠ 0
  hInvNear :
    BddAbove (norm ∘ ((fun s : ℂ => (riemannZeta s)⁻¹) - (fun s : ℂ => A * (s - p)⁻¹)) ''
      (U \ {p}))

/-- Local simple-pole model for `1/ζ` at an off-line zero candidate `p`. -/
structure InvZetaSimplePoleModel (p A : ℂ) where
  U : Set ℂ
  hU : U ∈ nhds p
  hOne : (1 : ℂ) ∉ U
  hA : A ≠ 0
  hZetaNonzero : ∀ s ∈ U \ {p}, riemannZeta s ≠ 0
  hInvNear :
    BddAbove (norm ∘ ((fun s : ℂ => (riemannZeta s)⁻¹) - (fun s : ℂ => A * (s - p)⁻¹)) ''
      (U \ {p}))

theorem InvZetaSimplePoleData.toModel
    {p A : ℂ} (hdata : InvZetaSimplePoleData p A) :
    ∃ hmodel : InvZetaSimplePoleModel p A, hmodel.U ⊆ hdata.U := by
  obtain ⟨V, hV, hVopen, hVnonzero⟩ := nonZeroOfBddAbove
    (f := fun s : ℂ => (riemannZeta s)⁻¹) hdata.hU hdata.hA hdata.hInvNear
  let W : Set ℂ := V ∩ hdata.U
  have hW : W ∈ nhds p := inter_mem hV hdata.hU
  have hWone : (1 : ℂ) ∉ W := by
    intro h1
    exact hdata.hOne h1.2
  have hWnonzero : ∀ s ∈ W \ {p}, riemannZeta s ≠ 0 := by
    intro s hs hzeta
    have hinv_ne : (riemannZeta s)⁻¹ ≠ 0 := hVnonzero s ⟨hs.1.1, hs.2⟩
    exact hinv_ne (by simp [hzeta])
  have hWInvNear :
      BddAbove (norm ∘ ((fun s : ℂ => (riemannZeta s)⁻¹) - (fun s : ℂ => A * (s - p)⁻¹)) ''
        (W \ {p})) := by
    refine hdata.hInvNear.mono (image_mono ?_)
    exact diff_subset_diff inter_subset_right subset_rfl
  refine ⟨
    { U := W
      hU := hW
      hOne := hWone
      hA := hdata.hA
      hZetaNonzero := hWnonzero
      hInvNear := hWInvNear }, ?_⟩
  intro z hz
  exact hz.2

theorem exists_invZetaSimplePoleData_of_isBigO
    {p A : ℂ}
    (hp : p ≠ 1)
    (hA : A ≠ 0)
    (hInvBigO :
      ((fun s : ℂ => (riemannZeta s)⁻¹) - (fun s : ℂ => A * (s - p)⁻¹))
        =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ)) :
    ∃ _ : InvZetaSimplePoleData p A, True := by
  obtain ⟨U, hU, hBdd⟩ := IsBigO_to_BddAbove (p := p) (f := fun s : ℂ =>
    (riemannZeta s)⁻¹ - A * (s - p)⁻¹) (by simpa [Pi.sub_apply] using hInvBigO)
  let W : Set ℂ := U ∩ {1}ᶜ
  have hW : W ∈ nhds p := by
    refine inter_mem hU ?_
    exact isOpen_compl_singleton.mem_nhds hp
  have hWone : (1 : ℂ) ∉ W := by
    intro h1
    exact h1.2 rfl
  have hWBdd :
      BddAbove (norm ∘ ((fun s : ℂ => (riemannZeta s)⁻¹) - (fun s : ℂ => A * (s - p)⁻¹)) ''
        (W \ {p})) := by
    refine hBdd.mono (image_mono ?_)
    exact diff_subset_diff inter_subset_left subset_rfl
  refine ⟨
    { U := W
      hU := hW
      hOne := hWone
      hA := hA
      hInvNear := by simpa [Pi.sub_apply] using hWBdd }, trivial⟩

theorem zetaLogDeriv_principalPart_of_invZetaSimplePole
    {p A : ℂ} (hmodel : InvZetaSimplePoleModel p A) :
    (zetaLogDeriv - (fun s : ℂ => (s - p)⁻¹)) =O[nhdsWithin p {p}ᶜ]
      (1 : ℂ → ℂ) := by
  let f : ℂ → ℂ := fun s => (riemannZeta s)⁻¹
  have hnonzero_f : ∀ s ∈ hmodel.U \ {p}, f s ≠ 0 := by
    intro s hs
    simpa [f] using inv_ne_zero (hmodel.hZetaNonzero s hs)
  have hhol_f : HolomorphicOn f (hmodel.U \ {p}) := by
    intro s hs
    have hsU : s ∈ hmodel.U := hs.1
    have hs1 : s ≠ 1 := by
      intro hs1
      exact hmodel.hOne (hs1 ▸ hsU)
    exact (DifferentiableAt.inv (differentiableAt_riemannZeta hs1)
      (hmodel.hZetaNonzero s hs)).differentiableWithinAt
  have hlog_f :
      (deriv f * f⁻¹ + (fun s : ℂ => (s - p)⁻¹)) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ) :=
    logDerivResidue hnonzero_f hhol_f hmodel.hU hmodel.hA hmodel.hInvNear
  have hEqOn :
      EqOn (fun s : ℂ => deriv f s * (f s)⁻¹ + (s - p)⁻¹)
        (fun s : ℂ => -zetaLogDeriv s + (s - p)⁻¹) (hmodel.U \ {p}) := by
    intro s hs
    have hsU : s ∈ hmodel.U := hs.1
    have hs1 : s ≠ 1 := by
      intro hs1
      exact hmodel.hOne (hs1 ▸ hsU)
    have hzeta : riemannZeta s ≠ 0 := hmodel.hZetaNonzero s hs
    have hderiv :
        deriv f s = -deriv riemannZeta s / riemannZeta s ^ 2 := by
      simpa [f] using (deriv_inv'' (c := riemannZeta) (x := s)
        (differentiableAt_riemannZeta hs1) hzeta)
    calc
      deriv f s * (f s)⁻¹ + (s - p)⁻¹
          = (-deriv riemannZeta s / riemannZeta s ^ 2) * riemannZeta s + (s - p)⁻¹ := by
              simp [hderiv, f]
      _ = -zetaLogDeriv s + (s - p)⁻¹ := by
            simp [zetaLogDeriv, div_eq_mul_inv]
            field_simp [hzeta]
  have hmem : hmodel.U \ {p} ∈ nhdsWithin p ({p}ᶜ) :=
    diff_mem_nhdsWithin_compl hmodel.hU {p}
  have hEq :
      (fun s : ℂ => deriv f s * (f s)⁻¹ + (s - p)⁻¹) =ᶠ[nhdsWithin p ({p}ᶜ)]
        (fun s : ℂ => -zetaLogDeriv s + (s - p)⁻¹) :=
    Set.EqOn.eventuallyEq_of_mem hEqOn hmem
  have hneg :
      (fun s : ℂ => -zetaLogDeriv s + (s - p)⁻¹) =O[nhdsWithin p ({p}ᶜ)]
        (1 : ℂ → ℂ) := hlog_f.congr' hEq (Filter.EventuallyEq.rfl)
  have hmul :
      (fun s : ℂ => (-1 : ℂ) * (-zetaLogDeriv s + (s - p)⁻¹)) =O[nhdsWithin p ({p}ᶜ)]
        (1 : ℂ → ℂ) := hneg.const_mul_left (-1 : ℂ)
  simpa [sub_eq_add_neg, mul_add, add_assoc, add_left_comm, add_comm] using hmul

theorem vertical_diff_ne_zero_of_invZetaSimplePole
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
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ ≠ 0 := by
  exact vertical_diff_ne_zero_of_zetaLogDeriv_principalPart
    (g := g) (σ := σ) (σ' := σ') (p := p)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hgNear
    (zetaLogDeriv_principalPart_of_invZetaSimplePole (p := p) (A := A) hInvModel) hgp

end MellinOrthogonality
