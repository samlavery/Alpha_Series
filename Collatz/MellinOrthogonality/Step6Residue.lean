import Collatz.MellinOrthogonality.Step6Integrability

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Small-square contour integral around `p` with radius `c`. -/
noncomputable def smallSquareIntegral (g : ℂ → ℂ) (p : ℂ) (c : ℝ) : ℂ :=
  RectangleIntegral (spectralIntegrand g) (-c - c * I + p) (c + c * I + p)

theorem smallSquareIntegral_eq_two_pi_I_mul_of_simplePole
    {g : ℂ → ℂ} {p A : ℂ} {c : ℝ}
    (hc : 0 < c)
    (hHolo :
      HolomorphicOn (spectralIntegrand g)
        (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ)) :
    smallSquareIntegral g p c = (2 * (Real.pi : ℂ) * I) * A := by
  have hzRe : (-c - c * I + p).re ≤ (c + c * I + p).re := by
    simp
    linarith
  have hzIm : (-c - c * I + p).im ≤ (c + c * I + p).im := by
    simp
    linarith
  have hpNhd : Rectangle (-c - c * I + p) (c + c * I + p) ∈ nhds p := by
    simpa [Square] using square_mem_nhds p (ne_of_gt hc)
  have hprime :
      RectangleIntegral' (spectralIntegrand g) (-c - c * I + p) (c + c * I + p) = A := by
    exact ResidueTheoremOnRectangleWithSimplePole' hzRe hzIm hpNhd hHolo hNear
  let K : ℂ := 2 * (Real.pi : ℂ) * I
  have hK_ne : K ≠ 0 := by
    dsimp [K]
    simp
  have hdiv :
      RectangleIntegral (spectralIntegrand g) (-c - c * I + p) (c + c * I + p) / K = A := by
    simpa [RectangleIntegral', K, div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      using hprime
  have hrect :
      RectangleIntegral (spectralIntegrand g) (-c - c * I + p) (c + c * I + p) =
      (2 * (Real.pi : ℂ) * I : ℂ) * A := by
    have hrect' :
        RectangleIntegral (spectralIntegrand g) (-c - c * I + p) (c + c * I + p) = A * K :=
      (div_eq_iff hK_ne).1 hdiv
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hrect'
  simpa [smallSquareIntegral] using hrect

theorem smallSquareIntegral_tendsto_two_pi_I_mul_of_simplePole
    {g : ℂ → ℂ} {p A : ℂ}
    (hHolo : ∀ c : ℝ, 0 < c →
      HolomorphicOn (spectralIntegrand g)
        (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ)) :
    Tendsto (smallSquareIntegral g p) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((2 * (Real.pi : ℂ) * I) * A)) := by
  have hevent :
      (smallSquareIntegral g p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun _ : ℝ => (2 * (Real.pi : ℂ) * I) * A) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact smallSquareIntegral_eq_two_pi_I_mul_of_simplePole
      (g := g) (p := p) (A := A) hc (hHolo c hc) hNear
  exact tendsto_const_nhds.congr' hevent.symm

theorem smallSquareIntegral_tendsto_two_pi_I_mul_of_simplePole_eventually
    {g : ℂ → ℂ} {p A : ℂ}
    (hHolo : ∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0),
      HolomorphicOn (spectralIntegrand g)
        (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ)) :
    Tendsto (smallSquareIntegral g p) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((2 * (Real.pi : ℂ) * I) * A)) := by
  have hevent :
      (smallSquareIntegral g p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun _ : ℝ => (2 * (Real.pi : ℂ) * I) * A) := by
    filter_upwards [hHolo, self_mem_nhdsWithin] with c hcHolo hc
    exact smallSquareIntegral_eq_two_pi_I_mul_of_simplePole
      (g := g) (p := p) (A := A) hc hcHolo hNear
  exact tendsto_const_nhds.congr' hevent.symm

theorem eventually_holoOn_smallSquare_of_holoOn_stripMinusPole
    {f : ℂ → ℂ} {σ σ' : ℝ} {p : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hfStrip : HolomorphicOn f (stripMinusPole σ σ' p)) :
    ∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0),
      HolomorphicOn f (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}) := by
  have hrectNhd : Icc σ σ' ×ℂ univ ∈ nhds p := by
    rw [← mem_interior_iff_mem_nhds, Complex.interior_reProdIm, interior_Icc, interior_univ]
    refine ⟨⟨?_, ?_⟩, trivial⟩ <;> linarith [hσp.1, hσp.2]
  obtain ⟨c', hc'0, hc'⟩ := ((nhds_hasBasis_square p).1 _).mp hrectNhd
  filter_upwards [Ioo_mem_nhdsGT hc'0] with c hc
  have hsubRect : Square p c ⊆ Icc σ σ' ×ℂ univ := (square_subset_square hc.1 hc.2.le).trans hc'
  have hsub :
      Rectangle (-c - c * I + p) (c + c * I + p) \ {p} ⊆ stripMinusPole σ σ' p := by
    intro z hz
    refine ⟨?_, hz.2⟩
    exact hsubRect (by simpa [Square] using hz.1)
  exact hfStrip.mono hsub

theorem vertical_diff_eq_smallSquare_limit_of_spectralIntegrand
    {g : ℂ → ℂ} {σ σ' : ℝ} {p L : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hlim :
      Tendsto (smallSquareIntegral g p) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ = L := by
  let V : ℂ := VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ
  have hevent :
      ∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0), smallSquareIntegral g p c = V := by
    have hsmall := contour_shift_to_small_square_spectralIntegrand
      (g := g) hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight
    filter_upwards [hsmall] with c hc
    simpa [smallSquareIntegral, V] using hc.symm
  have heventEq :
      (smallSquareIntegral g p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ : ℝ => V) := hevent
  have hsmall_to_V :
      Tendsto (smallSquareIntegral g p) (nhdsWithin 0 (Set.Ioi 0)) (nhds V) := by
    exact tendsto_const_nhds.congr' heventEq.symm
  have hVL : V = L := tendsto_nhds_unique hsmall_to_V hlim
  simpa [V] using hVL

theorem vertical_diff_eq_smallSquare_limit_invSqKernel_of_gt_one
    {σ σ' : ℝ} {p L : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hσσ' : σ ≤ σ')
    (hσ : 1 < σ)
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hlim :
      Tendsto (smallSquareIntegral invSqKernel p) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    VerticalIntegral (spectralIntegrand invSqKernel) σ' -
      VerticalIntegral (spectralIntegrand invSqKernel) σ = L := by
  have hgStrip : HolomorphicOn invSqKernel (stripMinusPole σ σ' p) := by
    have hNoNegOne : (-(1 : ℂ)) ∉ stripMinusPole σ σ' p := by
      intro hneg
      rcases hneg with ⟨hmem, _⟩
      have hσle : σ ≤ (-(1 : ℂ)).re := hmem.1.1
      norm_num at hσle
      linarith
    exact invSqKernel_holoOn hNoNegOne
  have hDecay : HorizontalDecay invSqKernel σ σ' :=
    horizontalDecay_of_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσ
  have hLeft :
      Integrable (fun y : ℝ => spectralIntegrand invSqKernel (↑σ + ↑y * I)) volume :=
    (integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσ).1
  have hRight :
      Integrable (fun y : ℝ => spectralIntegrand invSqKernel (↑σ' + ↑y * I)) volume :=
    (integrable_left_right_spectralIntegrand_invSqKernel_of_gt_one hσσ' hσ).2
  exact vertical_diff_eq_smallSquare_limit_of_spectralIntegrand
    (g := invSqKernel) hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hlim

theorem vertical_diff_eq_two_pi_I_mul_of_simplePole
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hHolo : ∀ c : ℝ, 0 < c →
      HolomorphicOn (spectralIntegrand g)
        (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ)) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ =
      (2 * (Real.pi : ℂ) * I) * A := by
  exact vertical_diff_eq_smallSquare_limit_of_spectralIntegrand
    (g := g) hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight
    (smallSquareIntegral_tendsto_two_pi_I_mul_of_simplePole
      (g := g) (p := p) (A := A) hHolo hNear)

theorem vertical_diff_eq_two_pi_I_mul_of_simplePole_of_strip
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ)) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ =
      (2 * (Real.pi : ℂ) * I) * A := by
  have hSpecStrip :
      HolomorphicOn (spectralIntegrand g) (stripMinusPole σ σ' p) :=
    spectralIntegrand_holoOn_stripMinusPole_of_nonzero hOneStrip hNonzeroStrip hgStrip
  have hHolo :
      ∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0),
        HolomorphicOn (spectralIntegrand g)
          (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}) :=
    eventually_holoOn_smallSquare_of_holoOn_stripMinusPole (f := spectralIntegrand g) hσp hSpecStrip
  exact vertical_diff_eq_smallSquare_limit_of_spectralIntegrand
    (g := g) hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight
    (smallSquareIntegral_tendsto_two_pi_I_mul_of_simplePole_eventually
      (g := g) (p := p) (A := A) hHolo hNear)

theorem vertical_diff_ne_zero_of_simplePole
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hHolo : ∀ c : ℝ, 0 < c →
      HolomorphicOn (spectralIntegrand g)
        (Rectangle (-c - c * I + p) (c + c * I + p) \ {p}))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ))
    (hA : A ≠ 0) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ ≠ 0 := by
  rw [vertical_diff_eq_two_pi_I_mul_of_simplePole
    (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hHolo hNear]
  exact mul_ne_zero (by simp) hA

theorem vertical_diff_ne_zero_of_simplePole_of_strip
    {g : ℂ → ℂ} {σ σ' : ℝ} {p A : ℂ}
    (hσp : σ < p.re ∧ p.re < σ')
    (hOneStrip : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzeroStrip : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hgStrip : HolomorphicOn g (stripMinusPole σ σ' p))
    (hDecay : HorizontalDecay g σ σ')
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I))
    (hNear :
      (spectralIntegrand g - (fun s : ℂ => A / (s - p))) =O[nhdsWithin p {p}ᶜ]
        (1 : ℂ → ℂ))
    (hA : A ≠ 0) :
    VerticalIntegral (spectralIntegrand g) σ' - VerticalIntegral (spectralIntegrand g) σ ≠ 0 := by
  rw [vertical_diff_eq_two_pi_I_mul_of_simplePole_of_strip
    (g := g) (σ := σ) (σ' := σ') (p := p) (A := A)
    hσp hOneStrip hNonzeroStrip hgStrip hDecay hLeft hRight hNear]
  exact mul_ne_zero (by simp) hA

end MellinOrthogonality
