import Collatz.MellinOrthogonality.Step5
import PrimeNumberTheoremAnd.ZetaBounds

open Complex Filter MeasureTheory Set

namespace MellinOrthogonality

/-- Upper strip used for top-tail contour control. -/
def upperStrip (σ σ' T : ℝ) : Set ℂ :=
  {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ T ≤ z.im}

/-- Lower strip used for bottom-tail contour control. -/
def lowerStrip (σ σ' T : ℝ) : Set ℂ :=
  {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ -T}

/-- Full vertical strip, punctured at the pole/zero location `p`. -/
def stripMinusPole (σ σ' : ℝ) (p : ℂ) : Set ℂ :=
  (Icc σ σ' ×ℂ univ) \ {p}

/-- The zeta log-derivative integrand core. -/
noncomputable def zetaLogDeriv (s : ℂ) : ℂ :=
  deriv riemannZeta s / riemannZeta s

/-- Candidate Mellin integrand for contour-shift arguments. -/
noncomputable def spectralIntegrand (g : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaLogDeriv s * g s

/-- Concrete holomorphic test kernel used for horizontal-tail decay goals. -/
noncomputable def invSqKernel (s : ℂ) : ℂ :=
  (s + 1)⁻¹ ^ (2 : ℕ)

theorem one_not_mem_upperStrip_of_pos {σ σ' T : ℝ} (hT : 0 < T) :
    (1 : ℂ) ∉ upperStrip σ σ' T := by
  intro h
  have hTi : T ≤ (1 : ℂ).im := h.2.2
  norm_num at hTi
  linarith

theorem one_not_mem_lowerStrip_of_pos {σ σ' T : ℝ} (hT : 0 < T) :
    (1 : ℂ) ∉ lowerStrip σ σ' T := by
  intro h
  have hTi : (1 : ℂ).im ≤ -T := h.2.2
  norm_num at hTi
  linarith

theorem neg_one_not_mem_upperStrip_of_one_lt_left {σ σ' T : ℝ} (hσ : 1 < σ) :
    (-(1 : ℂ)) ∉ upperStrip σ σ' T := by
  intro h
  have hre : σ ≤ (-(1 : ℂ)).re := h.1
  norm_num at hre
  linarith

theorem neg_one_not_mem_lowerStrip_of_one_lt_left {σ σ' T : ℝ} (hσ : 1 < σ) :
    (-(1 : ℂ)) ∉ lowerStrip σ σ' T := by
  intro h
  have hre : σ ≤ (-(1 : ℂ)).re := h.1
  norm_num at hre
  linarith

theorem zeta_nonzero_on_upperStrip_of_one_le {σ σ' T : ℝ} (hσ : 1 ≤ σ) :
    ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0 := by
  intro s hs
  exact riemannZeta_ne_zero_of_one_le_re (le_trans hσ hs.1)

theorem zeta_nonzero_on_lowerStrip_of_one_le {σ σ' T : ℝ} (hσ : 1 ≤ σ) :
    ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0 := by
  intro s hs
  exact riemannZeta_ne_zero_of_one_le_re (le_trans hσ hs.1)

theorem zetaLogDeriv_holoOn_of_nonzero {S : Set ℂ}
    (hOne : (1 : ℂ) ∉ S)
    (hNonzero : ∀ s ∈ S, riemannZeta s ≠ 0) :
    HolomorphicOn zetaLogDeriv S := by
  simpa [zetaLogDeriv] using LogDerivZetaHoloOn (S := S) hOne hNonzero

theorem spectralIntegrand_holoOn_of_nonzero {S : Set ℂ} {g : ℂ → ℂ}
    (hOne : (1 : ℂ) ∉ S)
    (hNonzero : ∀ s ∈ S, riemannZeta s ≠ 0)
    (hg : HolomorphicOn g S) :
    HolomorphicOn (spectralIntegrand g) S := by
  simpa [spectralIntegrand] using (zetaLogDeriv_holoOn_of_nonzero hOne hNonzero).mul hg

theorem invSqKernel_holoOn {S : Set ℂ} (hNoNegOne : (-(1 : ℂ)) ∉ S) :
    HolomorphicOn invSqKernel S := by
  have hLinear : HolomorphicOn (fun s : ℂ => s + 1) S := by
    exact Differentiable.differentiableOn (Differentiable.add_const (c := (1 : ℂ)) differentiable_fun_id)
  have hInv : HolomorphicOn (fun s : ℂ => (s + 1)⁻¹) S := by
    refine DifferentiableOn.inv hLinear ?_
    intro s hs hzero
    have hsEq : s = -(1 : ℂ) := by
      exact eq_neg_iff_add_eq_zero.mpr hzero
    exact hNoNegOne (hsEq ▸ hs)
  simpa [invSqKernel] using hInv.pow 2

/-- Direct wrapper of PNT+'s large-`|t|` log-derivative strip bound. -/
theorem zetaLogDeriv_bound_unif :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C),
      ∀ (σ : ℝ) (t : ℝ), 3 < |t| →
        σ ∈ Ici (1 - A / Real.log |t| ^ 9) →
        ‖zetaLogDeriv (σ + t * I)‖ ≤ C * Real.log |t| ^ 9 := by
  obtain ⟨A, hA, C, hC, hbound⟩ := LogDerivZetaBndUnif
  refine ⟨A, hA, C, hC, ?_⟩
  intro σ t ht hσ
  simpa [zetaLogDeriv] using hbound σ t ht hσ

/-- Fixed-vertical-line bound from PNT+ on `Re(s) > 1`. -/
theorem zetaLogDeriv_bound_on_vertical_ge_one
    {σ x t : ℝ} (hσ : 1 < σ) (hσx : σ ≤ x) :
    ‖zetaLogDeriv (x + t * I)‖ ≤ ‖zetaLogDeriv σ‖ := by
  have h :=
    dlog_riemannZeta_bdd_on_vertical_lines_generalized σ x t hσ hσx
  simpa [zetaLogDeriv, Complex.norm_div, norm_neg] using h

theorem invSqKernel_norm_le_one_div_one_add_sq
    {x y : ℝ} (hx : 0 ≤ x) :
    ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2) := by
  let z : ℂ := (↑x + ↑y * I) + 1
  have hz_nonzero : z ≠ 0 := by
    have hre : z.re = x + 1 := by simp [z]
    intro hz
    have : z.re = 0 := by simp [hz]
    linarith [hre]
  have hz_sq : (1 + y ^ 2) ≤ Complex.normSq z := by
    calc
      1 + y ^ 2 ≤ (x + 1) ^ 2 + y ^ 2 := by nlinarith [hx]
      _ = Complex.normSq z := by
        simp [z, Complex.normSq_apply, pow_two, add_assoc, add_comm, mul_comm]
  have hz_norm_sq : (1 + y ^ 2) ≤ ‖z‖ ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using hz_sq
  have hden_pos : 0 < 1 + y ^ 2 := by positivity
  have hinv : 1 / (‖z‖ ^ 2) ≤ 1 / (1 + y ^ 2) :=
    one_div_le_one_div_of_le hden_pos hz_norm_sq
  have hnorm : ‖invSqKernel (↑x + ↑y * I)‖ = 1 / (‖z‖ ^ 2) := by
    simp [invSqKernel, z]
  exact hnorm.trans_le hinv

theorem invSqKernel_bound_on_uIoc_of_nonneg_left
    {σ σ' y : ℝ} (hσσ' : σ ≤ σ') (hσ0 : 0 ≤ σ) :
    ∀ x : ℝ, x ∈ Set.uIoc σ σ' →
      ‖invSqKernel (↑x + ↑y * I)‖ ≤ 1 / (1 + y ^ 2) := by
  intro x hx
  have hxIoc : x ∈ Set.Ioc σ σ' := by
    simpa [Set.uIoc_of_le hσσ'] using hx
  exact invSqKernel_norm_le_one_div_one_add_sq (le_trans hσ0 (le_of_lt hxIoc.1))

/-- Holomorphy of the zeta log-derivative on a punctured strip. -/
theorem zetaLogDeriv_holoOn_stripMinusPole_of_nonzero
    {σ σ' : ℝ} {p : ℂ}
    (hOne : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzero : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0) :
    HolomorphicOn zetaLogDeriv (stripMinusPole σ σ' p) :=
  zetaLogDeriv_holoOn_of_nonzero hOne hNonzero

/-- Holomorphy of the full contour integrand on a punctured strip. -/
theorem spectralIntegrand_holoOn_stripMinusPole_of_nonzero
    {g : ℂ → ℂ} {σ σ' : ℝ} {p : ℂ}
    (hOne : (1 : ℂ) ∉ stripMinusPole σ σ' p)
    (hNonzero : ∀ s ∈ stripMinusPole σ σ' p, riemannZeta s ≠ 0)
    (hg : HolomorphicOn g (stripMinusPole σ σ' p)) :
    HolomorphicOn (spectralIntegrand g) (stripMinusPole σ σ' p) :=
  spectralIntegrand_holoOn_of_nonzero hOne hNonzero hg

/-- Build Step-5 contour assumptions for the concrete integrand, from explicit
holomorphy/nonvanishing/decay hypotheses. -/
theorem step5Context_of_spectralIntegrand
    {g : ℂ → ℂ} {σ σ' T : ℝ}
    (hσ : σ ≤ σ')
    (hOneUpper : (1 : ℂ) ∉ upperStrip σ σ' T)
    (hOneLower : (1 : ℂ) ∉ lowerStrip σ σ' T)
    (hNonzeroUpper : ∀ s ∈ upperStrip σ σ' T, riemannZeta s ≠ 0)
    (hNonzeroLower : ∀ s ∈ lowerStrip σ σ' T, riemannZeta s ≠ 0)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop : Tendsto (fun y : ℝ =>
      ∫ x : ℝ in σ..σ', spectralIntegrand g (↑x + ↑y * I)) atTop (nhds 0))
    (hBot : Tendsto (fun y : ℝ =>
      ∫ x : ℝ in σ..σ', spectralIntegrand g (↑x + ↑y * I)) atBot (nhds 0))
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)) :
    Step5Context (spectralIntegrand g) σ σ' T := by
  refine ⟨hσ, ?_, ?_, hTop, hBot, hLeft, hRight⟩
  · simpa [upperStrip] using
      (spectralIntegrand_holoOn_of_nonzero (S := upperStrip σ σ' T) hOneUpper hNonzeroUpper hgUpper)
  · simpa [lowerStrip] using
      (spectralIntegrand_holoOn_of_nonzero (S := lowerStrip σ σ' T) hOneLower hNonzeroLower hgLower)

/-- Convenience constructor when the strip sits in `Re(s) ≥ 1` and `T > 0`,
so the `1`-exclusion and zeta nonvanishing obligations are automatic. -/
theorem step5Context_of_spectralIntegrand_of_ge_one
    {g : ℂ → ℂ} {σ σ' T : ℝ}
    (hσ : σ ≤ σ')
    (hσ_ge_one : 1 ≤ σ)
    (hT : 0 < T)
    (hgUpper : HolomorphicOn g (upperStrip σ σ' T))
    (hgLower : HolomorphicOn g (lowerStrip σ σ' T))
    (hTop : Tendsto (fun y : ℝ =>
      ∫ x : ℝ in σ..σ', spectralIntegrand g (↑x + ↑y * I)) atTop (nhds 0))
    (hBot : Tendsto (fun y : ℝ =>
      ∫ x : ℝ in σ..σ', spectralIntegrand g (↑x + ↑y * I)) atBot (nhds 0))
    (hLeft : Integrable fun y : ℝ => spectralIntegrand g (↑σ + ↑y * I))
    (hRight : Integrable fun y : ℝ => spectralIntegrand g (↑σ' + ↑y * I)) :
    Step5Context (spectralIntegrand g) σ σ' T :=
  step5Context_of_spectralIntegrand hσ
    (one_not_mem_upperStrip_of_pos hT)
    (one_not_mem_lowerStrip_of_pos hT)
    (zeta_nonzero_on_upperStrip_of_one_le hσ_ge_one)
    (zeta_nonzero_on_lowerStrip_of_one_le hσ_ge_one)
    hgUpper hgLower hTop hBot hLeft hRight

end MellinOrthogonality
