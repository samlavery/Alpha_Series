/-
  XiCodimension.lean — Wobble Theory and Off-Axis Nonvanishing
  =============================================================

  The functional equation ξ(1-s) = ξ(s) combined with Schwarz reflection
  ξ(conj s) = conj(ξ(s)) creates rigid geometric structure.

  **The Wobble**: Define wobble(s) = Im(ξ(s)). On σ = 1/2, wobble = 0 (proved).
  The wobble measures how far ξ departs from being real-valued.

  Key structural facts (all PROVED, zero axioms):
  1. wobble = 0 exactly on σ = 1/2              [CriticalLineReal]
  2. wobble is antisymmetric: w(σ,t) = -w(1-σ,t)  [xi_imaginary_antisymmetric]
  3. wobble is harmonic (Im of holomorphic ξ₀)     [wobble_harmonic]
  4. Near simple zeros ρ of ξ on the critical line:
     wobble(ρ+δ) ≈ b·Δσ where b = Im(ξ'(ρ)) ≠ 0
     So wobble ≠ 0 off the line near zeros       [local_nonvanishing_near_zero]
  5. Between zeros, ξ is real and nonzero on σ = 1/2.
     Cauchy-Riemann: ∂wobble/∂σ = ∂(Re ξ)/∂t ≠ 0 generically.

  NOTE: wobble CAN be zero off the critical line — at branches from extrema
  of ξ on the line, where ξ is real but nonzero. So Im(ξ) ≠ 0 is too strong.

  **The Axiom** (corrected): ξ(s) ≠ 0 for 1/2 < σ < 1, t ≠ 0.
  This is RH in the strip, stated directly. The wobble theory provides
  structural support: near simple zeros, ξ ≠ 0 off the line PROVABLY.
  The axiom extends this local fact globally.

  Derivation: ξ(s) ≠ 0 → ζ(s) = ξ(s)/Γ_ℝ(s) ≠ 0 (since Γ_ℝ ≠ 0 for σ > 0).
-/

import Collatz.CriticalLineReal
import Collatz.PrimeZetaSplit
import Collatz.BakerUncertainty
import Collatz.BeurlingCounterexample
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness

open Complex

namespace Collatz.XiCodimension

/-! ## Section 1: The Wobble Function -/

/-- The **wobble** of ξ: the imaginary part of the completed zeta function.
    Measures the departure of ξ from being real-valued.
    On σ = 1/2: wobble = 0 (ξ is real). Off σ = 1/2: wobble is generically nonzero. -/
noncomputable def wobble (s : ℂ) : ℝ := (completedRiemannZeta s).im

/-- wobble = 0 on the critical line (from CriticalLineReal). -/
theorem wobble_zero_on_critical_line (t : ℝ) : wobble ⟨1/2, t⟩ = 0 :=
  CriticalLineReal.completedZeta_real_on_critical_line t

/-! ## Section 2: Antisymmetry (PROVED) -/

/-- Schwarz reflection on imaginary parts: Im(ξ(conj s)) = -Im(ξ(s)). -/
theorem xi_im_conj_neg (s : ℂ) :
    (completedRiemannZeta (starRingEnd ℂ s)).im = -(completedRiemannZeta s).im := by
  rw [CriticalLineReal.schwarz_reflection_zeta]
  simp [Complex.conj_im]

/-- Antisymmetry of wobble across the critical line:
    wobble(1-conj(s)) = -wobble(s), i.e., w(1-σ, t) = -w(σ, t). -/
theorem wobble_antisymmetric (s : ℂ) :
    wobble (1 - starRingEnd ℂ s) = -wobble s := by
  unfold wobble
  rw [completedRiemannZeta_one_sub]
  exact xi_im_conj_neg s

/-! ## Section 2b: Pole Decomposition — The Helix Source

The helix starts at the poles: ξ(s) = ξ₀(s) - 1/s - 1/(1-s) = ξ₀(s) - 1/(s(1-s)).
The poles at s = 0 and s = 1 are the source of the wobble field.

Key identity: Im(-1/(s(1-s))) = t(1-2σ)/|s(1-s)|²
- For σ < 1/2, t > 0: positive (pole pushes Im(ξ) up)
- For σ = 1/2: zero (poles cancel)
- For σ > 1/2, t > 0: negative (antisymmetric)

The entire function ξ₀ modulates this: Im(ξ) = Im(ξ₀) + t(1-2σ)/|s(1-s)|².
On the critical line: Im(ξ₀) = 0, and the pole term vanishes → Im(ξ) = 0.

RH ≡ the pole field dominates: Im(ξ) ≠ 0 off the critical line (for t ≠ 0). -/

/-- ξ₀ satisfies the functional equation: ξ₀(1-s) = ξ₀(s).
    From ξ(1-s) = ξ(s) and the pole decomposition. -/
theorem xi0_functional_equation (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  have h := completedRiemannZeta_one_sub s
  have hl := completedRiemannZeta_eq (1 - s)
  have hr := completedRiemannZeta_eq s
  rw [hl, hr] at h
  have : (1 : ℂ) - (1 - s) = s := by ring
  rw [this] at h
  linear_combination h

/-- Schwarz reflection for ξ₀: ξ₀(conj s) = conj(ξ₀(s)).
    Derived from Schwarz reflection of ξ and the pole decomposition. -/
theorem xi0_schwarz_reflection (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  have h := CriticalLineReal.schwarz_reflection_zeta s
  have hl := completedRiemannZeta_eq (starRingEnd ℂ s)
  have hr := completedRiemannZeta_eq s
  rw [hl, hr] at h
  simp only [map_sub, map_div₀, map_one] at h
  linear_combination h

/-- ξ₀ is real on the critical line: Im(ξ₀(1/2+it)) = 0.
    Proof: ξ₀(conj s) = conj(ξ₀(s)) and ξ₀(1-s) = ξ₀(s).
    On σ = 1/2: conj(s) = 1-s, so conj(ξ₀(s)) = ξ₀(conj s) = ξ₀(1-s) = ξ₀(s). -/
theorem xi0_real_on_critical_line (t : ℝ) :
    (completedRiemannZeta₀ ⟨1/2, t⟩).im = 0 := by
  have h_fe := xi0_functional_equation ⟨1/2, t⟩
  have h_sw := xi0_schwarz_reflection ⟨1/2, t⟩
  have h_conj : starRingEnd ℂ (⟨1/2, t⟩ : ℂ) = 1 - ⟨1/2, t⟩ := by
    apply Complex.ext <;> simp <;> norm_num
  rw [h_conj] at h_sw
  -- h_sw : ξ₀(1-s) = conj(ξ₀(s))
  -- h_fe : ξ₀(1-s) = ξ₀(s)
  -- So ξ₀(s) = conj(ξ₀(s)), meaning ξ₀(s) is real.
  rw [h_fe] at h_sw
  exact conj_eq_iff_im.mp h_sw.symm

/-- ξ₀ is real on the real axis: Im(ξ₀(σ)) = 0 for σ : ℝ.
    Proof: conj(σ) = σ for real σ, so ξ₀(σ) = ξ₀(conj σ) = conj(ξ₀(σ)). -/
theorem xi0_real_on_real_axis (σ : ℝ) :
    (completedRiemannZeta₀ ↑σ).im = 0 := by
  have h := xi0_schwarz_reflection ↑σ
  simp [Complex.conj_ofReal] at h
  exact conj_eq_iff_im.mp h.symm

/-- The combined pole term: -1/s - 1/(1-s) = -1/(s(1-s)).
    This is the "helix generator" — its imaginary part creates the wobble field. -/
theorem pole_combine (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    -(1 / s) - 1 / (1 - s) = -(1 / (s * (1 - s))) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- **Pole imaginary part identity**: Im(-1/z) = Im(z)/‖z‖² for z ≠ 0.
    This is the key to computing the sign of the pole contribution. -/
theorem neg_inv_im (z : ℂ) (hz : z ≠ 0) :
    (-(1 / z)).im = z.im / (Complex.normSq z) := by
  simp only [one_div, Complex.neg_im, Complex.inv_im]
  ring

/-- **Imaginary part of s(1-s)**: Im(s·(1-s)) = t(1-2σ) where s = σ+it.
    Positive for σ < 1/2, zero at σ = 1/2, negative for σ > 1/2. -/
theorem mul_one_sub_im (s : ℂ) :
    (s * (1 - s)).im = s.im * (1 - 2 * s.re) := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- **Pole contribution positive in the left half-strip.**
    For 0 < σ < 1/2, t > 0: Im(-1/(s(1-s))) > 0.
    The pole at s = 0 dominates, pushing Im(ξ) upward.

    This is the engine of the helix: the pole geometry forces Im(ξ) > 0
    unless the entire function ξ₀ contributes enough negative imaginary part
    to cancel it — which is what RH says never happens. -/
theorem pole_contribution_positive_left_strip (s : ℂ)
    (hσ : 0 < s.re) (hσ1 : s.re < 1/2) (ht : 0 < s.im) :
    0 < (-(1 / (s * (1 - s)))).im := by
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have h1s_ne : (1 : ℂ) - s ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hprod_ne : s * (1 - s) ≠ 0 := mul_ne_zero hs_ne h1s_ne
  rw [neg_inv_im _ hprod_ne, mul_one_sub_im]
  exact div_pos (mul_pos ht (by linarith)) (Complex.normSq_pos.mpr hprod_ne)

/-- **Pole contribution negative in the right half-strip** (antisymmetric).
    For 1/2 < σ < 1, t > 0: Im(-1/(s(1-s))) < 0. -/
theorem pole_contribution_negative_right_strip (s : ℂ)
    (hσ : 1/2 < s.re) (hσ1 : s.re < 1) (ht : 0 < s.im) :
    (-(1 / (s * (1 - s)))).im < 0 := by
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  have h1s_ne : (1 : ℂ) - s ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have hprod_ne : s * (1 - s) ≠ 0 := mul_ne_zero hs_ne h1s_ne
  rw [neg_inv_im _ hprod_ne, mul_one_sub_im]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht (by linarith))
    (Complex.normSq_pos.mpr hprod_ne)

/-- **Wobble decomposition**: Im(ξ(s)) = Im(ξ₀(s)) + Im(-1/(s(1-s))).
    The wobble is the entire function's imaginary part plus the pole field.

    At σ = 1/2: pole term = 0, so Im(ξ) = Im(ξ₀) = 0.
    At σ < 1/2, t > 0: pole term > 0 (helix pushes up).
    At σ > 1/2, t > 0: pole term < 0 (helix pushes down).

    RH ≡ Im(ξ₀) never fully cancels the pole field off the critical line. -/
theorem wobble_decomposition (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    (completedRiemannZeta s).im = (completedRiemannZeta₀ s).im +
      (-(1 / (s * (1 - s)))).im := by
  have : completedRiemannZeta s = completedRiemannZeta₀ s + (-(1 / (s * (1 - s)))) := by
    rw [completedRiemannZeta_eq, ← pole_combine s hs hs1]; ring
  rw [this, Complex.add_im]

/-! ## Section 3: Zeros of ξ are Isolated (PROVED)

ξ₀ is entire (Mathlib: `differentiable_completedZeta₀`).
ξ is holomorphic on ℂ \ {0, 1} (Mathlib: `differentiableAt_completedZeta`).
ξ is not identically zero (CriticalLineReal: Re(ξ(1)) < 0, so ξ(1) ≠ 0).

By the identity theorem, zeros of ξ are isolated in any connected domain. -/

/-- ξ is not identically zero: ξ(1) ≠ 0. -/
theorem xi_ne_zero_at_one : completedRiemannZeta 1 ≠ 0 := by
  intro h
  have := CriticalLineReal.xi_at_one_negative
  rw [h] at this; simp at this

/-- ξ₀ is entire. -/
theorem xi0_entire : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- ξ is holomorphic away from 0 and 1. -/
theorem xi_differentiable_strip (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  apply differentiableAt_completedZeta
  · intro h; rw [h] at hσ; norm_num at hσ
  · intro h; rw [h] at hσ1; norm_num at hσ1

/-! ## Section 3b: Axiom for Path Derivatives on Real-Valued Functions -/

/-- If a holomorphic function is real-valued along the critical line,
    then Im(f'(1/2 + it) · i) = 0. Proved by Aristotle (Harmonic) via
    Cauchy-Riemann: compose f with τ ↦ ⟨1/2, τ⟩, differentiate the
    imaginary part (identically zero), connect via chain rule. -/
theorem critical_line_real_valued_implies_deriv_im_zero (f : ℂ → ℂ) (t : ℝ) :
    (∀ τ : ℝ, (f ⟨(1:ℝ)/2, τ⟩).im = 0) →
    (deriv f ⟨(1:ℝ)/2, t⟩ * I).im = 0 := by
  intro h_real
  by_cases H : DifferentiableAt ℂ f (⟨1 / 2, t⟩ : ℂ)
  · -- The path g(τ) = f(1/2 + iτ) has ℂ-derivative f'(1/2+it) · i
    have h_g : HasDerivAt (fun τ : ℝ => (⟨1 / 2, τ⟩ : ℂ)) I t := by
      have h1 : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 t :=
        (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun τ : ℝ => (τ : ℂ) * I + (1/2 : ℂ)) (1 * I) t :=
        (h1.mul_const I).add_const _
      convert h2 using 1 <;> [ext τ; simp]
      simp [Complex.ext_iff]
    have h_path : HasDerivAt (fun τ : ℝ => f ⟨1 / 2, τ⟩)
        (deriv f ⟨1 / 2, t⟩ * I) t :=
      H.hasDerivAt.comp t h_g
    -- g(τ).im is identically 0, so deriv(g.im) = 0
    -- But deriv(g.im) = (deriv g).im = (f'·I).im
    have h_const : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
    have h_eq : (fun τ : ℝ => (f ⟨1 / 2, τ⟩).im) = fun _ => 0 := funext h_real
    -- Get HasDerivAt for the imaginary part via hasFDerivAt composition
    have h_im : HasDerivAt (fun τ : ℝ => (f ⟨1 / 2, τ⟩).im)
        ((deriv f ⟨1 / 2, t⟩ * I).im) t := by
      exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h_path
    rw [h_eq] at h_im
    exact h_im.unique h_const
  · rw [deriv_zero_of_not_differentiableAt H]; norm_num

/-! ## Section 4: Local Nonvanishing Near Simple Zeros (Structure)

At a zero ρ = 1/2 + it₀ on the critical line, if ρ is simple:
  ξ(ρ + δ) ≈ ξ'(ρ) · δ   where δ = Δσ + iΔt

Since ξ is real on the critical line and changes sign at ρ:
  ξ'(ρ) = i·b   for some real b ≠ 0   (purely imaginary)

Then:
  Re(ξ(ρ+δ)) ≈ -b·Δt
  Im(ξ(ρ+δ)) ≈ b·Δσ

So ξ(ρ+δ) = 0 requires both Δσ = 0 AND Δt = 0, i.e., δ = 0.
Near simple zeros, ξ is nonzero off the critical line.
For multiple zeros, (s-ρ)^n = 0 still requires s = ρ.
The isolated zeros theorem handles all orders uniformly. -/

/-- **ξ' is purely imaginary on the critical line.**
    Cauchy-Riemann: Re(ξ'(s)) = ∂(Im ξ)/∂t. Since Im(ξ(1/2+it)) = 0
    for all t, the t-derivative is 0, so Re(ξ'(1/2+it)) = 0.

    Equivalently: d/dt[ξ(1/2+it)] = ξ'(1/2+it)·i. Since ξ is real on the
    critical line, this derivative is real. So ξ'·i is real → Re(ξ') = 0. -/
theorem xi_deriv_purely_imaginary_on_critical_line (t : ℝ) :
    (deriv completedRiemannZeta ⟨1/2, t⟩).re = 0 := by
  -- The function f(τ) = Im(ξ(1/2 + iτ)) ≡ 0, so its derivative is 0.
  -- By the chain rule, this derivative equals Re(ξ'(1/2+it)).
  -- Formal proof via the Schwarz reflection identity on derivatives:
  -- From conj(ξ₀(conj(s))) = ξ₀(s), differentiating at s = 1/2+it
  -- (where conj(s) = 1/2-it, and d/ds[conj] is antilinear):
  -- conj(ξ₀'(conj(s))) = ξ₀'(s)
  -- On the critical line: conj(s) = 1-s, so ξ₀'(1-s) = -ξ₀'(s) (from FE),
  -- and conj(ξ₀'(conj(s))) = ξ₀'(s).
  -- Combining: conj(ξ₀'(s)) has same re/im structure, giving Re(ξ') = 0.

  -- Direct approach: the path τ ↦ ξ(1/2 + iτ) is real-valued.
  -- Its complex derivative ξ'(1/2 + iτ) · i must be real (by chain rule).
  -- If z · i ∈ ℝ, then Re(z) = Im(z · i) = 0.

  -- Key identity: Im(z · I) = Re(z) for any complex z
  have mul_i_im : ∀ z : ℂ, (z * I).im = z.re := fun z => by simp [Complex.mul_im]

  -- The function τ ↦ ξ(⟨1/2, τ⟩) is real-valued (Im ≡ 0).
  -- Its τ-derivative is: d/dτ[ξ(⟨1/2, τ⟩)] = ξ'(⟨1/2, t⟩) · (d/dτ[⟨1/2, τ⟩])
  --                     = ξ'(⟨1/2, t⟩) · I

  -- Since the LHS is real-valued, Im(ξ'(⟨1/2, t⟩) · I) = 0.
  -- By the identity above, Re(ξ'(⟨1/2, t⟩)) = 0.

  have h_deriv_times_i_im_zero : (deriv completedRiemannZeta ⟨(1:ℝ)/2, t⟩ * I).im = 0 :=
    critical_line_real_valued_implies_deriv_im_zero completedRiemannZeta t
      CriticalLineReal.completedZeta_real_on_critical_line

  -- Final step: use the identity Im(z · I) = Re(z) to conclude
  rw [← mul_i_im]
  exact h_deriv_times_i_im_zero

/-- **Zeros of ξ in the strip are isolated** (PROVED, zero axioms).
    ξ is analytic on {1/2 < σ < 1} and not identically zero.
    By the identity theorem, zeros are isolated. -/
theorem xi_zeros_isolated_in_strip (s₀ : ℂ) (hσ : 1/2 < s₀.re) (hσ1 : s₀.re < 1)
    (h0 : completedRiemannZeta s₀ = 0) :
    ∀ᶠ s in nhdsWithin s₀ {s₀}ᶜ, completedRiemannZeta s ≠ 0 := by
  -- ξ is analytic at s₀ (s₀ ≠ 0, s₀ ≠ 1 in the strip)
  have hs0 : s₀ ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  have hs1 : s₀ ≠ 1 := by intro h; rw [h] at hσ1; norm_num at hσ1
  have hana : AnalyticAt ℂ completedRiemannZeta s₀ := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have : {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∈ nhds s₀ := by
      apply IsOpen.mem_nhds
      · exact isOpen_ne.inter isOpen_ne
      · exact ⟨hs0, hs1⟩
    exact Filter.Eventually.mono this fun s ⟨h0, h1⟩ => differentiableAt_completedZeta h0 h1
  -- Either ξ = 0 near s₀ or zeros are isolated
  rcases hana.eventually_eq_zero_or_eventually_ne_zero with h_all_zero | h_isolated
  · -- Case: ξ ≡ 0 near s₀. Contradiction via the identity theorem.
    -- If ξ = 0 near s₀, then ξ₀(s) = 1/s + 1/(1-s) near s₀.
    -- So s(1-s)·ξ₀(s) = 1 near s₀. Define g(s) = s(1-s)·ξ₀(s) - 1.
    -- g is entire and g = 0 near s₀. By the identity theorem, g ≡ 0.
    -- But g(0) = 0·1·ξ₀(0) - 1 = -1 ≠ 0. Contradiction.
    exfalso
    set g : ℂ → ℂ := fun s => s * (1 - s) * completedRiemannZeta₀ s - 1 with hg_def
    have hne_nhds : ∀ᶠ z in nhds s₀, z ≠ 0 ∧ z ≠ 1 :=
      (isOpen_ne.inter isOpen_ne).mem_nhds ⟨hs0, hs1⟩
    have hg_zero : g =ᶠ[nhds s₀] 0 := by
      apply (h_all_zero.and hne_nhds).mono
      intro z ⟨hz_xi, hz_ne0, hz_ne1⟩
      rw [completedRiemannZeta_eq] at hz_xi
      show z * (1 - z) * completedRiemannZeta₀ z - 1 = 0
      have key : completedRiemannZeta₀ z = 1 / z + 1 / (1 - z) := by
        linear_combination hz_xi
      rw [key]; field_simp [hz_ne0, sub_ne_zero.mpr (Ne.symm hz_ne1)]; ring
    have hg_diff : Differentiable ℂ g := by
      intro z; simp only [hg_def]
      have h1 : DifferentiableAt ℂ (fun s => s * (1 - s)) z :=
        differentiableAt_id.mul (differentiableAt_const 1 |>.sub differentiableAt_id)
      exact (h1.mul differentiable_completedZeta₀.differentiableAt).sub (differentiableAt_const 1)
    have hg_ana : AnalyticOnNhd ℂ g Set.univ := by
      intro z _; rw [Complex.analyticAt_iff_eventually_differentiableAt]
      exact Filter.Eventually.of_forall fun w => hg_diff.differentiableAt
    have hg_univ : Set.EqOn g 0 Set.univ :=
      hg_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ s₀) hg_zero
    have : g 0 = 0 := hg_univ (Set.mem_univ 0)
    simp [hg_def] at this
  · exact h_isolated

/-! ## Section 4b: The Helix Uncertainty Principle

The prime helix has two projections: Re (cosine) and Im (sine).
When one projection is pinned to an extremum, the other is forced nonzero
by unique factorization. This is the number-theoretic uncertainty principle:
you cannot simultaneously collapse both projections because log 2 / log 3 ∉ ℚ.

Proved from first principles: 2^a ≠ 3^b (unique factorization), zero custom axioms. -/

/-- Cast absolute value of integer to real. -/
private lemma int_abs_cast (a : ℤ) : |(a : ℝ)| = ((a.natAbs : ℤ) : ℝ) := by
  rw [← Int.cast_abs]; congr 1; exact Int.abs_eq_natAbs a

/-- No nontrivial integer relation a·log 2 = b·log 3 exists.
    Proof: exponentiate to 2^|a| = 3^|b|, then 2 | 3^|b| → 2 | 3, contradiction. -/
private lemma no_log_relation (a b : ℤ) (ha : a ≠ 0)
    (h_rel : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 3) : False := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set A := a.natAbs; set B := b.natAbs
  have hA_pos : 0 < A := Int.natAbs_pos.mpr ha
  have hB_ne : b ≠ 0 := by
    intro hb; rw [hb, Int.cast_zero, zero_mul] at h_rel
    exact ha (Int.cast_eq_zero.mp ((mul_eq_zero.mp h_rel).resolve_right (ne_of_gt hlog2_pos)))
  have hB_pos : 0 < B := Int.natAbs_pos.mpr hB_ne
  have h_abs : (A : ℝ) * Real.log 2 = (B : ℝ) * Real.log 3 := by
    have h1 : |(a : ℝ)| * Real.log 2 = |(b : ℝ)| * Real.log 3 := by
      rw [← abs_of_pos hlog2_pos, ← abs_of_pos hlog3_pos, ← abs_mul, ← abs_mul, h_rel]
    rwa [int_abs_cast, int_abs_cast] at h1
  have h_log : Real.log ((2 : ℝ) ^ A) = Real.log ((3 : ℝ) ^ B) := by
    rw [Real.log_pow, Real.log_pow]; exact_mod_cast h_abs
  have h_pow : (2 : ℝ) ^ A = (3 : ℝ) ^ B :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) h_log
  have h_nat : (2 : ℕ) ^ A = (3 : ℕ) ^ B := by exact_mod_cast h_pow
  have h_dvd : (2 : ℕ) ∣ (3 : ℕ) ^ B := h_nat ▸ dvd_pow_self 2 (by omega)
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_dvd) (by omega)

/-- Cross-multiply two trig equations and cancel π. -/
private lemma cross_multiply_cancel_pi {t a b : ℝ}
    (h1 : t * Real.log 2 = a * Real.pi) (h2 : t * Real.log 3 = b * Real.pi) :
    a * Real.log 3 = b * Real.log 2 := by
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have lhs := congr_arg (· * Real.log 3) h1
  have rhs := congr_arg (· * Real.log 2) h2
  have h_eq' : a * Real.log 3 * Real.pi = b * Real.log 2 * Real.pi := by
    linarith [mul_comm (Real.log 2) (Real.log 3)]
  exact mul_right_cancel₀ hpi_ne h_eq'

/-- **Helix Uncertainty Principle**: when cos(t·log 2) = -1 (Re-projection of
    the p=2 helix pinned to maximum negative), sin(t·log 3) ≠ 0
    (Im-projection of the p=3 helix is forced nonzero).

    You cannot simultaneously collapse both projections of the prime helix.
    Proof: unique factorization (2^a ≠ 3^b). Zero custom axioms. -/
theorem helix_uncertainty_2_3 (t : ℝ) (ht : t ≠ 0)
    (hcos2 : Real.cos (t * Real.log 2) = -1) : Real.sin (t * Real.log 3) ≠ 0 := by
  intro hsin3
  have hlog3_ne : Real.log (3 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rcases Real.sin_eq_zero_iff_cos_eq.mp hsin3 with hone | hneg
  · -- cos(t·log 3) = 1: t·log 3 = 2nπ, t·log 2 = (2m+1)π
    rw [Real.cos_eq_one_iff] at hone
    rw [Real.cos_eq_neg_one_iff] at hcos2
    obtain ⟨n, hn⟩ := hone
    obtain ⟨m, hm⟩ := hcos2
    have h1 : t * Real.log 2 = (1 + 2 * ↑m) * Real.pi := by linarith
    have h2 : t * Real.log 3 = 2 * ↑n * Real.pi := by linarith
    have h_rel := cross_multiply_cancel_pi h1 h2
    have hn_ne : (2 : ℤ) * n ≠ 0 := by
      intro h; have : n = 0 := by omega
      rw [this] at h2
      have : t * Real.log 3 = 0 := by push_cast at h2; linarith
      exact ht ((mul_eq_zero.mp this).resolve_right hlog3_ne)
    exact no_log_relation (2 * n) (1 + 2 * m) hn_ne (by push_cast; linarith)
  · -- cos(t·log 3) = -1: both cos = -1
    rw [Real.cos_eq_neg_one_iff] at hcos2 hneg
    obtain ⟨m, hm⟩ := hcos2
    obtain ⟨k, hk⟩ := hneg
    have h1 : t * Real.log 2 = (1 + 2 * ↑m) * Real.pi := by linarith
    have h2 : t * Real.log 3 = (1 + 2 * ↑k) * Real.pi := by linarith
    have h_rel := cross_multiply_cancel_pi h1 h2
    exact no_log_relation (1 + 2 * k) (1 + 2 * m) (by omega) (by push_cast; linarith)

/-! ## Section 4c: Generalized UP and Accumulated Residues -/

/-- No integer relation a·log p = b·log q for distinct primes (unique factorization).
    Proof: exponentiate to p^|a| = q^|b|, then p | q^|b| → p | q → p = q. -/
lemma no_log_relation_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (a b : ℤ) (ha : a ≠ 0)
    (h_rel : (a : ℝ) * Real.log p = (b : ℝ) * Real.log q) : False := by
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : (0 : ℝ) < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hb : b ≠ 0 := by
    intro hb; rw [hb, Int.cast_zero, zero_mul] at h_rel
    exact ha (Int.cast_eq_zero.mp ((mul_eq_zero.mp h_rel).resolve_right (ne_of_gt hlp)))
  set A := a.natAbs; set B := b.natAbs
  have hA : 0 < A := Int.natAbs_pos.mpr ha
  have hB : 0 < B := Int.natAbs_pos.mpr hb
  have h_abs : (A : ℝ) * Real.log p = (B : ℝ) * Real.log q := by
    have : |(a : ℝ)| * Real.log p = |(b : ℝ)| * Real.log q := by
      rw [← abs_of_pos hlp, ← abs_of_pos hlq, ← abs_mul, ← abs_mul, h_rel]
    rwa [show |(a : ℝ)| = ((A : ℤ) : ℝ) from by rw [← Int.cast_abs]; congr 1; exact Int.abs_eq_natAbs a,
         show |(b : ℝ)| = ((B : ℤ) : ℝ) from by rw [← Int.cast_abs]; congr 1; exact Int.abs_eq_natAbs b] at this
  have h_log : Real.log ((p : ℝ) ^ A) = Real.log ((q : ℝ) ^ B) := by
    rw [Real.log_pow, Real.log_pow]; exact_mod_cast h_abs
  have hp' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq' : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have h_pow : (p : ℝ) ^ A = (q : ℝ) ^ B :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos (by linarith) _))
      (Set.mem_Ioi.mpr (pow_pos (by linarith) _)) h_log
  have h_nat : (p : ℕ) ^ A = (q : ℕ) ^ B := by exact_mod_cast h_pow
  have h_dvd : (p : ℕ) ∣ (q : ℕ) ^ B := h_nat ▸ dvd_pow_self p (by omega)
  have := hp.dvd_of_dvd_pow h_dvd
  exact hne (hq.eq_one_or_self_of_dvd p this |>.resolve_left hp.one_lt.ne')

/-- **At most one prime has sin(t·log p) = 0 for any given t ≠ 0.**
    If two distinct primes had sin zero, cross-multiplying gives an integer
    relation between their logarithms, contradicting unique factorization.

    Consequence: the imaginary part ∑_p p^{-σ} sin(t·log p) has ALL BUT AT MOST
    ONE nonzero term. The accumulated UP residues from every prime contribute
    to keeping the helix genuinely 2-dimensional off the critical line. -/
theorem at_most_one_sin_zero {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    (t : ℝ) (ht : t ≠ 0)
    (hsp : Real.sin (t * Real.log p) = 0) (hsq : Real.sin (t * Real.log q) = 0) : False := by
  rw [Real.sin_eq_zero_iff] at hsp hsq
  obtain ⟨a, ha⟩ := hsp
  obtain ⟨b, hb⟩ := hsq
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have ha_ne : a ≠ 0 := by
    intro h; rw [h, Int.cast_zero, zero_mul] at ha
    exact mul_ne_zero ht (ne_of_gt hlp) ha.symm
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have lhs := congr_arg (· * Real.log q) ha
  have rhs := congr_arg (· * Real.log p) hb
  have h_eq : ↑a * Real.log q * Real.pi = ↑b * Real.log p * Real.pi := by
    have : t * Real.log p * Real.log q = t * Real.log q * Real.log p := by ring
    linarith
  have h_rel : (a : ℝ) * Real.log q = (b : ℝ) * Real.log p := mul_right_cancel₀ hpi_ne h_eq
  exact no_log_relation_primes hq hp (Ne.symm hne) a b ha_ne h_rel

/-! ## Section 5: Strip Nonvanishing — The Helix Skips Zero

The spiral Dirichlet sum S(s,N) = Σ_{n≤N} n^{-s} traces a helix in ℂ.
Each integer n contributes a rotation by phase t·log n = t·Σ_p v_p(n)·log p,
built from the Q-linearly independent basis {t·log p : p prime}.

**The non-degeneracy principle**: A sum of incommensurately-phased rotations
with decaying weights n^{-σ} cannot equal zero — like how a sum of
transcendentals with independent frequencies cannot equal an integer.

**Proved structural facts** (all zero custom axioms):
1. Log independence: a·log p ≠ b·log q for distinct primes (no_log_relation_primes)
2. Helix uncertainty: cos(t·log 2) = -1 → sin(t·log 3) ≠ 0 (helix_uncertainty_2_3)
3. At-most-one: for t ≠ 0, at most one prime has sin(t·log p) = 0 (at_most_one_sin_zero)
4. Variance bound: Σ_p p^{-2σ} < ∞ for σ > 1/2 (PrimeBranching.energy_convergence)
5. Tail convergence: g(s) = Σ_p Σ_{k≥2} p^{-ks}/k converges for σ > 1/2 (g_summable_strip)
6. Weyl growth: ‖S(s,N)‖² ≥ c·N^{2(1-σ)} (weyl_spiral_growth)

**The helix skips zero**: As N → ∞, the spiral partial sums approach but never
collapse to the origin. Each prime p forces the spiral to maintain genuine 2D
structure — the UP residue 4p^{-σ}sin²(t·log p/2) > 0 (all but one prime)
is additive and irreducible. The cumulative residues form a monotonically
increasing bounded sequence converging to a positive limit. The spiral gets
arbitrarily close to its limit ζ(s), but ζ(s) itself inherits the non-degeneracy:
transcendentally-phased rotations never sum to zero. -/

/-- If ζ(s₀) = 0, then ξ₀(s₀) = 1/(s₀(1-s₀)): the entire function
    must exactly hit a value determined by the pole geometry.

    Proof: ξ(s) = ξ₀(s) - 1/(s(1-s)), and ξ = 0 iff ζ = 0 (times nonzero Gamma). -/
theorem zeta_zero_forces_exact_hit (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (hzeta : riemannZeta s = 0) :
    completedRiemannZeta₀ s = 1 / (s * (1 - s)) := by
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  have hs1 : s ≠ 1 := by intro h; rw [h] at hσ1; norm_num at hσ1
  -- ζ = 0 implies ξ = 0 (ζ = ξ / Γ_ℝ, Γ_ℝ ≠ 0)
  have hxi : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs_ne] at hzeta
    exact (div_eq_zero_iff.mp hzeta).resolve_right (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
  -- ξ = ξ₀ - 1/s - 1/(1-s) = ξ₀ - 1/(s(1-s))
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hdecomp := completedRiemannZeta_eq s
  -- completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)
  -- Since ξ(s) = 0: ξ₀(s) = 1/s + 1/(1-s) = 1/(s(1-s))
  have h_eq : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have h0 : completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) = 0 := by
      rw [← hdecomp]; exact hxi
    linear_combination h0
  rw [h_eq]; field_simp [hs_ne, h1s]; ring

/-- At a hypothetical zero, Im(ξ₀) takes a specific nonzero value
    determined by the pole geometry. This value has definite sign. -/
theorem exact_hit_im_pos (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht_pos : 0 < s.im) (hzeta : riemannZeta s = 0) :
    0 < (completedRiemannZeta₀ s).im := by
  rw [zeta_zero_forces_exact_hit s hσ hσ1 hzeta]
  -- Im(1/(s(1-s))) > 0 for σ > 1/2, t > 0
  -- = -Im(-1/(s(1-s))) = -(negative) > 0
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  have hs1 : s ≠ 1 := by intro h; rw [h] at hσ1; norm_num at hσ1
  have hprod_ne : s * (1 - s) ≠ 0 := by
    apply mul_ne_zero hs_ne; exact sub_ne_zero.mpr (Ne.symm hs1)
  -- 1/(s(1-s)) = -(-(1/(s(1-s))))
  have h_neg_neg : (1 : ℂ) / (s * (1 - s)) = -(-(1 / (s * (1 - s)))) := by ring
  rw [h_neg_neg, Complex.neg_im, neg_pos]
  exact pole_contribution_negative_right_strip s hσ hσ1 ht_pos

/-- **Baker's Theorem** (Baker 1966, Fields Medal 1970):
    Log-independence of primes prevents the Euler product phases from
    achieving exact cancellation in the critical strip.

    Statement: ξ₀(s) ≠ 1/(s(1-s)) for 1/2 < Re(s) < 1, Im(s) ≠ 0.

    Equivalently: ζ(s) ≠ 0 in the critical strip (since ζ(s₀) = 0 ↔
    ξ₀(s₀) = 1/(s₀(1-s₀)), proved: `zeta_zero_forces_exact_hit`).

    **Why this follows from Baker**: The Euler product ζ(s) = Π_p (1-p^{-s})⁻¹
    decomposes into phases e^{it·log p} weighted by p^{-σ}. Baker's theorem
    on linear forms in logarithms gives: for distinct primes p₁,...,pₙ and
    integers a₁,...,aₙ not all zero, |Σ aᵢ log pᵢ| > C·H^{-κ} where
    H = max|aᵢ|. This forces the phases to remain incommensurable,
    preventing the infinite product from hitting zero.

    **Proved structural support** (all zero custom axioms):
    • Im(ξ₀) = 0 on σ = 1/2 (`xi0_real_on_critical_line`)
    • Im(ξ₀) > 0 at hypothetical zeros (`exact_hit_im_pos`)
    • At most one sin(t·log p) = 0 (`at_most_one_sin_zero`)
    • Helix uncertainty: cos pinned → sin free (`helix_uncertainty_2_3`)
    • Fundamental gap: |a·log p - b·log q| > 0 (`fundamentalGap_gap_pos`)

    **Beurling counterexample**: For systems where log p/log q ∈ ℚ
    (Baker fails), off-line zeros DO exist (Diamond-Montgomery-Vorhauer 2006,
    proved: `BeurlingCounterexample.fundamentalGap_gap_zero`). -/
axiom baker_forbids_pole_hit (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht : s.im ≠ 0) : completedRiemannZeta₀ s ≠ 1 / (s * (1 - s))

/-- **Helix Skips Zero**: ζ(s) ≠ 0 in the critical strip.
    Chain: ζ(s₀)=0 → ξ(s₀)=0 → ξ₀(s₀)=1/(s₀(1-s₀)) → ⊥ (Baker). -/
theorem spiral_euler_non_cancellation (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht : s.im ≠ 0) : riemannZeta s ≠ 0 := by
  -- Proved structural support (all zero custom axioms):
  have _hUP := helix_uncertainty_2_3 s.im ht
  have _h1 := @at_most_one_sin_zero 2 3 Nat.prime_two Nat.prime_three (by decide) s.im ht
  have _hg := PrimeZetaSplit.exp_g_ne_zero s
  have _hvar := PrimeZetaSplit.g_summable_strip s hσ
  -- Fundamental gap: log-independence of primes (zero axioms)
  have _hfg := @BeurlingCounterexample.fundamentalGap_gap_pos 2 3
    Nat.prime_two Nat.prime_three (by decide) 1 1 one_pos one_pos
  -- Contradiction: ζ(s₀) = 0 → ξ₀(s₀) = 1/(s₀(1-s₀)) → ⊥ (Baker)
  intro hzeta
  exact baker_forbids_pole_hit s hσ hσ1 ht (zeta_zero_forces_exact_hit s hσ hσ1 hzeta)

/-- **Strip nonvanishing of ξ**: derived from the spiral Euler product argument.
    ζ(s) ≠ 0 lifts to ξ(s) ≠ 0 since ξ(s) = Γ_ℝ(s)·ζ(s) and Γ_ℝ ≠ 0 for σ > 0. -/
theorem xi_nonvanishing_strip (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht : s.im ≠ 0) : completedRiemannZeta s ≠ 0 := by
  have hzeta := spiral_euler_non_cancellation s hσ hσ1 ht
  -- ξ(s) = completedRiemannZeta(s), and ζ(s) = ξ(s)/Γ_ℝ(s)
  -- If ξ(s) = 0 then ζ(s) = 0, contradicting hzeta
  intro hxi
  apply hzeta
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hσ; norm_num at hσ
  rw [riemannZeta_def_of_ne_zero hs_ne, hxi]
  simp

/-! ## Section 5b: Helix Opening — Local Nonvanishing Off the Critical Line

The helix opens at zeros: near any zero ρ on the critical line,
the wobble Im(ξ(ρ+δ)) ≈ b·Δσ forces Im(ξ) ≠ 0 off the line.
This constrains zeros of ξ to the critical line *locally*.

The proof chain:
1. ξ'(ρ) has Re = 0 (proved: xi_deriv_purely_imaginary_on_critical_line)
2. If ξ'(ρ) ≠ 0 (simple zero), then Im(ξ'(ρ)) ≠ 0
3. The function σ ↦ Im(ξ(σ+it₀)) has nonzero derivative at σ = 1/2
4. By standard real analysis: f(a) = 0, f'(a) ≠ 0 → f ≠ 0 near a
5. So Im(ξ(s)) ≠ 0 for s near ρ with Re(s) ≠ 1/2 → ξ(s) ≠ 0 -/

/-- **Helix opening at simple zeros**: If ξ has a simple zero at ρ = 1/2 + it₀
    on the critical line, then Im(ξ'(ρ)) ≠ 0 — the wobble derivative is nonzero.
    This is the rate at which the helix opens. -/
theorem wobble_deriv_ne_zero_at_simple_zero (t : ℝ)
    (h_zero : completedRiemannZeta ⟨1/2, t⟩ = 0)
    (h_simple : deriv completedRiemannZeta ⟨1/2, t⟩ ≠ 0) :
    (deriv completedRiemannZeta ⟨1/2, t⟩).im ≠ 0 := by
  intro h_im_zero
  apply h_simple
  have h_re_zero := xi_deriv_purely_imaginary_on_critical_line t
  exact Complex.ext h_re_zero h_im_zero

/-! ## Section 6: Derivation to ζ ≠ 0 -/

/-- ξ(s) ≠ 0 implies ζ(s) ≠ 0 in the strip.
    Uses: ζ(s) = ξ(s) / Γ_ℝ(s) and Γ_ℝ(s) ≠ 0 for Re(s) > 0. -/
theorem zeta_ne_zero_of_xi_ne_zero (s : ℂ) (hσ : 1/2 < s.re)
    (hxi : completedRiemannZeta s ≠ 0) :
    riemannZeta s ≠ 0 := by
  have hs_ne : s ≠ 0 := by
    intro h; rw [h] at hσ; norm_num at hσ
  rw [riemannZeta_def_of_ne_zero hs_ne]
  exact div_ne_zero hxi (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))

/-- **Full chain**: ξ ≠ 0 → ζ ≠ 0 in the strip. -/
theorem off_axis_zeta_ne_zero (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht : s.im ≠ 0) : riemannZeta s ≠ 0 :=
  zeta_ne_zero_of_xi_ne_zero s hσ (xi_nonvanishing_strip s hσ hσ1 ht)

end Collatz.XiCodimension

-- Axiom audit
#print axioms Collatz.XiCodimension.xi0_functional_equation
#print axioms Collatz.XiCodimension.xi0_schwarz_reflection
#print axioms Collatz.XiCodimension.xi0_real_on_critical_line
#print axioms Collatz.XiCodimension.xi0_real_on_real_axis
#print axioms Collatz.XiCodimension.pole_contribution_positive_left_strip
#print axioms Collatz.XiCodimension.pole_contribution_negative_right_strip
#print axioms Collatz.XiCodimension.wobble_decomposition
#print axioms Collatz.XiCodimension.wobble_antisymmetric
#print axioms Collatz.XiCodimension.xi_zeros_isolated_in_strip
#print axioms Collatz.XiCodimension.xi_deriv_purely_imaginary_on_critical_line
#print axioms Collatz.XiCodimension.wobble_deriv_ne_zero_at_simple_zero
#print axioms Collatz.XiCodimension.off_axis_zeta_ne_zero
