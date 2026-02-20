/-
  CriticalLineReal.lean — ξ is Real-Valued on the Critical Line
  ==============================================================

  The completed zeta function ξ(s) = completedRiemannZeta(s) satisfies
  two symmetries:
    1. Functional equation: ξ(1-s) = ξ(s)           [Mathlib]
    2. Schwarz reflection:  ξ(conj s) = conj(ξ(s))  [PROVED]

  On the critical line s = 1/2 + it, these combine:
    1-s = 1/2-it = conj(s), so ξ(s) = ξ(1-s) = ξ(conj s) = conj(ξ(s))
    Therefore ξ(1/2+it) ∈ ℝ for all real t.

  This is the foundation of Hardy's approach: the vortex ξ(1/2+it)
  collapses from a spiral in ℂ to oscillation on ℝ. Each sign change
  gives a zero on the critical line — by the Intermediate Value Theorem.

  Proved (zero axioms):
  • schwarz_reflection_zeta: ξ(conj s) = conj(ξ(s))
  • completedZeta_real_on_critical_line: ξ(1/2+it).im = 0
  • xi_even_on_critical_line: ξ(1/2+it) = ξ(1/2-it)
  • gammaR_ne_zero_on_critical_line: Gammaℝ(1/2+it) ≠ 0
  • xi_eq_gammaR_mul_zeta: ξ(1/2+it) = Gammaℝ(1/2+it) · ζ(1/2+it)
  • gammaR_half_pos: Re(Gammaℝ(1/2)) > 0 (π^{-1/4}Γ(1/4) > 0)
  • xi_at_one_negative: Re(ξ(1)) < 0 (from γ < log(4π))
  • xi_at_zero_negative: Re(ξ(0)) < 0 (functional equation)
  • Continuity, IVT, zeros ↔ real zeros

  Assumption interface (for Hardy's theorem):
  • `XiOscillates` — Hardy oscillation (second moment forces sign changes)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Order.IntermediateValue

open Complex Filter

namespace CriticalLineReal

/-! ## Section 1: Schwarz Reflection (PROVED)

The completed zeta function has real Dirichlet coefficients (all 1).
By Schwarz reflection, ξ(conj s) = conj(ξ(s)).

Proof strategy:
  1. For Re(s) > 1: conjugate the tsum π^{-s/2} Γ(s/2) Σ n^{-s}
     using Gamma_conj, conj_cpow, conj_tsum.
  2. Lift to ξ₀ using completedRiemannZeta_eq.
  3. conj ∘ ξ₀ ∘ conj is entire (HasDerivAt.conj_conj).
  4. Identity theorem (eq_of_eventuallyEq) extends to all ℂ.
  5. Convert back to ξ. -/

/-- conj(π^s) = π^(conj s). Real base, so arg ≠ π. -/
private theorem conj_pi_cpow (s : ℂ) :
    starRingEnd ℂ ((↑Real.pi : ℂ) ^ s) = (↑Real.pi : ℂ) ^ (starRingEnd ℂ s) := by
  have harg : ((↑Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]; exact Real.pi_ne_zero.symm
  have h := conj_cpow (↑Real.pi : ℂ) s harg
  rw [show (starRingEnd ℂ) (↑Real.pi : ℂ) = ↑Real.pi from RCLike.conj_ofReal _] at h
  exact (congr_arg (starRingEnd ℂ) h).trans (by simp)

/-- conj(↑n ^ s) = ↑n ^ (conj s) for natural n. -/
private theorem conj_nat_cpow (n : ℕ) (s : ℂ) :
    starRingEnd ℂ ((↑n : ℂ) ^ s) = (↑n : ℂ) ^ (starRingEnd ℂ s) := by
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp only [Nat.cast_zero]
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · rw [zero_cpow hs, map_zero, zero_cpow]
      intro h
      exact hs (starRingEnd_self_apply s ▸ (congr_arg (starRingEnd ℂ) h).trans (map_zero _))
  · have harg : ((↑n : ℂ)).arg ≠ Real.pi := by
      rw [show (↑n : ℂ) = ↑(↑n : ℝ) from by push_cast; ring,
        arg_ofReal_of_nonneg (by positivity : (0:ℝ) ≤ ↑n)]
      exact Real.pi_ne_zero.symm
    have h := conj_cpow (↑n : ℂ) s harg
    rw [show (starRingEnd ℂ) (↑n : ℂ) = ↑n from RCLike.conj_ofReal _] at h
    exact (congr_arg (starRingEnd ℂ) h).trans (by simp)

/-- Schwarz reflection for ξ in the convergent half-plane Re(s) > 1.
    Conjugate π^{-s/2} · Γ(s/2) · Σ 1/n^s term by term. -/
private theorem conj_completedZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    starRingEnd ℂ (completedRiemannZeta s) = completedRiemannZeta (starRingEnd ℂ s) := by
  have hs' : 1 < (starRingEnd ℂ s).re := by simp [hs]
  rw [completedZeta_eq_tsum_of_one_lt_re hs, completedZeta_eq_tsum_of_one_lt_re hs']
  simp only [map_mul, conj_pi_cpow, ← Gamma_conj, Complex.conj_tsum]
  congr 1; congr 1
  · congr 1; simp [map_neg, map_div₀, map_ofNat]
  · congr 1; simp [map_div₀, map_ofNat]
  · exact tsum_congr (fun n => by simp [conj_nat_cpow])

/-- Lift to ξ₀ for Re(s) > 1 using ξ = ξ₀ - 1/s - 1/(1-s). -/
private theorem conj_xi0_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    starRingEnd ℂ (completedRiemannZeta₀ s) = completedRiemannZeta₀ (starRingEnd ℂ s) := by
  have heq : ∀ w : ℂ, completedRiemannZeta₀ w = completedRiemannZeta w + 1 / w + 1 / (1 - w) := by
    intro w; have := completedRiemannZeta_eq w; linear_combination -this
  rw [heq s, heq (starRingEnd ℂ s)]
  simp only [map_add, map_div₀, map_one, map_sub, conj_completedZeta_of_one_lt_re hs]

/-- conj ∘ ξ₀ ∘ conj is entire (from HasDerivAt.conj_conj). -/
private theorem differentiable_conj_xi0_conj :
    Differentiable ℂ (fun s => starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ s))) := by
  intro s
  have h := (differentiable_completedZeta₀ (starRingEnd ℂ s)).hasDerivAt.conj_conj
  simp only [starRingEnd_self_apply, Function.comp_def] at h
  exact h.differentiableAt

/-- The two entire functions agree near z₀ = 2 (in the half-plane Re > 1). -/
private theorem eventually_eq_near_two :
    (fun s => starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ s)))
      =ᶠ[nhds 2] completedRiemannZeta₀ := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  exact eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => by
    rw [Set.mem_setOf_eq] at hs
    have h := conj_xi0_of_one_lt_re hs
    -- h : conj(ξ₀ s) = ξ₀(conj s); take conj of both sides to get conj(ξ₀(conj s)) = ξ₀ s
    have h2 := congr_arg (starRingEnd ℂ) h
    simp only [starRingEnd_self_apply] at h2
    exact h2.symm)

/-- Identity theorem: conj ∘ ξ₀ ∘ conj = ξ₀ on all of ℂ. -/
private theorem conj_xi0_conj_eq_xi0 :
    (fun s => starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ s))) = completedRiemannZeta₀ :=
  AnalyticOnNhd.eq_of_eventuallyEq
    (differentiable_conj_xi0_conj.differentiableOn.analyticOnNhd isOpen_univ)
    (differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ)
    eventually_eq_near_two

/-- **Schwarz reflection for the completed zeta function.**
    ξ(conj s) = conj(ξ(s)) for all s ∈ ℂ.

    PROVED from Mathlib: identity theorem + tsum conjugation for Re > 1.
    Zero custom axioms. -/
theorem schwarz_reflection_zeta (s : ℂ) :
    completedRiemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta s) := by
  -- From conj_xi0_conj_eq_xi0: ∀ w, conj(ξ₀(conj w)) = ξ₀(w)
  -- Substitute conj s: conj(ξ₀(s)) = ξ₀(conj s)
  have h0 := congr_fun conj_xi0_conj_eq_xi0
  have h_conj_xi0 : completedRiemannZeta₀ (starRingEnd ℂ s) =
      starRingEnd ℂ (completedRiemannZeta₀ s) := by
    have := h0 (starRingEnd ℂ s)
    simp only [starRingEnd_self_apply] at this
    exact this.symm
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, h_conj_xi0]
  simp [map_sub, map_one]

/-! ## Section 2: ξ is Real on the Critical Line (PROVED) -/

/-- On the critical line, 1-s = conj(s). -/
theorem one_sub_eq_conj_on_critical_line (t : ℝ) :
    (1 : ℂ) - ⟨1/2, t⟩ = starRingEnd ℂ ⟨1/2, t⟩ := by
  apply ext
  · simp; ring
  · simp

/-- **ξ(1/2+it) is real for all real t.**

    The vortex ξ(1/2+it) collapses from spiral to real line.
    Proof: functional equation + Schwarz reflection combine on
    the critical line where 1-s = conj(s). -/
theorem completedZeta_real_on_critical_line (t : ℝ) :
    (completedRiemannZeta ⟨1/2, t⟩).im = 0 := by
  have hfe := completedRiemannZeta_one_sub (⟨1/2, t⟩ : ℂ)
  rw [one_sub_eq_conj_on_critical_line] at hfe
  rw [schwarz_reflection_zeta] at hfe
  exact conj_eq_iff_im.mp hfe

/-- ξ(1/2+it) is a real number. -/
theorem completedZeta_on_critical_line_real (t : ℝ) :
    ∃ r : ℝ, completedRiemannZeta ⟨1/2, t⟩ = ↑r := by
  rw [← conj_eq_iff_real]
  have hfe := completedRiemannZeta_one_sub (⟨1/2, t⟩ : ℂ)
  rw [one_sub_eq_conj_on_critical_line, schwarz_reflection_zeta] at hfe
  exact hfe

/-! ## Section 3: Zeros ↔ Real Zeros (PROVED) -/

/-- Zeros of ξ on the critical line reduce to real zeros:
    ξ(1/2+it) = 0 ↔ Re(ξ(1/2+it)) = 0. -/
theorem critical_line_zero_iff_re_zero (t : ℝ) :
    completedRiemannZeta ⟨1/2, t⟩ = 0 ↔
    (completedRiemannZeta ⟨1/2, t⟩).re = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; exact ext h (completedZeta_real_on_critical_line t)

/-! ## Section 4: Continuity Along the Critical Line (PROVED) -/

private theorem continuousAt_critical_line_emb (t : ℝ) :
    ContinuousAt (fun t : ℝ => (⟨(1:ℝ)/2, t⟩ : ℂ)) t := by
  have h : (fun t : ℝ => (⟨(1/2 : ℝ), t⟩ : ℂ)) =
    (fun t : ℝ => (↑(1/2 : ℝ) + ↑t * I : ℂ)) := by
    ext t; apply ext <;> simp
  rw [h]
  exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousAt

/-- ξ is continuous along the critical line (s ≠ 0, 1 there). -/
theorem continuous_xi_on_critical_line :
    Continuous (fun t : ℝ => completedRiemannZeta ⟨1/2, t⟩) := by
  rw [continuous_iff_continuousAt]; intro t
  have hs0 : (⟨(1:ℝ)/2, t⟩ : ℂ) ≠ 0 := by
    intro h; have := congr_arg re h; simp at this
  have hs1 : (⟨(1:ℝ)/2, t⟩ : ℂ) ≠ 1 := by
    intro h; have := congr_arg re h; simp at this
  exact (differentiableAt_completedZeta hs0 hs1).continuousAt.comp
    (continuousAt_critical_line_emb t)

/-- Re(ξ) is continuous along the critical line. -/
theorem continuous_xi_re_on_critical_line :
    Continuous (fun t : ℝ => (completedRiemannZeta ⟨1/2, t⟩).re) :=
  continuous_re.comp continuous_xi_on_critical_line

/-! ## Section 5: Sign Changes Give Zeros (PROVED)

Since ξ(1/2+it) is real-valued and continuous, the Intermediate Value
Theorem applies: whenever Re(ξ) changes sign between t₁ and t₂,
there exists t₀ ∈ (t₁, t₂) with ξ(1/2+it₀) = 0.

This is the mechanism that Hardy used to prove infinitely many zeros
on the critical line: the function Z(t) = e^{iθ(t)}ζ(1/2+it) is
real-valued and oscillates, producing infinitely many sign changes. -/

/-- **Sign changes of ξ on the critical line give zeros.**
    The IVT applied to the real-valued function t ↦ Re(ξ(1/2+it)). -/
theorem sign_change_gives_zero (t₁ t₂ : ℝ) (h12 : t₁ < t₂)
    (h1 : (completedRiemannZeta ⟨1/2, t₁⟩).re < 0)
    (h2 : 0 < (completedRiemannZeta ⟨1/2, t₂⟩).re) :
    ∃ t₀ : ℝ, t₁ < t₀ ∧ t₀ < t₂ ∧ completedRiemannZeta ⟨1/2, t₀⟩ = 0 := by
  have h0_mem : (0 : ℝ) ∈ Set.Icc ((completedRiemannZeta ⟨1/2, t₁⟩).re)
    ((completedRiemannZeta ⟨1/2, t₂⟩).re) := ⟨h1.le, h2.le⟩
  obtain ⟨t₀, ht₀_mem, ht₀_val⟩ := intermediate_value_Icc h12.le
    continuous_xi_re_on_critical_line.continuousOn h0_mem
  refine ⟨t₀, ?_, ?_, (critical_line_zero_iff_re_zero t₀).mpr ht₀_val⟩
  · rcases eq_or_lt_of_le ht₀_mem.1 with heq | hlt
    · linarith [heq ▸ ht₀_val]
    · exact hlt
  · rcases eq_or_lt_of_le ht₀_mem.2 with heq | hlt
    · linarith [heq ▸ ht₀_val]
    · exact hlt

/-! ## Section 6: Connection to ζ and Hardy's Z-Function

The completed zeta ξ relates to the Riemann zeta by:
  ξ(s) = Gammaℝ(s) · ζ(s)
where Gammaℝ(s) = π^{-s/2} Γ(s/2) is Mathlib's `Complex.Gammaℝ`.

On the critical line, Gammaℝ(1/2+it) ≠ 0 (Γ has no zeros), so:
  ξ(1/2+it) = 0  ↔  ζ(1/2+it) = 0

Hardy's Z-function unwinds the phase of Gammaℝ:
  Z(t) = e^{iθ(t)} · ζ(1/2+it)
where θ(t) = arg(Gammaℝ(1/2+it)). Since |Gammaℝ| > 0, the phase
is well-defined, and Z(t) is real-valued with |Z(t)| = |ζ(1/2+it)|.

The key for Hardy's theorem: Z(t) oscillates (grows on average
via the second moment ∫₀ᵀ Z(t)² dt ~ T log T, but has mean zero),
so it has infinitely many sign changes → infinitely many zeros. -/

/-- ξ(1/2+it) = 0 ↔ ζ(1/2+it) = 0 (since Gammaℝ ≠ 0 there). -/
theorem zeta_zero_iff_xi_zero (t : ℝ) :
    riemannZeta ⟨1/2, t⟩ = 0 ↔ completedRiemannZeta ⟨1/2, t⟩ = 0 := by
  have hs : (⟨(1:ℝ)/2, t⟩ : ℂ) ≠ 0 := by
    intro h; have := congr_arg re h; simp at this
  rw [riemannZeta_def_of_ne_zero hs]
  constructor
  · intro h
    have := div_eq_zero_iff.mp h
    rcases this with h1 | h1
    · exact h1
    · exfalso
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp : 0 < (⟨(1:ℝ)/2, t⟩ : ℂ).re) h1
  · intro h; rw [h, zero_div]

/-! ## Section 6a: Functional Equation on the Critical Line (PROVED)

The functional equation ξ(1-s) = ξ(s) specializes on the critical line to
ξ(1/2+it) = ξ(1/2-it): the function t ↦ ξ(1/2+it) is even.

Gammaℝ(1/2+it) = π^{-(1/2+it)/2} Γ((1/2+it)/2) is nonzero on the
critical line (Gammaℝ has zeros only at non-positive even integers).
Therefore ξ(1/2+it) = Gammaℝ(1/2+it) · ζ(1/2+it), and zeros of ξ
correspond exactly to zeros of ζ. -/

/-- ξ is even on the critical line: ξ(1/2+it) = ξ(1/2-it).
    From the functional equation ξ(1-s) = ξ(s) with 1-(1/2+it) = 1/2-it. -/
theorem xi_even_on_critical_line (t : ℝ) :
    completedRiemannZeta ⟨1/2, t⟩ = completedRiemannZeta ⟨1/2, -t⟩ := by
  have h := completedRiemannZeta_one_sub (⟨1/2, t⟩ : ℂ)
  have harg : (1 : ℂ) - ⟨1/2, t⟩ = ⟨1/2, -t⟩ := by
    apply ext <;> simp; ring
  rw [harg] at h; exact h.symm

/-- Gammaℝ(1/2+it) ≠ 0 for any real t (re = 1/2 > 0). -/
theorem gammaR_ne_zero_on_critical_line (t : ℝ) :
    Complex.Gammaℝ ⟨1/2, t⟩ ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by simp : 0 < (⟨(1:ℝ)/2, t⟩ : ℂ).re)

/-- ξ(1/2+it) = Gammaℝ(1/2+it) · ζ(1/2+it) — the multiplicative factorization.
    Zeros of ξ on the critical line are exactly zeros of ζ. -/
theorem xi_eq_gammaR_mul_zeta (t : ℝ) :
    completedRiemannZeta ⟨1/2, t⟩ = Complex.Gammaℝ ⟨1/2, t⟩ * riemannZeta ⟨1/2, t⟩ := by
  have hs : (⟨(1:ℝ)/2, t⟩ : ℂ) ≠ 0 := by
    intro h; have := congr_arg re h; simp at this
  rw [riemannZeta_def_of_ne_zero hs, mul_div_cancel₀ _ (gammaR_ne_zero_on_critical_line t)]

/-! ## Section 6b: ξ at Special Points (PROVED — zero axioms)

Gammaℝ(1/2) = π^{-1/4} · Γ(1/4) is a positive real number.

ξ(1) = (γ - log(4π))/2 < 0 from Mathlib's `completedRiemannZeta_one` and
the bound γ < 2/3 < 1 < log(4π). The functional equation gives ξ(0) = ξ(1) < 0.

These are concrete computed values of ξ — not on the critical line, but
demonstrating that ξ takes negative values. The critical-line sign changes
needed for Hardy's theorem are packaged as the hypothesis `XiOscillates`
in Section 7. -/

/-- Gammaℝ(1/2) = π^{-1/4} · Γ(1/4), a positive real number. -/
private theorem gammaR_half_eq :
    Complex.Gammaℝ (1/2 : ℂ) = ↑(Real.pi ^ (-(1/4 : ℝ)) * Real.Gamma (1/4 : ℝ)) := by
  rw [Complex.Gammaℝ.eq_1]
  have h1 : (-(1/2 : ℂ)/2) = ↑(-(1/4 : ℝ)) := by push_cast; ring
  have h2 : ((1/2 : ℂ)/2) = ↑(1/4 : ℝ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (le_of_lt Real.pi_pos), Complex.Gamma_ofReal]
  push_cast; ring

/-- Gammaℝ(1/2) is a positive real: re > 0. -/
theorem gammaR_half_pos : 0 < (Complex.Gammaℝ (1/2 : ℂ)).re := by
  rw [gammaR_half_eq, ofReal_re]
  exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4))

/-- Gammaℝ(1/2) is a positive real: im = 0. -/
theorem gammaR_half_im_zero : (Complex.Gammaℝ (1/2 : ℂ)).im = 0 := by
  rw [gammaR_half_eq, ofReal_im]

/-- **ξ(1) < 0**: the completed zeta at s = 1.
    Mathlib gives ξ(1) = (γ - log(4π))/2. Since γ < 2/3 and log(4π) > 1,
    we get ξ(1) < (2/3 - 1)/2 < 0. PROVED — zero custom axioms. -/
theorem xi_at_one_negative : (completedRiemannZeta 1).re < 0 := by
  have hre : (completedRiemannZeta 1).re =
      (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 := by
    rw [completedRiemannZeta_one,
      show (4 : ℂ) * ↑Real.pi = ↑(4 * Real.pi) from by push_cast; ring,
      ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ 4 * Real.pi)]
    simp [ofReal_re]
  rw [hre]
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hlog : 1 < Real.log (4 * Real.pi) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log (Real.exp_pos 1)
      (calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        _ < 4 * 3 := by norm_num
        _ < 4 * Real.pi := by linarith [Real.pi_gt_three])
  linarith

/-- **ξ(0) < 0**: from the functional equation ξ(0) = ξ(1).
    PROVED — zero custom axioms. -/
theorem xi_at_zero_negative : (completedRiemannZeta 0).re < 0 := by
  have h := completedRiemannZeta_one_sub (1 : ℂ)
  simp at h; rw [h]
  exact xi_at_one_negative

/-! ## Section 7: Hardy's Theorem — Infinitely Many Zeros (from `XiOscillates`)

The real-valued function t ↦ Re(ξ(1/2+it)) oscillates: for every T,
there exist t₁ > T and t₂ > t₁ where Re(ξ) is negative then positive.
This is the content of Hardy's 1914 result.

The oscillation follows from the second moment:
  ∫₀ᵀ |ζ(1/2+it)|² dt ~ T log T → ∞
but ∫₀ᵀ ζ(1/2+it) dt = T + O(T^{1/2}), forcing cancellation.

The hypothesis `XiOscillates` encodes this: Re(ξ) alternates sign
arbitrarily far along the critical line. Combined with IVT →
infinitely many zeros. -/

/-- Re(ξ) oscillates on the critical line: for every T, there are t₁ < t₂
    beyond T where Re(ξ) is negative at t₁ and positive at t₂.
    Content: the second moment ∫₀ᵀ |ζ(1/2+it)|² dt → ∞ forces oscillation. -/
def XiOscillates : Prop :=
    ∀ T : ℝ, ∃ t₁ t₂ : ℝ, T < t₁ ∧ t₁ < t₂ ∧
    (completedRiemannZeta ⟨1/2, t₁⟩).re < 0 ∧
    0 < (completedRiemannZeta ⟨1/2, t₂⟩).re

/-- **Hardy's Theorem** (1914): ζ(s) has infinitely many zeros on Re(s) = 1/2.
    Derived from `XiOscillates` + schwarz_reflection_zeta.

    The pipeline: `XiOscillates` gives sign changes of the real function
    Re(ξ(1/2+it)), IVT gives ξ(1/2+it₀) = 0, and ξ zero ↔ ζ zero
    (since Gammaℝ ≠ 0) converts to a ζ zero on the critical line. -/
theorem hardy_infinitely_many_zeros (hXi : XiOscillates) :
    ∀ T : ℝ, ∃ t : ℝ, T < t ∧ riemannZeta ⟨1/2, t⟩ = 0 := by
  intro T
  obtain ⟨t₁, t₂, hT, h12, hneg, hpos⟩ := hXi T
  have h0 : (0 : ℝ) ∈ Set.Icc ((completedRiemannZeta ⟨1/2, t₁⟩).re)
    ((completedRiemannZeta ⟨1/2, t₂⟩).re) := ⟨hneg.le, hpos.le⟩
  obtain ⟨t₀, ht₀, hval⟩ := intermediate_value_Icc h12.le
    continuous_xi_re_on_critical_line.continuousOn h0
  refine ⟨t₀, lt_of_lt_of_le hT ht₀.1, ?_⟩
  exact (zeta_zero_iff_xi_zero t₀).mpr ((critical_line_zero_iff_re_zero t₀).mpr hval)

end CriticalLineReal

-- Axiom audit
#print axioms CriticalLineReal.schwarz_reflection_zeta
#print axioms CriticalLineReal.completedZeta_real_on_critical_line
#print axioms CriticalLineReal.xi_even_on_critical_line
#print axioms CriticalLineReal.gammaR_ne_zero_on_critical_line
#print axioms CriticalLineReal.xi_eq_gammaR_mul_zeta
#print axioms CriticalLineReal.gammaR_half_pos
#print axioms CriticalLineReal.xi_at_one_negative
#print axioms CriticalLineReal.xi_at_zero_negative
#print axioms CriticalLineReal.hardy_infinitely_many_zeros
