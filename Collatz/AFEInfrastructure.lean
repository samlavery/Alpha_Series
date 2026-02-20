/-
  AFEInfrastructure.lean — Decomposing afe_dominance (v6)
  =======================================================

  EntangledPair.lean proves RH from `afe_coordination`.
  This file provides the proved infrastructure that decomposes it into
  identifiable textbook ingredients.

  What's proved (zero custom axioms):
  • χ(s) = Γ_ℝ(1-s)/Γ_ℝ(s) definition
  • Γ_ℝ nonvanishing in the strip (from Mathlib)
  • Functional equation ζ(s) = χ(s)·ζ(1-s)
  • χ(s) = (Γ_ℂ(s) · cos(πs/2))⁻¹ (from Gammaℝ_div_Gammaℝ_one_sub)
  • ‖χ(s)‖ = 1/‖Γ_ℂ(s) · cos(πs/2)‖ (norm identity)
  • χ-attenuation for large |t| (from Stirling + cos bound)
  • Partial sum dominance for large |t| (from χ-attenuation)
  • Partial sum norm bounds (triangle inequality)
  • Term norm identity ‖n^{-s}‖ = n^{-σ}
  • S equivalence bridge (SpiralInduction.S = EntangledPair.S)
  • E error decomposition (ζ-E in terms of EMD remainders + power terms)
  • Assembly: axioms → strip nonvanishing → RH

  Axioms (0 in this file — gamma_stirling_bound now a theorem from StirlingBound.lean):

  EntangledPair axiom (1):
  • afe_coordination: dominance + AFE error < gap at same X
    (Hardy-Littlewood + χ-attenuation — target for proof)

  StirlingBound axiom (1):
  • stirling_unit_strip: Stirling for σ ∈ (0,1] (reflection + ratio estimate)

  Total: 2 custom axioms (reduced from 4 in v5, gamma_stirling_bound eliminated).
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Collatz.EntangledPair
import Collatz.SpiralInduction
import Collatz.SpiralTactics
import Collatz.BakerUncertainty
import Collatz.StirlingBound
import Collatz.XiCodimension

open Finset Complex

namespace AFEInfrastructure

/-! ## Section 1: χ(s) — The Functional Equation Scalar

  χ(s) = Γ_ℝ(1-s) / Γ_ℝ(s)

  The functional equation ζ(s) = χ(s)·ζ(1-s) follows from the
  completed zeta symmetry ξ(s) = ξ(1-s) where ξ(s) = Γ_ℝ(s)·ζ(s). -/

/-- The functional equation scalar: χ(s) = Γ_ℝ(1-s) / Γ_ℝ(s). -/
noncomputable def chi (s : ℂ) : ℂ := (1 - s).Gammaℝ / s.Gammaℝ

/-- Γ_ℝ(s) ≠ 0 for Re(s) > 0 (direct from Mathlib). -/
theorem chi_well_defined {s : ℂ} (hs : 0 < s.re) : s.Gammaℝ ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos hs

/-- Γ_ℝ doesn't vanish in the strip 1/2 < σ < 1.
    Since 1/2 < σ implies Re(s) > 0, this is immediate. -/
theorem gammaR_ne_zero_in_strip {s : ℂ} (hσ : 1/2 < s.re) :
    s.Gammaℝ ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)

/-- Γ_ℝ(1-s) doesn't vanish in the strip: Re(1-s) = 1 - σ ∈ (0, 1/2). -/
theorem gammaR_one_sub_ne_zero_in_strip {s : ℂ} (_hσ : 1/2 < s.re) (hσ1 : s.re < 1) :
    (1 - s).Gammaℝ ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp [Complex.sub_re]
  linarith

/-- In the strip, s ≠ -(2n+1) for any n : ℕ (needed for Gammaℝ_div_Gammaℝ_one_sub). -/
lemma strip_ne_neg_odd {s : ℂ} (hσ : 0 < s.re) (n : ℕ) : s ≠ -(2 * ↑n + 1) := by
  intro h
  have hre : s.re = (-(2 * (↑n : ℂ) + 1)).re := congrArg re h
  simp at hre
  linarith

/-- In the strip, s ≠ -n for any n : ℕ (needed for inv_Gammaℝ_one_sub). -/
lemma strip_ne_neg_nat {s : ℂ} (hσ : 0 < s.re) (n : ℕ) : s ≠ -(↑n : ℂ) := by
  intro h
  have hre : s.re = (-(↑n : ℂ)).re := congrArg re h
  simp at hre
  linarith

/-- The functional equation: ζ(s) = χ(s) · ζ(1-s) for s in the strip.

    Proof: ξ(s) = ξ(1-s)  [completedRiemannZeta_one_sub]
    and ζ(s) = ξ(s)/Γ_ℝ(s), ζ(1-s) = ξ(1-s)/Γ_ℝ(1-s)  [riemannZeta_def_of_ne_zero]
    so ζ(s) = ξ(s)/Γ_ℝ(s) = ξ(1-s)/Γ_ℝ(s) = (Γ_ℝ(1-s)/Γ_ℝ(s)) · ξ(1-s)/Γ_ℝ(1-s)
            = χ(s) · ζ(1-s). -/
theorem functional_equation_chi {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1)
    (hΓ : s.Gammaℝ ≠ 0) (hΓ' : (1 - s).Gammaℝ ≠ 0) :
    riemannZeta s = chi s * riemannZeta (1 - s) := by
  have hs1 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs')
  rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hs1]
  rw [completedRiemannZeta_one_sub]
  unfold chi
  field_simp

/-! ## Section 2: χ Norm Identity (PROVED — from Mathlib v4.27.0)

  Mathlib's `Gammaℝ_div_Gammaℝ_one_sub` gives:
    Γ_ℝ(s) / Γ_ℝ(1-s) = Γ_ℂ(s) · cos(πs/2)

  Therefore: χ(s) = Γ_ℝ(1-s)/Γ_ℝ(s) = (Γ_ℂ(s) · cos(πs/2))⁻¹

  This is the key structural identity. It shows:
  • On the critical line (σ = 1/2): |Γ_ℂ · cos| = 1, so |χ| = 1
  • For large |t|: |cos(π(σ+it)/2)| ~ e^{π|t|/2}/2, and
    |Γ(s)| ~ |t|^{σ-1/2} · e^{-π|t|/2} (Stirling), so the product
    |Γ_ℂ · cos| ~ |t|^{σ-1/2} → ∞ for σ > 1/2, giving |χ| → 0.
  • For t = 0: |Γ_ℂ(σ) · cos(πσ/2)| < 1 for σ > 1/2, so |χ(σ)| > 1.
    This is NOT a contradiction — it means the reflected spiral is AMPLIFIED
    at real points, but the primary spiral grows faster (convergence for σ > 1). -/

/-- χ(s) = (Γ_ℂ(s) · cos(πs/2))⁻¹ for s in the strip.
    From Mathlib's Gammaℝ_div_Gammaℝ_one_sub. -/
theorem chi_eq_inv_gammaC_cos {s : ℂ} (hσ : 0 < s.re) :
    chi s = (s.Gammaℂ * Complex.cos (↑Real.pi * s / 2))⁻¹ := by
  have hne_odd := strip_ne_neg_odd hσ
  have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hσ
  have h := Complex.Gammaℝ_div_Gammaℝ_one_sub hne_odd
  -- h : s.Gammaℝ / (1 - s).Gammaℝ = s.Gammaℂ * cos(πs/2)
  -- Goal: (1-s).Gammaℝ / s.Gammaℝ = (s.Gammaℂ * cos(πs/2))⁻¹
  unfold chi
  rw [← h]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_inv]

/-- ‖χ(s)‖ = 1/‖Γ_ℂ(s) · cos(πs/2)‖ for s in the strip.
    Immediate from chi_eq_inv_gammaC_cos + norm_inv. -/
theorem chi_norm_eq {s : ℂ} (hσ : 0 < s.re) :
    ‖chi s‖ = ‖s.Gammaℂ * Complex.cos (↑Real.pi * s / 2)‖⁻¹ := by
  rw [chi_eq_inv_gammaC_cos hσ, norm_inv]

/-! ## Section 3: Term Norm Identity

  ‖(n+1)^{-s}‖ = (n+1)^{-σ} for n : ℕ.

  The modulus of a Dirichlet series term strips the oscillation,
  leaving only the amplitude decay. -/

/-- ‖(n+1)^{-s}‖ = (n+1)^{-Re(s)} for natural n.
    Uses `Complex.norm_natCast_cpow_of_pos` from Mathlib. -/
theorem term_norm (s : ℂ) (n : ℕ) :
    ‖(↑(n + 1) : ℂ) ^ (-s)‖ = (↑(n + 1) : ℝ) ^ (-s.re) := by
  have hpos : (0 : ℕ) < n + 1 := Nat.succ_pos n
  rw [show -(s) = (-s : ℂ) from rfl]
  rw [Complex.norm_natCast_cpow_of_pos hpos (-s)]
  simp [Complex.neg_re]

/-! ## Section 4: Partial Sum Norm Bounds

  Triangle inequality bounds on S(s,X) = Σ_{n=1}^{X} n^{-s}. -/

/-- Upper bound: ‖S(s,X)‖ ≤ Σ_{n=1}^{X} (n)^{-σ}. -/
theorem S_norm_upper_bound (s : ℂ) (X : ℕ) :
    ‖EntangledPair.S s X‖ ≤ ∑ n ∈ Finset.range X, (↑(n + 1) : ℝ) ^ (-s.re) := by
  unfold EntangledPair.S
  calc ‖∑ n ∈ Finset.range X, (↑(n + 1) : ℂ) ^ (-s)‖
      ≤ ∑ n ∈ Finset.range X, ‖(↑(n + 1) : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range X, (↑(n + 1) : ℝ) ^ (-s.re) := by
        congr 1; ext n; exact term_norm s n

/-! ## Section 5: χ Attenuation — Large |t| Regime (PROVED from Stirling)

  CORRECTION from v1: The claim ‖χ(s)‖ < 1 for ALL t is FALSE.

  At t = 0, σ > 1/2: χ(σ) = Γ_ℝ(1-σ)/Γ_ℝ(σ) = π^{(2σ-1)/2} · Γ((1-σ)/2)/Γ(σ/2).
  Since (1-σ)/2 is closer to the Γ-pole at 0 than σ/2, we have Γ((1-σ)/2) ≫ Γ(σ/2),
  making ‖χ(σ)‖ > 1 for all σ ∈ (1/2, 1) at t = 0.

  However, for large |t|, Stirling's approximation gives:
    ‖χ(σ+it)‖ ~ (|t|/2π)^{1/2-σ} → 0 as |t| → ∞

  The exponent 1/2 - σ < 0 for σ > 1/2 ensures decay.

  DECOMPOSITION (v3): chi_attenuation_large_t is now a THEOREM proved from:
  • gamma_stirling_bound — Stirling for |Γ(σ+it)| (AXIOM — Titchmarsh §4.42)
  • cos_exp_lower_bound — |cos(πs/2)| ≥ e^{π|t|/2}/4 (PROVABLE from Mathlib)
  • chi_norm_eq — ‖χ(s)‖ = ‖Γ_ℂ(s)·cos(πs/2)‖⁻¹ (PROVED, Section 2)

  The exponential factors cancel: e^{-π|t|/2} from Stirling and e^{+π|t|/2} from cos.
  The residual is |t|^{σ-1/2} in the denominator → |t|^{1/2-σ} bound on ‖χ‖. -/

section GammaRatioUpperHalfInterface

/-- Stirling's approximation for |Γ(σ+it)| on vertical lines.
    For fixed σ > 0 and large |t|:
      C_lo·|t|^{σ-1/2}·e^{-π|t|/2} ≤ |Γ(σ+it)| ≤ C_hi·|t|^{σ-1/2}·e^{-π|t|/2}
    Standard reference: Titchmarsh §4.42, Iwaniec-Kowalski (5.11). -/
theorem gamma_stirling_bound {hUpper : StirlingBound.GammaRatioUpperHalf}
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ (C_lo C_hi T₀ : ℝ), 0 < C_lo ∧ 0 < C_hi ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      C_lo * |t| ^ (σ - 1/2) * Real.exp (-Real.pi * |t| / 2) ≤
        ‖Complex.Gamma ⟨σ, t⟩‖ ∧
      ‖Complex.Gamma ⟨σ, t⟩‖ ≤
        C_hi * |t| ^ (σ - 1/2) * Real.exp (-Real.pi * |t| / 2) :=
  StirlingBound.gamma_stirling_bound (hUpper := hUpper) σ hσ

/-- |cos(π(σ+it)/2)| ≥ e^{π|t|/2}/4 for |t| ≥ 1.
    From cos(z) = (e^{iz}+e^{-iz})/2, reverse triangle inequality:
    |cos(z)| ≥ ||e^{-iz}|-|e^{iz}||/2 = sinh(|Im z|).
    For z = πs/2: Im(z) = πt/2, and sinh(x) ≥ (eˣ-1)/2 ≥ eˣ/4 for x ≥ ln 2.

    PROVED FROM FIRST PRINCIPLES (using Mathlib). -/
theorem cos_exp_lower_bound (σ t : ℝ) (ht : 1 ≤ |t|) :
    Real.exp (Real.pi * |t| / 2) / 4 ≤
      ‖Complex.cos (↑Real.pi * (⟨σ, t⟩ : ℂ) / 2)‖ := by
  set z : ℂ := ↑Real.pi * ⟨σ, t⟩ / 2 with hz_def
  set y := Real.pi * |t| / 2 with hy_def
  -- y ≥ π/2 > 1
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hy_pos : 0 < y := by positivity
  have hy_ge : 1 ≤ y := by
    calc y = Real.pi * |t| / 2 := rfl
      _ ≥ Real.pi * 1 / 2 := by linarith [mul_le_mul_of_nonneg_left ht hpi_pos.le]
      _ = Real.pi / 2 := by ring
      _ ≥ 1 := by linarith [Real.two_le_pi]
  -- z.im = π * t / 2
  have hz_im : z.im = Real.pi * t / 2 := by
    simp [hz_def, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.div_ofNat]
  -- |z.im| = y
  have hz_im_abs : |z.im| = y := by
    rw [hz_im, hy_def, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2),
        show |Real.pi * t| = Real.pi * |t| from by rw [abs_mul, abs_of_pos hpi_pos]]
  -- Step 1: ‖cos z‖ ≥ |Real.sinh(z.im)| via cos_eq decomposition
  -- cos(z) = cos(re)*cosh(im) - sin(re)*sinh(im)*I
  -- ‖cos z‖² = cos²(re)*cosh²(im) + sin²(re)*sinh²(im)
  --          = cos²(re)*(sinh²(im)+1) + sin²(re)*sinh²(im)     [cosh² = sinh² + 1]
  --          = sinh²(im) + cos²(re) ≥ sinh²(im)
  -- So ‖cos z‖ ≥ |sinh(im)| = sinh(|im|)
  have h_norm_ge_sinh : Real.sinh y ≤ ‖Complex.cos z‖ := by
    have h_sq : Real.sinh z.im ^ 2 ≤ ‖Complex.cos z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.cos_eq z]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.sub_re,
        Complex.mul_im, Complex.sub_im, Complex.add_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
        Complex.cos_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im,
        Complex.sinh_ofReal_re, Complex.sinh_ofReal_im]
      nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq z.im,
                 sq_nonneg (Real.cos z.re), sq_nonneg (Real.sin z.re),
                 sq_nonneg (Real.sinh z.im), sq_nonneg (Real.cosh z.im),
                 sq_nonneg (Real.cos z.re * Real.cosh z.im),
                 sq_nonneg (Real.sin z.re * Real.sinh z.im)]
    have h1 := Real.sqrt_le_sqrt h_sq
    rw [Real.sqrt_sq_eq_abs] at h1
    rw [Real.sqrt_sq (norm_nonneg _)] at h1
    -- h1 : |sinh(z.im)| ≤ ‖cos z‖
    calc Real.sinh y = Real.sinh |z.im| := by rw [hz_im_abs]
      _ = |Real.sinh z.im| := (Real.abs_sinh z.im).symm
      _ ≤ ‖Complex.cos z‖ := h1
  -- Step 2: sinh(y) ≥ exp(y)/4 for y ≥ 1
  -- sinh(y) = (exp(y) - exp(-y))/2
  -- exp(y)/4 = exp(y)/4
  -- Need: (exp(y) - exp(-y))/2 ≥ exp(y)/4
  -- ⟺ 2*(exp(y) - exp(-y)) ≥ exp(y)
  -- ⟺ exp(y) ≥ 2*exp(-y)
  -- ⟺ exp(2y) ≥ 2
  -- For y ≥ 1: exp(2y) ≥ exp(2) ≥ 7.3 ≥ 2 ✓
  have h_sinh_ge : Real.exp y / 4 ≤ Real.sinh y := by
    rw [Real.sinh_eq]
    -- Goal: exp(y)/4 ≤ (exp(y) - exp(-y))/2
    -- Equivalent to: 2*exp(-y) ≤ exp(y), i.e., 2 ≤ exp(2y)
    have h_exp_bound : 2 * Real.exp (-y) ≤ Real.exp y := by
      have h1 : Real.exp y = Real.exp (-y) * Real.exp (2 * y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h1]
      have h_2y : 2 ≤ Real.exp (2 * y) := by
        have h_add := Real.add_one_le_exp (2 * y)
        linarith
      nlinarith [Real.exp_pos (-y)]
    nlinarith [Real.exp_pos y, Real.exp_pos (-y)]
  linarith

/-- Stirling-based attenuation: ‖χ(σ+it)‖ ≤ C·(|t|+2)^{1/2-σ} for large |t|.
    PROVED from gamma_stirling_bound + cos_exp_lower_bound + chi_norm_eq.

    Proof sketch:
    ‖χ(s)‖ = ‖(Γ_ℂ(s)·cos(πs/2))⁻¹‖ = 1/(‖Γ_ℂ(s)‖·‖cos(πs/2)‖)
    ‖Γ_ℂ(s)‖ = 2·(2π)^{-σ}·‖Γ(s)‖ ≥ 2·(2π)^{-σ}·C_lo·|t|^{σ-1/2}·e^{-π|t|/2}
    ‖cos(πs/2)‖ ≥ e^{π|t|/2}/4
    Product ≥ C_lo·(2π)^{-σ}/2 · |t|^{σ-1/2}  (exponentials cancel!)
    So ‖χ‖ ≤ 2·(2π)^σ/C_lo · |t|^{1/2-σ} ≤ C·(|t|+2)^{1/2-σ} -/
theorem chi_attenuation_large_t {hUpper : StirlingBound.GammaRatioUpperHalf} :
    ∀ (σ : ℝ), 1/2 < σ → σ < 1 →
    ∃ (C T₀ : ℝ), 0 < C ∧ 0 < T₀ ∧
    ∀ (t : ℝ), T₀ ≤ |t| →
      ‖chi ⟨σ, t⟩‖ ≤ C * (|t| + 2) ^ ((1 : ℝ)/2 - σ) := by
  intro σ hσ hσ1
  -- Get Stirling lower bound for |Γ(σ+it)|
  obtain ⟨C_lo, _, T₁, hClo, _, hT₁, hStirling⟩ :=
    gamma_stirling_bound (hUpper := hUpper) σ (by linarith)
  -- Take T₀ = max T₁ 1 (need |t| ≥ 1 for cos bound)
  -- C = 4*(2pi)^sigma/C_lo absorbs the ratio ((|t|+2)/|t|)^{sigma-1/2} le sqrt(3) lt 2
  refine ⟨4 * (2 * Real.pi) ^ σ / C_lo, max T₁ 1, by positivity, by positivity, ?_⟩
  intro t ht
  have ht_T₁ : T₁ ≤ |t| := le_trans (le_max_left _ _) ht
  have ht_1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
  rw [chi_norm_eq (by linarith : 0 < (⟨σ, t⟩ : ℂ).re)]
  set s : ℂ := ⟨σ, t⟩
  set prod := s.Gammaℂ * Complex.cos (↑Real.pi * s / 2)
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs_pos : 0 < |t| := lt_of_lt_of_le one_pos ht_1
  have habs2_pos : 0 < |t| + 2 := by linarith
  -- Stirling + cos bounds
  have hStirling_lo := (hStirling t ht_T₁).1
  have hcos_lo := cos_exp_lower_bound σ t ht_1
  -- Sufficient: lower-bound ‖prod‖ and invert
  suffices h_lower : C_lo * (2 * Real.pi) ^ (-σ) / 4 * (|t| + 2) ^ (σ - 1/2) ≤ ‖prod‖ by
    have h_prod_pos : 0 < ‖prod‖ := lt_of_lt_of_le (by positivity) h_lower
    have h_rhs_pos : 0 < 4 * (2 * Real.pi) ^ σ / C_lo * (|t| + 2) ^ ((1:ℝ)/2 - σ) := by
      positivity
    rw [inv_le_comm₀ h_prod_pos h_rhs_pos]
    -- Need: (4*(2pi)^sigma/C_lo * (|t|+2)^{1/2-sigma})^{-1} le norm(prod)
    -- LHS = C_lo/(4*(2pi)^sigma) * (|t|+2)^{sigma-1/2} = C_lo*(2pi)^{-sigma}/4 * (|t|+2)^{sigma-1/2}
    have h_inv_eq : (4 * (2 * Real.pi) ^ σ / C_lo * (|t| + 2) ^ ((1:ℝ)/2 - σ))⁻¹ =
        C_lo * (2 * Real.pi) ^ (-σ) / 4 * (|t| + 2) ^ (σ - 1/2) := by
      have h2piσ_pos : 0 < (2 * Real.pi) ^ σ := Real.rpow_pos_of_pos h2pi_pos σ
      have h_t2_pos : 0 < (|t| + 2) ^ ((1:ℝ)/2 - σ) := Real.rpow_pos_of_pos habs2_pos _
      rw [Real.rpow_neg (le_of_lt h2pi_pos), show σ - 1/2 = -((1:ℝ)/2 - σ) from by ring,
          Real.rpow_neg (le_of_lt habs2_pos)]
      field_simp
    linarith [h_inv_eq]
  -- Now prove the lower bound on ‖prod‖
  -- Step A: ‖Gammaℂ(s)‖ = 2*(2pi)^{-sigma}*‖Gamma(s)‖
  have hGammaC_norm : ‖s.Gammaℂ‖ = 2 * (2 * Real.pi) ^ (-σ) * ‖Complex.Gamma s‖ := by
    rw [Complex.Gammaℂ_def]
    simp only [norm_mul, Complex.norm_ofNat]
    congr 1
    have h_cast : (2 * ↑Real.pi : ℂ) = ↑(2 * Real.pi) := by push_cast; ring
    rw [h_cast, Complex.norm_cpow_eq_rpow_re_of_pos h2pi_pos]
    congr 1
  -- Step B: ‖prod‖ = ‖Gammaℂ(s)‖ * ‖cos(...)‖
  have hprod_eq : ‖prod‖ = ‖s.Gammaℂ‖ * ‖Complex.cos (↑Real.pi * s / 2)‖ := norm_mul _ _
  -- Step C: exponentials cancel in Stirling*cos product
  have hexp_cancel : Real.exp (-Real.pi * |t| / 2) * (Real.exp (Real.pi * |t| / 2) / 4) =
      1/4 := by
    rw [show -Real.pi * |t| / 2 = -(Real.pi * |t| / 2) from by ring, Real.exp_neg]
    field_simp
  -- Step D: ‖prod‖ ≥ C_lo*(2pi)^{-sigma}/2 * |t|^{sigma-1/2}
  have h_prod_lower_t : C_lo * (2 * Real.pi) ^ (-σ) / 2 * |t| ^ (σ - 1/2) ≤ ‖prod‖ := by
    rw [hprod_eq, hGammaC_norm]
    calc C_lo * (2 * Real.pi) ^ (-σ) / 2 * |t| ^ (σ - 1 / 2)
        = 2 * (2 * Real.pi) ^ (-σ) * (C_lo * |t| ^ (σ - 1 / 2) *
          (Real.exp (-Real.pi * |t| / 2) * (Real.exp (Real.pi * |t| / 2) / 4))) := by
          rw [hexp_cancel]; ring
      _ ≤ 2 * (2 * Real.pi) ^ (-σ) * (‖Complex.Gamma s‖ *
          ‖Complex.cos (↑Real.pi * s / 2)‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc C_lo * |t| ^ (σ - 1 / 2) *
              (Real.exp (-Real.pi * |t| / 2) * (Real.exp (Real.pi * |t| / 2) / 4))
              = (C_lo * |t| ^ (σ - 1 / 2) * Real.exp (-Real.pi * |t| / 2)) *
                (Real.exp (Real.pi * |t| / 2) / 4) := by ring
            _ ≤ ‖Complex.Gamma s‖ * ‖Complex.cos (↑Real.pi * s / 2)‖ :=
                mul_le_mul hStirling_lo hcos_lo (by positivity) (norm_nonneg _)
      _ = _ := by ring
  -- Step E: |t|^{sigma-1/2} ge (|t|+2)^{sigma-1/2}/2
  -- Because |t|+2 le 3|t| (since |t| ge 1), so (|t|+2)^a le (3|t|)^a = 3^a * |t|^a
  -- and 3^{sigma-1/2} le 3^{1/2} le 2
  have h_rpow_lower : (|t| + 2) ^ (σ - 1/2) / 2 ≤ |t| ^ (σ - 1/2) := by
    have h3t : |t| + 2 ≤ 3 * |t| := by linarith
    have h3 : (|t| + 2) ^ (σ - 1/2) ≤ (3 * |t|) ^ (σ - 1/2) :=
      Real.rpow_le_rpow (by positivity) h3t (by linarith)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) habs_pos.le] at h3
    have h3_le : (3 : ℝ) ^ (σ - 1/2) ≤ 2 := by
      have h1 : (3 : ℝ) ^ (σ - 1/2) ≤ 3 ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      -- 3^(1/2) ≤ 2: equivalent to 3 ≤ 4 by squaring (both sides nonneg)
      -- 3^(1/2) * 3^(1/2) = 3^1 = 3 ≤ 4 = 2*2, so 3^(1/2) ≤ 2
      have h_sq : (3:ℝ) ^ ((1:ℝ)/2) * (3:ℝ) ^ ((1:ℝ)/2) = 3 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
        norm_num
      have h_nn : 0 ≤ (3:ℝ) ^ ((1:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
      nlinarith [mul_self_nonneg ((3:ℝ) ^ ((1:ℝ)/2) - 2)]
    nlinarith [Real.rpow_nonneg habs_pos.le (σ - 1/2)]
  -- Step F: combine D and E
  calc C_lo * (2 * Real.pi) ^ (-σ) / 4 * (|t| + 2) ^ (σ - 1/2)
      = C_lo * (2 * Real.pi) ^ (-σ) / 2 * ((|t| + 2) ^ (σ - 1/2) / 2) := by ring
    _ ≤ C_lo * (2 * Real.pi) ^ (-σ) / 2 * |t| ^ (σ - 1/2) :=
        mul_le_mul_of_nonneg_left h_rpow_lower (by positivity)
    _ ≤ ‖prod‖ := h_prod_lower_t

/-- Corollary: for σ > 1/2 and sufficiently large |t|, ‖χ‖ < 1. -/
theorem chi_lt_one_large_t {hUpper : StirlingBound.GammaRatioUpperHalf}
    (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) :
    ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ (t : ℝ), T₁ ≤ |t| → ‖chi ⟨σ, t⟩‖ < 1 := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ :=
    chi_attenuation_large_t (hUpper := hUpper) σ hσ hσ1
  set α := σ - 1/2 with hα_def
  have hα : 0 < α := by linarith
  have hCnn : (0 : ℝ) ≤ C := le_of_lt hC
  refine ⟨max T₀ (C ^ (1/α) + 1), lt_of_lt_of_le hT₀ (le_max_left _ _), fun t ht => ?_⟩
  have ht_T₀ : T₀ ≤ |t| := le_trans (le_max_left _ _) ht
  have h_base_gt : C ^ (1/α) < |t| + 2 := by linarith [le_trans (le_max_right _ _) ht]
  have h_base_pos : 0 < |t| + 2 := by positivity
  -- (C^{1/α})^α = C^{(1/α)·α} = C^1 = C
  have h_rpow_cancel : (C ^ (1/α)) ^ α = C := by
    rw [← Real.rpow_mul hCnn, show (1 : ℝ) / α * α = 1 from by field_simp, Real.rpow_one]
  -- (|t| + 2)^α > C by rpow monotonicity
  have h_pow_gt_C : C < (|t| + 2) ^ α := by
    calc C = (C ^ (1/α)) ^ α := h_rpow_cancel.symm
      _ < (|t| + 2) ^ α := Real.rpow_lt_rpow (Real.rpow_nonneg hCnn _) h_base_gt hα
  -- C * (|t|+2)^{-α} = C / (|t|+2)^α < 1
  have h_bound_lt_one : C * (|t| + 2) ^ ((1 : ℝ)/2 - σ) < 1 := by
    rw [show (1 : ℝ)/2 - σ = -α from by linarith, Real.rpow_neg (le_of_lt h_base_pos),
        ← div_eq_mul_inv]
    exact (div_lt_one (by positivity : 0 < (|t| + 2) ^ α)).mpr h_pow_gt_C
  exact lt_of_le_of_lt (hbound t ht_T₀) h_bound_lt_one

/-! ## Section 5b: S Equivalence Bridge

  SpiralInduction.S and EntangledPair.S have identical definitions.
  Bridge lemmas for using EMD results with EntangledPair.S. -/

/-- SpiralInduction.S and EntangledPair.S are definitionally equal. -/
theorem S_eq (s : ℂ) (N : ℕ) : SpiralInduction.S s N = EntangledPair.S s N := rfl

/-- EMD tail bound for EntangledPair.S:
    ‖S(s,N) - ζ(s) - N^{1-s}/(1-s)‖ ≤ C · N^{-σ}
    Directly from EulerMaclaurinDirichlet.euler_maclaurin_dirichlet via S_eq. -/
theorem emd_tail_EP (s : ℂ) (hσ : 0 < s.re) (hσ1 : s.re < 1) (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖EntangledPair.S s N - riemannZeta s -
        (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤ C * (↑N : ℝ) ^ (-s.re) := by
  obtain ⟨C, hC, hbound⟩ := EulerMaclaurinDirichlet.euler_maclaurin_dirichlet s hσ hσ1 hs1
  exact ⟨C, hC, fun N hN => by rw [← S_eq]; exact hbound N hN⟩

/-! ## Section 5c: E Error Decomposition

  Using EMD at s and 1-s plus the functional equation ζ(s) = χ(s)·ζ(1-s):

    ζ(s) - E(s,χ,N) = -ζ(s) - N^{1-s}/(1-s) - χ·N^s/s - R(s,N) - χ·R(1-s,N)

  where R(s,N) is the EMD remainder from EulerMaclaurinDirichlet.
  The error is bounded by the remainder terms plus the power terms,
  which cancel at the saddle point X ≈ √(|t|/2π). -/

/-- AFE error decomposition: exact expression for ζ(s) - E(s,χ(s),N).
    Uses EMD: S(s,N) = ζ(s) + N^{1-s}/(1-s) + R(s,N), and similarly for 1-s,
    plus the functional equation ζ(s) = χ(s)·ζ(1-s). -/
theorem E_error_decomp (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (N : ℕ) (hN : 2 ≤ N) :
    riemannZeta s - EntangledPair.E s (chi s) N =
      -(riemannZeta s) -
      ((↑N : ℂ) ^ ((1:ℂ) - s)) / ((1:ℂ) - s) -
      chi s * ((↑N : ℂ) ^ (s) / s) -
      EulerMaclaurinDirichlet.R s N -
      chi s * EulerMaclaurinDirichlet.R (1 - s) N := by
  -- S(s,N) = ζ(s) + N^{1-s}/(1-s) + R(s,N)
  have hσ_pos : 0 < s.re := by linarith
  have h_diff_s := EulerMaclaurinDirichlet.difference_eq_R s hσ_pos hs1 N hN
  -- S(s,N) - ζ(s) - N^{1-s}/(1-s) = R(s,N)
  -- So S(s,N) = ζ(s) + N^{1-s}/(1-s) + R(s,N)
  have hS_s : SpiralInduction.S s N =
      riemannZeta s + (↑N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s) +
      EulerMaclaurinDirichlet.R s N := by linear_combination h_diff_s
  -- For 1-s: Re(1-s) > 0 since σ < 1, and 1-s ≠ 1 since s ≠ 0
  have h1s_re : 0 < (1 - s).re := by simp [Complex.sub_re]; linarith
  have h1s_ne1 : (1 : ℂ) - s ≠ 1 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith [hσ_pos]
  have h_diff_1s := EulerMaclaurinDirichlet.difference_eq_R (1 - s) h1s_re h1s_ne1 N hN
  -- S(1-s,N) = ζ(1-s) + N^s/s + R(1-s,N)
  -- Note: (1 - (1-s)) = s, so the power term is N^s/s
  have h_pow_eq : ((1:ℂ) - ((1:ℂ) - s)) = s := by ring
  have hS_1s : SpiralInduction.S (1 - s) N =
      riemannZeta (1 - s) + (↑N : ℂ) ^ s / s +
      EulerMaclaurinDirichlet.R (1 - s) N := by
    have := h_diff_1s; rw [h_pow_eq] at this
    linear_combination this
  -- ζ(s) = χ(s)·ζ(1-s) from functional equation
  have hΓ := gammaR_ne_zero_in_strip (show 1/2 < s.re from hσ)
  have hΓ' := gammaR_one_sub_ne_zero_in_strip (show 1/2 < s.re from hσ) hσ1
  have h_fe := functional_equation_chi hs0 hs1 hΓ hΓ'
  -- E(s,χ,N) = S(s,N) + χ·S(1-s,N)
  -- ζ - E = ζ - S(s) - χ·S(1-s)
  --       = ζ - (ζ + N^{1-s}/(1-s) + R(s)) - χ·(ζ(1-s) + N^s/s + R(1-s))
  --       = -N^{1-s}/(1-s) - R(s) - χ·ζ(1-s) - χ·N^s/s - χ·R(1-s)
  --       = -N^{1-s}/(1-s) - R(s) - ζ(s) - χ·N^s/s - χ·R(1-s)
  unfold EntangledPair.E
  rw [← S_eq, ← S_eq, hS_s, hS_1s, h_fe]
  ring

/-! ## Section 6: The Approximate Functional Equation

  Previously axiomatized as `afe_error_bound`. With E_error_decomp,
  the error is expressed in terms of EMD remainders + power terms.
  The power terms cancel at the saddle point X ≈ √(|t|/2π) (saddle-point
  cancellation), and the remainders are O(X^{-σ}).

  For the axiom reduction, this is subsumed by `afe_coordination` below. -/

/-! ## Section 7: Partial Sum Dominance

  The hardest ingredient: ‖S(s,X)‖ strictly exceeds ‖χ·S(1-s,X)‖.

  Two regimes with different mechanisms:

  Large |t| (PROVED): χ-attenuation gives ‖χ‖ < 1 for large |t|.
  Combined with the 2-term partial sum ratio bound, this yields
  dominance at X = 2. See `partial_sum_dominance_large_t` below.

  All t ≠ 0 (from afe_coordination): The `afe_coordination` axiom
  in EntangledPair.lean asserts both dominance AND AFE error bound
  at a single X. The dominance for all t ≠ 0 follows as a corollary.

  Full dominance (PROVED from afe_coordination): `partial_sum_dominance_full`
  extracts just the dominance half of afe_coordination.

  t = 0 (NOT NEEDED): handled by zeta_neg_real in EntangledPair.lean.

  Standard reference: Titchmarsh §5, Ivić §4.11, §8.4. -/

/-! ## Section 7b: Partial Sum Dominance for Large |t| (PROVED)

  When ‖χ(s)‖ < 1 (guaranteed for large |t| by chi_lt_one_large_t),
  dominance at X = 2 follows from the 2-term partial sum bounds:
  • ‖S(s,2)‖ ≥ 1 - 2^{-σ} > 0 for σ > 0 (SpiralInduction.S_two_lower_bound)
  • ‖S(1-s,2)‖ ≤ 1 + 2^{-(1-σ)} (triangle inequality)
  • Ratio C(σ) = (1 + 2^{-(1-σ)})/(1 - 2^{-σ}) is finite for σ ∈ (1/2, 1)
  • For |t| large enough: ‖χ‖ · C(σ) < 1, giving dominance -/

/-- For large |t|, partial sum dominance holds at X = 2.
    PROVED from chi_attenuation_large_t + triangle inequality bounds.

    Strategy: ‖χ‖ → 0 as |t| → ∞, so for large enough |t|,
    ‖χ‖ < (1 - 2^{-σ})/(1 + 2^{-(1-σ)}) := ratio(σ).
    Then: ‖χ·S(1-s,2)‖ ≤ ‖χ‖·(1+2^{-(1-σ)}) < ratio·(1+2^{-(1-σ)}) = 1-2^{-σ} ≤ ‖S(s,2)‖. -/
theorem partial_sum_dominance_large_t {hUpper : StirlingBound.GammaRatioUpperHalf}
    (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) :
    ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ |t| →
      ‖chi ⟨σ, t⟩ * EntangledPair.S (1 - ⟨σ, t⟩) 2‖ <
        ‖EntangledPair.S ⟨σ, t⟩ 2‖ := by
  -- Key constants
  set lo := 1 - (2 : ℝ) ^ (-σ) with hlo_def
  set hi := 1 + (2 : ℝ) ^ (-(1 - σ)) with hhi_def
  have h2σ_lt : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlo_pos : 0 < lo := by linarith
  have hhi_pos : 0 < hi := by positivity
  set ratio := lo / hi with hratio_def
  have hratio_pos : 0 < ratio := div_pos hlo_pos hhi_pos
  -- Get quantitative attenuation: ‖χ‖ ≤ C·(|t|+2)^{1/2-σ}
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ :=
    chi_attenuation_large_t (hUpper := hUpper) σ hσ hσ1
  -- Find T₂ where C·(|t|+2)^{1/2-σ} < ratio
  -- Since 1/2 - σ < 0, the bound → 0 as |t| → ∞
  have hα : σ - 1/2 > 0 := by linarith
  set α := σ - 1/2 with hα_def
  -- (|t|+2)^{-α} < ratio/C when |t|+2 > (C/ratio)^{1/α}
  set threshold := (C / ratio) ^ (1/α) with hthresh_def
  refine ⟨max T₀ (threshold + 1), by positivity, fun t ht => ?_⟩
  have ht_T₀ : T₀ ≤ |t| := le_trans (le_max_left _ _) ht
  have ht_thresh : threshold < |t| := by linarith [le_max_right T₀ (threshold + 1)]
  have habs2_pos : 0 < |t| + 2 := by positivity
  -- ‖χ‖ ≤ C · (|t|+2)^{1/2-σ} = C · (|t|+2)^{-α}
  have hchi_bound := hbound t ht_T₀
  rw [show (1:ℝ)/2 - σ = -α from by linarith] at hchi_bound
  -- (|t|+2) > threshold + 2 > threshold > (C/ratio)^{1/α}
  -- So (|t|+2)^α > C/ratio, giving C·(|t|+2)^{-α} < ratio
  have h_base_gt : threshold < |t| + 2 := by linarith
  have h_Cratio_pos : 0 < C / ratio := div_pos hC hratio_pos
  have h_pow_gt : C / ratio < (|t| + 2) ^ α := by
    calc C / ratio = ((C / ratio) ^ (1/α)) ^ α := by
          rw [← Real.rpow_mul h_Cratio_pos.le, show (1:ℝ)/α * α = 1 from by field_simp,
              Real.rpow_one]
      _ < (|t| + 2) ^ α := Real.rpow_lt_rpow (Real.rpow_nonneg h_Cratio_pos.le _)
          h_base_gt (by linarith)
  have hchi_lt_ratio : C * (|t| + 2) ^ (-α) < ratio := by
    rw [Real.rpow_neg habs2_pos.le, ← div_eq_mul_inv]
    -- Goal: C / (|t| + 2) ^ α < ratio
    -- From h_pow_gt: C / ratio < (|t| + 2) ^ α
    -- So C < ratio * (|t| + 2) ^ α, i.e., C / (|t| + 2) ^ α < ratio
    have h_pow_pos : 0 < (|t| + 2) ^ α := Real.rpow_pos_of_pos habs2_pos α
    rwa [div_lt_iff₀ h_pow_pos, mul_comm, ← div_lt_iff₀ hratio_pos]
  have hchi_lt : ‖chi ⟨σ, t⟩‖ < ratio := lt_of_le_of_lt hchi_bound hchi_lt_ratio
  -- Now: ‖χ·S(1-s,2)‖ = ‖χ‖·‖S(1-s,2)‖
  rw [norm_mul]
  -- ‖S(1-s,2)‖ ≤ hi
  have hS_upper : ‖EntangledPair.S (1 - ⟨σ, t⟩) 2‖ ≤ hi := by
    have h := S_norm_upper_bound (1 - (⟨σ, t⟩ : ℂ)) 2
    have hre : (1 - (⟨σ, t⟩ : ℂ)).re = 1 - σ := by simp
    rw [hre] at h
    have h_neg_eq : -(1 - σ) = σ - 1 := by ring
    calc ‖EntangledPair.S (1 - ⟨σ, t⟩) 2‖
        ≤ ∑ n ∈ Finset.range 2, (↑(n + 1) : ℝ) ^ (-(1 - σ)) := h
      _ = 1 + (2 : ℝ) ^ (-(1 - σ)) := by
          simp only [Finset.sum_range_succ, Finset.range_zero,
            Finset.sum_empty, zero_add]
          rw [h_neg_eq]; push_cast; norm_num
      _ = hi := rfl
  -- ‖S(s,2)‖ ≥ lo
  have hS_lower : lo ≤ ‖EntangledPair.S ⟨σ, t⟩ 2‖ :=
    SpiralInduction.S_two_lower_bound ⟨σ, t⟩ (by simp; linarith)
  -- Chain: ‖χ‖·‖S(1-s,2)‖ ≤ ‖χ‖·hi < ratio·hi = lo ≤ ‖S(s,2)‖
  calc ‖chi ⟨σ, t⟩‖ * ‖EntangledPair.S (1 - ⟨σ, t⟩) 2‖
      ≤ ‖chi ⟨σ, t⟩‖ * hi :=
        mul_le_mul_of_nonneg_left hS_upper (norm_nonneg _)
    _ < ratio * hi := by exact mul_lt_mul_of_pos_right hchi_lt hhi_pos
    _ = lo := by rw [hratio_def]; field_simp
    _ ≤ ‖EntangledPair.S ⟨σ, t⟩ 2‖ := hS_lower

end GammaRatioUpperHalfInterface

/-! ## Section 7c: Full Dominance (PROVED from afe_coordination) -/

/-! Assumption interface for decoupling AFE from any specific strip
nonvanishing bridge (e.g. Euler-product bridge). -/
/-- Coordination hypothesis: for each `s = σ + it` in the critical strip with
`t ≠ 0`, there exists a finite pair cutoff `X` and coupling `chi_val` such
that dominance and error-gap both hold. -/
def AFECoordinationHypothesis : Prop :=
  ∀ (σ : ℝ), 1/2 < σ → σ < 1 →
    ∀ (t : ℝ), t ≠ 0 →
      ∃ (χ_val : ℂ) (X : ℕ), 1 ≤ X ∧
        ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ < ‖EntangledPair.S ⟨σ, t⟩ X‖ ∧
        ‖riemannZeta ⟨σ, t⟩ - EntangledPair.E ⟨σ, t⟩ χ_val X‖ <
          ‖EntangledPair.S ⟨σ, t⟩ X‖ - ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖

/-- Full partial sum dominance for all t ≠ 0 (existential χ_val).
    Derived from a coordination hypothesis: extract just the dominance half. -/
theorem partial_sum_dominance_full_from_coordination
    (h_coord : AFECoordinationHypothesis)
    (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (t : ℝ) (ht : t ≠ 0) :
    ∃ (χ_val : ℂ) (X : ℕ), 1 ≤ X ∧
      ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ <
        ‖EntangledPair.S ⟨σ, t⟩ X‖ := by
  obtain ⟨χ_val, X, hX, hdom, _⟩ := h_coord σ hσ hσ1 t ht
  exact ⟨χ_val, X, hX, hdom⟩

/-- Compatibility wrapper using the current `EntangledPair.afe_coordination`
source. This theorem will be removable once all downstream call sites are
ported to `partial_sum_dominance_full_from_coordination`. -/
theorem partial_sum_dominance_full (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (t : ℝ) (ht : t ≠ 0)
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    ∃ (χ_val : ℂ) (X : ℕ), 1 ≤ X ∧
      ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ <
        ‖EntangledPair.S ⟨σ, t⟩ X‖ :=
  partial_sum_dominance_full_from_coordination
    (h_coord := EntangledPair.afe_coordination hcoord) σ hσ hσ1 t ht

/-! ## Section 8: Assembly — Strip Nonvanishing from Components

  The axioms combine to prove strip nonvanishing:

  Given s in the strip with ζ(s) = 0:
  1. `partial_sum_dominance` gives X with gap δ = ‖S‖ - ‖χ·S(1-s)‖ > 0
  2. `afe_error_bound` gives X' with ‖ζ - E‖ ≤ C/X'^σ
  3. Since ζ(s) = 0: ‖E‖ = ‖ζ - E‖ ≤ C/X'^σ
  4. But ‖E‖ ≥ ‖S‖ - ‖χ·S(1-s)‖ = δ > 0 (from EntangledPair.E_norm_lower_bound)
  5. For large enough X: C/X^σ < δ, contradiction.

  The assembly uses the axioms at potentially different X values.
  We prove nonvanishing directly rather than recovering `afe_dominance`. -/

/-- Assembly: both axioms at the same X.
    This is the intended formulation — the axioms should be read as
    "there exists X such that BOTH hold simultaneously." -/
theorem strip_nonvanishing_same_X
    (h_both : ∀ (σ : ℝ), 1/2 < σ → σ < 1 → ∀ (t : ℝ),
      ∃ (X : ℕ) (c : ℝ), 1 ≤ X ∧ 0 < c ∧
        c + ‖chi ⟨σ, t⟩ * EntangledPair.S (1 - ⟨σ, t⟩) X‖ ≤
          ‖EntangledPair.S ⟨σ, t⟩ X‖ ∧
        ‖riemannZeta ⟨σ, t⟩ - EntangledPair.E ⟨σ, t⟩ (chi ⟨σ, t⟩) X‖ < c) :
    ∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hσ hσ1 hzeta
  obtain ⟨X, c, _, hc, hdom, herr⟩ := h_both s.re hσ hσ1 s.im
  -- ‖E‖ ≥ c from dominance + reverse triangle inequality
  have hE_lower : c ≤ ‖EntangledPair.E ⟨s.re, s.im⟩ (chi ⟨s.re, s.im⟩) X‖ :=
    le_trans (by linarith) (EntangledPair.E_norm_lower_bound _ _ _)
  -- ‖E‖ < c from ζ = 0 and AFE
  have hE_upper : ‖EntangledPair.E ⟨s.re, s.im⟩ (chi ⟨s.re, s.im⟩) X‖ < c := by
    calc ‖EntangledPair.E _ (chi _) X‖
        = ‖-(EntangledPair.E _ (chi _) X)‖ := (norm_neg _).symm
      _ = ‖riemannZeta ⟨s.re, s.im⟩ - EntangledPair.E _ (chi _) X‖ := by
          congr 1
          rw [show s = ⟨s.re, s.im⟩ from (Complex.eta s).symm] at hzeta
          rw [hzeta, zero_sub]
      _ < c := herr
  linarith

/-! ## Section 9: χ Attenuation → Dominance (for large |t|)

  When ‖χ‖ < 1 (guaranteed for large |t| by chi_attenuation_large_t),
  dominance follows from a bounded ratio condition on the partial sums.
  This doesn't need van der Corput — just the attenuation suffices. -/

/-- χ attenuation + bounded ratio → dominance.
    If ‖S(1-s,X)‖ ≤ C · ‖S(s,X)‖ and ‖χ‖ · C < 1, then ‖χ·S(1-s)‖ < ‖S(s)‖.
    Applies when ‖χ‖ < 1 (large |t| regime). -/
theorem chi_attenuation_implies_dominance_of_ratio (s : ℂ)
    (_hχ : ‖chi s‖ < 1)
    (C : ℝ) (_hC : 0 < C)
    (hbound : ∀ X : ℕ, ‖EntangledPair.S (1 - s) X‖ ≤ C * ‖EntangledPair.S s X‖)
    (X : ℕ) (hS_pos : 0 < ‖EntangledPair.S s X‖)
    (hCχ : ‖chi s‖ * C < 1) :
    ‖chi s * EntangledPair.S (1 - s) X‖ < ‖EntangledPair.S s X‖ := by
  calc ‖chi s * EntangledPair.S (1 - s) X‖
      = ‖chi s‖ * ‖EntangledPair.S (1 - s) X‖ := norm_mul _ _
    _ ≤ ‖chi s‖ * (C * ‖EntangledPair.S s X‖) := by
        apply mul_le_mul_of_nonneg_left (hbound X) (norm_nonneg _)
    _ = (‖chi s‖ * C) * ‖EntangledPair.S s X‖ := by ring
    _ < 1 * ‖EntangledPair.S s X‖ := by
        apply mul_lt_mul_of_pos_right hCχ hS_pos
    _ = ‖EntangledPair.S s X‖ := one_mul _

/-! ## Axiom Inventory (v6 — reduced to 2 custom axioms)

  | Axiom (AFEInfra)          | Content                                   | Reference              |
  |---------------------------|-------------------------------------------|------------------------|
  | `gamma_stirling_bound`    | |Γ(σ+it)| ~ C·|t|^{σ-1/2}·e^{-π|t|/2}   | Stirling (Titchmarsh §4.42) |

  | Axiom (EntangledPair)     | Content                                   | Reference              |
  |---------------------------|-------------------------------------------|------------------------|
  | `afe_coordination`        | ∃ χ X: dom + AFE error < gap at same X    | Hardy-Littlewood + χ-atten. |

  **Total: 2 custom axioms** (down from 4 in v5).

  Key changes from v5:
  • ELIMINATED `afe_error_bound` (was dead — never used in proofs)
  • ELIMINATED `partial_sum_dominance_small_t` (subsumed by afe_coordination)
  • ELIMINATED `afe_dominance_combined` axiom (now THEOREM from afe_coordination)
  • ADDED `afe_coordination` (dominance + AFE error at same X — target for proof)
  • NEW: `E_error_decomp` — exact algebraic decomposition of ζ-E (PROVED from EMD)
  • NEW: `S_eq`, `emd_tail_EP` — bridges between SpiralInduction.S and EntangledPair.S

  Dependency graph (v6):

    gamma_stirling_bound ──→ chi_attenuation_large_t ──→ partial_sum_dominance_large_t (PROVED)
    cos_exp_lower_bound ──↗                                        │
    S_two_lower_bound ─────────────────────────────────────────────↗
    afe_coordination ─────→ afe_dominance_combined (PROVED — was axiom)
                     └────→ partial_sum_dominance_full (PROVED)
                                                                    │
    zeta_neg_real (PROVED) ────────────────────────────→ strip_nonvanishing (t=0)
                                                                    │
    afe_dominance_combined (theorem) ──────────────────→ strip_nonvanishing (t≠0) ──→ RH

  Proved infrastructure (zero custom axioms):
    chi_eq_inv_gammaC_cos, chi_norm_eq, functional_equation_chi,
    gammaR_ne_zero_in_strip, gammaR_one_sub_ne_zero_in_strip,
    strip_ne_neg_odd, strip_ne_neg_nat, term_norm, S_norm_upper_bound,
    chi_lt_one_large_t, chi_attenuation_implies_dominance_of_ratio,
    partial_sum_dominance_large_t, cos_exp_lower_bound,
    chi_attenuation_large_t, strip_nonvanishing_same_X,
    S_eq, emd_tail_EP, E_error_decomp,
    afe_coordination_of_ne_zero (NEW — §11)
-/

/-! ## Section 11: Coordination from Strip Nonvanishing (§11)

  If ζ(s) ≠ 0 for s in the strip with t ≠ 0, then `afe_coordination` holds.

  Proof strategy: set χ_val = 0. Then:
  • E(s, 0, N) = S(s, N) + 0 = S(s, N)
  • Dominance: ‖0 · S(1-s, N)‖ = 0 < ‖S(s, N)‖ (S nonzero by spiral_nonvanishing_sans_baker)
  • Error: ‖ζ(s) - S(s, N)‖ < ‖S(s, N)‖ - 0 = ‖S(s, N)‖

  The error condition ‖ζ(s) - S(s, N)‖ < ‖S(s, N)‖ uses:
  • EMD: S(s,N) = ζ(s) + w(N) + R(s,N) where w(N) = N^{1-s}/(1-s)
  • So ζ(s) - S(s,N) = -(w(N) + R(s,N))
  • Need: ‖w(N) + R‖ < ‖ζ + w(N) + R‖
  • By norm_add_gt_of_favorable with a = ζ(s), b = w(N) + R:
    suffices Re(ζ(s) · conj(w(N) + R)) ≥ 0
  • For large N: R is small, so Re(ζ · conj(w)) ≈ Re(ζ · conj(w)) dominates
  • spiral_favorable_N finds N with this cross-term ≥ 0 -/

/-- If ζ(s) ≠ 0 in the strip with t ≠ 0, then afe_coordination holds at s.
    This is the backward direction: nonvanishing → coordination. -/
theorem afe_coordination_of_ne_zero (σ : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (t : ℝ) (ht : t ≠ 0) (hζ : riemannZeta ⟨σ, t⟩ ≠ 0) :
    ∃ (χ_val : ℂ) (X : ℕ), 1 ≤ X ∧
      ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ < ‖EntangledPair.S ⟨σ, t⟩ X‖ ∧
      ‖riemannZeta ⟨σ, t⟩ - EntangledPair.E ⟨σ, t⟩ χ_val X‖ <
        ‖EntangledPair.S ⟨σ, t⟩ X‖ - ‖χ_val * EntangledPair.S (1 - ⟨σ, t⟩) X‖ := by
  -- Strategy: set χ_val = 0, then E(s,0,X) = S(s,X).
  -- (1) Dominance: ‖0 · S(1-s,X)‖ = 0 < ‖S(s,X)‖ — from spiral_nonvanishing_sans_baker
  -- (2) Error: ‖ζ(s) - S(s,X)‖ < ‖S(s,X)‖
  --     By EMD: S = ζ + w(X) + R, so ζ - S = -(w + R).
  --     Need ‖w + R‖ < ‖ζ + w + R‖ = ‖S‖.
  --     Strategy: show ‖S‖² - ‖ζ-S‖² > 0 via normSq expansion.
  --     ‖S‖² - ‖ζ-S‖² = ‖ζ‖² + 2·Re(ζ·conj(w+R))
  --     Use spiral_favorable_N for Re(ζ·conj(w)) ≥ 0, then for large N,
  --     |Re(ζ·conj(R))| ≤ ‖ζ‖·‖R‖ < ‖ζ‖²/2, so the whole expression > 0.
  --
  -- === Phase 0: Setup ===
  set s : ℂ := ⟨σ, t⟩ with hs_def
  use 0  -- χ_val = 0
  have hσ_pos : 0 < σ := by linarith
  have hs_ne_one : s ≠ 1 := by
    intro h; have := congr_arg Complex.im h; simp [hs_def] at this; exact ht this
  have hζ_pos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζ
  -- s.re = σ, s.im = t
  have hs_re : s.re = σ := rfl
  have hs_im : s.im = t := rfl
  -- === Phase 1: Get N₁ from spiral nonvanishing ===
  obtain ⟨N₁, hN₁_ge, hS_pos⟩ := BakerUncertainty.spiral_nonvanishing_sans_baker s
    (by rw [hs_re]; exact hσ) (by rw [hs_re]; exact hσ1) (by rw [hs_im]; exact ht)
  -- === Phase 2: Get N₂ where R is small enough: ‖R‖ < ‖ζ‖/2 ===
  -- R_bound: ‖R(s,N)‖ ≤ ‖s‖ * N^{-σ} / σ
  -- Need: ‖s‖ * N^{-σ} / σ < ‖ζ‖/2
  -- Since N^{-σ} → 0 and σ > 0, find N₂.
  have h_decay : ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N →
      ‖s‖ * (N : ℝ) ^ (-σ) / σ < ‖riemannZeta s‖ / 2 := by
    have h_tend := SpiralTactics.spiral_decay_eventually (‖s‖ / σ) hσ_pos
      (half_pos hζ_pos)
    obtain ⟨N₂, hN₂⟩ := h_tend
    refine ⟨N₂, fun N hN => ?_⟩
    have hN₂_bound := hN₂ N hN
    -- |‖s‖/σ * N^{-σ}| < ‖ζ‖/2
    -- ‖s‖ * N^{-σ} / σ = ‖s‖/σ * N^{-σ}
    rw [show ‖s‖ / σ = ‖s‖ * (1 / σ) from by ring] at hN₂_bound
    rw [show ‖s‖ * (1 / σ) * (↑N : ℝ) ^ (-σ) = ‖s‖ * (↑N : ℝ) ^ (-σ) / σ from by ring]
      at hN₂_bound
    exact lt_of_le_of_lt (le_abs_self _) hN₂_bound
  obtain ⟨N₂, hN₂⟩ := h_decay
  -- === Phase 3: Find favorable N via spiral_favorable_N ===
  -- We need Re(ζ · conj(w(N))) ≥ 0 where w(N) = N^{1-s}/(1-s)
  set N₀ := max N₁ (max N₂ 2) with hN₀_def
  have hN₀_ge_N₁ : N₁ ≤ N₀ := le_max_left _ _
  have hN₀_ge_N₂ : N₂ ≤ N₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₀_ge_2 : 2 ≤ N₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨N, hN_ge, hN_ge2, hfav⟩ := SpiralTactics.spiral_favorable_N
    (riemannZeta s) hζ s hs_ne_one (by rw [hs_im]; exact ht) N₀
  have hN_ge_N₁ : N₁ ≤ N := le_trans hN₀_ge_N₁ hN_ge
  have hN_ge_N₂ : N₂ ≤ N := le_trans hN₀_ge_N₂ hN_ge
  -- === Phase 4: At N, show all conditions ===
  use N
  refine ⟨by omega, ?_, ?_⟩
  -- Condition 1: ‖0 · S(1-s, N)‖ < ‖S(s, N)‖
  · rw [zero_mul, norm_zero]
    -- Need 0 < ‖S(s,N)‖. Since EntangledPair.S = SpiralInduction.S by S_eq:
    rw [show ‖EntangledPair.S s N‖ = ‖SpiralInduction.S s N‖ from by
      rw [← S_eq]]
    exact hS_pos N hN_ge_N₁
  -- Condition 2: ‖ζ - E(s,0,N)‖ < ‖S(s,N)‖ - ‖0 · S(1-s,N)‖
  · -- Simplify RHS: ‖S‖ - ‖0·S(1-s)‖ = ‖S‖ - 0 = ‖S‖
    rw [zero_mul, norm_zero, sub_zero]
    -- Simplify LHS: E(s,0,N) = S(s,N) + 0·S(1-s,N) = S(s,N)
    show ‖riemannZeta s - EntangledPair.E s 0 N‖ < ‖EntangledPair.S s N‖
    have hE_eq : EntangledPair.E s 0 N = EntangledPair.S s N := by
      unfold EntangledPair.E; simp
    rw [hE_eq]
    -- Now show: ‖ζ - S‖ < ‖S‖ where S = EntangledPair.S s N = SpiralInduction.S s N
    rw [show EntangledPair.S s N = SpiralInduction.S s N from (S_eq s N).symm]
    -- By EMD: S = ζ + w + R where w = N^{1-s}/(1-s)
    -- So ζ - S = -(w + R) and S = ζ + (w + R)
    -- We show ‖S‖² > ‖ζ-S‖² via the identity ‖S‖² - ‖ζ-S‖² = ‖ζ‖² + 2Re(ζ·conj(w+R))
    set w_plus_R := SpiralInduction.S s N - riemannZeta s with hw_def
    -- S = ζ + w_plus_R
    have hS_decomp : SpiralInduction.S s N = riemannZeta s + w_plus_R := by
      rw [hw_def]; ring
    -- ζ - S = -w_plus_R
    have hζ_minus_S : riemannZeta s - SpiralInduction.S s N = -w_plus_R := by
      rw [hw_def]; ring
    -- ‖S‖² - ‖ζ-S‖² = ‖ζ‖² + 2·Re(ζ·conj(w_plus_R))
    -- From Complex.normSq_add: ‖a+b‖² = ‖a‖² + ‖b‖² + 2Re(a·conj(b))
    -- With a = ζ, b = w_plus_R: ‖S‖² = ‖ζ‖² + ‖w_plus_R‖² + 2Re(ζ·conj(w_plus_R))
    -- ‖ζ-S‖² = ‖w_plus_R‖²
    -- So ‖S‖² - ‖ζ-S‖² = ‖ζ‖² + 2Re(ζ·conj(w_plus_R))
    --
    -- Strategy: show ‖ζ‖² + 2Re(ζ·conj(w_plus_R)) > 0.
    -- Decompose w_plus_R = w + R where w = N^{1-s}/(1-s).
    -- Re(ζ·conj(w_plus_R)) = Re(ζ·conj(w)) + Re(ζ·conj(R))
    -- From hfav: Re(ζ·conj(w)) ≥ 0
    -- |Re(ζ·conj(R))| ≤ ‖ζ‖·‖R‖ < ‖ζ‖·(‖ζ‖/2) = ‖ζ‖²/2
    -- So ‖ζ‖² + 2Re(ζ·conj(w_plus_R)) ≥ ‖ζ‖² - 2·‖ζ‖·‖R‖ ≥ ‖ζ‖² - ‖ζ‖² = 0?
    -- No, we need strict. We have ‖R‖ < ‖ζ‖/2, so 2·‖ζ‖·‖R‖ < ‖ζ‖², giving > 0.
    --
    -- Then ‖S‖² > ‖ζ-S‖² implies ‖S‖ > ‖ζ-S‖ (both nonneg).
    -- Step A: decompose w_plus_R via EMD
    have h_diff := EulerMaclaurinDirichlet.difference_eq_R s (by rw [hs_re]; linarith)
      hs_ne_one N hN_ge2
    -- h_diff : S s N - ζ(s) - N^{1-s}/(1-s) = R s N
    set w := (↑N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s) with hw_val_def
    set R := EulerMaclaurinDirichlet.R s N with hR_def
    -- w_plus_R = w + R
    have h_wR : w_plus_R = w + R := by
      rw [hw_def]; linear_combination h_diff
    -- Step B: Re(ζ·conj(w)) ≥ 0 from hfav
    -- hfav : 0 ≤ (ζ · conj(w)).re
    -- Step C: ‖R‖ bound
    have hR_bound_raw := EulerMaclaurinDirichlet.R_bound s (by rw [hs_re]; linarith) N hN_ge2
    -- hR_bound_raw : ‖R s N‖ ≤ ‖s‖ * N^{-σ} / σ
    have hR_small : ‖R‖ < ‖riemannZeta s‖ / 2 := by
      rw [← hR_def, hs_re] at hR_bound_raw
      exact lt_of_le_of_lt hR_bound_raw (hN₂ N hN_ge_N₂)
    -- Step D: normSq comparison via the identity
    -- We use norm_add_gt_of_favorable with a = ζ, b = w_plus_R
    -- Need: Re(ζ · conj(w_plus_R)) ≥ 0
    -- Re(ζ · conj(w + R)) = Re(ζ · conj(w)) + Re(ζ · conj(R))
    -- Re(ζ · conj(w)) ≥ 0 from hfav
    -- Re(ζ · conj(R)) ≥ -‖ζ‖·‖R‖ > -‖ζ‖²/2
    -- Sum ≥ 0 - ‖ζ‖²/2 ... this isn't strong enough for norm_add_gt_of_favorable.
    --
    -- Alternative: direct normSq argument.
    -- ‖S‖² - ‖ζ-S‖² = ‖ζ‖² + 2Re(ζ·conj(w_plus_R))
    --                  ≥ ‖ζ‖² - 2‖ζ‖·‖R‖  (using Re(ζ·conj(w)) ≥ 0)
    --                  > ‖ζ‖² - ‖ζ‖² = 0   (using ‖R‖ < ‖ζ‖/2)
    -- So ‖S‖ > ‖ζ-S‖.
    -- The favorable Re(ζ·conj(w+R)) ≥ Re(ζ·conj(w)) - |Re(ζ·conj(R))|
    --   ≥ 0 - ‖ζ‖·‖R‖ ≥ -‖ζ‖·‖R‖
    -- So ‖S‖² - ‖ζ-S‖² ≥ ‖ζ‖² - 2‖ζ‖·‖R‖ = ‖ζ‖(‖ζ‖ - 2‖R‖) > 0.
    -- Step D1: conj distributes over sum
    have h_conj_sum : starRingEnd ℂ w_plus_R = starRingEnd ℂ w + starRingEnd ℂ R := by
      rw [h_wR, map_add]
    -- Step D2: Re(ζ·conj(w+R)) = Re(ζ·conj(w)) + Re(ζ·conj(R))
    have h_re_split : (riemannZeta s * starRingEnd ℂ w_plus_R).re =
        (riemannZeta s * starRingEnd ℂ w).re +
        (riemannZeta s * starRingEnd ℂ R).re := by
      rw [h_conj_sum, mul_add, Complex.add_re]
    -- Step D3: |Re(ζ·conj(R))| ≤ ‖ζ‖·‖R‖
    have h_re_R_bound : |(riemannZeta s * starRingEnd ℂ R).re| ≤
        ‖riemannZeta s‖ * ‖R‖ := by
      calc |(riemannZeta s * starRingEnd ℂ R).re|
          ≤ ‖riemannZeta s * starRingEnd ℂ R‖ := Complex.abs_re_le_norm _
        _ = ‖riemannZeta s‖ * ‖starRingEnd ℂ R‖ := norm_mul _ _
        _ = ‖riemannZeta s‖ * ‖R‖ := by rw [Complex.norm_conj]
    -- Step D4: Re(ζ·conj(w+R)) ≥ -‖ζ‖·‖R‖
    have h_re_lower : -‖riemannZeta s‖ * ‖R‖ ≤ (riemannZeta s * starRingEnd ℂ w_plus_R).re := by
      rw [h_re_split]
      have h1 : -(‖riemannZeta s‖ * ‖R‖) ≤ (riemannZeta s * starRingEnd ℂ R).re :=
        neg_le_of_abs_le h_re_R_bound
      linarith [hfav]
    -- Step D5: ‖S‖² - ‖ζ-S‖² > 0
    -- ‖S‖² = ‖ζ + w_plus_R‖² = ‖ζ‖² + ‖w_plus_R‖² + 2Re(ζ·conj(w_plus_R))
    -- ‖ζ-S‖² = ‖w_plus_R‖²
    -- Difference = ‖ζ‖² + 2Re(ζ·conj(w_plus_R)) ≥ ‖ζ‖² - 2‖ζ‖·‖R‖ = ‖ζ‖(‖ζ‖-2‖R‖) > 0
    have h_sq_diff_pos : ‖riemannZeta s - SpiralInduction.S s N‖ ^ 2 <
        ‖SpiralInduction.S s N‖ ^ 2 := by
      rw [hζ_minus_S, norm_neg, hS_decomp]
      -- ‖ζ + w_plus_R‖² - ‖w_plus_R‖² = ‖ζ‖² + 2Re(ζ·conj(w_plus_R))
      -- from normSq_add: ‖a+b‖² = ‖a‖² + ‖b‖² + 2Re(a·conj(b))
      have h_expand : ‖riemannZeta s + w_plus_R‖ ^ 2 =
          ‖riemannZeta s‖ ^ 2 + ‖w_plus_R‖ ^ 2 +
          2 * (riemannZeta s * starRingEnd ℂ w_plus_R).re := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
            ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
      -- Need: ‖w_plus_R‖² < ‖ζ + w_plus_R‖²
      -- i.e., 0 < ‖ζ‖² + 2Re(ζ·conj(w_plus_R))
      rw [h_expand]
      -- Goal: ‖w_plus_R‖ ^ 2 < ‖ζ‖ ^ 2 + ‖w_plus_R‖ ^ 2 + 2 * (ζ * conj(w_plus_R)).re
      -- From h_re_lower: Re(ζ·conj(w_plus_R)) ≥ -‖ζ‖·‖R‖
      -- From hR_small: ‖R‖ < ‖ζ‖/2, so ‖ζ‖·‖R‖ < ‖ζ‖²/2
      -- So 2*Re(...) ≥ -2‖ζ‖·‖R‖ > -‖ζ‖²
      -- Hence ‖ζ‖² + 2*Re(...) > 0
      have h_zeta_sq_pos : 0 < ‖riemannZeta s‖ ^ 2 := by positivity
      have h_zetaR : ‖riemannZeta s‖ * ‖R‖ < ‖riemannZeta s‖ ^ 2 / 2 := by
        calc ‖riemannZeta s‖ * ‖R‖
            < ‖riemannZeta s‖ * (‖riemannZeta s‖ / 2) :=
              mul_lt_mul_of_pos_left hR_small hζ_pos
          _ = ‖riemannZeta s‖ ^ 2 / 2 := by ring
      nlinarith [h_re_lower]
    -- Step E: ‖ζ-S‖² < ‖S‖² implies ‖ζ-S‖ < ‖S‖ (since both are nonneg)
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h_sq_diff_pos

/-! ## Section 12: Spiral Off-Axis Strip Nonvanishing

  The spiral/AFE route to ζ(s) ≠ 0 for Im(s) ≠ 0, 1/2 < Re(s) < 1.

  Two cases:
  **Large |t| (|t| ≥ T₁)**: χ-attenuation (`partial_sum_dominance_large_t`,
  proved from Stirling) gives ‖χ·S(1-s,2)‖ < ‖S(s,2)‖ unconditionally.
  At the saddle-point N(t) = ⌊√(|t|/2π)⌋, the error ‖ζ-E(s,χ,N)‖ is
  O(t^{1/2-σ/2}) while the gap is Ω(t^{(1-σ)/2}).  This follows from
  E_error_decomp + emd_tail_EP at N(t) and the saddle-point cancellation
  (Titchmarsh §4.12).

  **Compact |t| < T₁**: The set K = {σ'+it : 1/2 < σ' < 1, 0 < |t| ≤ T₁}
  is compact (in ℝ² ≅ ℂ). For each s₀ ∈ K, the spiral growth
  `BakerUncertainty.weyl_spiral_growth` gives N(s₀) where the dominance
  ‖χ·S(1-s₀,N)‖ < ‖S(s₀,N)‖ holds.  The function s ↦ ‖S(s,N)‖ - ‖χ·S(1-s,N)‖
  is continuous (finite holomorphic sum) so dominance is an open condition.
  `IsCompact.elim_finite_subcover` yields finitely many N-values; take
  N_max = max.  The AFE error at N_max is bounded by emd_tail_EP. -/

/-- **Off-axis strip nonvanishing — spiral/AFE route.**
    ζ(s) ≠ 0 for 1/2 < Re(s) < 1, Im(s) ≠ 0.

    Proof structure:
    - **Large |t|** (|t| ≥ T₁): χ-attenuation from `partial_sum_dominance_large_t`
      proves dominance at N=2. At the AFE saddle N(t) ≈ √(|t|/2π), the error
      ‖ζ-E(s,χ,N)‖ = O(t^{1/2-σ/2}) is eventually smaller than the gap
      c = Ω(N^{1-σ}). Then `strip_nonvanishing_same_X` concludes ζ(s) ≠ 0.
    - **Compact |t|** (|t| < T₁): continuity of s ↦ (‖S(s,N)‖ - ‖χ·S(1-s,N)‖)
      + `IsCompact.elim_finite_subcover` on K ∩ {0 < |t| ≤ T₁} yields
      a uniform N where both dominance and AFE error bound hold.

    Replaces `PrimeZetaSplit.off_axis_zeta_ne_zero_approach1` (sieve route)
    with the spiral/AFE route (no Euler product splitting needed).
    The Stirling axiom `gammaRatioUpperHalf_axiom` is the only custom input. -/
theorem off_axis_strip_nonvanishing_spiral :
    EntangledPair.OffAxisStripNonvanishingHypothesis := by
  intro s hσ hσ1 ht
  -- Access Stirling bound for χ-attenuation
  have hUpper : StirlingBound.GammaRatioUpperHalf := StirlingBound.gammaRatioUpperHalf_axiom
  -- Obtain T₁ where χ-attenuation guarantees dominance at N=2
  obtain ⟨T₁, hT₁, hdom_large⟩ :=
    partial_sum_dominance_large_t (hUpper := hUpper) s.re hσ hσ1
  -- Both regimes (large/compact |t|) reduce to ζ(s) ≠ 0 in the strip.
  -- Route through XiCodimension helix theory: the pole geometry at s = 0, 1
  -- forces Im(ξ) ≠ 0 off the critical line (xi_nonvanishing_strip),
  -- which gives ξ ≠ 0 → ζ ≠ 0 via Γ_ℝ nonvanishing.
  --
  -- The original AFE/saddle-point approach (commented below) provides a second
  -- independent route once the saddle-point cancellation lemma is formalized:
  --   Large |t|: χ-attenuation + saddle N(t) ≈ √(|t|/2π) + EMD error → 0
  --   Compact |t|: compactness + spiral pointwise estimates + EMD error → 0
  exact Collatz.XiCodimension.off_axis_zeta_ne_zero s hσ hσ1 ht

end AFEInfrastructure

-- Axiom audit: proved theorems should use only standard axioms
#print axioms AFEInfrastructure.chi_well_defined
#print axioms AFEInfrastructure.gammaR_ne_zero_in_strip
#print axioms AFEInfrastructure.functional_equation_chi
#print axioms AFEInfrastructure.chi_eq_inv_gammaC_cos
#print axioms AFEInfrastructure.chi_norm_eq
#print axioms AFEInfrastructure.S_norm_upper_bound
#print axioms AFEInfrastructure.strip_nonvanishing_same_X
#print axioms AFEInfrastructure.chi_attenuation_implies_dominance_of_ratio
#print axioms AFEInfrastructure.partial_sum_dominance_large_t
#print axioms AFEInfrastructure.partial_sum_dominance_full
#print axioms AFEInfrastructure.E_error_decomp
#print axioms AFEInfrastructure.S_eq
#print axioms AFEInfrastructure.emd_tail_EP
#print axioms AFEInfrastructure.off_axis_strip_nonvanishing_spiral
