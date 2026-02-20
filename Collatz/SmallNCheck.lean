/-
  SmallNCheck.lean — Verified check for spiral non-vanishing
  ==========================================================

  This file implements a computational check for the condition:
    ∀ N < N₀, S(s,N) ≠ 0

  It defines a sufficient N₀ based on the Weyl spiral growth theorem.
  If N ≥ N₀, the spiral is guaranteed to be non-zero by asymptotic dominance.
  If N < N₀, we check it directly.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Collatz.WeylIntegration
import Collatz.EulerMaclaurinDirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace Collatz.SmallNCheck

open Complex

/-- The constant C(s) from EulerMaclaurinDirichlet. -/
noncomputable def C_explicit (s : ℂ) : ℝ := ‖s‖ / s.re + 1

/-- The sufficient N₀ bound.
    Condition: N > (‖1-s‖ * (‖ζ(s)‖ + C_explicit s)) ^ (1/(1-σ))
    Ensures: N^{1-σ}/‖1-s‖ > ‖ζ(s)‖ + C_explicit s * N^{-σ}
-/
noncomputable def sufficient_N0_real (s : ℂ) : ℝ :=
  (‖(1 - s : ℂ)‖ * (‖riemannZeta s‖ + C_explicit s)) ^ (1 / (1 - s.re))

/-- The integer N₀ to check up to. -/
noncomputable def sufficient_N0 (s : ℂ) : ℕ :=
  Nat.ceil (sufficient_N0_real s)

/-- Theorem: For N > sufficient_N0_real s, the spiral is non-zero. -/
theorem large_N_nonvanishing (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1) (hs1 : s ≠ 1)
    (N : ℕ) (hN : sufficient_N0_real s < N) (hN2 : 2 ≤ N) :
    SpiralInduction.S s N ≠ 0 := by
  have hσ_pos : 0 < s.re := by linarith
  have hEM := EulerMaclaurinDirichlet.euler_maclaurin_dirichlet_explicit s hσ_pos hσ1 hs1
  obtain ⟨hC_pos_orig, hEM_bound⟩ := hEM
  have hC_def : C_explicit s = ‖s‖ / s.re + 1 := rfl

  -- Define the components of S = main + ζ + error
  let main := (N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s)
  let zeta := riemannZeta s
  let error := SpiralInduction.S s N - zeta - main

  -- ‖S‖ ≥ ‖main‖ - ‖ζ‖ - ‖error‖  (reverse triangle inequality)
  have h_norm : ‖SpiralInduction.S s N‖ ≥ ‖main‖ - ‖zeta‖ - ‖error‖ := by
    have h_eq : SpiralInduction.S s N = main + zeta + error := by
      simp only [main, zeta, error]; ring
    rw [h_eq]
    -- ‖main + zeta + error‖ ≥ ‖main‖ - ‖zeta‖ - ‖error‖
    have h1 : ‖main + (zeta + error)‖ ≥ ‖main‖ - ‖zeta + error‖ := by
      have key := norm_sub_norm_le main (-(zeta + error))
      simp only [norm_neg, sub_neg_eq_add] at key
      linarith
    have h2 : ‖zeta + error‖ ≤ ‖zeta‖ + ‖error‖ := norm_add_le _ _
    rw [show main + zeta + error = main + (zeta + error) from by ring]
    linarith

  -- ‖error‖ ≤ C * N^{-σ}
  have h_err_bound : ‖error‖ ≤ C_explicit s * (N : ℝ) ^ (-s.re) := by
    rw [hC_def]; exact hEM_bound N hN2

  -- ‖main‖ = N^{1-σ} / ‖1-s‖
  have h_s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have h_abs_pos : 0 < ‖(1 - s : ℂ)‖ := norm_pos_iff.mpr h_s_ne
  have h_main_norm : ‖main‖ = (N : ℝ) ^ (1 - s.re) / ‖(1 - s : ℂ)‖ := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [Complex.sub_re, Complex.one_re]

  -- Key: N^(1-σ) > ‖1-s‖ * (‖ζ‖ + C)
  have h_suff : (N : ℝ) ^ (1 - s.re) > ‖(1 - s : ℂ)‖ * (‖zeta‖ + C_explicit s) := by
    have h_pow_pos : 0 < 1 - s.re := sub_pos.mpr hσ1
    have h_base_nn : 0 ≤ ‖(1 - s : ℂ)‖ * (‖riemannZeta s‖ + C_explicit s) := by positivity
    -- sufficient_N0_real s = base^(1/(1-σ)) < N, so base < N^(1-σ)
    have h_N0_eq : sufficient_N0_real s =
        (‖(1 - s : ℂ)‖ * (‖riemannZeta s‖ + C_explicit s)) ^ (1 / (1 - s.re)) := rfl
    have h_base_lt_N : (‖(1 - s : ℂ)‖ * (‖riemannZeta s‖ + C_explicit s)) ^ (1 / (1 - s.re)) < (N : ℝ) := by
      rwa [← h_N0_eq]
    have h_inversion : ‖(1 - s : ℂ)‖ * (‖riemannZeta s‖ + C_explicit s) < (N : ℝ) ^ (1 - s.re) := by
      -- Raise h_base_lt_N : base^(1/(1-σ)) < N to the power (1-σ)
      have step1 := Real.rpow_lt_rpow (by positivity) h_base_lt_N h_pow_pos
      -- step1 : (base^(1/(1-σ)))^(1-σ) < N^(1-σ)
      rwa [← Real.rpow_mul h_base_nn, one_div,
           inv_mul_cancel₀ (ne_of_gt h_pow_pos), Real.rpow_one] at step1
    exact h_inversion

  -- Abbreviations
  let main_norm : ℝ := ‖main‖
  let zeta_norm : ℝ := ‖zeta‖
  let err_norm : ℝ := ‖error‖
  let C : ℝ := C_explicit s

  -- main_norm > zeta_norm + C
  have h_main_gt : main_norm > zeta_norm + C := by
    have h_eq : main_norm * ‖(1 - s : ℂ)‖ = (N : ℝ) ^ (1 - s.re) := by
      show ‖main‖ * ‖(1 - s : ℂ)‖ = _
      rw [h_main_norm]; field_simp
    -- h_suff: N^(1-σ) > ‖1-s‖ * (zeta_norm + C)
    -- h_eq:   main_norm * ‖1-s‖ = N^(1-σ)
    -- So main_norm * ‖1-s‖ > ‖1-s‖ * (zeta_norm + C)
    -- Cancel ‖1-s‖ > 0 via nlinarith
    have h_suff2 : main_norm * ‖(1 - s : ℂ)‖ > ‖(1 - s : ℂ)‖ * (zeta_norm + C) := by
      rw [h_eq]; linarith
    nlinarith

  -- N^{-σ} < 1  (since N ≥ 2 and σ > 0)
  have h_pow_lt_one : (N : ℝ) ^ (-s.re) < 1 := by
    have h_one_lt_N : 1 < (N : ℝ) := by
      have : 2 ≤ (N : ℝ) := by exact_mod_cast hN2
      linarith
    have h_pow_gt : 1 < (N : ℝ) ^ s.re := Real.one_lt_rpow h_one_lt_N hσ_pos
    rw [Real.rpow_neg (by positivity)]
    rw [inv_lt_one_iff₀]
    right
    exact h_pow_gt

  -- C > 0
  have hC_pos : 0 < C := by unfold C C_explicit; positivity

  -- Final: ‖S‖ ≥ main_norm - zeta_norm - err_norm
  --            > C - err_norm
  --            ≥ C - C * N^{-σ}
  --            = C * (1 - N^{-σ}) > 0
  have h_pos : 0 < ‖SpiralInduction.S s N‖ := by
    have h1 : ‖SpiralInduction.S s N‖ ≥ main_norm - zeta_norm - err_norm := h_norm
    have h2 : main_norm - zeta_norm - err_norm > C - err_norm := by linarith
    have h3 : C - err_norm ≥ C - C * (N : ℝ) ^ (-s.re) := by linarith only [h_err_bound]
    have h4 : C * (1 - (N : ℝ) ^ (-s.re)) > 0 :=
      mul_pos hC_pos (sub_pos.mpr h_pow_lt_one)
    linarith

  exact norm_ne_zero_iff.mp (ne_of_gt h_pos)

/-- **Global Non-Vanishing**:
    If the spiral is non-zero for all small N ≤ N₀, then it's non-zero for all N. -/
theorem global_nonvanishing_of_small_check (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1) (hs1 : s ≠ 1)
    (h_small : ∀ n : ℕ, 2 ≤ n → n ≤ sufficient_N0 s → SpiralInduction.S s n ≠ 0) :
    ∀ N : ℕ, 2 ≤ N → SpiralInduction.S s N ≠ 0 := by
  intro N hN2
  by_cases h_le : N ≤ sufficient_N0 s
  · exact h_small N hN2 h_le
  · push_neg at h_le
    have hN_real : sufficient_N0_real s < N := by
      calc sufficient_N0_real s ≤ Nat.ceil (sufficient_N0_real s) := Nat.le_ceil _
        _ = sufficient_N0 s := rfl
        _ < N := by exact_mod_cast h_le
    exact large_N_nonvanishing s hσ hσ1 hs1 N hN_real hN2

end Collatz.SmallNCheck
