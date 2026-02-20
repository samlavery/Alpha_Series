/-
  EulerMaclaurinDirichlet.lean — Discharging euler_maclaurin_dirichlet from Abel Summation
  ========================================================================================

  Proves the Euler-Maclaurin asymptotic for Dirichlet partial sums:
    S(s,N) = ζ(s) + N^{1-s}/(1-s) + O(N^{-σ})

  from Mathlib's Abel summation formula + analytic continuation.

  Proof structure:
  1. Abel summation identity: S(s,N) = N^{1-s}/(1-s) + c(s) + R(s,N)
     where R(s,N) = -s·∫_N^∞ {t}·t^{-s-1} dt and c(s) = s/(s-1) + s·∫₁^∞ {t}·t^{-s-1} dt
  2. For Re(s) > 1: c(s) = ζ(s) (from zeta_eq_tsum_one_div_nat_cpow)
  3. c(s) is analytic on {Re(s) > 0} \ {1}, and so is ζ(s)
  4. By the identity principle: c(s) = ζ(s) for all Re(s) > 0, s ≠ 1
  5. Error bound: ‖R(s,N)‖ ≤ |s|/σ · N^{-σ}

  Axiom discharged: euler_maclaurin_dirichlet (in BakerUncertainty.lean)
  Dependencies: Mathlib.NumberTheory.AbelSummation, standard Mathlib analysis
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Collatz.SpiralInduction

open Finset Complex MeasureTheory Set Filter Topology

namespace EulerMaclaurinDirichlet

/-! ## Section 1: The Fractional Part Integral

  The key analytic object: I(s,N) = s·∫_N^∞ {t}·t^{-s-1} dt
  This converges absolutely for Re(s) > 0 since |{t}| ≤ 1 and
  ∫_N^∞ t^{-σ-1} dt = N^{-σ}/σ. -/

/-- The fractional part of a real number, as used in Euler-Maclaurin. -/
noncomputable def fract (t : ℝ) : ℝ := t - ⌊t⌋

/-- The tail integral: ∫_N^∞ {t}·t^{-s-1} dt.
    Converges for Re(s) > 0, with bound N^{-σ}/σ. -/
noncomputable def tailIntegral (s : ℂ) (N : ℕ) : ℂ :=
  ∫ t in Set.Ioi (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))

/-- The error term: R(s,N) = s · tailIntegral(s,N).
    This is S(s,N) - ζ(s) - N^{1-s}/(1-s) after Abel summation. -/
noncomputable def R (s : ℂ) (N : ℕ) : ℂ :=
  s * tailIntegral s N

/-- Bound on the tail integral: ‖∫_N^∞ {t}·t^{-s-1} dt‖ ≤ N^{-σ}/σ.
    Since |{t}| ≤ 1 and ∫_N^∞ t^{-σ-1} dt = N^{-σ}/σ. -/
-- The custom fract agrees with Int.fract
private theorem fract_eq_Int_fract (t : ℝ) : fract t = Int.fract t := by
  unfold fract Int.fract; rfl

theorem tailIntegral_bound (s : ℂ) (hσ : 0 < s.re) (N : ℕ) (hN : 2 ≤ N) :
    ‖tailIntegral s N‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  unfold tailIntegral
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hσ_neg : -(s.re + 1) < -1 := by linarith
  -- The bound function is integrable on Ioi N
  have h_integ : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hσ_neg hN_pos
  -- Pointwise norm bound
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi (N : ℝ))),
      ‖(fract t : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Set.mem_Ioi] at ht
    have ht_pos : (0 : ℝ) < t := lt_trans hN_pos ht
    rw [norm_mul]
    -- ‖(fract t : ℂ)‖ ≤ 1
    have h_fract_bound : ‖(fract t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
          abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    -- ‖(t : ℂ) ^ (-(s+1))‖ = t ^ (-(s.re+1))
    have h_cpow : ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
      simp [Complex.add_re, Complex.neg_re, Complex.one_re]
    calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
        ≤ 1 * t ^ (-(s.re + 1)) := by
          apply mul_le_mul h_fract_bound (le_of_eq h_cpow)
            (norm_nonneg _) zero_le_one
      _ = t ^ (-(s.re + 1)) := one_mul _
  -- ‖∫ f‖ ≤ ∫ ‖f‖ ≤ ∫ bound
  calc ‖∫ t in Ioi (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ∫ t in Ioi (N : ℝ), t ^ (-(s.re + 1)) := by
        exact norm_integral_le_of_norm_le h_integ h_bound
    _ = -(N : ℝ) ^ (-(s.re + 1) + 1) / (-(s.re + 1) + 1) := by
        exact integral_Ioi_rpow_of_lt hσ_neg hN_pos
    _ = (N : ℝ) ^ (-s.re) / s.re := by
        ring_nf

/-- Bound on the error term: ‖R(s,N)‖ ≤ ‖s‖ · N^{-σ}/σ. -/
theorem R_bound (s : ℂ) (hσ : 0 < s.re) (N : ℕ) (hN : 2 ≤ N) :
    ‖R s N‖ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  unfold R
  calc ‖s * tailIntegral s N‖
      = ‖s‖ * ‖tailIntegral s N‖ := norm_mul _ _
    _ ≤ ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := by
        apply mul_le_mul_of_nonneg_left (tailIntegral_bound s hσ N hN) (norm_nonneg _)
    _ = ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by ring

/-! ## Section 2: Abel Summation for Dirichlet Series

  Specializing Mathlib's Abel summation to c(n) = 1_{n≥1} and f(t) = t^{-s}. -/

/-- The Abel summation identity for Dirichlet partial sums.
    S(s,N) = N^{1-s}/(1-s) + s/(s-1) - s·∫₁^N {t}·t^{-s-1} dt

    This is a FINITE identity (no convergence issues), valid for all s ≠ 1.
    The minus sign comes from: Σf(n) = A(N)f(N) - ∫A(t)f'(t)dt, with
    A(t)=⌊t⌋=t-{t} and f'(t)=-s·t^{-(s+1)}, giving s∫⌊t⌋t^{-(s+1)} =
    s∫t^{-s} - s∫{t}t^{-(s+1)}. -/
-- Helper: cpow identity a^{1-s} = a * a^{-s} for a > 0
private theorem cpow_one_sub_eq (a : ℝ) (ha : 0 < a) (s : ℂ) :
    (↑a : ℂ) ^ ((1 : ℂ) - s) = (↑a : ℂ) * (↑a : ℂ) ^ (-s) := by
  have ha_ne : (↑a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ha)
  rw [show (1 : ℂ) - s = -s + 1 by ring, cpow_add _ _ ha_ne, cpow_one, mul_comm]

-- Helper: integral_cpow on [N, N+1] for t^{-s}
private theorem integral_cpow_neg_s (s : ℂ) (N : ℕ) (hN : 1 ≤ N) (hs1 : s ≠ 1) :
    ∫ (x : ℝ) in (↑N : ℝ)..(↑(N + 1) : ℝ), (↑x : ℂ) ^ (-s) =
      ((↑(N + 1) : ℂ) ^ (-s + 1) - (↑N : ℂ) ^ (-s + 1)) / (-s + 1) := by
  apply integral_cpow; right
  exact ⟨by simp only [ne_eq, neg_eq_iff_eq_neg, neg_neg]; exact hs1,
         by rw [Set.uIcc_of_le (by exact_mod_cast (show N ≤ N + 1 by omega) : (↑N : ℝ) ≤ ↑(N+1))]
            simp only [Set.mem_Icc, not_and_or, not_le]
            left; exact_mod_cast Nat.pos_of_ne_zero (by omega : N ≠ 0)⟩

-- Helper: integral_cpow on [N, N+1] for t^{-(s+1)}
private theorem integral_cpow_neg_succ (s : ℂ) (N : ℕ) (hN : 1 ≤ N) (hσ : 0 < s.re) :
    ∫ (x : ℝ) in (↑N : ℝ)..(↑(N + 1) : ℝ), (↑x : ℂ) ^ (-(s + 1)) =
      ((↑(N + 1) : ℂ) ^ (-s) - (↑N : ℂ) ^ (-s)) / (-s) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hσ
  have h_ne : -(s + 1) ≠ -1 := by
    intro h; apply hs0; have := neg_injective h; linear_combination this
  have h_notzero : (0 : ℝ) ∉ Set.uIcc (↑N : ℝ) (↑(N+1) : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast (show N ≤ N + 1 by omega) : (↑N : ℝ) ≤ ↑(N+1))]
    simp only [Set.mem_Icc, not_and_or, not_le]
    left; exact_mod_cast Nat.pos_of_ne_zero (by omega : N ≠ 0)
  have key := integral_cpow (a := (↑N : ℝ)) (b := (↑(N+1) : ℝ)) (r := -(s+1))
    (Or.inr ⟨h_ne, h_notzero⟩)
  simp only [show -(s + 1) + 1 = -s by ring] at key; exact key

-- Helper: the integral over Icc 1 1 vanishes (the set has measure zero)
private theorem integral_Icc_one_one (s : ℂ) :
    ∫ t in Set.Icc (1 : ℝ) (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 0 := by
  have : Set.Icc (1 : ℝ) 1 = {1} := Set.Icc_self 1
  rw [this]; simp

-- Helper: on [k, k+1] for k ≥ 1 (as naturals), fract(t) = t - k a.e.
-- This is because ⌊t⌋ = k for t ∈ [k, k+1) and the boundary {k+1} has measure 0
private theorem fract_eq_sub_on_Icc (k : ℕ) (_hk : 1 ≤ k) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ))),
      fract t = t - ↑k := by
  -- Strategy: prove on Ico k (k+1) where ⌊t⌋ = k, then extend by null set
  -- Icc = Ico ∪ {k+1} and {k+1} has measure 0
  -- Use: volume.restrict Icc ≤ volume.restrict Ico + volume.restrict {k+1}
  -- Since the property holds on Ico and {k+1} is null, it holds a.e. on Icc
  -- Lebesgue: Icc and Ico have the same restriction (differ by endpoint of measure 0)
  rw [show MeasureTheory.volume.restrict (Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ)) =
      MeasureTheory.volume.restrict (Set.Ico (↑k : ℝ) (↑(k + 1) : ℝ)) from
    (MeasureTheory.restrict_Ico_eq_restrict_Icc).symm]
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  simp only [Set.mem_Ico] at ht
  unfold fract
  -- Need: t - ↑⌊t⌋ = t - ↑k, i.e., ↑⌊t⌋ = ↑k (as ℝ)
  -- This follows from ⌊t⌋ = ↑k (as ℤ)
  have hfloor : ⌊t⌋ = (↑k : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  simp [hfloor]

-- Helper: the integral of fract*cpow on [k,k+1] equals ∫t^{-s} - k*∫t^{-(s+1)}
private theorem integral_fract_piece (s : ℂ) (_hσ : 0 < s.re) (_hs : s ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ),
      (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
    (∫ x in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑x : ℂ) ^ (-s)) -
     (↑k : ℂ) * (∫ x in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑x : ℂ) ^ (-(s + 1))) := by
  have hle : (↑k : ℝ) ≤ (↑(k + 1) : ℝ) := by exact_mod_cast (show k ≤ k + 1 by omega)
  have hk_pos : (0 : ℝ) < (↑k : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_slit : ∀ t ∈ Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
    fun t ht => Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
  -- Integrability lemmas
  have h_int_cpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
      (Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ)) :=
    (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
      h_slit).integrableOn_compact isCompact_Icc
  have h_int_ts : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s))
      (Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ)) :=
    (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
      h_slit).integrableOn_compact isCompact_Icc
  -- Step 1: Replace fract(t) with (t - k) a.e., then simplify
  -- Goal: ∫ Icc fract*cpow = ∫ a..b t^{-s} - k * ∫ a..b t^{-(s+1)}
  -- We show: fract(t)*t^{-(s+1)} = t^{-s} - k*t^{-(s+1)} a.e. on Icc
  have h_ae_eq : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ) →
      (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - (↑k : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    have h_fract := fract_eq_sub_on_Icc k hk
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_fract
    filter_upwards [h_fract] with t ht_fract ht_mem
    have ht_fract' := ht_fract ht_mem
    rw [ht_fract']
    -- (t - k) * t^{-(s+1)} = t * t^{-(s+1)} - k * t^{-(s+1)}
    -- and t * t^{-(s+1)} = t^{-s}
    have ht_ne : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (by linarith [ht_mem.1]))
    have h_mul : (↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1)) = (↑t : ℂ) ^ (-s) := by
      rw [show -(s + 1) = -s - 1 from by ring, show -s - (1 : ℂ) = -s + (-1) from by ring,
          cpow_add _ _ ht_ne, show (-1 : ℂ) = ((-1 : ℤ) : ℂ) from by norm_cast,
          cpow_intCast, zpow_neg_one]
      field_simp
    rw [show (↑(t - ↑k) : ℂ) = (↑t : ℂ) - (↑k : ℂ) from by push_cast; ring]
    rw [sub_mul, h_mul]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Icc h_ae_eq]
  -- Now: ∫ Icc (t^{-s} - k*t^{-(s+1)}) = ∫ Icc t^{-s} - ∫ Icc k*t^{-(s+1)}
  rw [MeasureTheory.integral_sub h_int_ts (h_int_cpow.const_mul _)]
  -- Convert set integrals to interval integrals
  -- ∫ Icc f = ∫ Ioc f = ∫ a..b f
  rw [show ∫ t in Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ), (↑t : ℂ) ^ (-s) =
      ∫ t in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑t : ℂ) ^ (-s) from by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]]
  rw [show ∫ t in Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ), (↑k : ℂ) * (↑t : ℂ) ^ (-(s + 1)) =
      (↑k : ℂ) * ∫ t in Set.Icc (↑k : ℝ) (↑(k + 1) : ℝ), (↑t : ℂ) ^ (-(s + 1)) from
    MeasureTheory.integral_const_mul _ _]
  congr 1
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]

-- Helper: split Icc 1 (k+1) = Icc 1 k ∪ Icc k (k+1) for the integral
-- and relate the piece on [k, k+1] where fract(t) = t - k
private theorem integral_Icc_succ_split (s : ℂ) (hσ : 0 < s.re) (hs : s ≠ 1)
    (k : ℕ) (hk : 2 ≤ k) :
    ∫ t in Set.Icc (1 : ℝ) (↑(k + 1) : ℝ),
      (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
    (∫ t in Set.Icc (1 : ℝ) (↑k : ℝ),
      (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
    ((∫ x in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑x : ℂ) ^ (-s)) -
     (↑k : ℂ) * (∫ x in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑x : ℂ) ^ (-(s + 1)))) := by
  -- Step 1: Icc 1 (k+1) = Icc 1 k ∪ Icc k (k+1)
  have h1k : (1 : ℝ) ≤ (↑k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hkk1 : (↑k : ℝ) ≤ (↑(k + 1) : ℝ) := by exact_mod_cast (show k ≤ k + 1 by omega)
  rw [← Set.Icc_union_Icc_eq_Icc h1k hkk1]
  -- Step 2: Split the integral using ae-disjointness (overlap is {k}, measure 0)
  have h_ae_disj : MeasureTheory.AEDisjoint MeasureTheory.volume
      (Set.Icc (1 : ℝ) ↑k) (Set.Icc (↑k) (↑(k+1))) := by
    rw [MeasureTheory.AEDisjoint]
    -- Icc 1 k ∩ Icc k (k+1) = {k}
    have : Set.Icc (1 : ℝ) ↑k ∩ Set.Icc (↑k) (↑(k+1)) ⊆ {(↑k : ℝ)} := by
      intro x ⟨hx1, hx2⟩; simp only [Set.mem_Icc] at hx1 hx2; simp; linarith
    exact measure_mono_null this (by simp)
  -- Integrability on compact Icc sets: continuous integrand (up to ae modification)
  have h_slit_1k : ∀ t ∈ Set.Icc (1 : ℝ) (↑k : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
    fun t ht => Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
  have h_slit_kk1 : ∀ t ∈ Set.Icc (↑k : ℝ) (↑(k+1) : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
    fun t ht => Complex.ofReal_mem_slitPlane.mpr (by
      have : (0 : ℝ) < (↑k : ℝ) := Nat.cast_pos.mpr (by omega); linarith [ht.1])
  have h_int_1k : IntegrableOn (fun t : ℝ =>
      (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Icc (1 : ℝ) (↑k : ℝ)) := by
    have h_cpow_int : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
        (Set.Icc (1 : ℝ) (↑k : ℝ)) :=
      (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        h_slit_1k).integrableOn_compact isCompact_Icc
    exact h_cpow_int.integrable.mono
      (((continuous_ofReal.measurable.comp
        (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
        ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
          h_slit_1k).aestronglyMeasurable measurableSet_Icc))
      (by filter_upwards with t; rw [norm_mul]
          calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
              ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                    abs_of_nonneg (Int.fract_nonneg t)]
                exact (Int.fract_lt_one t).le
            _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _)
  have h_int_kk1 : IntegrableOn (fun t : ℝ =>
      (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Icc (↑k : ℝ) (↑(k+1) : ℝ)) := by
    have h_cpow_int : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
        (Set.Icc (↑k : ℝ) (↑(k+1) : ℝ)) :=
      (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        h_slit_kk1).integrableOn_compact isCompact_Icc
    exact h_cpow_int.integrable.mono
      (((continuous_ofReal.measurable.comp
        (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
        ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
          h_slit_kk1).aestronglyMeasurable measurableSet_Icc))
      (by filter_upwards with t; rw [norm_mul]
          calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
              ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                    abs_of_nonneg (Int.fract_nonneg t)]
                exact (Int.fract_lt_one t).le
            _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _)
  rw [MeasureTheory.integral_union_ae h_ae_disj measurableSet_Icc.nullMeasurableSet
    h_int_1k h_int_kk1]
  -- Step 3: Replace integral on Icc k (k+1) with the fract piece
  rw [integral_fract_piece s hσ hs k (by omega)]

-- Helper: the key per-step Abel identity
-- (k+1)^{-s} = [(k+1)^{1-s} - k^{1-s}] / (1-s)
--              - s * [∫_k^{k+1} t^{-s} dt - k * ∫_k^{k+1} t^{-(s+1)} dt]
private theorem abel_step (s : ℂ) (hs : s ≠ 1) (hσ : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    (↑(k + 1) : ℂ) ^ (-s) =
      ((↑(k + 1) : ℂ) ^ ((1 : ℂ) - s) - (↑k : ℂ) ^ ((1 : ℂ) - s)) / ((1 : ℂ) - s) -
      s * ((∫ x in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑x : ℂ) ^ (-s)) -
           (↑k : ℂ) * (∫ x in (↑k : ℝ)..(↑(k + 1) : ℝ), (↑x : ℂ) ^ (-(s + 1)))) := by
  have h1s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hσ
  have h_neg_s_ne : -s ≠ 0 := neg_ne_zero.mpr hs0
  -- Use integral_cpow_neg_s and integral_cpow_neg_succ
  rw [integral_cpow_neg_s s k hk hs, integral_cpow_neg_succ s k hk hσ]
  -- After substituting integral values, the goal is pure algebra in ℂ
  -- The goal has ↑(k+1) (Nat→ℂ cast) while cpow_one_sub_eq produces ↑(↑(k+1):ℝ) (Nat→ℝ→ℂ)
  -- These are definitionally equal (Complex.ofReal_natCast is rfl), so we normalize with push_cast
  -- Key identities: a^{1-s} = a * a^{-s}, a^{-s+1} = a * a^{-s}
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk1_pos : (0 : ℝ) < (↑(k + 1) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_ne : (↑k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1_ne : (↑(k+1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Rewrite cpow terms: a^{1-s} = a * a^{-s} and a^{-s+1} = a * a^{-s}
  have hk1_1s : (↑(k + 1) : ℂ) ^ ((1 : ℂ) - s) = (↑(k + 1) : ℂ) * (↑(k + 1) : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, cpow_add _ _ hk1_ne, cpow_one, mul_comm]
  have hk_1s : (↑k : ℂ) ^ ((1 : ℂ) - s) = (↑k : ℂ) * (↑k : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, cpow_add _ _ hk_ne, cpow_one, mul_comm]
  have hk1_ms1 : (↑(k + 1) : ℂ) ^ (-s + 1) = (↑(k + 1) : ℂ) * (↑(k + 1) : ℂ) ^ (-s) := by
    rw [cpow_add _ _ hk1_ne, cpow_one, mul_comm]
  have hk_ms1 : (↑k : ℂ) ^ (-s + 1) = (↑k : ℂ) * (↑k : ℂ) ^ (-s) := by
    rw [cpow_add _ _ hk_ne, cpow_one, mul_comm]
  rw [hk1_1s, hk_1s, hk1_ms1, hk_ms1]
  -- Now all cpow expressions are a^{-s}. Unify denominator: (-s+1) = (1-s)
  have h_denom : (-s + 1 : ℂ) = (1 : ℂ) - s := by ring
  rw [h_denom]
  -- After field_simp, we get an equation with cpow terms treated as atoms
  -- Need to show it's an identity in the ring ℂ[↑(k+1)^{-s}, ↑k^{-s}, s, ↑k]
  -- where ↑(k+1) = ↑k + 1
  have hk_cast : (↑(k + 1) : ℂ) = (↑k : ℂ) + 1 := by push_cast; ring
  field_simp
  -- The remaining goal should be solvable after replacing ↑(k+1) with ↑k + 1
  rw [hk_cast]
  ring

theorem abel_identity (s : ℂ) (hs : s ≠ 1) (hσ : 0 < s.re) (N : ℕ) (hN : 2 ≤ N) :
    SpiralInduction.S s N =
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) +
      s / (s - 1) -
      s * ∫ t in Set.Icc (1 : ℝ) (N : ℝ),
        (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  -- Proof by induction on N starting from 2
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 2: S(s,2) = 1 + 2^{-s}
    rw [SpiralInduction.S_succ, SpiralInduction.S_one]
    -- RHS: 2^{1-s}/(1-s) + s/(s-1) - s * ∫_{1}^{2} fract(t) * t^{-(s+1)} dt
    -- On [1,2], fract(t) = t - 1, so integral = ∫_1^2 (t-1)*t^{-(s+1)} dt
    --   = ∫_1^2 t^{-s} dt - ∫_1^2 t^{-(s+1)} dt
    -- Using helpers: ∫_1^2 t^{-s} dt = (2^{-s+1} - 1^{-s+1})/(-s+1)
    --               ∫_1^2 t^{-(s+1)} dt = (2^{-s} - 1^{-s})/(-s)
    -- After cpow_one_sub_eq: 2^{1-s} = 2 * 2^{-s}, 1^{1-s} = 1 * 1^{-s} = 1
    -- The identity abel_step with k=1 gives:
    --   2^{-s} = [2^{1-s} - 1^{1-s}]/(1-s) - s * [∫_1^2 t^{-s} - 1*∫_1^2 t^{-(s+1)}]
    -- So: 1 + 2^{-s} = 1 + [2^{1-s} - 1]/(1-s) - s * integral_piece
    -- = [1-s + 2^{1-s} - 1]/(1-s) - s * integral_piece
    -- = [2^{1-s} - s]/(1-s) - s * integral_piece
    -- = 2^{1-s}/(1-s) - s/(1-s) - s * integral_piece
    -- = 2^{1-s}/(1-s) + s/(s-1) - s * integral_piece  ✓
    -- Also: integral over Icc 1 2 of fract * cpow = integral_piece (since Icc 1 1 has measure 0)
    -- abel_step with k=1: 2^{-s} = [2^{1-s} - 1^{1-s}]/(1-s) - s*piece
    have hstep := abel_step s hs hσ 1 le_rfl
    -- integral_fract_piece: ∫ Icc 1 2 fract*cpow = piece
    have hpiece := integral_fract_piece s hσ hs 1 le_rfl
    -- Normalize ↑(1+1) to 2 everywhere
    norm_num at hstep hpiece ⊢
    -- Substitute the integral identity
    rw [hpiece, hstep]
    -- Now: 1 + [2^{1-s} - 1]/(1-s) - s*piece = 2^{1-s}/(1-s) + s/(s-1) - s*piece
    -- The 1^{1-s} term has already been simplified to 1 by norm_num above
    -- Pure algebra: 1 + [2^{1-s} - 1]/(1-s) - s*P = 2^{1-s}/(1-s) + s/(s-1) - s*P
    have h1s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have hs1_ne : s - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs
    field_simp
    ring
  | succ k hk ih =>
    -- Inductive step: S(s, k+1) = S(s,k) + (k+1)^{-s}
    -- and ∫ Icc 1 (k+1) = ∫ Icc 1 k + piece on [k, k+1]
    rw [SpiralInduction.S_succ, ih]
    -- Use abel_step for (k+1)^{-s}
    have hstep := abel_step s hs hσ k (by omega)
    -- Use integral splitting
    have hsplit := integral_Icc_succ_split s hσ hs k (by omega)
    -- Substitute and do algebra
    rw [hsplit, hstep]
    -- Now pure algebra: combine the N^{1-s}/(1-s) terms and factor
    have h1s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    -- Goal should reduce to algebra after substitution
    field_simp
    ring

/-! ## Section 3: The Analytic Continuation Function

  Define c(s) = s/(s-1) + s·∫₁^∞ {t}·t^{-s-1} dt.
  This is analytic on {Re(s) > 0} \ {1}. -/

/-- The analytic continuation function: c(s) = s/(s-1) - s·∫₁^∞ {t}·t^{-s-1} dt.
    For Re(s) > 1, this equals ζ(s). -/
noncomputable def c_fun (s : ℂ) : ℂ :=
  s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))

/-! ## Section 4: Agreement with ζ for Re(s) > 1

  For Re(s) > 1, S(s,N) → ζ(s) as N → ∞, and N^{1-s}/(1-s) → 0.
  So c(s) = ζ(s) for Re(s) > 1. -/

/-- Helper: ‖R(s,N)‖ → 0 as N → ∞ for Re(s) > 0. -/
private theorem R_tendsto_zero (s : ℂ) (hσ : 0 < s.re) :
    Tendsto (fun N : ℕ => R s N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_bound : ∀ᶠ N : ℕ in atTop, ‖R s N‖ ≤ ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    exact R_bound s hσ N hN
  have h_tend : Tendsto (fun N : ℕ => ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re) atTop (𝓝 (‖s‖ * 0 / s.re)) := by
      apply Tendsto.div_const
      apply Tendsto.const_mul
      have h_neg : 0 < s.re := hσ
      exact (tendsto_rpow_neg_atTop h_neg).comp tendsto_natCast_atTop_atTop
    simp at this
    exact this
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_tend
    (Eventually.of_forall (fun n => norm_nonneg (R s n))) h_bound

/-- Helper: S(s,N) → ζ(s) for Re(s) > 1. -/
private theorem S_tendsto_zeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => SpiralInduction.S s N) atTop (𝓝 (riemannZeta s)) := by
  -- S s N = ∑ n ∈ range N, (n+1)^{-s}
  -- ζ(s) = ∑' n, 1/(n+1)^s = ∑' n, (n+1)^{-s}
  -- HasSum gives Tendsto of partial sums
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have h_eq : (fun n : ℕ => 1 / (↑n + 1 : ℂ) ^ s) = (fun n : ℕ => (↑(n + 1) : ℂ) ^ (-s)) := by
    ext n; rw [cpow_neg, one_div]; push_cast; ring_nf
  rw [h_eq]
  have h_summable : Summable (fun n : ℕ => (↑(n + 1) : ℂ) ^ (-s)) := by
    rw [show (fun n : ℕ => (↑(n + 1) : ℂ) ^ (-s)) =
        (fun n : ℕ => 1 / (↑n + 1 : ℂ) ^ s) from h_eq.symm]
    have h_base := Complex.summable_one_div_nat_cpow.mpr hs
    -- h_base : Summable (fun n : ℕ => 1 / (↑n : ℂ) ^ s)
    -- We need: Summable (fun n : ℕ => 1 / (↑n + 1 : ℂ) ^ s)
    -- This equals (fun n => 1 / ↑(n+1) ^ s) = (fun n => (1 / ↑· ^ s) ∘ Nat.succ)
    -- Use Summable.comp_injective
    have h_eq' : (fun n : ℕ => 1 / (↑n + 1 : ℂ) ^ s) =
        (fun n : ℕ => 1 / (↑n : ℂ) ^ s) ∘ Nat.succ := by
      ext n; simp [Nat.succ_eq_add_one, Function.comp]
    rw [h_eq']
    exact h_base.comp_injective Nat.succ_injective
  have h_hassum := h_summable.hasSum
  exact h_hassum.tendsto_sum_nat

/-- Helper: N^{1-s}/(1-s) → 0 for Re(s) > 1. -/
private theorem cpow_div_tendsto_zero (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) atTop (𝓝 0) := by
  rw [show (0 : ℂ) = 0 / ((1 : ℂ) - s) from by rw [zero_div]]
  apply Tendsto.div_const
  -- Need: N^{1-s} → 0 as N → ∞
  -- ‖N^{1-s}‖ = N^{1-σ} → 0 since 1-σ < 0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_re_neg : 0 < s.re - 1 := by linarith
  -- ‖(↑N : ℂ) ^ (1-s)‖ = N^{Re(1-s)} = N^{1-σ} for N > 0
  have h_norm_eq : ∀ᶠ N : ℕ in atTop, ‖(↑N : ℂ) ^ ((1 : ℂ) - s)‖ = (↑N : ℝ) ^ (1 - s.re) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N)]
    simp [Complex.sub_re, Complex.one_re]
  -- N^{1-σ} = N^{-(σ-1)} → 0 since σ-1 > 0
  apply Filter.Tendsto.congr' (EventuallyEq.symm h_norm_eq)
  rw [show (1 - s.re) = -(s.re - 1) from by ring]
  exact (tendsto_rpow_neg_atTop h_re_neg).comp tendsto_natCast_atTop_atTop

/-- For Re(s) > 1: c(s) = ζ(s). Uses zeta_eq_tsum_one_div_nat_cpow from Mathlib. -/
theorem c_eq_zeta_of_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    c_fun s = riemannZeta s := by
  have hσ : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  -- Define a(N) = S(s,N) - N^{1-s}/(1-s)
  set a : ℕ → ℂ := fun N =>
    SpiralInduction.S s N - (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) with ha_def
  -- PART A: a(N) → c_fun(s) eventually (for N ≥ 2)
  -- From abel_identity: a(N) = s/(s-1) - s * ∫ Icc 1 N = c_fun(s) + R(s,N)
  -- Specifically: a(N) - c_fun(s) = R(s,N)
  have h_a_eq : ∀ N : ℕ, 2 ≤ N → a N - c_fun s = R s N := by
    intro N hN
    have habel := abel_identity s hs1 hσ N hN
    -- From abel_identity: S(s,N) = N^{1-s}/(1-s) + s/(s-1) - s*∫Icc
    -- So a(N) = S - N^{1-s}/(1-s) = s/(s-1) - s*∫Icc
    -- c_fun(s) = s/(s-1) - s*∫Ioi
    -- a(N) - c_fun(s) = -s*∫Icc + s*∫Ioi = s*(∫Ioi - ∫Icc) = s*∫IoiN = R(s,N)
    -- Step 1: Simplify a N using abel_identity
    have h_aN : a N = s / (s - 1) -
        s * ∫ t in Set.Icc (1 : ℝ) (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      simp only [ha_def]; rw [habel]; ring
    -- Step 2: Integral splitting ∫ Ioi 1 = ∫ Icc 1 N + ∫ Ioi N
    have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have h_split : ∫ t in Set.Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (∫ t in Set.Icc (1 : ℝ) (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        (∫ t in Set.Ioi (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      rw [← MeasureTheory.integral_Ici_eq_integral_Ioi, ← Set.Icc_union_Ioi_eq_Ici hle]
      exact MeasureTheory.setIntegral_union
        (Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt.mpr hx1.2 hx2))
        measurableSet_Ioi
        (by -- IntegrableOn on Icc 1 N
          have h_slit : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
            fun t ht => Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
          have h_cpow_int : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
              (Set.Icc (1 : ℝ) (N : ℝ)) :=
            (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
              h_slit).integrableOn_compact isCompact_Icc
          exact h_cpow_int.integrable.mono
            (((continuous_ofReal.measurable.comp
              (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
              ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
                h_slit).aestronglyMeasurable measurableSet_Icc))
            (by filter_upwards with t; rw [norm_mul]
                calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
                    ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ := by
                      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                      rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                          abs_of_nonneg (Int.fract_nonneg t)]
                      exact (Int.fract_lt_one t).le
                  _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _))
        (by -- IntegrableOn on Ioi N
          have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
          have hσ_neg : -(s.re + 1) < -1 := by linarith
          have h_slit : ∀ t ∈ Set.Ioi (N : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
            fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans hN_pos ht)
          have h_dom : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Set.Ioi (N : ℝ)) :=
            integrableOn_Ioi_rpow_of_lt hσ_neg hN_pos
          exact h_dom.integrable.mono
            (((continuous_ofReal.measurable.comp
              (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
              ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
                h_slit).aestronglyMeasurable measurableSet_Ioi))
            (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
                rw [Set.mem_Ioi] at ht
                have ht_pos : (0 : ℝ) < t := lt_trans hN_pos ht
                rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht_pos.le _)]
                calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
                    ≤ 1 * t ^ (-(s.re + 1)) := by
                      apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
                      · rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                            abs_of_nonneg (Int.fract_nonneg t)]
                        exact (Int.fract_lt_one t).le
                      · rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
                        simp [Complex.add_re, Complex.neg_re, Complex.one_re]
                  _ = t ^ (-(s.re + 1)) := one_mul _))
    -- Step 3: Now compute: a N - c_fun s
    -- a N = s/(s-1) - s * ∫Icc
    -- c_fun s = s/(s-1) - s * ∫Ioi
    -- ∫Ioi = ∫Icc + ∫IoiN  [from h_split]
    -- So: a N - c_fun s = -s*∫Icc + s*∫Ioi = s*(∫Ioi - ∫Icc) = s*∫IoiN = R s N
    rw [h_aN]
    unfold c_fun R tailIntegral
    rw [h_split]
    ring
  -- PART A conclusion: a(N) → c_fun(s)
  have h_tendsto_cfun : Tendsto a atTop (𝓝 (c_fun s)) := by
    have h_zero : Tendsto (fun N => a N - c_fun s) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h_bound : ∀ᶠ N : ℕ in atTop, ‖a N - c_fun s‖ ≤ ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re := by
        filter_upwards [Filter.eventually_ge_atTop 2] with N hN
        rw [h_a_eq N hN]
        exact R_bound s hσ N hN
      have h_tend : Tendsto (fun N : ℕ => ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re) atTop (𝓝 0) := by
        have : Tendsto (fun N : ℕ => ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re) atTop (𝓝 (‖s‖ * 0 / s.re)) := by
          apply Tendsto.div_const; apply Tendsto.const_mul
          exact (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
        simp at this; exact this
      have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_tend
        (Eventually.of_forall (fun N => norm_nonneg (a N - c_fun s))) h_bound
    have : Tendsto (fun N => c_fun s + (a N - c_fun s)) atTop (𝓝 (c_fun s + 0)) :=
      tendsto_const_nhds.add h_zero
    simp at this
    exact this.congr (fun N => by ring)
  -- PART B: a(N) → ζ(s)
  have h_tendsto_zeta : Tendsto a atTop (𝓝 (riemannZeta s)) := by
    show Tendsto (fun N => SpiralInduction.S s N -
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) atTop (𝓝 (riemannZeta s))
    have := (S_tendsto_zeta s hs).sub (cpow_div_tendsto_zero s hs)
    simp at this
    exact this
  -- Uniqueness of limits
  exact tendsto_nhds_unique h_tendsto_cfun h_tendsto_zeta

/-! ## Section 5: Analytic Continuation — c(s) = ζ(s) for Re(s) > 0

  Both c(s) and ζ(s) are analytic on {Re(s) > 0} \ {1}.
  They agree on {Re(s) > 1}, which is an open subset.
  By the identity principle, they agree everywhere on the connected domain. -/

/-- c(s) is analytic on {Re(s) > 0} \ {1}.

    Proof strategy: use `analyticAt_iff_eventually_differentiableAt` to reduce to showing
    c_fun is differentiable in a neighborhood of s. The function c_fun is a difference of
    two terms:
    1. s/(s-1) — a rational function, differentiable at s ≠ 1
    2. s * ∫_{1}^{∞} {t} * t^{-(s+1)} dt — product of s (differentiable) and a
       parameter-dependent integral (differentiable by the Mellin transform theory)

    The integral term is handled via `mellin_differentiableAt_of_isBigO_rpow`: after
    extending fract to Ioi 0 (zero on (0,1]), the integral becomes a Mellin transform
    evaluated at -s. The function is O(1) at ∞ and vanishes near 0, satisfying all
    conditions of the Mellin differentiability theorem for Re(s) > 0. -/
theorem c_fun_analyticAt (s : ℂ) (hσ : 0 < s.re) (hs : s ≠ 1) :
    AnalyticAt ℂ c_fun s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  -- Need: ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ c_fun z
  -- The set {z | 0 < z.re ∧ z ≠ 1} is open and contains s
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact isOpen_ne
  have hs_mem : s ∈ {z : ℂ | 0 < z.re ∧ z ≠ 1} := ⟨hσ, hs⟩
  filter_upwards [hU.mem_nhds hs_mem] with z ⟨hz_re, hz_ne⟩
  -- Show c_fun is differentiable at z with 0 < z.re and z ≠ 1
  unfold c_fun
  apply DifferentiableAt.sub
  · -- s/(s-1) is differentiable at z ≠ 1
    apply DifferentiableAt.div
    · exact differentiableAt_id
    · exact differentiableAt_id.sub (differentiableAt_const 1)
    · simp [sub_ne_zero]; exact hz_ne
  · -- s * ∫ ... is differentiable
    apply DifferentiableAt.mul
    · exact differentiableAt_id
    · -- The integral ∫ t in Ioi 1, {t} * t^{-(z+1)} dt is differentiable in z
      -- By Leibniz integral rule (hasFDerivAt_integral_of_dominated_of_fderiv_le).
      -- Derivative w.r.t. z: {t} * (-log(↑t)) * (↑t)^{-(z+1)}
      -- Bound: |log t| * t^{-(σ/2+1)}, integrable on Ioi 1.
      set μ := (volume : Measure ℝ).restrict (Set.Ioi (1 : ℝ))
      show DifferentiableAt ℂ (fun w => ∫ t, (fract t : ℂ) * (t : ℂ) ^ (-(w + 1)) ∂μ) z
      set σ := z.re
      set ε := σ / 4
      have hε_pos : 0 < ε := by positivity
      set F'val := fun (w : ℂ) (t : ℝ) =>
        (fract t : ℂ) * ((t : ℂ) ^ (-(w + 1)) * Complex.log (t : ℂ) * (-1))
      set F' := fun (w : ℂ) (t : ℝ) =>
        ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (F'val w t)
      set bound := fun (t : ℝ) => |Real.log t| * t ^ (-(σ / 2 + 1))
      suffices h : HasFDerivAt (fun w => ∫ t, (fract t : ℂ) * (t : ℂ) ^ (-(w + 1)) ∂μ)
          (∫ t, F' z t ∂μ) z from h.differentiableAt
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (s := Metric.ball z ε) (bound := bound)
      · exact Metric.ball_mem_nhds z hε_pos
      · -- AEStronglyMeasurable (integrand) for z near z₀
        have h_slit : ∀ t ∈ Ioi (1 : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
          fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
        exact .of_forall fun _ =>
          ((continuous_ofReal.measurable.comp
            (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
            ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
              h_slit).aestronglyMeasurable measurableSet_Ioi)
      · -- Integrable at z₀: dominated by t^{-(σ+1)}, integrable since -(σ+1) < -1
        have h_slit : ∀ t ∈ Ioi (1 : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
          fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
        have h_dom : IntegrableOn (fun t : ℝ => t ^ (-(σ + 1))) (Ioi (1 : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt (by linarith : -(σ + 1) < -1) one_pos
        have h_aesm : AEStronglyMeasurable (fun t : ℝ =>
            (fract t : ℂ) * (t : ℂ) ^ (-(z + 1)))
            (volume.restrict (Ioi (1 : ℝ))) :=
          ((continuous_ofReal.measurable.comp
            (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
            ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
              h_slit).aestronglyMeasurable measurableSet_Ioi)
        exact h_dom.integrable.mono h_aesm (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [Set.mem_Ioi] at ht
          have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
          calc ‖(fract t : ℂ) * (t : ℂ) ^ (-(z + 1))‖
              = ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(z + 1))‖ := norm_mul _ _
            _ ≤ 1 * ‖(t : ℂ) ^ (-(z + 1))‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                    abs_of_nonneg (Int.fract_nonneg t)]
                exact (Int.fract_lt_one t).le
            _ = ‖(t : ℂ) ^ (-(z + 1))‖ := one_mul _
            _ = t ^ (-(σ + 1)) := by
                rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]; congr 1
            _ = ‖t ^ (-(σ + 1))‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht_pos.le _)])
      · -- AEStronglyMeasurable of F': smulRight 1 ∘ F'val z is measurable
        have h_slit : ∀ t ∈ Ioi (1 : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
          fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
        have h1 : ContinuousOn (fun t : ℝ => (↑t : ℂ) ^ (-(z + 1))) (Ioi 1) :=
          ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const h_slit
        have h2 : ContinuousOn (fun t : ℝ => Complex.log (↑t : ℂ)) (Ioi 1) :=
          fun _ ht => (continuous_ofReal.continuousAt.clog
            (Complex.ofReal_mem_slitPlane.mpr (lt_trans one_pos ht))).continuousWithinAt
        have h3 : ContinuousOn (fun t : ℝ =>
            (↑t : ℂ) ^ (-(z + 1)) * Complex.log (↑t : ℂ) * (-1)) (Ioi 1) :=
          (h1.mul h2).mul continuousOn_const
        have h_F'val : AEStronglyMeasurable (F'val z) μ :=
          ((continuous_ofReal.measurable.comp
            (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
            (h3.aestronglyMeasurable measurableSet_Ioi)
        exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ
          (1 : ℂ →L[ℂ] ℂ)).continuous.comp_aestronglyMeasurable h_F'val
      · -- ‖F' w t‖ ≤ bound t for w in ball(z, σ/4)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        intro w hw
        rw [Set.mem_Ioi] at ht
        have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
        -- ‖F' w t‖ = ‖F'val w t‖
        have h_norm_F' : ‖F' w t‖ = ‖F'val w t‖ := by
          simp only [F']; rw [ContinuousLinearMap.norm_smulRight_apply]; simp
        rw [h_norm_F']
        -- Unfold F'val and simplify norms
        simp only [F'val, norm_mul, norm_neg, norm_one, mul_one]
        -- |fract(t)| ≤ 1
        have h_fract : ‖(fract t : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
              abs_of_nonneg (Int.fract_nonneg t)]
          exact (Int.fract_lt_one t).le
        -- ‖t^{-(w+1)}‖ = t^{-(w.re+1)}
        have h_cpow_norm : ‖(↑t : ℂ) ^ (-(w + 1))‖ = t ^ (-(w.re + 1)) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]; congr 1
        -- ‖Complex.log ↑t‖ = |Real.log t|
        have h_log_norm : ‖Complex.log (↑t : ℂ)‖ = |Real.log t| := by
          rw [(Complex.ofReal_log ht_pos.le).symm, Complex.norm_real, Real.norm_eq_abs]
        -- w.re > σ/2 from ball condition
        have hw_re : σ / 2 < w.re := by
          have h1 : |w.re - z.re| < σ / 4 := by
            calc |w.re - z.re| = |(w - z).re| := by simp [Complex.sub_re]
              _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
              _ = dist w z := rfl
              _ < ε := hw
          rw [show z.re = σ from rfl] at h1
          rw [abs_lt] at h1; linarith [h1.1]
        -- t^{-(w.re+1)} ≤ t^{-(σ/2+1)} since -(w.re+1) ≤ -(σ/2+1) and t ≥ 1
        have h_rpow_le : t ^ (-(w.re + 1)) ≤ t ^ (-(σ / 2 + 1)) :=
          Real.rpow_le_rpow_of_exponent_le ht.le (by linarith : -(w.re + 1) ≤ -(σ / 2 + 1))
        -- Combine
        calc ‖(fract t : ℂ)‖ * (‖(↑t : ℂ) ^ (-(w + 1))‖ * ‖Complex.log (↑t : ℂ)‖)
            ≤ 1 * (t ^ (-(σ / 2 + 1)) * |Real.log t|) := by
              apply mul_le_mul h_fract _ (by positivity) zero_le_one
              rw [h_cpow_norm, h_log_norm]
              exact mul_le_mul_of_nonneg_right h_rpow_le (abs_nonneg _)
          _ = |Real.log t| * t ^ (-(σ / 2 + 1)) := by ring
      · -- Integrable bound: ∫_Ioi1 |log t|·t^{-(σ/2+1)} < ∞
        -- Dominate: |log t| ≤ t^{σ/4} / (σ/4) by Real.log_le_rpow_div
        -- So bound(t) ≤ (4/σ) · t^{-(σ/4+1)}, integrable since -(σ/4+1) < -1
        have hσ4 : (0 : ℝ) < σ / 4 := by positivity
        have h_dom : IntegrableOn (fun t : ℝ => (4 / σ) * t ^ (-(σ / 4 + 1))) (Ioi (1 : ℝ)) :=
          (integrableOn_Ioi_rpow_of_lt (by linarith : -(σ / 4 + 1) < -1) one_pos).const_mul _
        have h_bound_meas : AEStronglyMeasurable bound μ :=
          (ContinuousOn.mul
            (continuous_abs.comp_continuousOn
              (Real.continuousOn_log.mono (fun _ ht => ne_of_gt (lt_trans one_pos ht))))
            (ContinuousOn.rpow_const continuousOn_id
              (fun _ ht => Or.inl (ne_of_gt (lt_trans one_pos ht))))).aestronglyMeasurable
            measurableSet_Ioi
        exact h_dom.integrable.mono h_bound_meas (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [Set.mem_Ioi] at ht
          have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
          -- Both sides are nonneg, so ‖·‖ = id
          have h_nn₁ : 0 ≤ bound t := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht_pos.le _)
          have h_nn₂ : 0 ≤ (4 / σ) * t ^ (-(σ / 4 + 1)) := by positivity
          rw [Real.norm_of_nonneg h_nn₁, Real.norm_of_nonneg h_nn₂]
          -- Goal: bound t ≤ (4/σ) * t^{-(σ/4+1)}
          simp only [bound]
          -- Goal: |log t| * t^{-(σ/2+1)} ≤ (4/σ) * t^{-(σ/4+1)}
          rw [abs_of_nonneg (Real.log_nonneg ht.le)]
          have h_log_bound : Real.log t ≤ t ^ (σ / 4) / (σ / 4) :=
            Real.log_le_rpow_div ht_pos.le hσ4
          calc Real.log t * t ^ (-(σ / 2 + 1))
              ≤ (t ^ (σ / 4) / (σ / 4)) * t ^ (-(σ / 2 + 1)) :=
                mul_le_mul_of_nonneg_right h_log_bound (Real.rpow_nonneg ht_pos.le _)
            _ = (4 / σ) * (t ^ (σ / 4) * t ^ (-(σ / 2 + 1))) := by ring
            _ = (4 / σ) * t ^ (σ / 4 + (-(σ / 2 + 1))) := by rw [Real.rpow_add ht_pos]
            _ = (4 / σ) * t ^ (-(σ / 4 + 1)) := by ring_nf)
      · -- HasFDerivAt for each t (the key analytical step — PROVED)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        intro w _
        rw [Set.mem_Ioi] at ht
        have ht_pos : (0 : ℝ) < t := lt_trans one_pos ht
        apply HasDerivAt.hasFDerivAt
        show HasDerivAt (fun w => (fract t : ℂ) * (t : ℂ) ^ (-(w + 1))) (F'val w t) w
        have ht_ne : ((t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
        have hf : HasDerivAt (fun w : ℂ => -(w + 1)) (-1 : ℂ) w := by
          convert (hasDerivAt_id w).add (hasDerivAt_const w (1 : ℂ)) |>.neg using 1; simp
        show HasDerivAt (fun w => (fract t : ℂ) * (↑t : ℂ) ^ (-(w + 1)))
          ((fract t : ℂ) * ((↑t : ℂ) ^ (-(w + 1)) * Complex.log (↑t : ℂ) * (-1))) w
        exact (hf.const_cpow (Or.inl ht_ne)).const_mul _

/-- The domain {Re(s) > 0} \ {1} is connected.
    Proof: decompose into four convex (hence preconnected) pieces whose pairwise
    intersections make a connected overlap graph, then glue with IsPreconnected.union'. -/
theorem domain_connected :
    IsPreconnected {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  -- Four convex pieces covering the domain:
  set X₁ := {s : ℂ | 0 < s.re ∧ 0 < s.im}       -- upper right half-plane
  set X₂ := {s : ℂ | 0 < s.re ∧ s.im < 0}        -- lower right half-plane
  set X₃ := {s : ℂ | 0 < s.re ∧ s.re < 1}        -- vertical strip 0 < re < 1
  set X₄ := {s : ℂ | (1 : ℝ) < s.re}              -- right of re = 1
  -- Each piece is convex (hence preconnected)
  have hc₁ : Convex ℝ X₁ :=
    (convex_halfSpace_gt Complex.reLm.isLinear 0).inter
      (convex_halfSpace_gt Complex.imLm.isLinear 0)
  have hc₂ : Convex ℝ X₂ :=
    (convex_halfSpace_gt Complex.reLm.isLinear 0).inter
      (convex_halfSpace_lt Complex.imLm.isLinear 0)
  have hc₃ : Convex ℝ X₃ :=
    (convex_halfSpace_gt Complex.reLm.isLinear 0).inter
      (convex_halfSpace_lt Complex.reLm.isLinear 1)
  have hc₄ : Convex ℝ X₄ := convex_halfSpace_gt Complex.reLm.isLinear 1
  -- Each piece is contained in the target
  have hsub₁ : X₁ ⊆ {s | 0 < s.re ∧ s ≠ 1} := by
    intro s ⟨hr, hi⟩; exact ⟨hr, fun h => by simp [h] at hi⟩
  have hsub₂ : X₂ ⊆ {s | 0 < s.re ∧ s ≠ 1} := by
    intro s ⟨hr, hi⟩; exact ⟨hr, fun h => by simp [h] at hi⟩
  have hsub₃ : X₃ ⊆ {s | 0 < s.re ∧ s ≠ 1} := by
    intro s ⟨hr, hlt⟩; exact ⟨hr, fun h => by simp [h] at hlt⟩
  have hsub₄ : X₄ ⊆ {s | 0 < s.re ∧ s ≠ 1} := by
    intro s (hr : 1 < s.re)
    exact ⟨by linarith, fun h => by simp [h] at hr⟩
  -- Witness points for overlaps
  -- w₁ = ½ + i ∈ X₁ ∩ X₃
  have hw₁_mem₁ : (⟨1/2, 1⟩ : ℂ) ∈ X₁ := by
    exact ⟨by norm_num, by norm_num⟩
  have hw₁_mem₃ : (⟨1/2, 1⟩ : ℂ) ∈ X₃ := by
    exact ⟨by norm_num, by norm_num⟩
  -- w₂ = 2 + i ∈ X₁ ∩ X₄
  have hw₂_mem₁ : (⟨2, 1⟩ : ℂ) ∈ X₁ := by
    exact ⟨by norm_num, by norm_num⟩
  have hw₂_mem₄ : (⟨2, 1⟩ : ℂ) ∈ X₄ := by
    show (1 : ℝ) < (⟨2, 1⟩ : ℂ).re; norm_num
  -- w₃ = ½ - i ∈ X₂ ∩ X₃
  have hw₃_mem₂ : (⟨1/2, -1⟩ : ℂ) ∈ X₂ := by
    exact ⟨by norm_num, by norm_num⟩
  have hw₃_mem₃ : (⟨1/2, -1⟩ : ℂ) ∈ X₃ := by
    exact ⟨by norm_num, by norm_num⟩
  -- Target = X₁ ∪ X₂ ∪ X₃ ∪ X₄
  suffices h_eq : {s : ℂ | 0 < s.re ∧ s ≠ 1} = X₁ ∪ X₂ ∪ X₃ ∪ X₄ by
    rw [h_eq]
    -- Build up preconnectedness by successive unions
    -- Step 1: X₁ ∪ X₃ (overlap at ½ + i)
    have h13 : IsPreconnected (X₁ ∪ X₃) :=
      hc₁.isPreconnected.union' ⟨_, hw₁_mem₁, hw₁_mem₃⟩ hc₃.isPreconnected
    -- Step 2: (X₁ ∪ X₃) ∪ X₄ (overlap: X₁ ∩ X₄ contains 2 + i)
    have h134 : IsPreconnected (X₁ ∪ X₃ ∪ X₄) :=
      h13.union' ⟨_, Or.inl hw₂_mem₁, hw₂_mem₄⟩ hc₄.isPreconnected
    -- Step 3: (X₁ ∪ X₃ ∪ X₄) ∪ X₂ (overlap: X₃ ∩ X₂ contains ½ - i)
    have h1342 : IsPreconnected (X₁ ∪ X₃ ∪ X₄ ∪ X₂) :=
      h134.union' ⟨_, Or.inl (Or.inr hw₃_mem₃), hw₃_mem₂⟩ hc₂.isPreconnected
    -- Rewrite to match the target
    have : X₁ ∪ X₂ ∪ X₃ ∪ X₄ = X₁ ∪ X₃ ∪ X₄ ∪ X₂ := by
      ext; simp only [Set.mem_union]; tauto
    rwa [this]
  -- Prove the set equality
  ext s; simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hre, hne⟩
    by_cases him_pos : 0 < s.im
    · left; left; left; exact ⟨hre, him_pos⟩
    · by_cases him_neg : s.im < 0
      · left; left; right; exact ⟨hre, him_neg⟩
      · -- s.im = 0, so s is real with 0 < re, s ≠ 1
        have him_zero : s.im = 0 := le_antisymm (not_lt.mp him_pos) (not_lt.mp him_neg)
        by_cases hre1 : s.re < 1
        · left; right; exact ⟨hre, hre1⟩
        · right
          push_neg at hre1
          exact lt_of_le_of_ne hre1 (fun h => hne (Complex.ext h.symm him_zero))
  · rintro (((⟨hr, hi⟩ | ⟨hr, hi⟩) | ⟨hr, hlt⟩) | hr)
    · exact hsub₁ ⟨hr, hi⟩
    · exact hsub₂ ⟨hr, hi⟩
    · exact hsub₃ ⟨hr, hlt⟩
    · exact hsub₄ hr

/-- c(s) = ζ(s) for all s with Re(s) > 0, s ≠ 1.
    By the identity principle: both are analytic on the connected domain
    {Re(s) > 0} \ {1} and agree on {Re(s) > 1} (which has limit points). -/
theorem c_eq_zeta (s : ℂ) (hσ : 0 < s.re) (hs : s ≠ 1) :
    c_fun s = riemannZeta s := by
  -- Domain U = {s | 0 < s.re ∧ s ≠ 1}
  set U := {s : ℂ | 0 < s.re ∧ s ≠ 1}
  -- c_fun is analytic on U (from c_fun_analyticAt)
  have hf : AnalyticOnNhd ℂ c_fun U := fun z ⟨hz1, hz2⟩ => c_fun_analyticAt z hz1 hz2
  -- riemannZeta is analytic on U: differentiable on {1}ᶜ (open), hence AnalyticOnNhd there,
  -- and U ⊆ {1}ᶜ so we restrict.
  have hg : AnalyticOnNhd ℂ riemannZeta U := by
    have h_diff_on : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact (h_diff_on.analyticOnNhd isOpen_compl_singleton).mono (fun z ⟨_, hz⟩ => hz)
  -- U is preconnected (from domain_connected)
  -- Witness point z₀ = 2 ∈ U (since Re(2) = 2 > 0 and 2 ≠ 1)
  have h₀ : (2 : ℂ) ∈ U := ⟨by simp, by norm_num⟩
  -- They agree eventually near z₀ = 2: on {Re(s) > 1} which is an open nhd of 2
  have hfg : c_fun =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show 1 < (2 : ℂ).re by simp)] with z hz
    exact c_eq_zeta_of_re_gt_one z hz
  -- Apply the identity principle
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg domain_connected h₀ hfg ⟨hσ, hs⟩

/-! ## Section 6: The Main Theorem

  From abel_identity: S = N^{1-s}/(1-s) + s/(s-1) - s·∫₁^N {t}·t^{-(s+1)}
  From c_fun def: c(s) = s/(s-1) - s·∫₁^∞ {t}·t^{-(s+1)}
  So: S - N^{1-s}/(1-s) = c(s) + s·∫_N^∞ = c(s) + R(s,N)
  With c(s) = ζ(s): S - ζ - N^{1-s}/(1-s) = R(s,N)
  And ‖R(s,N)‖ ≤ ‖s‖/σ · N^{-σ} = C · N^{-σ}. -/

/-- The key algebraic identity: S(s,N) - ζ(s) - N^{1-s}/(1-s) = R(s,N).
    Proof sketch:
    - Abel summation gives: S = N^{1-s}/(1-s) + s/(s-1) - s·∫₁^N {t}·t^{-(s+1)}
    - c_fun definition: c(s) = s/(s-1) - s·∫₁^∞ {t}·t^{-(s+1)}
    - Integral splitting: ∫₁^∞ = ∫₁^N + ∫_N^∞
    - So: S - N^{1-s}/(1-s) = s/(s-1) - s·∫₁^N = c(s) + s·∫_N^∞ = c(s) + R(s,N)
    - c_eq_zeta: c(s) = ζ(s) for Re(s) > 0, s ≠ 1
    - Therefore: S - ζ - N^{1-s}/(1-s) = R(s,N) -/
theorem difference_eq_R (s : ℂ) (hσ : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 2 ≤ N) :
    SpiralInduction.S s N - riemannZeta s -
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) = R s N := by
  have habel := abel_identity s hs1 hσ N hN
  have hzeta := c_eq_zeta s hσ hs1
  -- Expand c_fun definition: ζ(s) = s/(s-1) - s·∫₁^∞ {t}·t^{-(s+1)}
  have hzeta_expanded : riemannZeta s = s / (s - 1) -
      s * ∫ t in Set.Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← hzeta]; unfold c_fun; rfl
  -- Key integral splitting: ∫₁^∞ = ∫₁^N + ∫_N^∞
  have h_split : ∫ t in Set.Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Set.Icc (1 : ℝ) (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) +
      (∫ t in Set.Ioi (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    -- Ioi 1 = Ici 1 (ae) = Icc 1 N ∪ Ioi N (disjoint), then split
    have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi, ← Set.Icc_union_Ioi_eq_Ici hle]
    exact MeasureTheory.setIntegral_union
      (Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt.mpr hx1.2 hx2))
      measurableSet_Ioi
      (by -- IntegrableOn on Icc 1 N: cpow continuous on compact, |fract| ≤ 1
        have h_slit : ∀ t ∈ Icc (1 : ℝ) (N : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
          fun t ht => Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
        have h_cpow_int : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
            (Icc (1 : ℝ) (N : ℝ)) :=
          (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
            h_slit).integrableOn_compact isCompact_Icc
        have h_aesm : AEStronglyMeasurable (fun t : ℝ =>
            (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)))
            (volume.restrict (Icc (1 : ℝ) (N : ℝ))) :=
          ((continuous_ofReal.measurable.comp
            (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
            ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
              h_slit).aestronglyMeasurable measurableSet_Icc)
        exact h_cpow_int.integrable.mono h_aesm (by
          filter_upwards with t; rw [norm_mul]
          calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
              ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                    abs_of_nonneg (Int.fract_nonneg t)]
                exact (Int.fract_lt_one t).le
            _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _))
      (by -- IntegrableOn on Ioi N: dominated by t^{-(σ+1)}
        have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
        have hσ_neg : -(s.re + 1) < -1 := by linarith
        have h_slit : ∀ t ∈ Ioi (N : ℝ), (↑t : ℂ) ∈ Complex.slitPlane :=
          fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans hN_pos ht)
        have h_dom : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Ioi (N : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt hσ_neg hN_pos
        have h_aesm : AEStronglyMeasurable (fun t : ℝ =>
            (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)))
            (volume.restrict (Ioi (N : ℝ))) :=
          ((continuous_ofReal.measurable.comp
            (show Measurable fract from measurable_fract)).aestronglyMeasurable).mul
            ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
              h_slit).aestronglyMeasurable measurableSet_Ioi)
        exact h_dom.integrable.mono h_aesm (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [Set.mem_Ioi] at ht
          have ht_pos : (0 : ℝ) < t := lt_trans hN_pos ht
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht_pos.le _)]
          calc ‖(fract t : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖
              ≤ 1 * t ^ (-(s.re + 1)) := by
                apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
                · rw [Complex.norm_real, fract_eq_Int_fract, Real.norm_eq_abs,
                      abs_of_nonneg (Int.fract_nonneg t)]
                  exact (Int.fract_lt_one t).le
                · rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
                  simp [Complex.add_re, Complex.neg_re, Complex.one_re]
            _ = t ^ (-(s.re + 1)) := one_mul _))
  -- Substitute abel + zeta expansion, then simplify algebraically.
  -- After rw: goal = (N^{1-s}/(1-s) + s/(s-1) - s*∫Icc) - (s/(s-1) - s*∫Ioi1) - N^{1-s}/(1-s) = R s N
  -- Ring reduces to: s * (∫Ioi1 - ∫Icc)
  -- h_split gives: ∫Ioi1 - ∫Icc = ∫IoiN = tailIntegral s N
  -- So result = s * tailIntegral s N = R s N
  rw [habel, hzeta_expanded]
  -- Factor to s * (∫Ioi1 - ∫Icc) = R s N
  have h1 : (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) + s / (s - 1) -
      s * (∫ t in Set.Icc (1 : ℝ) (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) -
      (s / (s - 1) - s * (∫ t in Set.Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)))) -
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) =
      s * ((∫ t in Set.Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) -
           (∫ t in Set.Icc (1 : ℝ) (N : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)))) := by ring
  rw [h1, h_split]
  -- Goal: s * ((∫Icc + ∫IoiN) - ∫Icc) = R s N
  simp only [add_sub_cancel_left]; rfl

/-- **The Euler-Maclaurin formula for Dirichlet partial sums.**
    Discharges `euler_maclaurin_dirichlet` in BakerUncertainty.lean.

    S(s,N) = ζ(s) + N^{1-s}/(1-s) + O(N^{-σ})

    where the constant C = ‖s‖/σ depends on s but not N. -/
theorem euler_maclaurin_dirichlet (s : ℂ) (hσ : 0 < s.re) (_hσ1 : s.re < 1)
    (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖SpiralInduction.S s N - riemannZeta s -
        (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤
        C * (↑N : ℝ) ^ (-s.re) := by
  -- The constant: C = ‖s‖/σ + 1 (the +1 handles edge cases)
  refine ⟨‖s‖ / s.re + 1, by positivity, fun N hN => ?_⟩
  -- Step 1: The difference equals R(s,N)
  rw [difference_eq_R s hσ hs1 N hN]
  -- Step 2: ‖R(s,N)‖ ≤ ‖s‖ · N^{-σ} / σ
  have hRb := R_bound s hσ N hN
  -- Step 3: ‖s‖ · N^{-σ} / σ ≤ (‖s‖/σ + 1) · N^{-σ}
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNpow_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_nonneg hN_pos.le (-s.re)
  calc ‖R s N‖
      ≤ ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re := hRb
    _ ≤ (‖s‖ / s.re + 1) * (↑N : ℝ) ^ (-s.re) := by
        rw [add_mul, div_mul_eq_mul_div]
        linarith

/-- **Explicit form of Euler-Maclaurin.**
    Useful for computational checks where the constant matters.
    Returns the specific constant C = ‖s‖/σ + 1 used in the bound. -/
theorem euler_maclaurin_dirichlet_explicit (s : ℂ) (hσ : 0 < s.re) (_hσ1 : s.re < 1)
    (hs1 : s ≠ 1) :
    let C := ‖s‖ / s.re + 1
    0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖SpiralInduction.S s N - riemannZeta s -
        (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤
        C * (↑N : ℝ) ^ (-s.re) := by
  intro C
  constructor
  · positivity
  · intro N hN
    rw [difference_eq_R s hσ hs1 N hN]
    have hRb := R_bound s hσ N hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    calc ‖R s N‖
      ≤ ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re := hRb
    _ ≤ ‖s‖ * (↑N : ℝ) ^ (-s.re) / s.re + (↑N : ℝ) ^ (-s.re) := by
        have h_pow_pos : 0 < (N : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hN_pos _
        linarith
    _ = (‖s‖ / s.re + 1) * (↑N : ℝ) ^ (-s.re) := by
        rw [add_mul]
        field_simp

end EulerMaclaurinDirichlet
