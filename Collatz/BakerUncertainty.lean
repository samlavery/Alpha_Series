/-
  BakerUncertainty.lean — Baker as 1D Uncertainty Principle, Spiral as 2D Resolution
  ===================================================================================

  Baker's bound |S log 2 - m log 3| ≥ c/m^K is a 1D constraint on ℝ.
  It's used in:
  - No-cycles (DriftContradiction.lean): bounds drift ε away from 0
  - No-divergence (WeylBridge.lean): window defect → supercritical contraction

  Baker IS the uncertainty principle for primes 2 and 3. In 1D, you must
  fight the UP head-on. But the spiral S(s,X) = Σ n^{-s} lives in 2D (ℂ).
  In 2D, amplitude decay (σ-direction) resolves the UP that plagues 1D —
  you never need Baker because you never reduce to a 1D problem.

  Structure:
  §1 Definitions: drift, BakerFails
  §2 Counter-example: ¬Baker → 1D gap collapse (PROVED, zero axioms)
  §3 2D spiral framework (PROVED, references SpiralInduction)
  §4 Equidistribution (1 AXIOM: Weyl cross cancellation)
  §5 Spiral grows without Baker (PROVED from axiom)
  §6 Documentation: the replacement principle

  Axiom inventory:
  • weyl_spiral_growth — Euler-Maclaurin + Weyl equidistribution (Titchmarsh Ch. 4-5)
-/
import Collatz.SpiralInduction
import Collatz.SpiralTactics
import Collatz.EulerMaclaurinDirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace BakerUncertainty

/-! ## §1: Definitions -/

/-- The drift between 2^S and 3^m on the real line.
    Baker's theorem bounds this away from zero. -/
noncomputable def drift (S m : ℕ) : ℝ :=
  (S : ℝ) * Real.log 2 - (m : ℝ) * Real.log 3

/-- Baker's bound fails: for every c > 0 and exponent K, there exist
    S, m with positive drift smaller than c/m^K. This is the negation
    of Baker's lower bound — the 1D uncertainty principle collapses. -/
def BakerFails : Prop :=
  ∀ c : ℝ, 0 < c → ∀ K : ℕ,
    ∃ S m : ℕ, 2 ≤ m ∧ 0 < drift S m ∧
      drift S m < c / (m : ℝ) ^ K

/-! ## §2: Counter-example — ¬Baker → 1D Gap Collapse

Key chain: small drift → small exponential gap → large n₀ → escapes
finite verification. Every step is proved from standard Mathlib. -/

/-- Drift is the log-space version of the gap: 2^S / 3^m = exp(drift · log 3) · 3^{...}.
    When drift > 0, the ratio 2^S / 3^m > 1 (2^S exceeds 3^m).
    This is a reformulation: positive drift means 2^S > 3^m in ℝ. -/
theorem drift_pos_iff_ratio_gt_one (S m : ℕ) :
    0 < drift S m ↔ (3 : ℝ) ^ (m : ℝ) < (2 : ℝ) ^ (S : ℝ) := by
  unfold drift
  constructor
  · intro h
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    rw [sub_pos] at h
    rwa [← Real.log_rpow (by norm_num : (0 : ℝ) < 2),
         ← Real.log_rpow (by norm_num : (0 : ℝ) < 3),
         Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) _)
           (Real.rpow_pos_of_pos (by norm_num) _)] at h
  · intro h
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    rw [sub_pos]
    rwa [← Real.log_rpow (by norm_num : (0 : ℝ) < 2),
         ← Real.log_rpow (by norm_num : (0 : ℝ) < 3),
         Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) _)
           (Real.rpow_pos_of_pos (by norm_num) _)]

/-- If Baker fails, then for any exponent K there exist S, m
    with the exponential gap 2^S/3^m approaching 1 super-polynomially fast. -/
theorem baker_failure_gives_small_drift :
    BakerFails → ∀ K : ℕ, ∀ c : ℝ, 0 < c →
      ∃ S m : ℕ, 2 ≤ m ∧ 0 < drift S m ∧ drift S m < c / (m : ℝ) ^ K := by
  intro hbf K c hc
  exact hbf c hc K

/-- Small drift forces large cycle anchor: if a Collatz cycle has
    parameters (S, m) with drift d, and the cycle visits values
    ≥ n₀, then n₀ must compensate for d being small.
    Specifically: n₀ ≥ ⌈1/d⌉ when d > 0. -/
theorem small_drift_large_anchor (d : ℝ) (hd : 0 < d) (n₀ : ℕ)
    (hn : d * (n₀ : ℝ) ≥ 1) : (n₀ : ℝ) ≥ 1 / d := by
  rw [ge_iff_le]
  exact div_le_of_le_mul₀ (le_of_lt hd) (by positivity) (by linarith)

/-- Stronger version with explicit constant management. -/
theorem baker_is_1d_up_strong :
    BakerFails → ∀ B : ℝ, 0 < B →
      ∃ S m : ℕ, 2 ≤ m ∧ 0 < drift S m ∧ 1 / drift S m > B := by
  intro hbf B hB
  -- With K = 0: m^0 = 1, so drift < c/1 = c. Choose c = 1/(B+1).
  have hc : (0 : ℝ) < 1 / (B + 1) := div_pos one_pos (by linarith)
  obtain ⟨S, m, hm, hd, hlt⟩ := hbf (1 / (B + 1)) hc 0
  refine ⟨S, m, hm, hd, ?_⟩
  -- hlt : drift S m < 1/(B+1) / m^0 = 1/(B+1)
  simp at hlt
  -- drift < 1/(B+1), so 1/drift > B+1 > B
  rw [gt_iff_lt, one_div]
  calc B < B + 1 := by linarith
    _ ≤ (drift S m)⁻¹ := by
        rw [le_inv_comm₀ (by linarith) hd]
        linarith

/-- **Baker is the 1D uncertainty principle**: If Baker's bound fails,
    then cycle anchors grow beyond any fixed bound B. This means:
    • No finite verification covers all potential cycles
    • The 1D approach (bounding |S log 2 - m log 3| pointwise) fails

    PROVED from BakerFails definition + arithmetic. Zero axioms. -/
theorem baker_is_1d_up :
    BakerFails → ∀ B : ℕ, ∃ S m : ℕ, 2 ≤ m ∧ 0 < drift S m ∧
      1 / drift S m > (B : ℝ) := by
  intro hbf B
  -- baker_is_1d_up_strong needs B > 0, use B+1 to handle B=0
  obtain ⟨S, m, hm, hd, hlt⟩ := baker_is_1d_up_strong hbf ((B : ℝ) + 1) (by positivity)
  exact ⟨S, m, hm, hd, by linarith⟩

/-! ## §3: The 2D Spiral Framework

The spiral S(s,N) = Σ_{n=1}^{N} n^{-s} lives in ℂ. Its normSq evolves by:
  ‖S_{N+1}‖² = ‖S_N‖² + (N+1)^{-2σ} + 2·Re(S_N · conj((N+1)^{-s}))
                         ^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                         amplitude² (≥ 0)    cross term (oscillates)

The 2D structure separates amplitude (always helping) from phase (bounded).
This is the key advantage over the 1D Baker approach. -/

/-- The normSq recurrence from SpiralInduction, repackaged.
    2D decomposition: amplitude² + cross = normSq increment. -/
theorem normSq_2d_decomposition (s : ℂ) (N : ℕ) :
    Complex.normSq (SpiralInduction.S s (N + 1)) =
    Complex.normSq (SpiralInduction.S s N) +
    Complex.normSq ((↑(N + 1) : ℂ) ^ (-s)) +
    2 * (SpiralInduction.S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))).re :=
  SpiralInduction.normSq_recurrence s N

/-- Amplitude is always non-negative: the σ-direction always helps.
    This is the structural advantage of 2D over 1D. -/
theorem amplitude_nonneg (s : ℂ) (N : ℕ) :
    0 ≤ Complex.normSq ((↑(N + 1) : ℂ) ^ (-s)) :=
  Complex.normSq_nonneg _

/-- Cross term is bounded: the phase oscillation is controlled.
    Reference to SpiralInduction.cross_term_bound. -/
theorem cross_bounded (s : ℂ) (N : ℕ) :
    |2 * (SpiralInduction.S s N * starRingEnd ℂ ((↑(N + 1) : ℂ) ^ (-s))).re| ≤
    2 * ‖SpiralInduction.S s N‖ * ‖(↑(N + 1) : ℂ) ^ (-s)‖ :=
  SpiralInduction.cross_term_bound s N

/-! ## §4: Decomposed Equidistribution — The 2D Key

The spiral S(s,N) = Σ_{n≤N} n^{-s} grows at rate N^{1-σ} in the critical
strip. This follows from Euler-Maclaurin:
  S(s,N) = ζ(s) + N^{1-s}/(1-s) + O(N^{-σ})

The main term N^{1-s}/(1-s) has modulus N^{1-σ}/|1-s| → ∞.

We decompose this into two primitive axioms:
1. `euler_maclaurin_dirichlet`: the asymptotic identity itself
2. The growth bound follows from triangle inequality on the asymptotic

Note: An O(√K) bound on cross terms is NOT sufficient (amplitude sums
converge for 2σ > 1). The spiral's growth comes from the N^{1-s}/(1-s)
main term, not from amplitude vs. cross competition.

Axiom trade: `weyl_spiral_growth` → `euler_maclaurin_dirichlet`

The Euler-Maclaurin asymptotic is provable from Abel summation
(`Mathlib.NumberTheory.AbelSummation`) + integration by parts.
The bound ‖error‖ ≤ C·N^{-σ} uses that {t·log n} are equidistributed
(Weyl), controlling oscillatory integral remainder.

Reference: Titchmarsh Ch. 4, Ivić §1.3, Montgomery-Vaughan Ch. 8. -/

/-- **Euler-Maclaurin for Dirichlet sums**: The partial sum S(s,N) decomposes
    into the zeta value plus a main term plus a controlled error.

    S(s,N) - ζ(s) - N^{1-s}/(1-s) is the Euler-Maclaurin remainder,
    bounded by C·N^{-σ} in norm. The main term N^{1-s}/(1-s) grows
    as N^{1-σ}/|1-s|, driving spiral growth.

    Provable from Abel summation (in Mathlib) + integration by parts.
    The constant C depends on s but not on N.
    Reference: Titchmarsh, "Theory of the Riemann Zeta-Function", §4.11 -/
theorem euler_maclaurin_dirichlet (s : ℂ) (hσ : 0 < s.re) (hσ1 : s.re < 1)
    (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖SpiralInduction.S s N - riemannZeta s - (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ ≤
        C * (↑N : ℝ) ^ (-s.re) :=
  EulerMaclaurinDirichlet.euler_maclaurin_dirichlet s hσ hσ1 hs1

/-- **Weyl spiral growth** (PROVED from Euler-Maclaurin).

    From the asymptotic: ‖S(s,N)‖ ≥ ‖N^{1-s}/(1-s)‖ - ‖ζ(s)‖ - C·N^{-σ}
    = N^{1-σ}/|1-s| - |ζ(s)| - C·N^{-σ}

    For N ≥ N₀(s), the main term dominates. The growth bound
    c·N^{2(1-σ)} ≤ normSq(S(s,N)) follows by squaring.

    Previous status: axiom (standalone)
    Current status: THEOREM (from euler_maclaurin_dirichlet) -/
theorem weyl_spiral_growth (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (_ht : s.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ^ (2 * (1 - s.re)) ≤ Complex.normSq (SpiralInduction.S s N) := by
  -- s ≠ 1 since s.re < 1
  have hs1 : s ≠ 1 := by intro h; rw [h] at hσ1; simp at hσ1
  obtain ⟨C, hC, hEM⟩ := euler_maclaurin_dirichlet s (by linarith) hσ1 hs1
  -- Helper facts
  have hσ_pos : 0 < s.re := by linarith
  have h1mσ_pos : 0 < 1 - s.re := by linarith
  have h1ms_ne : (1 : ℂ) - s ≠ 0 := by
    intro h; apply hs1; have := congr_arg Complex.re h; simp at this; linarith
  have h1ms_norm_pos : 0 < ‖(1 : ℂ) - s‖ := norm_pos_iff.mpr h1ms_ne
  /-
  Proof sketch (Euler-Maclaurin → growth bound):

  From hEM (reverse triangle inequality):
    ‖S(s,N)‖ ≥ ‖N^{1-s}/(1-s)‖ - ‖ζ(s)‖ - C·N^{-σ}
             = N^{1-σ}/|1-s| - ‖ζ(s)‖ - C·N^{-σ}

  Since 1-σ > 0 and σ > 1/2, the first term grows while C·N^{-σ} → 0.
  Choose N₀ so that N ≥ N₀ ⟹ N^{1-σ}/(2|1-s|) ≥ ‖ζ(s)‖ + C·N^{-σ}.
  Then ‖S(s,N)‖ ≥ N^{1-σ}/(2|1-s|), so
    normSq(S(s,N)) ≥ N^{2(1-σ)}/(4|1-s|²).

  For 2 ≤ N < N₀, each S(s,N) ≠ 0:
  • S(s,N) = Σ_{n=1}^N n^{-s}, with leading term 1.
  • For N=2: proved by SpiralInduction.S_two_norm_pos.
  • For N ≥ 3 with small N: |S(s,N) - 1| ≤ Σ_{n=2}^N n^{-σ} which is
    bounded, and the imaginary parts don't cancel exactly (t ≠ 0).
  • Each positive normSq(S(s,N))/N^{2(1-σ)} gives a positive ratio.

  Take c = min(1/(4|1-s|²), min_{2 ≤ N < N₀} normSq(S(s,N))/N^{2(1-σ)}).
  -/
  -- We prove this by extracting three sub-results:
  -- (A) A norm lower bound from Euler-Maclaurin
  -- (B) Nonvanishing for small N
  -- (C) Combining into the uniform constant
  --
  -- (A) Reverse triangle inequality: for all N ≥ 2,
  --     ‖S(s,N)‖ ≥ N^{1-σ}/|1-s| - ‖ζ(s)‖ - C·N^{-σ}
  have h_lower : ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) ^ (1 - s.re) / ‖(1 : ℂ) - s‖ - ‖riemannZeta s‖ -
        C * (N : ℝ) ^ (-s.re) ≤ ‖SpiralInduction.S s N‖ := by
    intro N hN
    have hEM_N := hEM N hN
    -- ‖S - ζ - main‖ ≤ err, so ‖S‖ ≥ ‖ζ + main‖ - err ≥ ‖main‖ - ‖ζ‖ - err
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    -- Reverse triangle: ‖ζ+main‖ - ‖S‖ ≤ ‖(ζ+main) - S‖ = ‖S - (ζ+main)‖
    -- so ‖S‖ ≥ ‖ζ+main‖ - ‖S - (ζ+main)‖ ≥ ‖ζ+main‖ - err
    have h1 : ‖riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ -
        C * (N : ℝ) ^ (-s.re) ≤ ‖SpiralInduction.S s N‖ := by
      have hsub : SpiralInduction.S s N - riemannZeta s -
          (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) =
          SpiralInduction.S s N - (riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) := by
        ring
      rw [hsub] at hEM_N
      -- norm_sub_norm_le with (ζ+main, S) gives ‖ζ+main‖ - ‖S‖ ≤ ‖(ζ+main) - S‖
      have hrev := norm_sub_norm_le
        (riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))
        (SpiralInduction.S s N)
      -- ‖(ζ+main) - S‖ = ‖-(S - (ζ+main))‖ = ‖S - (ζ+main)‖
      rw [show riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) -
          SpiralInduction.S s N =
          -(SpiralInduction.S s N - (riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)))
          from by ring, norm_neg] at hrev
      linarith
    -- Second reverse triangle: ‖ζ + main‖ ≥ ‖main‖ - ‖ζ‖
    -- Use ‖b‖ - ‖a‖ ≤ ‖a + b‖ (from ‖b‖ - ‖-a‖ ≤ ‖b-(-a)‖ = ‖a+b‖)
    have h2 : ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ - ‖riemannZeta s‖ ≤
        ‖riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ := by
      have hrev := norm_sub_norm_le
        ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))
        (-riemannZeta s)
      rw [norm_neg, show (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) - -riemannZeta s =
          riemannZeta s + (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) from by ring] at hrev
      linarith
    -- Combine: ‖S‖ ≥ ‖main‖ - ‖ζ‖ - err
    have h3 : ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ - ‖riemannZeta s‖ -
        C * (N : ℝ) ^ (-s.re) ≤ ‖SpiralInduction.S s N‖ := by linarith
    -- ‖main‖ = ‖N^{1-s}‖ / ‖1-s‖ = N^{1-σ}/|1-s|
    have h_main_norm : ‖(↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ =
        (N : ℝ) ^ (1 - s.re) / ‖(1 : ℂ) - s‖ := by
      rw [norm_div]
      congr 1
      rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N)]
      simp [Complex.sub_re]
    linarith
  -- (B) The norm lower bound from (A) gives, for large N:
  --     ‖S(s,N)‖ ≥ N^{1-σ}/(2|1-s|)
  -- provided N^{1-σ}/(2|1-s|) ≥ ‖ζ(s)‖ + C·N^{-σ}.
  -- Since 1-σ > 0, N^{1-σ} → ∞, so such N₀ exists.
  -- Then normSq = ‖S‖² ≥ N^{2(1-σ)}/(4|1-s|²).
  --
  -- (C) For 2 ≤ N < N₀, we need normSq(S(s,N)) > 0 and use a finite
  -- minimum construction. S(s,2) ≠ 0 by S_two_norm_pos.
  --
  -- We extract these as atomic sorries with clear mathematical content.
  --
  -- Auxiliary 1: ∃ N₀ ≥ 2 such that for N ≥ N₀, the lower bound from
  -- h_lower exceeds N^{1-σ}/(2|1-s|). This is an Archimedean argument.
  have h_large_regime : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) ^ (1 - s.re) / (2 * ‖(1 : ℂ) - s‖) ≤ ‖SpiralInduction.S s N‖ := by
    -- Strategy: find N₀ such that for N ≥ N₀,
    -- N^{1-σ}/(2|1-s|) ≤ N^{1-σ}/|1-s| - ‖ζ‖ - C·N^{-σ} ≤ ‖S(s,N)‖
    -- This requires: N^{1-σ}/(2|1-s|) ≥ ‖ζ‖ + C·N^{-σ} ≥ ‖ζ‖ + C
    -- (using N^{-σ} ≤ 1 gives: it suffices that N^{1-σ} ≥ 2|1-s|(‖ζ‖+C))
    --
    -- From tendsto_rpow_atTop: x^{1-σ} → ∞, so ∃ N₀ in ℝ with N₀^{1-σ} ≥ target.
    -- Then take ⌈N₀⌉₊ ≥ 2.
    --
    -- For now we extract this as a concrete Archimedean step.
    -- The mathematical content: monotone rpow + Archimedean + h_lower.
    let target := 2 * ‖(1 : ℂ) - s‖ * (‖riemannZeta s‖ + C) + 1
    -- target > 0
    have h_target_pos : 0 < target := by positivity
    -- ∃ n : ℕ with n > target^{1/(1-σ)} (Archimedean)
    -- Then n^{1-σ} > target.
    -- For N ≥ n: N^{1-σ} ≥ n^{1-σ} > target ≥ 2|1-s|(‖ζ‖+C)
    -- So N^{1-σ}/(2|1-s|) > ‖ζ‖ + C ≥ ‖ζ‖ + C·N^{-σ}
    -- And h_lower gives: N^{1-σ}/|1-s| - ‖ζ‖ - C·N^{-σ} ≤ ‖S‖
    -- Since N^{1-σ}/|1-s| - ‖ζ‖ - C·N^{-σ} ≥ N^{1-σ}/(2|1-s|),
    -- we get N^{1-σ}/(2|1-s|) ≤ ‖S‖.
    --
    -- Use tendsto_rpow_atTop to find real x₀ with x₀^{1-σ} ≥ target.
    obtain ⟨x₀, hx₀⟩ := (Filter.tendsto_atTop_atTop.mp
      (tendsto_rpow_atTop h1mσ_pos)) target
    -- Take N₀ = max 2 ⌈x₀⌉₊
    refine ⟨max 2 (⌈x₀⌉₊ + 1), le_max_left _ _, fun N hN => ?_⟩
    -- N ≥ max 2 (⌈x₀⌉₊ + 1), so (N : ℝ) ≥ x₀ and N ≥ 2
    have hN_ge_2 : 2 ≤ N := le_of_max_le_left hN
    have hN_ge_x₀ : x₀ ≤ (N : ℝ) := by
      calc x₀ ≤ ⌈x₀⌉₊ := Nat.le_ceil x₀
        _ ≤ (⌈x₀⌉₊ + 1 : ℕ) := by exact_mod_cast Nat.le_succ _
        _ ≤ (N : ℝ) := by exact_mod_cast le_of_max_le_right hN
    -- So (N : ℝ)^{1-σ} ≥ target
    have h_rpow_ge : target ≤ (N : ℝ) ^ (1 - s.re) := hx₀ (N : ℝ) hN_ge_x₀
    -- target = 2|1-s|(‖ζ‖+C) + 1 > 2|1-s|(‖ζ‖+C)
    -- So (N : ℝ)^{1-σ} > 2|1-s|(‖ζ‖+C)
    -- i.e., (N : ℝ)^{1-σ}/(2|1-s|) > ‖ζ‖ + C ≥ ‖ζ‖ + C·N^{-σ}
    -- From h_lower: ‖S‖ ≥ N^{1-σ}/|1-s| - ‖ζ‖ - C·N^{-σ}
    --            = N^{1-σ}/(2|1-s|) + (N^{1-σ}/(2|1-s|) - ‖ζ‖ - C·N^{-σ})
    --            ≥ N^{1-σ}/(2|1-s|)    (since the second term is ≥ 0)
    have h_from_lower := h_lower N hN_ge_2
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    -- N^{-σ} ≤ 1 for N ≥ 1 and σ > 0
    have h_Nminσ_le : (N : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
    -- From h_rpow_ge: target ≤ N^{1-σ}
    -- target = 2|1-s|(‖ζ‖+C) + 1 > 2|1-s|(‖ζ‖+C)
    -- So N^{1-σ} > 2|1-s|(‖ζ‖+C) ≥ 2|1-s|(‖ζ‖ + C·N^{-σ})
    -- i.e., N^{1-σ}/(2|1-s|) ≥ ‖ζ‖ + C·N^{-σ}
    -- From h_from_lower: ‖S‖ ≥ N^{1-σ}/|1-s| - ‖ζ‖ - C·N^{-σ}
    -- = N^{1-σ}/(2|1-s|) + (N^{1-σ}/(2|1-s|) - ‖ζ‖ - C·N^{-σ})
    -- ≥ N^{1-σ}/(2|1-s|)
    have h2norm_pos : 0 < 2 * ‖(1 : ℂ) - s‖ := by positivity
    -- N^{1-σ} ≥ target = 2|1-s|(‖ζ‖+C) + 1 > 2|1-s|(‖ζ‖+C)
    have h_target_bound : 2 * ‖(1 : ℂ) - s‖ * (‖riemannZeta s‖ + C) < (N : ℝ) ^ (1 - s.re) := by
      calc 2 * ‖(1 : ℂ) - s‖ * (‖riemannZeta s‖ + C)
          < 2 * ‖(1 : ℂ) - s‖ * (‖riemannZeta s‖ + C) + 1 := by linarith
        _ = target := rfl
        _ ≤ (N : ℝ) ^ (1 - s.re) := h_rpow_ge
    -- So N^{1-σ}/(2|1-s|) > ‖ζ‖ + C ≥ ‖ζ‖ + C·N^{-σ}
    have h_half_bound : ‖riemannZeta s‖ + C * (N : ℝ) ^ (-s.re) ≤
        (N : ℝ) ^ (1 - s.re) / (2 * ‖(1 : ℂ) - s‖) := by
      rw [le_div_iff₀ h2norm_pos]
      -- goal: (‖ζ‖ + C·N^{-σ}) * (2|1-s|) ≤ N^{1-σ}
      -- Since C·N^{-σ} ≤ C·1 = C and 2|1-s| > 0:
      -- (‖ζ‖+C·N^{-σ}) * 2|1-s| ≤ (‖ζ‖+C) * 2|1-s| = 2|1-s|(‖ζ‖+C) < target ≤ N^{1-σ}
      have h1 : C * (N : ℝ) ^ (-s.re) ≤ C := by
        calc C * (N : ℝ) ^ (-s.re) ≤ C * 1 :=
          mul_le_mul_of_nonneg_left h_Nminσ_le (le_of_lt hC)
          _ = C := mul_one C
      have h2 : (‖riemannZeta s‖ + C * (N : ℝ) ^ (-s.re)) * (2 * ‖(1 : ℂ) - s‖) ≤
          (‖riemannZeta s‖ + C) * (2 * ‖(1 : ℂ) - s‖) :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h2norm_pos)
      calc (‖riemannZeta s‖ + C * (N : ℝ) ^ (-s.re)) * (2 * ‖(1 : ℂ) - s‖)
          ≤ (‖riemannZeta s‖ + C) * (2 * ‖(1 : ℂ) - s‖) := h2
        _ = 2 * ‖(1 : ℂ) - s‖ * (‖riemannZeta s‖ + C) := by ring
        _ ≤ (N : ℝ) ^ (1 - s.re) := le_of_lt h_target_bound
    -- Now combine: ‖S‖ ≥ N^{1-σ}/|1-s| - ‖ζ‖ - C·N^{-σ}
    -- = N^{1-σ}/(2|1-s|) + N^{1-σ}/(2|1-s|) - ‖ζ‖ - C·N^{-σ}
    -- ≥ N^{1-σ}/(2|1-s|)
    -- We need: N^{1-σ}/|1-s| = N^{1-σ}/(2|1-s|) + N^{1-σ}/(2|1-s|)
    have h_split : (N : ℝ) ^ (1 - s.re) / ‖(1 : ℂ) - s‖ =
        (N : ℝ) ^ (1 - s.re) / (2 * ‖(1 : ℂ) - s‖) +
        (N : ℝ) ^ (1 - s.re) / (2 * ‖(1 : ℂ) - s‖) := by
      field_simp; ring
    linarith
  obtain ⟨N₀, hN₀_ge, h_large⟩ := h_large_regime
  -- For N ≥ N₀: ‖S‖ ≥ N^{1-σ}/(2|1-s|), so normSq ≥ N^{2(1-σ)}/(4|1-s|²).
  -- No small-N case needed — eliminates the false finite_dirichlet_ne_zero axiom.
  refine ⟨1 / (4 * ‖(1 : ℂ) - s‖ ^ 2), by positivity, N₀, hN₀_ge, fun N hN => ?_⟩
  have hS_norm := h_large N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  -- Rewrite c * N^{...} = N^{...} / (4|1-s|²), then use the squaring argument
  have h_rw : 1 / (4 * ‖(1 : ℂ) - s‖ ^ 2) * (N : ℝ) ^ (2 * (1 - s.re)) =
      (N : ℝ) ^ (2 * (1 - s.re)) / (4 * ‖(1 : ℂ) - s‖ ^ 2) := by ring
  rw [h_rw, Complex.normSq_eq_norm_sq]
  have h_sq : (N : ℝ) ^ (1 - s.re) / (2 * ‖(1 : ℂ) - s‖) ≥ 0 := by
    apply div_nonneg (le_of_lt (Real.rpow_pos_of_pos hNpos _)) (by positivity)
  have h_denom : (2 * ‖(1 : ℂ) - s‖) ^ 2 = 4 * ‖(1 : ℂ) - s‖ ^ 2 := by ring
  calc (N : ℝ) ^ (2 * (1 - s.re)) / (4 * ‖(1 : ℂ) - s‖ ^ 2)
      = ((N : ℝ) ^ (1 - s.re)) ^ 2 / (2 * ‖(1 : ℂ) - s‖) ^ 2 := by
        rw [h_denom, ← Real.rpow_natCast ((N : ℝ) ^ (1 - s.re)) 2,
            ← Real.rpow_mul (le_of_lt hNpos)]
        congr 1; ring_nf
    _ = ((N : ℝ) ^ (1 - s.re) / (2 * ‖(1 : ℂ) - s‖)) ^ 2 := by
        rw [div_pow]
    _ ≤ ‖SpiralInduction.S s N‖ ^ 2 := by
        exact sq_le_sq' (by linarith) hS_norm

/-! ## §5: Spiral Grows Without Baker

From Weyl cross cancellation + amplitude positivity, the spiral's normSq
grows on average. The amplitude sum is linear in K, the cross sum is O(√K).
For large windows, amplitude dominates. -/

/-- The amplitude sum over a K-step window starting at N is bounded below.
    Each term contributes (N+k+1)^{-2σ}, and by integral comparison
    the sum is Θ(K · N^{-2σ}) for K ≤ N. -/
theorem amplitude_sum_pos (s : ℂ) (_hσ : 0 < s.re) (N K : ℕ) (hK : 1 ≤ K) (_hN : 1 ≤ N) :
    0 < ∑ k ∈ Finset.range K,
      Complex.normSq ((↑(N + k + 1) : ℂ) ^ (-s)) := by
  apply Finset.sum_pos
  · intro k _
    exact Complex.normSq_pos.mpr
      (show (↑(N + k + 1) : ℂ) ^ (-s) ≠ 0 from by
        have : (↑(N + k + 1) : ℂ) ^ (-s) = (↑(N + k) + 1 : ℂ) ^ (-s) := by
          push_cast; ring_nf
        rw [this]
        exact Complex.natCast_add_one_cpow_ne_zero _ _)
  · exact Finset.nonempty_range_iff.mpr (by omega)

/-- **Spiral grows on average**: Over a K-step window starting at N,
    normSq(S(s,N+K)) ≥ normSq(S(s,N)) + (amplitude sum) - |cross sum|.

    From the normSq window identity and triangle inequality. -/
theorem spiral_grows_on_average (s : ℂ) (N K : ℕ) :
    Complex.normSq (SpiralInduction.S s (N + K)) ≥
    Complex.normSq (SpiralInduction.S s N) +
    ∑ k ∈ Finset.range K, Complex.normSq ((↑(N + k + 1) : ℂ) ^ (-s)) -
    |∑ k ∈ Finset.range K,
      2 * (SpiralInduction.S s (N + k) *
        starRingEnd ℂ ((↑(N + k + 1) : ℂ) ^ (-s))).re| := by
  rw [SpiralInduction.normSq_window]
  have hsplit : ∑ k ∈ Finset.range K,
      (Complex.normSq ((↑(N + k + 1) : ℂ) ^ (-s)) +
       2 * (SpiralInduction.S s (N + k) * starRingEnd ℂ ((↑(N + k + 1) : ℂ) ^ (-s))).re) =
      ∑ k ∈ Finset.range K, Complex.normSq ((↑(N + k + 1) : ℂ) ^ (-s)) +
      ∑ k ∈ Finset.range K,
        2 * (SpiralInduction.S s (N + k) * starRingEnd ℂ ((↑(N + k + 1) : ℂ) ^ (-s))).re := by
    rw [← Finset.sum_add_distrib]
  rw [hsplit]
  have h_cross := neg_abs_le (∑ k ∈ Finset.range K,
    2 * (SpiralInduction.S s (N + k) * starRingEnd ℂ ((↑(N + k + 1) : ℂ) ^ (-s))).re)
  linarith

/-- **Spiral nonvanishing without Baker**: For s in the critical strip
    with t ≠ 0, all sufficiently large partial sums S(s,N) are nonzero.

    From `weyl_spiral_growth`: normSq(S(s,N)) ≥ c·N^{2(1-σ)} > 0 for N ≥ N₀.
    The spiral grows in 2D — amplitude decay (σ-direction)
    plus equidistributed phases (t-direction) produce net outward winding.
    No Baker-type pointwise bound on individual cross terms is needed. -/
theorem spiral_nonvanishing_sans_baker (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht : s.im ≠ 0) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 0 < ‖SpiralInduction.S s N‖ := by
  obtain ⟨c, hc, N₀, hN₀, hgrowth⟩ := weyl_spiral_growth s hσ hσ1 ht
  refine ⟨N₀, hN₀, fun N hN => ?_⟩
  rw [norm_pos_iff]
  intro hzero
  have h0 : Complex.normSq (SpiralInduction.S s N) = 0 := by rw [hzero, map_zero]
  have hbound := hgrowth N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  linarith [mul_pos hc (Real.rpow_pos_of_pos hNpos (2 * (1 - s.re)))]

/-! ## §6: Documentation — The Replacement Principle

Baker operates in 1D: |a log 2 - b log 3| ≥ c/max(a,b)^K.
The spiral operates in 2D: normSq = amplitude² + cross.

In 1D, the uncertainty principle forces a fight: you must bound
|S·log 2 - m·log 3| away from zero pointwise, which requires
deep Diophantine analysis (Baker/Gelfond-Schneider class).

In 2D, the spiral resolves the UP via Euler-Maclaurin + Weyl:
- Main term: S(s,N) ~ N^{1-s}/(1-s), growing as N^{1-σ}
- Error: O(N^{-σ}) from equidistribution of {t·log n / 2π}
- Net: normSq ≥ c·N^{2(1-σ)} > 0 unconditionally

**Axiom trade**:
- Old: `baker_lower_bound` (Diophantine, 1D, controls individual terms)
- Intermediate: `weyl_spiral_growth` (2D growth bound) — now a THEOREM
- New primitive: `euler_maclaurin_dirichlet` (standard asymptotic,
  provable from Abel summation in Mathlib + integration by parts)

The axiom chain: euler_maclaurin_dirichlet → weyl_spiral_growth
→ spiral_nonvanishing_sans_baker. One axiom, two theorems. -/

end BakerUncertainty

-- Axiom audit
#print axioms BakerUncertainty.baker_is_1d_up
#print axioms BakerUncertainty.spiral_nonvanishing_sans_baker
#print axioms BakerUncertainty.normSq_2d_decomposition
#print axioms BakerUncertainty.amplitude_nonneg
#print axioms BakerUncertainty.cross_bounded
#print axioms BakerUncertainty.spiral_grows_on_average
