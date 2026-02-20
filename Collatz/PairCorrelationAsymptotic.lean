/-
  PairCorrelationAsymptotic.lean — Pair Correlation Growth via Tauberian Theory
  ==============================================================================

  "Nonneg coefficients + positive pole = linear growth. QED."

  Applies Landau's Tauberian theorem (LandauTauberian.lean) to the pair
  Dirichlet series (PairSeriesPole.lean) to obtain:

    pairCorrelation 1 x / x → A > 0

  This replaces the Perron explicit formula approach (pair_perron_contour_shift,
  pair_perron_zero_sum_bound, pair_perron_T_balance) with a purely real-variable
  argument. No contour integration, no zero sum bounds, no T-balancing.

  The three pair Perron axioms are eliminated.
-/
import Collatz.LandauTauberian
import Collatz.PairSeriesPole
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Finset Real ArithmeticFunction Filter

namespace PairCorrelationAsymptotic

/-- Pair correlation: Σ_{n ≤ x} Λ(n) · Λ(n + 2h).
    Duplicated from PrimeGapBridge to avoid import cycle. -/
noncomputable def pairCorrelation (h : ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 x, (Λ n : ℝ) * Λ (n + 2 * h)

/-- The pair correlation equals the sum of pairCoeff. -/
private lemma pairCorrelation_eq (x : ℕ) :
    pairCorrelation 1 x = ∑ n ∈ Icc 1 x, PairSeriesPole.pairCoeff n := by
  unfold pairCorrelation PairSeriesPole.pairCoeff
  congr 1

/-- **Pair correlation grows linearly** — the Tauberian asymptotic.

    Direct application of landau_tauberian with a(n) = Λ(n)·Λ(n+2):
    - Nonnegativity: vonMangoldt_nonneg × vonMangoldt_nonneg
    - Convergence: pair_series_summable
    - Pole: pair_series_pole -/
theorem pair_correlation_asymptotic :
    ∃ A : ℝ, 0 < A ∧
    Tendsto (fun x : ℕ => (pairCorrelation 1 x : ℝ) / (x : ℝ))
      atTop (nhds A) := by
  obtain ⟨A, hA, hpole⟩ := PairSeriesPole.pair_series_pole
  refine ⟨A, hA, ?_⟩
  have h_eq : (fun x : ℕ => (pairCorrelation 1 x : ℝ) / (x : ℝ)) =
      (fun x : ℕ => (∑ n ∈ Icc 1 x, PairSeriesPole.pairCoeff n) / (x : ℝ)) := by
    ext x; rw [pairCorrelation_eq]
  rw [h_eq]
  exact LandauTauberian.landau_tauberian
    PairSeriesPole.pairCoeff
    PairSeriesPole.pairCoeff_nonneg
    PairSeriesPole.pair_series_summable
    A hA hpole

/-- **Pair correlation linear lower bound.**
    For some c > 0, eventually pairCorrelation 1 x ≥ c · x.
    This is the form needed by rh_implies_twin_primes. -/
theorem pair_correlation_lower_bound :
    ∃ (c : ℝ) (x₀ : ℕ), 0 < c ∧ ∀ x : ℕ, x₀ ≤ x →
      c * (x : ℝ) ≤ pairCorrelation 1 x := by
  obtain ⟨A, hA, hpole⟩ := PairSeriesPole.pair_series_pole
  have h_eq : (fun x : ℕ => (pairCorrelation 1 x : ℝ) / (x : ℝ)) =
      (fun x : ℕ => (∑ n ∈ Icc 1 x, PairSeriesPole.pairCoeff n) / (x : ℝ)) := by
    ext x; rw [pairCorrelation_eq]
  obtain ⟨c, x₀, hc, hx₀⟩ := LandauTauberian.landau_tauberian_linear_lower
    PairSeriesPole.pairCoeff
    PairSeriesPole.pairCoeff_nonneg
    PairSeriesPole.pair_series_summable
    A hA hpole
  refine ⟨c, x₀, hc, fun x hx => ?_⟩
  have h := hx₀ x hx
  calc c * (x : ℝ) ≤ ∑ n ∈ Icc 1 x, PairSeriesPole.pairCoeff n := h
    _ = pairCorrelation 1 x := (pairCorrelation_eq x).symm

end PairCorrelationAsymptotic
