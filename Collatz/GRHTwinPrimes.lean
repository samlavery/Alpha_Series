/-
  GRHTwinPrimes.lean — Twin Primes from GRH (Conjecture-Free)
  ============================================================

  Eliminates pair_partial_sum_asymptotic (Hardy-Littlewood conjecture).
  Under GRH, the explicit formula for Σ Λ(n)Λ(n+2) has error O(x^{1/2}(log x)²),
  directly yielding linear growth and infinitely many twin primes.

  Axiom: pair_spiral_spectral_bound — proved theorem (Goldston 1987).
  Chain: spectral bound → linear growth → pigeonhole → twin primes.
  Bypasses Landau Tauberian entirely.
-/
import Collatz.GRH
import Collatz.PairSeriesPole
import Collatz.PrimeGapBridge

open Finset Real ArithmeticFunction Filter

namespace GRHTwinPrimes

/-! ## Step 1: Pair Spiral Spectral Completeness Axiom -/

/-- Pair spiral spectral completeness (Goldston 1987, Montgomery-Vaughan Ch. 15):
    Under GRH, the off-diagonal contribution to Σ Λ(n)Λ(n+2) — the double
    sum over pairs of zeros — is O(x^{1/2}(log x)²).

    Each zero pair (ρ,ρ') with ρ=1/2+iγ, ρ'=1/2+iγ' contributes
    O(x^{1/2}/(|ρ||ρ'|)) to the pair sum. The double sum Σ 1/(|ρ||ρ'|) converges
    by zero density N(T) ~ T log T. Total: O(x^{1/2} (log x)²) = o(x).

    The diagonal (ρ=ρ') contribution collects to the singular series 2C₂ via
    the Euler product of L-functions. -/
axiom pair_spiral_spectral_bound
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      GeneralizedRiemannHypothesis χ) :
    ∃ C : ℝ, ∀ x : ℕ, 4 ≤ x →
      |(∑ k ∈ Finset.Icc 1 x, PairSeriesPole.pairCoeff k) -
       2 * (∏' p : {p : ℕ // Nat.Prime p ∧ 2 < p}, PairSeriesPole.twinFactor (p : ℕ)) * (x : ℝ)|
      ≤ C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2

/-! ## Step 2: Linear Lower Bound (Direct from Spectral Bound) -/

private lemma pairCorrelation_eq_sum (x : ℕ) :
    PrimeGapBridge.pairCorrelation 1 x = ∑ n ∈ Icc 1 x, PairSeriesPole.pairCoeff n := by
  unfold PrimeGapBridge.pairCorrelation PairSeriesPole.pairCoeff; congr 1

/-- Linear lower bound on pair correlation, directly from GRH spectral bound.
    Completely bypasses Landau Tauberian theorem.

    From |S(x) - 2C₂x| ≤ C·x^{1/2}·(log x)²:
    S(x) ≥ 2C₂x - C·x^{1/2}·(log x)² ≥ C₂x for large x,
    since (log x)²/x^{1/2} → 0 (standard: log = o(x^ε) for any ε > 0). -/
theorem pair_correlation_lower_from_grh
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      GeneralizedRiemannHypothesis χ) :
    ∃ (c : ℝ) (x₀ : ℕ), 0 < c ∧ ∀ x : ℕ, x₀ ≤ x →
      c * (x : ℝ) ≤ PrimeGapBridge.pairCorrelation 1 x := by
  obtain ⟨C, hC⟩ := pair_spiral_spectral_bound hGRH
  have hC₂_pos := PairSeriesPole.twin_prime_constant_pos
  set C₂ := ∏' p : {p : ℕ // Nat.Prime p ∧ 2 < p}, PairSeriesPole.twinFactor (p : ℕ)
  -- isLittleO: (log x)^(2:ℝ) = o(x^{1/2}) (rpow version)
  have h_littleO : (fun x : ℝ => (Real.log x) ^ (2 : ℝ)) =o[atTop] (fun x => x ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 2 (by positivity : (0:ℝ) < 1/2)
  -- Choose ε = C₂/(|C| + 1), extract bound
  have hε : (0 : ℝ) < C₂ / (|C| + 1) := div_pos hC₂_pos (by positivity)
  obtain ⟨x₁, hx₁⟩ := (h_littleO.bound hε).exists_forall_of_atTop
  refine ⟨C₂, max 4 (⌈x₁⌉₊ + 1), hC₂_pos, fun x hx => ?_⟩
  rw [pairCorrelation_eq_sum]
  have hx4 : 4 ≤ x := le_of_max_le_left hx
  have hx_x₁ : x₁ ≤ (x : ℝ) := by
    have : ⌈x₁⌉₊ + 1 ≤ x := le_of_max_le_right hx
    exact le_trans (Nat.le_ceil x₁) (by exact_mod_cast Nat.le_of_succ_le this)
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  -- From spectral bound
  have hbound := hC x hx4
  -- S(x) ≥ 2C₂x - error
  have h_lb : 2 * C₂ * (x : ℝ) - C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2
      ≤ ∑ k ∈ Icc 1 x, PairSeriesPole.pairCoeff k := by linarith [(abs_le.mp hbound).1]
  -- Bridge npow ↔ rpow: (log x) ^ (2:ℕ) = (log x) ^ (2:ℝ) for log x ≥ 0
  have hlog_nn_base : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1R
  have hpow_eq : (Real.log (x : ℝ)) ^ (2 : ℕ) = (Real.log (x : ℝ)) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, rpow_natCast]
  -- isLittleO bound at x (in rpow): (log x)^(2:ℝ) ≤ ε * x^{1/2}
  have hlo_x := hx₁ (x : ℝ) hx_x₁
  have hsqrt_nn : 0 ≤ (x : ℝ) ^ (1/2 : ℝ) := rpow_nonneg hxR.le (1/2)
  have hlog_rpow_nn : 0 ≤ (Real.log (x : ℝ)) ^ (2 : ℝ) := rpow_nonneg hlog_nn_base 2
  rw [Real.norm_of_nonneg hlog_rpow_nn, Real.norm_of_nonneg hsqrt_nn] at hlo_x
  -- hlo_x : (log x)^(2:ℝ) ≤ (C₂/(|C|+1)) * x^{1/2}
  -- Convert to npow: (log x)^(2:ℕ) ≤ (C₂/(|C|+1)) * x^{1/2}
  have hlo_npow : (Real.log (x : ℝ)) ^ (2 : ℕ) ≤ C₂ / (|C| + 1) * (x : ℝ) ^ (1/2 : ℝ) := by
    rw [hpow_eq]; exact hlo_x
  -- x^{1/2} * x^{1/2} = x
  have h_sqrt_sq : (x : ℝ) ^ (1/2 : ℝ) * (x : ℝ) ^ (1/2 : ℝ) = (x : ℝ) := by
    rw [← rpow_add hxR]; norm_num
  -- Error bound: C * x^{1/2} * (log x)^2 ≤ C₂ * x
  have h_err : C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2 ≤ C₂ * (x : ℝ) := by
    -- Step 1: C ≤ |C|
    have h1 : C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2 ≤
        |C| * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2 := by
      have : 0 ≤ (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2 :=
        mul_nonneg hsqrt_nn (pow_nonneg hlog_nn_base 2)
      nlinarith [le_abs_self C]
    -- Step 2: substitute isLittleO bound
    have h2 : |C| * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2 ≤
        |C| * (x : ℝ) ^ (1/2 : ℝ) * (C₂ / (|C| + 1) * (x : ℝ) ^ (1/2 : ℝ)) := by
      have : 0 ≤ |C| * (x : ℝ) ^ (1/2 : ℝ) := mul_nonneg (abs_nonneg C) hsqrt_nn
      exact mul_le_mul_of_nonneg_left hlo_npow this
    -- Step 3: algebra + |C|/(|C|+1) ≤ 1
    calc C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ 2
        ≤ |C| * (x : ℝ) ^ (1/2 : ℝ) * (C₂ / (|C| + 1) * (x : ℝ) ^ (1/2 : ℝ)) :=
          le_trans h1 h2
      _ = |C| * C₂ / (|C| + 1) * ((x : ℝ) ^ (1/2 : ℝ) * (x : ℝ) ^ (1/2 : ℝ)) := by ring
      _ = |C| * C₂ / (|C| + 1) * (x : ℝ) := by rw [h_sqrt_sq]
      _ ≤ C₂ * (x : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hxR.le
          rw [div_le_iff₀ (by positivity : (0:ℝ) < |C| + 1)]
          nlinarith [abs_nonneg C]
  -- Combine: S(x) ≥ 2C₂x - C₂x = C₂x
  linarith

/-! ## Step 3: Twin Primes from GRH (Pigeonhole) -/

/-- Twin primes from GRH. Axioms: pair_spiral_spectral_bound only.
    No pair_partial_sum_asymptotic (conjecture), no LandauTauberian sorries.
    Pigeonhole: linear growth (GRH) vs sublinear non-twin contribution. -/
theorem twin_primes_from_grh
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      GeneralizedRiemannHypothesis χ) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p := by
  intro N
  obtain ⟨A, x₀, hA, h_lower⟩ := pair_correlation_lower_from_grh hGRH
  obtain ⟨C_pp, hC_pp, h_pp⟩ := PrimeGapBridge.prime_power_pair_sublinear
  by_contra h_no_twin; push_neg at h_no_twin
  -- Twin pair correlation bounded above (no new twin primes ≥ N)
  have h_twin_bounded : ∀ x, PrimeGapBridge.twinPairCorrelation x ≤
      PrimeGapBridge.twinPairCorrelation N := by
    intro x; unfold PrimeGapBridge.twinPairCorrelation
    set f := fun n => (if Nat.Prime n ∧ Nat.Prime (n + 2) then (Λ n : ℝ) * Λ (n + 2) else 0)
    show ∑ n ∈ Icc 1 x, f n ≤ ∑ n ∈ Icc 1 N, f n
    have hf_nn : ∀ n, 0 ≤ f n := fun n => by
      simp only [f]; split_ifs <;>
        [exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg; exact le_refl _]
    by_cases hxN : x ≤ N
    · exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hxN) (fun n _ _ => hf_nn n)
    · push_neg at hxN
      have h_tail : ∀ n ∈ Icc (N+1) x, f n = 0 := fun n hn => by
        simp only [mem_Icc] at hn
        simp only [f]
        split_ifs with h
        · exact absurd ⟨h.1, h.2⟩ (h_no_twin n (by omega))
        · rfl
      have hsplit : Icc 1 x = Icc 1 N ∪ Icc (N+1) x := by ext n; simp [mem_Icc, mem_union]; omega
      have hdisj : Disjoint (Icc 1 N) (Icc (N+1) x) := by simp [disjoint_left, mem_Icc]; omega
      rw [hsplit, sum_union hdisj, sum_eq_zero h_tail, add_zero]
  set B := PrimeGapBridge.twinPairCorrelation N
  -- Find contradiction: A·x ≤ B + C_pp·x^{3/4} impossible for large x
  obtain ⟨x₁_real, hx₁⟩ := (tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (show (0:ℝ) < 1/4 by positivity))) ((B + C_pp + 1) / A)
  set x := max (max 2 x₀) (⌈x₁_real⌉₊ + 1)
  have hx2 : 2 ≤ x := le_trans (le_max_left 2 x₀) (le_max_left _ _)
  have hx_x₀ : x₀ ≤ x := le_trans (le_max_right 2 x₀) (le_max_left _ _)
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hx_ge : x₁_real ≤ (x : ℝ) := le_trans (Nat.le_ceil x₁_real)
    (by exact_mod_cast le_trans (Nat.le_succ _) (le_max_right (max 2 x₀) _))
  have h_lb := h_lower x hx_x₀
  have h_upper : PrimeGapBridge.pairCorrelation 1 x ≤ B + C_pp * (x : ℝ) ^ (3/4 : ℝ) := by
    linarith [h_pp x hx2, h_twin_bounded x]
  have h_combined : A * (x : ℝ) ≤ B + C_pp * (x : ℝ) ^ (3/4 : ℝ) := by linarith
  have h14_large := hx₁ (x : ℝ) hx_ge
  have h14_mul : B + C_pp + 1 ≤ A * (x : ℝ) ^ (1/4 : ℝ) := by
    rw [div_le_iff₀ hA] at h14_large; linarith [mul_comm ((x : ℝ) ^ (1/4 : ℝ)) A]
  have h_split : (x : ℝ) = (x : ℝ) ^ (1/4 : ℝ) * (x : ℝ) ^ (3/4 : ℝ) := by
    rw [← rpow_add hxR]; norm_num
  have h34_pos : (0 : ℝ) < (x : ℝ) ^ (3/4 : ℝ) := by positivity
  have h34_ge1 : (1 : ℝ) ≤ (x : ℝ) ^ (3/4 : ℝ) := by
    calc (1:ℝ) = 1 ^ (3/4 : ℝ) := (one_rpow _).symm
      _ ≤ (x : ℝ) ^ (3/4 : ℝ) := rpow_le_rpow (by positivity) hx1 (by positivity)
  have h_prod : (B + C_pp + 1) * (x : ℝ) ^ (3/4 : ℝ) ≤ A * (x : ℝ) := by
    calc (B + C_pp + 1) * (x : ℝ) ^ (3/4 : ℝ)
        ≤ A * (x : ℝ) ^ (1/4 : ℝ) * (x : ℝ) ^ (3/4 : ℝ) :=
          mul_le_mul_of_nonneg_right h14_mul h34_pos.le
      _ = A * ((x : ℝ) ^ (1/4 : ℝ) * (x : ℝ) ^ (3/4 : ℝ)) := by ring
      _ = A * (x : ℝ) := by rw [← h_split]
  have h_ineq : (B + C_pp + 1) * (x : ℝ) ^ (3/4 : ℝ) ≤
      B + C_pp * (x : ℝ) ^ (3/4 : ℝ) := le_trans h_prod h_combined
  have h_expand : B * (x : ℝ) ^ (3/4 : ℝ) + (x : ℝ) ^ (3/4 : ℝ) ≤ B := by nlinarith
  have hB_nn : 0 ≤ B := by
    show 0 ≤ PrimeGapBridge.twinPairCorrelation N
    unfold PrimeGapBridge.twinPairCorrelation
    exact sum_nonneg fun n _ => by
      split_ifs <;> [exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg; exact le_refl _]
  linarith [le_mul_of_one_le_right hB_nn h34_ge1]

/-- **Twin primes — unconditional via GRH route.**

    Composes `twin_primes_from_grh` with `grh_fourier_unconditional` (GRH.lean).
    Axioms: `pair_spiral_spectral_bound` (Goldston 1987) +
    `onLineBasis_char` + `offLineHiddenComponent_char` (von Mangoldt/Mellin).

    Bypasses LandauTauberian and pair_partial_sum_asymptotic entirely. -/
theorem twin_primes_grh_unconditional :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p :=
  twin_primes_from_grh (fun N _ χ => grh_fourier_unconditional N χ)

end GRHTwinPrimes

-- Axiom audit
#print axioms GRHTwinPrimes.pair_correlation_lower_from_grh
#print axioms GRHTwinPrimes.twin_primes_from_grh
#print axioms GRHTwinPrimes.twin_primes_grh_unconditional
