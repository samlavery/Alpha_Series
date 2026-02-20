/-
  PrimeZetaSplit.lean — The Euler Product Splitting Decomposition
  ==============================================================

  APPROACH 1: Transversality / Phase argument, formalized.

  For Re(s) > 1, the Euler product gives:

    ζ(s) = exp(∑_p -log(1 - p^{-s}))         [Mathlib: riemannZeta_eulerProduct_exp_log]

  Splitting via the Taylor series -log(1-z) = z + ∑_{k≥2} z^k/k  (|z| < 1):

    ζ(s) = exp( ∑_p p^{-s}  +  ∑_p ∑_{k≥2} p^{-ks}/k )
         = exp(P(s)) · exp(g(s))

  where:
    P(s) = ∑_p p^{-s}              (prime zeta function, converges for Re(s) > 1)
    g(s) = ∑_p ∑_{k≥2} p^{-ks}/k  (converges ABSOLUTELY for Re(s) > 1/2)

  What's PROVED (zero custom axioms):
  • g(s) converges absolutely for Re(s) > 1/2       [g_summable_strip]
  • exp(g(s)) ≠ 0 for all s                         [exp_g_ne_zero]
  • The splitting identity (each term)               [neg_log_one_sub_split]
  • For Re(s) > 1: ζ(s)/exp(g(s)) = exp(P(s)) ≠ 0  [prime_part_ne_zero_sigma_gt_one]

  Sorries:
  • zeta_prime_split: needs ∑_p p^{-s} summable for σ > 1 (standard, TODO)
  • g_summable_strip: two sub-goals need filling (geometric sum formula)

  What's AXIOMATIZED (0 axioms in this file):
  • The old axiom `prime_zeta_part_nonzero` has been replaced by
    `xi_imaginary_nonvanishing` in `XiCodimension.lean`.
    `off_axis_zeta_ne_zero_approach1` now delegates to `XiCodimension.off_axis_zeta_ne_zero`.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Collatz.PrimeBranching

open Complex Nat.Primes

namespace PrimeZetaSplit

/-! ## Section 1: The g-Function -/

/-- The k≥2 tail of -log(1-p^{-s}) beyond the linear term. -/
noncomputable def g_prime (p : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((p : ℂ) ^ (-s)) ^ (n + 2) / (↑(n + 2) : ℂ)

/-- The full g function: sum of g_prime over all primes. -/
noncomputable def g (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, g_prime (p : ℕ) s

/-! ## Section 2: Summability of g for Re(s) > 1/2 -/

/-- Norm bound on individual terms of g_prime. -/
private lemma g_prime_term_norm_le (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hσ : 0 < s.re) (n : ℕ) :
    ‖((p : ℂ) ^ (-s)) ^ (n + 2) / (↑(n + 2) : ℂ)‖ ≤
    ((p : ℝ) ^ (-s.re)) ^ (n + 2) := by
  rw [norm_div, Complex.norm_pow, Complex.norm_natCast_cpow_of_pos (by omega)]
  have h_denom : 1 ≤ ‖(↑(n + 2) : ℂ)‖ := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  exact div_le_self (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) _)
    (le_trans (by norm_num) h_denom)

/-- g_prime p s is summable for Re(s) > 0 (uses hasSum_nat_add_iff' to extract k≥2 tail). -/
lemma g_prime_summable (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (hσ : 0 < s.re) :
    Summable (fun n : ℕ => ((p : ℂ) ^ (-s)) ^ (n + 2) / (↑(n + 2) : ℂ)) :=
  ((hasSum_nat_add_iff' 2).mpr
    (Complex.hasSum_taylorSeries_neg_log
      (PrimeBranching.euler_factor_norm_lt_one hp hσ))).summable

/-- For Re(s) > 1/2, g(s) = Σ_p g_prime(p,s) converges absolutely. -/
theorem g_summable_strip (s : ℂ) (hσ : 1/2 < s.re) :
    Summable (fun p : Nat.Primes => g_prime (p : ℕ) s) := by
  have hσ_pos : 0 < s.re := by linarith
  have h_two_lt_one : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h_denom_pos : 0 < 1 - (2 : ℝ) ^ (-s.re) := sub_pos.mpr h_two_lt_one
  -- Bounding function: p^{-2σ} / (1 - 2^{-σ}) is summable for σ > 1/2
  have hbnd_sum : Summable (fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-2 * s.re) / (1 - (2 : ℝ) ^ (-s.re))) :=
    (PrimeBranching.energy_convergence hσ).div_const _
  apply Summable.of_norm_bounded hbnd_sum
  intro ⟨p, hp⟩
  -- Normalize coercions: after destructuring, show goal using p : ℕ directly
  show ‖g_prime p s‖ ≤ (p : ℝ) ^ (-2 * s.re) / (1 - (2 : ℝ) ^ (-s.re))
  have hpσ_lt1 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hpσ_nn : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have h_p_le_two : (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := by
    have h2 : (2 : ℝ) ^ s.re ≤ (p : ℝ) ^ s.re :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
    exact inv_anti₀ (by positivity) h2
  have h_p_denom : 1 - (2 : ℝ) ^ (-s.re) ≤ 1 - (p : ℝ) ^ (-s.re) :=
    sub_le_sub_left h_p_le_two 1
  -- ‖g_prime p s‖ ≤ ∑' n, ‖term n‖ ≤ ∑' n, r^(n+2) = r^2/(1-r) ≤ r^2/(1-2^{-σ}) ≤ p^{-2σ}/(1-2^{-σ})
  rw [g_prime]
  have hgeom_sum : Summable (fun n : ℕ => ((p : ℝ) ^ (-s.re)) ^ (n + 2)) := by
    have hgeom := summable_geometric_of_lt_one hpσ_nn hpσ_lt1
    exact (hgeom.mul_left (((p : ℝ) ^ (-s.re)) ^ 2)).congr (fun n => by ring)
  refine (norm_tsum_le_tsum_norm (g_prime_summable p hp s hσ_pos).norm).trans
    (((g_prime_summable p hp s hσ_pos).norm.tsum_mono hgeom_sum
      (fun n => g_prime_term_norm_le p hp.two_le s hσ_pos n)).trans ?_)
  -- ∑' n, r^(n+2) = r^2 / (1 - r) ≤ p^{-2σ} / (1 - 2^{-σ})
  have h_geom_sum : ∑' n : ℕ, ((p : ℝ) ^ (-s.re)) ^ (n + 2) =
      ((p : ℝ) ^ (-s.re)) ^ 2 / (1 - (p : ℝ) ^ (-s.re)) := by
    have := tsum_geometric_of_lt_one hpσ_nn hpσ_lt1
    -- ∑' n, r^n = 1/(1-r), so ∑' n, r^(n+2) = r^2 * ∑' n, r^n = r^2/(1-r)
    rw [show (fun n : ℕ => ((p : ℝ) ^ (-s.re)) ^ (n + 2)) =
        (fun n => ((p : ℝ) ^ (-s.re)) ^ 2 * ((p : ℝ) ^ (-s.re)) ^ n) from
      funext (fun n => by ring)]
    rw [tsum_mul_left, this]
    ring
  rw [h_geom_sum]
  -- r^2/(1-r) ≤ r^2/(1-2^{-σ}) when 1-r ≥ 1-2^{-σ}
  have h_sq : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1; ring
  rw [h_sq]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    h_denom_pos h_p_denom

/-! ## Section 3: exp(g(s)) ≠ 0 -/

/-- exp(g(s)) is nonzero for all s. -/
theorem exp_g_ne_zero (s : ℂ) : Complex.exp (g s) ≠ 0 :=
  Complex.exp_ne_zero _

/-! ## Section 4: The Splitting Identity -/

/-- -log(1 - p^{-s}) = p^{-s} + g_prime p s for Re(s) > 0. -/
theorem neg_log_one_sub_split (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (hσ : 0 < s.re) :
    -Complex.log (1 - (p : ℂ) ^ (-s)) = (p : ℂ) ^ (-s) + g_prime p s := by
  have hz : ‖(p : ℂ) ^ (-s)‖ < 1 := PrimeBranching.euler_factor_norm_lt_one hp hσ
  set z := (p : ℂ) ^ (-s) with hz_def
  have hs : HasSum (fun n : ℕ => z ^ n / (n : ℂ)) (-Complex.log (1 - z)) :=
    Complex.hasSum_taylorSeries_neg_log hz
  -- Head sum: ∑ i in range 2, z^i/(i:ℂ) = z^0/0 + z^1/1 = 0 + z = z
  have h_head : ∑ i ∈ Finset.range 2, z ^ i / (↑i : ℂ) = z := by
    simp [Finset.sum_range_succ]
  -- Shift HasSum by 2 to get the tail
  have hg : HasSum (fun n : ℕ => z ^ (n + 2) / (↑(n + 2) : ℂ))
      (-Complex.log (1 - z) - z) := by
    have h2 := (hasSum_nat_add_iff' 2).mpr hs
    rwa [h_head] at h2
  rw [g_prime, hg.tsum_eq]
  ring

/-! ## Section 5: The Splitting Theorem for ζ (Re(s) > 1) -/

/-- For Re(s) > 1: ζ(s) = exp(P(s)) · exp(g(s)).
    Sorry: needs summability of ∑_p p^{-s} for σ > 1. -/
theorem zeta_prime_split (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = Complex.exp (∑' p : Nat.Primes, (p : ℂ) ^ (-s)) *
                    Complex.exp (g s) := by
  rw [← Complex.exp_add, ← riemannZeta_eulerProduct_exp_log hs]
  congr 1
  have hσ : 0 < s.re := by linarith
  -- Summability of the prime zeta function for σ > 1:
  -- use energy_convergence with σ' = s.re/2 > 1/2, giving ∑_p p^{-2*(s.re/2)} = ∑_p p^{-s.re}
  have hpsum : Summable (fun p : Nat.Primes => (p : ℂ) ^ (-s)) := by
    apply Summable.of_norm_bounded
        (PrimeBranching.energy_convergence (show 1/2 < s.re/2 by linarith))
    intro ⟨p, hp⟩
    show ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-2 * (s.re / 2))
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp only [Complex.neg_re, show -2 * (s.re / 2) = -s.re from by ring, le_refl]
  -- Rewrite each Euler factor: -log(1-p^{-s}) = p^{-s} + g_prime p s
  rw [g, ← hpsum.tsum_add (g_summable_strip s (by linarith))]
  apply tsum_congr
  intro ⟨p, hp⟩
  exact neg_log_one_sub_split p hp s hσ

/-- For Re(s) > 1, ζ(s)/exp(g(s)) ≠ 0. -/
theorem prime_part_ne_zero_sigma_gt_one (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s / Complex.exp (g s) ≠ 0 := by
  rw [div_ne_zero_iff]
  exact ⟨riemannZeta_ne_zero_of_one_le_re (le_of_lt hs), exp_g_ne_zero s⟩

end PrimeZetaSplit

-- Axiom audit
#print axioms PrimeZetaSplit.exp_g_ne_zero
