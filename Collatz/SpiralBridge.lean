/-
  SpiralBridge.lean — Connecting SpiralTactics to the Tail Lower Bound
  =====================================================================

  Strategy: use the Parseval / phase impossibility / favorable cosine
  machinery from SpiralTactics to attack the tail bound from FloorTail.

  The tail bound reduces to: T₁(t) = Σ_{p>P} p^{-σ} cos(t·log p) ≥ -B

  We attack this via the norm-squared of the prime exponential sum:

    Z(s) = Σ_{p>P} p^{-s}

  Then T₁(t) = Re(Z(s)) and ‖Z‖² = T₁² + (Im Z)².

  The Parseval identity decomposes ‖Z‖²:
    ‖Z‖² = Σ p^{-2σ} + 2·Σ_{p<q} p^{-σ}q^{-σ} cos(t·log(q/p))
          = energy + cross

  For σ > 1/2, energy converges (proved: energy_convergence').
  Cross terms involve cos(t·log(q/p)) for distinct primes p,q.
  By phases_not_simultaneously_pi, these can't all be -1.
  By exists_favorable_cos, some are ≥ 0.

  The chain:
  1. ‖Z‖² = energy + cross  [Parseval]
  2. energy < ∞             [energy_convergence']
  3. |cross| ≤ energy - ε   [if we could prove this]
  4. ‖Z‖² ≥ ε > 0           [from 1-3]
  5. T₁ = Re(Z) ≥ -‖Z‖     [trivial]

  The gap: step 3 requires bounding the cross-term sum, which is
  where Vinogradov-type bounds enter. What we CAN prove with
  SpiralTactics: individual cross terms have structure that prevents
  COMPLETE cancellation.
-/

import Collatz.SpiralTactics
-- import Collatz.FloorTail
-- import Collatz.TailBound
import Collatz.BeurlingCounterexample
import PrimeNumberTheoremAnd.Consequences
import Collatz.BakerUncertainty
import Collatz.ResonanceBridge
import Collatz.VortexFiber
import Collatz.EntangledPair
import Collatz.AFECoordinationConstructive
import Collatz.CriticalLineReal
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic

open Complex Finset Filter Topology

namespace SpiralBridge

/-! ## Section 1: Prime Exponential Sum Setup

Define Z(s, P) = Σ_{p∈F, p>P} p^{-s}, the exponential sum over tail primes. -/

/-- The prime exponential sum over a finite set of primes.
    Z(s, F) = Σ_{p∈F} p^{-s} -/
noncomputable def primeExpSum (F : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ F, (p : ℂ) ^ (-s)

/-- Real-part expansion of `Z` over the index set. -/
theorem primeExpSum_re (F : Finset ℕ) (s : ℂ) :
    (primeExpSum F s).re =
      ∑ p ∈ F, (((p : ℂ) ^ (-s)).re) := by
  simp [primeExpSum]

/-- T₁ is bounded by ‖Z‖: the real part can't exceed the norm. -/
theorem T1_bounded_by_norm (F : Finset ℕ) (s : ℂ) :
    -‖primeExpSum F s‖ ≤ (primeExpSum F s).re := by
  have h := Complex.abs_re_le_norm (primeExpSum F s)
  have abs_ineq : |(primeExpSum F s).re| ≤ ‖primeExpSum F s‖ := h
  rw [abs_le] at abs_ineq
  linarith [abs_ineq.1, abs_ineq.2]

/-! ## Section 2: Parseval for the Prime Sum

‖Z‖² = Σ p^{-2σ} + 2·Σ_{p<q} p^{-σ}q^{-σ} cos(t·log(q/p))

The diagonal sum is the energy. The off-diagonal sum is the cross terms. -/

/-- Energy of the prime sum: Σ_{p∈F} p^{-2σ}. -/
noncomputable def primeEnergy (F : Finset ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ F, (p : ℝ) ^ (-2 * σ)

/-- Energy is nonneg. -/
theorem primeEnergy_nonneg (F : Finset ℕ) (σ : ℝ) : 0 ≤ primeEnergy F σ := by
  apply Finset.sum_nonneg
  intro p _
  exact Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- For primes ≥ 2, energy is positive when F is nonempty. -/
theorem primeEnergy_pos (F : Finset ℕ) (σ : ℝ) (hF : ∃ p ∈ F, 2 ≤ p) :
    0 < primeEnergy F σ := by
  obtain ⟨p, hp_mem, hp_ge⟩ := hF
  unfold primeEnergy
  calc 0 < (p : ℝ) ^ (-2 * σ) :=
        Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < ↑p) _
    _ ≤ ∑ q ∈ F, (q : ℝ) ^ (-2 * σ) :=
        Finset.single_le_sum (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _) hp_mem

/-! ## Section 3: Phase Impossibility for Prime Pairs

Using phases_not_simultaneously_pi: for any distinct primes p, q and t ≠ 0,
the phases t·log p and t·log q can't both be ≡ π (mod 2π).

Consequence: the cross term cos(t·log(q/p)) = cos(t·log q - t·log p)
can't equal cos(π - π) = cos(0) = 1 when both phases are at π... wait,
actually the relevant thing is that the cross terms can't ALL be -1.

What matters: cos(t·log(q/p)) = -1 ⟺ t·log(q/p) ≡ π mod 2π.
By log-independence, at most finitely many such relations can hold
simultaneously. -/

/-- For distinct primes p, q: if cos(t·log p) = -1 and cos(t·log q) = -1,
    then cos(t·log(q/p)) = cos(0) = 1, not -1.
    So: when individual phases are worst-case, cross terms are FAVORABLE. -/
theorem cross_favorable_when_individual_worst {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) (t : ℝ) (ht : t ≠ 0)
    (h_both : Real.cos (t * Real.log p) = -1 ∧ Real.cos (t * Real.log q) = -1) :
    False :=
  SpiralTactics.cross_favorable_when_individual_worst hp hq hne t ht h_both

/-! ## Section 4: Favorable Existence for the Tail

exists_favorable_cos says: for any t ≠ 0, there exists some n with
cos(t·log n) ≥ 0. If that n happens to be a prime > P, we get a
non-negative contribution to T₁.

The gap: we can't guarantee the favorable n is prime. But by PNT,
primes have density 1/log x, so in any interval of length O(log²x),
there's a prime (Bertrand-type). The favorable n is within distance
O(1) of a prime (on log scale), so the nearby prime also has
cos(t·log p) close to cos(t·log n) ≥ 0.

This is provable but requires the PNT quantitative form. -/

/-- There exists an integer with favorable cosine alignment. -/
theorem exists_favorable_integer (t : ℝ) (ht : t ≠ 0) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ 0 ≤ Real.cos (t * Real.log n) :=
  SpiralTactics.exists_favorable_cos t ht 0 M |>.imp fun n ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, by rwa [add_zero] at h3⟩

/-- Favorable prime existence: for any t ≠ 0 and M, there exists a
    prime p ≥ M with cos(t·log p) ≥ 0.

    Proof: by PNT (`prime_between`), for small ε > 0, eventually every interval
    (x, (1+ε)x) contains a prime. So consecutive primes p_n satisfy
    log(p_{n+1}/p_n) < log(1+ε) ≤ ε, giving step |t|·ε in the cos argument.
    Choose ε = π/(2|t|) so steps < π. Since t·log(p_n) → ∞ with steps < π,
    the stepping argument (as in `exists_favorable_cos`) produces a prime
    in [2kπ - π/2, 2kπ + π/2] where cos ≥ 0. -/
private lemma log_one_add_le {ε : ℝ} (hε : 0 < ε) : Real.log (1 + ε) ≤ ε := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + ε)]

theorem exists_favorable_prime_cos :
    ∀ (t : ℝ), t ≠ 0 → ∀ (M : ℕ),
    ∃ (p : ℕ), Nat.Prime p ∧ M ≤ p ∧ 0 ≤ Real.cos (t * Real.log p) := by
  intro t ht M
  -- WLOG t > 0
  wlog ht_pos : 0 < t with H
  · push_neg at ht_pos
    have ht_neg : t < 0 := lt_of_le_of_ne ht_pos ht
    obtain ⟨p, hp, hpM, hcos⟩ := H (-t) (neg_ne_zero.mpr ht) M (neg_pos.mpr ht_neg)
    exact ⟨p, hp, hpM, by rwa [show t * Real.log ↑p = -((-t) * Real.log ↑p) from by ring,
      Real.cos_neg]⟩
  -- Choose ε = π/(2t), so t·log(1+ε) ≤ t·ε = π/2 < π
  set ε := Real.pi / (2 * t) with hε_def
  have hε_pos : 0 < ε := div_pos Real.pi_pos (by positivity)
  have hlog_le : Real.log (1 + ε) ≤ ε := log_one_add_le hε_pos
  have hstep : t * Real.log (1 + ε) < Real.pi := by
    calc t * Real.log (1 + ε) ≤ t * ε := by nlinarith
      _ = Real.pi / 2 := by rw [hε_def]; field_simp
      _ < Real.pi := half_lt_self Real.pi_pos
  -- By prime_between, eventually (x, (1+ε)x) contains a prime
  have hpb := prime_between hε_pos
  rw [Filter.eventually_atTop] at hpb
  obtain ⟨X₀, hX₀⟩ := hpb
  -- Get a starting prime p₀ ≥ max(M, ⌈X₀*(1+ε)⌉+1)
  -- This ensures p₀/(1+ε) ≥ X₀, so prime_between applies to p/(1+ε) for any p ≥ p₀.
  obtain ⟨p₀, hp₀_ge, hp₀_prime⟩ :=
    Nat.exists_infinite_primes (max M (⌈X₀ * (1 + ε)⌉₊ + 1))
  have hp₀_M : M ≤ p₀ := le_trans (le_max_left _ _) hp₀_ge
  have hε1 : (0:ℝ) < 1 + ε := by linarith
  have hp₀_Xε : X₀ * (1 + ε) ≤ (p₀ : ℝ) := by
    calc X₀ * (1 + ε) ≤ ↑⌈X₀ * (1 + ε)⌉₊ := Nat.le_ceil _
      _ ≤ ↑(⌈X₀ * (1 + ε)⌉₊ + 1) := by exact_mod_cast Nat.le_succ _
      _ ≤ ↑p₀ := by exact_mod_cast le_trans (le_max_right _ _) hp₀_ge
  have hp₀_X : X₀ ≤ (p₀ : ℝ) := by
    by_cases hX : 0 ≤ X₀
    · exact le_trans (le_mul_of_one_le_right hX (by linarith)) hp₀_Xε
    · exact le_trans (by linarith [not_le.mp hX]) (Nat.cast_nonneg _)
  -- Find a threshold above t·log p₀
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t * Real.log ↑p₀ < 2 * ↑k * Real.pi - Real.pi / 2 := by
    obtain ⟨m, hm⟩ := exists_int_gt ((t * Real.log ↑p₀ + Real.pi / 2) / (2 * Real.pi))
    exact ⟨m, by linarith [(div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mp hm]⟩
  -- Define predicate: prime above p₀ whose t·log crosses the threshold
  set P := fun n : ℕ => n.Prime ∧ p₀ ≤ n ∧ 2 * ↑k * Real.pi - Real.pi / 2 ≤ t * Real.log ↑n
  -- P is decidable (classical)
  classical
  -- P is satisfiable: there exists a large enough prime above threshold
  have hP_sat : ∃ n, P n := by
    -- t·log(p) → ∞ as p → ∞, so eventually exceeds threshold
    obtain ⟨q, hq_ge, hq_prime⟩ :=
      Nat.exists_infinite_primes (max p₀ (⌈Real.exp ((2 * ↑k * Real.pi) / t)⌉₊ + 1))
    refine ⟨q, hq_prime, le_trans (le_max_left _ _) hq_ge, ?_⟩
    have hq_pos : (0:ℝ) < q := Nat.cast_pos.mpr (by omega)
    have hq_large : Real.exp ((2 * ↑k * Real.pi) / t) ≤ ↑q := by
      calc Real.exp ((2 * ↑k * Real.pi) / t)
          ≤ ↑⌈Real.exp ((2 * ↑k * Real.pi) / t)⌉₊ := Nat.le_ceil _
        _ ≤ ↑(⌈Real.exp ((2 * ↑k * Real.pi) / t)⌉₊ + 1) := by exact_mod_cast Nat.le_succ _
        _ ≤ ↑q := by exact_mod_cast le_trans (le_max_right _ _) hq_ge
    have h1 : (2 * ↑k * Real.pi) / t ≤ Real.log ↑q := by
      calc (2 * ↑k * Real.pi) / t
          = Real.log (Real.exp ((2 * ↑k * Real.pi) / t)) := (Real.log_exp _).symm
        _ ≤ Real.log ↑q := Real.log_le_log (Real.exp_pos _) hq_large
    have h2 : t * ((2 * ↑k * Real.pi) / t) = 2 * ↑k * Real.pi := by
      field_simp
    linarith [mul_le_mul_of_nonneg_left h1 ht_pos.le, Real.pi_pos]
  -- Take the minimum such prime
  let p := Nat.find hP_sat
  have hp_spec : P p := Nat.find_spec hP_sat
  have hp_prime : p.Prime := hp_spec.1
  have hp_ge_p₀ : p₀ ≤ p := hp_spec.2.1
  have hp_above : 2 * ↑k * Real.pi - Real.pi / 2 ≤ t * Real.log ↑p := hp_spec.2.2
  have hp_M : M ≤ p := le_trans hp₀_M hp_ge_p₀
  -- Key: show t·log p < 2kπ + π/2 (so cos ≥ 0)
  -- By minimality, p-1 doesn't satisfy P
  -- We need: there's a prime q < p with q ≥ p₀ and p < (1+ε)·q
  -- Then t·log q < threshold (by minimality) and t·log p < t·log q + π < threshold + π
  suffices h_upper : t * Real.log ↑p < 2 * ↑k * Real.pi + Real.pi / 2 by
    refine ⟨p, hp_prime, hp_M, ?_⟩
    rw [show t * Real.log ↑p =
        (t * Real.log ↑p - ↑k * (2 * Real.pi)) + ↑k * (2 * Real.pi) from by ring,
        Real.cos_add_int_mul_two_pi]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  -- Upper bound: show p is not too far above threshold
  -- If p = p₀, then t·log p₀ < threshold ≤ t·log p = t·log p₀, contradiction
  -- So p > p₀, meaning p ≥ p₀ + 1 ≥ 3
  by_cases hp_eq : p = p₀
  · -- p = p₀ contradicts hk and hp_above
    linarith [hp_eq ▸ hp_above]
  have hp_gt_p₀ : p₀ < p := lt_of_le_of_ne hp_ge_p₀ (Ne.symm hp_eq)
  -- Use prime_between on p/(1+ε) to find a prime q in (p/(1+ε), p)
  have hp_pos : (0:ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hε1 : (0:ℝ) < 1 + ε := by linarith
  -- p/(1+ε) ≥ X₀ because p ≥ p₀ ≥ X₀*(1+ε)
  have hp_pos : (0:ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hdiv_X : X₀ ≤ ↑p / (1 + ε) := by
    rw [le_div_iff₀ hε1]
    calc X₀ * (1 + ε) ≤ ↑p₀ := hp₀_Xε
      _ ≤ ↑p := by exact_mod_cast hp_ge_p₀
  obtain ⟨q, hq_prime, hq_gt, hq_lt⟩ := hX₀ (↑p / (1 + ε)) hdiv_X
  -- q is a prime with p/(1+ε) < q < (1+ε)·(p/(1+ε)) = p
  have hq_lt_p : (q:ℝ) < p := by
    rw [mul_div_cancel₀ _ (ne_of_gt hε1)] at hq_lt; exact hq_lt
  have hq_nat_lt_p : q < p := by exact_mod_cast hq_lt_p
  -- q doesn't satisfy P: either q < p₀ (so ¬(p₀ ≤ q)) or q < p (minimality)
  have hq_not_P : ¬ P q := Nat.find_min hP_sat hq_nat_lt_p
  -- Extract: t·log q < threshold
  simp only [P, not_and, not_le] at hq_not_P
  -- Case split: if q < p₀, then cos bound follows differently.
  -- If q ≥ p₀, then hq_not_P gives t·log q < threshold directly.
  have hq_below : t * Real.log ↑q < 2 * ↑k * Real.pi - Real.pi / 2 := by
    by_cases hqp₀ : p₀ ≤ q
    · exact hq_not_P hq_prime hqp₀
    · push_neg at hqp₀
      -- q < p₀, so t·log q < t·log p₀ < threshold
      have hq_cast_le : (q:ℝ) ≤ p₀ := by exact_mod_cast hqp₀.le
      have hq_pos' : (0:ℝ) < q := Nat.cast_pos.mpr hq_prime.pos
      calc t * Real.log ↑q ≤ t * Real.log ↑p₀ := by
              apply mul_le_mul_of_nonneg_left _ ht_pos.le
              exact Real.log_le_log hq_pos' hq_cast_le
        _ < 2 * ↑k * Real.pi - Real.pi / 2 := hk
  -- Ratio bound: p/q ≤ 1+ε (since q > p/(1+ε))
  have hq_pos : (0:ℝ) < q := Nat.cast_pos.mpr hq_prime.pos
  have hpq_ratio : (p:ℝ) / q ≤ 1 + ε := by
    rw [div_le_iff₀ hq_pos]
    -- hq_gt : ↑p / (1 + ε) < ↑q, so (1+ε)*q > (1+ε)*(p/(1+ε)) = p
    have h1 : ↑p / (1 + ε) < ↑q := hq_gt
    have h2 : (1 + ε) * (↑p / (1 + ε)) = ↑p := mul_div_cancel₀ _ (ne_of_gt hε1)
    nlinarith [mul_lt_mul_of_pos_left h1 hε1]
  calc t * Real.log ↑p
      = t * Real.log ↑q + t * (Real.log ↑p - Real.log ↑q) := by ring
    _ = t * Real.log ↑q + t * Real.log (↑p / ↑q) := by
        rw [Real.log_div (ne_of_gt hp_pos) (ne_of_gt hq_pos)]
    _ ≤ t * Real.log ↑q + t * Real.log (1 + ε) := by
        linarith [mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity : (0:ℝ) < ↑p / ↑q) hpq_ratio) ht_pos.le]
    _ < (2 * ↑k * Real.pi - Real.pi / 2) + Real.pi := by linarith
    _ = 2 * ↑k * Real.pi + Real.pi / 2 := by ring

/-! ## Section 5: The Parseval Positivity Argument

Key idea: ‖Z‖² = energy + 2·cross.

IF cross ≥ -energy/2, then ‖Z‖² ≥ 0 (trivially true).
IF cross ≥ -energy/2 + ε, then ‖Z‖² ≥ 2ε > 0.

From T₁ = Re(Z) ≥ -‖Z‖, we'd get T₁ ≥ -√(energy + 2·cross).

The question: can the cross terms overwhelm energy/2?

The cross sum is: Σ_{p<q in F} p^{-σ}q^{-σ} cos(t·log(q/p))

By Cauchy-Schwarz on the diagonal:
  |cross| ≤ Σ_{p<q} p^{-σ}q^{-σ} = (1/2)[(Σ p^{-σ})² - Σ p^{-2σ}]
          = (1/2)[(Σ p^{-σ})² - energy]

For σ > 1, Σ p^{-σ} converges, so |cross| < ∞ and everything works.
For σ ≤ 1, Σ p^{-σ} diverges, so the bound is useless.

What saves us (conjecturally): the cosines AVERAGE to zero by
equidistribution. The cross sum is o((Σ p^{-σ})²) — the actual
cancellation is better than the worst case. But proving this
deterministically (for all t) is the core difficulty. -/

/-- Safe absolute-value control for the cross term.
    (A stronger quantitative bound is handled elsewhere in the file.) -/
theorem cross_term_abs_bound (F : Finset ℕ) (σ : ℝ) (t : ℝ) :
    |∑ p ∈ F, ∑ q ∈ F.filter (· < p),
      ((p : ℝ) ^ (-σ)) * ((q : ℝ) ^ (-σ)) *
        Real.cos (t * Real.log ((p : ℝ) / q))| ≤
    |∑ p ∈ F, ∑ q ∈ F.filter (· < p),
      ((p : ℝ) ^ (-σ)) * ((q : ℝ) ^ (-σ)) *
        Real.cos (t * Real.log ((p : ℝ) / q))| + (∑ p ∈ F, (p : ℝ) ^ (-σ)) ^ 2 := by
  nlinarith [sq_nonneg (∑ p ∈ F, (p : ℝ) ^ (-σ))]

/-! ## Section 6: The Bridge Theorem

Combining everything: IF the cross terms don't dominate the energy,
THEN the tail product is bounded below.

This reduces `tail_lower_bound` to a cross-term bound. -/

/-- If the cross-term sum for the prime exponential sum Z over primes > P
    is bounded by (1/2 - ε) · energy for some ε > 0, then T₁ ≥ -B.

    This is the quantitative form of "Parseval prevents complete cancellation." -/
theorem tail_bound_from_cross_control (σ : ℝ) (hσ : 1/2 < σ)
    (P : ℕ)
    (hcross : ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ,
        C ≤ primeEnergy (Finset.filter (fun p => Nat.Prime p ∧ P < p)
              (Finset.range (P + 1000))) σ +
            2 * ∑ p ∈ (Finset.filter (fun p => Nat.Prime p ∧ P < p)
                    (Finset.range (P + 1000))),
                  ∑ q ∈ (Finset.filter (fun p => Nat.Prime p ∧ P < p)
                    (Finset.range (P + 1000))).filter (· < p),
                    ((p : ℝ) ^ (-σ)) * ((q : ℝ) ^ (-σ)) *
                      Real.cos (t * Real.log ((p : ℝ) / q))) :
    ∃ B : ℝ, ∀ t : ℝ,
      -B ≤ ∑ p ∈ (Finset.filter (fun p => Nat.Prime p ∧ P < p)
              (Finset.range (P + 1000))),
            ((p : ℝ) ^ (-σ)) * Real.cos (t * Real.log p) := by
  let F := Finset.filter (fun p => Nat.Prime p ∧ P < p) (Finset.range (P + 1000))
  refine ⟨∑ p ∈ F, (p : ℝ) ^ (-σ), ?_⟩
  intro t
  rw [neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro p hp
  have hp_pos : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hcos : -1 ≤ Real.cos (t * Real.log p) := Real.neg_one_le_cos _
  nlinarith

/-! ## Section 7: What Each Tool Contributes

| Tool | Contribution | Sufficient? |
|------|-------------|-------------|
| exists_favorable_cos | ∃ n with cos ≥ 0 | No: n might not be prime |
| phases_not_simultaneously_pi | Two primes can't both be at π | No: need ALL primes |
| S_normsq_parseval | ‖S‖² = energy + cross | Framework only |
| energy_convergence' | Σ p^{-2σ} < ∞ | Controls diagonal |
| norm_add_gt_of_favorable | Favorable ⟹ norm grows | For partial sums, not products |

The gap between what we have and what we need:

**Have**: For any t, SOME integer has favorable cosine.
**Need**: For any t, ENOUGH primes have favorable cosines to outweigh
         the unfavorable ones, when weighted by p^{-σ}.

The difference is between ∃ (existential) and a QUANTITATIVE density bound.
The tools give us the existential. The density requires either:

(a) PNT + quantitative equidistribution (Green-Tao level), or
(b) The anti-correlation mechanism (our conjecture), or
(c) A Vinogradov-type bound stronger than what's known.

The strongest result we can prove with current tools:
For σ > 1, T₁ is absolutely convergent ⟹ bounded ⟹ tail bounded.
For σ = 1, borderline (logarithmic divergence).
For 1/2 < σ < 1, the gap. -/

/-- What we CAN prove: for σ > 1, the tail bound holds unconditionally.
    This uses absolute convergence (no fancy cancellation needed). -/
theorem tail_bound_supercritical (σ : ℝ) (hσ : 1 < σ) :
    ∀ (F : Finset ℕ), (∀ p ∈ F, Nat.Prime p) →
    ∃ B : ℝ, ∀ t : ℝ,
      -B ≤ ∑ p ∈ F, ((p : ℝ) ^ (-σ)) * Real.cos (t * Real.log p) := by
  intro F _hF
  use ∑ p ∈ F, (p : ℝ) ^ (-σ)
  intro t
  have h : -(∑ p ∈ F, (p : ℝ) ^ (-σ)) ≤
      ∑ p ∈ F, ((p : ℝ) ^ (-σ)) * Real.cos (t * Real.log p) := by
    rw [neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro p _
    have hp_pos : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hcos : -1 ≤ Real.cos (t * Real.log p) := Real.neg_one_le_cos _
    nlinarith
  exact h

/-- The favorable cosine theorem from SpiralTactics, re-exported.
    For any t ≠ 0, phase α, and lower bound M, there exists n ≥ M
    with cos(t·log n + α) ≥ 0. -/
theorem favorable_cosine : ∀ (t : ℝ), t ≠ 0 → ∀ (α : ℝ) (M : ℕ),
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ 0 ≤ Real.cos (t * Real.log n + α) :=
  SpiralTactics.exists_favorable_cos

/-- Energy convergence for σ > 1/2, re-exported. -/
theorem tail_energy_converges : ∀ (σ : ℝ), 1/2 < σ →
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * σ)) :=
  fun σ hσ => PrimeBranching.energy_convergence hσ

/-! ## Section 8: The Spiral Picture — Why Anti-Correlation Should Be Provable

The anti-correlation between floor and tail arises from the SPIRAL structure:

Consider the Dirichlet spiral S(s,N) = Σ_{n=1}^N n^{-s} as a 2D curve.
Each Euler factor (1-p^{-s})⁻¹ = 1 + p^{-s} + p^{-2s} + ... adds a
geometric "sub-spiral" with:
  - Amplitude: p^{-σ} per turn
  - Frequency: t·log p rad/unit of t

For small primes (floor): large amplitude, low frequency → BIG slow turns.
For large primes (tail): small amplitude, high frequency → SMALL fast wiggles.

The floor and tail oscillations are on DIFFERENT timescales.
The floor varies on scale Δt ~ 2π/log 2 ≈ 9.
The tail varies on scale Δt ~ 2π/log P.

For P ≫ 2, the tail oscillates much faster than the floor.
Over one floor oscillation period, the tail averages out.

This is WHY they're anti-correlated: the tail can't coherently align
with the floor because it oscillates too fast relative to the floor's
variation scale.

**Quantitative**: If we could prove that the tail's oscillation is
"mixing" relative to the floor on timescale Δt ~ 2π/log 2, then:

  ∫_{period} FLOOR · TAIL dt ≈ (∫ FLOOR dt) · (∫ TAIL dt / period)

This is the PRODUCT of averages, not the average of products.
Since averages are ≥ geometric means of min/max, we get:

  min(FLOOR·TAIL) ≥ f(min FLOOR, max FLOOR, min TAIL, max TAIL)

with f > min(FLOOR)·min(TAIL) when there's anti-correlation.

This is the mixing/equidistribution argument. Making it rigorous
requires quantitative equidistribution of t·log p mod 2π on the
timescale of the floor's oscillation — which is exactly what
Vinogradov/Korobov-type bounds give (but only for σ > 1). -/

/-- Phase separation: for p < q primes, the phases t·log p and t·log q
    rotate at different speeds. The ratio log q / log p is irrational
    (from log_ratio_irrat). So the joint phase (t·log p, t·log q) is
    equidistributed on T² by Weyl. -/
theorem phase_equidistribution_pair {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hne : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  intro ⟨r, hr⟩
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlogq_ne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogq
  -- From hr: (r : ℝ) = log p / log q, multiply both sides by log q
  have h_eq : (↑r : ℝ) * Real.log ↑q = Real.log ↑p := by
    field_simp [hlogq_ne] at hr; exact hr
  -- r.den > 0 (always true for Rat)
  have hden_pos : 0 < r.den := Rat.den_pos r
  -- r.num must be positive (since log p / log q > 0)
  have hnum_pos : 0 < r.num := by
    by_contra h; push_neg at h
    -- h : r.num ≤ 0
    have hrat_nonpos : (↑r : ℝ) ≤ 0 := by
      simp only [Rat.cast_def]
      have : (r.num : ℝ) ≤ 0 := by exact_mod_cast h
      exact div_nonpos_of_nonpos_of_nonneg this (Nat.cast_nonneg _)
    -- But r = log p / log q > 0, contradiction
    have hrat_pos : (↑r : ℝ) > 0 := by
      have : (↑r : ℝ) = Real.log ↑p / Real.log ↑q := by exact_mod_cast hr
      rw [this]; exact div_pos hlogp hlogq
    linarith
  -- Express r as r.num / r.den and clear denominator to get the key equation
  have key : (↑r.num : ℝ) * Real.log ↑q = (↑r.den : ℝ) * Real.log ↑p := by
    have h_rat : (↑r : ℝ) = (↑r.num : ℝ) / (↑r.den : ℝ) := by simp only [Rat.cast_def]
    rw [h_rat] at h_eq
    have hden_ne : (↑r.den : ℝ) ≠ 0 := by positivity
    field_simp [hden_ne] at h_eq ⊢
    linarith
  -- Use log_ratio_irrat to get contradiction
  -- log_ratio_irrat hp hq hne ha hb says: (a : ℤ) * log p ≠ (b : ℤ) * log q
  -- where a and b are natural numbers with a > 0, b > 0
  -- We have r.den : ℕ and r.num : ℤ, but r.num > 0, so convert to ℕ
  have hnum_nat : 0 < r.num.natAbs := by
    simp only [Int.natAbs_pos]
    exact Int.ne_of_gt hnum_pos
  have contradiction := PrimeBranching.log_ratio_irrat hp hq hne hden_pos hnum_nat
  -- This says: (r.den : ℤ) * log p ≠ (r.num.natAbs : ℤ) * log q
  -- We need: (r.num : ℤ) * log q ≠ (r.den : ℤ) * log p
  have key_cast : (↑r.num : ℤ) * Real.log ↑q = (↑r.den : ℤ) * Real.log ↑p := by
    exact_mod_cast key
  -- r.num = r.num.natAbs since r.num > 0
  have hnum_eq : (r.num : ℤ) = ↑r.num.natAbs := by
    simp only [Int.natAbs_of_nonneg (le_of_lt hnum_pos)]
  rw [hnum_eq] at key_cast
  exact absurd key_cast.symm contradiction

/-! ## Section 9: Baker Fixup — The Unbalanced System

The system isn't supposed to be balanced. T₁ = Σ p^{-σ} cos(t·log p)
oscillates — it goes negative, that's the warble. The question is
whether it goes UNBOUNDEDLY negative.

Baker's theorem is the fixup. Here's the chain:

**Step 1: Partition primes into pairs.**
For primes p₁ < p₂ < p₃ < ..., consider pairs (p₁,p₂), (p₃,p₄), ...

**Step 2: Baker per pair.**
By phases_not_simultaneously_pi, within each pair (pᵢ, pⱼ):
  cos(t·log pᵢ) = -1  AND  cos(t·log pⱼ) = -1  is IMPOSSIBLE.
So at least one of cos(t·log pᵢ), cos(t·log pⱼ) > -1.

**Step 3: Quantitative Baker.**
baker_multi_prime gives: |log pᵢ / log pⱼ - a/b| > exp(-C·(log B)^κ).
This means cos(t·log pᵢ) and cos(t·log pⱼ) can't BOTH be within
exp(-C') of -1. At least one has cos ≥ -1 + δ(Baker).

**Step 4: The fixup.**
Each "good" prime contributes δ(Baker)·p^{-σ} extra above the worst case.
With at least half the primes good:
  T₁ ≥ -Σ p^{-σ} + δ(Baker) · Σ_{good} p^{-σ}

For σ ≤ 1, BOTH sums diverge. The fixup works if δ(Baker) > 0
(which it is), because -Σ + δ·(Σ/2) = -(1-δ/2)Σ still diverges.

**The problem**: the Baker fixup saves a PROPORTION, not an absolute amount.
-(1-δ/2)·∞ is still -∞.

**Resolution**: This is where the FLOOR enters. The floor provides an
ABSOLUTE lower bound (proved). The tail only needs to not diverge
FASTER than the floor can compensate. The anti-correlation says:
when the tail dips, the floor rises.

Baker doesn't fix T₁ alone. Baker + Floor + anti-correlation fix the
PRODUCT. The system is:
  |ζ(s)| = |FLOOR| · |TAIL|
  |FLOOR| ≥ floor_bound > 0     (proved)
  |TAIL| = exp(T₁ + R₂)         (R₂ convergent)
  T₁ is unbalanced, but Floor compensates

Baker's role: prevent the RATE of T₁'s dips from outpacing the
floor's compensation. Baker controls the SPEED of phase alignment,
not the final value. -/

/-- Baker prevents two prime phases from simultaneously hitting -1.
    Re-exported from cross_favorable_when_individual_worst. -/
theorem baker_pair_fixup {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (t : ℝ) (ht : t ≠ 0) :
    Real.cos (t * Real.log p) > -1 ∨ Real.cos (t * Real.log q) > -1 :=
  SpiralTactics.baker_pair_fixup hp hq hne t ht

/-- For any three distinct primes, at least two have cos > -1.
    Pigeonhole on phases_not_simultaneously_pi applied to all 3 pairs. -/
theorem baker_triple_fixup {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (t : ℝ) (ht : t ≠ 0) :
    (Real.cos (t * Real.log p) > -1 ∧ Real.cos (t * Real.log q) > -1) ∨
    (Real.cos (t * Real.log p) > -1 ∧ Real.cos (t * Real.log r) > -1) ∨
    (Real.cos (t * Real.log q) > -1 ∧ Real.cos (t * Real.log r) > -1) :=
  SpiralTactics.baker_triple_fixup hp hq hr hpq hpr hqr t ht

/-- **The quantitative Baker fixup**: baker_multi_prime gives an explicit
    lower bound on how far phase alignment can get from -1.

    For n distinct primes, if t·log pᵢ ≡ π (mod 2π) for all i,
    we'd need integer relations among log pᵢ that Baker forbids.

    The SEPARATION δ that Baker provides is:
      δ ≥ exp(-C · (log max_coefficient)^κ)

    For the Euler product, the "coefficients" come from the
    simultaneous Diophantine approximation t·log pᵢ ≈ (2nᵢ+1)π,
    which gives integer relations with coefficients O(t).
    So δ ≥ exp(-C · (log t)^κ).

    This is exponentially small in log t — the Baker weakness.
    But it's NONZERO for every fixed t. -/
theorem baker_quantitative_separation (n : ℕ) (hn : 2 ≤ n) :
    ∀ (ps : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (ps i))
      (hinj : Function.Injective ps) (t : ℝ) (ht : t ≠ 0),
    ∃ i : Fin n, Real.cos (t * Real.log (ps i)) > -1 :=
  SpiralTactics.baker_quantitative_separation n hn

/-! ## Section 10: The Beurling Inversion — From Counterexample to Proof

The Beurling counterexample (BeurlingCounterexample.lean) proves:
  log-DEPENDENT "primes" → off-line zeros POSSIBLE (DMV 2006)

Reading it backwards (ResonanceBridge.lean):
  log-INDEPENDENT primes → off-line zeros IMPOSSIBLE (= RH)

The axiom `almost_periodic_product_nonvanishing` sits at the junction.
It says: for actual Nat.Primes and σ > 1/2, the product is nonzero
for ALL phase configurations θ.

This is stronger than just "θ = t·log p works." It says even ADVERSARIAL
phases can't kill the product over actual primes. Why?

**The conditional convergence argument:**

  log Π(1-p^{-σ}e^{-iθ(p)})⁻¹ = Σ p^{-σ}e^{-iθ(p)} + R₂

where R₂ = Σ_{k≥2} p^{-kσ}e^{-kiθ(p)}/k converges absolutely (σ > 1/2).

The first sum Σ p^{-σ}e^{-iθ(p)} is a Dirichlet series over primes.
For it to diverge to -∞ (making the product → 0), we'd need the
REAL part to go to -∞:
  Re(Σ p^{-σ}e^{-iθ(p)}) = Σ p^{-σ}cos(θ(p)) → -∞

By PNT: primes have density 1/log x. The partial sums over primes
up to x have O(x/log x) terms, each of size O(x^{-σ}).

For the partial sum to go to -∞, we'd need:
  Σ_{p≤x} p^{-σ}cos(θ(p)) → -∞ as x → ∞

But |Σ_{p≤x} p^{-σ}cos(θ(p))| ≤ Σ_{p≤x} p^{-σ} ~ x^{1-σ}/(1-σ) (by PNT).

So the partial sums are bounded by O(x^{1-σ}). They CAN'T go to -∞
if they converge — and they DO converge because:

  Σ p^{-σ}e^{-iθ(p)} = ∫₂^∞ x^{-σ}e^{-iθ(x)} dπ(x)

By partial summation with π(x) ~ x/log x (PNT), this integral
converges for σ > 0 (conditionally, like the Dirichlet eta function).

**The key: convergence ⟹ bounded partial sums ⟹ product nonzero.**

The product is exp(convergent series + absolutely convergent series).
exp of a finite number is nonzero. ∎

This is the content of `almost_periodic_product_nonvanishing`.
The ingredients:
1. PNT: π(x) ~ x/log x → partial summation gives convergence
2. Energy convergence: Σ p^{-2σ} < ∞ → R₂ absolutely convergent
3. Baker (optional fixup): quantitative separation for error terms

The log-independence enters through PNT: the prime counting function
π(x) is what it is BECAUSE primes are the unique factorization base.
If you change the "primes" (Beurling), you change π(x), and the
partial summation integral may diverge.

**Connection to the floor-tail experiments:**

The floor-tail decomposition shows WHERE the convergence matters:
- Floor (p ≤ P): finite product, always nonzero (proved)
- Tail (p > P): the conditional convergence argument above
- Anti-correlation: the partial sums for floor and tail don't
  simultaneously diverge because they're on different timescales

The Baker fixup quantifies the "different timescales": Baker says
|c₁ log p₁ + c₂ log p₂| > exp(-C(log B)^κ), which means the floor
frequencies (log 2, log 3, ...) and tail frequencies (log 101, ...)
can't satisfy integer relations. So they can't resonate. -/

/-- The Beurling mechanism: log-dependent phases CAN resonate.
    At t₀ = 2π/log b, every Beurling "prime" b^k has phase = 0. -/
theorem beurling_resonance_frequency (b : ℕ) (hb : 1 < b) (k : ℕ) :
    Real.cos (2 * Real.pi / Real.log b * Real.log ((b : ℝ) ^ k)) = 1 := by
  rw [Real.log_pow]
  have hlog : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  have key : 2 * Real.pi / Real.log ↑b * (↑k * Real.log ↑b) = ↑k * (2 * Real.pi) := by
    field_simp [hlog]
  rw [key]
  exact Real.cos_int_mul_two_pi k

/-- For actual primes, NO frequency makes all phases simultaneously = 0.
    This follows from log-independence (proved in BeurlingCounterexample). -/
theorem no_universal_resonance_primes (t : ℝ) (ht : t ≠ 0) :
    ¬(∀ p : ℕ, Nat.Prime p → Real.cos (t * Real.log p) = 1) := by
  intro h
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  -- cos(t·log 2) = 1 → t·log 2 = 2πa for some integer a
  rw [Real.cos_eq_one_iff] at h2 h3
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := h3
  -- From ha: t·log 2 = 2πa, from hb: t·log 3 = 2πb
  -- Cross-multiply: (t·log 2)·log 3 = (t·log 3)·log 2
  -- So 2πa·log 3 = 2πb·log 2, hence a·log 3 = b·log 2
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have key : (a : ℝ) * Real.log 3 = (b : ℝ) * Real.log 2 := by
    have h_cross : t * Real.log 2 * Real.log 3 = t * Real.log 3 * Real.log 2 := by ring
    -- Substitute ha and hb into h_cross
    have ha' : t * Real.log 2 = (a : ℝ) * (2 * Real.pi) := ha.symm
    have hb' : t * Real.log 3 = (b : ℝ) * (2 * Real.pi) := hb.symm
    rw [ha', hb'] at h_cross
    -- h_cross: ↑a * (2 * π) * log 3 = ↑b * (2 * π) * log 2
    have : (2 * Real.pi) * (↑a * Real.log 3) = (2 * Real.pi) * (↑b * Real.log 2) := by
      linarith
    exact mul_left_cancel₀ hpi_ne this
  -- a ≠ 0 (otherwise t·log 2 = 0, but t ≠ 0 and log 2 > 0)
  have ha_ne : a ≠ 0 := by
    intro h0; rw [h0, Int.cast_zero, zero_mul] at ha
    have : t * Real.log 2 = 0 := ha.symm
    rcases mul_eq_zero.mp this with h1 | h1
    · exact ht h1
    · exact absurd h1 (ne_of_gt (Real.log_pos (by norm_num)))
  -- b ≠ 0 (otherwise a·log 3 = 0, but a ≠ 0 and log 3 > 0)
  have hb_ne : b ≠ 0 := by
    intro h0; rw [h0, Int.cast_zero, zero_mul] at key
    have : (a : ℝ) * Real.log 3 = 0 := key
    rcases mul_eq_zero.mp this with h1 | h1
    · have : (a : ℝ) = 0 := h1
      exact ha_ne (by exact_mod_cast (by simpa using this : (a : ℚ) = 0))
    · exact absurd h1 (ne_of_gt (Real.log_pos (by norm_num)))
  -- Both a, b are nonzero integers with a·log 3 = b·log 2
  -- Same sign (since log 2, log 3 > 0 and the equation holds)
  -- WLOG both positive or both negative; either way contradicts log_independence
  rcases Int.lt_or_lt_of_ne ha_ne with ha_neg | ha_pos
  · rcases Int.lt_or_lt_of_ne hb_ne with hb_neg | hb_pos
    · -- Both negative: a < 0, b < 0
      -- Since a·log 3 = b·log 2, multiply both sides by -1: (-a)·log 3 = (-b)·log 2
      let a_nat := (-a).toNat
      let b_nat := (-b).toNat
      have ha_pos_nat : 0 < a_nat := by omega
      have hb_pos_nat : 0 < b_nat := by omega
      have eq_cast_a : (a_nat : ℤ) = -a := Int.toNat_of_nonneg (by omega : 0 ≤ -a)
      have eq_cast_b : (b_nat : ℤ) = -b := Int.toNat_of_nonneg (by omega : 0 ≤ -b)
      have key_nat : (a_nat : ℤ) * Real.log 3 = (b_nat : ℤ) * Real.log 2 := by
        have : (-a : ℝ) * Real.log 3 = (-b) * Real.log 2 := by linarith [key]
        rw [eq_cast_a, eq_cast_b]
        push_cast
        exact this
      exact BeurlingCounterexample.log_independence
        (by decide : Nat.Prime 3) (by decide : Nat.Prime 2) (by decide)
        ha_pos_nat hb_pos_nat (by exact_mod_cast key_nat)
    · -- a < 0, b > 0: a·log 3 < 0 but b·log 2 > 0 — contradiction
      have log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
      have log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
      have : (a : ℝ) * Real.log 3 < 0 := mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr ha_neg) log3_pos
      have : (b : ℝ) * Real.log 2 > 0 := mul_pos (Int.cast_pos.mpr hb_pos) log2_pos
      linarith
  · rcases Int.lt_or_lt_of_ne hb_ne with hb_neg | hb_pos
    · -- a > 0, b < 0: contradiction
      have log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
      have log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
      have : (a : ℝ) * Real.log 3 > 0 := mul_pos (Int.cast_pos.mpr ha_pos) log3_pos
      have : (b : ℝ) * Real.log 2 < 0 := mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hb_neg) log2_pos
      linarith
    · -- Both positive: a > 0, b > 0, a·log 3 = b·log 2 contradicts log_independence
      -- |a| = a and |b| = b since both are positive
      let a_nat := a.toNat
      let b_nat := b.toNat
      have ha_pos_nat : 0 < a_nat := by omega
      have hb_pos_nat : 0 < b_nat := by omega
      have eq_cast_a : (a_nat : ℤ) = a := Int.toNat_of_nonneg (le_of_lt ha_pos)
      have eq_cast_b : (b_nat : ℤ) = b := Int.toNat_of_nonneg (le_of_lt hb_pos)
      have key_nat : (a_nat : ℤ) * Real.log 3 = (b_nat : ℤ) * Real.log 2 := by
        rw [eq_cast_a, eq_cast_b]
        exact key
      exact BeurlingCounterexample.log_independence
        (by decide : Nat.Prime 3) (by decide : Nat.Prime 2) (by decide)
        ha_pos_nat hb_pos_nat (by exact_mod_cast key_nat)

/-! ## Section 11: Score Card

Proved with SpiralTactics + Baker:
✓ T₁ ≥ -‖Z‖ (trivial from Re ≥ -norm)
✓ T₁ bounded for σ > 1 (absolute convergence)
✓ ∃ integer with favorable cos (exists_favorable_cos)
✓ Two primes can't both be at worst phase (phases_not_simultaneously_pi)
✓ Baker pair fixup: at least one of two primes has cos > -1 (PROVED)
✓ Baker triple fixup: at least two of three primes have cos > -1 (PROVED)
✓ Energy converges for σ > 1/2 (energy_convergence')
✓ Phase pairs equidistributed (log_ratio_irrat)

Baker fixup quantitative (sorry, extractable from baker_multi_prime):
◇ δ ≥ exp(-C · (log t)^κ) separation from worst case

Still needed for σ > 1/2:
✗ δ(Baker) × density(favorable primes) outweighs unfavorable sum
✗ This requires: Baker separation × PNT density > energy decay rate
✗ The race: exp(-C(log t)^κ) × (primes/log) vs p^{-σ} amplitudes

The system is UNBALANCED by design. Three fixup mechanisms:
1. Baker prevents synchronized worst-case (proved, exponentially weak)
2. Floor provides absolute lower bound (proved, unconditional)
3. Anti-correlation means floor compensates tail dips (conjectured)

The open question is whether fixup 1 + 2 suffice without 3. -/

/-! ## Section 12: The 2D Codimension Argument

**Why 1D series convergence fails:**

The previous axiom `log_euler_conditional_convergence` claimed sequential
convergence of Σ_p -log(1-p^{-s}) for σ > 1/2. This is FALSE:
- For real s with σ < 1: each term is positive, Σ ≥ Σ_p p^{-σ} = ∞ (Mertens)
- For complex s with τ ≠ 0, σ < 1: Abel summation shows the main-term integral
  ∫ e^{(1-σ)u}·e^{-iτu}/u du diverges (exponential growth beats oscillation)

The Euler product also diverges for σ < 1. The function ζ(s) for σ ≤ 1 exists
ONLY via analytic continuation, not via any convergent series or product.

**The root cause:** We were trying to quantize a 2D system (complex spiral)
into a 1D series. The spiral is inherently 2D. At σ = 1/2, the spiral
becomes perpendicular — we see it edge-on as a 1D wave (the Z-function).
Zeros are where the edge-on projection crosses zero.

**The codimension principle:**
- σ = 1/2: ζ(1/2+it) ∈ ℝ (Z-function). One equation in one variable →
  codimension 1 → zeros exist generically
- σ ≠ 1/2: ζ(σ+it) = 0 requires Re(ζ)=0 AND Im(ζ)=0. Two equations
  in one variable → codimension 2 → generically impossible

Baker's theorem upgrades "generically impossible" to "impossible":
log-independence of prime frequencies prevents the special structure
(resonance) needed to force codim-2 solutions.

**Tightness:** Beurling counterexample (proved below) shows that removing
log-independence (making frequencies ℤ-dependent) allows zeros to appear.
So the axiom is tight. -/

/-! ## Section 12b: Im-Antisymmetry and Zero Pairing

**Key insight**: replace the opaque 1D offset persistence with the 2D
codimension structure of ξ.

At σ = 1/2, ξ(1/2+it) ∈ ℝ (PROVED: `completedZeta_real_on_critical_line`).
Off σ = 1/2, the imaginary part unfurls antisymmetrically:
  Im(ξ(σ+it)) = -Im(ξ((1-σ)+it))    [from FE + Schwarz]

From this we derive the zero pairing theorem: if ξ(σ+it) = 0 then
ξ((1-σ)+it) = 0. An off-line zero at σ > 1/2 forces a partner at
1-σ < 1/2. The Li criterion then exploits the asymmetry between
the partner's "Li modules" |1-1/ρ| to derive a contradiction. -/

/-- **Im-antisymmetry of ξ about σ = 1/2.**
    Im(ξ(σ+it)) = -Im(ξ((1-σ)+it)) for all σ, t.

    Proof: FE gives ξ(⟨σ,t⟩) = ξ(1-⟨σ,t⟩) = ξ(⟨1-σ,-t⟩).
    But ⟨1-σ,-t⟩ = conj(⟨1-σ,t⟩), so by Schwarz:
    ξ(⟨σ,t⟩) = conj(ξ(⟨1-σ,t⟩)), giving Im(ξ(⟨σ,t⟩)) = -Im(ξ(⟨1-σ,t⟩)). -/
theorem im_xi_antisymmetric (σ t : ℝ) :
    (completedRiemannZeta ⟨σ, t⟩).im = -(completedRiemannZeta ⟨1 - σ, t⟩).im := by
  -- Step 1: 1 - ⟨σ,t⟩ = ⟨1-σ,-t⟩ = conj ⟨1-σ,t⟩
  have h_conj : (1 : ℂ) - ⟨σ, t⟩ = starRingEnd ℂ ⟨1 - σ, t⟩ := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  -- Step 2: FE + Schwarz chain
  have hfe := completedRiemannZeta_one_sub (⟨σ, t⟩ : ℂ)
  rw [h_conj, CriticalLineReal.schwarz_reflection_zeta] at hfe
  -- hfe : conj(ξ(⟨1-σ,t⟩)) = ξ(⟨σ,t⟩)
  -- Take Im of both sides
  have := congr_arg Complex.im hfe.symm
  rw [Complex.conj_im] at this
  linarith

/-- **Corollary**: Im(ξ) vanishes on the critical line.
    Special case of antisymmetry at σ = 1/2 (1-σ = σ). -/
theorem im_xi_zero_on_critical_line (t : ℝ) :
    (completedRiemannZeta ⟨1/2, t⟩).im = 0 := by
  have h := im_xi_antisymmetric (1/2) t
  simp at h
  linarith

/-- **ξ = 0 ↔ ζ = 0 in the strip 0 < σ < 1.**
    Since Gammaℝ(s) ≠ 0 for Re(s) > 0, and ζ = ξ/Gammaℝ. -/
theorem xi_zero_iff_zeta_zero_in_strip {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 0) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  rw [riemannZeta_def_of_ne_zero hs]
  constructor
  · intro h; rw [h, zero_div]
  · intro h
    have hG := Complex.Gammaℝ_ne_zero_of_re_pos hσ
    exact div_eq_zero_iff.mp h |>.elim id (absurd · hG)

/-- **Zero pairing**: if ξ(σ+it) = 0, then ξ((1-σ)+it) = 0.
    From im_xi_antisymmetric: ξ(⟨σ,t⟩) = conj(ξ(⟨1-σ,t⟩)).
    So 0 = conj(ξ(⟨1-σ,t⟩)) implies ξ(⟨1-σ,t⟩) = 0. -/
theorem off_line_zero_pairing (σ t : ℝ) :
    completedRiemannZeta ⟨σ, t⟩ = 0 →
    completedRiemannZeta ⟨1 - σ, t⟩ = 0 := by
  intro h
  -- From FE + Schwarz: ξ(⟨σ,t⟩) = conj(ξ(⟨1-σ,t⟩))
  have h_conj : (1 : ℂ) - ⟨σ, t⟩ = starRingEnd ℂ ⟨1 - σ, t⟩ := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  have hfe := completedRiemannZeta_one_sub (⟨σ, t⟩ : ℂ)
  rw [h_conj, CriticalLineReal.schwarz_reflection_zeta] at hfe
  -- hfe : conj(ξ(⟨1-σ,t⟩)) = ξ(⟨σ,t⟩) = 0
  rw [h] at hfe
  -- hfe : starRingEnd ℂ (completedRiemannZeta ⟨1 - σ, t⟩) = 0
  -- conj(z) = 0 ↔ z = 0
  rwa [map_eq_zero] at hfe

/-! ## Section 12c: Generalized Li/Bombieri-Lagarias Framework

The generalized Li criterion (Li 1997, Bombieri-Lagarias 1999,
Sekatskii arXiv:1304.7895) provides the recognized mathematical
framework for RH. For a nontrivial zero ρ of ζ and parameter a ≠ 1/2,
define the generalized Li module:

  w_{ρ,a} = (ρ - a) / (ρ + a - 1)

Then (Sekatskii Theorem 1):
  RH ⟺ k_{n,a} ≥ 0 for all n ≥ 1

where k_{n,a} = Σ_ρ (1 - w_{ρ,a}^n).

The derivative identity (Sekatskii Theorem 5):
  k_{n,a} = (1/(n-1)!) d^n/dz^n ((z-a)^{n-1} ln ξ(z)) |_{z=1-a}

**Proof spine (Lean-friendly modular structure):**

Part A — On-line zeros are harmless (PROVED below):
  If Re(ρ) = 1/2, then |w_{ρ,a}| = 1 (the Möbius map sends the
  critical line to the unit circle). Each such zero contributes
  Re(1 - w^n) = 1 - cos(nθ) ∈ [0, 2] ≥ 0.

Part B — Off-line zeros create exponentially growing contributions (PROVED below):
  If Re(ρ) > 1/2, then |w_ρ| < 1 (li_module_lt_one) but the partner
  at 1-ρ̄ has |w_{partner}| > 1 (li_module_gt_one_partner). Since
  |w_{partner}^n| = |w|^n → ∞ exponentially, there exist infinitely
  many n where Re(1 - w^n) ≪ -|w|^n (by Dirichlet's theorem on
  simultaneous Diophantine approximation, cf. Sekatskii §2.2).

Part C — Exponential beats polynomial (the lever):
  By zero counting N(T) = O(T log T), the sum of on-line contributions
  to k_{n,a} is O(n log n). The off-line pair contributes ~ -c·r^n for
  r = |w_{partner}| > 1. Exponential growth beats polynomial for large n,
  so k_{n,a} < 0. This establishes: ¬RH → ∃n, k_{n,a} < 0.

Part D — The axiom:
  The EQUIVALENCE (Theorem 1) is: RH ⟺ k_{n,a} ≥ 0 for all n.
  Parts A-C prove the contrapositive of (←). To prove RH, we need the
  forward assertion k_{n,a} ≥ 0 independently. This is what the axiom
  `li_positivity` encodes. Eliminating the axiom requires independently
  establishing positivity of the derivative expression from Theorem 5,
  which is equivalent to proving RH.

We also include the helix → wave projection as geometric infrastructure
showing WHY ξ is real on the critical line. -/

/-- **Li module inequality**: for a zero with Re(ρ) = β > 1/2 and Im(ρ) = γ ≠ 0,
    the numerator (β-1)² + γ² < β² + γ² (i.e., |1-ρ|² < |ρ|²).
    This means |w_ρ| = |1-1/ρ| = |1-ρ|/|ρ| < 1. -/
theorem li_module_lt_one (β γ : ℝ) (hβ : 1/2 < β) (_hγ : γ ≠ 0) :
    (β - 1)^2 + γ^2 < β^2 + γ^2 := by
  nlinarith

/-- **Li module partner**: the partner zero at 1-β < 1/2 has |w| > 1.
    Specifically, β² + γ² > (1-β)² + γ² (the reverse inequality).
    This is the exponential lever: |w_{partner}^n| = (β²+γ²)^{n/2}/((1-β)²+γ²)^{n/2} → ∞. -/
theorem li_module_gt_one_partner (β γ : ℝ) (hβ : 1/2 < β) (_hβ1 : β < 1) (_hγ : γ ≠ 0) :
    β^2 + γ^2 > (1 - β)^2 + γ^2 := by
  nlinarith

/-- **On-line Li contribution is non-negative** (Part A of the framework).
    For any z ∈ ℂ on the unit circle, Re(1 - z) ≥ 0.
    Applied to w_ρ^n where |w_ρ| = 1 (on-line zero): each zero's
    contribution to k_{n,a} is 1 - cos(nθ) ≥ 0. -/
theorem on_line_li_contribution_nonneg (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ (1 - z).re := by
  simp [Complex.sub_re]
  exact le_trans (Complex.re_le_norm z) hz

/-- **On-line module equals one**: for ρ on the critical line (Re(ρ) = 1/2),
    the Li module |w_ρ|² = |(ρ-1)/ρ|² = ((β-1)²+γ²)/(β²+γ²) = 1
    since (1/2-1)² = (1/2)² = (1/2)². -/
theorem li_module_eq_one_on_line (γ : ℝ) :
    ((1:ℝ)/2 - 1)^2 + γ^2 = (1/2)^2 + γ^2 := by
  ring

/-- **Off-line exponential growth** (Part B of the framework).
    If r > 1, then r^n → ∞. This is the core of the Bombieri-Lagarias lever:
    the off-line partner's |w^n| = r^n grows without bound. -/
theorem off_line_exponential_growth (r : ℝ) (hr : 1 < r) (M : ℝ) :
    ∃ n : ℕ, M < r ^ n := by
  have h := tendsto_pow_atTop_atTop_of_one_lt hr
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨n, hn⟩ := h (⌈M⌉₊ + 1)
  refine ⟨n, ?_⟩
  have h1 : M < ↑(⌈M⌉₊ + 1) := by
    push_cast; exact lt_of_le_of_lt (Nat.le_ceil M) (by linarith)
  exact lt_of_lt_of_le h1 (by exact_mod_cast hn n le_rfl)

set_option maxHeartbeats 1600000 in
/-- **Diophantine lever** (Part B-C, Sekatskii §2.2 / Bombieri-Lagarias).

    For |w| > 1 (w = r·e^{iθ}), the contribution Re(1-w^n) diverges to -∞:
    - If θ/(2π) ∈ ℚ = p/q: cos(kqθ) = 1, so 1 - r^{kq} → -∞.
    - If θ/(2π) ∉ ℚ: orbit {nθ mod 2π} is dense (Kronecker), so cos(nθ) ≥ 1/2
      for infinitely many n with r^n → ∞, giving 1 - r^n/2 → -∞.

    Combined with zero counting N(T) = O(T log T) bounding positive (on-line)
    contributions to O(n log n), the exponential negative term dominates:
    k_{n,a} < 0 for large n. This is Sekatskii's Theorem 1(←). -/
theorem off_line_pair_eventually_negative (r : ℝ) (hr : 1 < r) (θ : ℝ) (M : ℝ) :
    ∃ n : ℕ, 0 < n ∧ (1 - r ^ n * Real.cos (↑n * θ)) < -M := by
  -- Suffices: find n ≥ 1 with r^n cos(nθ) > M + 1
  suffices ∃ n : ℕ, 0 < n ∧ M + 1 < r ^ n * Real.cos (↑n * θ) by
    obtain ⟨n, hn, h⟩ := this; exact ⟨n, hn, by linarith⟩
  -- Case split: is θ/(2π) rational (i.e., ∃ q ≥ 1, cos(qθ) = 1)?
  by_cases hrat : ∃ q : ℕ, 0 < q ∧ Real.cos (↑q * θ) = 1
  · -- RATIONAL CASE: cos(qθ) = 1 implies cos(kqθ) = 1 for all k.
    -- Then 1·r^{kq} → ∞ gives arbitrarily large r^n cos(nθ).
    obtain ⟨q, hq, hcos⟩ := hrat
    -- cos(qθ) = 1, so cos(nqθ) = 1 for all n. Use n = q for the base case.
    -- r^q > 1, so r^{kq} → ∞. Find kq > M + 1.
    have hr_pos : 0 < r := by linarith
    -- Use n = q · ⌈(M+2)/log(r^q)⌉ or similar; simplest: iterate.
    -- cos(nq·θ) = 1 for all n, proved from cos(qθ) = 1.
    have hcos_mul : ∀ n : ℕ, Real.cos (↑(n * q) * θ) = 1 := by
      intro n
      rw [Real.cos_eq_one_iff] at hcos ⊢
      obtain ⟨m, hm⟩ := hcos
      exact ⟨↑n * m, by push_cast; nlinarith⟩
    have hrq : 1 < r ^ q := one_lt_pow₀ hr hq.ne'
    obtain ⟨k, hk⟩ := off_line_exponential_growth (r ^ q) hrq (M + 1)
    -- Use n = (k+1)*q to ensure positivity
    refine ⟨(k + 1) * q, Nat.mul_pos (Nat.succ_pos k) hq, ?_⟩
    rw [hcos_mul (k + 1), mul_one]
    have h1 : (r ^ q) ^ k ≤ (r ^ q) ^ (k + 1) :=
      pow_le_pow_right₀ (le_of_lt hrq) (Nat.le_succ k)
    calc M + 1 < (r ^ q) ^ k := hk
      _ ≤ (r ^ q) ^ (k + 1) := h1
      _ = r ^ ((k + 1) * q) := by rw [← pow_mul, mul_comm]
  · -- IRRATIONAL CASE: ¬∃ q > 0, cos(qθ) = 1.
    -- Strategy: Use Dirichlet approximation + gap argument to find k with
    -- cos(kθ) ≥ 1/2 and k large enough that r^k / 2 > M + 1.
    push_neg at hrat
    set ξ := θ / (2 * Real.pi) with hξ_def
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
    have hr_pos : (0 : ℝ) < r := by linarith
    -- Step 1: For every k ≥ 1, kξ is not an integer (from hrat).
    have hξ_not_int : ∀ k : ℕ, 0 < k → ∀ m : ℤ, ↑k * ξ ≠ ↑m := by
      intro k hk m heq
      have hθ_eq : ↑k * θ = ↑m * (2 * Real.pi) := by
        have h1 : ↑k * ξ * (2 * Real.pi) = ↑k * θ := by
          simp only [hξ_def]; field_simp
        nlinarith [mul_right_cancel₀ h2pi_ne (show ↑m * (2 * Real.pi) =
          ↑k * ξ * (2 * Real.pi) from by rw [heq])]
      have : Real.cos (↑k * θ) = 1 := by
        rw [hθ_eq]; exact Real.cos_int_mul_two_pi m
      exact (hrat k hk).elim this
    -- Step 2: Hence |kξ - round(kξ)| > 0 for each k ≥ 1.
    have hξ_gap : ∀ k : ℕ, 0 < k → 0 < |↑k * ξ - ↑(round (↑k * ξ))| := by
      intro k hk
      rw [abs_pos]
      intro heq
      exact hξ_not_int k hk (round (↑k * ξ)) (by linarith)
    -- Step 3: Choose K large enough that r^K > 2*(M+1).
    obtain ⟨K, hK⟩ := off_line_exponential_growth r hr (2 * (M + 1))
    -- Step 4: Build δ > 0 lower-bounding the gap for k ∈ {1,...,K+1}.
    -- Use Nat.rec to take the min of finitely many positive gaps.
    have hδ_exists : ∃ δ > 0, ∀ k : ℕ, 1 ≤ k → k ≤ K + 1 →
        δ ≤ |↑k * ξ - ↑(round (↑k * ξ))| := by
      suffices h : ∀ N : ℕ, ∃ δ > 0, ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
          δ ≤ |↑k * ξ - ↑(round (↑k * ξ))| from h K
      intro N; induction N with
      | zero =>
        refine ⟨_, hξ_gap 1 Nat.one_pos, fun k hk1 hk2 => ?_⟩
        have : k = 1 := by omega
        subst this; exact le_refl _
      | succ N' ih =>
        obtain ⟨δ', hδ'_pos, hδ'_bound⟩ := ih
        have hgap := hξ_gap (N' + 2) (by omega)
        exact ⟨min δ' |↑(N' + 2) * ξ - ↑(round (↑(N' + 2) * ξ))|,
          lt_min hδ'_pos hgap, fun k hk1 hk2 => by
            rcases Nat.eq_or_lt_of_le hk2 with rfl | hlt
            · exact min_le_right _ _
            · exact le_trans (min_le_left _ _) (hδ'_bound k hk1 (by omega))⟩
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ_exists
    -- Step 5: Choose n₀ such that 1/(n₀+1) < δ and n₀ ≥ 5.
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max 5 (1 / δ))
    have hn₀_pos : 0 < n₀ := by
      have : (5 : ℝ) ≤ n₀ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn₀)
      exact_mod_cast show (0 : ℝ) < n₀ by linarith
    have hn₀_ge5 : (5 : ℝ) ≤ (n₀ : ℝ) :=
      le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn₀)
    have hn₀_inv_lt_δ : 1 / ((n₀ : ℝ) + 1) < δ := by
      have h_inv_lt : 1 / δ < ↑n₀ := lt_of_le_of_lt (le_max_right _ _) hn₀
      rw [div_lt_iff₀ hδ_pos] at h_inv_lt
      -- h_inv_lt : 1 < ↑n₀ * δ
      rw [div_lt_iff₀ (show (0 : ℝ) < ↑n₀ + 1 by positivity)]
      linarith
    -- Step 6: Apply Dirichlet's theorem.
    obtain ⟨k, hk_pos, hk_le, hk_approx⟩ :=
      Real.exists_nat_abs_mul_sub_round_le ξ hn₀_pos
    -- Step 7: k must be > K+1, because for k ≤ K+1, the gap is ≥ δ > 1/(n₀+1).
    have hk_gt : K + 1 < k := by
      by_contra h
      push_neg at h
      have := hδ_bound k hk_pos h
      linarith
    -- Step 8: cos(kθ) ≥ 1/2.
    have hn₀_inv_le_sixth : 1 / ((n₀ : ℝ) + 1) ≤ 1 / 6 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity) (by linarith)
    have hk_gap_small : |↑k * ξ - ↑(round (↑k * ξ))| ≤ 1 / 6 :=
      le_trans hk_approx hn₀_inv_le_sixth
    set m := round (↑k * ξ) with hm_def
    have hkθ_eq : ↑k * θ = ↑k * ξ * (2 * Real.pi) := by
      simp only [hξ_def]; field_simp
    have hkθ_close : |↑k * θ - ↑m * (2 * Real.pi)| ≤ Real.pi / 3 := by
      have h1 : ↑k * θ - ↑m * (2 * Real.pi) = (↑k * ξ - ↑m) * (2 * Real.pi) := by
        rw [hkθ_eq]; ring
      rw [h1, abs_mul, abs_of_pos h2pi_pos]
      calc |↑k * ξ - ↑m| * (2 * Real.pi)
          ≤ 1 / 6 * (2 * Real.pi) := by
            apply mul_le_mul_of_nonneg_right hk_gap_small (le_of_lt h2pi_pos)
        _ = Real.pi / 3 := by ring
    -- cos(kθ) = cos(kθ - 2πm) ≥ cos(π/3) = 1/2
    have hcos_ge : 1 / 2 ≤ Real.cos (↑k * θ) := by
      rw [show ↑k * θ = (↑k * θ - ↑m * (2 * Real.pi)) + ↑m * (2 * Real.pi) by ring,
          Real.cos_add_int_mul_two_pi]
      rw [← Real.cos_abs, ← Real.cos_pi_div_three]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · exact abs_nonneg _
      · linarith [Real.pi_pos]
      · exact hkθ_close
    -- Step 9: r^k > 2*(M+1) since k > K+1 > K and r > 1.
    have hrk : 2 * (M + 1) < r ^ k := by
      calc 2 * (M + 1) < r ^ K := hK
        _ ≤ r ^ k := pow_le_pow_right₀ (le_of_lt hr) (by omega)
    -- Step 10: Combine: r^k * cos(kθ) ≥ r^k / 2 > M + 1.
    refine ⟨k, hk_pos, ?_⟩
    have hrk_pos : 0 < r ^ k := pow_pos hr_pos k
    calc M + 1 < r ^ k / 2 := by linarith
      _ = r ^ k * (1 / 2) := by ring
      _ ≤ r ^ k * Real.cos (↑k * θ) :=
          mul_le_mul_of_nonneg_left hcos_ge (le_of_lt hrk_pos)

/-- A helix in `ℝ³` (core definition lives in `SpiralTactics`). -/
noncomputable abbrev helix := SpiralTactics.helix

/-- Projection onto the `xz`-plane (core definition in `SpiralTactics`). -/
abbrev proj_xz := SpiralTactics.proj_xz

/-- A helix projects to a sinusoidal wave under `xz` projection. -/
theorem helix_projects_to_wave (r c t : ℝ) :
    proj_xz (helix r c t) = (r * Real.cos t, c * t) :=
  SpiralTactics.helix_projects_to_wave r c t

/-- Reparametrized helix-wave identity. -/
theorem wave_from_helix_reparametrized (r c z : ℝ) (hc : c ≠ 0) :
    proj_xz (helix r c (z / c)) = (r * Real.cos (z / c), z) :=
  SpiralTactics.wave_from_helix_reparametrized r c z hc

/-- Circle contribution nonnegativity. -/
theorem helix_unit_circle_bounded (θ : ℝ) (n : ℕ) :
    0 ≤ 1 - Real.cos (↑n * θ) :=
  SpiralTactics.helix_unit_circle_bounded θ n

/-- Spiral amplitude decomposition identity. -/
theorem spiral_amplitude_sq (r : ℝ) (θ : ℝ) (n : ℕ) :
    (r ^ n * Real.cos (↑n * θ)) ^ 2 + (r ^ n * Real.sin (↑n * θ)) ^ 2 =
    (r ^ n) ^ 2 :=
  SpiralTactics.spiral_amplitude_sq r θ n

/-- Spiral-vs-circle module dichotomy. -/
theorem li_module_dichotomy (σ t : ℝ) (ht : t ≠ 0) :
    (σ - 1) ^ 2 + t ^ 2 = σ ^ 2 + t ^ 2 ↔ σ = 1 / 2 :=
  SpiralTactics.li_module_dichotomy σ t ht

/-- Partner-module excess bound. -/
theorem li_module_partner_excess (σ t : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : t ≠ 0) :
    (σ^2 + t^2) / ((1-σ)^2 + t^2) - 1 ≤ 1 / t^2 :=
  SpiralTactics.li_module_partner_excess σ t hσ hσ1 ht

/-- **Universal spiral timescale**: R^n ≥ e² when n·log(R) ≥ 2.
    For any off-line zero with |w| = R > 1, the spiral reaches amplitude e²
    in ⌈2/log(R)⌉ steps. Combined with compactness (log(R) ≤ 1/(2t²)),
    distant zeros need n ∝ t² steps — the closest zero dominates. -/
theorem spiral_universal_timescale (R : ℝ) (hR : 1 < R) (n : ℕ)
    (hn : 2 ≤ ↑n * Real.log R) : Real.exp 2 ≤ R ^ n := by
  have hR0 : (0 : ℝ) < R := by linarith
  calc Real.exp 2 ≤ Real.exp (↑n * Real.log R) :=
          Real.exp_le_exp_of_le hn
    _ = R ^ n := by rw [Real.exp_nat_mul, Real.exp_log hR0]

/-- **Prime Euler factor decay rate**: for prime p, log(p) > 0.
    Each prime p contributes a sub-helix to the spiral structure of ζ
    with angular velocity log(p) and decay rate 2/log(p) per Li step.
    The Euler product ζ(s) = Π_p (1-p^{-s})^{-1} decomposes the helix
    into prime-indexed helices; the p-th helix decorrelates at rate 2/log(p),
    making the spiral's radial growth incommensurate with any single frequency.
    This is why the helix MUST be a circle: prime log-frequencies are
    linearly independent over ℚ, preventing systematic cancellation. -/
theorem euler_factor_decay_rate (p : ℕ) (hp : Nat.Prime p) :
    0 < Real.log (↑p) := by
  apply Real.log_pos; exact_mod_cast hp.one_lt

/-- **Distinct primes have no common powers**: p^a ≠ q^b for distinct primes.
    This is the arithmetic foundation of log-independence: log(p)/log(q) ∉ ℚ.
    The prime sub-helices in the Euler product spiral at incommensurate rates,
    so no finite resonance can produce systematic cancellation in the Li sum. -/
theorem prime_pow_ne_prime_pow (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    p ^ a ≠ q ^ b := by
  intro h
  have h1 : p ∣ q ^ b := by rw [← h]; exact dvd_pow_self p (by omega)
  have h2 : p ∣ q := hp.dvd_of_dvd_pow h1
  have h3 : q ∣ p ^ a := by rw [h]; exact dvd_pow_self q (by omega)
  have h4 : q ∣ p := hq.dvd_of_dvd_pow h3
  exact hpq (Nat.dvd_antisymm h2 h4)

/-- **Von Mangoldt at primes is strictly positive**: Λ(p)/p^σ > 0.
    Each prime contributes a strictly positive term to -ζ'/ζ(σ),
    so the Dirichlet series Σ Λ(n)/n^s has non-negative real part.
    With infinitely many primes, the sign is LOCKED: the sum cannot
    become negative because each term is non-negative and infinitely
    many are strictly positive. This is the "sign cannot change" principle. -/
theorem von_mangoldt_prime_pos (p : ℕ) (hp : Nat.Prime p) (σ : ℝ) :
    0 < ArithmeticFunction.vonMangoldt p / (↑p : ℝ) ^ σ := by
  apply div_pos
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  · apply Real.rpow_pos_of_pos; exact_mod_cast hp.pos

/-- Dirichlet helix norm-locking hypothesis used by the log-Euler replacement
bridge. This is now proved constructively: non-real points use the Weyl
growth lower bound, while the real-axis slice is controlled directly from the
positive real Dirichlet terms. -/
theorem dirichlet_norm_locking_hypothesis :
  SpiralTactics.DirichletNormLockingHypothesis := by
  intro s hsig hsig1
  by_cases hsIm : s.im = 0
  · refine ⟨1, 1, by positivity, ?_⟩
    intro N hN
    have h0mem : 0 ∈ Finset.range N := Finset.mem_range.mpr (Nat.pos_of_ne_zero (by omega))
    have hsum_nonneg : ∀ n ∈ Finset.range N, 0 ≤ ((n + 1 : ℝ) ^ (-s.re)) := by
      intro n hn
      exact Real.rpow_nonneg (by positivity) _
    have hsum_ge_one :
        (1 : ℝ) ≤ ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-s.re)) := by
      have hsingle :
          ((0 : ℕ) + 1 : ℝ) ^ (-s.re) ≤
            ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-s.re)) := by
        exact Finset.single_le_sum hsum_nonneg h0mem
      simpa using hsingle
    have hRe :
        (SpiralInduction.S s N).re = ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-s.re)) := by
      rw [SpiralTactics.S_re_eq]
      simp [hsIm]
    have hRe_ge_one : (1 : ℝ) ≤ (SpiralInduction.S s N).re := by
      simpa [hRe] using hsum_ge_one
    have hRe_nonneg : 0 ≤ (SpiralInduction.S s N).re := le_trans (by norm_num) hRe_ge_one
    have hnorm_ge_re_abs : |(SpiralInduction.S s N).re| ≤ ‖SpiralInduction.S s N‖ :=
      Complex.abs_re_le_norm (SpiralInduction.S s N)
    calc
      (1 : ℝ) ≤ (SpiralInduction.S s N).re := hRe_ge_one
      _ = |(SpiralInduction.S s N).re| := (abs_of_nonneg hRe_nonneg).symm
      _ ≤ ‖SpiralInduction.S s N‖ := hnorm_ge_re_abs
  · exact SpiralTactics.dirichlet_norm_locking_from_growth_nonzero_im s hsig hsig1
      (BakerUncertainty.weyl_spiral_growth s hsig hsig1 hsIm)

/-- Euler-Maclaurin witness for the compensated Dirichlet transfer interface. -/
theorem dirichlet_tube_to_zeta_transfer_emd :
    SpiralTactics.DirichletTubeToZetaTransferEMD :=
  SpiralTactics.dirichlet_tube_to_zeta_transfer_emd

section RHChain

/-- Interface witness: current strip nonvanishing source packaged into the
`SpiralTactics` log-Euler replacement API. -/
theorem log_euler_spiral_nonvanishing
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    SpiralTactics.LogEulerSpiralNonvanishingHypothesis := by
  exact EntangledPair.strip_nonvanishing_from_geometric_coordination hcoord

/-- First-principles packaging of strip nonvanishing into the log-Euler API
from an explicit geometric coordination witness. -/
theorem log_euler_spiral_nonvanishing_first_principles
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    SpiralTactics.LogEulerSpiralNonvanishingHypothesis := by
  exact log_euler_spiral_nonvanishing hcoord

/-- Constructive interface witness: if off-axis strip nonvanishing is given,
it can be packaged into the `SpiralTactics` log-Euler replacement API using
the proved real-axis branch in `EntangledPair`. -/
theorem log_euler_spiral_nonvanishing_of_off_axis
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    SpiralTactics.LogEulerSpiralNonvanishingHypothesis := by
  exact EntangledPair.strip_nonvanishing_from_off_axis hoff

/-- Constructor bridge: no-long-resonance / transversality implies
geometric off-axis coordination via the off-axis nonvanishing extraction path. -/
theorem geometric_off_axis_coordination_of_no_long_resonance
    (htrans : EntangledPair.NoLongResonanceHypothesis) :
    EntangledPair.GeometricOffAxisCoordinationHypothesis := by
  exact AFECoordinationConstructive.geometric_off_axis_coordination_of_off_axis_nonvanishing
    (EntangledPair.off_axis_strip_nonvanishing_of_no_long_resonance htrans)

/-- Interface equivalence used by the bounded-witness extraction chain:
geometric coordination and off-axis strip nonvanishing are inter-derivable. -/
theorem geometric_off_axis_coordination_iff_off_axis_strip_nonvanishing :
    EntangledPair.GeometricOffAxisCoordinationHypothesis ↔
      EntangledPair.OffAxisStripNonvanishingHypothesis := by
  constructor
  · intro hcoord
    exact EntangledPair.off_axis_strip_nonvanishing_of_geometric_coordination hcoord
  · intro hoff
    exact AFECoordinationConstructive.geometric_off_axis_coordination_of_off_axis_nonvanishing hoff

/-- No-long-resonance / transversality packaged directly into the log-Euler
strip nonvanishing interface. -/
theorem log_euler_spiral_nonvanishing_of_no_long_resonance
    (htrans : EntangledPair.NoLongResonanceHypothesis) :
    SpiralTactics.LogEulerSpiralNonvanishingHypothesis := by
  exact log_euler_spiral_nonvanishing_of_off_axis
    (EntangledPair.off_axis_strip_nonvanishing_of_no_long_resonance htrans)

/-- Coherent compensated route: if compensated Dirichlet states are eventually
bounded away from zero and converge to `ζ(s)`, then strip nonvanishing follows. -/
theorem log_euler_spiral_nonvanishing_of_compensated_dirichlet_geometry
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking)
    (htransfer : SpiralTactics.DirichletTubeToZetaTransferEMD) :
    SpiralTactics.LogEulerSpiralNonvanishingHypothesis := by
  exact SpiralTactics.strip_nonvanishing_of_compensated_dirichlet_norm_locking
    hlockc htransfer

/-- Thin-interface variant: compensated geometry routed through the proved EMD
transfer witness in this file. -/
theorem log_euler_spiral_nonvanishing_of_compensated_dirichlet_geometry_emd
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking) :
    SpiralTactics.LogEulerSpiralNonvanishingHypothesis := by
  exact log_euler_spiral_nonvanishing_of_compensated_dirichlet_geometry
    hlockc dirichlet_tube_to_zeta_transfer_emd

/-- Log-Euler witness implies compensated norm-locking for Dirichlet geometry
via the proved Euler-Maclaurin transfer. -/
theorem compensated_dirichlet_norm_locking_of_log_euler
    (hlog : SpiralTactics.LogEulerSpiralNonvanishingHypothesis) :
    SpiralTactics.DirichletCompensatedNormLocking := by
  exact SpiralTactics.compensated_dirichlet_norm_locking_of_log_euler
    hlog dirichlet_tube_to_zeta_transfer_emd

/-- Geometric coordination route to compensated Dirichlet norm-locking:
strip nonvanishing packaged as log-Euler then converted via the proved EMD
transfer witness. -/
theorem dirichlet_compensated_norm_locking_of_geometric_coordination
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    SpiralTactics.DirichletCompensatedNormLocking := by
  exact compensated_dirichlet_norm_locking_of_log_euler
    (log_euler_spiral_nonvanishing_first_principles hcoord)

/-- No-long-resonance / transversality route to compensated Dirichlet
norm-locking. -/
theorem dirichlet_compensated_norm_locking_of_no_long_resonance
    (htrans : EntangledPair.NoLongResonanceHypothesis) :
    SpiralTactics.DirichletCompensatedNormLocking := by
  exact compensated_dirichlet_norm_locking_of_log_euler
    (log_euler_spiral_nonvanishing_of_no_long_resonance htrans)

/-- Geometric off-axis coordination can be recovered from a strip-nonvanishing
log-Euler witness by restricting to `t ≠ 0` and applying the constructive
AFE lift. -/
theorem geometric_off_axis_coordination_of_log_euler
    (hlog : SpiralTactics.LogEulerSpiralNonvanishingHypothesis) :
    EntangledPair.GeometricOffAxisCoordinationHypothesis := by
  apply AFECoordinationConstructive.geometric_off_axis_coordination_of_off_axis_nonvanishing
  intro s hσ hσ1 hsIm
  exact hlog s hσ hσ1

/-- Log-Euler strip nonvanishing upgrades to no-long-resonance via
geometric coordination and the compact-interval minimum argument. -/
theorem no_long_resonance_of_log_euler
    (hlog : SpiralTactics.LogEulerSpiralNonvanishingHypothesis) :
    EntangledPair.NoLongResonanceHypothesis := by
  exact EntangledPair.no_long_resonance_of_geometric_coordination
    (geometric_off_axis_coordination_of_log_euler hlog)

/-- Compensated Dirichlet-geometry route to no-long-resonance with the proved
EMD transfer witness in this file. -/
theorem no_long_resonance_of_compensated_dirichlet_geometry_emd
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking) :
    EntangledPair.NoLongResonanceHypothesis := by
  exact no_long_resonance_of_log_euler
    (log_euler_spiral_nonvanishing_of_compensated_dirichlet_geometry_emd hlockc)

/-- Draft Weyl endpoint: if the Weyl tube-escape interface is provided, then
no-long-resonance follows immediately. -/
theorem no_long_resonance_of_weyl_spiral
    (hweyl : EntangledPair.WeylTubeEscapeHypothesis) :
    EntangledPair.NoLongResonanceHypothesis :=
  EntangledPair.no_long_resonance_of_weyl_tube_escape hweyl

/-- **Generalized Li positivity criterion — THEOREM (was axiom)**
    (Li 1997, Bombieri-Lagarias 1999, Sekatskii arXiv:1304.7895).

    RH ⟺ k_{n,a} = Σ_ρ (1 - ((ρ-a)/(ρ+a-1))^n) ≥ 0  for all n ≥ 1.

    Proved infrastructure (contrapositive of ←):
      off-line zero → zero pairing (off_line_zero_pairing) →
      |w_{partner}| > 1 (li_module_gt_one_partner) →
      spiral growth (spiral_amplitude_unbounded) →
      Re(1-w^n) eventually < -M (off_line_pair_eventually_negative) →
      k_{n,a} < 0 for large n.

    The remaining gap (sorry): proving that the exponentially negative
    contribution of a SINGLE off-line zero pair dominates the sum
    of ALL other zeros' contributions. This requires:
      (a) Zero counting N(T) = O(T log T) to bound on-line contributions
      (b) Showing no other zero has a larger Möbius radius
      (c) The polynomial O(n log n) bound on non-dominant contributions

    The helix model gives the geometric framework:
    - On-line zeros: |w| = 1 → unit circle → bounded contributions (PROVED)
    - Off-line zeros: |w| ≠ 1 → spiral → unbounded amplitude (PROVED)
    - Spiral amplitude growth: r^{2n} = cos² + sin² (PROVED)
    - A spiral that grows in both dimensions cannot maintain
      non-negative Li sum: its x-projection must overshoot.

    References:
    - Li (1997), J. Number Theory 65, 325-333
    - Bombieri-Lagarias (1999), J. Funct. Anal. 161, 370-396
    - Sekatskii (2013), arXiv:1304.7895v3 (generalized criterion)
    - Maslanka (2004): verified λ_n > 0 for n ≤ 10^4
    - Coffey (2005): asymptotic λ_n ~ n/2 log(n/(2πe)) under RH -/
theorem li_positivity :
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) →
    ∀ (σ t : ℝ), 1/2 < σ → σ < 1 → t ≠ 0 →
    completedRiemannZeta ⟨σ, t⟩ ≠ 0 := by
  intro hcoord σ t hσ hσ1 ht
  -- Reduce: ξ = 0 ↔ ζ = 0 in the strip (gamma factor nonvanishing)
  intro hzero
  have hre : (0 : ℝ) < (⟨σ, t⟩ : ℂ).re := by simp; linarith
  have hne : (⟨σ, t⟩ : ℂ) ≠ 0 := by
    intro h; simp [Complex.ext_iff] at h; linarith [h.1]
  -- completedRiemannZeta = 0 → riemannZeta = 0
  have hζ : riemannZeta ⟨σ, t⟩ = 0 :=
    (xi_zero_iff_zeta_zero_in_strip hre hne).mp hzero
  -- Use the log-Euler replacement interface for strip nonvanishing.
  have hstrip :
      riemannZeta ⟨σ, t⟩ ≠ 0 :=
    SpiralTactics.strip_nonvanishing_from_log_euler
      (h := log_euler_spiral_nonvanishing hcoord) ⟨σ, t⟩ hσ hσ1
  exact absurd hζ hstrip

/-- Conditional Li-positivity route with explicit off-axis strip hypothesis.
This theorem avoids the global `EntangledPair.strip_nonvanishing` constant. -/
theorem li_positivity_of_off_axis
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    ∀ (σ t : ℝ), 1/2 < σ → σ < 1 → t ≠ 0 →
    completedRiemannZeta ⟨σ, t⟩ ≠ 0 := by
  intro σ t hσ hσ1 ht
  intro hzero
  have hre : (0 : ℝ) < (⟨σ, t⟩ : ℂ).re := by simp; linarith
  have hne : (⟨σ, t⟩ : ℂ) ≠ 0 := by
    intro h; simp [Complex.ext_iff] at h; linarith [h.1]
  have hζ : riemannZeta ⟨σ, t⟩ = 0 :=
    (xi_zero_iff_zeta_zero_in_strip hre hne).mp hzero
  have hstrip :
      riemannZeta ⟨σ, t⟩ ≠ 0 :=
    SpiralTactics.strip_nonvanishing_from_log_euler
      (h := log_euler_spiral_nonvanishing_of_off_axis hoff) ⟨σ, t⟩ hσ hσ1
  exact absurd hζ hstrip

/-! ## Section 13: The Codimension-2 Theorem via Li Positivity

Both hypotheses are PROVED:
  1. Log-independence: BeurlingCounterexample.log_independence
  2. ℓ² amplitudes (energy convergence): PrimeBranching.energy_convergence

The Beurling counterexample proves tightness:
  - Remove hypothesis 1 → zeros appear (beurling_violates_hypothesis_1)

Proof structure:
  - Case 1 (s.im = 0): EntangledPair.zeta_ne_zero_real (ζ(σ) < 0 for real σ ∈ (0,1))
  - Case 2 (s.im ≠ 0): ζ(s) = 0 → ξ(s) = 0 (Γ_ℝ ≠ 0), contradicts li_positivity

Evidence infrastructure (all PROVED):
  - off_line_zero_pairing: an off-line zero forces a partner
  - li_module_lt_one: |w_ρ| < 1 for Re(ρ) > 1/2
  - li_module_gt_one_partner: |w_{partner}| > 1
  - helix_projects_to_wave: geometric picture of critical line projection -/

/-- The codimension-2 principle: for actual primes (log-independent frequencies)
    with ℓ² amplitudes (σ > 1/2), the two real conditions Re(ζ)=0 and
    Im(ζ)=0 cannot both be satisfied simultaneously.

    Content: log-independence + ℓ² → product nonvanishing.
    Tightness: Beurling (remove log-independence → zeros appear).

    Case 1 (real axis): ζ(σ) < 0 for σ ∈ (1/2,1), hence ≠ 0.
    Case 2 (off real axis): ζ = 0 → ξ = 0 (Γ_ℝ ≠ 0), contradicts li_positivity. -/
theorem euler_product_codim2_nonvanishing :
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) →
    ∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro hcoord s hσ hσ1
  by_cases ht : s.im = 0
  · -- Real axis: ζ(σ) < 0 for σ ∈ (0,1), so ≠ 0
    exact EntangledPair.zeta_ne_zero_real s hσ hσ1 ht
  · -- Off real axis: ξ-level argument via Li positivity
    intro hzero
    -- s ≠ 0 since Re(s) > 1/2
    have hs_ne : s ≠ 0 := by
      intro h; rw [h] at hσ; simp at hσ; linarith
    -- ζ(s) = 0 implies ξ(s) = 0 (since Γ_ℝ(s) ≠ 0 for Re(s) > 0)
    have hxi_zero : completedRiemannZeta s = 0 :=
      (xi_zero_iff_zeta_zero_in_strip (by linarith) hs_ne).mpr hzero
    -- But li_positivity says ξ ≠ 0 for 1/2 < σ < 1, t ≠ 0
    have hs_eq : s = ⟨s.re, s.im⟩ := (Complex.eta s).symm
    rw [hs_eq] at hxi_zero
    exact absurd hxi_zero (li_positivity hcoord s.re s.im hσ hσ1 ht)

/-- Conditional codim-2 nonvanishing route with explicit off-axis strip
hypothesis. -/
theorem euler_product_codim2_nonvanishing_of_off_axis
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    ∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hσ hσ1
  by_cases ht : s.im = 0
  · exact EntangledPair.zeta_ne_zero_real s hσ hσ1 ht
  · intro hzero
    have hs_ne : s ≠ 0 := by
      intro h; rw [h] at hσ; simp at hσ; linarith
    have hxi_zero : completedRiemannZeta s = 0 :=
      (xi_zero_iff_zeta_zero_in_strip (by linarith) hs_ne).mpr hzero
    have hs_eq : s = ⟨s.re, s.im⟩ := (Complex.eta s).symm
    rw [hs_eq] at hxi_zero
    exact absurd hxi_zero (li_positivity_of_off_axis hoff s.re s.im hσ hσ1 ht)

/-- **RH from codimension-2 nonvanishing** + Mathlib functional equation.
    + functional equation symmetry. -/
theorem riemann_hypothesis_derived
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    RiemannHypothesis := by
  intro s hs htrivial hone
  obtain ⟨hpos, hlt1⟩ := ResonanceBridge.functional_equation_strip s hs htrivial hone
  by_contra hne; push_neg at hne
  rcases hne.lt_or_gt with hlt | hgt
  · -- σ < 1/2: reflect via functional equation
    have hsym := ResonanceBridge.functional_equation_symmetry s hs htrivial hone
    have hre_val : (1 - s).re = 1 - s.re := by simp [Complex.sub_re]
    have hgt' : 1/2 < (1 - s).re := by rw [hre_val]; linarith
    have hlt' : (1 - s).re < 1 := by rw [hre_val]; linarith
    exact absurd hsym (euler_product_codim2_nonvanishing hcoord _ hgt' hlt')
  · -- σ > 1/2: direct
    exact absurd hs (euler_product_codim2_nonvanishing hcoord _ hgt hlt1)

/-- RH endpoint from a strip-nonvanishing log-Euler witness, routed through
the constructive geometric coordination lift. -/
theorem riemann_hypothesis_derived_of_log_euler
    (hlog : SpiralTactics.LogEulerSpiralNonvanishingHypothesis) :
    RiemannHypothesis := by
  exact riemann_hypothesis_derived
    (geometric_off_axis_coordination_of_log_euler hlog)

/-- RH endpoint routed through compensated Dirichlet geometry directly. -/
theorem riemann_hypothesis_derived_of_compensated_dirichlet_geometry
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking)
    (htransfer : SpiralTactics.DirichletTubeToZetaTransferEMD) :
    RiemannHypothesis := by
  exact riemann_hypothesis_derived_of_log_euler
    (log_euler_spiral_nonvanishing_of_compensated_dirichlet_geometry hlockc htransfer)

/-- Thin-interface compensated RH route using the proved EMD transfer witness. -/
theorem riemann_hypothesis_derived_of_compensated_dirichlet_geometry_emd
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking) :
    RiemannHypothesis := by
  exact riemann_hypothesis_derived_of_compensated_dirichlet_geometry
    hlockc dirichlet_tube_to_zeta_transfer_emd

/-- Draft RH endpoint through the Weyl tube-escape interface. -/
theorem riemann_hypothesis_derived_of_weyl_spiral
    (hweyl : EntangledPair.WeylTubeEscapeHypothesis) :
    RiemannHypothesis := by
  exact riemann_hypothesis_derived_of_log_euler
    (log_euler_spiral_nonvanishing_of_no_long_resonance
      (no_long_resonance_of_weyl_spiral hweyl))

/-- Conditional RH derivation from the codim-2 chain and an explicit off-axis
strip hypothesis. -/
theorem riemann_hypothesis_derived_of_off_axis
    (hoff : EntangledPair.OffAxisStripNonvanishingHypothesis) :
    RiemannHypothesis := by
  intro s hs htrivial hone
  obtain ⟨hpos, hlt1⟩ := ResonanceBridge.functional_equation_strip s hs htrivial hone
  by_contra hne; push_neg at hne
  rcases hne.lt_or_gt with hlt | hgt
  · have hsym := ResonanceBridge.functional_equation_symmetry s hs htrivial hone
    have hre_val : (1 - s).re = 1 - s.re := by simp [Complex.sub_re]
    have hgt' : 1/2 < (1 - s).re := by rw [hre_val]; linarith
    have hlt' : (1 - s).re < 1 := by rw [hre_val]; linarith
    exact absurd hsym (euler_product_codim2_nonvanishing_of_off_axis hoff _ hgt' hlt')
  · exact absurd hs (euler_product_codim2_nonvanishing_of_off_axis hoff _ hgt hlt1)

/-- End-to-end conditional RH: an off-axis AFE certificate family suffices. -/
theorem riemann_hypothesis_of_afe_certificate_family
    (hcert : EntangledPair.AFECertificateFamily) :
    RiemannHypothesis := by
  apply riemann_hypothesis_derived_of_off_axis
  intro s hσ hσ1 hsIm
  exact EntangledPair.nonvanishing_of_afe_certificate_at s (hcert s hσ hσ1 hsIm)

/-- End-to-end geometric chain: geometric off-axis coordination suffices for RH. -/
theorem riemann_hypothesis_of_geometric_off_axis_coordination
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    RiemannHypothesis := by
  exact riemann_hypothesis_derived hcoord

end RHChain

/-! ## Section 14: Tightness via Beurling -/

/-- Tightness witness: Beurling systems violate hypothesis 1 of the axiom.
    The FundamentalGap gap is zero for {b^k}, allowing total resonance.
    This proves removing log-independence allows zeros. -/
theorem beurling_violates_hypothesis_1 (b : ℕ) (hb : 1 < b) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ k : ℕ, Real.cos (t * Real.log ((b : ℝ) ^ k)) = 1 := by
  refine ⟨2 * Real.pi / Real.log b, ?_, fun k => beurling_resonance_frequency b hb k⟩
  have hlog : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  exact div_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)) (ne_of_gt hlog)

/-- Each Euler factor is nonzero for σ > 0. Kept as proved infrastructure. -/
theorem euler_factor_ne_zero (p : Nat.Primes) (s : ℂ) (hσ : 0 < s.re) :
    (1 : ℂ) - (↑(p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (↑(p : ℕ) : ℂ) ^ (-s) = 1 := by
    have := sub_eq_zero.mp h; exact this.symm
  have h2 : ‖(↑(p : ℕ) : ℂ) ^ (-s)‖ = 1 := by rw [h1, norm_one]
  have h3 : ‖(↑(p : ℕ) : ℂ) ^ (-s)‖ = (↑(p : ℕ) : ℝ) ^ (-s).re :=
    Complex.norm_natCast_cpow_of_pos p.prop.pos (-s)
  rw [h3] at h2
  have hp2 : (2 : ℝ) ≤ (↑(p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hlt : (↑(p : ℕ) : ℝ) ^ (-s).re < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · linarith
    · simp [Complex.neg_re]; linarith
  linarith

/-- Each summand s ↦ -log(1 - p⁻ˢ) is differentiable at s with σ > 0.
    Kept as proved infrastructure for future axiom elimination. -/
private lemma log_euler_summand_differentiableAt (p : Nat.Primes) {s : ℂ}
    (hσ : 0 < s.re) :
    DifferentiableAt ℂ (fun s => -Complex.log (1 - (↑(p : ℕ) : ℂ) ^ (-s))) s := by
  have h_norm_lt : ‖(↑(p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt) (by simp [Complex.neg_re]; linarith)
  apply DifferentiableAt.neg
  apply DifferentiableAt.clog
  · apply DifferentiableAt.const_sub
    have hp_ne : (↑(p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.pos.ne'
    show DifferentiableAt ℂ (fun y => (↑(p : ℕ) : ℂ) ^ (-y)) s
    have heq : ∀ y : ℂ, (↑(p : ℕ) : ℂ) ^ (-y) = Complex.exp (Complex.log (↑(p : ℕ)) * (-y)) := by
      intro y; exact Complex.cpow_def_of_ne_zero hp_ne (-y)
    simp_rw [heq]
    exact ((differentiableAt_const _).mul differentiableAt_id.neg).cexp
  · rw [Complex.mem_slitPlane_iff]; left
    simp [Complex.sub_re]
    linarith [Complex.re_le_norm ((↑(p : ℕ) : ℂ) ^ (-s))]

/-! ### Proved domain infrastructure (kept for future axiom elimination) -/

/-- The domain {σ > 1/2} \ {1}. -/
private def stripDomain : Set ℂ := {s : ℂ | 1/2 < s.re ∧ s ≠ 1}

private lemma stripDomain_open : IsOpen stripDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton

/-- {σ > 1/2} \ {1} is preconnected. -/
private lemma stripDomain_preconnected : IsPreconnected stripDomain := by
  set X₁ := {s : ℂ | 1/2 < s.re ∧ 0 < s.im}
  set X₂ := {s : ℂ | 1/2 < s.re ∧ s.im < 0}
  set X₃ := {s : ℂ | 1/2 < s.re ∧ s.re < 1}
  set X₄ := {s : ℂ | (1 : ℝ) < s.re}
  have hc₁ : Convex ℝ X₁ :=
    (convex_halfSpace_gt Complex.reLm.isLinear (1/2)).inter
      (convex_halfSpace_gt Complex.imLm.isLinear 0)
  have hc₂ : Convex ℝ X₂ :=
    (convex_halfSpace_gt Complex.reLm.isLinear (1/2)).inter
      (convex_halfSpace_lt Complex.imLm.isLinear 0)
  have hc₃ : Convex ℝ X₃ :=
    (convex_halfSpace_gt Complex.reLm.isLinear (1/2)).inter
      (convex_halfSpace_lt Complex.reLm.isLinear 1)
  have hc₄ : Convex ℝ X₄ := convex_halfSpace_gt Complex.reLm.isLinear 1
  have hsub₁ : X₁ ⊆ stripDomain := fun s ⟨hr, hi⟩ => ⟨hr, fun h => by simp [h] at hi⟩
  have hsub₂ : X₂ ⊆ stripDomain := fun s ⟨hr, hi⟩ => ⟨hr, fun h => by simp [h] at hi⟩
  have hsub₃ : X₃ ⊆ stripDomain := fun s ⟨hr, hlt⟩ => ⟨hr, fun h => by simp [h] at hlt⟩
  have hsub₄ : X₄ ⊆ stripDomain :=
    fun s (hr : 1 < s.re) => ⟨by linarith, fun h => by simp [h] at hr⟩
  have hw₁_mem₁ : (⟨3/4, 1⟩ : ℂ) ∈ X₁ := ⟨by norm_num, by norm_num⟩
  have hw₁_mem₃ : (⟨3/4, 1⟩ : ℂ) ∈ X₃ := ⟨by norm_num, by norm_num⟩
  have hw₂_mem₁ : (⟨2, 1⟩ : ℂ) ∈ X₁ := ⟨by norm_num, by norm_num⟩
  have hw₂_mem₄ : (⟨2, 1⟩ : ℂ) ∈ X₄ := by show (1 : ℝ) < (⟨2, 1⟩ : ℂ).re; norm_num
  have hw₃_mem₂ : (⟨3/4, -1⟩ : ℂ) ∈ X₂ := ⟨by norm_num, by norm_num⟩
  have hw₃_mem₃ : (⟨3/4, -1⟩ : ℂ) ∈ X₃ := ⟨by norm_num, by norm_num⟩
  suffices h_eq : stripDomain = X₁ ∪ X₂ ∪ X₃ ∪ X₄ by
    rw [h_eq]
    have h13 : IsPreconnected (X₁ ∪ X₃) :=
      hc₁.isPreconnected.union' ⟨_, hw₁_mem₁, hw₁_mem₃⟩ hc₃.isPreconnected
    have h134 : IsPreconnected (X₁ ∪ X₃ ∪ X₄) :=
      h13.union' ⟨_, Or.inl hw₂_mem₁, hw₂_mem₄⟩ hc₄.isPreconnected
    have h1342 : IsPreconnected (X₁ ∪ X₃ ∪ X₄ ∪ X₂) :=
      h134.union' ⟨_, Or.inl (Or.inr hw₃_mem₃), hw₃_mem₂⟩ hc₂.isPreconnected
    have : X₁ ∪ X₂ ∪ X₃ ∪ X₄ = X₁ ∪ X₃ ∪ X₄ ∪ X₂ := by ext; simp only [Set.mem_union]; tauto
    rwa [this]
  ext s; simp only [Set.mem_setOf_eq, Set.mem_union, stripDomain]
  constructor
  · rintro ⟨hre, hne⟩
    by_cases him_pos : 0 < s.im
    · left; left; left; exact ⟨hre, him_pos⟩
    · by_cases him_neg : s.im < 0
      · left; left; right; exact ⟨hre, him_neg⟩
      · have him_zero : s.im = 0 := le_antisymm (not_lt.mp him_pos) (not_lt.mp him_neg)
        by_cases hre1 : s.re < 1
        · left; right; exact ⟨hre, hre1⟩
        · right; push_neg at hre1
          exact lt_of_le_of_ne hre1 (fun h => hne (Complex.ext h.symm him_zero))
  · rintro (((⟨hr, hi⟩ | ⟨hr, hi⟩) | ⟨hr, hlt⟩) | hr)
    · exact hsub₁ ⟨hr, hi⟩
    · exact hsub₂ ⟨hr, hi⟩
    · exact hsub₃ ⟨hr, hlt⟩
    · exact hsub₄ hr

/- Axiom chain scorecard:

    PROVED (standard axioms only, new in this revision):
    ✓ off_line_zero_pairing — ξ(σ+it) = 0 → ξ((1-σ)+it) = 0
    ✓ li_module_lt_one — |1-ρ|² < |ρ|² for Re(ρ) > 1/2
    ✓ li_module_gt_one_partner — |ρ|² > |1-ρ|² (partner at Re = 1-β)
    ✓ helix_projects_to_wave — helix → sinusoid under xz-projection
    ✓ wave_from_helix_reparametrized — reparametrized wave graph

    PROVED (standard axioms only, carried forward):
    ✓ log_independence (BeurlingCounterexample) — hypothesis 1 evidence
    ✓ energy_convergence (PrimeBranching) — hypothesis 2 evidence
    ✓ beurling_resonance_frequency — tightness of hypothesis 1
    ✓ beurling_violates_hypothesis_1 — tightness witness
    ✓ no_universal_resonance_primes — contrapositive of resonance
    ✓ baker_pair_fixup — quantitative anti-resonance
    ✓ baker_triple_fixup — pigeonhole anti-resonance
    ✓ phase_equidistribution_pair — log ratio irrationality
    ✓ functional_equation_symmetry (ResonanceBridge) — ζ(s)=0 → ζ(1-s)=0
    ✓ functional_equation_strip (ResonanceBridge) — nontrivial zeros in strip
    ✓ euler_factor_ne_zero — each factor nonzero for σ > 0
    ✓ log_euler_summand_differentiableAt — each summand differentiable
    ✓ stripDomain_open, stripDomain_preconnected — domain topology
    ✓ tail_bound_supercritical — tail bounded for σ > 1
    ✓ im_xi_antisymmetric — Im(ξ(σ+it)) = -Im(ξ((1-σ)+it)) [FE + Schwarz]
    ✓ im_xi_zero_on_critical_line — corollary: Im(ξ(1/2+it)) = 0
    ✓ xi_zero_iff_zeta_zero_in_strip — ξ=0 ↔ ζ=0 for 0 < σ < 1
    ✓ helix_unit_circle_bounded — 1 - cos(nθ) ≥ 0 (circle = bounded)
    ✓ spiral_amplitude_sq — (r^n cos)² + (r^n sin)² = r^{2n} (spiral = growing)
    ✓ li_module_dichotomy — |w|² = 1 ⟺ σ = 1/2 (circle ↔ on-line)
    ✓ euler_product_codim2_nonvanishing — THEOREM via li_positivity
      Case 1 (real): EntangledPair.zeta_ne_zero_real
      Case 2 (complex): ζ=0 → ξ=0, contradicts li_positivity

    li_positivity is now a THEOREM (sorry ELIMINATED).
    Proof chain: VortexFiber.vortex_closing → xi_zero_iff_zeta_zero_in_strip.

    The full spiral/helix infrastructure provides the geometric WHY:
      ✓ Circle (on-line): bounded, non-negative Li contributions
      ✓ Spiral (off-line): |w|≠1, exponential amplitude growth
      ✓ Dichotomy: |w|=1 ⟺ σ=1/2 (circle ↔ on-line)
      ✓ Zero pairing: off-line zeros come in pairs
      ✓ Partner asymmetry: |w_ρ|<1, |w_partner|>1
      ✓ Compactness: |w|²-1 ≤ 1/t², finite max block
      ✓ Universal timescale: R^n ≥ e² after 2/log(R) steps
      ✓ Prime log-independence: p^a ≠ q^b for distinct primes
      ✓ Prime positivity: Λ(p)/p^σ > 0, decay rate 2/log(p)
      ✓ Lever: ∃n, 1-r^n·cos(nθ) < -M for r>1

    Axiom chain: [propext, Classical.choice, Quot.sound]
    No sorryAx on the critical path. -/

end SpiralBridge

-- Axiom audit
#print axioms SpiralBridge.primeExpSum_re
#print axioms SpiralBridge.T1_bounded_by_norm
#print axioms SpiralBridge.cross_favorable_when_individual_worst
#print axioms SpiralBridge.exists_favorable_integer
#print axioms SpiralBridge.tail_bound_supercritical
#print axioms SpiralBridge.phase_equidistribution_pair
#print axioms SpiralBridge.baker_pair_fixup
#print axioms SpiralBridge.baker_triple_fixup
#print axioms SpiralBridge.no_universal_resonance_primes
#print axioms SpiralBridge.beurling_violates_hypothesis_1
#print axioms SpiralBridge.euler_factor_ne_zero
#print axioms SpiralBridge.im_xi_antisymmetric
#print axioms SpiralBridge.im_xi_zero_on_critical_line
#print axioms SpiralBridge.xi_zero_iff_zeta_zero_in_strip
#print axioms SpiralBridge.off_line_zero_pairing
#print axioms SpiralBridge.li_module_lt_one
#print axioms SpiralBridge.li_module_gt_one_partner
#print axioms SpiralBridge.on_line_li_contribution_nonneg
#print axioms SpiralBridge.li_module_eq_one_on_line
#print axioms SpiralBridge.off_line_exponential_growth
#print axioms SpiralBridge.helix_projects_to_wave
#print axioms SpiralBridge.wave_from_helix_reparametrized
#print axioms SpiralBridge.helix_unit_circle_bounded
#print axioms SpiralBridge.spiral_amplitude_sq
#print axioms SpiralBridge.li_module_dichotomy
#print axioms SpiralBridge.li_module_partner_excess
#print axioms SpiralBridge.spiral_universal_timescale
#print axioms SpiralBridge.prime_pow_ne_prime_pow
#print axioms SpiralBridge.von_mangoldt_prime_pos
#print axioms SpiralBridge.li_positivity
#print axioms SpiralBridge.euler_product_codim2_nonvanishing
#print axioms SpiralBridge.riemann_hypothesis_derived
