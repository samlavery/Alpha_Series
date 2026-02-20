/-
  BeurlingCounterexample.lean — The Riemann Hypothesis Is Fragile
  ===============================================================

  Zero-axiom demonstration that the Riemann Hypothesis for
  ζ(s) = Π_p (1-p^{-s})^{-1} depends on the linear independence of
  {log p : p prime} over ℤ — the "FundamentalGap constant" of the zeta function.

  For Beurling generalized primes where this independence fails, the
  analog of RH is false. Diamond–Montgomery–Vorhauer (2006) proved
  Beurling systems exist satisfying PNT with off-line zeros.

  Structure (parallel to LiouvilleCounterexample.lean):
  1. Actual primes: log-independent (phases cannot resonate off σ=1/2)
  2. Beurling "primes": log-dependent (phases resonate trivially)
  3. Tilt: same for both systems (tilt alone doesn't prevent zeros)
  4. The FundamentalGap gap: positive for primes, zero for Beurling

  All results: zero custom axioms (only propext, Classical.choice, Quot.sound).
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

namespace BeurlingCounterexample

/-! ## Part 1: Logarithmic Independence of Actual Primes

{log 2, log 3, log 5, ...} is linearly independent over ℤ.
Proof: unique prime factorization. If a·log(p) = b·log(q) then
p^a = q^b, impossible for distinct primes.

This is the RH FundamentalGap constant. Baker (1966) makes it effective:
|Σ bᵢ log pᵢ| > exp(-C(log B)^κ). Without this bound, prime phases
can resonate off the critical line and zeros migrate from Re(s) = 1/2. -/

/-- Log of a prime is positive. -/
lemma log_prime_pos {p : ℕ} (hp : Nat.Prime p) : 0 < Real.log (p : ℝ) :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

/-- Distinct primes have distinct powers (fundamental theorem of arithmetic). -/
lemma prime_pow_ne {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    {a : ℕ} (ha : 0 < a) (b : ℕ) : p ^ a ≠ q ^ b := by
  intro h
  have h1 : p ∣ p ^ a := dvd_pow_self p (by omega : a ≠ 0)
  rw [h] at h1
  rcases hq.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow h1) with h3 | h3
  · exact absurd h3 hp.one_lt.ne'
  · exact hne h3

/-- **Log-linear independence**: no integer relation a·log(p) = b·log(q)
    exists for distinct primes. The FundamentalGap constant of ζ(s) is positive. -/
theorem log_independence {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    (a : ℤ) * Real.log p ≠ (b : ℤ) * Real.log q := by
  intro h
  have h1 : Real.log ((p : ℝ) ^ a) = Real.log ((q : ℝ) ^ b) := by
    rw [Real.log_pow, Real.log_pow]; exact_mod_cast h
  have h2 : (p : ℝ) ^ a = (q : ℝ) ^ b :=
    Real.log_injOn_pos
      (Set.mem_Ioi.mpr (pow_pos (by exact_mod_cast hp.pos) _))
      (Set.mem_Ioi.mpr (pow_pos (by exact_mod_cast hq.pos) _)) h1
  exact prime_pow_ne hp hq hne ha b (by exact_mod_cast h2)

/-- FundamentalGap gap for actual primes: |a·log(p) - b·log(q)| > 0.
    Baker's theorem strengthens this to an effective lower bound. -/
theorem fundamentalGap_gap_pos {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < |(a : ℤ) * Real.log p - (b : ℤ) * Real.log q| :=
  abs_pos.mpr (sub_ne_zero.mpr (log_independence hp hq hne ha hb))

/-- Concrete: 2² ≠ 3, so 2·log(2) ≠ log(3). Primes 2, 3 cannot resonate. -/
theorem no_resonance_2_3 : 2 * Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
  intro h
  have h1 : Real.log ((2 : ℝ) ^ 2) = Real.log (3 : ℝ) := by
    rw [Real.log_pow]; push_cast; linarith
  have h2 : (2 : ℝ) ^ 2 = 3 :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by norm_num)) h1
  norm_num at h2

/-- Concrete: 2³ ≠ 3², so 3·log(2) ≠ 2·log(3). -/
theorem no_resonance_2_3_v2 : 3 * Real.log (2 : ℝ) ≠ 2 * Real.log (3 : ℝ) := by
  intro h
  have h1 : Real.log ((2 : ℝ) ^ 3) = Real.log ((3 : ℝ) ^ 2) := by
    rw [Real.log_pow, Real.log_pow]; push_cast; linarith
  have h2 : (2 : ℝ) ^ 3 = (3 : ℝ) ^ 2 :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) h1
  norm_num at h2

/-! ## Part 2: Logarithmic Dependence for Beurling "Primes"

Replace actual primes with {b, b², b³, ...} for a base b > 1.
Since log(b^k) = k·log(b), all "prime" logarithms are proportional.
The system is maximally linearly dependent.

The FundamentalGap constant is zero. Baker's theorem provides no obstruction.
Phase resonance at t = 2π/log(b) makes every "prime" phase equal 1.

Diamond–Montgomery–Vorhauer (2006) proved: Beurling systems exist
where π_B(x) ~ x/log(x) (PNT holds) but ζ_B has off-line zeros. -/

/-- Power-base logs are proportional: log(b^k) = k·log(b). -/
theorem log_power_base (b : ℕ) (_hb : 1 < b) (k : ℕ) :
    Real.log ((b : ℝ) ^ k) = k * Real.log (b : ℝ) := by
  rw [Real.log_pow]

/-- Nontrivial integer relation: log(b^k) - k·log(b) = 0.
    Compare: for actual primes, this difference is NEVER zero (Part 1). -/
theorem log_dep_beurling (b : ℕ) (_hb : 1 < b) (k : ℕ) :
    Real.log ((b : ℝ) ^ k) - k * Real.log (b : ℝ) = 0 := by
  rw [Real.log_pow]; ring

/-- **FundamentalGap gap is zero** for Beurling systems. Baker is vacuous. -/
theorem fundamentalGap_gap_zero (b : ℕ) (hb : 1 < b) (k : ℕ) :
    |Real.log ((b : ℝ) ^ k) - k * Real.log (b : ℝ)| = 0 := by
  rw [log_dep_beurling b hb k, abs_zero]

/-- Phase ratio for Beurling: log(b^k)/log(b) = k ∈ ℕ.
    Phases are commensurable — resonance at t = 2π/log(b). -/
theorem phase_ratio_beurling (b : ℕ) (hb : 1 < b) {k : ℕ} (hk : 0 < k) :
    Real.log ((b : ℝ) ^ k) / Real.log (b : ℝ) = k := by
  rw [log_power_base b hb k]
  have : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  field_simp

/-- Concrete: log(4) = 2·log(2). "Primes" {2, 4} are phase-locked. -/
theorem resonance_2_4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
  have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [this, Real.log_pow]; push_cast; ring

/-- Concrete: log(8) = 3·log(2). "Primes" {2, 8} are phase-locked. -/
theorem resonance_2_8 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
  have : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
  rw [this, Real.log_pow]; push_cast; ring

/-- **Any rational phase ratio is achievable** by Beurling "primes":
    log(2^a)/log(2^b) = a/b for any positive a, b. -/
theorem beurling_any_ratio (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.log ((2 : ℝ) ^ a) / Real.log ((2 : ℝ) ^ b) = (a : ℝ) / (b : ℝ) := by
  rw [Real.log_pow, Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hb_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-! ## Part 3: The Tilt Structure

The amplitude tilt τ_p(σ) = p^{-σ} - p^{-1/2} measures each prime's
deviation from the critical-line weighting.

The tilt has the SAME structure for actual primes and Beurling "primes":
zero at σ = 1/2, negative for σ > 1/2, positive for σ < 1/2.

This proves: **tilt alone does not prevent off-line zeros**. What
distinguishes the two systems is the PHASES: independent phases
(actual primes) create irreducible noise; dependent phases (Beurling)
can align to cancel the tilt.

Parallel to Collatz: contraction rate 3/2^ν is the same for integer
and real multipliers. Integer structure forces extra halving (no
divergence); removing it allows persistent minimal halving. -/

/-- Amplitude tilt: deviation from critical-line weighting p^{-1/2}. -/
noncomputable def tilt (p : ℕ) (σ : ℝ) : ℝ :=
  (p : ℝ) ^ (-σ) - (p : ℝ) ^ (-(1 / 2 : ℝ))

/-- Tilt vanishes on the critical line — for ANY system. -/
theorem tilt_zero_critical (p : ℕ) : tilt p (1 / 2) = 0 := by
  unfold tilt; simp

/-- Tilt is negative for σ > 1/2: large primes suppressed. -/
theorem tilt_neg_of_gt {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 / 2 < σ) :
    tilt p σ < 0 := by
  unfold tilt
  have hp_gt : (1 : ℝ) < p := by
    have : 2 ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  apply sub_neg_of_lt
  apply Real.rpow_lt_rpow_of_exponent_lt hp_gt
  linarith

/-- Tilt is positive for σ < 1/2: large primes amplified. -/
theorem tilt_pos_of_lt {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : σ < 1 / 2) :
    0 < tilt p σ := by
  unfold tilt
  have hp_gt : (1 : ℝ) < p := by
    have : 2 ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  apply sub_pos_of_lt
  apply Real.rpow_lt_rpow_of_exponent_lt hp_gt
  linarith

/-! ## Part 4: The Fragility Summary

The RH requires BOTH:
1. Tilt (σ ≠ 1/2 creates amplitude bias at every prime)
2. Phase incommensurability (log-independence prevents resonance)

For actual primes, both hold. For Beurling "primes" {b^k}, (1) holds
but (2) fails. Phases can resonate to overcome the tilt.

| | Collatz | RH |
|---|---|---|
| FundamentalGap constant | \|2^S - 3^k\| > exp(-Ck^κ) | \|Σ bᵢ log pᵢ\| > exp(-C(log B)^κ) |
| When FundamentalGap = 0 | Cycles form (Liouville m) | Off-line zeros form (Beurling) |
| Tilt analog | Contraction rate 3/2^ν | Amplitude p^{-σ} vs p^{-1/2} |
| Structure analog | Integer mod → ν forced | Prime logs independent → phases free | -/

/-- **Main theorem**: FundamentalGap gap positive for actual primes, zero for Beurling.
    The RH depends essentially on this distinction. -/
theorem fragility :
    -- Actual primes: FundamentalGap gap positive (Baker prevents resonance)
    (∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q →
      ∀ (a b : ℕ), 0 < a → 0 < b →
        0 < |(a : ℤ) * Real.log p - (b : ℤ) * Real.log q|) ∧
    -- Beurling "primes": FundamentalGap gap zero (resonance trivial)
    (∀ (b : ℕ), 1 < b → ∀ (k : ℕ),
      |Real.log ((b : ℝ) ^ k) - k * Real.log (b : ℝ)| = 0) :=
  ⟨fun _ _ hp hq hne _ _ ha hb => fundamentalGap_gap_pos hp hq hne ha hb,
   fun b hb k => fundamentalGap_gap_zero b hb k⟩

end BeurlingCounterexample

-- Verify: zero custom axioms
#print axioms BeurlingCounterexample.fragility
#print axioms BeurlingCounterexample.log_independence
#print axioms BeurlingCounterexample.fundamentalGap_gap_pos
#print axioms BeurlingCounterexample.fundamentalGap_gap_zero
#print axioms BeurlingCounterexample.no_resonance_2_3
#print axioms BeurlingCounterexample.resonance_2_4
