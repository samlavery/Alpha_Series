/-
  FloorTail.lean — Floor-Tail Decomposition of the Euler Product
  ===============================================================

  The Euler product ∏_p (1 - p^{-s})⁻¹ decomposes as:

    ζ(s) = FLOOR(s, F) × TAIL(s, F)

  where FLOOR = ∏_{p∈F} (1 - p^{-s})⁻¹  (finite product, small primes)
        TAIL  = ∏_{p∉F} (1 - p^{-s})⁻¹  (infinite product, large primes)

  What is proved here (standard axioms only):

    1. Euler factor upper bound: ‖1 - p^{-s}‖ ≤ 1 + p^{-σ}
    2. Euler factor lower bound: ‖1 - p^{-s}‖ ≥ 1 - p^{-σ}  (for σ > 0, so p^{-σ} < 1)
    3. Inverse factor lower bound: (1 + p^{-σ})⁻¹ ≤ ‖(1 - p^{-s})⁻¹‖
    4. Finite floor lower bound: ‖FLOOR(s, F)‖ ≥ ∏_{p∈F} (1 + p^{-σ})⁻¹ > 0

  What is axiomatized (open):

    5. tail_lower_bound — the infinite TAIL product is bounded below.
       Mathematical content: T₁(t) = Σ_{p∉F} p^{-σ} cos(t log p) ≥ -B.
       Equivalent to RH for 1/2 < σ < 1. See TailBound.lean.

    6. anti_correlation_principle — floor and tail don't simultaneously minimize.
       Supported by computational experiments (ratio ≈ 1.7, R² = 0.91).
       Conjectural. Would simplify the tail_lower_bound argument.

  Computational evidence (wobble_experiment5.py, FOOTNOTES.md):
    - corr(log|FLOOR|, log|TAIL|) ≈ -0.05
    - min(FLOOR × TAIL) / [min(FLOOR) · min(TAIL)] ≈ 1.7
    - Gap saturates at P ≈ 100 (~27 primes); large primes contribute < 1% each
    - Baker-Euler power law: log(Euler gap) ≈ 0.14·log(Baker gap) - 0.52 (R² = 0.91)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Collatz.PrimeBranching

open Complex Finset

namespace FloorTail

/-! ## Section 1: Euler Factor Bounds (PROVED, standard axioms)

Each Euler factor satisfies:

  1 - p^{-σ}  ≤  |1 - p^{-s}|  ≤  1 + p^{-σ}

from the triangle inequality. Inverting gives floor and ceiling for the
Euler product factors. -/

/-- Upper bound on |1 - p^{-s}|: at most 1 + p^{-σ}. -/
theorem euler_factor_norm_upper {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : 0 < s.re) : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-s.re) := by
  calc ‖1 - (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le 1 _
    _ = 1 + (p : ℝ) ^ (-s.re) := by
        rw [norm_one, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]

/-- Lower bound on |1 - p^{-s}|: at least 1 - p^{-σ}. -/
theorem euler_factor_norm_lower {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : 0 < s.re) : 1 - (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have key : ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-s)‖ ≤ ‖1 - (p : ℂ) ^ (-s)‖ :=
    norm_sub_norm_le 1 _
  rw [norm_one, Complex.norm_natCast_cpow_of_pos hp.pos] at key
  exact_mod_cast key

/-- Lower bound on |(1 - p^{-s})⁻¹|: at least 1/(1 + p^{-σ}). -/
theorem euler_factor_inv_lower {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : 0 < s.re) :
    (1 + (p : ℝ) ^ (-s.re))⁻¹ ≤ ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
  rw [norm_inv]
  have hne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := PrimeBranching.euler_factor_ne_zero hp hs
  have hpos : 0 < ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := norm_pos_iff.mpr hne
  exact inv_anti₀ hpos (euler_factor_norm_upper hp hs)

/-! ## Section 2: Finite Product Floor Bound (PROVED, standard axioms)

The FLOOR = ∏_{p∈F} |(1 - p^{-s})|⁻¹ is bounded below by ∏_{p∈F} 1/(1 + p^{-σ}).
This is a finite product of positive terms, hence unconditionally positive. -/

/-- The floor: finite product over a set of primes. -/
noncomputable def floor (F : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ F, (1 - (p : ℂ) ^ (-s))⁻¹

/-- Floor is nonzero when all primes in F are prime and Re(s) > 0. -/
theorem floor_ne_zero (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p)
    {s : ℂ} (hs : 0 < s.re) : floor F s ≠ 0 := by
  simp only [floor]
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    PrimeBranching.euler_factor_inv_ne_zero (hF p hp) hs

/-- The floor lower bound: ‖FLOOR‖ ≥ ∏_{p∈F} 1/(1 + p^{-σ}). -/
theorem floor_lower_bound (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p)
    {s : ℂ} (hs : 0 < s.re) :
    ∏ p ∈ F, (1 + (p : ℝ) ^ (-s.re))⁻¹ ≤ ‖floor F s‖ := by
  rw [floor, Complex.norm_prod]
  apply Finset.prod_le_prod
  · intro p _; positivity
  · intro p hp
    exact euler_factor_inv_lower (hF p hp) hs

/-- The floor lower bound is strictly positive. -/
theorem floor_lower_bound_pos (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p)
    {s : ℂ} (hs : 0 < s.re) :
    0 < ∏ p ∈ F, (1 + (p : ℝ) ^ (-s.re))⁻¹ := by
  apply Finset.prod_pos
  intro p _; positivity

/-! ## Section 3: The Open Axioms

These two axioms are the new mathematical content. The anti-correlation
principle is supported by computational experiments. The tail lower bound
is equivalent to RH for 1/2 < σ < 1. See TailBound.lean for the full
analysis and the connection to `residual_exponential_sum_bounded`. -/

/-- Tail lower bound: the infinite product over large primes is bounded below.
    For σ > 1/2 and any cutoff P, there exists C > 0 such that the infinite
    product over primes p > P is always ≥ C.

    Equivalent to `TailBound.residual_exponential_sum_bounded` via the
    Euler product log-expansion (valid for σ > 1; extension to σ > 1/2
    is the mathematical gap — see TailBound.lean §4-5). -/
axiom tail_lower_bound : ∀ (σ : ℝ), 1/2 < σ → ∃ P : ℕ, ∃ C : ℝ, 0 < C ∧
  ∀ (t : ℝ), C ≤ ∏ᶠ (p : {q : Nat.Primes | P < (q : ℕ)}),
    ‖(1 - ((p : ℕ) : ℂ) ^ (-(⟨σ, t⟩ : ℂ)))⁻¹‖

/-- Anti-correlation principle: when the tail dips, the floor compensates.
    Experimental evidence: corr(log|FLOOR|, log|TAIL|) ≈ -0.05,
    min(FLOOR × TAIL) ≥ 1.7 × min(FLOOR) × min(TAIL).
    Conjectural — not yet proved. Subsumes tail_lower_bound if true. -/
axiom anti_correlation_principle : ∀ (σ : ℝ), 1/2 < σ →
  ∃ P : ℕ, ∃ R : ℝ, 1 < R ∧ ∀ (t : ℝ),
    R * (⨅ t' : ℝ, ‖floor (Finset.filter (· ≤ P) (Finset.range (P + 1))) ⟨σ, t'⟩‖) *
      (⨅ t' : ℝ, ∏ᶠ (p : {q : Nat.Primes | P < (q : ℕ)}),
        ‖(1 - ((p : ℕ) : ℂ) ^ (-(⟨σ, t'⟩ : ℂ)))⁻¹‖) ≤
    ‖floor (Finset.filter (· ≤ P) (Finset.range (P + 1))) ⟨σ, t⟩‖ *
      ∏ᶠ (p : {q : Nat.Primes | P < (q : ℕ)}),
        ‖(1 - ((p : ℕ) : ℂ) ^ (-(⟨σ, t⟩ : ℂ)))⁻¹‖

end FloorTail

/-! ## Axiom Audit

  `FloorTail.euler_factor_norm_upper`     : standard axioms only
  `FloorTail.euler_factor_norm_lower`     : standard axioms only
  `FloorTail.euler_factor_inv_lower`      : standard axioms only
  `FloorTail.floor_ne_zero`               : standard axioms only
  `FloorTail.floor_lower_bound`           : standard axioms only
  `FloorTail.floor_lower_bound_pos`       : standard axioms only
  `FloorTail.tail_lower_bound`            : custom axiom (≡ RH for σ > 1/2)
  `FloorTail.anti_correlation_principle`  : custom axiom (conjectural)
-/
