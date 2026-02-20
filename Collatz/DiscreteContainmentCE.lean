/-
  DiscreteContainmentCE.lean — Counterexample to the Three-Pillar Framework
  ==========================================================================

  PROVES: the `discrete_containment` axiom is equivalent to bare strip
  nonvanishing — the three pillar hypotheses are tautologically true in
  the region of interest and carry zero mathematical content.

  The three hypotheses of `discrete_containment`:
  1. All finite sub-products nonzero  — TRUE for Re(s) > 0 (each factor nonzero)
  2. Energy convergence               — TRUE for σ > 1/2 (Nat.Primes.summable_rpow)
  3. Log independence                  — TRUE unconditionally (unique factorization)

  Therefore `discrete_containment` reduces to:
    ∀ s, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0
  which is RH for the strip, with no content from the pillars.

  This file also shows why: the pillars describe PROPERTIES OF THE PRIMES,
  which are fixed. They don't vary with s, and they don't distinguish ζ from
  other Euler products over the same primes. A generalized Euler product
  ∏_p (1 - c_p · p^{-s})⁻¹ with |c_p| ≤ 1 satisfies all three pillar
  analogs, but different choices of c_p give different zero sets.

  The Beurling counterexample shows pillar 3 is NECESSARY (for systems
  where it fails, zeros appear). But necessity ≠ sufficiency.

  Zero custom axioms in this file (only references DiscreteContainment).
-/
import Collatz.DiscreteContainment

open scoped BigOperators

namespace DiscreteContainmentCE

/-! ## Part 1: The Three Hypotheses Are Tautologically True

Each hypothesis of `discrete_containment` is unconditionally satisfied
in the strip 1/2 < Re(s) < 1. We prove this explicitly. -/

/-- Hypothesis 1 is always true: finite Euler products are nonzero for Re(s) > 0.
    In the strip 1/2 < σ < 1, we have σ > 0, so this is immediate. -/
theorem hyp1_always_holds (s : ℂ) (hσ : 1 / 2 < s.re) :
    ∀ N : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.range N),
      (1 - (p : ℂ) ^ (-s)) ≠ 0 :=
  fun N => DiscreteContainment.finite_euler_product_ne_zero N (by linarith)

/-- Hypothesis 2 is always true: energy converges for σ > 1/2. -/
theorem hyp2_always_holds (s : ℂ) (hσ : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * s.re)) :=
  PrimeBranching.energy_convergence hσ

/-- Hypothesis 3 is always true: log independence is a fact about primes,
    not about s. It holds unconditionally (unique factorization). -/
theorem hyp3_always_holds :
    ∀ (n : ℕ) (ps : Fin n → ℕ) (_ : ∀ i, Nat.Prime (ps i))
      (_ : Function.Injective ps) (cs : Fin n → ℤ) (_ : cs ≠ 0),
      ∑ i, cs i * Real.log (ps i) ≠ 0 :=
  fun _ _ hp hinj _ hcs => PrimeBranching.log_primes_ne_zero hp hinj hcs

/-! ## Part 2: The Equivalence

`discrete_containment` is logically equivalent to bare strip nonvanishing.
The three-pillar dress-up adds zero content. -/

/-- Bare strip nonvanishing: ζ(s) ≠ 0 for 1/2 < Re(s) < 1.
    This is what `discrete_containment` actually says. -/
def StripNonvanishing : Prop :=
  ∀ (s : ℂ), 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- The three-pillar formulation (matching `discrete_containment`'s type). -/
def ThreePillarNonvanishing : Prop :=
  ∀ (s : ℂ), 1 / 2 < s.re → s.re < 1 →
    (∀ N : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.range N),
      (1 - (p : ℂ) ^ (-s)) ≠ 0) →
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * s.re)) →
    (∀ (n : ℕ) (ps : Fin n → ℕ) (_ : ∀ i, Nat.Prime (ps i))
      (_ : Function.Injective ps) (cs : Fin n → ℤ) (_ : cs ≠ 0),
      ∑ i, cs i * Real.log (ps i) ≠ 0) →
    riemannZeta s ≠ 0

/-- **The three-pillar formulation is equivalent to bare strip nonvanishing.**
    The hypotheses are vacuous — they're always true in the strip.
    PROVED: zero custom axioms. -/
theorem three_pillars_are_vacuous : StripNonvanishing ↔ ThreePillarNonvanishing := by
  constructor
  · -- Forward: bare → three-pillar (trivially, ignore the hypotheses)
    intro h s hσ hσ1 _ _ _
    exact h s hσ hσ1
  · -- Backward: three-pillar → bare (feed in the always-true hypotheses)
    intro h s hσ hσ1
    exact h s hσ hσ1
      (hyp1_always_holds s hσ)
      (hyp2_always_holds s hσ)
      hyp3_always_holds

/-! ## Part 3: Why the Framework Fails

The three pillars describe PROPERTIES OF THE PRIMES:
- Pillar 1: primes are > 1, so each p^{-s} has norm < 1
- Pillar 2: primes grow fast enough that Σ p^{-2σ} < ∞ for σ > 1/2
- Pillar 3: primes have unique factorization

These are NUMBER-THEORETIC CONSTANTS — they don't depend on s, and they
don't distinguish ζ from any other Euler product over the same primes.

A generalized Euler product ∏_p (1 - c_p · p^{-s})⁻¹ with |c_p| ≤ 1
satisfies all three pillar analogs (the PRIMES are the same), but
different coefficient sequences c_p give different functions with
potentially different zero sets.

For ζ(s): c_p = 1 for all p.
For L(s,χ): c_p = χ(p) with |χ(p)| ≤ 1.
For random Euler products: c_p ∈ {±1} chosen randomly.

The three pillars can't see the coefficients. They only see the primes.
So they can't distinguish these functions. Since they might have different
zero sets, the pillars alone can't determine where zeros are.

The missing ingredient is the SPECIFIC MULTIPLICATIVE STRUCTURE of ζ:
the fact that c_p = 1 for all p, which gives ζ(s) = Σ n^{-s} (complete
multiplicativity with trivial character). This is not captured by any
of the three pillars. -/

/-- The three-pillar hypotheses hold for ANY s with Re(s) > 1/2.
    They carry no information about s.im and cannot constrain
    where ζ vanishes on vertical lines. -/
theorem pillars_independent_of_imaginary_part (σ : ℝ) (hσ : 1 / 2 < σ) :
    -- For ANY t, all three hypotheses are satisfied at σ + it
    ∀ t : ℝ,
    let s : ℂ := ⟨σ, t⟩
    (∀ N : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.range N),
      (1 - (p : ℂ) ^ (-s)) ≠ 0) ∧
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * s.re)) ∧
    (∀ (n : ℕ) (ps : Fin n → ℕ) (_ : ∀ i, Nat.Prime (ps i))
      (_ : Function.Injective ps) (cs : Fin n → ℤ) (_ : cs ≠ 0),
      ∑ i, cs i * Real.log (ps i) ≠ 0) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · exact hyp1_always_holds ⟨σ, t⟩ (by show 1 / 2 < (⟨σ, t⟩ : ℂ).re; simp; linarith)
  · exact hyp2_always_holds ⟨σ, t⟩ (by show 1 / 2 < (⟨σ, t⟩ : ℂ).re; simp; linarith)
  · exact hyp3_always_holds

/-! ## Part 4: What Would Make the Pillars Non-Vacuous

For the framework to have content, the hypotheses must DEPEND on s
(especially s.im) in a way that's NOT always true. Candidates:

1. **Conditional convergence of Σ_p p^{-s}**: the prime zeta function
   P(s) = Σ_p p^{-s} converges conditionally for σ > 1/2 iff PNT holds
   with strong enough error term. This depends on both σ AND t (through
   cancellation in the oscillatory sum). But P(s) diverges for σ ≤ 1
   regardless of t, so it doesn't help in the strip.

2. **Non-concentration of partial Euler products**: require that
   |∏_{p ≤ N} (1 - p^{-s})| stays bounded away from 0 and ∞ as N → ∞.
   This is NOT always true — it's essentially equivalent to ζ(s) ≠ 0.

3. **Equidistribution of (t·log p mod 2π)**: the orbit on T^∞ is
   equidistributed for all t ≠ 0 (by pillar 3 + Kronecker-Weyl).
   But equidistribution doesn't prevent hitting measure-zero sets.

None of these give a clean, non-vacuous reformulation.

The honest conclusion: ζ(s) ≠ 0 in the strip is a statement about the
ANALYTIC CONTINUATION of the Euler product, not about the Euler product
itself. The Euler product diverges in the strip. The three pillars
describe convergence properties — they can't reach the continuation. -/

end DiscreteContainmentCE

-- Zero custom axioms in the counterexample analysis
#print axioms DiscreteContainmentCE.three_pillars_are_vacuous
#print axioms DiscreteContainmentCE.pillars_independent_of_imaginary_part
#print axioms DiscreteContainmentCE.hyp1_always_holds
#print axioms DiscreteContainmentCE.hyp2_always_holds
#print axioms DiscreteContainmentCE.hyp3_always_holds
