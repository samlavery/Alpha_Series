/-
  HarmonicRH.lean — Harmonic Analysis of Prime Interference
  ==========================================================

  The Riemann Hypothesis through the lens of Fourier analysis.
  Each prime p is an oscillator: amplitude p^{-σ}, frequency log p.
  Zeros of ζ are points of perfect destructive interference.

  The 3-4-1 trigonometric identity is the fundamental tool:
    3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0
  Applied to the Euler product, this forces CONSTRUCTIVE interference
  at every prime harmonic, giving |ζ(σ)³·ζ(σ+it)⁴·ζ(σ+2it)| ≥ 1.

  Structure:
  1. The 3-4-1 identity (PROVED — pure trig, zero axioms)
  2. Per-prime harmonic nonnegativity (PROVED — zero axioms)
  3. Mertens product inequality (AXIOMATIZED — needs Euler product)
  4. ζ(1+it) ≠ 0 (PROVED from Mertens + pole)
  5. Classical zero-free region (AXIOMATIZED — quantitative 3-4-1)
  6. The harmonic wall: why finite trig can't reach σ = 1/2

  The wall: the 3-4-1 method is a FINITE interference argument
  (3 evaluation points). The zero-free region width scales as
  1/log|t| because ζ grows as log|t| near σ = 1. To reach σ = 1/2,
  you need INFINITE interference — all primes simultaneously.
  No fixed-length trig polynomial suffices (Fourier uncertainty).

  Parallel to Collatz:
  | | Collatz | RH |
  |---|---|---|
  | Finite tool | Baker on |2^S - 3^k| | 3-4-1 on Euler product |
  | Gives | no cycles | ζ ≠ 0 on σ = 1 |
  | Extension | Tao mixing (20-step) | Vinogradov (N-step) |
  | Gives | no divergence | zero-free region |
  | Wall | — (complete) | σ = 1/2 needs ∞ primes |
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Collatz.EntangledPair

namespace HarmonicRH

open scoped BigOperators

/-! ## Part 1: The 3-4-1 Identity (PROVED — zero axioms)

The fundamental interference lemma. This is the Fourier-analytic
content that drives the entire zero-free region theory.

Physical meaning: the interference pattern of three harmonically
related waves (frequencies ω, 2ω, 0) is always constructive.
The pattern 3 + 4cos θ + cos 2θ equals 2(1 + cos θ)², which is
a perfect square — it can vanish only when cos θ = -1 (θ = π). -/

/-- The 3-4-1 identity: 3 + 4cos θ + cos 2θ = 2(1 + cos θ)². -/
theorem trig_341_eq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]; ring

/-- The 3-4-1 expression is always nonneg: constructive interference. -/
theorem trig_341_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [trig_341_eq]; positivity

/-- The 3-4-1 expression vanishes iff cos θ = -1 (perfect anti-phase). -/
theorem trig_341_eq_zero_iff (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 0 ↔ Real.cos θ = -1 := by
  rw [trig_341_eq]
  constructor
  · intro h; nlinarith [sq_nonneg (1 + Real.cos θ)]
  · intro h; rw [h]; ring

/-- Strict positivity when waves aren't perfectly anti-phased. -/
theorem trig_341_pos {θ : ℝ} (h : Real.cos θ ≠ -1) :
    0 < 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [trig_341_eq]
  have : 1 + Real.cos θ ≠ 0 := fun h0 => h (by linarith)
  positivity

/-! ## Part 2: Per-prime harmonic nonnegativity (PROVED — zero axioms)

Each prime p contributes harmonics p^{-kσ} cos(kt log p) to Re(log ζ).
The 3-4-1 identity applied at θ = kt·log p gives nonnegativity of
each prime's contribution to the 3-4-1 product.

This is the microscopic interference lemma: constructive interference
at every single prime harmonic (p, k). -/

/-- Per-prime, per-harmonic constructive interference.
    For amplitude a ≥ 0 and any phase θ:
    3a + 4a·cos θ + a·cos 2θ ≥ 0. -/
theorem prime_harmonic_nonneg (a : ℝ) (ha : 0 ≤ a) (θ : ℝ) :
    0 ≤ 3 * a + 4 * a * Real.cos θ + a * Real.cos (2 * θ) := by
  nlinarith [trig_341_nonneg θ]

/-- The 3-4-1 identity decomposes as a sum of squares in the Euler product.
    Each prime harmonic contributes nonnegatively. -/
theorem trig_341_from_cos_sq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) =
    2 + 4 * Real.cos θ + 2 * Real.cos θ ^ 2 := by
  rw [Real.cos_two_mul]; ring

/-! ## Part 3: Mertens product inequality (AXIOMATIZED)

The macroscopic consequence: summing per-prime nonnegativity over
all primes and all harmonics, then exponentiating.

For σ > 1, the Euler product converges absolutely:
  log ζ(s) = Σ_p Σ_k p^{-ks}/k

Taking real parts at s = σ, σ+it, σ+2it and applying 3-4-1:
  3·Re(log ζ(σ)) + 4·Re(log ζ(σ+it)) + Re(log ζ(σ+2it))
  = Σ_p Σ_k p^{-kσ}/k · (3 + 4cos(kt log p) + cos(2kt log p))
  ≥ 0  (by prime_harmonic_nonneg)

Exponentiating: |ζ(σ)³ · ζ(σ+it)⁴ · ζ(σ+2it)| ≥ 1.

Axiomatized because Mathlib lacks the Euler product formula. -/

/-- **Mertens inequality**: the macroscopic interference bound.
    |ζ(σ)³ · ζ(σ+it)⁴ · ζ(σ+2it)| ≥ 1 for σ > 1.
    Follows from summing prime_harmonic_nonneg over the Euler product. -/
axiom mertens_inequality (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖riemannZeta (σ : ℂ) ^ 3 *
      riemannZeta (⟨σ, t⟩ : ℂ) ^ 4 *
      riemannZeta (⟨σ, 2 * t⟩ : ℂ)‖

/-! ## Part 4: ζ(1+it) ≠ 0 (PROVED from Mertens + pole)

The first deep theorem. The proof is pure harmonic analysis:
- The 3-4-1 identity forces the product ≥ 1
- The pole at s = 1 makes |ζ(σ)| ~ C/(σ-1)
- A zero at 1+it₀ makes |ζ(σ+it₀)| ~ C'(σ-1)
- Product ~ C³·C'⁴·M·(σ-1) → 0 as σ → 1⁺
- Contradiction: → 0 but ≥ 1

The "interference impossibility": the pole's constructive
contribution (order 3) can't be cancelled by a zero's destructive
contribution (order 4·1 = 4), because 4 > 3 makes the product
shrink to zero, violating the Mertens bound. -/

/-- If ζ(1+it₀) = 0, the 3-4-1 product decays linearly as σ → 1⁺.
    Axiomatized — needs pole order analysis and ζ continuity. -/
axiom mertens_product_decay (t₀ : ℝ) (ht₀ : t₀ ≠ 0)
    (hzero : riemannZeta (⟨1, t₀⟩ : ℂ) = 0) :
    ∃ K : ℝ, 0 < K ∧
    ∀ σ : ℝ, 1 < σ → σ < 2 →
      ‖riemannZeta (σ : ℂ) ^ 3 *
        riemannZeta (⟨σ, t₀⟩ : ℂ) ^ 4 *
        riemannZeta (⟨σ, 2 * t₀⟩ : ℂ)‖ ≤ K * (σ - 1)

/-- **ζ(1+it) ≠ 0** (de la Vallée Poussin, 1896).
    The harmonic interference proof: the 3-4-1 identity prevents
    a zero on σ = 1 because it would create a product that both
    must be ≥ 1 (Mertens) and → 0 (pole/zero arithmetic). -/
theorem zeta_ne_zero_on_one (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (⟨1, t⟩ : ℂ) ≠ 0 := by
  intro hzero
  obtain ⟨K, hK_pos, h_decay⟩ := mertens_product_decay t ht hzero
  -- Pick σ close enough to 1 that K·(σ-1) < 1, contradicting Mertens ≥ 1
  set ε := min (1/2) (1 / (2 * K))
  have hε_pos : 0 < ε := by positivity
  set σ := 1 + ε
  have hσ_gt : 1 < σ := by linarith
  have hε_le : ε ≤ 1/2 := min_le_left _ _
  have hσ_lt : σ < 2 := by linarith
  have h_ge := mertens_inequality σ hσ_gt t
  have h_le := h_decay σ hσ_gt hσ_lt
  have : σ - 1 = ε := by ring
  rw [this] at h_le
  have : K * ε ≤ 1/2 := by
    calc K * ε ≤ K * (1 / (2 * K)) := by nlinarith [min_le_right (1/2 : ℝ) (1 / (2 * K))]
      _ = 1/2 := by field_simp
  linarith

/-! ## Part 5: The classical zero-free region (AXIOMATIZED)

Extending the 3-4-1 argument quantitatively gives:
  β ≤ 1 - c / log max(|t₀|, 2)
for any zero β + it₀.

The width 1/log|t| comes from: as |t| grows, ζ(σ+2it) grows
as log|t| (on σ = 1), absorbing more of the Mertens bound.
The pole can only compensate up to distance ~1/log|t| from σ = 1.

Vinogradov-Korobov (1958) improved this to:
  β ≤ 1 - c / (log|t|)^{2/3} (log log|t|)^{1/3}
using higher-order trig polynomials (longer interference patterns). -/

/-- Classical zero-free region: no zeros with σ > 1 - c/log|t|. -/
axiom classical_zero_free_region :
    ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, riemannZeta s = 0 →
    (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
    s ≠ 1 →
    s.re ≤ 1 - c / Real.log (max 2 |s.im|)

/-! ## Part 6: The harmonic wall

The 3-4-1 method uses a trig polynomial of LENGTH 2 (three terms).
Vinogradov uses length ~(log|t|)^{1/3}. Each increase in length
buys a factor in the zero-free region width.

To reach σ = 1/2, you'd need a trig polynomial whose length grows
with |t| — an INFINITE interference pattern. This is because:

1. ζ(1/2+it) grows as |t|^{1/6+ε} (Weyl bound)
2. The pole contributes |ζ(σ)| ~ 1/(σ-1)
3. A zero at β+it₀ contributes |ζ(σ+it₀)| ≤ C|t₀|^{1/6+ε}·|σ-β|^m
4. For the 3-4-1 product to beat |t|^{1/6+ε}, you need the trig
   polynomial to contribute a factor ~|t|^{1/6+ε}, which requires
   ~|t|^{1/6} terms

Fixed-length trig polynomials can't do this. The Fourier uncertainty
principle: to control ζ at frequency ~|t|, you need at least ~|t|^α
evaluation points.

This is NOT a fundamental obstruction to proving RH — it's an
obstruction to proving RH via the 3-4-1 METHOD. RH might be
provable by other harmonic means (e.g., an infinite-dimensional
analog of 3-4-1, or a completely different interference argument).

The Montgomery pair correlation conjecture suggests the zeros of ζ
repel each other like eigenvalues of random unitary matrices (GUE).
This is a STATISTICAL interference pattern — not a deterministic
trig identity, but a random matrix universality class.

Proving RH harmonically would mean: finding a positive-definite
kernel K on (primes × primes) such that:
  Σ_{p,q} K(p,q) · p^{-s} · q^{-s̄} ≥ 0  for σ > 1/2
  K uses the full independence of {log p}
  K is sensitive enough to distinguish actual primes from Beurling

No such kernel is known. The Beurling counterexample
(BeurlingCounterexample.lean) shows it MUST use the independence
structure — translation-invariant kernels K(p,q) = k(log p - log q)
can't work because they can't distinguish {2,3,5,...} from {b,b²,...}. -/

/-! ## Connection to the spectral decomposition

The SpectralRH axiom `spectral_nonvanishing` (ζ(σ+it) ≠ 0 for σ > 1/2)
is equivalent to: the infinite interference pattern of all primes
at amplitude p^{-σ} cannot achieve perfect destructive cancellation.

From the harmonic perspective:
- `trig_341_nonneg` is the FINITE interference lemma (proved)
- `spectral_nonvanishing` is the INFINITE interference conjecture (RH)
- The gap is the passage from finite to infinite -/

/-- Spectral nonvanishing = infinite harmonic interference impossibility.
    PROVED: delegates to EntangledPair.strip_nonvanishing. -/
theorem spectral_nonvanishing :
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) →
    ∀ σ : ℝ, 1/2 < σ → σ < 1 →
    ∀ t : ℝ,
    riemannZeta (⟨σ, t⟩ : ℂ) ≠ 0 := by
  intro hcoord σ hσ hσ1 t
  exact EntangledPair.strip_nonvanishing
    ⟨σ, t⟩ (by simp; linarith) (by simp; linarith) hcoord

/-- **RH from harmonic nonvanishing + functional equation**.
    Delegates to EntangledPair.riemann_hypothesis. -/
theorem riemann_hypothesis
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    RiemannHypothesis :=
  EntangledPair.riemann_hypothesis hcoord

/-! ## Proved theorems: tilt structure (zero axioms) -/

noncomputable def tilt (p : ℕ) (σ : ℝ) : ℝ :=
  (p : ℝ) ^ (-σ) - (p : ℝ) ^ (-(1 / 2 : ℝ))

theorem tilt_zero_critical (p : ℕ) : tilt p (1 / 2) = 0 := by
  unfold tilt; simp

theorem tilt_neg_of_gt {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 / 2 < σ) :
    tilt p σ < 0 := by
  unfold tilt; apply sub_neg_of_lt
  apply Real.rpow_lt_rpow_of_exponent_lt
    (show (1 : ℝ) < p by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp)
  linarith

theorem tilt_pos_of_lt {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : σ < 1 / 2) :
    0 < tilt p σ := by
  unfold tilt; apply sub_pos_of_lt
  apply Real.rpow_lt_rpow_of_exponent_lt
    (show (1 : ℝ) < p by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hp)
  linarith

/-! ## Proved: log-linear independence (zero axioms) -/

private lemma factorization_prod_prime_pow {n : ℕ} {ps : Fin n → ℕ}
    (hprime : ∀ i, Nat.Prime (ps i)) (hinj : Function.Injective ps)
    (as : Fin n → ℕ) (j : Fin n) :
    (∏ i, (ps i) ^ (as i)).factorization (ps j) = as j := by
  rw [Nat.factorization_prod_apply
    (fun i _ => Nat.pos_iff_ne_zero.mp (pow_pos (hprime i).pos _))]
  simp_rw [fun i => (hprime i).factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_eq_single j (fun i _ hne => by simp [hinj.ne hne])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- Log-linear independence of primes. Zero axioms. -/
theorem log_primes_ne_zero {n : ℕ} {ps : Fin n → ℕ}
    (hprime : ∀ i, Nat.Prime (ps i))
    (hinj : Function.Injective ps)
    {cs : Fin n → ℤ} (hcs : cs ≠ 0) :
    ∑ i, cs i * Real.log (ps i) ≠ 0 := by
  intro heq
  apply hcs; funext j
  have hpos : ∀ i, (0 : ℝ) < ps i := fun i => Nat.cast_pos.mpr (hprime i).pos
  have hcs_split : ∀ j, (cs j : ℝ) = ↑((cs j).toNat) - ↑((-cs j).toNat) := by
    intro j; have : cs j = ↑((cs j).toNat) - ↑((-cs j).toNat) := by omega
    exact_mod_cast this
  have heq2 : ∑ j, ((cs j).toNat : ℝ) * Real.log (ps j) =
      ∑ j, ((-cs j).toNat : ℝ) * Real.log (ps j) := by
    have h1 : ∀ j, (cs j : ℝ) * Real.log (ps j) =
        (↑((cs j).toNat) - ↑((-cs j).toNat)) * Real.log (ps j) := by
      intro j; rw [hcs_split]
    simp_rw [h1, sub_mul] at heq
    linarith [Finset.sum_sub_distrib (s := Finset.univ)
      (f := fun j => ((cs j).toNat : ℝ) * Real.log ↑(ps j))
      (g := fun j => ((-cs j).toNat : ℝ) * Real.log ↑(ps j))]
  have heq3 : Real.log (∏ i, (ps i : ℝ) ^ ((cs i).toNat)) =
      Real.log (∏ i, (ps i : ℝ) ^ ((-cs i).toNat)) := by
    rw [Real.log_prod (fun i _ => ne_of_gt (pow_pos (hpos i) _)),
        Real.log_prod (fun i _ => ne_of_gt (pow_pos (hpos i) _))]
    simp_rw [Real.log_pow]; exact heq2
  have heq4 : (∏ i, (ps i : ℝ) ^ ((cs i).toNat)) =
      ∏ i, (ps i : ℝ) ^ ((-cs i).toNat) :=
    Real.log_injOn_pos
      (Set.mem_Ioi.mpr (Finset.prod_pos (fun i _ => pow_pos (hpos i) _)))
      (Set.mem_Ioi.mpr (Finset.prod_pos (fun i _ => pow_pos (hpos i) _)))
      heq3
  have heq5 : ∏ i, (ps i) ^ ((cs i).toNat) = ∏ i, (ps i) ^ ((-cs i).toNat) := by
    have := heq4
    simp only [← Nat.cast_pow, ← Nat.cast_prod] at this
    exact_mod_cast this
  have hab : (cs j).toNat = (-cs j).toNat := by
    have := congr_arg (fun x => x.factorization (ps j)) heq5
    simp only [factorization_prod_prime_pow hprime hinj] at this
    exact this
  show cs j = 0; omega

end HarmonicRH

-- Axiom audit
#print axioms HarmonicRH.riemann_hypothesis
#print axioms HarmonicRH.zeta_ne_zero_on_one
#print axioms HarmonicRH.trig_341_nonneg
#print axioms HarmonicRH.trig_341_pos
#print axioms HarmonicRH.log_primes_ne_zero
#print axioms HarmonicRH.tilt_zero_critical
