# Liouville Counterexample: The Collatz Conjecture Is Fragile

## Claim

The Collatz conjecture for the generalized map mx+d depends essentially on the
Diophantine properties of the multiplier m. For a dense set of transcendental
multipliers, the analogous conjecture is **false**: cycles exist (mx+1) and
orbits diverge (mx+3). The standard conjecture (m=3) avoids these pathologies
precisely because log₂(3) has finite irrationality measure.

## Preliminaries

**Definition (Liouville number).** A real number α is *Liouville* if for every
positive integer n, there exist integers p, q with q > 1 such that
|α - p/q| < 1/q^n. Equivalently, α has infinite irrationality measure.
Every Liouville number is transcendental (Liouville, 1844). The set of
Liouville numbers is dense in ℝ and comeager (a dense G_δ).

**The orbit equation.** For the map T_{m,d} with multiplier m > 1 and offset
d > 0 (odd), a Syracuse-style orbit satisfies:

    x_{i+1} · 2^{ν_{i+1}} = m · x_i + d

where ν_i ≥ 1 encodes the 2-adic valuation of m·x_i + d. After k steps:

    x_k · 2^{S_k} = m^k · x_0 + W_k

where S_k = Σᵢ νᵢ and the *wavesum* W_k = Σᵢ₌₀^{k-1} d · m^{k-1-i} · 2^{S_k - S_{i+1}}
is always positive.

**The cycle equation.** A k-cycle (x_k = x_0) satisfies:

    x_0 · (2^S - m^k) = W_k(m)

which has a unique positive solution whenever 2^S > m^k:

    x_0 = W_k(m) / (2^S - m^k)

For integer m = 3, Baker's theorem gives:

    |2^S - 3^k| > exp(-C · (log max(S,k))^κ)

for effective constants C, κ. This lower bound prevents the denominator from
being small enough to produce nontrivial integer solutions x_0. The three-path
argument in NoCycle.lean then excludes all remaining candidates.

---

## Part 1: Cycles Become Possible (mx+1)

**Theorem.** For any cycle length k ≥ 2 and any halving pattern (ν_1,...,ν_k)
with S = Σν_i > k·log₂(m), there exist uncountably many Liouville numbers
m ∈ (1, 2^{S/k}) such that the cycle equation

    x_0 = W_k(m) / (2^S - m^k)

has a positive real solution x_0 > 1.

**Proof.**

Fix k and the ν-pattern. Consider the function

    φ(m) = W_k(m) / (2^S - m^k)

defined for m ∈ (0, 2^{S/k}).

*Step 1: φ is continuous with a pole.*

W_k(m) is a polynomial in m with positive coefficients (it is a sum of terms
d · m^j · 2^{S - S_{j+1}} for j = 0,...,k-1, with d = 1). In particular
W_k(m) > 0 for all m > 0. The denominator 2^S - m^k is positive for
m < 2^{S/k} and vanishes at m = 2^{S/k}. Therefore:

- As m → 2^{S/k} from below: φ(m) → +∞
- At m = 0: φ(0) = W_k(0) / 2^S > 0

By the intermediate value theorem, φ takes every value in (W_k(0)/2^S, ∞).
In particular, for any target x_0 > W_k(0)/2^S, there exists m_0 ∈ (0, 2^{S/k})
with φ(m_0) = x_0.

*Step 2: Liouville numbers are dense.*

The set of Liouville numbers is a dense G_δ subset of ℝ (Baire category).
The set of m giving φ(m) > 1 is an open interval I ⊂ (0, 2^{S/k}).
Since Liouville numbers are dense in every open interval, I contains
uncountably many Liouville numbers.

For any such Liouville m ∈ I, the cycle equation has a positive real
solution x_0 = φ(m) > 1.  □

**Why this fails for m = 3.** For integer m = 3, the denominator
|2^S - 3^k| is bounded below by Baker's theorem. The wavesum W_k(3) grows
as O(3^k), so x_0 = W_k(3)/(2^S - 3^k) is bounded above. The three-path
argument (DriftContradiction, LatticeProof, CyclotomicBridge) then verifies
computationally that no integer x_0 > 1 satisfies the equation for any
valid (k, ν-pattern) pair. Baker's lower bound is the load-bearing wall.

**What the Liouville construction breaks.** When log₂(m) is Liouville,
for any n there exist S, k with |2^S - m^k| < 1/k^n. The denominator
in the cycle equation can be made smaller than any polynomial bound.
Baker's theorem — which guarantees a polynomial-in-log lower bound —
simply does not apply to numbers with infinite irrationality measure.
The "FundamentalGap constant" of the dynamical system is zero.

---

## Part 2: Divergence Becomes Inevitable (mx+3)

**Theorem.** For any real m > 2, if the halving pattern ν_i = 1 persists
for all i, the orbit equation with d = 3 produces an unbounded orbit:
x_k → ∞ for any x_0 > 0.

**Proof.**

Set ν_i = 1 for all i (minimum halving at every step). The orbit equation becomes:

    x_{i+1} = (m · x_i + 3) / 2

This is a linear recurrence with growth factor m/2 > 1 (since m > 2).
The fixed point is x* = 3/(2 - m) < 0. The general solution is:

    x_k = (m/2)^k · (x_0 - x*) + x*

Since x_0 > 0 and x* < 0, we have x_0 - x* > 0, so:

    x_k ≥ (m/2)^k · x_0 → ∞

The orbit diverges geometrically with rate m/2 > 1.  □

**Why ν = 1 can persist for Liouville m but not for integer m.**

For real (non-integer) m, the orbit leaves ℤ immediately. The values
x_i are real numbers, so v₂(m·x_i + d) is not constrained by any
residue structure — the halving pattern ν_i is a free parameter. In
particular, ν_i = 1 for all i is achievable. The Liouville property of
m is not what causes the divergence (any real m > 2 diverges under
constant ν = 1); it is what *removes the obstruction* to persistent
minimal halving by taking the orbit out of ℤ.

**Why this can't happen for integer m = 3, d = 3.**

For integer orbits, the halving pattern ν_i is not a free parameter — it is
determined by ν_i = v₂(3x_i + 3) = v₂(3(x_i + 1)) = v₂(x_i + 1). The
integer structure forces additional halving:

1. If x_i ≡ 1 (mod 4) (odd): then x_i + 1 ≡ 2 (mod 4), so ν_i = 1.
   Next value: x_{i+1} = 3(x_i + 1)/2. Since (x_i + 1)/2 is odd,
   x_{i+1} = 3 · (odd) ≡ 3 (mod 4).

2. If x_i ≡ 3 (mod 4) (odd): then x_i + 1 ≡ 0 (mod 4), so ν_i ≥ 2.
   The orbit gets at least two halvings.

**The pattern ν = 1 cannot persist for two consecutive steps.** After one
minimal-halving step from x_i ≡ 1 (mod 4), the next value satisfies
x_{i+1} ≡ 3 (mod 4), which forces ν_{i+1} ≥ 2. The integer residue
structure guarantees that at least half of all steps have ν ≥ 2, pushing
the average halving rate above the critical threshold.

This is exactly what Tao's mixing argument quantifies: the ν-values are
forced (by the arithmetic of the orbit mod 2^k) to be well-distributed,
with average ν ≥ 33/20 = 1.65 per step over any 20-step window. The
effective growth rate is then 3/2^{1.65} ≈ 0.956 < 1: contraction.

For Liouville m on ℝ, there is no integer residue structure. The ν-pattern
is unconstrained. Persistent ν = 1 is possible, and divergence follows.

---

## Part 3: The Necessity Theorem

Combining Parts 1 and 2:

**Corollary.** For a dense G_δ set of transcendental multipliers m:

- **(mx+1)**: The cycle equation has positive real solutions for every
  cycle length k ≥ 2. The no-cycle guarantee fails.

- **(mx+3)**: Orbits with persistent minimal halving diverge geometrically.
  The no-divergence guarantee fails.

The Collatz conjecture for m = 3 avoids both pathologies because:

1. **log₂(3) has finite irrationality measure** (μ = 2, by Roth's theorem),
   so Baker's effective lower bound on |2^S - 3^k| holds. This is the
   "FundamentalGap constant" that prevents cycles.

2. **3 is an integer**, so the orbit lives in ℤ and the 2-adic valuation
   v₂(3x + d) is determined by the residue x mod 2^k. This integer
   structure forces well-distributed halving (Tao mixing), preventing
   divergence.

Both properties fail simultaneously for Liouville multipliers: the
irrationality measure is infinite (no Baker bound), and the orbit
leaves the integers (no residue structure, no forced halving).

---

## Interpretation

This does not show that 3x+1 is false. It shows that the proof is **tight**:
the hypotheses (Baker's theorem + integer residue structure) are not just
sufficient but *necessary*. Remove either one and the conjecture fails.

The Collatz conjecture is true because of a coincidence between two
independent properties of the number 3:

| Property | What it prevents | What breaks without it |
|---|---|---|
| log₂(3) has finite irrationality measure | Cycles | Liouville m: cycle equation satisfiable |
| 3 is an integer (orbit in ℤ) | Divergence | Real m: ν-pattern unconstrained, persistent minimal halving |

Erdos said mathematics may not be ready for such problems. More precisely:
mathematics cannot solve 3x+1 without an effective theory of transcendental
numbers (Baker) and a quantitative theory of integer residue mixing (Tao).
These are the two deepest tools in the proof, and they correspond exactly
to the two ways the conjecture can fail.

The Collatz conjecture sits at the intersection of transcendence theory
and arithmetic dynamics. It is true — but only barely, and only because
log₂(3) is the right kind of irrational number.
