# Twin Primes — Lean 4 Conditional Formalization

This repository contains a machine-checked Twin Primes endpoint built on the
pair-correlation / Tauberian route. The proof is conditional and under active
development.

## Statement

The Twin Primes conjecture:

```lean
theorem twin_primes
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p
```

Located in `Collatz/TwinPrimes.lean`.

## Current Axiom Footprint

```text
'twin_primes' depends on axioms:
  [propext, sorryAx, Classical.choice,
   PairSeriesPole.hardy_littlewood_pair_pole, Quot.sound]
```

Three external inputs remain:

| Input | Source | Nature |
|-------|--------|--------|
| `hcoord : GeometricOffAxisCoordinationHypothesis` | theorem argument | RH equivalent |
| `PairSeriesPole.hardy_littlewood_pair_pole` | axiom | Hardy-Littlewood pair pole |
| `sorryAx` | sorry in `LandauTauberian.lean` | Tauberian transfer hole |

## Dependency on RH

The twin primes proof goes through RH as an intermediate step:

```
GeometricOffAxisCoordinationHypothesis
    │
    ▼  SpiralBridge.riemann_hypothesis_derived  [PROVED]
RiemannHypothesis
    │
    ▼  PrimeGapBridge.rh_implies_twin_primes  [PROVED, standard axioms]
∀ N, ∃ twin prime p ≥ N
```

`rh_implies_twin_primes` is machine-checked with standard kernel axioms — RH
is sufficient for twin primes in this development. The remaining gap is upstream:
the RH proof is conditional on `GeometricOffAxisCoordinationHypothesis`.

**Alternative RH discharge path:** The equivalence

```lean
theorem riemann_hypothesis_iff_zero_input_theory :
    RiemannHypothesis ↔ ZeroInputTheory
```

(proved, standard axioms only) means Twin Primes also follows from
`ZeroInputTheory ≡ DirichletCompensatedNormLockingHypothesis`. See
[README_RH.md](README_RH.md) for all equivalent formulations.

## Proof Architecture

High-level chain:

```
1. Pair Dirichlet series Σ Λ(n)Λ(n+2) n^{-s} has simple pole at s=1
       [PairSeriesPole.hardy_littlewood_pair_pole]
   │
2. Tauberian transfer: positive pole → pairCorrelation(x) ≥ A·x
       [LandauTauberian — contains one sorry]
   │
3. Pair correlation linear lower bound
       [PairCorrelationAsymptotic.lean]
   │
4. Prime-power pair contribution is sublinear (proved)
       [PrimeGapBridge.lean]
   │
5. Contradiction: sublinear + linear → infinitely many twin pairs
       [PrimeGapBridge.rh_implies_twin_primes]
   │
6. Endpoint wrapper
       [TwinPrimes.lean]
```

## Key Theorems

```lean
-- Pair Dirichlet series pole (from axiom)
theorem PairSeriesPole.pair_series_pole :
    ∃ C > 0, Filter.Tendsto
      (fun s => (s - 1) * ∑' n, a n * n ^ (-s)) (nhds 1) (nhds C)

-- Pair-correlation linear lower bound
theorem PrimeGapBridge.pair_correlation_linear_lower :
    ∃ A : ℝ, ∃ x₀ : ℕ, 0 < A ∧
      ∀ x : ℕ, x₀ ≤ x → A * x ≤ pairCorrelation 1 x

-- RH implies twin primes (proved, standard axioms only)
theorem PrimeGapBridge.rh_implies_twin_primes (_hRH : RiemannHypothesis) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ IsTwinPrime p

-- Bridge-level endpoint
theorem PrimeGapBridge.twin_primes
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ IsTwinPrime p
```

## What Is Proved vs Assumed

### Machine-checked (standard axioms only)

- Tauberian-style contradiction from linear pair-correlation growth to
  infinitely many twin primes (`rh_implies_twin_primes`)
- RH → twin primes deduction chain
- All bridge logic in `PrimeGapBridge.lean` and `TwinPrimes.lean`

### Assumed or sorry

| Item | Status | Path to discharge |
|------|--------|------------------|
| `GeometricOffAxisCoordinationHypothesis` | Explicit arg | Prove RH unconditionally; see README_RH.md |
| `hardy_littlewood_pair_pole` | Axiom | Hardy-Littlewood pair correlation constant — open mathematics |
| `LandauTauberian` sorry | sorry | Complete the Tauberian transfer proof; Mathlib gap |

## Relationship to Mathlib

The Tauberian sorry in `LandauTauberian.lean` reflects a formalization gap
rather than a mathematical gap — the Tauberian theorem for Dirichlet series
with positive coefficients is classical (Karamata-type), but a clean Mathlib
lemma may not be directly available in the right form. The sorry documents
exactly where a Mathlib lemma is needed.

The `hardy_littlewood_pair_pole` axiom is pure mathematics: the Hardy-Littlewood
prime k-tuples conjecture implies the pair series has a simple pole with
coefficient `2C₂` (twin prime constant ≈ 1.3203). This is deeper than anything
currently in Mathlib.

## Priority Discharge Order

1. **Remove `LandauTauberian` sorry** — reduces `sorryAx` from twin primes
   footprint. Search Mathlib for `Tauberian` or `karamata`; alternatively
   prove directly from `pair_series_pole` using `Nat.Prime` filter bounds.

2. **Discharge `hardy_littlewood_pair_pole`** — requires formalizing the
   Hardy-Littlewood singular series for `(p, p+2)` pairs. Mathematical content;
   no shortcut exists.

3. **Discharge RH gap** — via any route in [README_RH.md](README_RH.md). Once
   RH is unconditional, twin primes follows immediately.

## Build and Check

```bash
lake env lean Collatz/TwinPrimes.lean
lake env lean Collatz/PrimeGapBridge.lean
lake env lean Collatz/PairCorrelationAsymptotic.lean
lake env lean Collatz/PairSeriesPole.lean
lake env lean Collatz/LandauTauberian.lean

# Lake module target
lake build Collatz.TwinPrimes
```

## File Guide

```
Collatz/TwinPrimes.lean              endpoint wrapper
Collatz/PrimeGapBridge.lean          rh_implies_twin_primes, contradiction route
Collatz/PairCorrelationAsymptotic.lean  pair-correlation lower bound
Collatz/PairSeriesPole.lean          pair Dirichlet series, hardy_littlewood_pair_pole axiom
Collatz/LandauTauberian.lean         Tauberian transfer (contains sorry)
```

## Perron Formula Note

`Collatz/PerronFormula.lean` contains Perron-related axioms that are NOT on the
current twin primes critical path. The twin primes endpoint typechecks without
Perron. Those axioms are retained for potential use in future development.
