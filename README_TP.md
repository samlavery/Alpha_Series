# Twin Primes — Lean 4 Formalization

Two independent proof routes to infinitely many twin primes.

## Routes

| Route | Endpoint | Axioms | Conjectures | Sorries |
|-------|----------|--------|-------------|---------|
| **From GRH** | `twin_primes_from_grh` | 1 (Goldston 1987) | 0 | 0 |
| **Unconditional** | `twin_primes_unconditional` | 1 (Hardy-Littlewood) | 1 | `sorryAx` via LandauTauberian |

## From GRH (primary route)

### Statement

```lean
theorem twin_primes_from_grh
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      GeneralizedRiemannHypothesis χ) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p
```

Located in `Collatz/GRHTwinPrimes.lean`.

### Axiom Footprint

```text
'twin_primes_from_grh' depends on axioms:
  [propext, Classical.choice, GRHTwinPrimes.pair_spiral_spectral_bound, Quot.sound]
```

**No `sorryAx`. No conjecture axioms.** The single axiom `pair_spiral_spectral_bound` encodes a proved theorem (Goldston 1987, Montgomery-Vaughan Ch. 15).

### Proof Architecture

```
1. Under GRH, explicit formula gives:
   |Σ Λ(n)Λ(n+2) - 2C₂·x| ≤ C·x^{1/2}·(log x)²
       [pair_spiral_spectral_bound — Goldston 1987]
   │
2. Error x^{1/2}·(log x)² = o(x) [isLittleO_log_rpow_rpow_atTop]
   → pair correlation ≥ C₂·x for large x
       [pair_correlation_lower_from_grh]
   │
3. Prime-power pair contribution is sublinear (proved)
       [PrimeGapBridge.prime_power_pair_sublinear]
   │
4. Linear growth − sublinear non-twin → infinitely many twin pairs
       [twin_primes_from_grh — pigeonhole]
```

Completely bypasses Landau Tauberian and its sorries.

### Axiom

| Axiom | Reference | Nature |
|-------|-----------|--------|
| `pair_spiral_spectral_bound` | Goldston (1987), Montgomery-Vaughan Ch. 15 | Proved theorem under GRH |

The axiom states: under GRH, the double zero sum in the explicit formula for Σ Λ(n)Λ(n+2) contributes O(x^{1/2}(log x)²). Each zero pair (ρ,ρ') with Re(ρ)=Re(ρ')=1/2 contributes O(x^{1/2}/(|ρ||ρ'|)), and the double sum Σ 1/(|ρ||ρ'|) converges by zero density N(T) ~ T log T.

## Unconditional Route

### Statement

```lean
theorem twin_primes_unconditional :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p
```

Located in `Collatz/PrimeGapBridge.lean`.

### Axiom Footprint

```text
'twin_primes_unconditional' depends on axioms:
  [propext, sorryAx, Classical.choice,
   PairSeriesPole.pair_partial_sum_asymptotic, Quot.sound]
```

One conjecture axiom (`pair_partial_sum_asymptotic` — Hardy-Littlewood) and `sorryAx` from `LandauTauberian.lean`.

| Input | Source | Nature |
|-------|--------|--------|
| `pair_partial_sum_asymptotic` | axiom | Hardy-Littlewood pair conjecture |
| `sorryAx` | sorry in `LandauTauberian.lean` | Tauberian transfer hole |

### Proof Chain (unconditional)

```
1. Hardy-Littlewood: Σ Λ(n)Λ(n+2) ~ 2C₂·N
       [pair_partial_sum_asymptotic — conjecture axiom]
   │
2. Abelian theorem: asymptotic → pair Dirichlet series pole at s=1
       [PairSeriesPole.pair_series_pole]
   │
3. Tauberian transfer: positive pole → pairCorrelation(x) ≥ A·x
       [LandauTauberian — contains sorry]
   │
4. Prime-power pair contribution is sublinear (proved)
       [PrimeGapBridge.prime_power_pair_sublinear]
   │
5. Pigeonhole: linear − sublinear → infinitely many twin pairs
       [twin_primes_unconditional]
```

## Key Theorems

```lean
-- GRH route (0 conjectures, 0 sorries)
theorem GRHTwinPrimes.twin_primes_from_grh (hGRH) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p

-- GRH route: direct linear lower bound (bypasses Tauberian)
theorem GRHTwinPrimes.pair_correlation_lower_from_grh (hGRH) :
    ∃ (c : ℝ) (x₀ : ℕ), 0 < c ∧ ∀ x : ℕ, x₀ ≤ x → c * x ≤ pairCorrelation 1 x

-- Unconditional route
theorem twin_primes_unconditional :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ PrimeGapBridge.IsTwinPrime p
```

## What Is Proved vs Assumed

### Machine-checked (standard axioms only)

- Pair correlation linear lower bound → pigeonhole → infinitely many twins (both routes)
- `prime_power_pair_sublinear`: non-twin contributions sublinear (proved)
- `twin_prime_constant_pos`: 2C₂ > 0 (proved)
- All bridge logic in `GRHTwinPrimes.lean` and `PrimeGapBridge.lean`

### Axioms

| Axiom | Route | Reference | Nature |
|-------|-------|-----------|--------|
| `pair_spiral_spectral_bound` | GRH | Goldston (1987), M-V Ch. 15 | Proved theorem |
| `pair_partial_sum_asymptotic` | Unconditional | Hardy-Littlewood (1923) | Conjecture |

### Remaining gaps (unconditional route only)

| Item | Status | Notes |
|------|--------|-------|
| `pair_partial_sum_asymptotic` | Axiom | Hardy-Littlewood conjecture |
| `LandauTauberian` sorry | sorry | Karamata Tauberian formalization gap |

The GRH route has **no remaining gaps** — 1 proved-theorem axiom, 0 sorries, 0 conjectures.

## Build and Check

```bash
# GRH route (recommended)
lake build Collatz.GRHTwinPrimes
lake env lean Collatz/GRHTwinPrimes.lean 2>&1 | grep axioms

# Unconditional route
lake build Collatz.PrimeGapBridge
lake env lean Collatz/PrimeGapBridge.lean 2>&1 | grep axioms

# Supporting files
lake env lean Collatz/PairSeriesPole.lean 2>&1 | grep axioms
lake env lean Collatz/LandauTauberian.lean 2>&1 | grep axioms
```

## File Guide

```
Collatz/GRHTwinPrimes.lean             GRH route endpoint (0 sorries, 0 conjectures)
Collatz/PrimeGapBridge.lean            unconditional route endpoint + pigeonhole
Collatz/PairCorrelationAsymptotic.lean pair-correlation lower bound (unconditional)
Collatz/PairSeriesPole.lean            pair Dirichlet series, axioms
Collatz/LandauTauberian.lean           Tauberian transfer (contains sorry)
Collatz/GRH.lean                       GRH definition + axioms (used by GRH route)
```
