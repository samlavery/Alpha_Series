# Aristotle Prompt: Remove `pair_spiral_detects_small_gaps` (Self-Contained)

You only see this prompt text (no repository files). Generate Lean code that
removes this global axiom dependency.

## Embedded target declaration

```lean
axiom pair_spiral_detects_small_gaps :
    RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, ∃ (p q : ℕ), N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧
      p < q ∧ (q : ℝ) - p < ε * Real.log p
```

The theorem that currently uses it:

```lean
theorem rh_implies_small_gaps : RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (primeGap n : ℝ) < ε * Real.log (nthPrime n) := by
  ...
```

## Goal

Eliminate axiom usage by either:
1. proving the statement directly, or
2. converting it to an explicit hypothesis interface and threading it only into
   `rh_implies_small_gaps` (preferred fallback).

## Hard constraints

- No new global axioms.
- Keep theorem statements as stable as possible.
- No `sorry`.
- Do not disturb TwinPrimes route unless required by signature threading.

## Output format

Return:
1. Lean code for the preferred solution.
2. If fallback is used, include exact new hypothesis definition and revised
   theorem signatures.
3. Brief axiom-impact summary (which theorem footprints improve/stay unchanged).
