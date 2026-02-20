# Aristotle Prompt: Fallback Interface Refactor (Self-Contained)

You only see this prompt text (no repository files). Generate a cross-file
refactor plan and Lean code snippets.

## Goal

If direct proof of `hardy_littlewood_pair_pole` is too large, eliminate it as a
global axiom by turning it into an explicit hypothesis and threading that
hypothesis through the TwinPrimes chain.

## Required API direction

In `PairSeriesPole`:

```lean
def HardyLittlewoodPairPoleHypothesis : Prop :=
  ∃ A : ℝ, 0 < A ∧
    Tendsto (fun s => (s - 1) * ∑' n, pairCoeff n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)

theorem pair_series_pole (hPole : HardyLittlewoodPairPoleHypothesis) :
    ∃ A : ℝ, 0 < A ∧
    Tendsto (fun s => (s - 1) * ∑' n, pairCoeff n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A) := ...
```

Then thread explicit `hPole` (or a `Fact` wrapper around it) through:

- `PairCorrelationAsymptotic.pair_correlation_asymptotic`
- `PairCorrelationAsymptotic.pair_correlation_lower_bound`
- `PrimeGapBridge.pair_correlation_linear_lower`
- `PrimeGapBridge.rh_implies_twin_primes`
- `PrimeGapBridge.twin_primes`
- `TwinPrimes.twin_primes`

## Hard constraints

- No new axioms.
- No `sorry` additions.
- Keep theorem names stable whenever possible.
- Only add hypothesis arguments needed for threading.

## Output format

Return:
1. A short file-by-file patch plan.
2. Lean code snippets for each changed theorem signature/body.
3. A final list of expected `#print axioms` improvements.

No repository-path assumptions, no shell commands.
