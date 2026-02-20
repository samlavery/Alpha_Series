# Aristotle Prompt: Prove `hardy_littlewood_pair_pole` (Self-Contained)

You only see this prompt text (no repository files). Generate Lean code that
can be pasted into `Collatz/PairSeriesPole.lean`.

## Embedded local context

```lean
namespace PairSeriesPole

noncomputable def pairCoeff (n : ℕ) : ℝ := (Λ n : ℝ) * Λ (n + 2)

theorem pairCoeff_nonneg (n : ℕ) : 0 ≤ pairCoeff n := ...

theorem pair_series_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n => pairCoeff n / (n : ℝ) ^ s) := ...

axiom hardy_littlewood_pair_pole :
    ∃ A : ℝ, 0 < A ∧
    Tendsto (fun s => (s - 1) * ∑' n, pairCoeff n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)

theorem pair_series_pole :
    ∃ A : ℝ, 0 < A ∧
    Tendsto (fun s => (s - 1) * ∑' n, pairCoeff n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A) :=
  hardy_littlewood_pair_pole

end PairSeriesPole
```

## Task

Replace the axiom with a theorem proof:

```lean
theorem hardy_littlewood_pair_pole :
    ∃ A : ℝ, 0 < A ∧
    Tendsto (fun s => (s - 1) * ∑' n, pairCoeff n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A) := by
  ...
```

## Hard constraints

- Do not change the statement.
- Do not add any new axioms.
- Do not use `sorry`.
- Keep `pair_series_pole` as a direct consequence of this theorem.

## Output format

Return only:
1. The replacement Lean code block for `hardy_littlewood_pair_pole`.
2. Any small helper lemmas required (also as Lean code), in the same namespace.

No prose outside the code blocks.
