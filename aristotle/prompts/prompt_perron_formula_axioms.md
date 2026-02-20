# Aristotle Prompt: Perron Formula Axiom Elimination (Self-Contained)

You only see this prompt text (no repository files). Produce Lean snippets for
removing or isolating Perron global axioms.

## Embedded current shape

```lean
namespace PerronFormula

axiom perronZeroSum : ℝ → ℝ → ℝ
axiom perron_contour_shift : ...
axiom perron_zero_sum_bound : ...

theorem perron_explicit_formula : ...
theorem rh_explicit_formula : ...
theorem explicit_formula_unconditional : ...

end PerronFormula
```

Downstream user (example):
- `HadamardBridge.rh_implies_psi_error` depends on Perron stack.

## Goal

Reduce Perron-related global axioms while preserving downstream theorem APIs as
much as possible.

## Priority

1. Best: prove `perron_contour_shift` and `perron_zero_sum_bound` directly.
2. Fallback: convert them to explicit hypothesis interfaces and thread only
   through needed theorems.

## Hard constraints

- No new global axioms.
- No `sorry`.
- Keep names stable where possible.
- Preserve downstream usability (`HadamardBridge` path).

## Fallback interface template

```lean
def PerronContourShiftHypothesis : Prop := ...
def PerronZeroSumBoundHypothesis : Prop := ...
```

Then revise:

- `perron_explicit_formula`
- `rh_explicit_formula`
- `explicit_formula_unconditional`

to take explicit hypothesis arguments.

## Output format

Return:
1. A compact refactor plan.
2. Lean code snippets for revised declarations and proofs.
3. Expected axiom-footprint changes for:
   - `PerronFormula.perron_explicit_formula`
   - `PerronFormula.rh_explicit_formula`
   - `PerronFormula.explicit_formula_unconditional`
   - `HadamardBridge.rh_implies_psi_error`
