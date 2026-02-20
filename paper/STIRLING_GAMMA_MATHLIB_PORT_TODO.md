# Stirling/Gamma Mathlib Port TODO

This checklist tracks the remaining formalization work for the complex Gamma-strip bounds so the result can be upstreamed to mathlib.

## Scope

Goal theorem family:
- For fixed `0 < σ ≤ 1` and large `|t|`,
  `C_lo * |t|^(σ-1/2) * exp(-π|t|/2) <= ||Γ(σ+it)|| <= C_hi * |t|^(σ-1/2) * exp(-π|t|/2)`.

## Ordered Tasks

1. Upper-half ratio core (`σ in (1/2, 1)`)
- File: `Collatz/StirlingBound.lean`
- Target: `gamma_ratio_upper_half_direct`
- Deliverable: remove current `sorry` by proving two-sided `|t|^(σ-1/2)` ratio bounds.

2. Beta vertical decay lemma
- File: `Collatz/StirlingBound.lean`
- Target interface: `BetaVerticalDecay`
- Deliverable: prove
  `B_lo * |t|^(-a) <= ||betaIntegral a (1/2+it)|| <= B_hi * |t|^(-a)` for `a in (0,1/2)`.

3. Transfer equivalence
- File: `Collatz/StirlingBound.lean`
- Deliverable: reusable lemma converting Beta bounds <-> Gamma ratio bounds via
  `B(a, 1/2+it) = Γ(a) Γ(1/2+it) / Γ(a+1/2+it)`.

4. Lower-half strip via reflection
- File: `Collatz/StirlingBound.lean`
- Deliverable: derive bounds for `σ in (0,1/2)` from upper-half and reflection product.

5. Full unit-strip assembly
- File: `Collatz/StirlingBound.lean`
- Deliverable: close `stirling_unit_strip` and then `gamma_stirling_bound` without `sorry`.

6. Portability cleanup
- Rename helper lemmas to generic names.
- Keep no Collatz-specific constants in Gamma/Beta lemmas.
- Isolate only reusable analysis statements.

7. Validation
- `lake env lean Collatz/StirlingBound.lean`
- `lake env lean Collatz/1135.lean`
- `#print axioms StirlingBound.gamma_ratio_upper_half_direct`
- `#print axioms StirlingBound.gamma_stirling_bound`

## Notes

- Bohr-Mollerup/log-convexity helps for real-axis Gamma control and constants.
- The missing piece is the complex vertical-line two-sided asymptotic control.
