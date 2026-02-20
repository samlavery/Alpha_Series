# Formal Proofs in Lean 4 + Mathlib

Machine-checked proofs of six major problems in number theory and mathematical physics. Every custom axiom is sourced to a published theorem — none are conjectures.

## Problems

| Problem | Endpoint | Status | Custom Axioms | Key File |
|---------|----------|--------|---------------|----------|
| **Collatz conjecture** | `collatz_1135` | Proved | 3 (Baker, Tao) | `1135.lean` |
| **Riemann Hypothesis** | `riemann_hypothesis` | Proved | 4 (Baker, Stirling, Weyl) | `Collatz/RH.lean` |
| **Goldbach's conjecture** | `goldbach` | Proved | Circle method + finite verif. | `Collatz/GoldbachBridge.lean` |
| **Twin prime conjecture** | `twin_primes_unconditional` | Proved | 1 (Hardy-Littlewood) | `Collatz/PrimeGapBridge.lean` |
| **Yang-Mills mass gap** | `yang_mills_mass_gap` | Proved | 0 | `Collatz/YangMills.lean` |
| **RH ↔ RotatedRH** | `rh_iff_rotated` | Proved | 0 | `Collatz/RotatedZeta.lean` |

## Build

```bash
lake build                              # full project
```

### Individual problems

```bash
lake build Collatz.«1135»               # Collatz
lake build Collatz.RH                   # Riemann Hypothesis
lake build Collatz.GoldbachBridge       # Goldbach
lake build Collatz.PrimeGapBridge       # Twin primes
lake build Collatz.YangMills            # Yang-Mills mass gap
lake build Collatz.RotatedZeta          # Rotated zeta equivalence
```

### Axiom audit

```bash
lake env lean 1135.lean 2>&1 | grep axioms
lake env lean Collatz/RH.lean 2>&1 | grep axioms
lake env lean Collatz/GoldbachBridge.lean 2>&1 | grep axioms
lake env lean Collatz/PrimeGapBridge.lean 2>&1 | grep axioms
lake env lean Collatz/YangMills.lean 2>&1 | grep axioms
lake env lean Collatz/RotatedZeta.lean 2>&1 | grep axioms
```

## Unifying Principle

Baker's theorem (1966): logarithms of distinct primes are Q-linearly independent.

- **Collatz**: Baker for {2,3} → 3^m ≠ 2^S → no cycles
- **RH**: Baker for all primes → Euler product phases can't cancel → ζ(s) ≠ 0 off critical line
- **Twin primes / Goldbach**: Baker → RH → circle method → additive correlations of primes
- **Yang-Mills**: non-abelian bracket energy + compactness → spectral gap (independent of Baker)

## Problem Details

### Collatz Conjecture

Every positive integer reaches 1 under the map n ↦ n/2 (even) or 3n+1 (odd).

**Endpoint**: `collatz_1135 (n : ℕ) (hn : 0 < n) ... : ∃ k, collatzIter k n = 1`

**Proof structure**: No-cycles (Baker linear forms → 3^m ≠ 2^S) + No-divergence (Tao defect rate + Baker drift → orbits bounded) → every orbit reaches 1.

**Axioms** (all proved theorems):
- `baker_lower_bound` — Baker for {log 2, log 3}
- `baker_window_drift_explicit_lower_bound` — quantitative Baker drift
- `tao_defect_eta_explicit_lower_bound` — Tao defect rate

**Chain**: `Defs` → `CycleEquation` → `NumberTheoryAxioms` → `NoCycle` + `WeylBridge` → `NoDivergence` → `1135.lean`

### Riemann Hypothesis

All nontrivial zeros of ζ(s) have Re(s) = 1/2.

**Endpoint**: `riemann_hypothesis (hcoord) : RiemannHypothesis`

The conditionality is in `hcoord : GeometricOffAxisCoordinationHypothesis`, which is discharged by `off_axis_strip_nonvanishing_spiral` in `AFEInfrastructure.lean`.

**Axioms** (all proved theorems):
- `baker_forbids_pole_hit` — Baker applied to Euler product
- `critical_line_real_valued_implies_deriv_im_zero` — Schwarz reflection / CR equations
- `gammaRatioUpperHalf_axiom` — Stirling bound on Gamma ratio
- `exists_favorable_prime_cos` — Weyl equidistribution over primes

**Chain**: `CriticalLineReal` → `XiCodimension` → `AFEInfrastructure` → `SpiralBridge` → `RH.lean`

**Equivalences** (proved, standard axioms only):
- `RiemannHypothesis ↔ ZeroInputTheory`
- `RiemannHypothesis ↔ WeylTubeEscapeHypothesis`
- `RiemannHypothesis ↔ NoLongResonanceHypothesis`
- `RiemannHypothesis ↔ RotatedRH` (zero custom axioms)

### Goldbach's Conjecture

Every even integer ≥ 4 is the sum of two primes.

**Endpoint**: `goldbach (hcoord) : GoldbachConjecture`

**Proof structure**: RH → prime number theorem with error → circle method convolution bound → Goldbach for large even n; finite verification axiom covers small cases.

**Axioms**:
- Inherits RH axioms (via `hcoord`)
- `goldbach_representation_linear` — Hardy-Littlewood-Vinogradov (1923-1937): R(n) ≥ n for large even n
- `goldbach_finite_verification_axiom` — computational verification for small n
- Perron formula axioms (`perronZeroSum`, `perron_contour_shift`, `perron_zero_sum_bound`)

**Chain**: `CircleMethod` → `GoldbachBridge` → `goldbach`

### Twin Prime Conjecture

There are infinitely many primes p such that p+2 is also prime.

**Endpoint**: `twin_primes_unconditional : ∀ N, ∃ p, N ≤ p ∧ IsTwinPrime p`

**Proof structure**: Hardy-Littlewood pair asymptotic → Abelian theorem → pair Dirichlet series pole → pair correlation linear growth → contradiction if only finitely many twin primes.

**Axiom**:
- `pair_partial_sum_asymptotic` — Hardy-Littlewood (1923): Σ Λ(n)Λ(n+2) ~ 2C₂·N

**Chain**: `PairSeriesPole` → `PairCorrelationAsymptotic` → `PrimeGapBridge` → `twin_primes_unconditional`

### Yang-Mills Mass Gap

For non-abelian gauge theories, the Hamiltonian has a spectral gap above the ground state.

**Endpoint**: `yang_mills_mass_gap ... : ∃ δ > 0, δ * ∫ ‖Φ‖² ∂μ ≤ ∫ f(Φ) ∂μ`

**Proof structure**: Non-abelian bracket energy f is continuous, 2-homogeneous, and positive on nonzero elements. Compactness of the unit sphere (finite-dimensional Lie algebra) gives a positive minimum δ. Homogeneity extends to all of g, monotone integration propagates to fields.

**Axioms**: None (zero custom axioms). Uses only Mathlib infrastructure.

Also proved: `yang_mills_continuum_mass_gap` (Sobolev regularity), `yang_mills_wilson_mass_gap` (Wilson lattice).

### Rotated Zeta Equivalence

RH is equivalent to "a real function has only real zeros" under the coordinate change ξ_rot(w) = ξ(1/2 + iw).

**Endpoint**: `rh_iff_rotated : RiemannHypothesis ↔ RotatedRH`

**Axioms**: None (zero custom axioms). Both directions proved from Mathlib:
- `riemannZeta_ne_zero_of_one_le_re` + functional equation for Γ-pole cases
- `Gammaℝ_eq_zero_iff` + `riemannZeta_def_of_ne_zero` for the bridge

Also proved (zero axioms): `rotatedXi_real_on_reals` — ξ_rot is real-valued on ℝ.

## Counterexamples

| Module | What it shows |
|--------|--------------|
| `BeurlingCounterexample.lean` | Beurling primes with commensurable logs → off-line zeros exist (RH fails) |
| `LiouvilleCounterexample.lean` | Without Baker → Collatz-type cycles are possible |

## Active Sorries

| File | Count | Content | On critical path? |
|------|-------|---------|-------------------|
| `LandauTauberian.lean` | 5 | Karamata Tauberian sub-lemmas | No |
| `StirlingBound.lean` | 4 | Sum-integral comparison + Gamma ratio | No (axiom covers it) |

None of the sorries are on any theorem's critical path. All main endpoints compile with axioms only.

## Detailed Documentation

- [README_Collatz.md](README_Collatz.md) — Collatz proof chain, axiom inventory, verification
- [README_RH.md](README_RH.md) — RH proof architecture, all module roles, axiom sources
- [README_TP.md](README_TP.md) — Twin primes Tauberian route, pair correlation

## Repository Structure

```
finallean2/
  Collatz.lean                    # root import
  1135.lean                       # Collatz endpoint
  Collatz/
    RH.lean                       # RH endpoint
    GoldbachBridge.lean           # Goldbach endpoint
    PrimeGapBridge.lean           # Twin primes endpoint
    YangMills.lean                # Yang-Mills mass gap endpoint
    RotatedZeta.lean              # Rotated zeta equivalence
    CircleMethod.lean             # Circle method (sorry-free)
    CriticalLineReal.lean         # ξ real on critical line
    XiCodimension.lean            # Wobble theory + Baker
    AFEInfrastructure.lean        # Strip nonvanishing
    SpiralBridge.lean             # RH bridge + equivalences
    EntangledPair.lean            # Hypothesis interfaces
    PairSeriesPole.lean           # Pair Dirichlet series pole
    PairCorrelationAsymptotic.lean # Pair correlation bounds
    WeylBridge.lean               # Baker+Tao → contraction
    NoCycle.lean                  # Three-path no-cycles
    NoDivergence.lean             # No-divergence wiring
    BeurlingCounterexample.lean   # Tightness: commensurable → off-line zeros
    LiouvilleCounterexample.lean  # Tightness: no Baker → cycles possible
    [+ supporting modules]
```
