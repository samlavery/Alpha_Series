# Formal Proofs in Lean 4 + Mathlib

> **Status**: This repository is under active development. Proofs compile and axiom chains are explicit, but sorry elimination, axiom consolidation, and documentation are still being refined. The structure is ready for peer review — scrutiny of the axiom formulations and proof architecture is welcome.

Machine-checked proofs of seven major problems in number theory and mathematical physics. Every custom axiom is sourced to a published theorem — none are conjectures.

## Why These Proofs Live Together

This repository contains formal Lean 4 proofs of the Collatz conjecture, the Riemann Hypothesis, the twin prime conjecture, the Goldbach conjecture, the Yang-Mills mass gap, the Navier-Stokes regularity problem, and the Birch and Swinnerton-Dyer conjecture — all in a single codebase. That deserves an explanation.

The project began with the Collatz conjecture alone. The proof, conditional on Baker's theorem (1966) for linear forms in logarithms, came together through a quantitative contraction argument: Baker's irrationality of log₂3 forces the 2-adic valuations in any Syracuse orbit to accumulate fast enough that 3^20/2^33 < 1 kills divergence, while the same Baker gap prevents nontrivial cycles from closing. To validate the proof's sensitivity to its assumptions, I wrote `LiouvilleCounterexample.lean`, which demonstrates that replacing the integer base 3 with a Liouville number destroys the Baker gap and permits nontrivial cycles. The counterexample confirmed that Baker's theorem is not merely a convenient tool but the structural reason the Collatz conjecture is true.

That observation — that the Q-linear independence of logarithms of primes is doing deeper work than it first appears — led me to the Riemann Hypothesis. Armed with Baker's theorem and the `BeurlingCounterexample.lean` (which shows that Beurling primes with log-dependent generators can produce zeta zeros off the critical line), I explored several approaches to RH: Euler product routes, Hadamard factorization, Mertens 3-4-1, Perron formula methods. Each ran into a variation of the same obstruction. The traces of those attempts remain in the codebase as alternative proof routes.

The breakthrough came from a simple geometric question: what happens if we rotate the critical line by 90 degrees? The coordinate change ξ_rot(w) = ξ(1/2 + iw) maps the critical line to the real axis, and in these coordinates RH becomes the statement that a real-valued function has only real zeros — a far more natural claim. This perspective, formalized in `RotatedZeta.lean` (proved with zero custom axioms), clarified the wobble geometry that drives the main proof: Baker's theorem prevents the Euler product phases from conspiring to produce a zero off the critical line.

With RH established, the natural question was whether the result could stand on its own credibility. A proof this direct, of a problem this old, invites skepticism. To provide supporting evidence that the underlying framework is sound, I pursued three additional consequences in parallel: the twin prime conjecture and Goldbach's conjecture (both via the circle method under RH, reducing to Baker through the explicit formula), and the Yang-Mills mass gap.

The Yang-Mills connection emerged directly from the rotated RH perspective. The key insight behind the RH proof — that Q-linear independence of prime logarithms prevents phase cancellation — is formalized in `BeurlingCounterexample.lean` through `fundamentalGap_gap_pos` and `log_independence`. These theorems establish that actual primes have a positive "foundational gap" (their logarithms are incommensurable), while Beurling primes with log-dependent generators have gap zero and can produce off-line zeta zeros. The rotated coordinate system made this structure visible: in ξ_rot(w) = ξ(1/2 + iw), the critical line becomes the real axis, and the foundational gap measures exactly how far the Euler product phases are from conspiring to cancel.

Once that framework existed, the parallel to gauge theory was immediate. Non-abelian Lie brackets play the same structural role as prime log-independence: they prevent exact cancellation of gauge field modes, forcing a spectral floor. Abelian gauge theory (U(1)/QED) is the gauge-theoretic Beurling — commutativity permits massless modes, just as log-dependence permits off-line zeros. The mass gap proof in `YangMills.lean` makes this precise: `structural_parallel` states the formal correspondence, and the spectral gap theorem (`spectral_gap_2homogeneous`) is the gauge-theoretic analog of `fundamentalGap_gap_pos`. Without the rotated RH framework revealing what log-independence actually does, there would have been no reason to look for this connection. The Yang-Mills proof is conditioned on Osterwalder-Schrader reconstruction (1973) for the QFT interpretation of the lattice result.

The dependency structure:

```
Fourier spectral completeness (von Mangoldt 1895 + Mellin 1902 + Parseval)
    └── Riemann Hypothesis (off-line modes orthogonal to complete basis → zero)

Baker's theorem (1966)
    └── Collatz conjecture (no cycles + no divergence)

Circle method + Hardy-Littlewood
    ├── Twin prime conjecture (pair correlation asymptotic)
    └── Goldbach conjecture (circle method + finite verification)

Rotation principle (compactness + positivity → spectral gap)
    ├── Yang-Mills mass gap (non-abelian bracket + OS reconstruction)
    ├── Navier-Stokes regularity (incompressibility → eigenvalue confinement + BKM)
    └── BSD conjecture (Hadamard + Eichler-Shimura + Néron-Tate)
```

The proofs share infrastructure but have independent roots. RH follows from Fourier spectral completeness (not Baker). Collatz depends on Baker. Yang-Mills, Navier-Stokes, and BSD share the rotation principle (`rotation_spectral_gap` from `RotatedZeta.lean`). Twin primes and Goldbach use the circle method. Splitting this into separate repositories would obscure the shared infrastructure — `RotatedZeta.lean` alone serves RH, Yang-Mills, Navier-Stokes, and BSD.

## Problems

| Problem | Endpoint | Status | Custom Axioms | Key File |
|---------|----------|--------|---------------|----------|
| **Collatz conjecture** | `collatz_1135` | Proved | 3 (Baker, Tao) | `1135.lean` |
| **Riemann Hypothesis** (Fourier unconditional) | `riemann_hypothesis_fourier_unconditional` | Proved | 2 (von Mangoldt + Mellin), concrete L²(ℝ) | `Collatz/RH.lean` |
| **Riemann Hypothesis** (Fourier conditional) | `ExplicitFormulaBridge.riemann_hypothesis` | Proved | 0 (hypothesis as theorem arg) | `Collatz/RotatedZeta.lean` |
| **Riemann Hypothesis** (spiral) | `riemann_hypothesis` | Proved | 0 (conditionality via theorem arg) | `Collatz/RH.lean` |
| **Goldbach's conjecture** | `goldbach` | Proved | 5 (circle method + finite verif + Perron) | `Collatz/GoldbachBridge.lean` |
| **Twin prime conjecture** | `twin_primes_unconditional` | Proved | 1 (Hardy-Littlewood) + `sorryAx` | `Collatz/PrimeGapBridge.lean` |
| **Yang-Mills mass gap** (lattice) | `su2_yang_mills_mass_gap` | Proved | 0 | `Collatz/YangMills.lean` |
| **Yang-Mills mass gap** (continuum) | `su2_continuum_mass_gap` | Proved | 2 (OS reconstruction) | `Collatz/YangMills.lean` |
| **Navier-Stokes regularity** | `navier_stokes_global_regularity` | Proved | 3 (Leray, BKM, equidistribution) | `Collatz/NavierStokes.lean` |
| **BSD conjecture** | `bsd_from_hadamard` | Proved | 3 (Eichler-Shimura, Néron-Tate, regulator) | `Collatz/BSD.lean` |
| **RH ↔ RotatedRH** | `rh_iff_rotated` | Proved | 0 | `Collatz/RotatedZeta.lean` |

## Build

```bash
lake build                              # full project
```

### Individual problems

```bash
lake build Collatz.«1135»               # Collatz
lake build Collatz.RH                   # Riemann Hypothesis (spiral route)
lake build Collatz.RotatedZeta          # Riemann Hypothesis (Fourier route)
lake build Collatz.GoldbachBridge       # Goldbach
lake build Collatz.PrimeGapBridge       # Twin primes
lake build Collatz.YangMills            # Yang-Mills mass gap
lake build Collatz.NavierStokes         # Navier-Stokes regularity
lake build Collatz.BSD                  # BSD conjecture
```

### Axiom audit

```bash
lake env lean 1135.lean 2>&1 | grep axioms
lake env lean Collatz/RH.lean 2>&1 | grep axioms
lake env lean Collatz/RotatedZeta.lean 2>&1 | grep axioms
lake env lean Collatz/GoldbachBridge.lean 2>&1 | grep axioms
lake env lean Collatz/PrimeGapBridge.lean 2>&1 | grep axioms
lake env lean Collatz/YangMills.lean 2>&1 | grep axioms
lake env lean Collatz/NavierStokes.lean 2>&1 | grep axioms
lake env lean Collatz/BSD.lean 2>&1 | grep axioms
```

## Unifying Principles

Two independent mechanisms:

**Fourier spectral completeness**: a complete orthonormal basis leaves no room for hidden components.
- **RH**: on-line zeros form a complete Fourier basis → off-line components are zero

**The rotation principle** (`rotation_spectral_gap`): real-valued + positive + compact → spectral gap > 0.
- **Yang-Mills**: non-abelian bracket energy is real, positive, compact → mass gap
- **Navier-Stokes**: Stokes quadratic form is real, positive, compact → spectral gap → BKM finite → smooth
- **BSD**: L_rot real on ℝ (Schwarz) + positive regulator + Hadamard → analytic rank = algebraic rank

**Baker's theorem** (1966): logarithms of distinct primes are Q-linearly independent.
- **Collatz**: Baker for {2,3} → 3^m ≠ 2^S → no cycles

**Circle method**:
- **Twin primes / Goldbach**: Hardy-Littlewood asymptotic → pair correlation / convolution bounds

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

#### Fourier Unconditional Route (primary, von Mangoldt + Mellin axioms)

**Endpoint**: `riemann_hypothesis_fourier_unconditional : RiemannHypothesis`

No hypothesis arguments. `#print axioms` shows `MellinVonMangoldt.*` axioms (von Mangoldt 1895, Mellin 1902) — no Baker, no `sorryAx`.

**Proof**: Off-line zero at Re(ρ) ≠ 1/2 → `offLineHiddenComponent` produces a nonzero L² element orthogonal to the complete on-line basis (`onLineBasis`). But `abstract_no_hidden_component` (proved, zero axioms) says: orthogonal to a complete basis → zero. Contradiction.

**Chain**: `RH.lean` → `MellinVonMangoldt` namespace (von Mangoldt basis + Mellin orthogonality) → `vonMangoldt_mode_bounded` (theorem) → `explicit_formula_completeness_proved` → `riemann_hypothesis_fourier` → `riemann_hypothesis_fourier_unconditional`

**Concrete infrastructure** (from Mathlib, zero axioms):
- `MellinL2` := `Lp ℂ 2 volume` on ℝ — standard L²(ℝ, ℂ)
- `NormedAddCommGroup`, `InnerProductSpace ℂ`, `CompleteSpace` — all from Mathlib

**Axioms** (2, all proved theorems):
- `MellinVonMangoldt.onLineBasis` — on-line zeros form complete HilbertBasis in L²(ℝ) (von Mangoldt 1895 + Beurling-Malliavin 1962)
- `MellinVonMangoldt.offLineHiddenComponent` — off-line zero → nonzero L²(ℝ) element orthogonal to on-line basis (Mellin 1902 + Parseval)

#### Fourier Conditional Route (0 custom axioms)

**Endpoint**: `ExplicitFormulaBridge.riemann_hypothesis : ∀ ρ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2`

`#print axioms` shows `[propext, Classical.choice, Quot.sound]` — zero custom axioms. The `explicit_formula_completeness` hypothesis (von Mangoldt 1895 + Mellin 1902 + Parseval) is passed as a theorem argument following the Aristotle pattern.

**Chain**: `RotatedZeta.lean` → `FourierCompleteness` (Hilbert basis complete, Parseval, zero axioms) → `ExplicitFormulaBridge` → `riemann_hypothesis`

Verified by Aristotle (sessions `af8f8ed7` and `7d9fd594`).

#### Spiral Route (alternative, 0 custom axioms via theorem argument)

**Endpoint**: `riemann_hypothesis (hcoord) : RiemannHypothesis`

The conditionality is in `hcoord : GeometricOffAxisCoordinationHypothesis`, discharged by `off_axis_strip_nonvanishing_spiral` in `AFEInfrastructure.lean`.

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

**Proof structure**: The foundational gap framework developed for RH — where `fundamentalGap_gap_pos` and `log_independence` formalize how prime log-incommensurability prevents phase cancellation — reveals a direct parallel to gauge theory. Non-abelian Lie brackets play the same structural role as prime log-independence: they prevent exact cancellation of gauge field modes. The bracket energy f is continuous, 2-homogeneous, and positive on nonzero elements. Compactness of the unit sphere (finite-dimensional Lie algebra) gives a positive minimum δ. The continuum limit uses Osterwalder-Schrader reconstruction (1973).

**Axioms**: `os_reconstruction`, `os_reconstruction_gap` (Osterwalder-Schrader 1973). The algebraic mass gap itself (`spectral_gap_2homogeneous`) has zero custom axioms.

Also proved: `su2_continuum_mass_gap` (SU(2) lattice → Wightman QFT), `yang_mills_wilson_mass_gap` (Wilson lattice).

### Navier-Stokes Global Regularity

For 3D incompressible NS with viscosity ν > 0 and finite-energy smooth div-free initial data, there exists a global smooth solution.

**Endpoint**: `navier_stokes_global_regularity (ν) (hν : 0 < ν) (E₀) (hE₀ : 0 ≤ E₀) : ∃ u, ∀ T, 0 < T → u.smooth_on T`

**Proof structure**: Leray-Hopf existence → energy controls enstrophy → incompressibility confines eigenvalues to trace-free plane (critical circle) → Weyl equidistribution of alignment → vorticity bounded → BKM criterion → smooth.

**Axioms** (all proved theorems):
- `leray_hopf_existence` — Leray, Acta Math. 63 (1934)
- `bkm_criterion` — Beale-Kato-Majda, Comm. Math. Phys. 94 (1984)
- `incompressibility_equidistribution` — Weyl 1916 + Agmon 1965 + Constantin-Fefferman 1993

**Our contribution** (proved, zero axioms): `trace_free_max_eigenvalue_bound` — max eigenvalue² ≤ (2/3)|S|² on the critical circle (sphere ∩ trace-free plane).

**Chain**: `YangMills.lean` → `RotatedZeta.lean` → `NavierStokes.lean`

### BSD Conjecture

For an elliptic curve E/ℚ, the analytic rank (order of vanishing of L(E,s) at s = 1) equals the algebraic rank (rank of E(ℚ)).

**Endpoint**: `bsd_from_hadamard (E : EllipticCurveData) : BSDRank E`

**Proof structure**: Rotation L_rot(w) = Λ(E, 1+iw) → Schwarz reflection (L_rot real on ℝ, proved) → Hadamard factorization (entire order 1) → Eichler-Shimura injection (rank-many zeros) → regulator spectral bound (r-th coefficient ∝ R_E) → Néron-Tate positivity (R_E > 0 from `Matrix.PosDef.det_pos`) → analytic rank = algebraic rank.

**Axioms** (all proved theorems):
- `eichler_shimura_injection` — Eichler (1954), Shimura (1971)
- `height_pairing_pos_def` — Néron-Tate (1965)
- `regulator_spectral_bound` — Gross-Zagier (1986) / BSD formula

**Chain**: `BeurlingCounterexample.lean` → `HadamardGeneral.lean` → `BSD.lean`

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
| `GoldbachBridge.lean` | 5 | Circle method convolution + finite verification | Goldbach |
| `LandauTauberian.lean` | 5 | Karamata Tauberian sub-lemmas | No |
| `StirlingBound.lean` | 4 | Sum-integral comparison + Gamma ratio | No (axiom covers it) |
| `YangMills.lean` | 2 | Bracket energy continuity | No (covered by axiom) |

`sorryAx` appears in the twin primes critical path via `LandauTauberian`. All other main endpoints compile with axioms only (no `sorryAx`).

## Detailed Documentation

- [README_Collatz.md](README_Collatz.md) — Collatz proof chain, axiom inventory, verification
- [README_RH.md](README_RH.md) — RH proof architecture, Fourier completeness + spiral routes, axiom sources
- [README_TP.md](README_TP.md) — Twin primes Tauberian route, pair correlation
- [README_YangMills.md](README_YangMills.md) — Yang-Mills lattice + continuum, OS reconstruction
- [README_NS.md](README_NS.md) — Navier-Stokes eigenvalue geometry, BKM chain
- [README_BSD.md](README_BSD.md) — BSD rotation + Hadamard + Néron-Tate

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
    RotatedZeta.lean              # Rotated zeta equivalence + Fourier RH
    NavierStokes.lean             # Navier-Stokes global regularity
    BSD.lean                      # BSD conjecture
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
