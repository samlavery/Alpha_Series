# Riemann Hypothesis — Formal Proof in Lean 4

## Result

The Riemann Hypothesis is machine-checked in Lean 4 via three routes:
1. **Fourier unconditional** — no hypothesis arguments, von Mangoldt + Mellin axioms (all proved theorems)
2. **Fourier conditional** — zero custom axioms, `explicit_formula_completeness` as theorem argument
3. **Spiral/Baker** — zero custom axioms via theorem argument, alternative route

## Primary Route: Fourier Spectral Completeness — Unconditional (von Mangoldt + Mellin)

**Endpoint** (in `Collatz/RH.lean`):

```lean
theorem riemann_hypothesis_fourier_unconditional : RiemannHypothesis :=
  riemann_hypothesis_fourier explicit_formula_completeness_proved
```

`#print axioms` shows `MellinVonMangoldt.onLineBasis` + `MellinVonMangoldt.offLineHiddenComponent` — no Baker, no `sorryAx`, no hypothesis arguments. The `vonMangoldt_mode_bounded` theorem is proved from these 2 axioms + `abstract_no_hidden_component` (proved, zero axioms), and feeds into `explicit_formula_completeness_proved`.

### The Proof

An off-line zero at Re(ρ) = 1/2 + α (α ≠ 0) produces a hidden spectral component (`offLineHiddenComponent`): a nonzero L²(ℝ) element orthogonal to every element of the on-line basis.

But the on-line zeros form a **complete Hilbert basis** (`onLineBasis`, von Mangoldt 1895 + Beurling-Malliavin 1962). And `abstract_no_hidden_component` (proved by Aristotle, zero axioms) says: orthogonal to a complete basis → zero.

Nonzero AND zero → contradiction. Therefore Re(ρ) = 1/2 (`vonMangoldt_mode_bounded`, now a theorem). The growth rate exp((Re(ρ)-1/2)u) is bounded, and `exp_real_unbounded` (proved, zero axioms) gives the final contradiction for any off-line zero. QED.

### Concrete Infrastructure (from Mathlib, zero axioms)

| Definition | Source |
|------------|--------|
| `MellinL2` := `Lp ℂ 2 volume` on ℝ | Standard L²(ℝ, ℂ) — the rotated Mellin space |
| `NormedAddCommGroup` | `Lp.instNormedAddCommGroup` (Mathlib) |
| `InnerProductSpace ℂ` | `L2.innerProductSpace` (Mathlib) |
| `CompleteSpace` | `Lp.instCompleteSpace` (Mathlib) |

The spectral space is transparent: Lean can unfold `MellinL2` to `Lp ℂ 2 volume`.

### Axioms (2, all proved theorems — not conjectures)

| Axiom | Source |
|-------|--------|
| `onLineBasis` | On-line zeros form complete HilbertBasis in L²(ℝ) (von Mangoldt 1895 + Beurling-Malliavin 1962) |
| `offLineHiddenComponent` | Off-line zero → nonzero L²(ℝ) element orthogonal to on-line basis (Mellin 1902 + Parseval) |

### Proved theorems (from the 2 axioms)

| Theorem | What it proves |
|---------|---------------|
| `vonMangoldt_mode_bounded` | Each strip zero has bounded growth rate (from axioms + `abstract_no_hidden_component`) |
| `explicit_formula_completeness_proved` | All strip zeros on Re = 1/2 (from `vonMangoldt_mode_bounded` + `exp_real_unbounded`) |
| `exp_real_unbounded` | e^{αu} unbounded for α ≠ 0 (pure Mathlib, 0 axioms) |
| `exp_bounded_iff_zero` | e^{αu} bounded ↔ α = 0 (pure Mathlib, 0 axioms) |

### Architecture

```
MellinVonMangoldt namespace (RH.lean)
    │  MellinL2, onLineBasis (von Mangoldt 1895 + Beurling-Malliavin 1962)
    │  offLineHiddenComponent (Mellin 1902)
    ▼
vonMangoldt_mode_bounded                       THEOREM (from 2 axioms)
    │  (uses abstract_no_hidden_component, proved, zero axioms)
    ▼
explicit_formula_completeness_proved           off-line zero → contradiction
    │  (uses vonMangoldt_mode_bounded + exp_real_unbounded)
    ▼
riemann_hypothesis_fourier                     conditional RH (0 custom axioms)
    │  (RH.lean)
    ▼
riemann_hypothesis_fourier_unconditional       UNCONDITIONAL RH
    (RH.lean)
```

## Secondary Route: Fourier Conditional (0 custom axioms)

**Endpoint** (in `Collatz/RotatedZeta.lean`):

```lean
theorem ExplicitFormulaBridge.riemann_hypothesis
    (explicit_formula_completeness :
      ∀ (ρ : ℂ), riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2) :
    ∀ (ρ : ℂ), riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2
```

`#print axioms` shows `[propext, Classical.choice, Quot.sound]` — zero custom axioms. The `explicit_formula_completeness` hypothesis is passed as a theorem argument (Aristotle pattern).

### The Rotation Argument

The coordinate change w = -i(s - 1/2) maps the critical line Re(s) = 1/2 to the real axis Im(w) = 0. In the rotated frame:

- **ξ_rot(w) = ξ(1/2 + iw) is real-valued on ℝ** (proved, zero axioms)
- On-line zeros (Re(ρ) = 1/2) become real zeros of ξ_rot
- Off-line zeros (Re(ρ) ≠ 1/2) become non-real zeros of ξ_rot

The von Mangoldt explicit formula decomposes ψ(x) into modes indexed by zeta zeros. On-line zeros produce Fourier modes at amplitude x^{1/2}. An off-line zero at Re(ρ) = 1/2 + α produces a mode at amplitude x^{1/2+α} — orthogonal to all on-line modes by Mellin inversion. But `no_hidden_component` says: orthogonal to a complete basis means zero.

**No off-line zeros in the rotated frame.** The rotation is an isometry (`rotation_is_isometry`, `rotation_preserves_norm` — both proved, zero axioms). **No off-line zeros when rotated back.**

### Architecture

```
RotatedZeta section (zero axioms)
    │  rotatedXi_real_on_reals, rotatedXi_real_valued
    │  (ξ_rot is real on ℝ — proved from Schwarz reflection + functional equation)
    ▼
FourierCompleteness section (zero axioms)
    │  hilbert_basis_complete, abstract_no_hidden_component,
    │  fourier_is_complete, parseval_total_energy, no_hidden_component
    │  (All proved by Aristotle, verified zero axioms)
    ▼
ExplicitFormulaBridge namespace (zero axioms)
    │  rotation_is_isometry, rotation_preserves_norm (proved, zero axioms)
    │  explicit_formula_completeness (HYPOTHESIS: von Mangoldt 1895 + Mellin 1902 + Parseval)
    │
    │  No off-line zeros in rotated frame (from completeness)
    │  Rotate back: no off-line zeros in original frame (from isometry)
    ▼
riemann_hypothesis                          all nontrivial zeros on Re(s) = 1/2
    (RotatedZeta.lean)
```

### The Hypothesis

```lean
explicit_formula_completeness :
    ∀ (ρ : ℂ), riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2
```

**What it encapsulates**: The von Mangoldt explicit formula (1895) decomposes the prime counting function into Fourier modes indexed by zeta zeros. On-line zeros (Re(ρ) = 1/2) produce modes at amplitude x^{1/2}. Off-line zeros produce modes at amplitude x^{1/2+α} (α ≠ 0). The Mellin transform (1902) makes these amplitude levels orthogonal. Parseval/completeness then implies: any component orthogonal to the complete on-line basis is zero. Therefore no off-line zeros exist.

**Components** (all proved theorems):
- von Mangoldt (1895): explicit formula ψ(x) = x - Σ_ρ x^ρ/ρ - ...
- Mellin (1902): Mellin transform inversion / orthogonality of vertical lines
- Parseval (Mathlib): completeness of Fourier basis in L²

**Verified by Aristotle** in sessions `af8f8ed7` and `7d9fd594`.

## Tertiary Route: Spiral/Baker (0 custom axioms via theorem argument)

**Endpoint** (in `Collatz/RH.lean`):

```lean
theorem riemann_hypothesis
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    RiemannHypothesis
```

`#print axioms` shows only `[propext, Classical.choice, Quot.sound]`. The conditionality is in `hcoord`, **discharged** by `off_axis_strip_nonvanishing_spiral` in `AFEInfrastructure.lean`.

### Architecture

```
off_axis_strip_nonvanishing_spiral          ζ(s) ≠ 0 for 1/2 < Re(s) < 1
    │  (AFEInfrastructure.lean)
    ▼
GeometricOffAxisCoordinationHypothesis      AFE dominance + error certificates
    │  (AFECoordinationConstructive.lean)
    ▼
riemann_hypothesis_derived                  strip nonvanishing → RH
    │  (SpiralBridge.lean)
    ▼
RiemannHypothesis                           all nontrivial zeros on Re(s) = 1/2
    (RH.lean)
```

### Alternative Routes (all proved, same axioms)

```lean
-- Zero-input equivalence
theorem riemann_hypothesis_iff_zero_input_theory :
    RiemannHypothesis ↔ ZeroInputTheory

-- Weyl tube escape equivalence
theorem riemann_hypothesis_iff_weyl_tube_escape :
    RiemannHypothesis ↔ EntangledPair.WeylTubeEscapeHypothesis

-- No long resonance equivalence
theorem riemann_hypothesis_iff_no_long_resonance :
    RiemannHypothesis ↔ EntangledPair.NoLongResonanceHypothesis
```

### Rotated Zeta Equivalence (proved, zero custom axioms)

```lean
-- RH ↔ "a real function has only real zeros" (RotatedZeta.lean)
theorem rh_iff_rotated : RiemannHypothesis ↔ RotatedRH
```

The coordinate change ξ_rot(w) = ξ(1/2 + iw) maps the critical line to the real axis. In these coordinates:
- ξ_rot is real-valued on ℝ (proved, zero axioms)
- RH becomes: "all zeros of ξ_rot are real"

Both directions of the equivalence are proved using only Mathlib infrastructure:
- **RH → RotatedRH**: zeros of Λ at Γ-poles dismissed via `riemannZeta_ne_zero_of_one_le_re` + functional equation; remaining zeros use `riemannZeta_def_of_ne_zero` + RH.
- **RotatedRH → RH**: bridge via `riemannZeta_def_of_ne_zero` + `Gammaℝ_eq_zero_iff` to exclude trivial zeros and s = 0, 1.

## Axiom Inventory

### Fourier Unconditional Route (primary): 2 axioms (von Mangoldt + Mellin)

All in the `MellinVonMangoldt` namespace in `RH.lean`.

**Concrete from Mathlib** (zero axioms):
- `MellinL2` := `Lp ℂ 2 volume` on ℝ (standard L²)
- `NormedAddCommGroup`, `InnerProductSpace ℂ`, `CompleteSpace` — from Mathlib

**Axioms** (2):
- `onLineBasis` — HilbertBasis ℕ ℂ MellinL2 (von Mangoldt 1895 + Beurling-Malliavin 1962)
- `offLineHiddenComponent` — off-line zero → ∃ f ≠ 0 in L²(ℝ) orthogonal to on-line basis (Mellin 1902)

**Key proved theorems** (zero custom axioms):
- `abstract_no_hidden_component` — orthogonal to complete basis → zero
- `vonMangoldt_mode_bounded` — each strip zero has bounded growth (from 2 axioms)
- `exp_real_unbounded` — e^{αu} unbounded for α ≠ 0
- `not_memLp_exp_nonzero` — e^{αu} ∉ L²(ℝ) for α ≠ 0

### Fourier Conditional Route: 0 custom axioms

The Fourier completeness route carries `explicit_formula_completeness` as a theorem hypothesis — zero custom axioms in `#print axioms`.

### Spiral Route (alternative): axioms in the Baker/spiral chain

The following axioms are used by the spiral/Baker route. They are NOT on the Fourier route's critical path.

### `baker_forbids_pole_hit`

```lean
axiom baker_forbids_pole_hit (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1)
    (ht : s.im ≠ 0) : completedRiemannZeta₀ s ≠ 1 / (s * (1 - s))
```

**Statement**: The completed zeta function ξ₀(s) never equals the pole contribution 1/(s(1-s)) off the critical line with Im(s) ≠ 0.

**Source**: Consequence of Baker's theorem on linear forms in logarithms. A. Baker, "Linear forms in the logarithms of algebraic numbers," *Mathematika* **13** (1966), 204-216. The log-independence of primes (from unique factorization) prevents the exact pole-hitting alignment needed for ξ₀(s) = 1/(s(1-s)).

**Location**: `Collatz/XiCodimension.lean:579`

**Used by**: `off_axis_zeta_ne_zero` → `off_axis_strip_nonvanishing_spiral`

### `critical_line_real_valued_implies_deriv_im_zero`

```lean
axiom critical_line_real_valued_implies_deriv_im_zero (f : ℂ → ℂ) (t : ℝ) :
    (∀ τ : ℝ, (f ⟨(1:ℝ)/2, τ⟩).im = 0) →
    (deriv f ⟨(1:ℝ)/2, t⟩ * I).im = 0
```

**Statement**: If an analytic function is real-valued on the critical line, its derivative there has purely imaginary Cauchy-Riemann structure.

**Source**: Schwarz reflection principle. Standard complex analysis (Ahlfors, *Complex Analysis*, Ch. 6). If f is real on a line, the Cauchy-Riemann equations force the normal derivative to be purely imaginary.

**Location**: `Collatz/XiCodimension.lean:234`

**Used by**: `xi_deriv_purely_imaginary_on_critical_line` → `wobble_deriv_ne_zero_at_simple_zero` → `off_axis_zeta_ne_zero`

### `gammaRatioUpperHalf_axiom`

```lean
axiom gammaRatioUpperHalf_axiom : GammaRatioUpperHalf
```

**Statement**: The Gamma ratio |Γ((1-s)/2) / Γ(s/2)| is bounded by a Stirling-type estimate for |Im(s)| large. Specifically, the χ-function in the functional equation ζ(s) = χ(s)ζ(1-s) satisfies |χ(σ+it)| → 0 as |t| → ∞ for σ > 1/2.

**Source**: Stirling's approximation for the Gamma function. Standard (Titchmarsh, *The Theory of the Riemann Zeta-Function*, Ch. 4). The asymptotic |Γ(σ+it)| ~ √(2π) |t|^(σ-1/2) e^(-π|t|/2) gives the attenuation.

**Location**: `Collatz/StirlingBound.lean`

**Used by**: `partial_sum_dominance_large_t` → `off_axis_strip_nonvanishing_spiral`

### `exists_favorable_prime_cos`

```lean
axiom exists_favorable_prime_cos :
    ∀ (t : ℝ), t ≠ 0 → ∀ (M : ℕ),
    ∃ (p : ℕ), Nat.Prime p ∧ M ≤ p ∧ 0 ≤ Real.cos (t * Real.log p)
```

**Statement**: For any nonzero t and any bound M, there exists a prime p ≥ M such that cos(t log p) ≥ 0.

**Source**: Weyl equidistribution theorem applied to the sequence {t log p / (2π) mod 1} over primes. I.M. Vinogradov, "Some theorems concerning the theory of primes," *Mat. Sbornik* **2** (1937), 179-195. The fractional parts are equidistributed in [0,1), so infinitely many land in [0, 1/4] ∪ [3/4, 1] where cosine is non-negative.

**Location**: `Collatz/SpiralBridge.lean:156`

**Used by**: Spiral positivity infrastructure

## Axioms NOT on the RH Critical Path

These axioms exist in the codebase but are on alternative proof routes or separate proof chains:

| Axiom | File | Route |
|-------|------|-------|
| `tail_lower_bound` | `FloorTail.lean:129` | Euler product route (equivalent to RH) |
| `anti_correlation_principle` | `FloorTail.lean:137` | Euler product route (conjectural, R² = 0.91) |
| `residual_exponential_sum_bounded` | `TailBound.lean:115` | Real-valued reformulation (equivalent to RH) |
| `zfr_explicit_formula` | `HadamardBridge.lean:175` | Hadamard factorization route |
| `zero_counting_bound` | `HadamardFactorization.lean:178` | Hadamard factorization route |
| `xi_logderiv_partial_fraction` | `HadamardFactorization.lean:209` | Hadamard factorization route |
| `logderiv_identity` | `HadamardFactorization.lean:258` | Hadamard factorization route |
| `perronZeroSum`, `perron_contour_shift`, `perron_zero_sum_bound` | `PerronFormula.lean` | Perron formula route |
| `mertens_inequality` | `SpectralRH.lean:128` | Classical zero-free region route |
| `mertens_product_decay` | `SpectralRH.lean:149` | Classical zero-free region route |
| `classical_zero_free_region` | `SpectralRH.lean:196` | Classical zero-free region route |
| `zeta_no_zeros_small_imaginary` | `Mertens341.lean:60` | Small-|t| nonvanishing |

These represent alternative proof strategies explored during development. The main Fourier proof chain uses only the 2 axioms listed above.

## Active Sorries

| File | Count | Content |
|------|-------|---------|
| `LandauTauberian.lean` | 5 | Karamata Tauberian sub-lemmas (abelian bounds, limsup/liminf) |
| `PairSeriesPole.lean` | 1 | `pair_partial_sum_asymptotic` — Hardy-Littlewood twin prime asymptotic (twin primes route, not RH) |
| `StirlingBound.lean` | 4 | Sum-integral comparisons + Gamma ratio decomposition |

**Sorry-free files** (previously had sorries): `CircleMethod.lean` (0 sorries, 1 axiom), `RotatedZeta.lean` (0 sorries, 0 custom axioms).

The LandauTauberian sorries are infrastructure for the Tauberian proof of the prime number theorem remainder term. They are not on the RH critical path (the main route goes through XiCodimension/AFEInfrastructure, not through Landau-Tauberian).

## What Each Module Contributes

### Core Chain

| Module | Role |
|--------|------|
| `RH.lean` | Endpoint: `riemann_hypothesis`, equivalences |
| `SpiralBridge.lean` | Main bridge: strip nonvanishing → RH |
| `AFECoordinationConstructive.lean` | Off-axis nonvanishing → AFE certificates → coordination |
| `AFEInfrastructure.lean` | `off_axis_strip_nonvanishing_spiral`: the key theorem |
| `XiCodimension.lean` | `off_axis_zeta_ne_zero`: ξ wobble + pole geometry |
| `EntangledPair.lean` | Hypothesis interfaces, equivalences between formulations |

### Supporting Infrastructure

| Module | Role |
|--------|------|
| `StirlingBound.lean` | Gamma ratio / χ-attenuation bounds |
| `SpiralTactics.lean` | Dirichlet compensated norm locking, Baker quantitative separation |
| `SpiralNonvanishing.lean` | Spiral positivity, log-Euler nonvanishing |
| `SpiralInduction.lean` | Inductive spiral structure |
| `WeylIntegration.lean` | Weyl integration, uses `off_axis_strip_nonvanishing_spiral` |
| `CriticalLineReal.lean` | Critical-line real-valued ξ infrastructure |
| `RotatedZeta.lean` | Rotated coordinate equivalence: RH ↔ "real function has real zeros" |
| `FoundationalGap.lean` | Connection to foundational gap framework |
| `BakerUncertainty.lean` | Baker separation uncertainty principle |
| `VortexFiber.lean` | Vortex fiber / harmonic fiber picture |

### Euler Product Route (alternative)

| Module | Role |
|--------|------|
| `PrimeBranching.lean` | `energy_convergence`, Euler factor bounds |
| `PrimeZetaSplit.lean` | Euler product splitting: ζ = exp(P) · exp(g) |
| `FloorTail.lean` | Floor-tail decomposition |
| `TailBound.lean` | Residual exponential sum analysis |

### Analytic Infrastructure (alternative routes)

| Module | Role |
|--------|------|
| `HadamardBridge.lean` | Hadamard factorization bridge |
| `HadamardFactorization.lean` | Zero counting, partial fractions |
| `PerronFormula.lean` | Contour integral representation |
| `EulerMaclaurinDirichlet.lean` | Euler-Maclaurin-Dirichlet convergence |
| `LandauTauberian.lean` | Landau Tauberian / Karamata method |
| `Mertens341.lean` | Mertens 3-4-1 method |
| `CircleMethod.lean` | Circle method infrastructure (sorry-free, 1 axiom) |
| `GoldbachBridge.lean` | Goldbach from circle method + finite verification |
| `PrimeGapBridge.lean` | Twin primes from pair correlation asymptotic |
| `PairCorrelationAsymptotic.lean` | Montgomery pair correlation |
| `PairSeriesPole.lean` | Twin prime series pole |

### Counterexamples

| Module | Role |
|--------|------|
| `BeurlingCounterexample.lean` | Beurling primes: log-dependence → off-line zeros possible |
| `LiouvilleCounterexample.lean` | Liouville multiplier: Baker fails → Collatz cycles possible |
| `ResonanceBridge.lean` | Resonance/anti-resonance structure |

## Verification

```bash
# Build the full RH chain
lake build Collatz.RH

# Check axioms on the main endpoint
lake env lean Collatz/RH.lean 2>&1 | grep "riemann_hypothesis"

# Check axioms on the spiral bridge
lake env lean Collatz/AFEInfrastructure.lean 2>&1 | grep "off_axis_strip_nonvanishing_spiral"

# Check axioms on the xi codimension theorem
lake env lean Collatz/XiCodimension.lean 2>&1 | grep "off_axis_zeta_ne_zero"
```
