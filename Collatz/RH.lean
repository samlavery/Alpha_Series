import Collatz.SpiralBridge
import Collatz.GeometricOffAxisProof
import Collatz.EntangledPair
import Collatz.TailBound
import Collatz.WeylIntegration

/-- RH endpoint routed through `SpiralBridge`. -/
theorem riemann_hypothesis
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    RiemannHypothesis := by
  exact SpiralBridge.riemann_hypothesis_derived hcoord

/-- RH endpoint from the canonical in-project first-principles chain:
geometric coordination witness → log-Euler strip nonvanishing → RH. -/
theorem riemann_hypothesis_first_principles
    (hcoord : EntangledPair.GeometricOffAxisCoordinationHypothesis) :
    RiemannHypothesis := by
  exact SpiralBridge.riemann_hypothesis_derived_of_log_euler
    (SpiralBridge.log_euler_spiral_nonvanishing_first_principles hcoord)

/-- RH endpoint via the geometric Dirichlet interface, routed through the
compensated geometry chain (no main-term cancellation assumption). -/
theorem riemann_hypothesis_of_dirichlet_geometry
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking) :
    RiemannHypothesis := by
  exact SpiralBridge.riemann_hypothesis_derived_of_compensated_dirichlet_geometry_emd
    hlockc

/-- RH endpoint via compensated Dirichlet geometry. -/
theorem riemann_hypothesis_of_compensated_dirichlet_geometry
    (hlockc : SpiralTactics.DirichletCompensatedNormLocking) :
    RiemannHypothesis := by
  exact SpiralBridge.riemann_hypothesis_derived_of_compensated_dirichlet_geometry_emd
    hlockc

/-- RH endpoint from a no-long-resonance / transversality constructor. -/
theorem riemann_hypothesis_of_no_long_resonance
    (htrans : EntangledPair.NoLongResonanceHypothesis) :
    RiemannHypothesis := by
  exact SpiralBridge.riemann_hypothesis_derived_of_log_euler
    (SpiralBridge.log_euler_spiral_nonvanishing_of_no_long_resonance htrans)

/-- Draft RH endpoint through the Weyl tube-escape interface. -/
theorem riemann_hypothesis_of_weyl_spiral
    (hweyl : EntangledPair.WeylTubeEscapeHypothesis) :
    RiemannHypothesis := by
  exact SpiralBridge.riemann_hypothesis_derived_of_weyl_spiral hweyl

/-- RH endpoint from the varying-`N(t)` uniform proxy wrapper. -/
theorem riemann_hypothesis_of_uniform_proxy_gap_and_wobble_wrapper
    (hwrap : EntangledPair.UniformProxyGapAndWobbleWrapperHypothesis) :
    RiemannHypothesis := by
  exact riemann_hypothesis_of_weyl_spiral
    (EntangledPair.weyl_tube_escape_of_uniform_proxy_gap_and_wobble_wrapper hwrap)

/-- Endpoint equivalence: RH is equivalent to Weyl tube-escape in this
project's bridge stack. This pins the remaining closure task to constructing
`WeylTubeEscapeHypothesis` with zero arguments. -/
theorem riemann_hypothesis_iff_weyl_tube_escape :
    RiemannHypothesis ↔ EntangledPair.WeylTubeEscapeHypothesis := by
  constructor
  · intro hRH
    exact EntangledPair.weyl_tube_escape_of_off_axis_strip_nonvanishing
      (EntangledPair.off_axis_strip_nonvanishing_of_rh hRH)
  · intro hweyl
    exact riemann_hypothesis_of_weyl_spiral hweyl

/-- Equivalent endpoint phrased via no-long-resonance / transversality. -/
theorem riemann_hypothesis_iff_no_long_resonance :
    RiemannHypothesis ↔ EntangledPair.NoLongResonanceHypothesis := by
  constructor
  · intro hRH
    exact EntangledPair.no_long_resonance_of_off_axis_strip_nonvanishing
      (EntangledPair.off_axis_strip_nonvanishing_of_rh hRH)
  · intro htrans
    exact riemann_hypothesis_of_no_long_resonance htrans

/-- **Zero-input closure target.**
`DirichletCompensatedNormLockingHypothesis` asserts only that the
Euler-Maclaurin compensated Dirichlet partial sums
  `S(s,N) - N^{1-s}/(1-s)`
stay uniformly bounded away from zero for all s in the critical strip.
No `riemannZeta s ≠ 0` appears in the statement.

Why this closes RH (both directions proved with standard axioms only):
- Backward: `S(s,N) - N^{1-s}/(1-s) → ζ(s)` is proved (`dirichlet_tube_to_zeta_transfer_emd`);
  a uniform lower bound on the limit forces `ζ(s) ≠ 0`.
- Forward: if `ζ(s) ≠ 0` everywhere in the strip, the proved EMD convergence forces
  the partial sums to be eventually bounded away from zero.

Falsifiability: if ζ(s₀) = 0 for some s₀ in the critical strip, then
  `S(s₀,N) - N^{1-s₀}/(1-s₀) → ζ(s₀) = 0`,
so no `delta > 0` can serve as a lower bound for all large N, directly
contradicting this hypothesis.

Weyl Integration:
The asymptotic component of this hypothesis (for large N) is discharged by
`Collatz.WeylIntegration.spiral_asymptotic_nonvanishing`. It proves that
|S(s,N)| → ∞, so the uncompensated spiral cannot stay near zero.
This reduces the burden of `ZeroInputTheory` to:
1. Finite check for small N.
2. Convergence of the compensated sum to ζ(s) (via Geometric Coordination). -/
abbrev ZeroInputTheory : Prop :=
  SpiralTactics.DirichletCompensatedNormLockingHypothesis

/-- One-line closure: if `ZeroInputTheory` is discharged, RH follows. -/
theorem riemann_hypothesis_of_zero_input_theory
    (hzero : ZeroInputTheory) :
    RiemannHypothesis :=
  SpiralBridge.riemann_hypothesis_derived_of_compensated_dirichlet_geometry_emd hzero

/-- RH is equivalent to the zero-input theory:
ζ(s) ≠ 0 in the strip iff the Euler-Maclaurin compensated partial sums
are eventually bounded below by a positive constant. -/
theorem riemann_hypothesis_iff_zero_input_theory :
    RiemannHypothesis ↔ ZeroInputTheory := by
  constructor
  · intro hRH
    exact SpiralBridge.compensated_dirichlet_norm_locking_of_log_euler
      (SpiralBridge.log_euler_spiral_nonvanishing_of_off_axis
        (EntangledPair.off_axis_strip_nonvanishing_of_rh hRH))
  · exact riemann_hypothesis_of_zero_input_theory

/-- Canonical zero-input endpoint theorem for this repo:
RH is equivalent to the zero-input closure target. -/
theorem zero_input_theorem :
    RiemannHypothesis ↔ ZeroInputTheory :=
  riemann_hypothesis_iff_zero_input_theory

/-! ## Euler Product Route: Residual Exponential Sum

`TailBound.residual_exponential_sum_bounded` is a real-valued reformulation
of RH in terms of a prime cosine sum:

  T₁(t) = Σ_p p^{-σ} cos(t · log p) ≥ -B   for all t, fixed σ > 1/2

This is equivalent to `ZeroInputTheory` via the Euler product log-expansion.
See `Collatz/TailBound.lean` for the full score card and Vinogradov barrier
analysis. `Collatz/FloorTail.lean` contains the proved floor factor bounds.

FORMALIZATION NOTE: `TailBound.residual_exponential_sum_bounded` uses `∑'`
which equals 0 for non-summable series. The Lean statement is technically
vacuous for 1/2 < σ ≤ 1 (the critical range); a rigorous version requires
`Filter.Tendsto` on partial sums. The axiom documents the mathematical content.
-/

/-- The Euler product route to RH:
`residual_exponential_sum_bounded` asserts a uniform lower bound on the prime
cosine sum. This is real-valued (no complex analysis in the statement),
involves only primes, and is equivalent to RH.

IMPORTANT: The Lean `∑'` form is technically vacuous for 1/2 < σ ≤ 1 due to
the non-summability convention `∑' = 0`. The axiom in `TailBound.lean` records
the mathematical content; see the formalization caveat there. -/
abbrev ResidualExponentialSumBounded : Prop :=
  ∀ (σ : ℝ), 1/2 < σ → ∃ B : ℝ, ∀ (t : ℝ),
    -B ≤ ∑' (p : Nat.Primes), ((p : ℕ) : ℝ) ^ (-σ) *
      Real.cos (t * Real.log ((p : ℕ) : ℝ))

#print axioms riemann_hypothesis
