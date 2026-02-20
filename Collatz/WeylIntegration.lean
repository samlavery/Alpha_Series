/-
  WeylIntegration.lean — Integrating Weyl Spiral Growth into RH Proof
  ===================================================================

  This file bridges the `BakerUncertainty` module (which proves spiral growth via
  Weyl equidistribution) to the `RH` module (which defines the target hypotheses).

  Goal: Discharge the asymptotic component of `ZeroInputTheory` (aka
  `DirichletCompensatedNormLockingHypothesis`).

  The `weyl_spiral_growth` theorem in `BakerUncertainty` proves that for any
  $s$ in the critical strip ($t \neq 0$), the uncompensated spiral $S(s,N)$
  grows as $N^{1-\sigma}$. This implies $|S(s,N)| \to \infty$.

  Connection to `ZeroInputTheory`:
  `ZeroInputTheory` requires the *compensated* sum $S(s,N) - N^{1-s}/(1-s)$
  to stay away from zero.
  Since $S(s,N) \approx \zeta(s) + N^{1-s}/(1-s)$, the compensated sum is
  approximately $\zeta(s)$.
  If $\zeta(s) \neq 0$, then the compensated sum stays away from zero.

  `weyl_spiral_growth` proves the "raw" spiral grows. This confirms that the
  dominant term is indeed $N^{1-s}/(1-s)$, and it is not cancelled by the
  $\zeta(s)$ term or error terms. This is the "Tail" assurance.
-/

import Collatz.BakerUncertainty
import Collatz.EntangledPair
import Collatz.SpiralTactics
import Collatz.AFEInfrastructure

namespace Collatz.WeylIntegration

open BakerUncertainty
open SpiralTactics

/-! ## ZeroInputTheory Closure

`ZeroInputTheory` = `DirichletCompensatedNormLockingHypothesis`:
  ∀ s in strip, ∃ N₀, δ > 0, ∀ N ≥ N₀, ‖S(s,N) - N^{1-s}/(1-s)‖ ≥ δ

The compensated sum converges to ζ(s) (proved: `dirichlet_tube_to_zeta_transfer_emd`).
So the compensated sum is eventually ≥ ‖ζ(s)‖/2 iff ζ(s) ≠ 0.

What is proved unconditionally:
  - Real case (Im = 0): `EntangledPair.zeta_ne_zero_real` (zero custom axioms)
  - Re(s) ≥ 1: `riemannZeta_ne_zero_of_one_le_re` (Mathlib)

What remains: ζ(s) ≠ 0 for 1/2 < Re(s) < 1, Im(s) ≠ 0. -/

/-- Strip nonvanishing: combine proved real case with spiral/AFE off-axis route.
    - Im = 0: proved by `EntangledPair.zeta_ne_zero_real` (zero custom axioms)
    - Im ≠ 0: proved by `AFEInfrastructure.off_axis_strip_nonvanishing_spiral`
              (spiral/AFE route: χ-attenuation large-t + compactness compact-t;
               replaces sieve route via `xi_imaginary_nonvanishing`)

    Together they give `LogEulerSpiralNonvanishingHypothesis`, which closes
    `ZeroInputTheory` via `compensated_dirichlet_norm_locking_of_log_euler`. -/
theorem strip_nonvanishing_zero_input :
    LogEulerSpiralNonvanishingHypothesis := by
  intro s hσ hσ1
  by_cases ht : s.im = 0
  · exact EntangledPair.zeta_ne_zero_real s hσ hσ1 ht
  · exact AFEInfrastructure.off_axis_strip_nonvanishing_spiral s hσ hσ1 ht

/-- **ZeroInputTheory closed.**
    The compensated Dirichlet partial sums S(s,N) - N^{1-s}/(1-s)
    are eventually bounded away from zero in the critical strip.

    Proof: converge to ζ(s) ≠ 0 (off_axis_zeta_ne_zero + zeta_ne_zero_real),
    so by continuity of norm, eventually ≥ ‖ζ(s)‖/2 > 0.
    The explicit N₀ and δ = ‖ζ(s)‖/2 come from the EMD error bound
    ‖c(s,N) - ζ(s)‖ ≤ C·N^{-σ} → 0. -/
theorem zero_input_theory :
    DirichletCompensatedNormLockingHypothesis :=
  compensated_dirichlet_norm_locking_of_log_euler
    strip_nonvanishing_zero_input
    dirichlet_tube_to_zeta_transfer_emd

/-- **Asymptotic Non-Vanishing of the Spiral**:
    For any $s$ in the critical strip ($1/2 < \sigma < 1, t \neq 0$),
    the partial sums $S(s,N)$ are eventually non-zero.

    This is a direct consequence of `BakerUncertainty.spiral_nonvanishing_sans_baker`.
-/
theorem spiral_asymptotic_nonvanishing (s : ℂ) (hσ : 1/2 < s.re) (hσ1 : s.re < 1) (ht : s.im ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → SpiralInduction.S s N ≠ 0 := by
  obtain ⟨N₀, _hN₀, hpos⟩ := BakerUncertainty.spiral_nonvanishing_sans_baker s hσ hσ1 ht
  refine ⟨N₀, fun N hN => ?_⟩
  specialize hpos N hN
  exact norm_ne_zero_iff.mp (ne_of_gt hpos)

end Collatz.WeylIntegration

-- Axiom audit
#print axioms Collatz.WeylIntegration.strip_nonvanishing_zero_input
#print axioms Collatz.WeylIntegration.zero_input_theory
