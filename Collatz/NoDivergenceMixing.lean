/-
  NoDivergenceMixing.lean
  =======================

  No-divergence proof: thin wrapper around the Baker+Tao quantitative
  contraction argument in WeylBridge.lean.

  The proof chain: WeylBridge builds a supercritical ν-sum bound and uses
  a constructive bridge to residue hitting. The mixing/M=2 machinery in
  NoDivergence.lean then yields the contradiction.

  This file packages the result as `no_divergence_via_mixing` for
  consumption by 1135.lean.
-/

import Collatz.NoDivergence

namespace Collatz

/-- Divergence contradiction via WeylBridge's constructive bridge.
    Routes through `mixing_orbit_contradiction` at M = 2, but the real proof
    is Baker+Tao quantitative contraction in WeylBridge.lean. -/
theorem divergence_contradiction_via_mixing (n₀ : ℕ) (h_n₀ : n₀ > 1) (h_odd : Odd n₀)
    (h_div : OddOrbitDivergent n₀) : False :=
  mixing_orbit_contradiction n₀ 2 h_n₀ h_odd (by omega) h_div 0
    (orbit_mod_two_ne_zero n₀ h_odd (by omega))

/-- No odd orbit is divergent (Baker+Tao contraction via WeylBridge). -/
theorem no_divergence_via_mixing (n₀ : ℕ) (h_n₀ : n₀ > 1) (h_odd : Odd n₀) :
    ¬OddOrbitDivergent n₀ :=
  fun h_div => divergence_contradiction_via_mixing n₀ h_n₀ h_odd h_div

end Collatz
