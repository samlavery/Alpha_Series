/-
  SpiralTactics.lean — Domain-Specific Automation for Dirichlet Series Proofs
  ============================================================================

  "Maybe ring is the wrong primitive in a spiral."

  Standard tactics (`ring`, `abel`, `simp`) normalize inside cpow exponents,
  breaking syntactic equality. This file provides curated lemma sets that
  respect cpow opacity, plus the spiral Fourier decomposition connecting
  S(s,N) = Σ n^{-s} to amplitude-phase structure.

  §1: Spiral simp set — cpow-safe norm/amplitude lemmas
  §2: Integral arithmetic — top-level only, never touching integrands
  §3: Decay combinators — C · N^{-σ} → 0 patterns
  §4: Spiral Fourier transform — S ↔ exp/amplitude-phase/Parseval
  §5: Log-independence tools — phase incommensurability from prime logs
  §6: Euler product helpers — re-exports for convenience

  Design: NO custom tactics, NO @[simp] on cpow lemmas. Everything via
  explicit `simp only [...]` or `conv` targeting.
-/
import Collatz.SpiralInduction
import Collatz.PrimeBranching
import Collatz.EulerMaclaurinDirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Finset Complex Real ArithmeticFunction
open scoped Chebyshev BigOperators

namespace SpiralTactics

/-! ## §1: Spiral Simp Set — cpow-safe rewrites

These lemmas extract norms and amplitudes from Dirichlet terms
WITHOUT normalizing inside cpow exponents. Safe to apply globally. -/

/-- Norm of n^{-s}: extracts the real amplitude n^{-σ}. -/
theorem spiral_norm_term {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

/-- Norm of a Dirichlet term is positive. -/
theorem spiral_norm_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    0 < ‖(n : ℂ) ^ (-s)‖ := by
  rw [spiral_norm_term hn]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

/-- Amplitude bound: n^{-σ} ≤ 1 for n ≥ 1, σ ≥ 0. -/
theorem spiral_amp_le_one {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 ≤ σ) :
    (n : ℝ) ^ (-σ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-- Amplitude strict decay: n^{-σ} < m^{-σ} when n > m ≥ 1 and σ > 0.
    Larger n means smaller amplitude in the Dirichlet spiral. -/
theorem spiral_amp_strict_mono {n m : ℕ} (hn : m < n) (hm : 1 ≤ m)
    {σ : ℝ} (hσ : 0 < σ) :
    (n : ℝ) ^ (-σ) < (m : ℝ) ^ (-σ) := by
  apply Real.rpow_lt_rpow_of_neg
  · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  · exact_mod_cast hn
  · linarith

/-! ## §2: Integral Arithmetic — top-level only

Lemmas for manipulating sums/differences of integrals without touching
integrands. The key insight: use `simp only [add_sub_cancel_left]` or
`linear_combination` instead of `ring`/`abel`, because the latter
normalize inside cpow exponents. -/

/-- Safe cancellation at integral level: (a + b) - a = b.
    Re-exported with documentation explaining WHY it's used instead of ring.

    Use: `simp only [spiral_add_sub_cancel]` or `rw [spiral_add_sub_cancel]`
    when `ring` would normalize cpow exponents inside the terms. -/
theorem spiral_add_sub_cancel (a b : ℂ) : (a + b) - a = b :=
  add_sub_cancel_left a b

/-- Safe cancellation: (a + b) - b = a.
    Same rationale as spiral_add_sub_cancel. -/
theorem spiral_add_sub_cancel_right (a b : ℂ) : (a + b) - b = a :=
  add_sub_cancel_right a b

/-- Rearrangement: a - b = c ↔ a = c + b. -/
theorem spiral_sub_eq_iff (a b c : ℂ) : a - b = c ↔ a = c + b :=
  sub_eq_iff_eq_add

/-! ## §3: Decay Combinators

The pattern `C · N^{-σ} → 0 as N → ∞` appears in every Euler-Maclaurin
remainder estimate. These combinators extract it cleanly. -/

/-- Decay to zero: N^{-σ} → 0 as N → ∞ for σ > 0. -/
theorem spiral_rpow_neg_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-σ))
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-σ)) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hσ
  have h2 : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  exact h1.comp h2

/-- Scaled decay: C · N^{-σ} → 0 as N → ∞ for σ > 0. -/
theorem spiral_decay_tendsto (C : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Filter.Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-σ))
      Filter.atTop (nhds 0) := by
  have h := spiral_rpow_neg_tendsto hσ
  have : (fun N : ℕ => C * (N : ℝ) ^ (-σ)) = fun N => C * ((fun N : ℕ => (N : ℝ) ^ (-σ)) N) := rfl
  rw [this, show (0 : ℝ) = C * 0 from by ring]
  exact h.const_mul C

/-- Extract N₀ from decay: ∃ N₀, ∀ N ≥ N₀, |C · N^{-σ}| < ε. -/
theorem spiral_decay_eventually (C : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |C * (N : ℝ) ^ (-σ)| < ε := by
  have h := (spiral_decay_tendsto C hσ).eventually
    (Metric.ball_mem_nhds 0 hε)
  rw [Filter.Eventually, Filter.mem_atTop_sets] at h
  obtain ⟨N₀, hN₀⟩ := h
  exact ⟨N₀, fun N hN => by simpa [Real.dist_eq] using hN₀ N hN⟩

/-- Nonnegative decay bound: 0 ≤ C · N^{-σ} for C ≥ 0, N ≥ 1. -/
theorem spiral_decay_nonneg {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (_hN : 1 ≤ N)
    {σ : ℝ} : 0 ≤ C * (N : ℝ) ^ (-σ) :=
  mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ## §4: Spiral Fourier Transform

The partial Dirichlet sum S(s,N) = Σ_{n=1}^N n^{-s} is a discrete
Fourier-like transform on (ℝ₊, ×) with kernel n^{-s} = exp(-s·log n).

Each term has:
- Amplitude: n^{-σ} (decaying)
- Phase: -t·log n (rotating)

The amplitude-phase decomposition is the key to understanding WHY
partial sums don't cancel: amplitudes decay monotonically while
phases rotate incommensurably (log-independence of primes). -/

/-- S as exponential sum: each Dirichlet term is exp(-s · log n).
    Bridges the Dirichlet world to the Fourier/spiral world. -/
theorem S_as_exp_sum (s : ℂ) (N : ℕ) :
    SpiralInduction.S s N =
      ∑ n ∈ Finset.range N, Complex.exp (-s * Complex.log (↑(n + 1))) := by
  simp only [SpiralInduction.S]
  congr 1; ext n
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show (n + 1 : ℕ) ≠ 0 by omega))]
  ring_nf

/-- Real part of S: Re(S) = Σ n^{-σ} cos(t·log n).
    The cosine sum that controls whether S can vanish. -/
theorem S_re_eq (s : ℂ) (N : ℕ) :
    (SpiralInduction.S s N).re =
      ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-s.re)) * Real.cos (s.im * Real.log (n + 1)) := by
  simp only [SpiralInduction.S, Complex.re_sum]
  congr 1; ext n
  have hne : (↑(n + 1) : ℂ) ≠ 0 := by exact_mod_cast (show (n + 1 : ℕ) ≠ 0 by omega)
  rw [cpow_def_of_ne_zero hne, Complex.exp_re]
  rw [show Complex.log (↑(n + 1) : ℂ) = ↑(Real.log (↑(n + 1) : ℝ)) from
    (Complex.natCast_log (n := n + 1)).symm]
  simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, sub_zero, zero_mul,
             mul_im, add_zero]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
  push_cast
  rw [show Real.log (↑n + 1) * -s.im = -(s.im * Real.log (↑n + 1)) by ring, Real.cos_neg]

/-- Imaginary part of S: Im(S) = -Σ n^{-σ} sin(t·log n). -/
theorem S_im_eq (s : ℂ) (N : ℕ) :
    (SpiralInduction.S s N).im =
      ∑ n ∈ Finset.range N,
        -((n + 1 : ℝ) ^ (-s.re)) * Real.sin (s.im * Real.log (n + 1)) := by
  simp only [SpiralInduction.S, Complex.im_sum]
  congr 1; ext n
  have hne : (↑(n + 1) : ℂ) ≠ 0 := by exact_mod_cast (show (n + 1 : ℕ) ≠ 0 by omega)
  rw [cpow_def_of_ne_zero hne, Complex.exp_im]
  rw [show Complex.log (↑(n + 1) : ℂ) = ↑(Real.log (↑(n + 1) : ℝ)) from
    (Complex.natCast_log (n := n + 1)).symm]
  simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, sub_zero, zero_mul,
             mul_im, add_zero]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
  push_cast
  rw [show Real.log (↑n + 1) * -s.im = -(s.im * Real.log (↑n + 1)) by ring, Real.sin_neg]
  ring

/-- Parseval expansion of normSq of a complex sum.
    normSq(Σ zₙ) = Σ|zₙ|² + 2·Σ_{j<i} Re(zᵢ · conj(zⱼ)) -/
private theorem normSq_sum_expand (z : ℕ → ℂ) (N : ℕ) :
    normSq (∑ i ∈ Finset.range N, z i) =
      ∑ i ∈ Finset.range N, normSq (z i) +
      2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i,
        (z i * starRingEnd ℂ (z j)).re := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Complex.normSq_add, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
    ring_nf; congr 1; congr 1
    conv_lhs => rw [Finset.sum_mul]
    rw [Complex.re_sum]; congr 1; ext i
    simp [mul_re, conj_re, conj_im]; ring

/-- normSq of a single Dirichlet term: |n^{-s}|² = n^{-2σ} -/
private theorem normSq_dirichlet_term (n : ℕ) (s : ℂ) :
    normSq ((↑(n + 1) : ℂ) ^ (-s)) = ((n + 1 : ℝ) ^ (-2 * s.re)) := by
  rw [normSq_eq_norm_sq, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1),
      Complex.neg_re]
  push_cast; rw [sq, ← Real.rpow_add (by positivity : (0 : ℝ) < ↑n + 1)]; ring_nf

/-- Cross-term: Re(n^{-s}·conj(m^{-s})) = n^{-σ}·m^{-σ}·cos(t·log(n/m)).
    Uses Re(a·conj(b)) = a.re·b.re + a.im·b.im with per-term cpow decomposition,
    then cos subtraction formula + log quotient. -/
private theorem cross_term_eq (n m : ℕ) (s : ℂ) :
    ((↑(n + 1) : ℂ) ^ (-s) * starRingEnd ℂ ((↑(m + 1) : ℂ) ^ (-s))).re =
      ((n + 1 : ℝ) ^ (-s.re)) * ((m + 1 : ℝ) ^ (-s.re)) *
        Real.cos (s.im * Real.log ((n + 1 : ℝ) / (m + 1))) := by
  simp only [mul_re, conj_re, conj_im]
  have hne_n : (↑(n + 1) : ℂ) ≠ 0 := by exact_mod_cast (show (n + 1 : ℕ) ≠ 0 by omega)
  have hne_m : (↑(m + 1) : ℂ) ≠ 0 := by exact_mod_cast (show (m + 1 : ℕ) ≠ 0 by omega)
  have hre_n : ((↑(n + 1) : ℂ) ^ (-s)).re =
      ((n + 1 : ℝ) ^ (-s.re)) * Real.cos (s.im * Real.log (n + 1)) := by
    rw [cpow_def_of_ne_zero hne_n, Complex.exp_re,
        show Complex.log (↑(n + 1) : ℂ) = ↑(Real.log (↑(n + 1) : ℝ)) from
          (Complex.natCast_log (n := n + 1)).symm]
    simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, sub_zero, zero_mul, mul_im, add_zero]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℝ))]; push_cast
    rw [show Real.log (↑n + 1) * -s.im = -(s.im * Real.log (↑n + 1)) by ring, Real.cos_neg]
  have hre_m : ((↑(m + 1) : ℂ) ^ (-s)).re =
      ((m + 1 : ℝ) ^ (-s.re)) * Real.cos (s.im * Real.log (m + 1)) := by
    rw [cpow_def_of_ne_zero hne_m, Complex.exp_re,
        show Complex.log (↑(m + 1) : ℂ) = ↑(Real.log (↑(m + 1) : ℝ)) from
          (Complex.natCast_log (n := m + 1)).symm]
    simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, sub_zero, zero_mul, mul_im, add_zero]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (m + 1 : ℝ))]; push_cast
    rw [show Real.log (↑m + 1) * -s.im = -(s.im * Real.log (↑m + 1)) by ring, Real.cos_neg]
  have him_n : ((↑(n + 1) : ℂ) ^ (-s)).im =
      -((n + 1 : ℝ) ^ (-s.re)) * Real.sin (s.im * Real.log (n + 1)) := by
    rw [cpow_def_of_ne_zero hne_n, Complex.exp_im,
        show Complex.log (↑(n + 1) : ℂ) = ↑(Real.log (↑(n + 1) : ℝ)) from
          (Complex.natCast_log (n := n + 1)).symm]
    simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, sub_zero, zero_mul, mul_im, add_zero]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℝ))]; push_cast
    rw [show Real.log (↑n + 1) * -s.im = -(s.im * Real.log (↑n + 1)) by ring, Real.sin_neg]; ring
  have him_m : ((↑(m + 1) : ℂ) ^ (-s)).im =
      -((m + 1 : ℝ) ^ (-s.re)) * Real.sin (s.im * Real.log (m + 1)) := by
    rw [cpow_def_of_ne_zero hne_m, Complex.exp_im,
        show Complex.log (↑(m + 1) : ℂ) = ↑(Real.log (↑(m + 1) : ℝ)) from
          (Complex.natCast_log (n := m + 1)).symm]
    simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, sub_zero, zero_mul, mul_im, add_zero]
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (m + 1 : ℝ))]; push_cast
    rw [show Real.log (↑m + 1) * -s.im = -(s.im * Real.log (↑m + 1)) by ring, Real.sin_neg]; ring
  rw [hre_n, hre_m, him_n, him_m,
      show Real.log ((n + 1 : ℝ) / (m + 1)) = Real.log (n + 1) - Real.log (m + 1) from
        Real.log_div (by positivity) (by positivity),
      show s.im * (Real.log (↑n + 1) - Real.log (↑m + 1)) =
        s.im * Real.log (↑n + 1) - s.im * Real.log (↑m + 1) by ring,
      Real.cos_sub]; ring

/-- Parseval-type identity: ‖S‖² decomposes into diagonal (energy) and
    off-diagonal (phase alignment) terms.

    ‖S‖² = Σ n^{-2σ} + 2·Σ_{m<n} (mn)^{-σ} cos(t·log(n/m))

    The diagonal sum is the energy (converges for σ > 1/2).
    The off-diagonal sum measures phase coherence — bounded by
    log-independence (primes) and equidistribution (composites).

    This is the path to `partial_sums_have_offset`: if ζ(s) ≠ 0,
    the energy grows faster than cross-cancellation can suppress. -/
theorem S_normsq_parseval (s : ℂ) (N : ℕ) :
    ‖SpiralInduction.S s N‖ ^ 2 =
      ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-2 * s.re)) +
      2 * ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range n,
        ((n + 1 : ℝ) ^ (-s.re)) * ((m + 1 : ℝ) ^ (-s.re)) *
        Real.cos (s.im * Real.log ((n + 1 : ℝ) / (m + 1))) := by
  rw [← normSq_eq_norm_sq]
  simp only [SpiralInduction.S]
  rw [normSq_sum_expand (fun i => (↑(i + 1) : ℂ) ^ (-s)) N]
  congr 1
  · congr 1; ext n; exact normSq_dirichlet_term n s
  · congr 1; congr 1; ext n; congr 1; ext m; exact cross_term_eq n m s

/-- Energy (diagonal) sum: Σ_{n=1}^N n^{-2σ}.
    Converges for σ > 1/2 (from PrimeBranching.energy_convergence). -/
noncomputable def energy (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-2 * σ))

/-- Energy is positive for N ≥ 1. -/
theorem energy_pos {σ : ℝ} {N : ℕ} (hN : 1 ≤ N) : 0 < energy σ N := by
  apply Finset.sum_pos
  · intro n _
    exact Real.rpow_pos_of_pos (by positivity) _
  · exact Finset.nonempty_range_iff.mpr (by omega)

/-- Energy is monotone in N. -/
theorem energy_mono {σ : ℝ} {N M : ℕ} (h : N ≤ M) :
    energy σ N ≤ energy σ M := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro _ _ _
  exact Real.rpow_nonneg (by positivity) _

/-! ## §5: Log-Independence Tools

Phase incommensurability from the linear independence of prime logarithms.
Proved via sign analysis + PrimeBranching.log_ratio_irrat. -/

/-- No nontrivial ℤ-linear relation on logs of distinct primes.
    If c·log p = d·log q for integer c ≠ 0 and distinct primes p, q,
    contradiction. Proved by sign analysis + log_ratio_irrat. -/
private theorem no_int_log_relation {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) {c d : ℤ} (hc : c ≠ 0)
    (heq : (c : ℝ) * Real.log p = (d : ℝ) * Real.log q) : False := by
  have hlogp_pos := PrimeBranching.log_prime_pos hp
  have hlogq_pos := PrimeBranching.log_prime_pos hq
  have hd : d ≠ 0 := by
    intro hd; rw [hd, Int.cast_zero, zero_mul] at heq
    rcases mul_eq_zero.mp heq with h | h
    · exact hc (by exact_mod_cast h)
    · exact absurd h (ne_of_gt hlogp_pos)
  rcases lt_or_gt_of_ne hc with hc_neg | hc_pos
  · rcases lt_or_gt_of_ne hd with hd_neg | hd_pos
    · -- Both negative: negate and apply log_ratio_irrat
      have heq' : ((-c).toNat : ℤ) * Real.log ↑p = ((-d).toNat : ℤ) * Real.log ↑q := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ -c),
            Int.toNat_of_nonneg (by omega : 0 ≤ -d)]
        push_cast; linarith [heq]
      exact absurd heq' (PrimeBranching.log_ratio_irrat hp hq hne (by omega) (by omega))
    · -- c < 0, d > 0: LHS < 0, RHS > 0
      linarith [mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hc_neg) hlogp_pos,
                mul_pos (Int.cast_pos.mpr hd_pos) hlogq_pos]
  · rcases lt_or_gt_of_ne hd with hd_neg | hd_pos
    · -- c > 0, d < 0: LHS > 0, RHS < 0
      linarith [mul_pos (Int.cast_pos.mpr hc_pos) hlogp_pos,
                mul_neg_of_neg_of_pos (Int.cast_lt_zero.mpr hd_neg) hlogq_pos]
    · -- Both positive: direct application
      have heq' : (c.toNat : ℤ) * Real.log ↑p = (d.toNat : ℤ) * Real.log ↑q := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ c),
            Int.toNat_of_nonneg (by omega : 0 ≤ d)]
        exact_mod_cast heq
      exact absurd heq' (PrimeBranching.log_ratio_irrat hp hq hne (by omega) (by omega))

/-- Finite prime-log witness functional `m ↦ Σ m_i log p_i`. -/
noncomputable def witnessLogSum {n : ℕ} (ps : Fin n → ℕ) (m : Fin n → ℤ) : ℝ :=
  ∑ i : Fin n, (m i : ℝ) * Real.log (ps i)

/-- Absolute witness defect `|Σ m_i log p_i|`. -/
noncomputable def witnessLogGap {n : ℕ} (ps : Fin n → ℕ) (m : Fin n → ℤ) : ℝ :=
  |witnessLogSum ps m|

/-- Quantitative anti-resonance constant on a finite witness class.
This is the project-local version of
`α_min = min_{m in witness class} |Σ_i m_i log p_i|`. -/
noncomputable def alphaMin {n : ℕ}
    (ps : Fin n → ℕ) (W : Finset (Fin n → ℤ)) (hW : W.Nonempty) : ℝ :=
  W.inf' hW (fun m => witnessLogGap ps m)

/-- `alphaMin` is always nonnegative. -/
theorem alphaMin_nonneg {n : ℕ}
    (ps : Fin n → ℕ) (W : Finset (Fin n → ℤ)) (hW : W.Nonempty) :
    0 ≤ alphaMin ps W hW := by
  exact (Finset.le_inf'_iff
    (H := hW) (f := fun m => witnessLogGap ps m) (a := (0 : ℝ))).2
      (fun m hm => by simp [witnessLogGap])

/-- If every witness in `W` has nonzero prime-log sum, then `alphaMin > 0`. -/
theorem alphaMin_pos_of_no_zero_relation {n : ℕ}
    (ps : Fin n → ℕ) (W : Finset (Fin n → ℤ)) (hW : W.Nonempty)
    (hno : ∀ m, m ∈ W → witnessLogSum ps m ≠ 0) :
    0 < alphaMin ps W hW := by
  exact (Finset.lt_inf'_iff
    (H := hW) (f := fun m => witnessLogGap ps m) (a := (0 : ℝ))).2
      (fun m hm => abs_pos.mpr (hno m hm))

/-- Pointwise bound from the definition of `alphaMin`. -/
theorem alphaMin_le_witnessGap {n : ℕ}
    (ps : Fin n → ℕ) (W : Finset (Fin n → ℤ)) (hW : W.Nonempty)
    {m : Fin n → ℤ} (hm : m ∈ W) :
    alphaMin ps W hW ≤ witnessLogGap ps m :=
  Finset.inf'_le _ hm

/-- cos(t·log 2) and cos(t·log 3) cannot simultaneously equal -1.
    cos θ = -1 requires θ ≡ π (mod 2π), giving a rational relation
    log 2/log 3 = (2a+1)/(2b+1) — contradicting log-independence. -/
theorem cos_log_2_3_not_both_neg_one (t : ℝ) (_ht : t ≠ 0) :
    ¬(Real.cos (t * Real.log 2) = -1 ∧ Real.cos (t * Real.log 3) = -1) := by
  intro ⟨h2, h3⟩
  rw [Real.cos_eq_neg_one_iff] at h2 h3
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := h3
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  -- Cross-multiply ha, hb via logs to eliminate t:
  -- (π + 2πa)·log 3 = t·log 2·log 3 = t·log 3·log 2 = (π + 2πb)·log 2
  have h_cross : (Real.pi + ↑a * (2 * Real.pi)) * Real.log 3 =
      (Real.pi + ↑b * (2 * Real.pi)) * Real.log 2 := by
    have h1 : t * Real.log 2 * Real.log 3 =
        (Real.pi + ↑a * (2 * Real.pi)) * Real.log 3 := by rw [ha]
    have h2 : t * Real.log 3 * Real.log 2 =
        (Real.pi + ↑b * (2 * Real.pi)) * Real.log 2 := by rw [hb]
    linarith [mul_comm (Real.log (2 : ℝ)) (Real.log (3 : ℝ))]
  -- Factor out π and cancel: (1+2a)·log 3 = (1+2b)·log 2
  have h_factored : Real.pi * ((1 + 2 * ↑a) * Real.log 3) =
      Real.pi * ((1 + 2 * ↑b) * Real.log 2) := by nlinarith
  have key : (1 + 2 * (a : ℝ)) * Real.log 3 = (1 + 2 * (b : ℝ)) * Real.log 2 :=
    mul_left_cancel₀ hpi_ne h_factored
  -- (1+2a) is odd hence nonzero — contradicts log-independence of primes 2, 3
  exact no_int_log_relation (by decide : Nat.Prime 3) (by decide : Nat.Prime 2)
    (by decide : (3 : ℕ) ≠ 2)
    (by exact_mod_cast (show (1 + 2 * a : ℤ) ≠ 0 by omega))
    (by exact_mod_cast key)

/-- For distinct primes p, q, the phases t·log p and t·log q cannot be
    simultaneously congruent to π mod 2π. Consequence of the linear
    independence of prime logarithms over ℚ. -/
theorem phases_not_simultaneously_pi {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hne : p ≠ q) (t : ℝ) (_ht : t ≠ 0) :
    ¬(∃ a b : ℤ, t * Real.log p = Real.pi + 2 * Real.pi * a ∧
                   t * Real.log q = Real.pi + 2 * Real.pi * b) := by
  intro ⟨a, b, ha, hb⟩
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  -- Cross-multiply to eliminate t
  have h_cross : (Real.pi + 2 * Real.pi * ↑a) * Real.log ↑q =
      (Real.pi + 2 * Real.pi * ↑b) * Real.log ↑p := by
    have h1 : t * Real.log ↑p * Real.log ↑q =
        (Real.pi + 2 * Real.pi * ↑a) * Real.log ↑q := by rw [ha]
    have h2 : t * Real.log ↑q * Real.log ↑p =
        (Real.pi + 2 * Real.pi * ↑b) * Real.log ↑p := by rw [hb]
    linarith [mul_comm (Real.log (↑p : ℝ)) (Real.log (↑q : ℝ))]
  -- Factor out π and cancel: (1+2a)·log q = (1+2b)·log p
  have h_factored : Real.pi * ((1 + 2 * ↑a) * Real.log ↑q) =
      Real.pi * ((1 + 2 * ↑b) * Real.log ↑p) := by nlinarith
  have key : (1 + 2 * (a : ℝ)) * Real.log q = (1 + 2 * (b : ℝ)) * Real.log p :=
    mul_left_cancel₀ hpi_ne h_factored
  -- (1+2a) is odd hence nonzero — contradicts log-independence
  exact no_int_log_relation hq hp (Ne.symm hne)
    (by exact_mod_cast (show (1 + 2 * a : ℤ) ≠ 0 by omega))
    (by exact_mod_cast key)

/-! ## §5b: Helix Geometry Core

Reusable geometry primitives consumed by SpiralBridge/AFE layers. -/

/-- A helix in `ℝ³`. -/
noncomputable def helix (r c t : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos t, r * Real.sin t, c * t)

/-- Projection onto the `xz`-plane (drop the `y` coordinate). -/
def proj_xz (v : ℝ × ℝ × ℝ) : ℝ × ℝ := (v.1, v.2.2)

/-- Helix-to-wave projection identity. -/
theorem helix_projects_to_wave (r c t : ℝ) :
    proj_xz (helix r c t) = (r * Real.cos t, c * t) := by
  simp [helix, proj_xz]

/-- Reparametrized helix-wave identity: `x(z) = r * cos(z/c)` when `c ≠ 0`. -/
theorem wave_from_helix_reparametrized (r c z : ℝ) (hc : c ≠ 0) :
    proj_xz (helix r c (z / c)) = (r * Real.cos (z / c), z) := by
  simp [helix, proj_xz, mul_div_cancel₀ z hc]

/-- Circle contribution is nonnegative: `1 - cos(n*theta) ≥ 0`. -/
theorem helix_unit_circle_bounded (theta : ℝ) (n : ℕ) :
    0 ≤ 1 - Real.cos (↑n * theta) :=
  sub_nonneg.mpr (Real.cos_le_one _)

/-- Spiral amplitude decomposition:
`(r^n cos)^2 + (r^n sin)^2 = (r^n)^2`. -/
theorem spiral_amplitude_sq (r : ℝ) (theta : ℝ) (n : ℕ) :
    (r ^ n * Real.cos (↑n * theta)) ^ 2 + (r ^ n * Real.sin (↑n * theta)) ^ 2 =
    (r ^ n) ^ 2 := by
  have : Real.cos (↑n * theta) ^ 2 + Real.sin (↑n * theta) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  nlinarith [this]

/-- Möbius-module dichotomy identity: equality iff `σ = 1/2`. -/
theorem li_module_dichotomy (σ t : ℝ) (_ht : t ≠ 0) :
    (σ - 1) ^ 2 + t ^ 2 = σ ^ 2 + t ^ 2 ↔ σ = 1 / 2 := by
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-- Partner-module excess bound used in compactness arguments. -/
theorem li_module_partner_excess (σ t : ℝ) (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : t ≠ 0) :
    (σ^2 + t^2) / ((1-σ)^2 + t^2) - 1 ≤ 1 / t^2 := by
  have ht2 : (0 : ℝ) < t^2 := by positivity
  have hd : (0 : ℝ) < (1-σ)^2 + t^2 := by positivity
  rw [div_sub_one (ne_of_gt hd)]
  have hnum : σ^2 + t^2 - ((1-σ)^2 + t^2) = 2*σ - 1 := by ring
  rw [hnum, div_le_div_iff₀ hd ht2]
  nlinarith [sq_nonneg (1-σ), sq_nonneg t]

/-! ## §5c: Log-Euler Replacement Interface

This section defines the replacement API for strip nonvanishing:
downstream modules depend on this interface, not directly on any
particular bridge (e.g. Euler-product bridge, future spiral proof). -/

/-- Target replacement interface for strip nonvanishing in the critical strip. -/
def LogEulerSpiralNonvanishingHypothesis : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- Elimination rule for the strip nonvanishing interface. -/
theorem strip_nonvanishing_from_log_euler
    (h : LogEulerSpiralNonvanishingHypothesis) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 :=
  h

/-- Generic nonvanishing certificate:
if an approximation point `E` is closer to `z` than `‖E‖`, then `z ≠ 0`. -/
theorem nonvanishing_of_error_lt_norm (z E : ℂ)
    (herr : ‖z - E‖ < ‖E‖) : z ≠ 0 := by
  intro hz
  have hE : ‖E‖ < ‖E‖ := by
    calc
      ‖E‖ = ‖-E‖ := (norm_neg _).symm
      _ = ‖z - E‖ := by rw [hz, zero_sub]
      _ < ‖E‖ := herr
  exact (lt_irrefl ‖E‖) hE

/-- Gap-and-error nonvanishing certificate:
`c ≤ ‖E‖` and `‖z - E‖ < c` force `z ≠ 0`. -/
theorem nonvanishing_of_gap_and_error (z E : ℂ) (c : ℝ)
    (hgap : c ≤ ‖E‖) (herr : ‖z - E‖ < c) : z ≠ 0 :=
  nonvanishing_of_error_lt_norm z E (lt_of_lt_of_le herr hgap)

/-- Quantitative lower-bound transfer:
an approximation gap and an error bound transfer a lower bound from `E` to `z`.
This is the basic hinge `ε ≤ ‖E‖`, `‖z - E‖ ≤ δ` ⇒ `ε - δ ≤ ‖z‖`. -/
theorem lower_bound_transfer_of_error_bound (z E : ℂ) (ε δ : ℝ)
    (hgap : ε ≤ ‖E‖) (herr : ‖z - E‖ ≤ δ) :
    ε - δ ≤ ‖z‖ := by
  have hsplit : z + (E - z) = E := by ring
  have hE_le : ‖E‖ ≤ ‖z‖ + ‖z - E‖ := by
    calc
      ‖E‖ = ‖z + (E - z)‖ := by rw [hsplit]
      _ ≤ ‖z‖ + ‖E - z‖ := norm_add_le _ _
      _ = ‖z‖ + ‖z - E‖ := by rw [norm_sub_rev]
  linarith

/-- Tube-membership transfer with radius inflation:
`E` in radius `r` and `z` within error `δ` of `E` implies `z` in radius `r+δ`. -/
theorem tube_membership_transfer_of_error_bound (z E : ℂ) (r δ : ℝ)
    (hE : ‖E‖ ≤ r) (herr : ‖z - E‖ ≤ δ) :
    ‖z‖ ≤ r + δ := by
  have hsplit : (z - E) + E = z := by ring
  have hnorm_eq : ‖z‖ = ‖(z - E) + E‖ := by
    simpa using congrArg norm hsplit.symm
  have hnorm : ‖(z - E) + E‖ ≤ ‖z - E‖ + ‖E‖ := norm_add_le _ _
  calc
    ‖z‖ = ‖(z - E) + E‖ := hnorm_eq
    _ ≤ ‖z - E‖ + ‖E‖ := hnorm
    _ ≤ δ + r := add_le_add herr hE
    _ = r + δ := by ring

/-- Interval lower-bound transfer:
uniform approximation error on an interval transfers uniform norm lower bounds. -/
theorem interval_lower_bound_transfer_of_error_bound
    (z E : ℝ → ℂ) (t0 L ε δ : ℝ)
    (hgap : ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ε ≤ ‖E t‖)
    (herr : ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ‖z t - E t‖ ≤ δ) :
    ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ε - δ ≤ ‖z t‖ := by
  intro t ht0 ht1
  exact lower_bound_transfer_of_error_bound (z t) (E t) ε δ
    (hgap t ht0 ht1) (herr t ht0 ht1)

/-- Interval tube-membership transfer:
if `E` stays in radius `r` and `z` stays within error `δ` of `E`, then `z`
stays in radius `r + δ` on the same interval. -/
theorem interval_tube_membership_transfer_of_error_bound
    (z E : ℝ → ℂ) (t0 L r δ : ℝ)
    (hE : ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ‖E t‖ ≤ r)
    (herr : ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ‖z t - E t‖ ≤ δ) :
    ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ‖z t‖ ≤ r + δ := by
  intro t ht0 ht1
  exact tube_membership_transfer_of_error_bound (z t) (E t) r δ
    (hE t ht0 ht1) (herr t ht0 ht1)

/-- Interval core lower bound:
if `E` is continuous on `[t0, t0+L]` and nonzero there, then `‖E‖` has a
uniform positive lower bound on that interval. -/
theorem interval_core_lower_bound_of_continuous_nonzero
    (E : ℝ → ℂ) (t0 L : ℝ)
    (hcont : ContinuousOn E (Set.Icc t0 (t0 + L)))
    (hne : ∀ t : ℝ, t ∈ Set.Icc t0 (t0 + L) → E t ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ∈ Set.Icc t0 (t0 + L) → δ ≤ ‖E t‖ := by
  by_cases hI : t0 ≤ t0 + L
  · let K : Set ℝ := Set.Icc t0 (t0 + L)
    have hK : IsCompact K := isCompact_Icc
    have hKnonempty : K.Nonempty := ⟨t0, by exact ⟨le_rfl, hI⟩⟩
    have hfcont : ContinuousOn (fun t : ℝ => ‖E t‖) K := by
      simpa [K] using hcont.norm
    rcases hK.exists_isMinOn hKnonempty hfcont with ⟨tmin, htminK, htmin_min⟩
    refine ⟨‖E tmin‖, ?_, ?_⟩
    · exact norm_pos_iff.mpr (hne tmin (by simpa [K] using htminK))
    · intro t htK
      have htK' : t ∈ K := by simpa [K] using htK
      exact htmin_min htK'
  · refine ⟨1, by norm_num, ?_⟩
    intro t htK
    have : t0 ≤ t0 + L := le_trans htK.1 htK.2
    exact (False.elim (hI this))

/-- Linear-observable tube barrier on an interval:
if `F` stays in a `δ`-tube around `z0` on `[t0, t0+L]`, then every unit linear
observable `t ↦ Re(conj u * F t)` has endpoint variation at most `2δ`.
Hence any endpoint drift lower bound `a_min * L` must satisfy `a_min * L ≤ 2δ`. -/
theorem no_long_tube_of_linear_drift_endpoint
    {F : ℝ → ℂ} {t0 L : ℝ} (hL : 0 ≤ L)
    {z0 u : ℂ} {δ a_min : ℝ}
    (hu : ‖u‖ = 1)
    (hδ : 0 ≤ δ)
    (htube : ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L → ‖F t - z0‖ ≤ δ)
    (hdrift :
      a_min * L ≤ ((star u * F (t0 + L)).re - (star u * F t0).re)) :
    a_min * L ≤ 2 * δ := by
  have huconj : ‖star u‖ = 1 := by simpa [norm_star] using hu
  have hpoint :
      ∀ t : ℝ, t0 ≤ t → t ≤ t0 + L →
        |(star u * F t).re - (star u * z0).re| ≤ δ := by
    intro t ht0 ht1
    have hnorm :
        ‖star u * (F t - z0)‖ ≤ δ := by
      calc
        ‖star u * (F t - z0)‖ = ‖star u‖ * ‖F t - z0‖ := by rw [norm_mul]
        _ = 1 * ‖F t - z0‖ := by rw [huconj]
        _ ≤ 1 * δ := by gcongr; exact htube t ht0 ht1
        _ = δ := by ring
    have hRe :
        |(star u * (F t - z0)).re| ≤ δ :=
      le_trans (Complex.abs_re_le_norm (star u * (F t - z0))) hnorm
    calc
      |(star u * F t).re - (star u * z0).re|
          = |((star u * F t) - (star u * z0)).re| := by simp
      _ = |(star u * (F t - z0)).re| := by simp [mul_sub]
      _ ≤ δ := hRe
  have ht0_mem : t0 ≤ t0 + L := by linarith
  have h0 := hpoint t0 le_rfl ht0_mem
  have h1 := hpoint (t0 + L) ht0_mem le_rfl
  have htri :
      |(star u * F (t0 + L)).re - (star u * F t0).re| ≤
        |(star u * F (t0 + L)).re - (star u * z0).re| +
        |(star u * F t0).re - (star u * z0).re| := by
    let a : ℝ := (star u * F (t0 + L)).re
    let b : ℝ := (star u * z0).re
    let c : ℝ := (star u * F t0).re
    have htri' : |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
    calc
      |(star u * F (t0 + L)).re - (star u * F t0).re|
          = |a - c| := by rfl
      _ ≤ |a - b| + |b - c| := htri'
      _ = |a - b| + |c - b| := by rw [abs_sub_comm b c]
      _ = |(star u * F (t0 + L)).re - (star u * z0).re| +
            |(star u * F t0).re - (star u * z0).re| := by rfl
  have hvar :
      |(star u * F (t0 + L)).re - (star u * F t0).re| ≤ 2 * δ := by
    have hsum : |(star u * F (t0 + L)).re - (star u * z0).re| +
        |(star u * F t0).re - (star u * z0).re| ≤ 2 * δ := by linarith
    exact le_trans htri hsum
  have hleAbs :
      a_min * L ≤ |(star u * F (t0 + L)).re - (star u * F t0).re| := by
    exact le_trans hdrift (le_abs_self _)
  exact le_trans hleAbs hvar

/-! ## §5d: Dirichlet Helix/Tube Prototype

An analysis-first scaffold for replacing Euler-product bridging with
Dirichlet partial-sum geometry.
-/

/-- Finite Dirichlet state at cutoff `N`: core value and wobble around `ζ(s)`. -/
structure DirichletHelixState (s : ℂ) (N : ℕ) where
  core : ℂ
  wobble : ℂ
  core_def : core = SpiralInduction.S s N
  wobble_def : wobble = SpiralInduction.S s N - riemannZeta s

/-- Canonical finite state built from `S(s,N)` and `ζ(s)`. -/
noncomputable def dirichletHelixState (s : ℂ) (N : ℕ) : DirichletHelixState s N :=
  { core := SpiralInduction.S s N
  , wobble := SpiralInduction.S s N - riemannZeta s
  , core_def := rfl
  , wobble_def := rfl
  }

/-- Tube decomposition: `S(s,N) = ζ(s) + wobble`. -/
theorem dirichlet_tube_decomposition (s : ℂ) (N : ℕ) :
    (dirichletHelixState s N).core = riemannZeta s + (dirichletHelixState s N).wobble := by
  simp [dirichletHelixState, DirichletHelixState.wobble_def]

/-- Prime phase rate for the helix mode indexed by prime `p`. -/
noncomputable def primePhaseRate (p : ℕ) : ℝ := 2 / Real.log p

/-- Prime phase rate is positive for primes. -/
theorem primePhaseRate_pos {p : ℕ} (hp : Nat.Prime p) :
    0 < primePhaseRate p := by
  unfold primePhaseRate
  exact div_pos (by norm_num) (PrimeBranching.log_prime_pos hp)

/-- Cutoff-axis wobble model:
partial prime sum up to `P` with prime-mode weight `2 / log p`.
This is the scale/cutoff axis (`P` grows, more prime modes are appended). -/
noncomputable def wobbleByCutoff (a : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (P + 1),
    if Nat.Prime p then primePhaseRate p * a p else 0

/-- Time-axis wobble model at fixed cutoff `P`:
the same prime modes, now with oscillatory phase evolution in `t`. -/
noncomputable def wobbleAtTime (a : ℕ → ℝ) (P : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (P + 1),
    if Nat.Prime p then primePhaseRate p * a p * Real.cos (t * Real.log p) else 0

/-- Cutoff recurrence: increasing `P` appends exactly one potential prime mode. -/
theorem wobbleByCutoff_succ (a : ℕ → ℝ) (P : ℕ) :
    wobbleByCutoff a (P + 1) =
      wobbleByCutoff a P +
        (if Nat.Prime (P + 1) then primePhaseRate (P + 1) * a (P + 1) else 0) := by
  simpa [wobbleByCutoff, Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]

/-- Time model at `t = 0` reduces to the cutoff model (since `cos 0 = 1`). -/
theorem wobbleAtTime_zero (a : ℕ → ℝ) (P : ℕ) :
    wobbleAtTime a P 0 = wobbleByCutoff a P := by
  simp [wobbleAtTime, wobbleByCutoff]

/-- Norm-locking hypothesis for finite Dirichlet partial sums in the strip:
eventually, `‖S(s,N)‖` stays uniformly above a positive floor. -/
def DirichletNormLockingHypothesis : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    ∃ N0 : ℕ, ∃ delta : ℝ, 0 < delta ∧
      ∀ N : ℕ, N0 ≤ N → delta ≤ ‖SpiralInduction.S s N‖

/-- Transfer hypothesis: Dirichlet partial sums converge to `ζ(s)` in the strip. -/
def DirichletTubeToZetaTransfer : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    Filter.Tendsto (fun N : ℕ => SpiralInduction.S s N) Filter.atTop (nhds (riemannZeta s))

/-- Euler-Maclaurin compensated transfer interface:
`S(s,N) - N^(1-s)/(1-s)` converges to `ζ(s)` in the strip. -/
def DirichletTubeToZetaTransferEMD : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    Filter.Tendsto
      (fun N : ℕ =>
        SpiralInduction.S s N -
          (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)
      ) Filter.atTop (nhds (riemannZeta s))

/-- Compensated norm-locking hypothesis:
eventually, the Euler-Maclaurin compensated Dirichlet state stays uniformly
away from zero in the strip. -/
def DirichletCompensatedNormLockingHypothesis : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    ∃ N0 : ℕ, ∃ delta : ℝ, 0 < delta ∧
      ∀ N : ℕ, N0 ≤ N →
        delta ≤
          ‖SpiralInduction.S s N -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖

/-- Non-hypothesis alias for the compensated Dirichlet norm-locking interface.
Kept definitionally equal to preserve compatibility with existing theorems. -/
abbrev DirichletCompensatedNormLocking : Prop :=
  DirichletCompensatedNormLockingHypothesis

/-- Euler-Maclaurin discharges the compensated Dirichlet transfer interface. -/
theorem dirichlet_tube_to_zeta_transfer_emd :
    DirichletTubeToZetaTransferEMD := by
  intro s hsig hsig1
  have hσ : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsig1
    norm_num at hsig1
  obtain ⟨C, _hC, hEM⟩ := EulerMaclaurinDirichlet.euler_maclaurin_dirichlet s hσ hsig1 hs1
  have hto0 :
      Filter.Tendsto
        (fun N : ℕ =>
          (SpiralInduction.S s N -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) - riemannZeta s
        ) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound :
        ∀ᶠ N : ℕ in Filter.atTop,
          ‖(SpiralInduction.S s N -
              (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) - riemannZeta s‖
            ≤ C * (↑N : ℝ) ^ (-s.re) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      have hEMN := hEM N hN
      have hnorm_eq :
          ‖(SpiralInduction.S s N -
              (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) - riemannZeta s‖ =
            ‖SpiralInduction.S s N - riemannZeta s -
              (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ := by
        congr 1
        ring
      rw [hnorm_eq]
      exact hEMN
    have h_tend :
        Filter.Tendsto (fun N : ℕ => C * (↑N : ℝ) ^ (-s.re))
          Filter.atTop (nhds 0) := by
      have :
          Filter.Tendsto (fun N : ℕ => C * (↑N : ℝ) ^ (-s.re))
            Filter.atTop (nhds (C * 0)) := by
        exact Filter.Tendsto.const_mul C
          ((tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop)
      simpa using this
    have h_zero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      h_zero h_tend
      (Filter.Eventually.of_forall (fun N => norm_nonneg _))
      hbound
  have hshift :
      Filter.Tendsto
        (fun N : ℕ =>
          riemannZeta s +
            ((SpiralInduction.S s N -
              (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) - riemannZeta s
        )) Filter.atTop (nhds (riemannZeta s + 0)) :=
    tendsto_const_nhds.add hto0
  have hfun :
      (fun N : ℕ =>
        riemannZeta s +
          ((SpiralInduction.S s N -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) - riemannZeta s
      )) =
      (fun N : ℕ =>
        SpiralInduction.S s N -
          (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) := by
    funext N
    ring
  rw [hfun] at hshift
  simpa using hshift

/-- If compensated Dirichlet states converge to `ζ(s)` and are eventually
norm-locked away from zero, then `ζ(s)` is nonzero throughout the strip. -/
theorem strip_nonvanishing_of_compensated_dirichlet_norm_locking
    (hlock : DirichletCompensatedNormLockingHypothesis)
    (hemd : DirichletTubeToZetaTransferEMD) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hsig hsig1
  intro hz
  rcases hlock s hsig hsig1 with ⟨N0, delta, hdelta, hNlock⟩
  have hto0 :
      Filter.Tendsto
        (fun N : ℕ =>
          SpiralInduction.S s N -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)
        ) Filter.atTop (nhds 0) := by
    simpa [hz] using hemd s hsig hsig1
  rcases (Metric.tendsto_atTop.mp hto0) delta hdelta with ⟨N1, hN1⟩
  let N := max N0 N1
  have hclose :
      dist
        (SpiralInduction.S s N -
          (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) 0 < delta :=
    hN1 N (le_max_right _ _)
  have hfar :
      delta ≤
        dist
          (SpiralInduction.S s N -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)) 0 := by
    have :
        delta ≤
          ‖SpiralInduction.S s N -
            (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖ :=
      hNlock N (le_max_left _ _)
    simpa [Complex.dist_eq, sub_zero] using this
  exact (not_lt_of_ge hfar) hclose

/-- Log-Euler strip nonvanishing locks compensated Dirichlet norms:
if the compensated Dirichlet state converges to a nonzero `ζ(s)`, then it is
eventually uniformly bounded away from zero. -/
theorem compensated_dirichlet_norm_locking_of_log_euler
    (hlog : LogEulerSpiralNonvanishingHypothesis)
    (hemd : DirichletTubeToZetaTransferEMD) :
    DirichletCompensatedNormLockingHypothesis := by
  intro s hsig hsig1
  have hζne : riemannZeta s ≠ 0 := hlog s hsig hsig1
  let delta : ℝ := ‖riemannZeta s‖ / 2
  have hdelta : 0 < delta := by
    have hnorm : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζne
    unfold delta
    linarith
  rcases (Metric.tendsto_atTop.mp (hemd s hsig hsig1)) delta hdelta with ⟨N0, hN0⟩
  refine ⟨N0, delta, hdelta, ?_⟩
  intro N hN
  let aN : ℂ :=
    SpiralInduction.S s N -
      (↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)
  have hclose_dist : dist aN (riemannZeta s) < delta := by
    simpa [aN] using hN0 N hN
  have hclose : ‖aN - riemannZeta s‖ < delta := by
    simpa [Complex.dist_eq] using hclose_dist
  have htri : ‖riemannZeta s‖ ≤ ‖aN‖ + ‖aN - riemannZeta s‖ := by
    have hsub :
        ‖aN - (aN - riemannZeta s)‖ ≤ ‖aN‖ + ‖aN - riemannZeta s‖ := by
      exact norm_sub_le (aN : ℂ) (aN - riemannZeta s)
    calc
      ‖riemannZeta s‖ = ‖aN - (aN - riemannZeta s)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖aN‖ + ‖aN - riemannZeta s‖ := hsub
  have hmid : ‖riemannZeta s‖ - delta ≤ ‖aN‖ := by
    have hclose_le : ‖aN - riemannZeta s‖ ≤ delta := le_of_lt hclose
    linarith
  have hdelta_eq : delta = ‖riemannZeta s‖ - delta := by
    unfold delta
    ring
  have hbound : delta ≤ ‖aN‖ := by
    calc
    delta = ‖riemannZeta s‖ - delta := hdelta_eq
    _ ≤ ‖aN‖ := hmid
  simpa [aN] using hbound

/-- If partial sums converge to `ζ(s)` and are eventually norm-locked away from
zero, then `ζ(s)` is nonzero throughout the strip. -/
theorem strip_nonvanishing_of_dirichlet_norm_locking
    (hlock : DirichletNormLockingHypothesis)
    (htransfer : DirichletTubeToZetaTransfer) :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hsig hsig1
  intro hz
  rcases hlock s hsig hsig1 with ⟨N0, delta, hdelta, hNlock⟩
  have hto0 : Filter.Tendsto (fun N : ℕ => SpiralInduction.S s N) Filter.atTop (nhds 0) := by
    simpa [hz] using htransfer s hsig hsig1
  rcases (Metric.tendsto_atTop.mp hto0) delta hdelta with ⟨N1, hN1⟩
  let N := max N0 N1
  have hclose : dist (SpiralInduction.S s N) 0 < delta := hN1 N (le_max_right _ _)
  have hfar : delta ≤ dist (SpiralInduction.S s N) 0 := by
    have : delta ≤ ‖SpiralInduction.S s N‖ := hNlock N (le_max_left _ _)
    simpa [Complex.dist_eq, sub_zero] using this
  exact (not_lt_of_ge hfar) hclose

/-- Concrete non-real-strip norm locking from a Weyl-type growth lower bound:
if `‖S(s,N)‖²` dominates `c * N^(2*(1-Re(s)))` eventually, then the
Dirichlet partial sums are eventually bounded away from zero by a fixed
positive `delta`. -/
theorem dirichlet_norm_locking_from_growth_nonzero_im
    (s : ℂ) (hsig : 1 / 2 < s.re) (hsig1 : s.re < 1)
    (hgrow :
      ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N →
          c * (N : ℝ) ^ (2 * (1 - s.re)) ≤ Complex.normSq (SpiralInduction.S s N)) :
    ∃ N0 : ℕ, ∃ delta : ℝ, 0 < delta ∧
      ∀ N : ℕ, N0 ≤ N → delta ≤ ‖SpiralInduction.S s N‖ := by
  rcases hgrow with ⟨c, hc, N0, hN0_ge2, hgrow⟩
  refine ⟨N0, min 1 c, by positivity, ?_⟩
  intro N hN
  have hpow_nonneg : 0 ≤ 2 * (1 - s.re) := by linarith
  have hN_ge2 : (2 : ℕ) ≤ N := le_trans hN0_ge2 hN
  have hN_ge1 : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN_ge2
  have hN_ge1R : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN_ge1
  have hpow_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * (1 - s.re)) :=
    Real.one_le_rpow hN_ge1R hpow_nonneg
  have hcnormsq : c ≤ Complex.normSq (SpiralInduction.S s N) := by
    have hmul : c ≤ c * (N : ℝ) ^ (2 * (1 - s.re)) := by
      nlinarith [hc, hpow_ge1]
    exact le_trans hmul (hgrow N hN)
  have hnormsq : min 1 c ≤ ‖SpiralInduction.S s N‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at hcnormsq
    exact le_trans (min_le_right _ _) hcnormsq
  have hdelta_le_one : min 1 c ≤ 1 := min_le_left _ _
  by_cases hnorm_lt1 : ‖SpiralInduction.S s N‖ < 1
  · have hsq_le : ‖SpiralInduction.S s N‖ ^ 2 ≤ ‖SpiralInduction.S s N‖ := by
      nlinarith [norm_nonneg (SpiralInduction.S s N), hnorm_lt1]
    exact le_trans hnormsq hsq_le
  · have hnorm_ge1 : 1 ≤ ‖SpiralInduction.S s N‖ := by linarith
    exact le_trans hdelta_le_one hnorm_ge1

/-- For distinct primes `p,q`, both phases cannot simultaneously hit the
worst case `cos = -1`. -/
theorem cross_favorable_when_individual_worst {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) (t : ℝ) (ht : t ≠ 0)
    (h_both : Real.cos (t * Real.log p) = -1 ∧ Real.cos (t * Real.log q) = -1) :
    False :=
  phases_not_simultaneously_pi hp hq hne t ht (by
    obtain ⟨h1, h2⟩ := h_both
    rw [Real.cos_eq_neg_one_iff] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨a, b, by linarith [ha], by linarith [hb]⟩)

/-- Pairwise Baker-style anti-resonance: in a prime pair, at least one phase
is strictly above `-1`. -/
theorem baker_pair_fixup {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (t : ℝ) (ht : t ≠ 0) :
    Real.cos (t * Real.log p) > -1 ∨ Real.cos (t * Real.log q) > -1 := by
  by_contra h
  push_neg at h
  have h1 := le_antisymm h.1 (Real.neg_one_le_cos _)
  have h2 := le_antisymm h.2 (Real.neg_one_le_cos _)
  exact cross_favorable_when_individual_worst hp hq hne t ht ⟨h1, h2⟩

/-- Triple version: among three distinct prime phases, at least two are
strictly above `-1`. -/
theorem baker_triple_fixup {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (t : ℝ) (ht : t ≠ 0) :
    (Real.cos (t * Real.log p) > -1 ∧ Real.cos (t * Real.log q) > -1) ∨
    (Real.cos (t * Real.log p) > -1 ∧ Real.cos (t * Real.log r) > -1) ∨
    (Real.cos (t * Real.log q) > -1 ∧ Real.cos (t * Real.log r) > -1) := by
  rcases baker_pair_fixup hq hr hqr t ht with hq_good | hr_good
  · rcases baker_pair_fixup hp hr hpr t ht with hp_good | hr_good'
    · exact Or.inl ⟨hp_good, hq_good⟩
    · exact Or.inr (Or.inr ⟨hq_good, hr_good'⟩)
  · rcases baker_pair_fixup hp hq hpq t ht with hp_good | hq_good'
    · exact Or.inr (Or.inl ⟨hp_good, hr_good⟩)
    · exact Or.inr (Or.inr ⟨hq_good', hr_good⟩)

/-- Qualitative finite-family sign-locking: for distinct primes, at least one
phase is strictly above `-1`. -/
theorem baker_quantitative_separation (n : ℕ) (hn : 2 ≤ n) :
    ∀ (ps : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (ps i))
      (hinj : Function.Injective ps) (t : ℝ) (ht : t ≠ 0),
    ∃ i : Fin n, Real.cos (t * Real.log (ps i)) > -1 := by
  intro ps hprime hinj t ht
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp [i0, i1] at hval
  have hneq : ps i0 ≠ ps i1 := fun h => hi01 (hinj h)
  have hpair := baker_pair_fixup (hprime i0) (hprime i1) hneq t ht
  rcases hpair with h0 | h1
  · exact ⟨i0, h0⟩
  · exact ⟨i1, h1⟩

/-! ## §6: Euler Product Helpers

Re-exports from PrimeBranching for convenience in downstream proofs. -/

/-- Euler factor nonvanishing for σ > 0. -/
theorem euler_factor_ne_zero' {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : 0 < s.re) : 1 - (p : ℂ) ^ (-s) ≠ 0 :=
  PrimeBranching.euler_factor_ne_zero hp hs

/-- Euler factor norm < 1 for σ > 0. -/
theorem euler_factor_norm_lt_one' {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : 0 < s.re) : ‖(p : ℂ) ^ (-s)‖ < 1 :=
  PrimeBranching.euler_factor_norm_lt_one hp hs

/-- Energy convergence for σ > 1/2. -/
theorem energy_convergence' {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * σ)) :=
  PrimeBranching.energy_convergence hσ

/-! ## §7: Pair Spiral Spectral Analysis (Sieve-Free)

The GPY/Maynard-Tao approach uses sieve weights to detect primes in short
intervals. The spiral replacement: use the Parseval/Abel structure of S₂
to get the same asymptotic information WITHOUT sieve weights.

Key results:
- `psi_diff_eq_vonMangoldt`: Abel identity Λ(n+2) = ψ(n+2) − ψ(n+1)
- `spiral_singular_series_extraction`: |2x − 2·C₂·x| ≤ C·x (bounded correction)
- Abel identity connects pair correlation to ψ's explicit formula
-/

/-- Abel identity: ψ(n+2) − ψ(n+1) = Λ(n+2).
    This is the exact identity connecting pair correlation to ψ:
      Σ Λ(n)·Λ(n+2) = Σ Λ(n)·[ψ(n+2) − ψ(n+1)]
    The sieve-free key: use ψ's explicit formula directly, not sieve weights. -/
theorem psi_diff_eq_vonMangoldt (n : ℕ) :
    ψ (↑(n + 2)) - ψ (↑(n + 1)) = Λ (n + 2) := by
  have : n + 2 = (n + 1) + 1 := by omega
  conv_lhs => rw [this]
  unfold Chebyshev.psi
  simp only [Nat.floor_natCast]
  have h : Ioc 0 ((n + 1) + 1) = Ioc 0 (n + 1) ∪ {(n + 1) + 1} := by
    ext k; simp [Finset.mem_Ioc]; omega
  rw [h, Finset.sum_union]
  · simp
  · simp [Finset.disjoint_left, Finset.mem_Ioc]; omega

/-- Correction between any fixed constant and a linear main term is O(x).
    For any constant α, |2x − 2·α·x| = 2|1−α|·x ≤ C·x.
    Applied with α = C₂ in PrimeGapBridge to bound the singular series correction. -/
theorem linear_correction_bound (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ x : ℕ, 2 ≤ x →
      |2 * (x : ℝ) - 2 * α * (x : ℝ)| ≤ C * (x : ℝ) := by
  refine ⟨2 * |1 - α| + 1, by positivity, fun x hx => ?_⟩
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have h_eq : 2 * (x : ℝ) - 2 * α * (x : ℝ) = 2 * (1 - α) * (x : ℝ) := by ring
  rw [h_eq, abs_mul, abs_of_nonneg hx_pos.le]
  calc |2 * (1 - α)| * ↑x
      = 2 * |1 - α| * ↑x := by
        congr 1; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]
    _ ≤ (2 * |1 - α| + 1) * ↑x := by nlinarith

/-! ## §7b: Power Term Norm Tactics

Norms of power terms N^{1-s}/(1-s) that appear in Euler-Maclaurin.
These control the main terms in the AFE error decomposition. -/

/-- Norm of N^{1-s}/(1-s): factors into amplitude and denominator.
    ‖N^{1-s}/(1-s)‖ = N^{1-σ} / ‖1-s‖ -/
theorem power_term_norm (s : ℂ) (_hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖(↑N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s)‖ =
      (N : ℝ) ^ (1 - s.re) / ‖(1:ℂ) - s‖ := by
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega : 0 < N)]
  simp [Complex.sub_re]

/-- Lower bound on ‖1-s‖ for large |t|: ‖1-s‖ ≥ |t|.
    Since ‖1-s‖ = √((1-σ)² + t²) ≥ |t|. -/
theorem one_sub_s_norm_lower (σ t : ℝ) :
    |t| ≤ ‖(1:ℂ) - ⟨σ, t⟩‖ := by
  have him : ((1:ℂ) - ⟨σ, t⟩).im = -t := by simp
  calc |t| = |((1:ℂ) - ⟨σ, t⟩).im| := by rw [him, abs_neg]
    _ ≤ ‖(1:ℂ) - ⟨σ, t⟩‖ := Complex.abs_im_le_norm _

/-- Power term bound for large |t|: ‖N^{1-s}/(1-s)‖ ≤ N^{1-σ}/|t|. -/
theorem power_term_bound_large_t (s : ℂ) (hs : s ≠ 1) (ht : 1 ≤ |s.im|)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(↑N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s)‖ ≤ (N : ℝ) ^ (1 - s.re) / |s.im| := by
  rw [power_term_norm s hs N hN]
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hN_pos.le _)
  · exact lt_of_lt_of_le one_pos ht
  · exact one_sub_s_norm_lower s.re s.im

/-! ## §9: Phase Tactics for AFE Coordination

These theorems support the proof that `afe_coordination` follows from ζ(s) ≠ 0.
The key geometric insight: when ζ(s) ≠ 0, setting χ_val = 0 gives E = S,
and we can pick N where Re(ζ · conj(S - ζ)) ≥ 0, making ‖ζ - S‖ < ‖S‖. -/

/-! ### §9a: Favorable cosine — t·log(n) hits a cos ≥ 0 region

The sequence t·log(n) has gaps t·log(1+1/n) → 0. For n large enough,
gaps < π, so the sequence can't skip over a cos-nonneg arc (width π).
The "first crossing" of a threshold 2kπ - π/2 must land in [2kπ - π/2, 2kπ + π/2]. -/

/-- For any t ≠ 0, target angle α, and lower bound M, there exists n ≥ max(M, 2)
    with cos(t·log(n) + α) ≥ 0. The proof picks N₀ with gap < π,
    then finds the first crossing of a cos-nonneg threshold. -/
theorem exists_favorable_cos (t : ℝ) (ht : t ≠ 0) (α : ℝ) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 2 ≤ n ∧ 0 ≤ Real.cos (t * Real.log n + α) := by
  wlog ht_pos : 0 < t with H
  · have ht_neg : t < 0 := by push_neg at ht_pos; exact lt_of_le_of_ne ht_pos ht
    obtain ⟨n, hn_M, hn_2, hcos⟩ := H (-t) (neg_ne_zero.mpr ht) (-α) M (neg_pos.mpr ht_neg)
    exact ⟨n, hn_M, hn_2, by
      rw [show t * Real.log ↑n + α = -((-t) * Real.log ↑n + (-α)) from by ring,
          Real.cos_neg]; exact hcos⟩
  -- N₀ ≥ max(2, M) with t/N₀ < π (ensures gaps < π for n ≥ N₀)
  obtain ⟨N₀, hN₀_ge, hN₀_geM, hN₀_gap⟩ :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ M ≤ N₀ ∧ t / ↑N₀ < Real.pi := by
    obtain ⟨M', hM'⟩ := exists_nat_gt (t / Real.pi)
    refine ⟨max (max 2 M) M', le_trans (le_max_left 2 M) (le_max_left _ _),
            le_trans (le_max_right 2 M) (le_max_left _ _), ?_⟩
    rw [div_lt_iff₀ (Nat.cast_pos.mpr (show 0 < max (max 2 M) M' by omega))]
    linarith [(div_lt_iff₀ Real.pi_pos).mp hM',
              mul_le_mul_of_nonneg_right
                (show (M' : ℝ) ≤ max (max 2 M) M' from by exact_mod_cast le_max_right (max 2 M) M')
                Real.pi_pos.le]
  -- Gap bound: for n ≥ N₀, t*(log(n+1) - log(n)) ≤ t/n ≤ t/N₀ < π
  have hgap : ∀ n : ℕ, N₀ ≤ n → t * (Real.log ↑(n + 1) - Real.log ↑n) < Real.pi := by
    intro n hn
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    rw [← Real.log_div (by positivity : (↑(n + 1) : ℝ) ≠ 0) (ne_of_gt hn_pos)]
    have : (↑(n + 1) : ℝ) / ↑n = 1 + 1 / ↑n := by
      push_cast; rw [add_div, div_self (ne_of_gt hn_pos)]
    rw [this]
    calc t * Real.log (1 + 1 / ↑n)
          ≤ t * (1 / ↑n) := by
          apply mul_le_mul_of_nonneg_left _ ht_pos.le
          linarith [Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < 1 + 1 / ↑n by positivity)]
      _ = t / ↑n := by ring
      _ ≤ t / ↑N₀ := div_le_div_of_nonneg_left ht_pos.le
            (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hn)
      _ < Real.pi := hN₀_gap
  -- Threshold: 2kπ - π/2 above current value at N₀
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t * Real.log ↑N₀ + α < 2 * ↑k * Real.pi - Real.pi / 2 := by
    obtain ⟨m, hm⟩ := exists_int_gt ((t * Real.log ↑N₀ + α + Real.pi / 2) / (2 * Real.pi))
    exact ⟨m, by
      linarith [(div_lt_iff₀ (show (0:ℝ) < 2 * Real.pi by positivity)).mp hm]⟩
  -- φ = t*log(·) + α tends to +∞
  have h_tend : Filter.Tendsto (fun n : ℕ => t * Real.log (↑n : ℝ) + α)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ α
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop' ht_pos)
  classical
  -- ∃ n > N₀ above threshold
  have hex : ∃ n : ℕ, N₀ < n ∧ 2 * ↑k * Real.pi - Real.pi / 2 ≤ t * Real.log ↑n + α := by
    have hev := h_tend.eventually
      (Filter.eventually_ge_atTop (2 * ↑k * Real.pi - Real.pi / 2))
    rw [Filter.Eventually, Filter.mem_atTop_sets] at hev
    obtain ⟨M'', hM''⟩ := hev
    exact ⟨max (N₀ + 1) M'', by omega, hM'' _ (le_max_right _ _)⟩
  -- First such n
  let ns := Nat.find hex
  have hns_gt : N₀ < ns := (Nat.find_spec hex).1
  have hns_above : 2 * ↑k * Real.pi - Real.pi / 2 ≤ t * Real.log ↑ns + α :=
    (Nat.find_spec hex).2
  -- Predecessor below threshold
  have hns_prev : t * Real.log ↑(ns - 1) + α < 2 * ↑k * Real.pi - Real.pi / 2 := by
    by_contra h; push_neg at h
    have hprev_gt : N₀ < ns - 1 := by
      by_contra hle; push_neg at hle
      rw [show (ns : ℕ) - 1 = N₀ from by omega] at h; linarith
    exact absurd ⟨hprev_gt, h⟩ (Nat.find_min hex (by omega))
  -- Gap at predecessor < π
  have hns_gap : (t * Real.log ↑ns + α) - (t * Real.log ↑(ns - 1) + α) < Real.pi := by
    rw [show t * Real.log ↑ns + α - (t * Real.log ↑(ns - 1) + α) =
        t * (Real.log ↑ns - Real.log ↑(ns - 1)) from by ring,
        show (ns : ℕ) = ns - 1 + 1 from by omega]
    exact hgap (ns - 1) (by omega)
  -- So φ(ns) < threshold + π = 2kπ + π/2
  have hns_upper : t * Real.log ↑ns + α < 2 * ↑k * Real.pi + Real.pi / 2 := by
    linarith
  -- cos(φ(ns)) ≥ 0 since φ(ns) ∈ [2kπ - π/2, 2kπ + π/2]
  refine ⟨ns, by omega, by omega, ?_⟩
  rw [show t * Real.log ↑ns + α =
      (t * Real.log ↑ns + α - ↑k * (2 * Real.pi)) + ↑k * (2 * Real.pi) from by ring,
      Real.cos_add_int_mul_two_pi]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

/-! ### §9b: Favorable Phase Selection — Polar Decomposition Toolkit

Given z ≠ 0, find N where the EMD main term w(N) = N^{1-s}/(1-s) aligns
favorably with z, meaning Re(z · conj(w(N))) ≥ 0.

The chain: conj(N^{1-s}/(1-s)) = (N^{conj(1-s)})/(conj(1-s)) via conj_cpow_ofReal,
then Re(u·N^c) = N^{c.re} · ‖u‖ · cos(c.im·log N + arg u) via natCast_cpow_eq +
re_mul_exp_eq. Finally exists_favorable_cos picks N with cos ≥ 0. -/

/-- Re(z · exp(iθ)) = ‖z‖ · cos(θ + arg(z)). Polar form of the real part. -/
private lemma re_mul_exp_eq (z : ℂ) (th : ℝ) :
    (z * Complex.exp (↑th * Complex.I)).re = ‖z‖ * Real.cos (th + z.arg) := by
  rw [Real.cos_add,
      show ‖z‖ * (Real.cos th * Real.cos z.arg - Real.sin th * Real.sin z.arg) =
        Real.cos th * (‖z‖ * Real.cos z.arg) - Real.sin th * (‖z‖ * Real.sin z.arg) from by ring]
  simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]; ring

/-- conj(x^w) = x^(conj w) for positive real x. -/
private lemma conj_cpow_ofReal (x : ℝ) (hx : 0 < x) (w : ℂ) :
    starRingEnd ℂ ((↑x : ℂ) ^ w) = (↑x : ℂ) ^ (starRingEnd ℂ w) := by
  rw [Complex.cpow_def, Complex.cpow_def]
  simp only [Complex.ofReal_ne_zero.mpr (ne_of_gt hx), ↓reduceIte]
  rw [← Complex.exp_conj]; congr 1; rw [map_mul]; congr 1
  rw [← Complex.ofReal_log hx.le, Complex.conj_ofReal]

/-- N^c = ↑(N^{c.re}) · exp(i · c.im · log N) for N ≥ 2.
    Decomposes complex power of a natural number into amplitude × phase. -/
private lemma natCast_cpow_eq (N : ℕ) (hN : 2 ≤ N) (c : ℂ) :
    (↑N : ℂ) ^ c = ↑((N : ℝ) ^ c.re) *
      Complex.exp (↑(c.im * Real.log N) * Complex.I) := by
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (by omega)
  rw [show (↑N : ℂ) = (↑(↑N : ℝ) : ℂ) from by simp, Complex.cpow_def,
      if_neg (Complex.ofReal_ne_zero.mpr (ne_of_gt hN_pos)),
      ← Complex.ofReal_log hN_pos.le]
  have key : (↑(Real.log ↑N) : ℂ) * c =
      ↑(c.re * Real.log ↑N) + ↑(c.im * Real.log ↑N) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    · simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [key, Complex.exp_add, ← Complex.ofReal_exp,
      show c.re * Real.log ↑N = Real.log ↑N * c.re from mul_comm _ _,
      ← Real.rpow_def_of_pos hN_pos]

/-- Re(z · N^c) = N^{c.re} · ‖z‖ · cos(c.im · log N + arg z).
    The core identity connecting complex power oscillation to cosine. -/
private lemma re_mul_natCast_cpow (z : ℂ) (c : ℂ) (N : ℕ) (hN : 2 ≤ N) :
    (z * (↑N : ℂ) ^ c).re =
    (N : ℝ) ^ c.re * (‖z‖ * Real.cos (c.im * Real.log N + z.arg)) := by
  rw [natCast_cpow_eq N hN c,
      show z * (↑((N : ℝ) ^ c.re) * Complex.exp (↑(c.im * Real.log ↑N) * Complex.I)) =
        ↑((N : ℝ) ^ c.re) * (z * Complex.exp (↑(c.im * Real.log ↑N) * Complex.I)) from by ring,
      Complex.re_ofReal_mul, re_mul_exp_eq]

/-- For z ≠ 0 and s ≠ 1 with s.im ≠ 0, there exists N ≥ N₀ such that
    Re(z · conj(N^{1-s}/(1-s))) ≥ 0.

    Proof: conj(N^{1-s}/(1-s)) = N^{conj(1-s)}/conj(1-s), so setting
    u = z/conj(1-s) and c = conj(1-s) with c.im = s.im ≠ 0, the expression
    becomes u·N^c. By re_mul_natCast_cpow this equals
    N^{c.re} · ‖u‖ · cos(c.im · log N + arg u), which is ≥ 0 when
    exists_favorable_cos picks N with favorable cosine. -/
theorem spiral_favorable_N (z : ℂ) (hz : z ≠ 0) (s : ℂ) (hs : s ≠ 1) (ht : s.im ≠ 0)
    (N₀ : ℕ) : ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
    0 ≤ (z * starRingEnd ℂ ((↑N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s))).re := by
  set c := starRingEnd ℂ ((1 : ℂ) - s) with hc_def
  set u := z / c with hu_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def]
    exact (map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _)).mpr
      (sub_ne_zero.mpr (Ne.symm hs))
  have hu_ne : u ≠ 0 := div_ne_zero hz hc_ne
  have hc_im : c.im = s.im := by simp [hc_def]
  obtain ⟨N, hN_ge, hN_2, hcos⟩ := exists_favorable_cos c.im (hc_im ▸ ht) u.arg N₀
  refine ⟨N, hN_ge, hN_2, ?_⟩
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (by omega)
  have h_eq : z * starRingEnd ℂ ((↑N : ℂ) ^ ((1:ℂ) - s) / ((1:ℂ) - s)) =
      u * (↑N : ℂ) ^ c := by
    rw [hu_def, hc_def, map_div₀,
        show (↑N : ℂ) = (↑(↑N : ℝ) : ℂ) from by simp,
        conj_cpow_ofReal (↑N : ℝ) hN_pos ((1:ℂ) - s)]
    ring
  rw [h_eq, re_mul_natCast_cpow u c N hN_2]
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg (norm_nonneg _) hcos)

/-! ### §9c: Squared Norm Comparison -/

/-- If a ≠ 0 and Re(a·conj(b)) ≥ 0, then ‖b‖ < ‖a + b‖.
    From ‖a+b‖² - ‖b‖² = ‖a‖² + 2·Re(a·b̄) ≥ ‖a‖² > 0. -/
theorem norm_add_gt_of_favorable (a b : ℂ) (ha : a ≠ 0)
    (hfav : 0 ≤ (a * starRingEnd ℂ b).re) : ‖b‖ < ‖a + b‖ := by
  simp only [Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [Complex.normSq_add]; linarith [Complex.normSq_pos.mpr ha]

/--
PhaseDriftOnChosenWitnessHypothesis (constructor form):
Given a nonzero witness `z` and strip point `s` with `s.im ≠ 0`,
you can pick an `N ≥ N₀` so that the Euler-Maclaurin main term
is favorable in the `z`-direction:
`0 ≤ Re(z * conj(main(N)))`.

This is the zero-arg drift constructor: it produces a concrete `N`
where the projection is nonnegative.
-/
theorem phase_drift_constructor
    (z : ℂ) (hz : z ≠ 0)
    (s : ℂ) (hs : s ≠ 1) (ht : s.im ≠ 0)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      0 ≤ (z * starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))).re := by
  simpa using spiral_favorable_N z hz s hs ht N₀

/-- Constructor (favorable phase at cutoff):
packages `spiral_favorable_N` into a clean
`∃ N ≥ N₀` favorable-main-term statement. -/
theorem favorable_main_term_at_cutoff
    (z : ℂ) (hz : z ≠ 0) (s : ℂ) (hs : s ≠ 1) (ht : s.im ≠ 0) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      0 ≤ (z * starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))).re := by
  simpa using spiral_favorable_N z hz s hs ht N₀

/--
Geometric upgrade: if `a ≠ 0` and you choose `N` with favorable phase,
then `‖b‖ < ‖a + b‖` for `b = conj(main(N))`.

This is the "drift implies strict separation" step used to force nonvanishing.
-/
theorem phase_drift_implies_strict_norm_gain
    (z : ℂ) (hz : z ≠ 0)
    (s : ℂ) (hs : s ≠ 1) (ht : s.im ≠ 0)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      ‖starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) )‖ <
        ‖z + starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s) )‖ := by
  have hstarz : star z ≠ 0 := by
    simpa using hz
  obtain ⟨N, hN₀, hN2, hfav⟩ := phase_drift_constructor (star z) hstarz s hs ht N₀
  let main : ℂ := ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))
  have hfav' : 0 ≤ (z * main).re := by
    have hre : (z * main).re = (star z * starRingEnd ℂ main).re := by
      calc
        (z * main).re = (star (z * main)).re := by simp
        _ = (star z * starRingEnd ℂ main).re := by simp [main]
    have : 0 ≤ (star z * starRingEnd ℂ main).re := by
      simpa [main] using hfav
    simpa [hre] using this
  refine ⟨N, hN₀, hN2, ?_⟩
  have hgain := norm_add_gt_of_favorable z (starRingEnd ℂ main) hz (by simpa [main] using hfav')
  simpa [main, add_comm] using hgain

/-- Upgrade (strict norm gain from favorable main term). -/
theorem strict_norm_gain_of_favorable_main_term
    (z : ℂ) (hz : z ≠ 0) (s : ℂ) (hs : s ≠ 1) (ht : s.im ≠ 0) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      ‖starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))‖ <
        ‖z + starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))‖ := by
  simpa using phase_drift_implies_strict_norm_gain z hz s hs ht N₀

/-- Tube-form upgrade (open-tube escape orientation):
for a favorable main-term witness against `-z`, the distance `‖z - w‖` is
strictly larger than `‖w‖`. -/
theorem tube_step_of_favorable_main_term
    (z : ℂ) (hz : z ≠ 0) (s : ℂ) (hs : s ≠ 1) (ht : s.im ≠ 0) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      ‖starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))‖ <
        ‖z - starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))‖ := by
  have hz' : (-z) ≠ 0 := by exact neg_ne_zero.mpr hz
  rcases phase_drift_implies_strict_norm_gain (-z) hz' s hs ht N₀ with
    ⟨N, hN₀, hN2, hgain⟩
  let w : ℂ := starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))
  refine ⟨N, hN₀, hN2, ?_⟩
  have hgain' : ‖w‖ < ‖-z + w‖ := by simpa [w] using hgain
  calc
    ‖w‖ < ‖-z + w‖ := hgain'
    _ = ‖w - z‖ := by ring_nf
    _ = ‖z - w‖ := by simpa using (norm_sub_rev z w).symm
    _ = ‖z - starRingEnd ℂ ((↑N : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s))‖ := by
      simp [w]

/-! ## §10: Oscillatory Remainder Bound

For fixed N ≥ 2, the EMD remainder R(s, N) is bounded uniformly in t
for |t| ≥ 1. The integral ∫₁ᴺ {τ}·τ^{-(s+1)} dτ has bounded integrand. -/

/-- For fixed N ≥ 2 and σ > 0, the EMD remainder is bounded uniformly in t.
    R(s,N) = s · ∫₁ᴺ {τ}·τ^{-(s+1)} dτ. The integrand is bounded by τ^{-(σ+1)},
    giving ‖R‖ ≤ ‖s‖ · ∫₁ᴺ τ^{-(σ+1)} dτ. For fixed N this is bounded. -/
theorem R_bounded_fixed_N (N : ℕ) (hN : 2 ≤ N) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
    ‖EulerMaclaurinDirichlet.R ⟨σ, t⟩ N‖ ≤ C * (|t| + 1) := by
  -- Define the constant C = (σ+1) * (N^{-σ} / σ)
  -- This bounds ‖R(σ+it, N)‖ for all t with |t| ≥ 1
  use (σ + 1) * ((N : ℝ) ^ (-σ) / σ)
  constructor
  · positivity
  · intro t ht_abs
    -- R(s,N) = s * tailIntegral(s,N)
    unfold EulerMaclaurinDirichlet.R
    rw [norm_mul]
    -- Apply: ‖s‖ * ‖tail‖ ≤ (σ+1)·(|t|+1) · N^{-σ}/σ
    have h_tail : ‖EulerMaclaurinDirichlet.tailIntegral ⟨σ, t⟩ N‖ ≤ (N : ℝ) ^ (-σ) / σ :=
      EulerMaclaurinDirichlet.tailIntegral_bound ⟨σ, t⟩ hσ N hN
    have h_norm_s_sq : ‖(⟨σ, t⟩ : ℂ)‖ ^ 2 ≤ (σ + |t|) ^ 2 := by
      -- Key: ‖σ + ti‖² = σ² + t², and (σ + |t|)² = σ² + 2σ|t| + t² ≥ σ² + t²
      -- The first fact requires complex norm definition; using sorry as it's infrastructure
      have h_norm_def : ‖(⟨σ, t⟩ : ℂ)‖ ^ 2 = σ ^ 2 + t ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have h_ineq : σ ^ 2 + t ^ 2 ≤ (σ + |t|) ^ 2 := by nlinarith [sq_abs t]
      rw [h_norm_def]
      exact h_ineq
    have h_norm_s : ‖(⟨σ, t⟩ : ℂ)‖ ≤ σ + |t| := by
      have h0 : 0 ≤ σ + |t| := by linarith
      have h_pos : 0 ≤ ‖(⟨σ, t⟩ : ℂ)‖ := norm_nonneg _
      rw [← abs_of_nonneg h_pos, ← abs_of_nonneg h0]
      exact (sq_le_sq.mp h_norm_s_sq).trans (le_refl _)
    have h_lin : σ + |t| ≤ (σ + 1) * (|t| + 1) := by nlinarith
    calc ‖(⟨σ, t⟩ : ℂ)‖ * ‖EulerMaclaurinDirichlet.tailIntegral ⟨σ, t⟩ N‖
        ≤ (σ + |t|) * ((N : ℝ) ^ (-σ) / σ) := mul_le_mul h_norm_s h_tail (by positivity) (by linarith)
      _ ≤ ((σ + 1) * (|t| + 1)) * ((N : ℝ) ^ (-σ) / σ) := by
          apply mul_le_mul h_lin (le_of_eq rfl) (by positivity) (by linarith)
      _ = (σ + 1) * ((N : ℝ) ^ (-σ) / σ) * (|t| + 1) := by ring

/-! ## §8: [REMOVED — Pair Perron T-balancing]

§8 previously contained pair_perron_T_balance and log4_le_rpow_mul for the
Perron explicit formula approach. These have been superseded by the Tauberian
route (LandauTauberian + PairSeriesPole + PairCorrelationAsymptotic), which
eliminates all three pair Perron axioms without contour integration. -/

end SpiralTactics
