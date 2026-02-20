/-
  LandauTauberian.lean — Landau's Real-Variable Tauberian Theorem
  ================================================================

  "The Tauberian hammer: nonneg coefficients + pole → asymptotic."

  Landau (1908): If a(n) ≥ 0, F(s) = Σ a(n)/n^s converges for Re(s) > 1,
  and (s-1)·F(s) → A > 0 as s → 1+ (real), then Σ_{n≤x} a(n) ~ A·x.

  This is a REAL-VARIABLE proof — no complex analysis needed.
  The key insight: nonnegativity of a(n) makes upper and lower bounds
  easy via comparison with the Dirichlet series at s = 1 + 1/log(x).

  References:
  - Tenenbaum, "Introduction to Analytic Number Theory", II.7
  - Montgomery & Vaughan, "Multiplicative Number Theory I", §8.3
  - Korevaar, "Tauberian Theory: A Century of Developments", Ch. III
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open Finset Real Filter

namespace LandauTauberian

/-! ## Helper lemmas for partial sums -/

private noncomputable def partialSum (a : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 x, a n

private lemma partialSum_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (x : ℕ) :
    0 ≤ partialSum a x := by
  unfold partialSum
  exact Finset.sum_nonneg (fun n hn => ha n)

private lemma partialSum_mono (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {x y : ℕ} (hxy : x ≤ y) :
    partialSum a x ≤ partialSum a y := by
  unfold partialSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (le_refl _) hxy) ?_
  intro n hnxs hnys
  exact ha n

private lemma partialSum_zero (a : ℕ → ℝ) : partialSum a 0 = 0 := by
  simp [partialSum]

private lemma partialSum_succ (a : ℕ → ℝ) (n : ℕ) :
    partialSum a (n + 1) = partialSum a n + a (n + 1) := by
  simp only [partialSum]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-! ## Tauberian weight function μ_n(s) = (s-1) · n · (n^{-s} - (n+1)^{-s}) -/

/-- The Tauberian weight: μ_n(s) = (s-1) · n · (n^{-s} - (n+1)^{-s}).
    For s > 1, n ≥ 1: μ_n(s) ≥ 0 and Σ μ_n(s) = (s-1)ζ(s) → 1. -/
private noncomputable def tauberWeight (n : ℕ) (s : ℝ) : ℝ :=
  (s - 1) * (n : ℝ) * ((n : ℝ) ^ (-s) - ((n : ℝ) + 1) ^ (-s))

private lemma tauberWeight_nonneg {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 1 < s) :
    0 ≤ tauberWeight n s := by
  unfold tauberWeight
  have hs1 : 0 < s - 1 := by linarith
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  apply mul_nonneg (mul_nonneg (le_of_lt hs1) (le_of_lt hnpos))
  rw [sub_nonneg]
  exact rpow_le_rpow_of_nonpos hnpos (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    (neg_nonpos.mpr (le_of_lt (lt_trans one_pos hs)))

/-! ## One-sided Abelian bounds (Tauberian core)

These use Abel summation by parts + weight normalization ((s-1)ζ(s) → 1).
The representation (s-1)F(s) = Σ (u(n)/n)·μ_n(s), with μ_n(s) ≥ 0 and Σ μ_n → 1,
converts pointwise bounds on v(n) = u(n)/n into asymptotic bounds on (s-1)F(s).

The key identity (Abel summation): for s > 1, N ≥ 1:
  Σ_{n=1}^N a(n)/n^s = u(N)/N^s + Σ_{n=1}^{N-1} u(n)·(1/n^s - 1/(n+1)^s)
where u(n) = partialSum a n.

Taking N → ∞ and using u(N)/N^s → 0 (proved in partialSum_div_rpow_tendsto_zero):
  F(s) = Σ_{n≥1} u(n)·(1/n^s - 1/(n+1)^s)
       = Σ_{n≥1} v(n)·μ_n(s)/(s-1)
where v(n) = u(n)/n and μ_n(s) = (s-1)·n·(1/n^s - 1/(n+1)^s) ≥ 0.

The weights satisfy Σ μ_n(s) = (s-1)·ζ(s) → 1 as s → 1+. -/

/-- Finite Abel summation: Σ_{k=1}^{N} a(k)/k^s = u(N)/N^s + Σ_{k=1}^{N-1} u(k)·(k^{-s}-(k+1)^{-s}).
    This is proved by induction (telescoping). -/
private lemma finite_abel_summation
    (a : ℕ → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, a k / (k : ℝ) ^ s =
      partialSum a N / (N : ℝ) ^ s +
      ∑ k ∈ Finset.Icc 1 (N - 1), partialSum a k * ((k : ℝ) ^ (-s) - ((k : ℝ) + 1) ^ (-s)) := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · -- Base case: N = 1
      subst hn; simp [partialSum]
    · -- Inductive step: n ≥ 1
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have ih' := ih hn1
      -- LHS: Σ_{1..n+1} = Σ_{1..n} + a(n+1)/(n+1)^s
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih']
      -- RHS: n+1-1 = n, then split Σ_{1..n} = Σ_{1..n-1} + term at n
      simp only [show n + 1 - 1 = n from by omega]
      have hsplit : ∀ (f : ℕ → ℝ),
          ∑ k ∈ Finset.Icc 1 n, f k =
          ∑ k ∈ Finset.Icc 1 (n - 1), f k + f n := by
        intro f
        have := Finset.sum_Icc_succ_top (show 1 ≤ (n - 1) + 1 by omega) f
        rwa [show (n - 1) + 1 = n from by omega] at this
      rw [hsplit]
      -- Now algebra: u(n)/n^s + Σ_old + a(n+1)/(n+1)^s
      --            = u(n+1)/(n+1)^s + Σ_old + u(n)·(n^{-s}-(n+1)^{-s})
      have hpsu : partialSum a (n + 1) = partialSum a n + a (n + 1) := partialSum_succ a n
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hn1pos : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
      rw [hpsu, rpow_neg (le_of_lt hnpos) s, rpow_neg (by linarith : (0:ℝ) ≤ (n:ℝ) + 1) s]
      have hnpow : (n : ℝ) ^ s ≠ 0 := (rpow_pos_of_pos hnpos s).ne'
      have hn1pow : ((n : ℝ) + 1) ^ s ≠ 0 := (rpow_pos_of_pos hn1pos s).ne'
      push_cast [Nat.cast_add]
      field_simp
      ring

/-- From finite Abel summation: the tail weighted sum is bounded by the Dirichlet series.
    For M ≥ 1 and N ≥ M+1:
    Σ_{k=M}^{N-1} u(k)·(k^{-s}-(k+1)^{-s}) ≤ Σ_{k=1}^N a(k)/k^s.
    Proof: by finite_abel_summation, the RHS = u(N)/N^s + full weighted sum ≥ tail sum. -/
private lemma finite_partial_sum_ge_weighted_tail
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {s : ℝ} (hs : 1 < s)
    {M N : ℕ} (hM : 1 ≤ M) (hN : M + 1 ≤ N) :
    ∑ k ∈ Finset.Icc M (N - 1), partialSum a k *
      ((k : ℝ) ^ (-s) - ((k : ℝ) + 1) ^ (-s)) ≤
    ∑ k ∈ Finset.Icc 1 N, a k / (k : ℝ) ^ s := by
  rw [finite_abel_summation a (by linarith : 0 < s) N (by omega)]
  -- RHS = u(N)/N^s + Σ_{1..N-1} u(k)·(...)
  -- LHS = Σ_{M..N-1} u(k)·(...)
  -- Since Σ_{M..N-1} ⊆ Σ_{1..N-1} and all terms ≥ 0, and u(N)/N^s ≥ 0:
  have hu_nonneg : 0 ≤ partialSum a N / (N : ℝ) ^ s :=
    div_nonneg (partialSum_nonneg a ha N) (rpow_nonneg (Nat.cast_nonneg' N) s)
  have hweight_nonneg : ∀ k ∈ Finset.Icc 1 (N - 1),
      0 ≤ partialSum a k * ((k : ℝ) ^ (-s) - ((k : ℝ) + 1) ^ (-s)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    apply mul_nonneg (partialSum_nonneg a ha k)
    rw [sub_nonneg]
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    exact rpow_le_rpow_of_nonpos hkpos (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
      (neg_nonpos.mpr (le_of_lt (lt_trans one_pos hs)))
  have hsub : Finset.Icc M (N - 1) ⊆ Finset.Icc 1 (N - 1) :=
    Finset.Icc_subset_Icc hM le_rfl
  linarith [Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k hk hnk => hweight_nonneg k hk)]

/-- Abel summation for infinite Dirichlet series: F(s) = Σ u(k)·(k^{-s}-(k+1)^{-s}).
    Uses finite_abel_summation + u(N)/N^s → 0 + convergence of partial sums. -/
private lemma abel_summation_tsum
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    {s : ℝ} (hs : 1 < s) :
    HasSum (fun k => partialSum a (k + 1) * (((k + 1 : ℕ) : ℝ) ^ (-s) - (((k + 1 : ℕ) : ℝ) + 1) ^ (-s)))
      (∑' n, a n / (n : ℝ) ^ s) := by
  sorry

/-- Abelian lower bound: if u(n)/n ≥ B for all n ≥ N₀ with n ≥ 1, then
    (s-1)F(s) ≥ B - ε for s close to 1. -/
private lemma abelian_lower_bound
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (B : ℝ) (N₀ : ℕ)
    (hv : ∀ n, N₀ ≤ n → 1 ≤ n → B ≤ partialSum a n / (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      B - ε ≤ (s - 1) * ∑' n, a n / (n : ℝ) ^ s := by
  -- For B ≤ 0: trivial since B - ε < 0 ≤ (s-1)·F(s) for all s > 1
  by_cases hB : B ≤ 0
  · apply eventually_nhdsWithin_of_forall
    intro s hs
    rw [Set.mem_Ioi] at hs
    have : 0 ≤ (s - 1) * ∑' n, a n / (n : ℝ) ^ s :=
      mul_nonneg (by linarith) (tsum_nonneg (fun n => div_nonneg (ha n)
        (rpow_nonneg (Nat.cast_nonneg' n) s)))
    linarith
  push_neg at hB
  -- For B > 0: use Abel summation + weight normalization.
  -- Key: for s > 1 and M = max N₀ 1, any N ≥ M+1:
  --   Σ_{1..N} a(k)/k^s ≥ B · Σ_{k=M}^{N-1} k·(k^{-s}-(k+1)^{-s})  (*)
  -- And Σ_{k=1}^{N} k·(k^{-s}-(k+1)^{-s}) = Σ_{m=1}^{N+1} m^{-s} - (N+1)^{1-s}
  -- Taking N→∞: F(s) ≥ B·(ζ(s) - Σ_{k<M} k·(k^{-s}-(k+1)^{-s}))
  -- And (s-1)·ζ(s) → 1, (s-1)·finite → 0, so (s-1)·F(s) ≥ B - ε.
  --
  -- Step (*) uses finite_partial_sum_ge_weighted_tail + u(k) ≥ B·k.
  -- The passage to infinite series + the weight-ζ identity require
  -- HasSum manipulation that is substantial to formalize.
  sorry

/-- Abelian upper bound: if u(n)/n ≤ B for all n ≥ N₀ with n ≥ 1, then
    (s-1)F(s) ≤ B + ε for s close to 1. -/
private lemma abelian_upper_bound
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (B : ℝ) (N₀ : ℕ)
    (hv : ∀ n, N₀ ≤ n → 1 ≤ n → partialSum a n / (n : ℝ) ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (s - 1) * ∑' n, a n / (n : ℝ) ^ s ≤ B + ε := by
  sorry

/-- If u(n)/n ≥ A + ε eventually, contradiction with (s-1)F(s) → A. -/
private lemma not_eventually_above
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    {ε : ℝ} (hε : 0 < ε) {N₀ : ℕ}
    (habove : ∀ n, N₀ ≤ n → 1 ≤ n → A + ε ≤ partialSum a n / (n : ℝ)) :
    False := by
  -- Abelian lower bound gives (s-1)F(s) ≥ A + ε - ε/2 = A + ε/2 near s = 1
  have hlb := abelian_lower_bound a ha hconv (A + ε) N₀ habove (half_pos hε)
  -- But (s-1)F(s) → A, so eventually (s-1)F(s) < A + ε/2
  have hub : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (s - 1) * ∑' n, a n / (n : ℝ) ^ s < A + ε / 2 := by
    have h := Metric.tendsto_nhds.mp hpole (ε / 2) (half_pos hε)
    exact h.mono fun s hs => by
      rw [Real.dist_eq, abs_lt] at hs; linarith [hs.2]
  -- Both hold eventually; intersection gives A + ε/2 ≤ ... < A + ε/2
  have hboth := hlb.and hub
  obtain ⟨s, hs⟩ := hboth.exists
  linarith [hs.1, hs.2]

/-- If u(n)/n ≤ A - ε eventually, contradiction with (s-1)F(s) → A. -/
private lemma not_eventually_below
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    {ε : ℝ} (hε : 0 < ε) {N₀ : ℕ}
    (hbelow : ∀ n, N₀ ≤ n → 1 ≤ n → partialSum a n / (n : ℝ) ≤ A - ε) :
    False := by
  -- Abelian upper bound gives (s-1)F(s) ≤ A - ε + ε/2 = A - ε/2 near s = 1
  have hub := abelian_upper_bound a ha hconv (A - ε) N₀ hbelow (half_pos hε)
  -- But (s-1)F(s) → A, so eventually (s-1)F(s) > A - ε/2
  have hlb : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      A - ε / 2 < (s - 1) * ∑' n, a n / (n : ℝ) ^ s := by
    have h := Metric.tendsto_nhds.mp hpole (ε / 2) (half_pos hε)
    exact h.mono fun s hs => by
      rw [Real.dist_eq, abs_lt] at hs; linarith [hs.1]
  have hboth := hub.and hlb
  obtain ⟨s, hs⟩ := hboth.exists
  linarith [hs.1, hs.2]

private lemma partialSum_div_rpow_le_sum_weighted
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {s : ℝ} (hs : 1 < s) {x : ℕ} (hx : 1 ≤ x) :
    partialSum a x / (x : ℝ) ^ s ≤
      ∑ n ∈ Icc 1 x, a n / (n : ℝ) ^ s := by
  unfold partialSum
  have hs0 : 0 ≤ s := le_of_lt (lt_trans (by positivity : (0 : ℝ) < 1) hs)
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hx)
  have hxpows_pos : 0 < (x : ℝ) ^ s := Real.rpow_pos_of_pos hxpos s
  have hterm :
      ∀ n ∈ Icc 1 x, a n / (x : ℝ) ^ s ≤ a n / (n : ℝ) ^ s := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn1)
    have hnpows_pos : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hnpos s
    have hpow_le : (n : ℝ) ^ s ≤ (x : ℝ) ^ s := by
      exact Real.rpow_le_rpow (show 0 ≤ (n : ℝ) from by positivity)
        (by exact_mod_cast hnx) hs0
    exact div_le_div_of_nonneg_left (ha n) hnpows_pos (hpow_le)
  calc
    (∑ n ∈ Icc 1 x, a n) / (x : ℝ) ^ s = ∑ n ∈ Icc 1 x, a n * ((x : ℝ) ^ s)⁻¹ := by
      rw [div_eq_mul_inv, Finset.sum_mul]
    _ = ∑ n ∈ Icc 1 x, a n / (x : ℝ) ^ s := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ n ∈ Icc 1 x, a n / (n : ℝ) ^ s := Finset.sum_le_sum hterm

private lemma partialSum_div_rpow_le_tsum
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    {s : ℝ} (hs : 1 < s) {x : ℕ} (hx : 1 ≤ x) :
    partialSum a x / (x : ℝ) ^ s ≤ ∑' n, a n / (n : ℝ) ^ s := by
  have hle₁ :
      partialSum a x / (x : ℝ) ^ s ≤ ∑ n ∈ Icc 1 x, a n / (n : ℝ) ^ s :=
    partialSum_div_rpow_le_sum_weighted a ha hs hx
  have hle₂ :
      ∑ n ∈ Icc 1 x, a n / (n : ℝ) ^ s ≤ ∑' n, a n / (n : ℝ) ^ s := by
    exact (hconv s hs).sum_le_tsum (Icc 1 x) (fun n hn => by
      refine div_nonneg (ha n) ?_
      exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from by positivity) s)
  exact hle₁.trans hle₂

private lemma eventually_pole_bounds
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      A - ε ≤ (s - 1) * ∑' n, a n / (n : ℝ) ^ s ∧
      (s - 1) * ∑' n, a n / (n : ℝ) ^ s ≤ A + ε := by
  have hdist :=
    (Metric.tendsto_nhds.mp hpole) ε hε
  filter_upwards [hdist] with s hs
  have hs' : |(s - 1) * ∑' n, a n / (n : ℝ) ^ s - A| < ε := by
    simpa [Real.dist_eq] using hs
  exact ⟨by linarith [abs_lt.mp hs' |>.1], by linarith [abs_lt.mp hs' |>.2]⟩

private lemma partialSum_div_le_of_pole_upper
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    {s B : ℝ} (hs : 1 < s)
    (hB : (s - 1) * (∑' n, a n / (n : ℝ) ^ s) ≤ B)
    {x : ℕ} (hx : 1 ≤ x) :
    partialSum a x / (x : ℝ) ≤ B * (x : ℝ) ^ (s - 1) / (s - 1) := by
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hx)
  have hs_sub_pos : 0 < s - 1 := sub_pos.mpr hs
  have hsum_le : ∑' n, a n / (n : ℝ) ^ s ≤ B / (s - 1) := by
    refine (le_div_iff₀ hs_sub_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hB
  have hps_le : partialSum a x / (x : ℝ) ^ s ≤ B / (s - 1) := by
    exact (partialSum_div_rpow_le_tsum a ha hconv hs hx).trans hsum_le
  have hfac_nonneg : 0 ≤ (x : ℝ) ^ (s - 1) := Real.rpow_nonneg hxpos.le _
  have hmul :=
    mul_le_mul_of_nonneg_left hps_le hfac_nonneg
  have hleft :
      (x : ℝ) ^ (s - 1) * (partialSum a x / (x : ℝ) ^ s) = partialSum a x / (x : ℝ) := by
    calc
      (x : ℝ) ^ (s - 1) * (partialSum a x / (x : ℝ) ^ s)
          = partialSum a x * ((x : ℝ) ^ (s - 1) * (1 / (x : ℝ) ^ s)) := by ring
      _ = partialSum a x * (1 / (x : ℝ)) := by
        congr 1
        calc
          (x : ℝ) ^ (s - 1) * (1 / (x : ℝ) ^ s)
              = (x : ℝ) ^ (s - 1) * (x : ℝ) ^ (-s) := by
                  rw [one_div, Real.rpow_neg hxpos.le]
          _ = (x : ℝ) ^ ((s - 1) + (-s)) := by rw [← Real.rpow_add hxpos]
          _ = (x : ℝ) ^ (-1 : ℝ) := by congr 1; ring
          _ = 1 / (x : ℝ) := by simp [Real.rpow_neg_one, one_div]
      _ = partialSum a x / (x : ℝ) := by simp [div_eq_mul_inv]
  calc
    partialSum a x / (x : ℝ)
        = (x : ℝ) ^ (s - 1) * (partialSum a x / (x : ℝ) ^ s) := by
          rw [hleft]
    _ ≤ (x : ℝ) ^ (s - 1) * (B / (s - 1)) := hmul
    _ = B * (x : ℝ) ^ (s - 1) / (s - 1) := by ring

private lemma exists_delta_pole_bounds
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
      A - ε ≤ (s - 1) * ∑' n, a n / (n : ℝ) ^ s ∧
      (s - 1) * ∑' n, a n / (n : ℝ) ^ s ≤ A + ε := by
  let P : ℝ → Prop := fun s =>
    A - ε ≤ (s - 1) * ∑' n, a n / (n : ℝ) ^ s ∧
    (s - 1) * ∑' n, a n / (n : ℝ) ^ s ≤ A + ε
  have hP : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), P s :=
    eventually_pole_bounds a A hpole hε
  have hP' : ∀ᶠ s in nhds (1 : ℝ), s ∈ Set.Ioi (1 : ℝ) → P s :=
    (eventually_nhdsWithin_iff.mp hP)
  have hPt : {s : ℝ | s ∈ Set.Ioi (1 : ℝ) → P s} ∈ nhds (1 : ℝ) := hP'
  rcases Metric.mem_nhds_iff.mp hPt with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro s hs1 hsδ
  have hsabs : |s - 1| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs1.le)]
    linarith
  exact hball hsabs hs1

private lemma eventually_pole_bounds_at_zero_right
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A - ε ≤ t * ∑' n, a n / (n : ℝ) ^ (1 + t) ∧
      t * ∑' n, a n / (n : ℝ) ^ (1 + t) ≤ A + ε := by
  rcases exists_delta_pole_bounds a A hpole hε with ⟨δ, hδ, hδprop⟩
  refine (eventually_nhdsWithin_iff).2 ?_
  have hball : Metric.ball (0 : ℝ) δ ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hδ
  refine Filter.mem_of_superset hball ?_
  intro t ht htpos
  have htpos' : 0 < t := htpos
  have ht_lt : t < δ := by
    have habs : |t| < δ := by simpa [Metric.mem_ball, Real.dist_eq, sub_eq_add_neg] using ht
    have : t ≤ |t| := le_abs_self t
    exact lt_of_le_of_lt this habs
  have hs1 : 1 < 1 + t := by linarith
  have h := hδprop (1 + t) hs1 (by linarith)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using h

private lemma tendsto_one_div_add_atTop_nhdsWithin_zero_right :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  refine (tendsto_nhdsWithin_iff).2 ?_
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  exact Filter.Eventually.of_forall (fun n => by
    change 0 < (1 : ℝ) / (n + 1)
    positivity)

private lemma eventually_pole_bounds_on_nat
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A - ε ≤ (1 / (n + 1 : ℝ)) * ∑' k, a k / (k : ℝ) ^ (1 + (1 / (n + 1 : ℝ))) ∧
      (1 / (n + 1 : ℝ)) * ∑' k, a k / (k : ℝ) ^ (1 + (1 / (n + 1 : ℝ))) ≤ A + ε := by
  exact tendsto_one_div_add_atTop_nhdsWithin_zero_right.eventually
    (eventually_pole_bounds_at_zero_right a A hpole hε)

private noncomputable def poleNatSeq (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / (n + 1 : ℝ)) * ∑' k, a k / (k : ℝ) ^ (1 + (1 / (n + 1 : ℝ)))

private lemma tendsto_poleNatSeq
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    Tendsto (poleNatSeq a) atTop (nhds A) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (eventually_pole_bounds_on_nat a A hpole hε2))
  refine ⟨N, ?_⟩
  intro n hn
  have hn' := hN n hn
  rcases hn' with ⟨hlo, hhi⟩
  have hlo' : A - ε / 2 ≤ poleNatSeq a n := by
    simpa [poleNatSeq] using hlo
  have hhi' : poleNatSeq a n ≤ A + ε / 2 := by
    simpa [poleNatSeq] using hhi
  have hdist : dist (poleNatSeq a n) A < ε := by
    have : |poleNatSeq a n - A| ≤ ε / 2 := by
      rw [abs_le]
      constructor <;> linarith [hlo', hhi']
    have : |poleNatSeq a n - A| < ε := by linarith
    simpa [Real.dist_eq] using this
  exact hdist

private lemma tendsto_inv_log_nat_add_two_nhdsWithin_zero_right :
    Tendsto (fun n : ℕ => (Real.log ((n + 2 : ℕ) : ℝ))⁻¹) atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  refine (tendsto_nhdsWithin_iff).2 ?_
  refine ⟨?_, ?_⟩
  · have hnat : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 2)
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hnat)
  · exact Filter.Eventually.of_forall (fun n => by
      have hlog : 0 < Real.log ((n + 2 : ℕ) : ℝ) := by
        refine Real.log_pos ?_
        exact_mod_cast (show 1 < n + 2 by omega)
      exact inv_pos.mpr hlog)

private noncomputable def poleLogSeq (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.log ((n + 2 : ℕ) : ℝ))⁻¹ *
    ∑' k, a k / (k : ℝ) ^ (1 + (Real.log ((n + 2 : ℕ) : ℝ))⁻¹)

private lemma tendsto_poleLogSeq
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    Tendsto (poleLogSeq a) atTop (nhds A) := by
  have hcomp :
      Tendsto (fun n : ℕ => (Real.log ((n + 2 : ℕ) : ℝ))⁻¹)
        atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_inv_log_nat_add_two_nhdsWithin_zero_right
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hEv :
      ∀ᶠ n : ℕ in atTop,
        A - ε / 2 ≤
            (Real.log ((n + 2 : ℕ) : ℝ))⁻¹ *
              ∑' k, a k / (k : ℝ) ^ (1 + (Real.log ((n + 2 : ℕ) : ℝ))⁻¹) ∧
        (Real.log ((n + 2 : ℕ) : ℝ))⁻¹ *
              ∑' k, a k / (k : ℝ) ^ (1 + (Real.log ((n + 2 : ℕ) : ℝ))⁻¹) ≤
            A + ε / 2 := by
    exact hcomp.eventually (eventually_pole_bounds_at_zero_right a A hpole hε2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEv
  refine ⟨N, ?_⟩
  intro n hn
  have hn' := hN n hn
  rcases hn' with ⟨hlo, hhi⟩
  have hlo' : A - ε / 2 ≤ poleLogSeq a n := by
    simpa [poleLogSeq] using hlo
  have hhi' : poleLogSeq a n ≤ A + ε / 2 := by
    simpa [poleLogSeq] using hhi
  have hdist : dist (poleLogSeq a n) A < ε := by
    have : |poleLogSeq a n - A| ≤ ε / 2 := by
      rw [abs_le]
      constructor <;> linarith [hlo', hhi']
    have : |poleLogSeq a n - A| < ε := by linarith
    simpa [Real.dist_eq] using this
  exact hdist

private lemma partialSum_ratio_le_log_scaled_poleLogSeq
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (n : ℕ) :
    partialSum a (n + 2) / (n + 2 : ℝ) ≤
      poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) *
        Real.log ((n + 2 : ℕ) : ℝ) := by
  let t : ℝ := (Real.log ((n + 2 : ℕ) : ℝ))⁻¹
  have hs : 1 < 1 + t := by
    have htpos : 0 < t := by
      dsimp [t]
      exact inv_pos.mpr (Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega)))
    linarith
  have hB : ((1 + t) - 1) * (∑' k, a k / (k : ℝ) ^ (1 + t)) ≤ poleLogSeq a n := by
    have hEq : ((1 + t) - 1) * (∑' k, a k / (k : ℝ) ^ (1 + t)) = poleLogSeq a n := by
      dsimp [t, poleLogSeq]
      ring_nf
    exact hEq.le
  have hmain := partialSum_div_le_of_pole_upper a ha hconv hs hB (x := n + 2) (by omega)
  have hmain' :
      partialSum a (n + 2) / (n + 2 : ℝ) ≤
        poleLogSeq a n * ((n + 2 : ℝ) ^ ((1 + t) - 1)) / ((1 + t) - 1) := by
    simpa using hmain
  calc
    partialSum a (n + 2) / (n + 2 : ℝ)
        ≤ poleLogSeq a n * ((n + 2 : ℝ) ^ ((1 + t) - 1)) / ((1 + t) - 1) := hmain'
    _ = poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) *
          Real.log ((n + 2 : ℕ) : ℝ) := by
      have hlog_pos : 0 < Real.log ((n + 2 : ℕ) : ℝ) := by
        refine Real.log_pos ?_
        exact_mod_cast (show 1 < n + 2 by omega)
      have hlog_ne : Real.log ((n + 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt hlog_pos
      dsimp [t]
      rw [div_eq_mul_inv]
      ring_nf
      simp [inv_inv]
      ring

private lemma tendsto_rpow_inv_log_nat_add_two :
    Tendsto (fun n : ℕ => ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) )
      atTop (nhds (Real.exp 1)) := by
  have hEq :
      (fun n : ℕ => ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) ) =
        (fun _ : ℕ => Real.exp 1) := by
    funext n
    have hpos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hne1 : ((n + 2 : ℕ) : ℝ) ≠ 1 := by
      exact_mod_cast (show (n + 2 : ℕ) ≠ 1 by omega)
    simpa using (Real.rpow_inv_log hpos hne1)
  rw [hEq]
  exact tendsto_const_nhds

private lemma partialSum_ratio_div_log_le_poleLogScaled
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (n : ℕ) :
    partialSum a (n + 2) / ((n + 2 : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)) ≤
      poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) := by
  have hmain := partialSum_ratio_le_log_scaled_poleLogSeq a ha hconv n
  have hlog_nonneg : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
    exact le_of_lt (Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega)))
  have hdiv := div_le_div_of_nonneg_right hmain hlog_nonneg
  have hlog_ne : Real.log ((n + 2 : ℕ) : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega)))
  calc
    partialSum a (n + 2) / ((n + 2 : ℝ) * Real.log ((n + 2 : ℕ) : ℝ))
        = (partialSum a (n + 2) / (n + 2 : ℝ)) / Real.log ((n + 2 : ℕ) : ℝ) := by
          have hnp2_ne : (n + 2 : ℝ) ≠ 0 := by positivity
          field_simp [hnp2_ne, hlog_ne]
    _ ≤ (poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) *
          Real.log ((n + 2 : ℕ) : ℝ)) / Real.log ((n + 2 : ℕ) : ℝ) := hdiv
    _ = poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) := by
          field_simp [hlog_ne]

private lemma tendsto_poleLogSeq_mul_rpow_inv_log_nat_add_two
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    Tendsto (fun n : ℕ =>
      poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)))
      atTop (nhds (A * Real.exp 1)) := by
  have hPole : Tendsto (poleLogSeq a) atTop (nhds A) := tendsto_poleLogSeq a A hpole
  have hScale :
      Tendsto (fun n : ℕ => ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)))
        atTop (nhds (Real.exp 1)) := tendsto_rpow_inv_log_nat_add_two
  simpa [mul_comm, mul_left_comm, mul_assoc] using hPole.mul hScale

private lemma tendsto_atTop_shift_iff {f : ℕ → ℝ} {l : ℝ} (k : ℕ) :
    Tendsto f atTop (nhds l) ↔ Tendsto (fun n : ℕ => f (n + k)) atTop (nhds l) := by
  simpa [Nat.add_comm] using (tendsto_add_atTop_iff_nat k : Tendsto (fun n : ℕ => f (n + k)) atTop (nhds l) ↔
    Tendsto f atTop (nhds l)).symm

private lemma shifted_partialSum_ratio_eq
    (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 (n + 2), a k) / (n + 2 : ℝ) = partialSum a (n + 2) / (n + 2 : ℝ) := by
  rfl

private lemma eventually_le_add_of_tendsto {f : ℕ → ℝ} {l ε : ℝ}
    (hf : Tendsto f atTop (nhds l)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, f n ≤ l + ε := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hf) ε hε
  have hdist :
      ∀ᶠ n : ℕ in atTop, dist (f n) l < ε := Filter.eventually_atTop.mpr ⟨N, hN⟩
  filter_upwards [hdist] with n hn
  have hn' : |f n - l| < ε := by simpa [Real.dist_eq] using hn
  linarith [(abs_lt.mp hn').2]

private lemma eventually_sub_le_of_tendsto {f : ℕ → ℝ} {l ε : ℝ}
    (hf : Tendsto f atTop (nhds l)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, l - ε ≤ f n := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hf) ε hε
  have hdist :
      ∀ᶠ n : ℕ in atTop, dist (f n) l < ε := Filter.eventually_atTop.mpr ⟨N, hN⟩
  filter_upwards [hdist] with n hn
  have hn' : |f n - l| < ε := by simpa [Real.dist_eq] using hn
  linarith [(abs_lt.mp hn').1]

private lemma tendsto_atTop_of_eventually_between {f : ℕ → ℝ} {l : ℝ}
    (hbetween : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, l - ε ≤ f n ∧ f n ≤ l + ε) :
    Tendsto f atTop (nhds l) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hEv := hbetween (ε / 2) hε2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEv
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨hlo, hhi⟩
  have habs : |f n - l| < ε := by
    have hle : |f n - l| ≤ ε / 2 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  simpa [Real.dist_eq] using habs

private lemma tendsto_div_of_monotone_of_subseq_one_add_inv
    (u : ℕ → ℝ) (l : ℝ) (hmono : Monotone u)
    (hsub :
      ∀ k : ℕ,
        Tendsto (fun n : ℕ =>
          u (Nat.floor (((1 : ℝ) + (1 / (k + 1 : ℝ))) ^ n)) /
            (Nat.floor (((1 : ℝ) + (1 / (k + 1 : ℝ))) ^ n) : ℝ))
          atTop (nhds l)) :
    Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (nhds l) := by
  let c : ℕ → ℝ := fun k => (1 : ℝ) + (1 / (k + 1 : ℝ))
  have hcone : ∀ k, 1 < c k := by
    intro k
    dsimp [c]
    have : 0 < (1 / (k + 1 : ℝ)) := by positivity
    linarith
  have hclim : Tendsto c atTop (nhds 1) := by
    have honeDiv : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [c] using tendsto_const_nhds.add honeDiv
  have hsub' : ∀ k, Tendsto (fun n : ℕ => u ⌊c k ^ n⌋₊ / (⌊c k ^ n⌋₊ : ℝ)) atTop (nhds l) := by
    intro k
    simpa [c] using hsub k
  simpa using tendsto_div_of_monotone_of_tendsto_div_floor_pow u l hmono c hcone hclim hsub'

private lemma partialSum_ratio_le_scaled_poleNatSeq
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (n : ℕ) :
    partialSum a (n + 1) / (n + 1 : ℝ) ≤
      poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) * (n + 1 : ℝ) := by
  have hs : 1 < (1 + (1 / (n + 1 : ℝ))) := by
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hB :
      ((1 + (1 / (n + 1 : ℝ))) - 1) *
        (∑' k, a k / (k : ℝ) ^ (1 + (1 / (n + 1 : ℝ)))) ≤ poleNatSeq a n := by
    simp [poleNatSeq]
  have hmain := partialSum_div_le_of_pole_upper a ha hconv hs hB (x := n + 1) (by omega)
  have hmain' :
      partialSum a (n + 1) / (n + 1 : ℝ) ≤
        poleNatSeq a n * ((n + 1 : ℝ) ^ ((1 + (1 / (n + 1 : ℝ))) - 1)) /
          ((1 + (1 / (n + 1 : ℝ))) - 1) := by
    simpa using hmain
  calc
    partialSum a (n + 1) / (n + 1 : ℝ)
        ≤ poleNatSeq a n * ((n + 1 : ℝ) ^ ((1 + (1 / (n + 1 : ℝ))) - 1)) /
            ((1 + (1 / (n + 1 : ℝ))) - 1) := hmain'
    _ = poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) * (n + 1 : ℝ) := by
      have hnp1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hnp1_ne]
      ring_nf

private lemma tendsto_rpow_one_div_nat_add_one :
    Tendsto (fun n : ℕ => ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ)))) atTop (nhds 1) := by
  have hlogdiv : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have h := tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 one_ne_zero
    have hplus : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hplus
    have h' : Tendsto (fun n : ℕ => Real.log (((n + 1 : ℕ) : ℝ)) ^ (1 : ℕ) /
        (1 * (((n + 1 : ℕ) : ℝ)) + 0)) atTop (nhds 0) := h.comp hcast
    simpa using h'
  have hexp : Tendsto (fun n : ℕ => Real.exp (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))) atTop
      (nhds (Real.exp 0)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlogdiv
  have hEq : (fun n : ℕ => ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ)))) =
      (fun n : ℕ => Real.exp (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))) := by
    funext n
    have hnpos : 0 < ((n : ℝ) + 1) := by positivity
    rw [Real.rpow_def_of_pos hnpos]
    ring_nf
  rw [hEq]
  simpa using hexp

private lemma tendsto_poleNatSeq_mul_scale
    (a : ℕ → ℝ)
    (A : ℝ)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    Tendsto (fun n : ℕ => poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))))
      atTop (nhds A) := by
  have hPole : Tendsto (poleNatSeq a) atTop (nhds A) := tendsto_poleNatSeq a A hpole
  have hScale : Tendsto (fun n : ℕ => ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ)))) atTop (nhds 1) :=
    tendsto_rpow_one_div_nat_add_one
  simpa using hPole.mul hScale

private lemma partialSum_ratio_sq_le_poleScaled
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (n : ℕ) :
    partialSum a (n + 1) / ((n + 1 : ℝ) ^ 2) ≤
      poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) := by
  have h := partialSum_ratio_le_scaled_poleNatSeq a ha hconv n
  have hnp1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hnp1_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right h hnp1_nonneg
  have hden : ((n + 1 : ℝ) ^ 2) = (n + 1 : ℝ) * (n + 1 : ℝ) := by ring
  calc
    partialSum a (n + 1) / ((n + 1 : ℝ) ^ 2)
        = (partialSum a (n + 1) / (n + 1 : ℝ)) / (n + 1 : ℝ) := by
          field_simp [hden, hnp1_pos.ne']
    _ ≤ (poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) * (n + 1 : ℝ)) / (n + 1 : ℝ) := hdiv
    _ = poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) := by
          field_simp [hnp1_pos.ne']

private lemma partialSum_div_rpow_tendsto_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N : ℕ => partialSum a N / (N : ℝ) ^ s) atTop (nhds 0) := by
  -- Pick s' = (1+s)/2 ∈ (1,s); then u(N)/N^s ≤ F(s')·N^{s'-s} → 0
  have hs'1 : 1 < (1 + s) / 2 := by linarith
  have hd : 0 < s - (1 + s) / 2 := by linarith
  set C := ∑' n, a n / (n : ℝ) ^ ((1 + s) / 2)
  have htend : Tendsto (fun N : ℕ => C * (N : ℝ) ^ ((1 + s) / 2 - s)) atTop (nhds 0) := by
    have heq : (1 + s) / 2 - s = -(s - (1 + s) / 2) := by ring
    rw [heq]
    have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(s - (1 + s) / 2))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
    have : C * 0 = 0 := mul_zero C
    rw [← this]
    exact tendsto_const_nhds.mul h0
  apply squeeze_zero
  · intro N
    exact div_nonneg (partialSum_nonneg a ha N) (rpow_nonneg (Nat.cast_nonneg' N) s)
  · intro N
    show partialSum a N / (N : ℝ) ^ s ≤ C * (N : ℝ) ^ ((1 + s) / 2 - s)
    rcases Nat.eq_zero_or_pos N with rfl | hNp
    · have hexp_ne : (1 + s) / 2 - s ≠ 0 := by linarith
      simp [partialSum, zero_rpow hexp_ne]
    · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hNp
      have hNs_pos : (0 : ℝ) < (N : ℝ) ^ s := rpow_pos_of_pos hNpos s
      have hNs'_pos : (0 : ℝ) < (N : ℝ) ^ ((1 + s) / 2) := rpow_pos_of_pos hNpos _
      rw [div_le_iff₀ hNs_pos]
      have hrpow : C * (N : ℝ) ^ ((1 + s) / 2 - s) * (N : ℝ) ^ s =
          C * (N : ℝ) ^ ((1 + s) / 2) := by
        rw [mul_assoc, ← rpow_add hNpos]; ring_nf
      rw [hrpow]
      exact (div_le_iff₀ hNs'_pos).mp
        (partialSum_div_rpow_le_tsum a ha hconv hs'1 (Nat.one_le_of_lt hNp))
  · exact htend

/-! ## Core Tauberian Theorem -/

/-  **Karamata Monotone Tauberian** (Tenenbaum II.7.2).

    For nonneg a(n) and monotone u = partialSum a, if (s-1)·F(s) → A as s → 1+,
    then for any fixed c > 1, the geometric subsequence u(⌊cⁿ⌋)/⌊cⁿ⌋ → A.

    This is a genuine Tauberian theorem (converse of the Abelian direction).
    The standard proof uses Abel integral representation + monotone comparison:
    upper bound via contradiction (if u(T)/T > A+ε persistently, then (s-1)F(s) > A+ε);
    lower bound via tail control using the upper bound.

    Status: not yet in Mathlib. The Abelian direction (Landau's theorem) is in
    `Mathlib.NumberTheory.LSeries.SumCoeff` as
    `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg`.

    References: Tenenbaum II.7.2, Montgomery–Vaughan §8.3, Korevaar Ch. III. -/

/-- Upper bound half of Karamata: limsup u(⌊cⁿ⌋)/⌊cⁿ⌋ ≤ A.

    This is the harder half. The naive bound u(x)/x^s ≤ F(s) only gives
    u(x)/x ≤ F(s)·x^{s-1} ~ (A/(s-1))·x^{s-1}, which diverges for any fixed s > 1.
    The genuine Tauberian content requires Abel summation by parts:
      F(s) = ∑ (u(n)/n) · n·[1/n^s - 1/(n+1)^s],  ∑ n·[1/n^s - 1/(n+1)^s] = ζ(s).
    If u(n)/n ≥ A+ε eventually, then F(s) ≥ (A+ε)·ζ(s) + O(1), giving
    (s-1)F(s) ≥ (A+ε) + o(1) as s → 1+, contradicting (s-1)F(s) → A.
    Combined with the slowly-decreasing property u(n+1)/(n+1) ≥ u(n)/n · n/(n+1),
    the limsup bound follows by Karamata's method (Tenenbaum II.7.2, Korevaar III). -/
private lemma karamata_limsup_le
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ) (hA : 0 < A)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    (c : ℝ) (hc : 1 < c)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      partialSum a (Nat.floor (c ^ n)) / (Nat.floor (c ^ n) : ℝ) ≤ A + ε := by
  sorry

/-- Lower bound half of Karamata: liminf u(⌊cⁿ⌋)/⌊cⁿ⌋ ≥ A.

    Symmetric to the upper bound: if u(n)/n ≤ A-ε eventually, then by Abel summation
    F(s) ≤ (A-ε)·ζ(s) + O(1), giving (s-1)F(s) ≤ A-ε + o(1), contradiction.
    The slowly-decreasing property and Karamata's method close the argument.
    References: Tenenbaum II.7.2, Korevaar Ch. III. -/
private lemma karamata_liminf_ge
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ) (hA : 0 < A)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    (c : ℝ) (hc : 1 < c)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A - ε ≤ partialSum a (Nat.floor (c ^ n)) / (Nat.floor (c ^ n) : ℝ) := by
  sorry

private theorem karamata_monotone_geom
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ) (hA : 0 < A)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A))
    (c : ℝ) (hc : 1 < c) :
    Tendsto (fun n : ℕ => partialSum a (Nat.floor (c ^ n)) / (Nat.floor (c ^ n) : ℝ))
      atTop (nhds A) := by
  apply tendsto_atTop_of_eventually_between
  intro ε hε
  exact Filter.Eventually.and
    (karamata_liminf_ge a ha hconv A hA hpole c hc ε hε)
    (karamata_limsup_le a ha hconv A hA hpole c hc ε hε)

/-! ## Main Theorem -/

/-- **Landau's Tauberian Theorem** (1908).

    If a(n) ≥ 0, F(s) = Σ a(n)/n^s converges for s > 1,
    and (s-1)·F(s) → A > 0 as s → 1+ (real approach from above),
    then Σ_{n≤x} a(n) / x → A.

    Proof strategy (real-variable, Tenenbaum II.7):
    1. Upper bound: At s = 1 + 1/log(x), nonnegativity gives
       F(s) ≥ Σ_{n≤x} a(n)/n^s ≥ e^{-1} · Σ_{n≤x} a(n)/n.
       Partial summation converts to S(x)/x.
    2. Lower bound: F(s) = Σ_{n≤x} + Σ_{n>x}. The tail vanishes as x → ∞
       for fixed s > 1. Nonnegativity bounds each tail term.
    3. Squeeze: both bounds converge to A, so S(x)/x → A. -/
theorem landau_tauberian
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ) (hA : 0 < A)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
              (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, a n) / (x : ℝ))
      atTop (nhds A) := by
  let u : ℕ → ℝ := partialSum a
  have hu_nonneg : ∀ n, 0 ≤ u n := partialSum_nonneg a ha
  have hu_mono : Monotone u := fun m n hmn => partialSum_mono a ha hmn
  have hGeomReduce :
      (∀ k : ℕ,
        Tendsto (fun n : ℕ =>
          u (Nat.floor (((1 : ℝ) + (1 / (k + 1 : ℝ))) ^ n)) /
            (Nat.floor (((1 : ℝ) + (1 / (k + 1 : ℝ))) ^ n) : ℝ))
          atTop (nhds A)) →
      Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (nhds A) := by
    intro hsub
    exact tendsto_div_of_monotone_of_subseq_one_add_inv u A hu_mono hsub
  have hPoleNat (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop,
        A - ε ≤ (1 / (n + 1 : ℝ)) * ∑' k, a k / (k : ℝ) ^ (1 + (1 / (n + 1 : ℝ))) ∧
        (1 / (n + 1 : ℝ)) * ∑' k, a k / (k : ℝ) ^ (1 + (1 / (n + 1 : ℝ))) ≤ A + ε :=
    eventually_pole_bounds_on_nat a A hpole hε
  have hPoleSeq : Tendsto (poleNatSeq a) atTop (nhds A) :=
    tendsto_poleNatSeq a A hpole
  have hShiftGoal :
      Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, a n) / (x : ℝ)) atTop (nhds A) ↔
      Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 (n + 2), a k) / (n + 2 : ℝ)) atTop (nhds A) := by
    simpa using
      (tendsto_atTop_shift_iff
        (f := fun x : ℕ => (∑ n ∈ Icc 1 x, a n) / (x : ℝ)) (l := A) 2)
  have hPoleLogSeq : Tendsto (poleLogSeq a) atTop (nhds A) :=
    tendsto_poleLogSeq a A hpole
  have hTransferLog (n : ℕ) :
      u (n + 2) / (n + 2 : ℝ) ≤
        poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) *
          Real.log ((n + 2 : ℕ) : ℝ) := by
    simpa [u] using partialSum_ratio_le_log_scaled_poleLogSeq a ha hconv n
  have hTransferLogNorm (n : ℕ) :
      u (n + 2) / ((n + 2 : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)) ≤
        poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)) := by
    simpa [u] using partialSum_ratio_div_log_le_poleLogScaled a ha hconv n
  have hScaleLog :
      Tendsto (fun n : ℕ => ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)))
        atTop (nhds (Real.exp 1)) :=
    tendsto_rpow_inv_log_nat_add_two
  have hPoleLogScaled :
      Tendsto (fun n : ℕ =>
        poleLogSeq a n * ((n + 2 : ℝ) ^ ((Real.log ((n + 2 : ℕ) : ℝ))⁻¹)))
        atTop (nhds (A * Real.exp 1)) :=
    tendsto_poleLogSeq_mul_rpow_inv_log_nat_add_two a A hpole
  have hTransferUpper (n : ℕ) :
      u (n + 1) / (n + 1 : ℝ) ≤
        poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) * (n + 1 : ℝ) := by
    simpa [u] using partialSum_ratio_le_scaled_poleNatSeq a ha hconv n
  have hScale : Tendsto (fun n : ℕ => ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ)))) atTop (nhds 1) :=
    tendsto_rpow_one_div_nat_add_one
  have hPoleScaled :
      Tendsto (fun n : ℕ => poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))))
        atTop (nhds A) :=
    tendsto_poleNatSeq_mul_scale a A hpole
  have hTransferUpperSq (n : ℕ) :
      u (n + 1) / ((n + 1 : ℝ) ^ 2) ≤
        poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) := by
    simpa [u] using partialSum_ratio_sq_le_poleScaled a ha hconv n
  have hPoleScaledUpper :
      ∀ᶠ n : ℕ in atTop,
        poleNatSeq a n * ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ))) ≤ A + 1 := by
    have hA1 : 0 < (1 : ℝ) := by positivity
    exact eventually_le_add_of_tendsto hPoleScaled hA1
  have hQuadUpper :
      ∀ᶠ n : ℕ in atTop, u (n + 1) ≤ (A + 1) * ((n + 1 : ℝ) ^ 2) := by
    filter_upwards [hPoleScaledUpper] with n hn
    have hstep : u (n + 1) / ((n + 1 : ℝ) ^ 2) ≤ A + 1 := (hTransferUpperSq n).trans hn
    have hsq_nonneg : 0 ≤ ((n + 1 : ℝ) ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hstep hsq_nonneg
    have hsq_pos : 0 < ((n + 1 : ℝ) ^ 2) := by positivity
    -- clear the normalization on the left
    have hleft : (u (n + 1) / ((n + 1 : ℝ) ^ 2)) * ((n + 1 : ℝ) ^ 2) = u (n + 1) := by
      field_simp [hsq_pos.ne']
    calc
      u (n + 1) = (u (n + 1) / ((n + 1 : ℝ) ^ 2)) * ((n + 1 : ℝ) ^ 2) := hleft.symm
      _ ≤ (A + 1) * ((n + 1 : ℝ) ^ 2) := by simpa [mul_assoc] using hmul
  have hMainDiv : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (nhds A) := by
    refine hGeomReduce ?_
    intro k
    let c : ℝ := (1 : ℝ) + (1 / (k + 1 : ℝ))
    let m : ℕ → ℕ := fun n => Nat.floor (c ^ n)
    have hc_gt_one : 1 < c := by
      dsimp [c]
      have : 0 < (1 / (k + 1 : ℝ)) := by positivity
      linarith
    have hm_atTop : Tendsto m atTop atTop := by
      dsimp [m]
      exact (tendsto_nat_floor_atTop (α := ℝ)).comp (tendsto_pow_atTop_atTop_of_one_lt hc_gt_one)
    have hm_one_le (n : ℕ) : 1 ≤ m n := by
      dsimp [m]
      refine (Nat.one_le_floor_iff _).mpr ?_
      exact one_le_pow₀ hc_gt_one.le
    have hm_ratio_tendsto_one :
        Tendsto (fun n : ℕ => (m n : ℝ) / (m n + 1 : ℝ)) atTop (nhds 1) := by
      have hm_succ_atTop : Tendsto (fun n : ℕ => m n + 1) atTop atTop :=
        (tendsto_add_atTop_nat 1).comp hm_atTop
      have hm_succ_cast_atTop' : Tendsto (fun n : ℕ => ((m n + 1 : ℕ) : ℝ)) atTop atTop := by
        exact
          ((tendsto_natCast_atTop_atTop : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop).comp
            hm_succ_atTop)
      have hm_succ_cast_atTop : Tendsto (fun n : ℕ => (m n : ℝ) + 1) atTop atTop := by
        convert hm_succ_cast_atTop' using 1
        funext n
        norm_num [Nat.cast_add]
      have hm_succ_inv_zero : Tendsto (fun n : ℕ => ((m n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hm_succ_cast_atTop
      have hEq :
          (fun n : ℕ => (m n : ℝ) / (m n + 1 : ℝ)) =
            (fun n : ℕ => 1 - ((m n : ℝ) + 1)⁻¹) := by
        funext n
        have hm1_ne : ((m n : ℝ) + 1) ≠ 0 := by positivity
        calc
          (m n : ℝ) / (m n + 1 : ℝ) = (((m n : ℝ) + 1) - 1) / ((m n : ℝ) + 1) := by ring
          _ = 1 - ((m n : ℝ) + 1)⁻¹ := by
            field_simp [hm1_ne]
      rw [hEq]
      simpa using tendsto_const_nhds.sub hm_succ_inv_zero
    have hPoleNatSubseq (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ n : ℕ in atTop,
          A - ε ≤
              (1 / (m n + 1 : ℝ)) *
                ∑' j, a j / (j : ℝ) ^ (1 + (1 / (m n + 1 : ℝ))) ∧
          (1 / (m n + 1 : ℝ)) *
                ∑' j, a j / (j : ℝ) ^ (1 + (1 / (m n + 1 : ℝ))) ≤
              A + ε := by
      exact hm_atTop.eventually (hPoleNat ε hε)
    have hPoleScaledSubseq :
        Tendsto (fun n : ℕ => poleNatSeq a (m n) * ((m n + 1 : ℝ) ^ (1 / (m n + 1 : ℝ))))
          atTop (nhds A) := hPoleScaled.comp hm_atTop
    have hTransferUpperSqSubseq (n : ℕ) :
        u (m n + 1) / ((m n + 1 : ℝ) ^ 2) ≤
          poleNatSeq a (m n) * ((m n + 1 : ℝ) ^ (1 / (m n + 1 : ℝ))) := by
      simpa using hTransferUpperSq (m n)
    have hNonnegSubseq (n : ℕ) : 0 ≤ u (m n + 1) := hu_nonneg (m n + 1)
    have _ := hPoleNatSubseq
    have _ := hPoleScaledSubseq
    have _ := hTransferUpperSqSubseq
    have _ := hNonnegSubseq
    have _ := hm_one_le
    have _ := hm_ratio_tendsto_one
    have hPoleSubseq : Tendsto (fun n : ℕ => poleNatSeq a (m n)) atTop (nhds A) :=
      hPoleSeq.comp hm_atTop
    have hScaleSubseq :
        Tendsto (fun n : ℕ => ((m n + 1 : ℝ) ^ (1 / (m n + 1 : ℝ)))) atTop (nhds 1) := by
      simpa using (tendsto_rpow_one_div_nat_add_one.comp hm_atTop)
    have hQuadUpperSubseq :
        ∀ᶠ n : ℕ in atTop, u (m n + 1) ≤ (A + 1) * ((m n + 1 : ℝ) ^ 2) := by
      exact hm_atTop.eventually hQuadUpper
    have _ := hPoleSubseq
    have _ := hScaleSubseq
    have _ := hQuadUpperSubseq
    have hPoleSubseqUpper :
        ∀ᶠ n : ℕ in atTop, poleNatSeq a (m n) ≤ A + 1 := by
      exact eventually_le_add_of_tendsto hPoleSubseq (by positivity)
    have hPoleSubseqLower :
        ∀ᶠ n : ℕ in atTop, A - 1 ≤ poleNatSeq a (m n) := by
      exact eventually_sub_le_of_tendsto hPoleSubseq (by positivity)
    have _ := hPoleSubseqUpper
    have _ := hPoleSubseqLower
    suffices hSubseqDiv : Tendsto (fun n : ℕ => u (m n) / (m n : ℝ)) atTop (nhds A) by
      simpa [m, c] using hSubseqDiv
    -- Karamata monotone Tauberian: Abel integral F(s) = s∫u(t)/t^{s+1}dt + monotone
    -- comparison closes the squeeze for the fixed geometric subsequence.
    -- u = partialSum a, m n = ⌊c^n⌋, c = 1 + 1/(k+1) > 1.
    have hKaramata := karamata_monotone_geom a ha hconv A hA hpole c hc_gt_one
    simp only [u, m] at hKaramata ⊢
    exact hKaramata
  simpa [u] using hMainDiv

/-- Corollary: eventual linear lower bound with coefficient A/2.
    For twin primes, we only need pairCorrelation ≥ c·x for some c > 0. -/
theorem landau_tauberian_linear_lower
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hconv : ∀ s : ℝ, 1 < s → Summable (fun n => a n / (n : ℝ) ^ s))
    (A : ℝ) (hA : 0 < A)
    (hpole : Tendsto (fun s => (s - 1) * ∑' n, a n / (n : ℝ) ^ s)
              (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    ∃ (c : ℝ) (x₀ : ℕ), 0 < c ∧ ∀ x : ℕ, x₀ ≤ x →
      c * (x : ℝ) ≤ ∑ n ∈ Icc 1 x, a n := by
  have h_tend := landau_tauberian a ha hconv A hA hpole
  -- From S(x)/x → A, for ε = A/2, eventually |S(x)/x - A| < A/2
  -- So S(x)/x > A/2, hence S(x) > (A/2)·x
  rw [Metric.tendsto_atTop] at h_tend
  obtain ⟨x₀, hx₀⟩ := h_tend (A / 2) (by positivity)
  refine ⟨A / 2, max x₀ 1, by positivity, fun x hx => ?_⟩
  have hx_ge : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr (by omega : 0 < x)
  have hdist := hx₀ x hx_ge
  rw [Real.dist_eq] at hdist
  -- |S(x)/x - A| < A/2 → S(x)/x > A/2
  have h_lower : A / 2 < (∑ n ∈ Icc 1 x, a n) / (x : ℝ) := by
    have := (abs_lt.mp hdist).1; linarith
  linarith [(lt_div_iff₀ hxpos).mp h_lower]

end LandauTauberian
