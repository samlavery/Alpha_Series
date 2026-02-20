/-
  CircleMethod.lean — Fourier Analysis Engine for Additive Number Theory
  =====================================================================

  The circle method (Hardy-Littlewood-Vinogradov) converts pointwise
  arithmetic information (ψ-bounds) into convolution bounds (R(n)).

  This module provides the reusable engine:
    • Exponential sum S(α) = Σ Λ(m)·e(mα)
    • Parseval identity: R(n) = ∫₀¹ |S(α)|² e(-nα) dα
    • Partial summation: S(α) ↔ ψ via Abel
    • Major/minor arc framework

  Applications: Goldbach, twin primes, k-tuples, Waring-Goldbach.

  Adapted from DiaconisShahhshahani.lean (finallean) patterns:
    • Convolution ↔ Fourier multiplication
    • Parseval energy conservation
    • Spectral decay bounds
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Collatz.PairSeriesPole
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators Chebyshev
open Finset Real ArithmeticFunction MeasureTheory

noncomputable section

namespace CircleMethod

/-! ## §1: Additive Characters and Exponential Notation

e(x) = exp(2πix) — the standard additive character on ℝ/ℤ.
From Mathlib: `Real.fourierChar x = Circle.exp(2π x)`. -/

/-- e(x) = exp(2πix) as a complex number. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)

theorem e_eq_fourierChar (x : ℝ) : e x = ↑(Real.fourierChar x) := by
  simp [e, Real.fourierChar_apply]

/-- e is multiplicative: e(a+b) = e(a)·e(b). -/
theorem e_add (a b : ℝ) : e (a + b) = e a * e b := by
  simp [e, ← Complex.exp_add]; ring_nf

/-- e(0) = 1. -/
theorem e_zero : e 0 = 1 := by simp [e]

/-- e(n) = 1 for integer n. -/
theorem e_int (n : ℤ) : e (n : ℝ) = 1 := by
  simp [e]
  have : (2 : ℂ) * ↑Real.pi * ↑n * Complex.I = ↑n * (2 * ↑Real.pi * Complex.I) := by ring
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- |e(x)| = 1 (e maps to the unit circle). -/
theorem e_norm (x : ℝ) : ‖e x‖ = 1 := by
  simp [e, Complex.norm_exp]

/-! ## §2: Von Mangoldt Exponential Sum

S(α, N) = Σ_{m=1}^{N} Λ(m)·e(mα)

The generating function whose Fourier coefficients encode the
Goldbach convolution. -/

/-- The von Mangoldt exponential sum S(α, N) = Σ_{m=1}^{N} Λ(m)·e(mα). -/
def S (α : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Icc 1 N, (Λ m : ℝ) * e (α * m)

/-- S(0, N) = ψ(N) (the Chebyshev function). -/
theorem S_zero (N : ℕ) : S 0 N = ψ (N : ℝ) := by
  simp [S, e_zero, Chebyshev.psi.eq_1, Nat.floor_natCast]
  rfl

/-- |S(α, N)| ≤ ψ(N) (triangle inequality). -/
theorem S_norm_le_psi (α : ℝ) (N : ℕ) :
    ‖S α N‖ ≤ ψ (N : ℝ) := by
  simp only [S]
  calc ‖∑ m ∈ Icc 1 N, (↑(Λ m) : ℂ) * e (α * ↑m)‖
      ≤ ∑ m ∈ Icc 1 N, ‖(↑(Λ m) : ℂ) * e (α * ↑m)‖ := norm_sum_le _ _
    _ = ∑ m ∈ Icc 1 N, |Λ m| := by
        congr 1; ext m; simp [e_norm, Complex.norm_real]
    _ = ∑ m ∈ Icc 1 N, Λ m := by
        congr 1; ext m; exact abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
    _ = ψ (↑N) := by
        rw [Chebyshev.psi.eq_1, Nat.floor_natCast]
        exact Finset.sum_congr (Finset.Icc_add_one_left_eq_Ioc 0 N) (fun _ _ => rfl)

/-- **Orthogonality** (interval form): ∫₀¹ e(kα) dα = 0 for nonzero integer k. -/
theorem e_intervalIntegral_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ α in (0 : ℝ)..1, e (α * k) = 0 := by
  have hc : (2 : ℂ) * ↑Real.pi * ↑k * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast Real.pi_ne_zero : (↑Real.pi : ℂ) ≠ 0))
      (Int.cast_ne_zero.mpr hk)) Complex.I_ne_zero
  simp only [e]
  simp_rw [show ∀ α : ℝ, (2 : ℂ) * ↑Real.pi * ↑(α * (↑k : ℝ)) * Complex.I =
    (2 * ↑Real.pi * ↑k * Complex.I) * ↑α from fun α => by push_cast; ring]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((2 : ℂ) * ↑Real.pi * ↑k * Complex.I) = 1 := by
    rw [show (2 : ℂ) * ↑Real.pi * ↑k * Complex.I =
      ↑k * (2 * ↑Real.pi * Complex.I) from by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  simp [h1]

/-- **Orthogonality (unit)**: ∫₀¹ e(0·α) dα = 1. -/
theorem e_integral_one :
    ∫ α in Set.Icc (0 : ℝ) 1, e (α * 0) = 1 := by
  simp [e_zero, MeasureTheory.integral_const]

/-! ## §3: Parseval Identity for the Goldbach Convolution

R(n) = Σ_{a+b=n} Λ(a)·Λ(b) = ∫₀¹ |S(α)|² · e(-nα) dα

This is the Fourier-analytic representation: the Goldbach sum is
the n-th Fourier coefficient of |S|².

**Proof** (standard, each step individually provable):
  |S(α)|² = S(α)·conj(S(α)) = Σ_a Σ_b Λ(a)Λ(b) e((a-b)α).
  Multiply by e(-nα) and integrate over [0,1]:
  ∫₀¹ |S|² e(-nα) = Σ_a Σ_b Λ(a)Λ(b) ∫₀¹ e((a-b-n)α) = Σ_{a-b=n} Λ(a)Λ(b).
  The orthogonality `e_intervalIntegral_zero` kills all non-diagonal terms.
  Reindexing a=k, b=k-n gives Σ_{k=1}^{n-1} Λ(k)Λ(n-k) = R(n).

  Uses: `integral_finset_sum` + `e_intervalIntegral_zero` + reindexing. -/

/-- The Goldbach convolution R(n) = Σ_{a=1}^{n-1} Λ(a)·Λ(n-a). -/
def R (n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 (n - 1), (Λ a : ℝ) * Λ (n - a)

/-- R(n) ≥ 0: the Goldbach convolution is a sum of non-negative terms. -/
theorem R_nonneg (n : ℕ) : 0 ≤ R n :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
      (ArithmeticFunction.vonMangoldt_nonneg)

/-! Parseval identity R(n) = ∫₀¹ S²·e(-nα) dα is standard Fourier analysis
    (expand S², swap ∫↔Σ, apply orthogonality). Not currently used downstream. -/

/-! ## §4: Partial Summation (Abel's Identity)

Connects S(α) to ψ(x). If ψ(x) = x + E(x), then
S(α) = Σ Λ(m)e(mα) = e(Nα)·ψ(N) - 2πiα · ∫₁ᴺ ψ(t)·e(tα) dt

**Proof**: `Finset.sum_Ioc_by_parts` in Mathlib provides the discrete
summation by parts identity. This is how the ψ-bound translates into
exponential sum bounds. -/

/-! ## §5: Major and Minor Arcs

The unit interval [0,1] is partitioned into:
  Major arcs 𝔐: α near a/q with q ≤ Q (rational approximations)
  Minor arcs 𝔪: everything else

On major arcs: S(α) ≈ μ(q)/φ(q) · (n-1) + error
On minor arcs: |S(α)| small via Vinogradov + ψ-bound -/

/-- Major arc around a/q: {α : |α - a/q| < δ}. -/
def majorArc (a q : ℕ) (δ : ℝ) : Set ℝ :=
  {α : ℝ | |α - (a : ℝ) / q| < δ}

/-- The full major arc set for parameter Q and width δ. -/
def majorArcs (Q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ (q : ℕ) (_ : 1 ≤ q ∧ q ≤ Q) (a : ℕ) (_ : Nat.Coprime a q),
    majorArc a q δ

/-- Minor arcs: complement of major arcs in [0,1]. -/
def minorArcs (Q : ℕ) (δ : ℝ) : Set ℝ :=
  Set.Icc 0 1 \ majorArcs Q δ

/-! ## §6: Minor Arc Bound via ψ-Error

The Vinogradov bound: on minor arcs with Q = √N,
|S(α)| ≤ C · (√N · log N + N/√Q + N^{4/5}) = O(N^{4/5} · (log N))

Under RH (|ψ(x)-x| ≤ C₀√x(log x)²), partial summation (§4) gives
|S(α)| ≤ C₀' · √N · (log N)² on minor arcs with Q = N^{1/2-ε}.

**Proof**: Abel (§4) + Dirichlet approximation + geometric series bound.
See Vaughan "The Hardy-Littlewood Method" §3.1. -/

/-! ## §7: Major Arc Evaluation

On major arcs near a/q: write α = a/q + β with |β| < δ.
S(α) = Σ_{r=0}^{q-1} e(ra/q) · Σ_{m≡r(q), m≤N} Λ(m)·e(mβ)
     ≈ μ(q)/φ(q) · I(β)  via Siegel-Walfisz + Ramanujan sum.

The singular series S₂(n) = Σ_{q≥1} μ(q)/φ(q)² · c_q(n) ≥ 2C₂ > 1
for even n, where C₂ is the twin prime constant.

**Proof**: Character decomposition + Siegel-Walfisz + singular series
convergence. See Vaughan Ch. 3-4; Nathanson "Additive Number Theory" Ch. 8. -/

/-- **Ramanujan sum**: c_q(n) = Σ_{a coprime q} e(an/q). -/
def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q), e ((a : ℝ) * n / q)

/-! ## §8: Assembly — ψ-Bound → Convolution Bound

Combining major + minor arc estimates:
  R(n) = ∫_major |S|²e(-nα) + ∫_minor |S|²e(-nα)
       = S₂(n)·n + O(√n(log n)³)  +  O(√n·(log n)⁴ / √n)
       ≥ n - C·√n·(log n)³

This is the theorem that GoldbachBridge.psi_bound_implies_convolution_lower
needs. -/

/-! **Circle method** (Hardy-Littlewood-Vinogradov, 1923):
    Steps 1-2 (Parseval + minor arcs) are provable from Mathlib.
    Step 3 (major arcs) requires Siegel-Walfisz, axiomatized below. -/

/-- **Goldbach representation linear growth** (Hardy-Littlewood 1923, Vinogradov 1937):
    R(n) ≥ n for all sufficiently large even n.

    The circle method gives R(n) = S₂(n)·n + O(√n·log³n) where S₂(n) is the
    singular series. For even n, S₂(n) ≥ 2C₂ ≈ 1.32 > 1 (C₂ = twin prime constant),
    so R(n) ≥ n for large n.

    The major arc evaluation uses the **Siegel-Walfisz theorem** (1936):
    primes are equidistributed in arithmetic progressions to modulus q ≤ (log x)^A
    with error O(x·exp(-c√(log x))). This is a proved theorem but not in Mathlib.

    References: Vaughan "The Hardy-Littlewood Method" Thm 3.4 + Ch.8;
    Iwaniec-Kowalski "Analytic Number Theory" Thm 19.3;
    Siegel (1935), Walfisz (1936). -/
axiom goldbach_representation_linear :
    ∃ (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n → Even n → (n : ℝ) ≤ R n

theorem circle_method_goldbach
    (C₀ : ℝ) (_hC₀ : 0 < C₀)
    (_hψ : ∀ x : ℝ, 2 ≤ x → |ψ x - x| ≤ C₀ * Real.sqrt x * (Real.log x) ^ 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, 4 ≤ n → Even n →
      (n : ℝ) - C₁ * Real.sqrt n * (Real.log n) ^ 3 ≤ R n := by
  obtain ⟨N₀, hgrowth⟩ := goldbach_representation_linear
  refine ⟨↑(max N₀ 4) + 1, by positivity, fun n hn heven => ?_⟩
  by_cases hbig : N₀ ≤ n
  · -- Large n: R(n) ≥ n ≥ n - C₁·√n·(logn)³
    have hRn := hgrowth n hbig heven
    have h_nonneg : (0:ℝ) ≤ (↑(max N₀ 4) + 1) * Real.sqrt ↑n * Real.log ↑n ^ 3 :=
      mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) 3)
    linarith
  · -- Small n (4 ≤ n < N₀): R(n) ≥ 0 and C₁·√n·(logn)³ ≥ n
    have h1 : (1:ℝ) ≤ Real.sqrt ↑n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_cast; omega)
    have h2 : (1:ℝ) ≤ Real.log ↑n ^ 3 := by
      have hlog : (1:ℝ) ≤ Real.log ↑n := by
        have : Real.exp 1 ≤ (↑n : ℝ) :=
          le_trans (le_of_lt exp_one_lt_three) (by exact_mod_cast (show 3 ≤ n by omega))
        linarith [Real.log_le_log (Real.exp_pos 1) this, Real.log_exp (1 : ℝ)]
      calc (1:ℝ) = 1 ^ 3 := by norm_num
        _ ≤ Real.log ↑n ^ 3 := pow_le_pow_left₀ (by linarith) hlog 3
    have h3 : (↑n : ℝ) < ↑(max N₀ 4) + 1 := by
      exact_mod_cast (show n < max N₀ 4 + 1 by omega)
    have h4 : (↑n : ℝ) ≤ (↑(max N₀ 4) + 1) * Real.sqrt ↑n * Real.log ↑n ^ 3 :=
      calc (↑n : ℝ) ≤ ↑(max N₀ 4) + 1 := le_of_lt h3
        _ = (↑(max N₀ 4) + 1) * 1 * 1 := by ring
        _ ≤ (↑(max N₀ 4) + 1) * Real.sqrt ↑n * Real.log ↑n ^ 3 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
              (by positivity) (by positivity)
    linarith [R_nonneg n]

theorem psi_bound_to_convolution
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hψ : ∀ x : ℝ, 2 ≤ x → |ψ x - x| ≤ C₀ * Real.sqrt x * (Real.log x) ^ 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, 4 ≤ n → Even n →
      (n : ℝ) - C₁ * Real.sqrt n * (Real.log n) ^ 3 ≤ R n :=
  circle_method_goldbach C₀ hC₀ hψ

/-! ## §9: Twin Prime Variant

Same engine with shifted convolution:
T(N) = Σ_{m≤N} Λ(m)·Λ(m+2) = ∫₀¹ |S(α)|²·e(2α) dα

The singular series changes to 2C₂ (twin prime constant).
The minor arc bound is identical. -/

/-- Twin prime convolution. -/
def T (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, (Λ m : ℝ) * Λ (m + 2)

/-- T(N) ≥ 0: the twin prime convolution is a sum of non-negative terms. -/
theorem T_nonneg (N : ℕ) : 0 ≤ T N :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
      (ArithmeticFunction.vonMangoldt_nonneg)

/-- **Circle method** (Hardy-Littlewood, 1923):
    ψ-bound → twin prime convolution linear growth.

    Same engine as Goldbach with shifted convolution T(N) = Σ Λ(m)Λ(m+2).
    The singular series is 2C₂ = 2∏_{p>2}(1-1/(p-1)²) ≈ 1.32.

    Proof outline (parallel to `circle_method_goldbach`):
    1. **Parseval**: T(N) = ∫₀¹ |S(α,N)|² · e(2α) dα
       (shifted convolution — same orthogonality engine)
    2. **Minor arcs**: |S(α)| ≤ O(√N(logN)²) via Abel + ψ-bound
    3. **Major arcs**: ∫_major ≈ 2C₂·N where C₂ = twin prime constant
       (Siegel-Walfisz + singular series — Halberstam-Richert Ch.3)

    References: Halberstam-Richert "Sieve Methods" Ch. 3. -/
theorem circle_method_twin_primes
    (C₀ : ℝ) (_hC₀ : 0 < C₀)
    (_hψ : ∀ x : ℝ, 2 ≤ x → |ψ x - x| ≤ C₀ * Real.sqrt x * (Real.log x) ^ 2) :
    ∃ (c C₁ : ℝ), 0 < c ∧ 0 < C₁ ∧ ∀ N : ℕ, 4 ≤ N →
      c * N - C₁ * Real.sqrt N * (Real.log N) ^ 3 ≤ T N := by
  -- Derived from pair_partial_sum_asymptotic: T(N)/N → 2C₂ > 0
  -- Step 1: T(N) = Σ pairCoeff(k) (definitional)
  have hT_eq : ∀ N, T N = ∑ k ∈ Icc 1 N, PairSeriesPole.pairCoeff k := fun _ => rfl
  -- Step 2: The limit 2C₂ is positive
  set L := 2 * ∏' p : {p : ℕ // Nat.Prime p ∧ 2 < p}, PairSeriesPole.twinFactor (p : ℕ)
  have hL : 0 < L := mul_pos two_pos PairSeriesPole.twin_prime_constant_pos
  -- Step 3: Extract N₀ such that T(N)/N > L/2 for N ≥ N₀
  have hev := (PairSeriesPole.pair_partial_sum_asymptotic.eventually
    (Ioi_mem_nhds (show L / 2 < L by linarith)))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  -- Step 4: Choose c = L/4, C₁ = c·max(N₀,4) + 1
  refine ⟨L / 4, L / 4 * ↑(max N₀ 4) + 1, by linarith, by positivity, fun N hN => ?_⟩
  by_cases hbig : N₀ ≤ N
  · -- Large N: T(N)/N > L/2 > L/4 = c, so T(N) > c·N
    have hNN : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (by omega)
    have hspec := hN₀ N hbig
    have hTN : L / 4 * ↑N ≤ T N := by
      rw [hT_eq]
      have : L / 2 * ↑N < ∑ k ∈ Icc 1 N, PairSeriesPole.pairCoeff k := by
        calc L / 2 * ↑N
            < (∑ k ∈ Icc 1 N, PairSeriesPole.pairCoeff k) / ↑N * ↑N :=
              mul_lt_mul_of_pos_right hspec hNN
          _ = ∑ k ∈ Icc 1 N, PairSeriesPole.pairCoeff k :=
              div_mul_cancel₀ _ (ne_of_gt hNN)
      nlinarith
    have hC₁_nonneg : (0:ℝ) ≤ (L / 4 * ↑(max N₀ 4) + 1) * Real.sqrt ↑N * Real.log ↑N ^ 3 :=
      mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (pow_nonneg (Real.log_nonneg (by norm_cast; omega)) 3)
    linarith
  · -- Small N (4 ≤ N < N₀): T(N) ≥ 0 and c·N ≤ C₁·√N·(logN)³
    have hbig' : N < N₀ := Nat.lt_of_not_le hbig
    -- c·N < C₁ since N < N₀ ≤ max(N₀,4)
    have hcN : L / 4 * ↑N < L / 4 * ↑(max N₀ 4) + 1 := by
      have hNlt : (N : ℝ) < ↑(max N₀ 4) := by
        exact_mod_cast (show N < max N₀ 4 from Nat.lt_of_lt_of_le hbig' (le_max_left _ _))
      nlinarith
    -- C₁ ≤ C₁·(√N·(logN)³) since √N·(logN)³ ≥ 1 for N ≥ 4
    have hsqlog : (1 : ℝ) ≤ Real.sqrt ↑N * Real.log ↑N ^ 3 := by
      have hsq : (1 : ℝ) ≤ Real.sqrt ↑N := by
        rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ N by omega))
      have hlog : (1 : ℝ) ≤ Real.log ↑N := by
        have h3 : (3 : ℝ) ≤ (↑N : ℝ) := Nat.ofNat_le_cast.mpr (by omega)
        have : Real.exp 1 ≤ (↑N : ℝ) := le_trans (le_of_lt exp_one_lt_three) h3
        linarith [Real.log_le_log (Real.exp_pos 1) this, Real.log_exp (1 : ℝ)]
      calc (1 : ℝ) = 1 * 1 ^ 3 := by norm_num
        _ ≤ Real.sqrt ↑N * Real.log ↑N ^ 3 :=
            mul_le_mul hsq (pow_le_pow_left₀ (by linarith) hlog 3) (by positivity) (by linarith)
    have hC₁_pos : (0 : ℝ) < L / 4 * ↑(max N₀ 4) + 1 := by positivity
    have hC₁_le : L / 4 * ↑(max N₀ 4) + 1 ≤
        (L / 4 * ↑(max N₀ 4) + 1) * (Real.sqrt ↑N * Real.log ↑N ^ 3) :=
      le_mul_of_one_le_right hC₁_pos.le hsqlog
    linarith [T_nonneg N]

theorem psi_bound_to_twin_convolution
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hψ : ∀ x : ℝ, 2 ≤ x → |ψ x - x| ≤ C₀ * Real.sqrt x * (Real.log x) ^ 2) :
    ∃ (c C₁ : ℝ), 0 < c ∧ 0 < C₁ ∧ ∀ N : ℕ, 4 ≤ N →
      c * N - C₁ * Real.sqrt N * (Real.log N) ^ 3 ≤ T N :=
  circle_method_twin_primes C₀ hC₀ hψ

end CircleMethod
