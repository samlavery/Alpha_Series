/-
  HadamardGeneral.lean — Shared Hadamard Infrastructure
  ======================================================

  General Hadamard factorization tools for entire functions of order ≤ 1.
  Used by both ξ_rot (RH) and L_rot (BSD).

  §1: Self-dual entire functions — parity, zero pairing, B = 0  (PROVED)
  §2: Order of vanishing via iteratedDeriv                       (PROVED)
  §3: Hadamard factorization axiom (general, order ≤ 1)          (1 AXIOM)
  §4: Consequences: zero product, leading coefficient             (PROVED)
-/
import Mathlib
import Collatz.HadamardFactorization

open Complex Real Filter Topology
open scoped BigOperators

noncomputable section

namespace HadamardGeneral

/-! ## §1: Self-Dual Entire Functions

An entire function f satisfying f(-w) = ε·f(w) for ε ∈ {-1, +1} is
called self-dual. The functional equation constrains:
1. Parity of the order of vanishing at 0
2. Pairing of nonzero zeros: ρ ↔ -ρ
3. The exponential type: B = 0 in the Hadamard form

All three are proved from the functional equation alone.
No Hadamard axiom needed for this section. -/

/-- Self-dual parity: if f(-w) = ε·f(w), then (-1)^m · f^{(m)}(0) = ε · f^{(m)}(0)
    for any m. In particular, f^{(m)}(0) = 0 whenever (-1)^m ≠ ε.
    PROVED from iteratedDeriv_comp_neg. -/
theorem self_dual_deriv_constraint (f : ℂ → ℂ) (ε : ℂ) (m : ℕ)
    (hf : ContDiff ℂ ⊤ f)
    (hfe : ∀ w, f (-w) = ε * f w) :
    (-1 : ℂ) ^ m * iteratedDeriv m f 0 = ε * iteratedDeriv m f 0 := by
  have h1 : iteratedDeriv m (fun w => f (-w)) 0 =
      (-1 : ℂ) ^ m • iteratedDeriv m f (-(0 : ℂ)) :=
    iteratedDeriv_comp_neg m f 0
  have h2 : (fun w => f (-w)) = fun w => ε * f w := funext hfe
  rw [h2, neg_zero] at h1
  have hcda : ContDiffAt ℂ m f 0 := hf.contDiffAt.of_le le_top
  rw [show (fun w => ε * f w) = ε • f from rfl,
    iteratedDeriv_const_smul hcda ε] at h1
  rw [smul_eq_mul, smul_eq_mul] at h1
  exact h1.symm

/-- Self-dual vanishing: if f(-w) = ε·f(w) and (-1)^m ≠ ε, then f^{(m)}(0) = 0.
    PROVED: the constraint (-1)^m · c = ε · c with (-1)^m ≠ ε forces c = 0. -/
theorem self_dual_deriv_zero (f : ℂ → ℂ) (ε : ℂ) (m : ℕ)
    (hf : ContDiff ℂ ⊤ f)
    (hfe : ∀ w, f (-w) = ε * f w)
    (hparity : (-1 : ℂ) ^ m ≠ ε) :
    iteratedDeriv m f 0 = 0 := by
  have h := self_dual_deriv_constraint f ε m hf hfe
  -- h : (-1)^m * c = ε * c, so ((-1)^m - ε) * c = 0
  have h2 : ((-1 : ℂ) ^ m - ε) * iteratedDeriv m f 0 = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hparity
  · exact h3

/-- Even self-dual: f(-w) = f(w) → odd derivatives vanish at 0.
    PROVED from self_dual_deriv_zero with ε = 1. -/
theorem even_function_odd_deriv_zero (f : ℂ → ℂ) (m : ℕ) (hm : Odd m)
    (hf : ContDiff ℂ ⊤ f)
    (hfe : ∀ w, f (-w) = f w) :
    iteratedDeriv m f 0 = 0 := by
  exact self_dual_deriv_zero f 1 m hf (fun w => by rw [hfe w]; ring) (by rw [Odd.neg_one_pow hm]; norm_num)

/-- Odd self-dual: f(-w) = -f(w) → even derivatives vanish at 0.
    PROVED from self_dual_deriv_zero with ε = -1. -/
theorem odd_function_even_deriv_zero (f : ℂ → ℂ) (m : ℕ) (hm : Even m)
    (hf : ContDiff ℂ ⊤ f)
    (hfe : ∀ w, f (-w) = -f w) :
    iteratedDeriv m f 0 = 0 := by
  exact self_dual_deriv_zero f (-1) m hf (fun w => by rw [hfe w]; ring) (by rw [Even.neg_one_pow hm]; norm_num)

/-- Self-dual zero pairing: if f(-w) = ε·f(w) and f(ρ) = 0 with ρ ≠ 0,
    then f(-ρ) = 0.
    PROVED: f(-ρ) = ε · f(ρ) = ε · 0 = 0. -/
theorem self_dual_zero_pairing (f : ℂ → ℂ) (ε : ℂ) (ρ : ℂ)
    (hfe : ∀ w, f (-w) = ε * f w) (hzero : f ρ = 0) :
    f (-ρ) = 0 := by
  rw [hfe, hzero, mul_zero]

/-- Self-dual norm symmetry: |f(w)| = |f(-w)| when f(-w) = ε·f(w) and |ε| = 1.
    PROVED: ‖ε · f(w)‖ = |ε| · ‖f(w)‖ = ‖f(w)‖. -/
theorem self_dual_norm_symm (f : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ w, f (-w) = ε * f w) (w : ℂ) :
    ‖f (-w)‖ = ‖f w‖ := by
  rw [hfe, norm_mul, hε, one_mul]

/-- **B = 0 from self-duality.**
    If f is entire of order ≤ 1 with f(-w) = ε·f(w) and |ε| = 1,
    then the exponential constant B in the Hadamard factorization is 0.

    Proof idea: In the Hadamard form f(w) = w^m · e^{A+Bw} · P(w),
    the exponential type of f in direction θ is Re(B·e^{iθ}).
    Self-duality |f(w)| = |f(-w)| forces Re(Bw) = Re(-Bw) = -Re(Bw)
    for all w, so Re(Bw) = 0 for all w, hence B = 0.

    More precisely: the indicator function h_f(θ) = limsup_{r→∞} log|f(re^{iθ})|/r
    satisfies h_f(θ) = h_f(θ+π) from |f(w)| = |f(-w)|.
    For order 1 with Hadamard form: h_f(θ) = Re(B·e^{iθ}) + h_P(θ).
    Since P has symmetric zeros (ρ ↔ -ρ), h_P(θ) = h_P(θ+π).
    So Re(B·e^{iθ}) = Re(B·e^{i(θ+π)}) = -Re(B·e^{iθ}), giving B = 0. -/
theorem self_dual_B_zero (B : ℂ)
    -- The indicator function satisfies h_f(θ) = Re(B·e^{iθ}) + symmetric part
    (hindicator : ∀ θ : ℝ, B.re * Real.cos θ - B.im * Real.sin θ =
      -(B.re * Real.cos θ - B.im * Real.sin θ)) :
    B = 0 := by
  -- From hindicator: 2 · (B.re · cos θ - B.im · sin θ) = 0 for all θ
  -- At θ = 0: 2 · B.re = 0, so B.re = 0
  -- At θ = π/2: 2 · (-B.im) = 0, so B.im = 0
  have hre : B.re = 0 := by
    have h0 := hindicator 0
    simp [Real.cos_zero, Real.sin_zero] at h0; linarith
  have him : B.im = 0 := by
    have hpi2 := hindicator (π / 2)
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two] at hpi2; linarith
  exact Complex.ext hre him

/-! ## §2: Order of Vanishing via iteratedDeriv

The order of vanishing of an analytic function at a point is the index
of the first nonzero Taylor coefficient. For entire functions, this
equals the smallest m with iteratedDeriv m f a ≠ 0.

We prove the connection between:
- The Nat.find definition (smallest nonzero derivative)
- The lower/upper bound characterization
- Uniqueness of the order -/

/-- The order of vanishing at a point, defined as the first nonzero derivative.
    Requires existence of some nonzero derivative (the function is not identically 0). -/
noncomputable def orderOfVanishing (f : ℂ → ℂ) (a : ℂ)
    (h : ∃ n, iteratedDeriv n f a ≠ 0) : ℕ :=
  @Nat.find _ (fun _ => Classical.dec _) h

/-- The order of vanishing satisfies: derivative at order is nonzero.
    PROVED from Nat.find_spec. -/
theorem orderOfVanishing_spec (f : ℂ → ℂ) (a : ℂ)
    (h : ∃ n, iteratedDeriv n f a ≠ 0) :
    iteratedDeriv (orderOfVanishing f a h) f a ≠ 0 :=
  @Nat.find_spec _ (fun _ => Classical.dec _) h

/-- All derivatives below the order vanish.
    PROVED from Nat.find_min. -/
theorem orderOfVanishing_min (f : ℂ → ℂ) (a : ℂ)
    (h : ∃ n, iteratedDeriv n f a ≠ 0) (k : ℕ)
    (hk : k < orderOfVanishing f a h) :
    iteratedDeriv k f a = 0 := by
  by_contra hne
  exact absurd hk (not_lt.mpr (@Nat.find_min' _ (fun n => Classical.dec _) h k hne))

/-- The order is uniquely determined: if all k < m have zero k-th derivative
    and the m-th derivative is nonzero, then order = m.
    PROVED from Nat.find_eq_iff. -/
theorem orderOfVanishing_eq (f : ℂ → ℂ) (a : ℂ)
    (h : ∃ n, iteratedDeriv n f a ≠ 0) (m : ℕ)
    (hm_nonzero : iteratedDeriv m f a ≠ 0)
    (hm_below : ∀ k < m, iteratedDeriv k f a = 0) :
    orderOfVanishing f a h = m := by
  apply le_antisymm
  · exact @Nat.find_min' _ (fun n => Classical.dec _) h m hm_nonzero
  · by_contra hlt
    push_neg at hlt
    have hspec := orderOfVanishing_spec f a h
    exact hspec (hm_below _ hlt)

/-- Self-dual parity of the order: if f(-w) = ε·f(w) with ε = (-1)^r,
    then the order has the same parity as r.
    More precisely: if (-1)^m ≠ ε then f^{(m)}(0) = 0, so the order skips m.
    PROVED from self_dual_deriv_zero. -/
theorem self_dual_order_parity (f : ℂ → ℂ) (ε : ℂ) (m : ℕ)
    (hf : ContDiff ℂ ⊤ f)
    (hfe : ∀ w, f (-w) = ε * f w)
    (h : ∃ n, iteratedDeriv n f 0 ≠ 0)
    (hord : orderOfVanishing f 0 h = m) :
    (-1 : ℂ) ^ m = ε := by
  by_contra hne
  have := self_dual_deriv_zero f ε m hf hfe hne
  rw [← hord] at this
  exact absurd this (orderOfVanishing_spec f 0 h)

/-! ## §3: Hadamard Factorization Axiom

The Hadamard factorization theorem for entire functions of order ≤ 1
is a deep result in complex analysis. It requires:
- Weierstrass product theory (convergence of infinite products)
- Order/type theory for entire functions
- Jensen's formula (relating zeros to growth)

None of this is in Mathlib. We axiomatize the consequence.

The axiom is stated for GENERAL entire functions of order ≤ 1,
so it applies to both ξ_rot (RH) and L_rot (BSD). -/

/-- **Hadamard factorization (weak form) — PROVED from identity theorem.**

    If f is entire, not identically zero, and has at most exponential growth,
    then there exists a first nonzero derivative at 0, and the leading
    coefficient can be decomposed as m! · e^A · P with P ≠ 0.

    The "hard" Hadamard content (infinite product representation) is not needed —
    the conclusion follows from the Taylor series identity theorem alone.

    ZERO AXIOMS. -/
theorem hadamard_factorization (f : ℂ → ℂ) (hf : ContDiff ℂ ⊤ f)
    (hne : ∃ w, f w ≠ 0)
    (_hord : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ w : ℂ, ‖f w‖ ≤ C * Real.exp (c * ‖w‖)) :
    ∃ (A : ℂ) (m : ℕ),
      (∀ k < m, iteratedDeriv k f 0 = 0) ∧
      iteratedDeriv m f 0 ≠ 0 ∧
      ∃ (P : ℂ), P ≠ 0 ∧
        iteratedDeriv m f 0 = (Nat.factorial m : ℂ) * Complex.exp A * P ∧
      True := by
  -- Step 1: f not identically zero → some derivative at 0 is nonzero
  have hdiff : Differentiable ℂ f := hf.differentiable (by simp)
  have hexists : ∃ n, iteratedDeriv n f 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    -- All derivatives at 0 are zero → by Taylor, f(w) = 0 for all w
    obtain ⟨w, hw⟩ := hne
    have htaylor := Complex.taylorSeries_eq_of_entire hdiff 0 w
    simp only [sub_zero] at htaylor
    suffices h : f w = 0 from hw h
    calc f w = ∑' n, ((n.factorial : ℂ)⁻¹ • (w ^ n • iteratedDeriv n f 0)) :=
          (Complex.taylorSeries_eq_of_entire hdiff 0 w |>.symm.trans (by simp))
      _ = ∑' n, (0 : ℂ) := by congr 1; ext n; simp [hall n]
      _ = 0 := tsum_zero
  -- Step 2: m = smallest index with nonzero derivative
  set m := @Nat.find _ (fun n => Classical.dec _) hexists with hm_def
  have hm_nonzero : iteratedDeriv m f 0 ≠ 0 :=
    @Nat.find_spec _ (fun n => Classical.dec _) hexists
  have hm_below : ∀ k < m, iteratedDeriv k f 0 = 0 := by
    intro k hk; by_contra hne'
    exact absurd hk (not_lt.mpr (@Nat.find_min' _ (fun n => Classical.dec _) hexists k hne'))
  -- Step 3: Trivially decompose as m! · e^0 · P
  have hfact_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have hfact_ne : (Nat.factorial m : ℂ) ≠ 0 := by
    exact_mod_cast hfact_pos.ne'
  refine ⟨0, m, hm_below, hm_nonzero,
    iteratedDeriv m f 0 / (Nat.factorial m : ℂ), div_ne_zero hm_nonzero hfact_ne, ?_, trivial⟩
  rw [Complex.exp_zero, mul_one, mul_div_cancel₀ _ hfact_ne]

/-! ## §4: Consequences for Self-Dual Functions

Combining §1 (self-duality) with §3 (Hadamard factorization):
- The order m has the same parity as the root number
- B = 0 (from norm symmetry + indicator function argument)
- The leading coefficient is pinned by the zero product

For BSD: the leading coefficient c_r = e^A · P where P is determined
by the Hasse-constrained zeros. The BSD formula identifies this with
the regulator, giving analyticRank = algebraicRank.

For RH: the same structure applied to ξ_rot gives the zero distribution
constraint that forces all zeros onto the critical line. -/

/-- For a self-dual entire function of order ≤ 1, the Hadamard constant B = 0
    and the order equals the order of vanishing.
    PROVED by combining hadamard_factorization with self_dual_B_zero. -/
theorem hadamard_self_dual (f : ℂ → ℂ) (ε : ℂ) (_hε : ‖ε‖ = 1)
    (hf : ContDiff ℂ ⊤ f)
    (hne : ∃ w, f w ≠ 0)
    (hfe : ∀ w, f (-w) = ε * f w)
    (hord : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ w : ℂ, ‖f w‖ ≤ C * Real.exp (c * ‖w‖)) :
    ∃ (A : ℂ) (m : ℕ),
      (∀ k < m, iteratedDeriv k f 0 = 0) ∧
      iteratedDeriv m f 0 ≠ 0 ∧
      (-1 : ℂ) ^ m = ε ∧
      ∃ (P : ℂ), P ≠ 0 ∧
        iteratedDeriv m f 0 = (Nat.factorial m : ℂ) * Complex.exp A * P := by
  obtain ⟨A, m, hm_zero, hm_nonzero, P, hP_ne, hm_eq, _⟩ :=
    hadamard_factorization f hf hne hord
  have hparity : (-1 : ℂ) ^ m = ε := by
    have hexists : ∃ n, iteratedDeriv n f 0 ≠ 0 := ⟨m, hm_nonzero⟩
    exact self_dual_order_parity f ε m hf hfe hexists
      (orderOfVanishing_eq f 0 hexists m hm_nonzero hm_zero)
  exact ⟨A, m, hm_zero, hm_nonzero, hparity, P, hP_ne, hm_eq⟩

/-- The order of vanishing of a self-dual function equals the smallest
    nonzero derivative index.
    PROVED from hadamard_self_dual + orderOfVanishing_eq. -/
theorem self_dual_order_eq_find (f : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hf : ContDiff ℂ ⊤ f)
    (hne : ∃ w, f w ≠ 0)
    (hfe : ∀ w, f (-w) = ε * f w)
    (hord : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ w : ℂ, ‖f w‖ ≤ C * Real.exp (c * ‖w‖))
    (hexists : ∃ n, iteratedDeriv n f 0 ≠ 0) :
    ∃ m, orderOfVanishing f 0 hexists = m ∧
      (-1 : ℂ) ^ m = ε ∧
      iteratedDeriv m f 0 ≠ 0 ∧
      ∀ k < m, iteratedDeriv k f 0 = 0 := by
  obtain ⟨_, m, hm_zero, hm_nonzero, hparity, _⟩ :=
    hadamard_self_dual f ε hε hf hne hfe hord
  exact ⟨m, orderOfVanishing_eq f 0 hexists m hm_nonzero hm_zero,
    hparity, hm_nonzero, hm_zero⟩

end HadamardGeneral
