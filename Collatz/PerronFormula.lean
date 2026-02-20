/-
  PerronFormula.lean — Perron Explicit Formula from Primitive Axioms
  =================================================================

  Decomposes the Perron explicit formula into two independent axioms:

  AXIOM 1 — perron_contour_shift (Contour Integration)
    ψ(x) = x − perronZeroSum(x,T) + trunc_err + error
    with |trunc_err| ≤ C·x/T·(log x)², |error| ≤ C·log x.
    Content: Perron inversion + residue theorem + contour shifting.
    Requires: vertical line integrals, rectangular Cauchy-Goursat.
    NOT in Mathlib.

  AXIOM 2 — perron_zero_sum_bound (Zero Density)
    |perronZeroSum(x,T)| ≤ C·x^β·(log T)² for valid β.
    Content: Triangle inequality + Abel summation over zeros.
    Ingredients in Mathlib: rpow monotonicity, Finset.sum bounds.
    Requires: Abel summation from N(T) ≤ C·T·log T (our zero_counting_bound)
              to Σ 1/|ρ| ≤ C·(log T)².
    CLOSE to provable from existing axioms + Mathlib.

  THEOREM — perron_explicit_formula (from Axiom 1 + Axiom 2)
  THEOREM — rh_explicit_formula (from perron_explicit_formula + RH)
  THEOREM — explicit_formula_unconditional (from perron_explicit_formula)

  The separation matters: Axiom 1 is the deep contour result (irreducible
  without Mathlib infrastructure for vertical integrals). Axiom 2 is the
  counting/summation result (provable once Abel summation over zeros is
  formalized, using our zero_counting_bound from HadamardFactorization).
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators Chebyshev
open Real

namespace PerronFormula

/-! ## Axiom 1: The Contour Identity

The Perron integral (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ(s)) · x^s/s ds,
shifted from Re(s) = c > 1 past the pole at s = 1 and the nontrivial
zeros of ζ, gives the explicit formula:

  ψ(x) = x − Σ_{|γ|≤T} x^ρ/ρ + O(x/T·(log x)²) + O(log x)

We Skolemize the zero sum as a function perronZeroSum(x, T) to enable
independent axiomatization of its bound.

Proof would require: vertical line integrals, rectangular Cauchy-Goursat
for meromorphic functions, residue extraction at s = 1 and s = ρ.
Mathlib has the pieces (rectangle integrals, Cauchy integral formula)
but not the assembly. -/

/-- The contribution of nontrivial zeros to the explicit formula:
    perronZeroSum(x, T) = Σ_{ρ : |Im(ρ)| ≤ T, ζ(ρ) = 0} x^ρ/ρ.
    Skolemized from the contour shift identity. -/
axiom perronZeroSum : ℝ → ℝ → ℝ

/-- **Perron contour shift identity**: shifting the Perron integral
    past the zeros of ζ gives ψ(x) = x − zero_sum + controlled errors.

    The truncation error O(x/T·(log x)²) comes from cutting the
    vertical contour at height T and bounding the horizontal segments
    using |ζ'/ζ(σ ± iT)| ≤ C·log²T (Titchmarsh §3.6).

    The small error O(log x) absorbs trivial zeros at s = −2n and
    the boundary contribution from the left vertical segment.

    Reference: Davenport, "Multiplicative Number Theory", Ch. 17.
    Not in Mathlib: requires vertical contour integration infrastructure. -/
axiom perron_contour_shift :
    ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ∃ (trunc_err error : ℝ),
        |trunc_err| ≤ C * x / T * (Real.log x) ^ 2 ∧
        |error| ≤ C * Real.log x ∧
        ψ x = x - perronZeroSum x T + trunc_err + error

/-! ## Axiom 2: The Zero Sum Bound

Since perronZeroSum(x, T) = Σ_{|γ|≤T} x^ρ/ρ, the triangle inequality gives:
  |perronZeroSum(x, T)| ≤ Σ |x^ρ/ρ| = Σ x^{Re(ρ)}/|ρ|

For any β ≥ max{Re(ρ) : |Im(ρ)| ≤ T}, monotonicity of rpow gives:
  x^{Re(ρ)} ≤ x^β  (since x ≥ 2 > 1)

So |perronZeroSum(x, T)| ≤ x^β · Σ_{|γ|≤T} 1/|ρ|.

The key density bound: Σ_{|γ|≤T} 1/|ρ| ≤ C·(log T)².
This follows from N(T) ≤ C·T·log T (our zero_counting_bound) by
Abel summation (partial summation):
  Σ_{|γ|≤T} 1/|γ| ≈ N(T)/T + ∫₁ᵀ N(t)/t² dt
                    ≈ C·log T + C·∫₁ᵀ (log t)/t dt
                    = C·log T + C·(log T)²/2
                    ≤ C'·(log T)²

This axiom is CLOSE to provable from zero_counting_bound + Mathlib's
summation/integration tools. The gap is formalizing Abel summation
over the zeros of ζ ordered by |Im|. -/

/-- **Zero sum β-bound**: perronZeroSum is bounded by x^β · (log T)²
    whenever β uniformly bounds Re(ρ) for zeros with |Im(ρ)| ≤ T.

    Content: triangle inequality + rpow monotonicity + Abel summation.
    Provable from: zero_counting_bound + Abel summation formalization. -/
axiom perron_zero_sum_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
          |s.im| ≤ T → s.re ≤ β) →
        |perronZeroSum x T| ≤ C * x ^ β * (Real.log T) ^ 2

/-! ## perron_explicit_formula: PROVED from Axiom 1 + Axiom 2

The old axiom is now a theorem: combine the contour identity (which
gives the decomposition ψ = x − zero_sum + errors) with the zero
sum bound (which gives |zero_sum| ≤ C·x^β·(log T)²). -/

/-- **Perron explicit formula** — PROVED from perron_contour_shift + perron_zero_sum_bound.
    The β parameter controls the zero sum bound while T controls the truncation. -/
theorem perron_explicit_formula :
    ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
          |s.im| ≤ T → s.re ≤ β) →
        ∃ (zero_sum trunc_err error : ℝ),
          |zero_sum| ≤ C * x ^ β * (Real.log T) ^ 2 ∧
          |trunc_err| ≤ C * x / T * (Real.log x) ^ 2 ∧
          |error| ≤ C * Real.log x ∧
          ψ x = x - zero_sum + trunc_err + error := by
  obtain ⟨C₁, hC₁, h_contour⟩ := perron_contour_shift
  obtain ⟨C₂, hC₂, h_bound⟩ := perron_zero_sum_bound
  set C := max C₁ C₂ with hC_def
  have hC : 0 < C := lt_max_of_lt_left hC₁
  have hC₁_le : C₁ ≤ C := le_max_left _ _
  have hC₂_le : C₂ ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro x hx T hT β hβ hβ1 hzeros
  obtain ⟨te, err, hte, herr, heq⟩ := h_contour x hx T hT
  have hzb := h_bound x hx T hT β hβ hβ1 hzeros
  refine ⟨perronZeroSum x T, te, err, ?_, ?_, ?_, heq⟩
  · -- |perronZeroSum x T| ≤ C · x^β · (log T)²
    calc |perronZeroSum x T|
        ≤ C₂ * x ^ β * (Real.log T) ^ 2 := hzb
      _ ≤ C * x ^ β * (Real.log T) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hC₂_le
              (rpow_nonneg (by linarith : (0 : ℝ) ≤ x) β)
          · exact sq_nonneg _
  · -- |trunc_err| ≤ C · x/T · (log x)²
    calc |te| ≤ C₁ * x / T * (Real.log x) ^ 2 := hte
      _ ≤ C * x / T * (Real.log x) ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right hC₁_le (by linarith)
            · linarith
          · exact sq_nonneg _
  · -- |error| ≤ C · log x
    calc |err| ≤ C₁ * Real.log x := herr
      _ ≤ C * Real.log x := by
          apply mul_le_mul_of_nonneg_right hC₁_le
          exact le_of_lt (Real.log_pos (by linarith : (1 : ℝ) < x))

/-! ## RH → Explicit Formula

Under RH, every nontrivial zero has Re(ρ) = 1/2, so we take β = 1/2.
With T = x, the truncation error is O((log x)²), absorbed into the zero sum. -/

/-- Under RH, nontrivial zeros in the critical strip satisfy Re(s) ≤ 1/2. -/
private theorem rh_zeros_bounded (hRH : RiemannHypothesis)
    (s : ℂ) (hs : riemannZeta s = 0) (hpos : 0 < s.re) (hlt1 : s.re < 1) :
    s.re ≤ 1 / 2 := by
  have h_not_trivial : ¬∃ n : ℕ, s = -2 * (↑n + 1) := by
    rintro ⟨n, hn⟩
    have key : (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [hn, key, Complex.ofReal_re] at hpos
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h_ne_one : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hlt1; linarith
  exact le_of_eq (hRH s hs h_not_trivial h_ne_one)

/-- **RH-conditional explicit formula**: the zero sum is O(√x · (log x)²).
    PROVED from perron_explicit_formula + RiemannHypothesis. -/
theorem rh_explicit_formula (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ∃ (zero_sum : ℝ),
        |zero_sum| ≤ C * x.sqrt * (Real.log x) ^ 2 ∧
        ∃ error : ℝ, |error| ≤ C * Real.log x ∧
          ψ x = x - zero_sum + error := by
  obtain ⟨C, hC, hf⟩ := perron_explicit_formula
  refine ⟨2 * C, by linarith, ?_⟩
  intro x hx
  have hzeros : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ x → s.re ≤ 1 / 2 :=
    fun s hs hpos hlt1 _ => rh_zeros_bounded hRH s hs hpos hlt1
  obtain ⟨zs, te, err, hzs, hte, herr, heq⟩ :=
    hf x hx x hx (1 / 2) (by norm_num) (by norm_num) hzeros
  have hsqrt : x ^ (1 / 2 : ℝ) = x.sqrt := (Real.sqrt_eq_rpow x).symm
  rw [hsqrt] at hzs
  have hxx : C * x / x * (Real.log x) ^ 2 = C * (Real.log x) ^ 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt (show (0 : ℝ) < x by linarith))]; ring
  rw [hxx] at hte
  have hsqrt_ge : 1 ≤ x.sqrt := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  refine ⟨zs - te, ?_, err, ?_, ?_⟩
  · have h_tri : |zs - te| ≤ |zs| + |te| := by
      rw [abs_le]; constructor <;>
        linarith [le_abs_self zs, neg_abs_le zs, le_abs_self te, neg_abs_le te]
    calc |zs - te| ≤ |zs| + |te| := h_tri
      _ ≤ C * x.sqrt * (Real.log x) ^ 2 + C * (Real.log x) ^ 2 := by linarith
      _ ≤ C * x.sqrt * (Real.log x) ^ 2 + C * x.sqrt * (Real.log x) ^ 2 := by
          have : C * (Real.log x) ^ 2 ≤ C * x.sqrt * (Real.log x) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (le_mul_of_one_le_right (le_of_lt hC) hsqrt_ge) (sq_nonneg _)
          linarith
      _ = 2 * C * x.sqrt * (Real.log x) ^ 2 := by ring
  · linarith [mul_pos hC hlog_pos]
  · linarith

/-- Unconditional explicit formula: zero sum is O(x · (log x)²).
    PROVED from perron_explicit_formula with β = 1, T = x. -/
theorem explicit_formula_unconditional :
    ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x →
      ∃ (zero_sum : ℝ),
        |zero_sum| ≤ C * x * (Real.log x) ^ 2 ∧
        ∃ error : ℝ, |error| ≤ C * Real.log x ∧
          ψ x = x - zero_sum + error := by
  obtain ⟨C, hC, hf⟩ := perron_explicit_formula
  refine ⟨2 * C, by linarith, ?_⟩
  intro x hx
  have hzeros : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ x → s.re ≤ 1 := fun _ _ _ hlt1 _ => le_of_lt hlt1
  obtain ⟨zs, te, err, hzs, hte, herr, heq⟩ :=
    hf x hx x hx 1 (by norm_num) le_rfl hzeros
  have hx1 : x ^ (1 : ℝ) = x := Real.rpow_one x
  rw [hx1] at hzs
  have hxx : C * x / x * (Real.log x) ^ 2 = C * (Real.log x) ^ 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt (show (0 : ℝ) < x by linarith))]; ring
  rw [hxx] at hte
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  refine ⟨zs - te, ?_, err, ?_, ?_⟩
  · have h_tri : |zs - te| ≤ |zs| + |te| := by
      rw [abs_le]; constructor <;>
        linarith [le_abs_self zs, neg_abs_le zs, le_abs_self te, neg_abs_le te]
    calc |zs - te| ≤ |zs| + |te| := h_tri
      _ ≤ C * x * (Real.log x) ^ 2 + C * (Real.log x) ^ 2 := by linarith
      _ ≤ C * x * (Real.log x) ^ 2 + C * x * (Real.log x) ^ 2 := by
          have : C * (Real.log x) ^ 2 ≤ C * x * (Real.log x) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (le_mul_of_one_le_right (le_of_lt hC) (by linarith)) (sq_nonneg _)
          linarith
      _ = 2 * C * x * (Real.log x) ^ 2 := by ring
  · linarith [mul_pos hC hlog_pos]
  · linarith

end PerronFormula

-- Axiom audit
#print axioms PerronFormula.perron_explicit_formula
#print axioms PerronFormula.rh_explicit_formula
#print axioms PerronFormula.explicit_formula_unconditional
