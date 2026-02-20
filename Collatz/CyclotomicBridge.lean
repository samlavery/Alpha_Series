/-
  CyclotomicBridge.lean — Cyclotomic ring infrastructure for Collatz
  ====================================================================

  The cyclotomic ring ℤ[ζ_d] captures the "true" orbit position: while the
  integer lattice tracks W = Σ 3^{m-1-j} · 2^{Sⱼ} in ℤ, the cyclotomic
  lattice tracks the balance sum B = Σ FW_r · ζ^r in ℤ[ζ_d].

  At the trivial cycle (1→4→2→1), both lattices agree exactly: the gap is 0.
  For nontrivial profiles, each step introduces a residue between the integer
  position and the cyclotomic position. The gap grows until the two worlds
  become inconsistent — the integer representation would need to be in two
  places at once. Once the gap crosses the threshold, D ∤ W is forced.

  Key chain:
    D | W in ℤ  ⟹  Φ_d(4,3) | waveSumPoly(4) in ℤ
                ⟹  (4-3ζ) | B in O_K = ℤ[ζ_d]
                ⟹  (4^d-3^d) | evalSum43'(FW) in ℤ  [evaluation transfer]
                ⟹  4-adic cascade forces all FW_r equal  [|g_r| < 4]
                ⟹  contradiction with nontriviality

  Ported from finallean/Collatz/CyclotomicAlgebra.lean.
-/
import Collatz.Defs
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic

open Collatz
open scoped BigOperators

namespace Collatz.CyclotomicBridge

/-! ## Section 1: Bivariate cyclotomic polynomial -/

/-- Φ_d(x,y) = Σ_{i<d} x^{d-1-i} · y^i = (x^d - y^d)/(x - y) -/
def cyclotomicBivar (q : ℕ) (x y : ℤ) : ℤ :=
  ∑ i ∈ Finset.range q, x^(q - 1 - i) * y^i

/-- (x - y) · Φ_q(x,y) = x^q - y^q -/
lemma cyclotomicBivar_mul_sub (q : ℕ) (hq : 0 < q) (x y : ℤ) :
    (x - y) * cyclotomicBivar q x y = x^q - y^q := by
  unfold cyclotomicBivar
  induction q with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [show n + 1 - 1 - n = 0 from by omega, pow_zero, one_mul, mul_add]
    by_cases hn : n = 0
    · subst hn; simp
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h_sum_eq : ∑ i ∈ Finset.range n, x^(n + 1 - 1 - i) * y^i =
          ∑ i ∈ Finset.range n, x^(n - i) * y^i := by
        apply Finset.sum_congr rfl; intro i hi
        congr 1
      rw [h_sum_eq]
      have h_factor_sum : ∑ i ∈ Finset.range n, x^(n - i) * y^i =
          x * ∑ i ∈ Finset.range n, x^(n - 1 - i) * y^i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have : n - i = (n - 1 - i) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [h_factor_sum]
      -- Goal: (x - y) * (x * Σ...) + (x - y) * y^n = x^(n+1) - y^(n+1)
      have h_assoc : (x - y) * (x * ∑ i ∈ Finset.range n, x ^ (n - 1 - i) * y ^ i) =
          x * ((x - y) * ∑ i ∈ Finset.range n, x ^ (n - 1 - i) * y ^ i) := by ring
      rw [h_assoc, ih hn_pos]
      ring

/-- Φ_d(4,3) divides 4^m - 3^m when d | m. -/
lemma cyclotomicBivar_dvd_pow_sub_general {d m : ℕ} (hd_pos : 0 < d) (hd_dvd : d ∣ m) :
    (cyclotomicBivar d 4 3 : ℤ) ∣ (4^m - 3^m : ℤ) := by
  obtain ⟨k, hk⟩ := hd_dvd
  rw [hk, pow_mul, pow_mul]
  have h_factor : ((4 : ℤ)^d - 3^d) ∣ (((4 : ℤ)^d)^k - (3^d)^k) := by
    have : ∀ (a b : ℤ) (k : ℕ), (a - b) ∣ (a^k - b^k) := by
      intro a b k; induction k with
      | zero => simp
      | succ n ih' =>
        have : a^(n+1) - b^(n+1) = a * (a^n - b^n) + (a - b) * b^n := by ring
        rw [this]; exact dvd_add (dvd_mul_of_dvd_right ih' a) (dvd_mul_right _ _)
    exact this _ _ k
  have h_cyc : (4 : ℤ)^d - 3^d = (4 - 3) * cyclotomicBivar d 4 3 := by
    rw [cyclotomicBivar_mul_sub d hd_pos 4 3]
  rw [h_cyc, show (4 : ℤ) - 3 = 1 from by norm_num, one_mul] at h_factor
  exact h_factor

/-- General form: `Φ_d(x,y)` divides `x^m - y^m` whenever `d ∣ m`. -/
lemma cyclotomicBivar_dvd_pow_sub_general_xy {d m : ℕ} (x y : ℤ)
    (hd_pos : 0 < d) (hd_dvd : d ∣ m) :
    (cyclotomicBivar d x y : ℤ) ∣ (x^m - y^m : ℤ) := by
  obtain ⟨k, hk⟩ := hd_dvd
  rw [hk, pow_mul, pow_mul]
  have h_factor : ((x : ℤ)^d - y^d) ∣ (((x : ℤ)^d)^k - (y^d)^k) := by
    have : ∀ (a b : ℤ) (k : ℕ), (a - b) ∣ (a^k - b^k) := by
      intro a b k
      induction k with
      | zero => simp
      | succ n ih' =>
        have hstep : a^(n+1) - b^(n+1) = a * (a^n - b^n) + (a - b) * b^n := by ring
        rw [hstep]
        exact dvd_add (dvd_mul_of_dvd_right ih' a) (dvd_mul_right _ _)
    exact this _ _ k
  have h_cyc : (x : ℤ)^d - y^d = (x - y) * cyclotomicBivar d x y := by
    rw [cyclotomicBivar_mul_sub d hd_pos x y]
  have h_cyc_dvd : (cyclotomicBivar d x y : ℤ) ∣ ((x : ℤ)^d - y^d) := by
    refine ⟨x - y, ?_⟩
    rw [h_cyc]
    ring
  exact dvd_trans h_cyc_dvd h_factor

/-- Φ_d(4,3) > 0 for d ≥ 1. -/
lemma cyclotomicBivar_pos (q : ℕ) (hq : 0 < q) : cyclotomicBivar q 4 3 > 0 := by
  unfold cyclotomicBivar
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (pow_pos (by norm_num : (4 : ℤ) > 0) _) (pow_pos (by norm_num : (3 : ℤ) > 0) _)
  · rw [Finset.nonempty_range_iff]; omega

/-! ## Section 2: Cyclotomic field and ring of integers -/

variable (d : ℕ)

/-- CyclotomicField d ℚ. -/
abbrev CyclotomicFieldD := CyclotomicField d ℚ

/-- Primitive d-th root ζ_d. -/
noncomputable def zetaD [NeZero d] : CyclotomicFieldD d :=
  IsCyclotomicExtension.zeta d ℚ (CyclotomicFieldD d)

/-- zetaD is a primitive d-th root. -/
lemma zetaD_is_primitive [NeZero d] (hd_pos : 0 < d) :
    IsPrimitiveRoot (zetaD d) d :=
  IsCyclotomicExtension.zeta_spec d ℚ (CyclotomicFieldD d)

/-- Powers fold mod d: ζ^n = ζ^(n % d). -/
lemma zetaD_pow_mod [NeZero d] (hd_pos : 0 < d) (n : ℕ) :
    (zetaD d)^n = (zetaD d)^(n % d) := by
  conv_lhs => rw [← Nat.div_add_mod n d]
  rw [pow_add, pow_mul, (zetaD_is_primitive d hd_pos).pow_eq_one, one_pow, one_mul]

/-- (4 - 3ζ_d) in the cyclotomic field. -/
noncomputable def fourSubThreeZetaD [NeZero d] : CyclotomicFieldD d :=
  (4 : CyclotomicFieldD d) - 3 * zetaD d

/-- Balance sum B = Σ FW_r · ζ^r. -/
noncomputable def balanceSumD [NeZero d] (FW : Fin d → ℕ) : CyclotomicFieldD d :=
  ∑ r : Fin d, (FW r : CyclotomicFieldD d) * (zetaD d) ^ (r : ℕ)

/-- The ring of integers O_K = ℤ[ζ_d]. -/
abbrev OKD [NeZero d] : Subalgebra ℤ (CyclotomicFieldD d) :=
  Algebra.adjoin ℤ ({zetaD d} : Set (CyclotomicFieldD d))

/-- zetaD ∈ OKD. -/
lemma zetaD_mem_OKD [NeZero d] : zetaD d ∈ OKD d := Algebra.subset_adjoin (Set.mem_singleton _)

/-- 3 ∈ OKD. -/
lemma three_mem_OKD [NeZero d] : (3 : CyclotomicFieldD d) ∈ OKD d := Subalgebra.natCast_mem _ 3

/-- balanceSumD ∈ OKD. -/
lemma balanceSumD_mem_OKD [NeZero d] (FW : Fin d → ℕ) : balanceSumD d FW ∈ OKD d := by
  unfold balanceSumD
  apply Subalgebra.sum_mem; intro r _
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (FW r : ℤ))
    (Subalgebra.pow_mem _ (zetaD_mem_OKD d) _)

/-- fourSubThreeZetaD ∈ OKD. -/
lemma fourSubThreeZetaD_mem_OKD [NeZero d] : fourSubThreeZetaD d ∈ OKD d := by
  unfold fourSubThreeZetaD
  exact Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ 4)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ 3) (zetaD_mem_OKD d))

/-- OKD subalgebra elements. -/
noncomputable def fourSubThreeO [NeZero d] : OKD d := ⟨fourSubThreeZetaD d, fourSubThreeZetaD_mem_OKD d⟩
noncomputable def balanceSumO [NeZero d] (FW : Fin d → ℕ) : OKD d := ⟨balanceSumD d FW, balanceSumD_mem_OKD d FW⟩

@[simp] lemma fourSubThreeO_val [NeZero d] : (fourSubThreeO d : CyclotomicFieldD d) = fourSubThreeZetaD d := rfl
@[simp] lemma balanceSumO_val [NeZero d] (FW : Fin d → ℕ) :
    (balanceSumO d FW : CyclotomicFieldD d) = balanceSumD d FW := rfl

/-- fourSubThreeZetaD ≠ 0 (since ζ_d ≠ 4/3). -/
lemma fourSubThreeZetaD_ne_zero [NeZero d] (hd_ge_2 : d ≥ 2) : fourSubThreeZetaD d ≠ 0 := by
  unfold fourSubThreeZetaD
  intro h_eq
  have hd_pos : 0 < d := by omega
  have h_sub_zero := sub_eq_zero.mp h_eq
  have h_3zeta_eq_4 : (3 : CyclotomicFieldD d) * zetaD d = 4 := h_sub_zero.symm
  have hζ := zetaD_is_primitive d hd_pos
  have h_pow_eq : (4 : CyclotomicFieldD d) ^ d = 3 ^ d := by
    calc (4 : CyclotomicFieldD d) ^ d = (3 * zetaD d) ^ d := by rw [h_3zeta_eq_4]
      _ = 3 ^ d * (zetaD d) ^ d := by ring
      _ = 3 ^ d * 1 := by rw [hζ.pow_eq_one]
      _ = 3 ^ d := by ring
  have : (4 : CyclotomicFieldD d) ^ d ≠ 3 ^ d := by
    intro heq
    have h4 : (4 : CyclotomicFieldD d) ^ d = ((4 : ℕ) ^ d : ℕ) := by norm_cast
    have h3 : (3 : CyclotomicFieldD d) ^ d = ((3 : ℕ) ^ d : ℕ) := by norm_cast
    rw [h4, h3] at heq
    have hinj : Function.Injective (Nat.cast (R := CyclotomicFieldD d)) := Nat.cast_injective
    exact (Nat.ne_of_gt (Nat.pow_lt_pow_left (by omega : 3 < 4) (by omega : d ≠ 0))) (hinj heq)
  exact this h_pow_eq

/-! ## Section 3: Coprimality of 3 and (4-3ζ) in OKD -/

/-- IsCoprime 3 (4-3ζ) in OKD: witness (ζ-1)·3 + 1·(4-3ζ) = 1. -/
lemma isCoprime_three_fourSubThreeO [NeZero d] (hd_ge_2 : d ≥ 2) :
    IsCoprime (⟨3, three_mem_OKD d⟩ : OKD d) (fourSubThreeO d) := by
  have h_zeta_sub_one_mem : zetaD d - 1 ∈ OKD d :=
    Subalgebra.sub_mem _ (zetaD_mem_OKD d) (Subalgebra.one_mem _)
  let a : OKD d := ⟨zetaD d - 1, h_zeta_sub_one_mem⟩
  let b : OKD d := ⟨1, Subalgebra.one_mem _⟩
  have h_sum : a * ⟨3, three_mem_OKD d⟩ + b * fourSubThreeO d = 1 := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_one, fourSubThreeO_val]
    unfold fourSubThreeZetaD; ring
  exact ⟨a, b, h_sum⟩

/-! ## Section 4: Geometric series quotients in OKD -/

/-- Σ_{i<n} 4^{n-1-i} · (3ζ)^i ∈ OKD. -/
lemma geom_series_quotient_mem_OKD' [NeZero d] (n : ℕ) :
    (∑ i ∈ Finset.range n, (4 : CyclotomicFieldD d)^(n - 1 - i) * (3 * zetaD d)^i) ∈ OKD d := by
  apply Subalgebra.sum_mem; intro i _
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ 4) _)
    (Subalgebra.pow_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 3) (zetaD_mem_OKD d)) _)

/-! ## Section 5: Folding lemma — unfolded sum = folded sum via ζ^n = ζ^(n%d) -/

/-- Σ_j w_j · ζ^j = Σ_r FW_r · ζ^r when FW folds w by residue class mod d. -/
lemma sum_unfolded_eq_folded_zetaD [NeZero d] (hd_pos : 0 < d)
    {m : ℕ} (weights : Fin m → ℕ)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m, if (j : ℕ) % d = r.val then weights j else 0) :
    (∑ j : Fin m, (weights j : CyclotomicFieldD d) * (zetaD d)^j.val) =
    (∑ r : Fin d, (FW r : CyclotomicFieldD d) * (zetaD d)^(r : ℕ)) := by
  classical
  let ζ := zetaD d
  have h_pow_mod : ∀ j : Fin m, ζ ^ j.val = ζ ^ (j.val % d) := fun j => zetaD_pow_mod d hd_pos j.val
  conv_lhs => arg 2; ext j; rw [h_pow_mod j]
  symm
  calc ∑ r : Fin d, (FW r : CyclotomicFieldD d) * ζ ^ (r : ℕ)
      = ∑ r : Fin d, (∑ j : Fin m, if j.val % d = r.val
          then (weights j : CyclotomicFieldD d) else 0) * ζ ^ (r : ℕ) := by
        congr 1 with r; congr 1
        simp [h_FW_def r, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    _ = ∑ r : Fin d, ∑ j : Fin m, (if j.val % d = r.val
          then (weights j : CyclotomicFieldD d) else 0) * ζ ^ (r : ℕ) := by
        congr 1 with r; rw [Finset.sum_mul]
    _ = ∑ j : Fin m, ∑ r : Fin d, (if j.val % d = r.val
          then (weights j : CyclotomicFieldD d) else 0) * ζ ^ (r : ℕ) := by
        rw [Finset.sum_comm]
    _ = ∑ j : Fin m, (weights j : CyclotomicFieldD d) * ζ ^ (j.val % d) := by
        congr 1 with j
        rw [Finset.sum_eq_single ⟨j.val % d, Nat.mod_lt j.val hd_pos⟩]
        · simp only [Fin.val_mk, ite_true]
        · intro r _ hr_ne
          have : ¬(j.val % d = r.val) := fun h_eq => hr_ne (Fin.ext h_eq.symm)
          simp only [this, ite_false, zero_mul]
        · intro h_abs; exact absurd (Finset.mem_univ _) h_abs

/-! ## Section 6: Wave sum as polynomial -/

/-- f(x) = Σ_j 3^{m-1-j} · w_j · x^j evaluated at x. -/
def waveSumPoly (m : ℕ) (weights : Fin m → ℕ) (x : ℤ) : ℤ :=
  ∑ j : Fin m, 3^(m - 1 - j.val) * (weights j : ℤ) * x^j.val

/-! ## Section 7: The central bridge theorem

  If Φ_d(4,3) | waveSumPoly(4) in ℤ, then (4-3ζ) | B in O_K.

  This is the bridge from integer divisibility to cyclotomic ring
  divisibility. It lifts realizability from ℤ to ℤ[ζ_d]. -/

/-- Factorization: Φ_d(4,3) = (4-3ζ) · cofactor in CyclotomicFieldD. -/
lemma cyclotomicBivar_eq_fourSubThree_mul_cofactor [NeZero d] (hd_ge_2 : d ≥ 2) :
    ∃ C : CyclotomicFieldD d,
      (cyclotomicBivar d 4 3 : CyclotomicFieldD d) = fourSubThreeZetaD d * C := by
  classical
  have hd_pos : 0 < d := by omega
  let ζ := zetaD d
  let C := ∏ i ∈ Finset.filter (· ≠ 1) (Finset.range d), ((4 : CyclotomicFieldD d) - 3 * ζ ^ i)
  use C
  have hζ := zetaD_is_primitive d hd_pos
  have h_cyc : (cyclotomicBivar d 4 3 : CyclotomicFieldD d) = (4 : CyclotomicFieldD d)^d - 3^d := by
    have hz : (cyclotomicBivar d 4 3 : ℤ) = 4^d - 3^d := by
      linarith [cyclotomicBivar_mul_sub d hd_pos 4 3, show (4 : ℤ) - 3 = 1 from by norm_num]
    simp only [hz, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  rw [h_cyc]
  have h := hζ.pow_sub_pow_eq_prod_sub_mul (4 : CyclotomicFieldD d) 3 hd_pos
  rw [h]
  have h_roots : Polynomial.nthRootsFinset d (1 : CyclotomicFieldD d) =
      Finset.image (fun k => ζ ^ k) (Finset.range d) := by
    ext x; simp only [Polynomial.mem_nthRootsFinset hd_pos, Finset.mem_image, Finset.mem_range]
    exact ⟨fun hx => hζ.eq_pow_of_pow_eq_one hx,
      fun ⟨k, _, hkx⟩ => by rw [← hkx, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]⟩
  rw [h_roots, Finset.prod_image]
  · have h1_in : (1 : ℕ) ∈ Finset.range d := by simp; omega
    have h_split : (∏ k ∈ Finset.range d, ((4 : CyclotomicFieldD d) - 3 * ζ ^ k)) =
        (4 - 3 * ζ ^ 1) * C := by
      rw [← Finset.mul_prod_erase _ _ h1_in]
      congr 1; apply Finset.prod_congr
      · ext k; simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, ne_eq]; tauto
      · intros; rfl
    have h_comm : (∏ k ∈ Finset.range d, ((4 : CyclotomicFieldD d) - ζ ^ k * 3)) =
        ∏ k ∈ Finset.range d, ((4 : CyclotomicFieldD d) - 3 * ζ ^ k) := by
      apply Finset.prod_congr rfl; intro k _; ring
    rw [h_comm, h_split, pow_one]; rfl
  · intro x hx y hy hxy
    exact hζ.injOn_pow (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy

/-- If Φ_d(4,3) | n in ℤ, then (4-3ζ) | n in OKD with quotient in OKD. -/
lemma fourSubThreeZetaD_dvd_of_cyclotomicBivar_dvd_OKD [NeZero d] (hd_ge_2 : d ≥ 2)
    (n : ℤ) (h_dvd : (cyclotomicBivar d 4 3 : ℤ) ∣ n) :
    ∃ T : OKD d, (n : CyclotomicFieldD d) = fourSubThreeZetaD d * (T : CyclotomicFieldD d) := by
  classical
  obtain ⟨k, hk⟩ := h_dvd
  have hd_pos : 0 < d := by omega
  let ζ := zetaD d
  let C_val : CyclotomicFieldD d :=
    ∏ i ∈ Finset.filter (· ≠ 1) (Finset.range d), ((4 : CyclotomicFieldD d) - 3 * ζ ^ i)
  have hC_mem : C_val ∈ OKD d := by
    apply Subalgebra.prod_mem; intro i _
    exact Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ 4)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 3) (Subalgebra.pow_mem _ (zetaD_mem_OKD d) i))
  -- Show bivar = ftz * C_val directly
  have h_bivar_factor : (cyclotomicBivar d 4 3 : CyclotomicFieldD d) = fourSubThreeZetaD d * C_val := by
    have hζ := zetaD_is_primitive d hd_pos
    have h1_in : (1 : ℕ) ∈ Finset.range d := by simp; omega
    have h_prod_split : (∏ i ∈ Finset.range d, ((4 : CyclotomicFieldD d) - 3 * ζ ^ i)) =
        fourSubThreeZetaD d * C_val := by
      rw [← Finset.mul_prod_erase _ _ h1_in, pow_one]
      congr 1; apply Finset.prod_congr
      · ext i; simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, ne_eq]; tauto
      · intros; rfl
    have h_cyc_field : (cyclotomicBivar d 4 3 : CyclotomicFieldD d) =
        ∏ i ∈ Finset.range d, ((4 : CyclotomicFieldD d) - 3 * ζ ^ i) := by
      have hz : (cyclotomicBivar d 4 3 : ℤ) = 4 ^ d - 3 ^ d := by
        linarith [cyclotomicBivar_mul_sub d hd_pos 4 3, show (4 : ℤ) - 3 = 1 from by norm_num]
      simp only [hz, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
      rw [hζ.pow_sub_pow_eq_prod_sub_mul 4 3 hd_pos]
      have h_roots : Polynomial.nthRootsFinset d (1 : CyclotomicFieldD d) =
          Finset.image (fun k => ζ ^ k) (Finset.range d) := by
        ext x; simp only [Polynomial.mem_nthRootsFinset hd_pos, Finset.mem_image, Finset.mem_range]
        exact ⟨fun hx => hζ.eq_pow_of_pow_eq_one hx,
          fun ⟨k, _, hkx⟩ => by rw [← hkx, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]⟩
      rw [h_roots, Finset.prod_image]
      · apply Finset.prod_congr rfl; intro i _; ring
      · intro x hx y hy hxy
        have hx_lt := Finset.mem_range.mp hx
        have hy_lt := Finset.mem_range.mp hy
        exact hζ.injOn_pow (by exact Finset.mem_coe.mpr hx) (by exact Finset.mem_coe.mpr hy) hxy
    rw [h_cyc_field, h_prod_split]
  let C_okd : OKD d := ⟨C_val, hC_mem⟩
  let k_okd : OKD d := ⟨(k : CyclotomicFieldD d), Subalgebra.algebraMap_mem _ k⟩
  use C_okd * k_okd
  simp only [Subalgebra.coe_mul]
  calc (n : CyclotomicFieldD d)
      = (k : CyclotomicFieldD d) * (cyclotomicBivar d 4 3 : CyclotomicFieldD d) := by
        rw [hk]; push_cast; ring
    _ = (k : CyclotomicFieldD d) * (fourSubThreeZetaD d * C_val) := by rw [h_bivar_factor]
    _ = fourSubThreeZetaD d * (C_val * (k : CyclotomicFieldD d)) := by ring

/-- **The central bridge**: Φ_d(4,3) | waveSumPoly(4) ⟹ (4-3ζ) | B in O_K.

    D | W lifts to cyclotomic ring divisibility. -/
theorem OKD_divisibility_from_waveSum_divisibility [NeZero d] (hd_ge_2 : d ≥ 2)
    {m : ℕ} (hm : 0 < m) (hd_dvd : d ∣ m)
    (weights : Fin m → ℕ)
    (FW : Fin d → ℕ)
    (h_FW_def : ∀ r : Fin d, FW r = ∑ j : Fin m, if (j : ℕ) % d = r.val then weights j else 0)
    (h_cyc_dvd : (cyclotomicBivar d 4 3 : ℤ) ∣ waveSumPoly m weights 4) :
    fourSubThreeO d ∣ balanceSumO d FW := by
  classical
  have hd_pos : 0 < d := by omega
  let ζ := zetaD d

  -- Step 1: fourSubThreeZetaD | f(4) from cyclotomic divisibility
  obtain ⟨T_f4_okd, hT_f4_okd⟩ := fourSubThreeZetaD_dvd_of_cyclotomicBivar_dvd_OKD d hd_ge_2
    (waveSumPoly m weights 4) h_cyc_dvd

  -- Step 2: f(4) and f(3ζ) in the cyclotomic field
  let f_at_4 : CyclotomicFieldD d :=
    ∑ j : Fin m, (3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) *
      (4 : CyclotomicFieldD d)^j.val

  let f_at_3z : CyclotomicFieldD d :=
    ∑ j : Fin m, (3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) *
      (3 * ζ)^j.val

  -- Step 3: f(4) = waveSumPoly(4)
  have h_f4_eq : f_at_4 = (waveSumPoly m weights 4 : CyclotomicFieldD d) := by
    unfold f_at_4 waveSumPoly; push_cast; congr 1

  -- Step 4: (4-3ζ) | f(4) - f(3ζ)
  have h_diff_divisible : fourSubThreeZetaD d ∣ f_at_4 - f_at_3z := by
    have h_expand : f_at_4 - f_at_3z =
        ∑ j : Fin m, (3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) *
          ((4 : CyclotomicFieldD d)^j.val - (3 * ζ)^j.val) := by
      unfold f_at_4 f_at_3z; rw [← Finset.sum_sub_distrib]; congr 1 with j; ring
    rw [h_expand]
    apply Finset.dvd_sum; intro j _
    obtain ⟨qj, hqj⟩ := sub_dvd_pow_sub_pow (4 : CyclotomicFieldD d) (3 * ζ) j.val
    -- hqj : 4^j - (3*ζ)^j = (4 - 3*ζ) * qj
    -- Goal: fourSubThreeZetaD d ∣ 3^... * w * (4^j - (3*ζ)^j)
    show fourSubThreeZetaD d ∣ _
    rw [show fourSubThreeZetaD d = (4 : CyclotomicFieldD d) - 3 * ζ from rfl, hqj]
    exact ⟨(3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) * qj, by ring⟩

  -- Step 5: (4-3ζ) | f(3ζ)
  have h_f3z_divisible : fourSubThreeZetaD d ∣ f_at_3z := by
    have h1 : fourSubThreeZetaD d ∣ f_at_4 := by rw [h_f4_eq, hT_f4_okd]; exact dvd_mul_right _ _
    rw [show f_at_3z = f_at_4 - (f_at_4 - f_at_3z) from by ring]
    exact dvd_sub h1 h_diff_divisible

  -- Step 6: f(3ζ) = 3^{m-1} · unfolded_balance
  let unfolded_bal : CyclotomicFieldD d := ∑ j : Fin m, (weights j : CyclotomicFieldD d) * ζ^j.val

  have h_f3z_factor : f_at_3z = (3 : CyclotomicFieldD d)^(m - 1) * unfolded_bal := by
    unfold f_at_3z unfolded_bal; rw [Finset.mul_sum]; congr 1 with j
    simp only [mul_pow]
    have hj_lt : j.val < m := j.isLt
    have h_exp : m - 1 - j.val + j.val = m - 1 := by omega
    rw [show (3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) *
           (3^j.val * ζ^j.val)
        = 3^(m - 1 - j.val) * 3^j.val * (weights j : CyclotomicFieldD d) * ζ^j.val from by ring,
      ← pow_add, h_exp]
    ring

  -- Step 7: Fold: unfolded_bal = balanceSumD
  have h_fold : unfolded_bal = balanceSumD d FW := by
    unfold unfolded_bal balanceSumD
    exact sum_unfolded_eq_folded_zetaD d hd_pos weights FW h_FW_def

  -- Step 8: Build the quotient in OKD
  let T_diff_val : CyclotomicFieldD d :=
    ∑ j : Fin m, (3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) *
      (∑ i ∈ Finset.range j.val, (4 : CyclotomicFieldD d)^(j.val - 1 - i) * (3 * ζ)^i)

  have hT_diff_mem : T_diff_val ∈ OKD d := by
    apply Subalgebra.sum_mem; intro j _
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (three_mem_OKD d) _) (Subalgebra.natCast_mem _ _))
      (geom_series_quotient_mem_OKD' d j.val)

  let T_diff_okd : OKD d := ⟨T_diff_val, hT_diff_mem⟩

  -- Step 9: fourSubThreeZetaD · T_diff = f(4) - f(3ζ)
  have hT_diff_factor : fourSubThreeZetaD d * T_diff_val = f_at_4 - f_at_3z := by
    unfold T_diff_val; rw [Finset.mul_sum]
    have h_expand : f_at_4 - f_at_3z =
        ∑ j : Fin m, (3 : CyclotomicFieldD d)^(m - 1 - j.val) * (weights j : CyclotomicFieldD d) *
          ((4 : CyclotomicFieldD d)^j.val - (3 * ζ)^j.val) := by
      unfold f_at_4 f_at_3z; rw [← Finset.sum_sub_distrib]; congr 1 with j; ring
    rw [h_expand]; congr 1 with j
    have h_ftz : fourSubThreeZetaD d = 4 - 3 * ζ := rfl
    -- geom_sum₂_mul gives: (Σ 4^i * (3ζ)^(n-1-i)) * (4 - 3ζ) = 4^n - (3ζ)^n
    -- We need: (4 - 3ζ) * (Σ 4^(n-1-i) * (3ζ)^i) = 4^n - (3ζ)^n
    -- These are equal by commuting multiplication and reindexing
    have h_telesc : ∀ n : ℕ, (4 - 3 * ζ) *
        (∑ i ∈ Finset.range n, (4 : CyclotomicFieldD d)^(n - 1 - i) * (3 * ζ)^i) =
        4^n - (3 * ζ)^n := by
      intro n; induction n with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        simp only [show k + 1 - 1 - k = 0 from by omega, pow_zero, one_mul]
        rw [mul_add]
        by_cases hk : k = 0
        · subst hk; simp
        · have h_sum_eq : ∑ i ∈ Finset.range k, (4 : CyclotomicFieldD d)^(k + 1 - 1 - i) * (3 * ζ)^i =
              4 * ∑ i ∈ Finset.range k, (4 : CyclotomicFieldD d)^(k - 1 - i) * (3 * ζ)^i := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
            have hi_lt : i < k := Finset.mem_range.mp hi
            have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
            rw [this, pow_succ]; ring
          rw [h_sum_eq]
          -- Goal: (4 - 3*ζ) * (4 * Σ...) + (4 - 3*ζ) * (3*ζ)^k = 4^(k+1) - (3*ζ)^(k+1)
          -- = 4 * ((4 - 3*ζ) * Σ...) + (4 - 3*ζ) * (3*ζ)^k
          -- = 4 * (4^k - (3*ζ)^k) + (4 - 3*ζ) * (3*ζ)^k   [by ih]
          -- = 4^(k+1) - 4*(3*ζ)^k + 4*(3*ζ)^k - 3*(3*ζ)^k*ζ  [expand]
          -- = 4^(k+1) - (3*ζ)^(k+1)
          linear_combination 4 * ih
    rw [h_ftz]
    have := h_telesc j.val
    calc (4 - 3 * ζ) * (3 ^ (m - 1 - j.val) * ↑(weights j) *
           ∑ i ∈ Finset.range j.val, 4 ^ (j.val - 1 - i) * (3 * ζ) ^ i)
        = 3 ^ (m - 1 - j.val) * ↑(weights j) *
           ((4 - 3 * ζ) * ∑ i ∈ Finset.range j.val, 4 ^ (j.val - 1 - i) * (3 * ζ) ^ i) := by ring
      _ = 3 ^ (m - 1 - j.val) * ↑(weights j) *
           (4 ^ j.val - (3 * ζ) ^ j.val) := by rw [this]

  -- Step 10: S = T_f4 - T_diff
  let S_okd : OKD d := T_f4_okd - T_diff_okd

  have hS_factor : fourSubThreeZetaD d * (S_okd : CyclotomicFieldD d) =
      (3 : CyclotomicFieldD d)^(m-1) * balanceSumD d FW := by
    show fourSubThreeZetaD d * ((T_f4_okd : CyclotomicFieldD d) - (T_diff_okd : CyclotomicFieldD d)) = _
    rw [mul_sub, ← hT_f4_okd,
      show (waveSumPoly m weights 4 : CyclotomicFieldD d) = f_at_4 from h_f4_eq.symm,
      hT_diff_factor, show f_at_4 - (f_at_4 - f_at_3z) = f_at_3z from by ring,
      h_f3z_factor, h_fold]

  -- Step 11: fourSubThreeO | 3^{m-1} · balanceSumO in OKD
  have h_scaled_div_OKD : fourSubThreeO d ∣
      (⟨(3 : CyclotomicFieldD d)^(m-1), Subalgebra.pow_mem _ (three_mem_OKD d) _⟩ : OKD d) *
      balanceSumO d FW := by
    use S_okd
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, fourSubThreeO_val, balanceSumO_val]
    exact hS_factor.symm

  -- Step 12: Coprimality cancels 3^{m-1}
  have h_coprime_pow : IsCoprime
      (⟨(3 : CyclotomicFieldD d)^(m-1), Subalgebra.pow_mem _ (three_mem_OKD d) _⟩ : OKD d)
      (fourSubThreeO d) := by
    have h_base := isCoprime_three_fourSubThreeO d hd_ge_2
    induction m - 1 with
    | zero => simp only [pow_zero]; exact isCoprime_one_left
    | succ k ih =>
      simp only [pow_succ]
      exact IsCoprime.mul_left ih h_base

  exact IsCoprime.dvd_of_dvd_mul_left h_coprime_pow.symm h_scaled_div_OKD

/-! ## Section 8: Evaluation rigidity — the 4-adic cascade

  If (4-3ζ) | B in O_K, then evaluating at ζ = 4/3 (the zero of 4-3ζ)
  shows (4^d - 3^d) | evalSum43(FW) in ℤ. Combined with the bound
  0 ≤ evalSum43 ≤ N·(4^d-3^d), we get evalSum43 = k·(4^d-3^d) for
  0 ≤ k ≤ N. Then g_r = FW_r - k satisfies |g_r| < 4 and
  Σ g_r·4^r·3^{d-1-r} = 0, and the 4-adic cascade forces g_r = 0.

  This is the pure-ℤ kill shot: no norms, no infinite places, just
  polynomial evaluation + coprimality of 4 and 3. -/

/-- evalSum43 for folded weights: Σ FW_r · 4^r · 3^{d-1-r}. -/
def evalSum43' (d : ℕ) (FW : Fin d → ℕ) : ℤ :=
  ∑ r : Fin d, (FW r : ℤ) * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))

/-- Generalized integer evaluation:
`Σ FW_r · x^r · y^(d-1-r)`. -/
def evalSumXY (d : ℕ) (FW : Fin d → ℕ) (x y : ℤ) : ℤ :=
  ∑ r : Fin d, (FW r : ℤ) * x ^ (r : ℕ) * y ^ (d - 1 - (r : ℕ))

@[simp] lemma evalSumXY_43 (d : ℕ) (FW : Fin d → ℕ) :
    evalSumXY d FW 4 3 = evalSum43' d FW := by
  rfl

/-- Geometric sum: Σ_{r<d} 4^r · 3^{d-1-r} = 4^d - 3^d. -/
private lemma geom_sum_43_bridge (d : ℕ) (hd : 0 < d) :
    ∑ r : Fin d, (4 : ℤ) ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) = 4 ^ d - 3 ^ d := by
  induction d with
  | zero => omega
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h_last : (4 : ℤ) ^ n * 3 ^ (n + 1 - 1 - n) = 4 ^ n := by
      rw [show n + 1 - 1 - n = 0 from by omega]; simp
    rw [h_last]
    by_cases hn : n = 0
    · subst hn; simp
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h_eq : ∑ r : Fin n, (4 : ℤ) ^ (↑r : ℕ) * 3 ^ (n + 1 - 1 - (↑r : ℕ)) =
          3 * ∑ r : Fin n, (4 : ℤ) ^ (↑r : ℕ) * 3 ^ (n - 1 - (↑r : ℕ)) := by
        rw [Finset.mul_sum]; congr 1; ext r
        have hr_lt : (r : ℕ) < n := r.isLt
        rw [show n + 1 - 1 - (↑r : ℕ) = (n - 1 - (↑r : ℕ)) + 1 from by omega, pow_succ]; ring
      rw [h_eq, ih hn_pos]; ring

/-- Upper bound: evalSum43' ≤ N · (4^d - 3^d). -/
private lemma evalSum43'_le_N (d : ℕ) (hd : 0 < d) (FW : Fin d → ℕ)
    (N : ℕ) (h_bdd : ∀ r : Fin d, FW r ≤ N) :
    evalSum43' d FW ≤ ↑N * (4 ^ d - 3 ^ d) := by
  unfold evalSum43'
  calc ∑ r : Fin d, (FW r : ℤ) * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))
      ≤ ∑ r : Fin d, (N : ℤ) * (4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))) := by
        apply Finset.sum_le_sum; intro r _
        have : (FW r : ℤ) ≤ N := Int.ofNat_le.mpr (h_bdd r)
        calc (FW r : ℤ) * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))
            = (FW r : ℤ) * (4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))) := by ring
          _ ≤ (N : ℤ) * (4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))) := by
              exact mul_le_mul_of_nonneg_right this
                (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
    _ = ↑N * ∑ r : Fin d, 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) := by rw [← Finset.mul_sum]
    _ = ↑N * ((4 : ℤ) ^ d - 3 ^ d) := by congr 1; exact_mod_cast geom_sum_43_bridge d hd

/-- Nonnegativity of evalSum43'. -/
private lemma evalSum43'_nonneg (d : ℕ) (FW : Fin d → ℕ) :
    0 ≤ evalSum43' d FW := by
  unfold evalSum43'
  apply Finset.sum_nonneg; intro r _
  exact mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _)

/-- 4-adic cascade: if Σ g_r · 4^r · 3^{d-1-r} = 0 with |g_r| < 4, then all g_r = 0.

  Bottom-up induction: terms with index < r are 0 by IH, terms with index > r
  have factor 4^{r+1}. So 4 | g_r · 3^{d-1-r}. Since gcd(4,3) = 1, 4 | g_r.
  Combined with |g_r| < 4, this forces g_r = 0. -/
private lemma four_adic_dvd_below' (d : ℕ) (hd : 0 < d)
    (g : Fin d → ℤ)
    (h_bound : ∀ r : Fin d, |g r| < 4)
    (h_sum : ∑ r : Fin d, g r * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) = 0)
    (n : ℕ) (hn : n ≤ d) :
    ∀ r : Fin d, (r : ℕ) < n → g r = 0 := by
  induction n with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have hn_lt : n < d := by omega
    by_cases hr_eq : (r : ℕ) = n
    · have h_prev : ∀ i : Fin d, (i : ℕ) < n → g i = 0 := ih (by omega)
      have h_sum_split : g ⟨n, hn_lt⟩ * 4 ^ n * 3 ^ (d - 1 - n) +
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => n < (i : ℕ)),
            g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)) = 0 := by
        have h_rewrite : ∑ r : Fin d, g r * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) =
            g ⟨n, hn_lt⟩ * 4 ^ n * 3 ^ (d - 1 - n) +
            ∑ i ∈ Finset.univ.filter (fun i : Fin d => n < (i : ℕ)),
              g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)) := by
          have h_split := Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i : Fin d => n ≤ (i : ℕ))
            (fun i => g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)))
          have h_low : ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬n ≤ (i : ℕ)),
              g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)) = 0 := by
            apply Finset.sum_eq_zero; intro i hi
            rw [Finset.mem_filter] at hi; rw [h_prev i (by omega)]; ring
          have h_ge_split : ∑ i ∈ Finset.univ.filter (fun i : Fin d => n ≤ (i : ℕ)),
              g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)) =
              g ⟨n, hn_lt⟩ * 4 ^ n * 3 ^ (d - 1 - n) +
              ∑ i ∈ Finset.univ.filter (fun i : Fin d => n < (i : ℕ)),
                g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)) := by
            have h_eq_filter : Finset.univ.filter (fun i : Fin d => n ≤ (i : ℕ)) =
                (Finset.univ.filter (fun i : Fin d => (i : ℕ) = n)) ∪
                (Finset.univ.filter (fun i : Fin d => n < (i : ℕ))) := by
              ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
            rw [h_eq_filter, Finset.sum_union (by rw [Finset.disjoint_filter]; intro x _ hx; omega)]
            congr 1
            have : Finset.univ.filter (fun i : Fin d => (i : ℕ) = n) = {⟨n, hn_lt⟩} := by
              ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton, Fin.ext_iff]
            rw [this, Finset.sum_singleton]
          linarith
        linarith
      have h_above_dvd : (4 : ℤ) ^ (n + 1) ∣
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => n < (i : ℕ)),
            g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ)) := by
        apply Finset.dvd_sum; intro i hi
        rw [Finset.mem_filter] at hi
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow 4 hi.2) _) _
      have h_dvd_term : (4 : ℤ) ^ (n + 1) ∣ g ⟨n, hn_lt⟩ * 4 ^ n * 3 ^ (d - 1 - n) := by
        have : g ⟨n, hn_lt⟩ * 4 ^ n * 3 ^ (d - 1 - n) =
            -(∑ i ∈ Finset.univ.filter (fun i : Fin d => n < (i : ℕ)),
              g i * 4 ^ (i : ℕ) * 3 ^ (d - 1 - (i : ℕ))) := by linarith
        rw [this]; exact dvd_neg.mpr h_above_dvd
      have h_dvd_g3 : (4 : ℤ) ∣ g ⟨n, hn_lt⟩ * 3 ^ (d - 1 - n) := by
        rw [show (4 : ℤ) ^ (n + 1) = 4 ^ n * 4 from by ring] at h_dvd_term
        rw [show g ⟨n, hn_lt⟩ * 4 ^ n * 3 ^ (d - 1 - n) =
            4 ^ n * (g ⟨n, hn_lt⟩ * 3 ^ (d - 1 - n)) from by ring] at h_dvd_term
        exact (mul_dvd_mul_iff_left (ne_of_gt (pow_pos (by norm_num : (0:ℤ) < 4) n))).mp h_dvd_term
      have h_coprime : IsCoprime (4 : ℤ) (3 ^ (d - 1 - n)) := (by decide : IsCoprime (4:ℤ) 3).pow_right
      have h_dvd_g : (4 : ℤ) ∣ g ⟨n, hn_lt⟩ := h_coprime.dvd_of_dvd_mul_right h_dvd_g3
      rw [show r = (⟨n, hn_lt⟩ : Fin d) from Fin.ext (by omega)]
      obtain ⟨k, hk⟩ := h_dvd_g
      rw [hk]
      have hb := h_bound ⟨n, hn_lt⟩
      rw [hk, abs_mul, show |(4 : ℤ)| = 4 from rfl] at hb
      have : k = 0 := by
        by_contra h_ne
        linarith [Int.one_le_abs h_ne, mul_le_mul_of_nonneg_left (Int.one_le_abs h_ne) (by norm_num : (0:ℤ) ≤ 4)]
      rw [this]; ring
    · exact ih (by omega) r (by omega)

private lemma four_adic_forces_zero' (d : ℕ) (hd : 0 < d)
    (g : Fin d → ℤ)
    (h_bound : ∀ r : Fin d, |g r| < 4)
    (h_sum : ∑ r : Fin d, g r * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) = 0) :
    ∀ r : Fin d, g r = 0 :=
  fun r => four_adic_dvd_below' d hd g h_bound h_sum d le_rfl r (Fin.isLt r)

/-- **Evaluation rigidity**: if (4-3ζ) | B in O_K and all FW_r ≤ N < 4,
    then all FW_r are equal.

    The proof works entirely in ℤ via the evaluation trick:
    1. (4-3ζ) | B ⟹ (4^d - 3^d) | evalSum43'(FW) [via divisibility_transfer]
    2. 0 ≤ evalSum43' ≤ N·(4^d-3^d), so evalSum43' = k·(4^d-3^d) for 0 ≤ k ≤ N
    3. g_r = FW_r - k satisfies |g_r| < 4 and Σ g_r·4^r·3^{d-1-r} = 0
    4. 4-adic cascade: all g_r = 0, so all FW_r = k

    Note: This theorem accepts the divisibility (4^d-3^d) | evalSum43' as hypothesis,
    since the evaluation transfer from cyclotomic fields is established separately. -/
theorem folded_weights_all_equal_from_int_dvd (d : ℕ) (hd : 0 < d)
    (FW : Fin d → ℕ) (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N)
    (h_dvd : (4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FW) :
    ∀ r s : Fin d, FW r = FW s := by
  have hD_pos : (0 : ℤ) < 4 ^ d - 3 ^ d := by
    have h_nat : (3 : ℕ) ^ d < (4 : ℕ) ^ d := Nat.pow_lt_pow_left (by omega) (by omega)
    have : (3 : ℤ) ^ d < 4 ^ d := by exact_mod_cast h_nat
    linarith
  have h_nonneg := evalSum43'_nonneg d FW
  have h_upper := evalSum43'_le_N d hd FW N h_bdd
  obtain ⟨k, hk⟩ := h_dvd
  have hk_nonneg : 0 ≤ k := by
    by_contra h_neg; push_neg at h_neg
    linarith [show evalSum43' d FW ≤ (4 ^ d - 3 ^ d) * (-1) from by
      rw [hk]; exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hD_pos)]
  have hk_le_N : k ≤ N := by
    by_contra h_big; push_neg at h_big
    linarith [show (4 ^ d - 3 ^ d) * (↑N + 1) ≤ evalSum43' d FW from by
      rw [hk]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast h_big) (le_of_lt hD_pos)]
  set g : Fin d → ℤ := fun r => (FW r : ℤ) - k
  have h_g_sum : ∑ r : Fin d, g r * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) = 0 := by
    have h_expand : ∑ r : Fin d, g r * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) =
        evalSum43' d FW - k * ∑ r : Fin d, (4 : ℤ) ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ)) := by
      simp only [g, sub_mul, sub_mul]
      rw [Finset.sum_sub_distrib]; unfold evalSum43'
      congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    rw [h_expand, geom_sum_43_bridge d hd, hk]; ring
  have h_g_bound : ∀ r : Fin d, |g r| < 4 := by
    intro r; simp only [g]
    rw [abs_lt]; constructor
    · linarith [Int.natCast_nonneg (FW r)]
    · linarith [Int.ofNat_le.mpr (h_bdd r)]
  have h_all_zero := four_adic_forces_zero' d hd g h_g_bound h_g_sum
  intro r s
  have hr := h_all_zero r; have hs := h_all_zero s
  simp only [g, sub_eq_zero] at hr hs
  exact Nat.cast_injective (by linarith : (FW r : ℤ) = FW s)

/-- Under the same bounded-window hypotheses (`FW_r ≤ N < 4`), any non-uniform
folded-weight vector cannot satisfy the cyclotomic divisibility condition. -/
theorem nonuniform_folded_weights_not_divisible (d : ℕ) (hd : 0 < d)
    (FW : Fin d → ℕ) (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N)
    (h_nonuniform : ∃ r s : Fin d, FW r ≠ FW s) :
    ¬((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FW) := by
  intro h_dvd
  have h_all_eq := folded_weights_all_equal_from_int_dvd d hd FW N hN h_bdd h_dvd
  rcases h_nonuniform with ⟨r, s, hrs⟩
  exact hrs (h_all_eq r s)

/-- Eventual version: if an "irrational-profile" folded sequence becomes
non-uniform at some loop index, then at that index it fails the same
cyclotomic divisibility condition used by the integer profile. -/
theorem eventually_not_divisible_of_eventual_nonuniform
    (d : ℕ) (hd : 0 < d)
    (FWirr : ℕ → Fin d → ℕ) (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ L : ℕ, ∀ r : Fin d, FWirr L r ≤ N)
    (h_eventual_nonuniform : ∃ L : ℕ, ∃ r s : Fin d, FWirr L r ≠ FWirr L s) :
    ∃ L : ℕ, ¬((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (FWirr L)) := by
  rcases h_eventual_nonuniform with ⟨L, r, s, hrs⟩
  refine ⟨L, ?_⟩
  exact nonuniform_folded_weights_not_divisible d hd (FWirr L) N hN (h_bdd L) ⟨r, s, hrs⟩

/-- Integer-vs-irrational incompatibility: if the irrational folded profile
eventually becomes non-uniform, then eventually the two profiles cannot both
satisfy the same cyclotomic divisibility requirement. -/
theorem eventually_not_both_divisible_integer_and_irrational
    (d : ℕ) (hd : 0 < d)
    (FWint : Fin d → ℕ)
    (FWirr : ℕ → Fin d → ℕ) (N : ℕ) (hN : N < 4)
    (h_bdd_irr : ∀ L : ℕ, ∀ r : Fin d, FWirr L r ≤ N)
    (h_eventual_nonuniform : ∃ L : ℕ, ∃ r s : Fin d, FWirr L r ≠ FWirr L s) :
    ∃ L : ℕ,
      ¬(((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FWint) ∧
        ((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (FWirr L))) := by
  obtain ⟨L, h_not_div_irr⟩ :=
    eventually_not_divisible_of_eventual_nonuniform d hd FWirr N hN h_bdd_irr h_eventual_nonuniform
  refine ⟨L, ?_⟩
  intro hboth
  exact h_not_div_irr hboth.2

/-! ### Concrete drift-update model for irrational folded weights -/

/-- Any nonzero real drift eventually has nonzero rounded accumulated drift:
there exists a loop count `L` with `round (L * drift) ≠ 0`. -/
lemma exists_round_mul_ne_zero_of_ne_zero (drift : ℝ) (h_drift : drift ≠ 0) :
    ∃ L : ℕ, round ((L : ℝ) * drift) ≠ 0 := by
  have h_abs_pos : 0 < |drift| := abs_pos.mpr h_drift
  let L : ℕ := Nat.ceil (1 / |drift|)
  refine ⟨L, ?_⟩
  intro h_round
  have hL_ge : (L : ℝ) ≥ 1 / |drift| := Nat.le_ceil (1 / |drift|)
  have h_abs_mul_ge_one : |(L : ℝ) * drift| ≥ 1 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) by exact_mod_cast Nat.zero_le L)]
    have h_abs_nonneg : (0 : ℝ) ≤ |drift| := abs_nonneg drift
    have h1 : (L : ℝ) * |drift| ≥ (1 / |drift|) * |drift| :=
      mul_le_mul_of_nonneg_right hL_ge h_abs_nonneg
    have h_inv : (1 / |drift|) * |drift| = 1 := by
      field_simp [h_drift]
    linarith [h1, h_inv]
  have h_abs_le_half : |(L : ℝ) * drift| ≤ 1 / 2 := by
    have h_eq : (L : ℝ) * drift = (L : ℝ) * drift - (round ((L : ℝ) * drift) : ℝ) := by
      rw [h_round]
      ring
    rw [h_eq]
    exact abs_sub_round ((L : ℝ) * drift)
  linarith

/-- Stronger form: if `drift ≠ 0`, then beyond some threshold `L0`,
the rounded accumulated drift is never zero. -/
lemma eventually_round_mul_ne_zero_of_ne_zero (drift : ℝ) (h_drift : drift ≠ 0) :
    ∃ L0 : ℕ, ∀ L : ℕ, L ≥ L0 → round ((L : ℝ) * drift) ≠ 0 := by
  have h_abs_pos : 0 < |drift| := abs_pos.mpr h_drift
  let L0 : ℕ := Nat.ceil (1 / |drift|)
  refine ⟨L0, ?_⟩
  intro L hL
  intro h_round
  have hL_ge : (L : ℝ) ≥ 1 / |drift| := by
    have hL_nat : L ≥ L0 := hL
    exact le_trans (Nat.le_ceil (1 / |drift|)) (by exact_mod_cast hL_nat)
  have h_abs_mul_ge_one : |(L : ℝ) * drift| ≥ 1 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) by exact_mod_cast Nat.zero_le L)]
    have h_abs_nonneg : (0 : ℝ) ≤ |drift| := abs_nonneg drift
    have h1 : (L : ℝ) * |drift| ≥ (1 / |drift|) * |drift| :=
      mul_le_mul_of_nonneg_right hL_ge h_abs_nonneg
    have h_inv : (1 / |drift|) * |drift| = 1 := by
      field_simp [h_drift]
    linarith [h1, h_inv]
  have h_abs_le_half : |(L : ℝ) * drift| ≤ 1 / 2 := by
    have h_eq : (L : ℝ) * drift = (L : ℝ) * drift - (round ((L : ℝ) * drift) : ℝ) := by
      rw [h_round]
      ring
    rw [h_eq]
    exact abs_sub_round ((L : ℝ) * drift)
  linarith [h_abs_mul_ge_one, h_abs_le_half]

/-- One-bit drift indicator from accumulated irrational drift `L * drift`. -/
noncomputable def driftBit (drift : ℝ) (L : ℕ) : ℕ :=
  if round ((L : ℝ) * drift) = 0 then 0 else 1

lemma driftBit_le_one (drift : ℝ) (L : ℕ) : driftBit drift L ≤ 1 := by
  unfold driftBit
  split_ifs <;> omega

/-- Concrete irrational folded-weight update:
only residue class `0` receives the drift bit. -/
noncomputable def driftUpdatedFoldedWeights (d : ℕ)
    (FWint : Fin d → ℕ) (drift : ℝ) (L : ℕ) : Fin d → ℕ :=
  fun r => if r.val = 0 then FWint r + driftBit drift L else FWint r

lemma driftBit_eq_zero_of_zero_drift (L : ℕ) :
    driftBit 0 L = 0 := by
  unfold driftBit
  simp

lemma driftUpdatedFoldedWeights_zero_drift (d : ℕ)
    (FWint : Fin d → ℕ) (L : ℕ) :
    driftUpdatedFoldedWeights d FWint 0 L = FWint := by
  funext r
  unfold driftUpdatedFoldedWeights
  split_ifs with h0
  · rw [driftBit_eq_zero_of_zero_drift]
    omega
  · rfl

/-- Zero-drift propagation: if the real-side divisibility condition holds at
one loop index and drift is zero, then it holds at every loop index because
the drift-updated folded weights are constant in `L`. -/
theorem divisibility_holds_forever_of_zero_drift
    (d : ℕ) (FWint : Fin d → ℕ) (L0 : ℕ)
    (h_once : (4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (driftUpdatedFoldedWeights d FWint 0 L0)) :
    ∀ L : ℕ, (4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (driftUpdatedFoldedWeights d FWint 0 L) := by
  intro L
  simpa [driftUpdatedFoldedWeights_zero_drift] using h_once

lemma driftUpdatedFoldedWeights_bdd_three
    (d : ℕ) (FWint : Fin d → ℕ) (drift : ℝ)
    (h_fwint_bdd : ∀ r : Fin d, FWint r ≤ 2) :
    ∀ L : ℕ, ∀ r : Fin d, driftUpdatedFoldedWeights d FWint drift L r ≤ 3 := by
  intro L r
  unfold driftUpdatedFoldedWeights
  split_ifs with h0
  · calc
      FWint r + driftBit drift L ≤ 2 + 1 := by
        exact Nat.add_le_add (h_fwint_bdd r) (driftBit_le_one drift L)
      _ = 3 := by norm_num
  · exact le_trans (h_fwint_bdd r) (by norm_num)

lemma driftUpdatedFoldedWeights_nonuniform_of_round_ne_zero
    (d : ℕ) (hd_ge_2 : d ≥ 2)
    (FWint : Fin d → ℕ) (drift : ℝ) (L : ℕ)
    (h_uniform : ∀ r s : Fin d, FWint r = FWint s)
    (h_round_ne_zero : round ((L : ℝ) * drift) ≠ 0) :
    ∃ r s : Fin d, driftUpdatedFoldedWeights d FWint drift L r ≠
      driftUpdatedFoldedWeights d FWint drift L s := by
  let r0 : Fin d := ⟨0, by omega⟩
  let r1 : Fin d := ⟨1, by omega⟩
  refine ⟨r0, r1, ?_⟩
  have hbit_one : driftBit drift L = 1 := by
    unfold driftBit
    simp [h_round_ne_zero]
  have h_r0 : driftUpdatedFoldedWeights d FWint drift L r0 = FWint r0 + 1 := by
    unfold driftUpdatedFoldedWeights
    simp [r0, hbit_one]
  have h_r1 : driftUpdatedFoldedWeights d FWint drift L r1 = FWint r1 := by
    unfold driftUpdatedFoldedWeights
    have : (r1 : Fin d).val ≠ 0 := by simp [r1]
    simp [r1, this]
  rw [h_r0, h_r1, h_uniform r0 r1]
  omega

/-- Fixed-step incompatibility: at any loop index `L` where rounded accumulated
drift is nonzero, integer and drift-updated folded weights cannot both satisfy
the same cyclotomic divisibility requirement. -/
theorem not_both_divisible_from_drift_update_at_L
    (d : ℕ) (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (FWint : Fin d → ℕ) (drift : ℝ) (L : ℕ)
    (h_fwint_bdd : ∀ r : Fin d, FWint r ≤ 2)
    (h_uniform : ∀ r s : Fin d, FWint r = FWint s)
    (h_round_ne_zero : round ((L : ℝ) * drift) ≠ 0) :
    ¬(((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FWint) ∧
      ((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (driftUpdatedFoldedWeights d FWint drift L))) := by
  have h_nonuniform :
      ∃ r s : Fin d, driftUpdatedFoldedWeights d FWint drift L r ≠
        driftUpdatedFoldedWeights d FWint drift L s :=
    driftUpdatedFoldedWeights_nonuniform_of_round_ne_zero d hd_ge_2 FWint drift L h_uniform
      h_round_ne_zero
  have h_bdd_irr : ∀ r : Fin d, driftUpdatedFoldedWeights d FWint drift L r ≤ 3 :=
    driftUpdatedFoldedWeights_bdd_three d FWint drift h_fwint_bdd L
  have h_not_div_irr :
      ¬((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (driftUpdatedFoldedWeights d FWint drift L)) :=
    nonuniform_folded_weights_not_divisible d hd (driftUpdatedFoldedWeights d FWint drift L)
      3 (by norm_num) h_bdd_irr h_nonuniform
  intro hboth
  exact h_not_div_irr hboth.2

/-- Concrete bridge theorem: under the drift-update rule, once accumulated
drift has nonzero rounded integer part, the irrational folded weights are
non-uniform and therefore cannot keep the same cyclotomic divisibility
requirement as the integer folded weights. -/
theorem eventually_not_both_divisible_from_drift_update
    (d : ℕ) (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (FWint : Fin d → ℕ) (drift : ℝ)
    (h_fwint_bdd : ∀ r : Fin d, FWint r ≤ 2)
    (h_uniform : ∀ r s : Fin d, FWint r = FWint s)
    (h_eventual_round_ne_zero : ∃ L : ℕ, round ((L : ℝ) * drift) ≠ 0) :
    ∃ L : ℕ,
      ¬(((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FWint) ∧
        ((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (driftUpdatedFoldedWeights d FWint drift L))) := by
  set FWirr : ℕ → Fin d → ℕ := fun L => driftUpdatedFoldedWeights d FWint drift L
  have h_bdd_irr : ∀ L : ℕ, ∀ r : Fin d, FWirr L r ≤ 3 := by
    intro L r
    exact driftUpdatedFoldedWeights_bdd_three d FWint drift h_fwint_bdd L r
  have h_eventual_nonuniform : ∃ L : ℕ, ∃ r s : Fin d, FWirr L r ≠ FWirr L s := by
    rcases h_eventual_round_ne_zero with ⟨L, hL⟩
    rcases driftUpdatedFoldedWeights_nonuniform_of_round_ne_zero d hd_ge_2 FWint drift L
      h_uniform hL with ⟨r, s, hrs⟩
    exact ⟨L, r, s, hrs⟩
  exact eventually_not_both_divisible_integer_and_irrational d hd FWint FWirr 3
    (by norm_num) h_bdd_irr h_eventual_nonuniform

/-- Drift-only corollary: the eventual nonzero-round premise is generated
internally from `drift ≠ 0`. -/
theorem eventually_not_both_divisible_from_drift_update_of_ne_zero
    (d : ℕ) (hd : 0 < d) (hd_ge_2 : d ≥ 2)
    (FWint : Fin d → ℕ) (drift : ℝ)
    (h_fwint_bdd : ∀ r : Fin d, FWint r ≤ 2)
    (h_uniform : ∀ r s : Fin d, FWint r = FWint s)
    (h_drift : drift ≠ 0) :
    ∃ L : ℕ,
      ¬(((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FWint) ∧
        ((4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d (driftUpdatedFoldedWeights d FWint drift L))) := by
  obtain ⟨L, hL⟩ := exists_round_mul_ne_zero_of_ne_zero drift h_drift
  exact eventually_not_both_divisible_from_drift_update d hd hd_ge_2 FWint drift
    h_fwint_bdd h_uniform ⟨L, hL⟩

/-- Balance polynomial: p(X) = Σ FW_r · X^r -/
private noncomputable def balancePoly (d : ℕ) (FW : Fin d → ℕ) : Polynomial ℤ :=
  ∑ r : Fin d, Polynomial.C (FW r : ℤ) * Polynomial.X ^ (r : ℕ)

/-- Evaluating the balance polynomial at ζ gives the balance sum. -/
private lemma balancePoly_aeval_eq [NeZero d] (FW : Fin d → ℕ) :
    Polynomial.aeval (zetaD d) (balancePoly d FW) = balanceSumD d FW := by
  unfold balancePoly balanceSumD
  simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, map_natCast]

/-- T ∈ OKD = Algebra.adjoin ℤ {ζ} can be written as a polynomial in ζ. -/
private lemma T_exists_as_poly [NeZero d] (T : OKD d) :
    ∃ g : Polynomial ℤ, Polynomial.aeval (zetaD d) g = (T : CyclotomicFieldD d) := by
  have h_mem : (T : CyclotomicFieldD d) ∈ Algebra.adjoin ℤ ({zetaD d} : Set (CyclotomicFieldD d)) := T.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h_mem
  exact h_mem

/-- If p(ζ) = 0 in the cyclotomic field, then the d-th cyclotomic polynomial divides p.
    This uses the fact that for prime d, minpoly ℚ ζ = Φ_d. -/
private lemma cyclotomic_dvd_of_aeval_zero [NeZero d] (hd_prime : Nat.Prime d)
    (p : Polynomial ℤ) (hp : Polynomial.aeval (zetaD d) p = 0) :
    Polynomial.cyclotomic d ℤ ∣ p := by
  have hd_pos : 0 < d := hd_prime.pos
  have hζ := zetaD_is_primitive d hd_pos
  have hp_Q : Polynomial.aeval (zetaD d) (p.map (algebraMap ℤ ℚ)) = 0 := by
    rwa [Polynomial.aeval_map_algebraMap]
  have h_dvd_Q : minpoly ℚ (zetaD d) ∣ p.map (algebraMap ℤ ℚ) :=
    minpoly.dvd ℚ _ hp_Q
  rw [← (IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible hζ
    (Polynomial.cyclotomic.irreducible_rat hd_pos))] at h_dvd_Q
  rw [← Polynomial.map_cyclotomic d (algebraMap ℤ ℚ)] at h_dvd_Q
  exact (Polynomial.map_dvd_map (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
    (Polynomial.cyclotomic.monic d ℤ)).mp h_dvd_Q

/-- **Divisibility transfer from OKD to ℤ (prime case)**: if d is prime and
    (4-3ζ) | B in O_K, then (4^d - 3^d) | evalSum43'(FW) in ℤ.

    Proof: Write B = (4-3ζ)·T, express T = g(ζ) as polynomial. Then
    p(X) - (4-3X)·g(X) vanishes at ζ, so Φ_d | (p-(4-3X)·g) in ℤ[X].
    Evaluate at X=4/3 (where 4-3X=0): p(4/3) = Φ_d(4/3)·h(4/3).
    Clear 3^{d-1}: evalSum43' is divisible by Φ_d(4,3) = 4^d-3^d. -/
theorem divisibility_transfer_from_OKD_prime [NeZero d] (hd_prime : Nat.Prime d)
    (FW : Fin d → ℕ) (h_OKD_dvd : fourSubThreeO d ∣ balanceSumO d FW) :
    (4 ^ d - 3 ^ d : ℤ) ∣ evalSum43' d FW := by
  have hd_pos : 0 < d := hd_prime.pos
  -- Extract T : OKD d with B = (4-3ζ)·T
  obtain ⟨T, hT⟩ := h_OKD_dvd
  have hT_field : balanceSumD d FW = fourSubThreeZetaD d * (T : CyclotomicFieldD d) := by
    have := congr_arg Subtype.val hT
    simp only [Subalgebra.coe_mul, fourSubThreeO_val, balanceSumO_val] at this; exact this
  -- T = g(ζ) for some polynomial g ∈ ℤ[X]
  obtain ⟨g, hg⟩ := T_exists_as_poly d T
  -- Build: α(X) = 4 - 3X, p(X) = balancePoly
  set p := balancePoly d FW
  set α := Polynomial.C (4 : ℤ) - Polynomial.C 3 * Polynomial.X
  have hα_zeta : Polynomial.aeval (zetaD d) α = fourSubThreeZetaD d := by
    unfold fourSubThreeZetaD
    simp only [α, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_ofNat]
  -- p(ζ) - α(ζ)·g(ζ) = 0
  set diff := p - α * g
  have h_diff_zero : Polynomial.aeval (zetaD d) diff = 0 := by
    simp only [diff, map_sub, map_mul, hα_zeta, hg]
    rw [balancePoly_aeval_eq, hT_field]; ring
  -- Φ_d | diff in ℤ[X]
  obtain ⟨h, hh⟩ := cyclotomic_dvd_of_aeval_zero d hd_prime diff h_diff_zero
  -- p = α·g + Φ_d·h
  have hf_decomp : p = α * g + Polynomial.cyclotomic d ℤ * h := by
    have h1 : p - α * g = Polynomial.cyclotomic d ℤ * h := hh
    have h2 : p = p - α * g + α * g := by ring
    rw [h2, h1]; ring
  -- Evaluate at X = 4/3 ∈ ℚ using eval₂
  let ev : Polynomial ℤ →+* ℚ := Polynomial.eval₂RingHom (Int.castRingHom ℚ) (4/3 : ℚ)
  have hev_α : ev α = 0 := by
    simp [ev, α, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    push_cast; ring
  -- ev(p) = ev(Φ_d)·ev(h)
  have hev_p_eq : ev p = ev (Polynomial.cyclotomic d ℤ) * ev h := by
    have : ev p = ev (α * g + Polynomial.cyclotomic d ℤ * h) := by rw [← hf_decomp]
    rw [this, map_add, map_mul, map_mul, hev_α, zero_mul, zero_add]
  -- Relate ev(p) to evalSum43' via scaling by 3^{d-1}
  have h_ev_p_scaled : (evalSum43' d FW : ℚ) = (3 : ℚ) ^ (d - 1) * ev p := by
    simp only [evalSum43', ev, Polynomial.coe_eval₂RingHom, p, balancePoly]
    simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
    rw [Finset.mul_sum]; push_cast
    apply Finset.sum_congr rfl; intro r _
    have hr_le : (r : ℕ) ≤ d - 1 := by omega
    have h3_ne : (3 : ℚ) ≠ 0 := by positivity
    have h_denom : (3 : ℚ) ^ (r : ℕ) ≠ 0 := pow_ne_zero _ h3_ne
    have heq : (d - 1 : ℕ) = (r : ℕ) + (d - 1 - (r : ℕ)) := by omega
    calc (FW r : ℚ) * 4 ^ (r : ℕ) * 3 ^ (d - 1 - (r : ℕ))
        = (FW r : ℚ) * 4 ^ (r : ℕ) * (3 ^ (d - 1) / 3 ^ (r : ℕ)) := by
          congr 1; rw [heq, pow_add]
          field_simp
          congr 1; omega
      _ = (3 : ℚ) ^ (d - 1) * ((FW r : ℚ) * (4 / 3) ^ (r : ℕ)) := by
          rw [div_pow]; ring
  -- Relate ev(Φ_d) · 3^{d-1} to 4^d - 3^d
  have h_ev_cycl_scaled : (3 : ℚ) ^ (d - 1) * ev (Polynomial.cyclotomic d ℤ) =
      ↑((4 : ℤ) ^ d - 3 ^ d) := by
    simp only [ev, Polynomial.coe_eval₂RingHom]
    haveI : Fact (Nat.Prime d) := ⟨hd_prime⟩
    rw [Polynomial.cyclotomic_prime]
    simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [Finset.mul_sum]
    have h3_ne : (3 : ℚ) ≠ 0 := by positivity
    have h_term : ∀ i ∈ Finset.range d, (3 : ℚ) ^ (d - 1) * (4 / 3) ^ i =
        (4 : ℚ) ^ i * 3 ^ (d - 1 - i) := fun i hi => by
      rw [Finset.mem_range] at hi; rw [div_pow]
      field_simp [pow_ne_zero i h3_ne]; rw [← pow_add]; congr 1; omega
    rw [show ∑ i ∈ Finset.range d, (3 : ℚ) ^ (d - 1) * (4 / 3) ^ i =
            ∑ i ∈ Finset.range d, (4 : ℚ) ^ i * 3 ^ (d - 1 - i) from
          Finset.sum_congr rfl h_term]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    exact_mod_cast geom_sum_43_bridge d hd_pos
  -- Combine: evalSum43' = (4^d - 3^d) · ev(h)
  have h_key : (evalSum43' d FW : ℚ) = ↑((4 : ℤ) ^ d - 3 ^ d) * ev h := by
    rw [h_ev_p_scaled, hev_p_eq, ← mul_assoc, h_ev_cycl_scaled]
  -- Extract integer divisibility by clearing 3^{d-1} from ev(h)
  -- ev(h) must be rational, and evalSum43' is an integer, so ev(h) = k/1 for some k ∈ ℤ
  suffices h_suff : ∃ k : ℤ, ev h = ↑k by
    obtain ⟨k, hk⟩ := h_suff
    refine ⟨k, ?_⟩
    have : (evalSum43' d FW : ℚ) = ↑(((4 : ℤ) ^ d - 3 ^ d) * k) := by
      rw [h_key, hk]; push_cast; ring
    exact_mod_cast this
  -- Show ev(h) ∈ ℤ by 3-adic clearing
  set deg := h.natDegree
  have h_scaled : ∃ m : ℤ, (3 : ℚ) ^ deg * ev h = ↑m := by
    simp only [ev, Polynomial.coe_eval₂RingHom]
    rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℚ) (show h.natDegree < deg.succ by omega)]
    rw [Finset.mul_sum]
    refine ⟨∑ i ∈ Finset.range deg.succ, h.coeff i * 4 ^ i * 3 ^ (deg - i), ?_⟩
    push_cast; congr 1; ext i
    simp only [Int.coe_castRingHom]
    by_cases hi : i ≤ deg
    · rw [div_pow]; field_simp [pow_ne_zero i (show (3:ℚ) ≠ 0 by positivity)]
      rw [show (3 : ℚ) ^ deg = 3 ^ i * 3 ^ (deg - i) from by rw [← pow_add]; congr 1; omega]; ring
    · push_neg at hi
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  obtain ⟨m, hm⟩ := h_scaled
  -- From evalSum43' · 3^deg = (4^d-3^d) · m, and 3 ∤ (4^d-3^d), conclude 3^deg | m
  have h_eq_Z : evalSum43' d FW * (3 : ℤ) ^ deg = ((4 : ℤ) ^ d - 3 ^ d) * m := by
    apply Int.cast_injective (α := ℚ); push_cast
    rw [show (evalSum43' d FW : ℚ) * 3 ^ deg = ↑((4 : ℤ) ^ d - 3 ^ d) * ((3 : ℚ) ^ deg * ev h) from
      by rw [h_key]; ring, hm]; push_cast; ring
  have h_not_dvd_3 : ¬ (3 : ℤ) ∣ ((4 : ℤ) ^ d - 3 ^ d) := by
    have h_mod : (4 : ℤ) ^ d - 3 ^ d ≡ 1 [ZMOD 3] := by
      have := ((show (4 : ℤ) ≡ 1 [ZMOD 3] from by decide).pow d).sub
        ((show (3 : ℤ) ≡ 0 [ZMOD 3] from by decide).pow d)
      simp [one_pow, zero_pow (by omega : d ≠ 0), sub_zero] at this; exact this
    rw [Int.ModEq] at h_mod; intro h_dvd
    have := Int.emod_eq_zero_of_dvd h_dvd; omega
  have h3_prime : Nat.Prime (3 : ℤ).natAbs := by decide
  -- By induction on deg: 3^deg | m using (4^d-3^d) coprime to 3
  have h_pow_dvd : ∀ (d' : ℕ) (m' : ℤ),
      (∃ E : ℤ, E * (3 : ℤ) ^ d' = ((4 : ℤ) ^ d - 3 ^ d) * m') → (3 : ℤ) ^ d' ∣ m' := by
    intro d'; induction d' with
    | zero => intro m' _; simp
    | succ n ih =>
      intro m' ⟨E, hE⟩
      have hp_dvd_prod : (3 : ℤ) ∣ ((4 : ℤ) ^ d - 3 ^ d) * m' := by
        rw [pow_succ'] at hE; exact ⟨E * 3 ^ n, by linarith⟩
      have hp_prime_int : Prime (3 : ℤ) := Iff.mpr Int.prime_iff_natAbs_prime h3_prime
      have hp_dvd_m' : (3 : ℤ) ∣ m' :=
        (hp_prime_int.dvd_or_dvd hp_dvd_prod).resolve_left h_not_dvd_3
      obtain ⟨m'', rfl⟩ := hp_dvd_m'
      rw [pow_succ']
      exact mul_dvd_mul_left 3 (ih m'' ⟨E, mul_left_cancel₀ (show (3:ℤ) ≠ 0 by omega) (by
        rw [pow_succ] at hE; linarith)⟩)
  obtain ⟨k, hk⟩ := h_pow_dvd deg m ⟨evalSum43' d FW, h_eq_Z⟩
  exact ⟨k, mul_left_cancel₀ (show (3 : ℚ) ^ deg ≠ 0 from pow_ne_zero deg (by positivity))
    (by rw [hm, hk]; push_cast; ring)⟩

/-- **Combined rigidity (prime case)**: for prime d, (4-3ζ) | B in O_K
    with all FW ≤ N < 4 ⟹ all FW equal. -/
theorem folded_weights_all_equal_prime [NeZero d] (hd_prime : Nat.Prime d)
    (FW : Fin d → ℕ) (N : ℕ) (hN : N < 4)
    (h_bdd : ∀ r : Fin d, FW r ≤ N)
    (h_OKD_dvd : fourSubThreeO d ∣ balanceSumO d FW) :
    ∀ r s : Fin d, FW r = FW s := by
  have h_dvd := divisibility_transfer_from_OKD_prime d hd_prime FW h_OKD_dvd
  exact folded_weights_all_equal_from_int_dvd d (Nat.Prime.pos hd_prime) FW N hN h_bdd h_dvd

end Collatz.CyclotomicBridge
