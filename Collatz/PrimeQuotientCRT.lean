/-
  PrimeQuotientCRT.lean — Prime-quotient CRT decomposition infrastructure
  =========================================================================

  For m = q * t with q prime, decomposes weight sequences into t "slices"
  of length q via `sliceFW`. Establishes periodicity mod (m/q) as the
  combinatorial observable: a nonconstant weight sequence that is periodic
  at every prime quotient forces a contradiction via CRT.

  Key results:
  - `sliceFW`: extracts the s-th slice (residue class mod t) of a Fin m → ℕ
  - `periodic_mod`: shift-periodicity of Fin m → ℕ by period t
  - `gcdList_primeQuotients_eq_one_of_squarefree`: gcd of all m/q is 1 for squarefree m
  - `exists_prime_not_periodic_of_nonconst`: a nonconstant function on Fin m
    cannot be periodic at every prime quotient simultaneously
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Collatz.PrimeQuotientCRT

open scoped BigOperators

variable {α : Type*}

/-- Slice coefficients by a fixed residue class mod `t` when `m = q * t`.
This preserves the original coefficient alphabet (no folding). -/
def sliceFW (m q t : ℕ) (hm : m = q * t) (s : Fin t) (FW : Fin m → ℕ) : Fin q → ℕ :=
  fun r =>
    let idx : ℕ := s.val + t * r.val
    have hidx : idx < m := by
      have h1 : s.val + t * r.val < t + t * r.val :=
        Nat.add_lt_add_right s.isLt (t * r.val)
      have h2 : t + t * r.val = t * (r.val + 1) := by
        calc
          t + t * r.val = t * r.val + t := by ac_rfl
          _ = t * r.val + t * 1 := by simp
          _ = t * (r.val + 1) := by
            simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h3 : r.val + 1 ≤ q := Nat.succ_le_iff.mpr r.isLt
      have h4 : t * (r.val + 1) ≤ t * q := Nat.mul_le_mul_left t h3
      have hlt : s.val + t * r.val < t * q := by
        exact lt_of_lt_of_le (by simpa [h2] using h1) (by simpa [h2] using h4)
      simpa [hm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
    FW ⟨idx, hidx⟩

/-- Shift-periodicity on `ZMod m`. -/
def periodic_add (m : ℕ) (a : ZMod m) (f : ZMod m → α) : Prop :=
  ∀ x, f (x + a) = f x

private lemma periodic_add_nsmul {m : ℕ} {a : ZMod m} {f : ZMod m → α}
    (h : periodic_add m a f) : ∀ n : ℕ, ∀ x, f (x + n • a) = f x := by
  intro n x
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h' := h (x + n • a)
      calc
        f (x + (n + 1) • a) = f ((x + n • a) + a) := by
          rw [succ_nsmul]
          ac_rfl
        _ = f (x + n • a) := by
          simpa [add_assoc] using h'
        _ = f x := ih

private lemma periodic_add_zsmul {m : ℕ} {a : ZMod m} {f : ZMod m → α}
    (h : periodic_add m a f) : ∀ k : ℤ, ∀ x, f (x + k • a) = f x := by
  intro k x
  cases k with
  | ofNat n =>
      simpa using (periodic_add_nsmul (a := a) h n x)
  | negSucc n =>
      have h_pos : ∀ x, f (x + (n + 1) • a) = f x := by
        intro x'
        simpa using (periodic_add_nsmul (a := a) h (n + 1) x')
      have h_neg : ∀ x, f (x + -((n + 1) • a)) = f x := by
        intro x'
        have h' := h_pos (x' - (n + 1) • a)
        have h'' : f x' = f (x' - (n + 1) • a) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
        simpa [sub_eq_add_neg] using h''.symm
      rw [negSucc_zsmul]
      simpa using h_neg x

/-- If a function is shift-periodic for two periods, it is shift-periodic for their gcd. -/
theorem periodic_add_gcd {m : ℕ} {f : ZMod m → α} {t₁ t₂ : ℕ}
    (h₁ : periodic_add m (t₁ : ZMod m) f)
    (h₂ : periodic_add m (t₂ : ZMod m) f) :
    periodic_add m (Nat.gcd t₁ t₂ : ZMod m) f := by
  classical
  have hbez : (Nat.gcd t₁ t₂ : ℤ) = t₁ * Nat.gcdA t₁ t₂ + t₂ * Nat.gcdB t₁ t₂ :=
    Nat.gcd_eq_gcd_ab t₁ t₂
  have hbez' :
      (Nat.gcd t₁ t₂ : ZMod m) =
        (Nat.gcdA t₁ t₂ : ℤ) • (t₁ : ZMod m) +
        (Nat.gcdB t₁ t₂ : ℤ) • (t₂ : ZMod m) := by
    have hbez_cast := congrArg (fun z : ℤ => (z : ZMod m)) hbez
    simpa [zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hbez_cast
  intro x
  have h₁z : ∀ x, f (x + (Nat.gcdA t₁ t₂ : ℤ) • (t₁ : ZMod m)) = f x :=
    fun x' => periodic_add_zsmul (a := (t₁ : ZMod m)) h₁ (Nat.gcdA t₁ t₂) x'
  have h₂z : ∀ x, f (x + (Nat.gcdB t₁ t₂ : ℤ) • (t₂ : ZMod m)) = f x :=
    fun x' => periodic_add_zsmul (a := (t₂ : ZMod m)) h₂ (Nat.gcdB t₁ t₂) x'
  calc
    f (x + (Nat.gcd t₁ t₂ : ZMod m)) =
        f (x + ((Nat.gcdA t₁ t₂ : ℤ) • (t₁ : ZMod m) +
          (Nat.gcdB t₁ t₂ : ℤ) • (t₂ : ZMod m))) := by
          simpa [hbez']
    _ = f ((x + (Nat.gcdA t₁ t₂ : ℤ) • (t₁ : ZMod m)) +
          (Nat.gcdB t₁ t₂ : ℤ) • (t₂ : ZMod m)) := by
          ac_rfl
    _ = f (x + (Nat.gcdA t₁ t₂ : ℤ) • (t₁ : ZMod m)) := by
          simpa [add_assoc] using h₂z (x + (Nat.gcdA t₁ t₂ : ℤ) • (t₁ : ZMod m))
    _ = f x := h₁z x

/-- The list of prime-quotient periods `m / p` for `p ∈ primeFactorsList m`. -/
def primeQuotients (m : ℕ) : List ℕ :=
  (Nat.primeFactorsList m).map (fun p => m / p)

/-- GCD over a list (recursive). -/
def gcdList : List ℕ → ℕ
  | [] => 0
  | t :: ts => Nat.gcd t (gcdList ts)

lemma gcdList_dvd_of_mem : ∀ {L : List ℕ} {t : ℕ}, t ∈ L → gcdList L ∣ t := by
  intro L t ht
  induction L with
  | nil =>
      cases ht
  | cons a L ih =>
      simp [gcdList] at ht
      rcases ht with rfl | ht
      · exact Nat.gcd_dvd_left _ _
      · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (ih ht)

lemma primeQuotients_nonempty {m : ℕ} (hm1 : 1 < m) : primeQuotients m ≠ [] := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hm1)
  have hq_mem : q ∈ Nat.primeFactorsList m := by
    exact (Nat.mem_primeFactorsList hm0).2 ⟨hq_prime, hq_dvd⟩
  intro hnil
  have hmem : m / q ∈ primeQuotients m := by
    apply List.mem_map.2
    exact ⟨q, hq_mem, rfl⟩
  have : m / q ∈ ([] : List ℕ) := by
    simpa [hnil] using hmem
  simpa using this

theorem gcdList_primeQuotients_eq_one_of_squarefree {m : ℕ}
    (hm1 : 1 < m) (hsf : Squarefree m) :
    gcdList (primeQuotients m) = 1 := by
  classical
  by_contra hg1
  set g : ℕ := gcdList (primeQuotients m)
  have h_g_nonzero : g ≠ 0 := by
    have hm0 : m ≠ 0 := by omega
    obtain ⟨q0, hq0_prime, hq0_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hm1)
    have hq0_mem : q0 ∈ Nat.primeFactorsList m := by
      exact (Nat.mem_primeFactorsList hm0).2 ⟨hq0_prime, hq0_dvd⟩
    have hq0_in : m / q0 ∈ primeQuotients m := by
      apply List.mem_map.2
      exact ⟨q0, hq0_mem, rfl⟩
    have hg_dvd : g ∣ m / q0 := gcdList_dvd_of_mem (L := primeQuotients m) hq0_in
    have hm_pos : 0 < m := by omega
    have h_le : q0 ≤ m := Nat.le_of_dvd hm_pos hq0_dvd
    have h_mdiv_pos : 0 < m / q0 := Nat.div_pos h_le hq0_prime.pos
    intro hg0
    have : (0 : ℕ) ∣ m / q0 := by simpa [g, hg0] using hg_dvd
    have : m / q0 = 0 := (zero_dvd_iff.mp this)
    exact (ne_of_gt h_mdiv_pos) this
  obtain ⟨p, hp_prime, hp_dvd_g⟩ := Nat.exists_prime_and_dvd (by simpa [g] using hg1)
  have h_g_dvd_all :
      ∀ q : ℕ, q ∈ Nat.primeFactorsList m → g ∣ m / q := by
    intro q hq_mem
    have : m / q ∈ primeQuotients m := by
      apply List.mem_map.2
      exact ⟨q, hq_mem, rfl⟩
    exact gcdList_dvd_of_mem (L := primeQuotients m) this
  have hm0 : m ≠ 0 := by omega
  obtain ⟨q0, hq0_prime, hq0_dvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hm1)
  have hq0_mem : q0 ∈ Nat.primeFactorsList m := by
    exact (Nat.mem_primeFactorsList hm0).2 ⟨hq0_prime, hq0_dvd⟩
  have hp_dvd_m : p ∣ m := by
    have hp_dvd_mdiv : p ∣ m / q0 := Nat.dvd_trans hp_dvd_g (h_g_dvd_all q0 hq0_mem)
    exact Nat.dvd_trans hp_dvd_mdiv (Nat.div_dvd_of_dvd hq0_dvd)
  have hp_mem : p ∈ Nat.primeFactorsList m := by
    exact (Nat.mem_primeFactorsList hm0).2 ⟨hp_prime, hp_dvd_m⟩
  have hp_dvd_mdivp : p ∣ m / p := Nat.dvd_trans hp_dvd_g (h_g_dvd_all p hp_mem)
  have hpp_dvd_m : p * p ∣ m := by
    rcases hp_dvd_mdivp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      m = p * (m / p) := by
        exact (Nat.mul_div_cancel' hp_dvd_m).symm
      _ = p * (p * k) := by simp [hk]
      _ = p * p * k := by ac_rfl
  have h_sf := (Nat.squarefree_iff_prime_squarefree).1 hsf
  exact (h_sf p hp_prime) hpp_dvd_m

lemma periodic_add_gcdList {m : ℕ} {f : ZMod m → α} :
    ∀ L : List ℕ,
      (∀ t ∈ L, periodic_add m (t : ZMod m) f) →
      periodic_add m (gcdList L : ZMod m) f := by
  intro L
  induction L with
  | nil =>
      intro _ x
      simp [gcdList, periodic_add]
  | cons t ts ih =>
      intro h_per
      have ht : periodic_add m (t : ZMod m) f := h_per t (by simp)
      have hts : periodic_add m (gcdList ts : ZMod m) f := by
        apply ih
        intro u hu
        exact h_per u (by simp [hu])
      simpa [gcdList] using (periodic_add_gcd (m := m) (f := f) (t₁ := t) (t₂ := gcdList ts) ht hts)

/-- If all prime-quotient periods are present and their gcd is 1, then the function is constant. -/
theorem periodic_add_const_of_prime_quotients {m : ℕ} [NeZero m] {f : ZMod m → α}
    (h_per : ∀ q : ℕ, Nat.Prime q → q ∣ m → periodic_add m (m / q : ZMod m) f)
    (h_gcd : gcdList (primeQuotients m) = 1) :
    ∀ x y : ZMod m, f x = f y := by
  have h_periodic :
      periodic_add m (gcdList (primeQuotients m) : ZMod m) f := by
    apply periodic_add_gcdList (m := m) (f := f) (L := primeQuotients m)
    intro t ht
    rcases List.mem_map.1 ht with ⟨p, hp, rfl⟩
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp
    have hp_dvd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    exact h_per p hp_prime hp_dvd
  have h1 : periodic_add m (1 : ZMod m) f := by
    simpa [h_gcd] using h_periodic
  have h1n : ∀ n : ℕ, f (n : ZMod m) = f 0 := by
    intro n
    simpa using (periodic_add_nsmul (a := (1 : ZMod m)) h1 n (0 : ZMod m))
  intro x y
  have hx : f x = f 0 := by
    simpa [ZMod.natCast_zmod_val] using h1n x.val
  have hy : f y = f 0 := by
    simpa [ZMod.natCast_zmod_val] using h1n y.val
  simpa [hx, hy]

/-- A weight function on `Fin m` is `t`-periodic if it depends only on `j % t`. -/
def periodic_mod (m t : ℕ) (FW : Fin m → ℕ) : Prop :=
  ∀ i j : Fin m, i.val % t = j.val % t → FW i = FW j

private def liftFW (m : ℕ) [NeZero m] (FW : Fin m → ℕ) : ZMod m → ℕ :=
  fun x => FW ⟨x.val, x.val_lt⟩

private lemma periodic_add_of_periodic_mod (m t : ℕ) [NeZero m]
    (FW : Fin m → ℕ) (ht : t ∣ m) (h_per : periodic_mod m t FW) :
    periodic_add m (t : ZMod m) (liftFW m FW) := by
  intro x
  let i : Fin m := ⟨x.val, x.val_lt⟩
  let j : Fin m := ⟨(x + (t : ZMod m)).val, (x + (t : ZMod m)).val_lt⟩
  have hmod : i.val % t = j.val % t := by
    have hval : (x + (t : ZMod m)).val = (x.val + t) % m := by
      simpa using (ZMod.val_add x (t : ZMod m))
    have hmod1 : ((x.val + t) % m) % t = (x.val + t) % t := by
      simpa using (Nat.mod_mod_of_dvd (x.val + t) ht)
    have hmod2 : (x.val + t) % t = x.val % t := by
      calc
        (x.val + t) % t = (x.val % t + t % t) % t := by
          simpa [Nat.add_mod]
        _ = x.val % t := by simp
    simpa [i, j, hval, hmod1, hmod2]
  have h := h_per i j hmod
  simpa [liftFW, i, j] using h.symm

/-- Nonconstant weights force a prime quotient with non-periodicity (when the gcd condition holds). -/
theorem exists_prime_not_periodic_of_nonconst
    (m : ℕ) [NeZero m]
    (FW : Fin m → ℕ)
    (h_nonconst : ∃ i j : Fin m, FW i ≠ FW j)
    (h_gcd : gcdList (primeQuotients m) = 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧ ¬ periodic_mod m (m / q) FW := by
  by_contra h_all
  push_neg at h_all
  let FWz : ZMod m → ℕ := liftFW m FW
  have h_per :
      ∀ q : ℕ, Nat.Prime q → q ∣ m → periodic_add m (m / q : ZMod m) FWz := by
    intro q hq hq_dvd
    have hper : periodic_mod m (m / q) FW := h_all q hq hq_dvd
    have ht : m / q ∣ m := Nat.div_dvd_of_dvd hq_dvd
    exact periodic_add_of_periodic_mod m (m / q) FW ht hper
  have hconst : ∀ x y : ZMod m, FWz x = FWz y :=
    periodic_add_const_of_prime_quotients (m := m) (f := FWz) h_per h_gcd
  have hFWconst : ∀ i j : Fin m, FW i = FW j := by
    intro i j
    have h := hconst (i.val : ZMod m) (j.val : ZMod m)
    have hi : (⟨i.val % m, Nat.mod_lt _ (NeZero.pos _)⟩ : Fin m) = i := by
      apply Fin.ext
      simpa [Nat.mod_eq_of_lt i.isLt]
    have hj : (⟨j.val % m, Nat.mod_lt _ (NeZero.pos _)⟩ : Fin m) = j := by
      apply Fin.ext
      simpa [Nat.mod_eq_of_lt j.isLt]
    simpa [FWz, liftFW, hi, hj] using h
  rcases h_nonconst with ⟨i, j, hij⟩
  exact hij (hFWconst i j)

/-- Nonconstant `FW`: either one prime quotient is non-periodic, or all are periodic. -/
theorem exists_prime_nonconstant_slice_or_all_periodic
    (m : ℕ) [NeZero m] (hm : m ≥ 2)
    (FW : Fin m → ℕ)
    (h_nonconst : ∃ i j : Fin m, FW i ≠ FW j) :
    (∃ q : ℕ, Nat.Prime q ∧ q ∣ m ∧ ¬ periodic_mod m (m / q) FW) ∨
    (∀ q : ℕ, Nat.Prime q → q ∣ m → periodic_mod m (m / q) FW) := by
  by_cases h : ∀ q : ℕ, Nat.Prime q → q ∣ m → periodic_mod m (m / q) FW
  · exact Or.inr h
  · left
    push_neg at h
    exact h

private lemma sliceFW_eq_of_index
    (m q t : ℕ) (hm : m = q * t) (FW : Fin m → ℕ)
    (s : Fin t) (r : Fin q)
    (i : Fin m)
    (hi : i.val = s.val + t * r.val) :
    sliceFW m q t hm s FW r = FW i := by
  have hidx : (s.val + t * r.val) < m := by
    have h1 : s.val + t * r.val < t + t * r.val :=
      Nat.add_lt_add_right s.isLt (t * r.val)
    have h2 : t + t * r.val = t * (r.val + 1) := by
      calc
        t + t * r.val = t * r.val + t := by ac_rfl
        _ = t * r.val + t * 1 := by simp
        _ = t * (r.val + 1) := by
          simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h3 : r.val + 1 ≤ q := Nat.succ_le_iff.mpr r.isLt
    have h4 : t * (r.val + 1) ≤ t * q := Nat.mul_le_mul_left t h3
    have hlt : s.val + t * r.val < t * q := by
      exact lt_of_lt_of_le (by simpa [h2] using h1) (by simpa [h2] using h4)
    simpa [hm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
  have h_fin : (⟨s.val + t * r.val, hidx⟩ : Fin m) = i := by
    apply Fin.ext
    simpa [hi]
  simp [sliceFW, h_fin]

private lemma sliceFW_eq_weight_of_mod
    (m q t : ℕ) (hm : m = q * t) (ht : 0 < t)
    (FW : Fin m → ℕ)
    (i : Fin m) :
    let s : Fin t := ⟨i.val % t, Nat.mod_lt _ ht⟩
    let r : Fin q := ⟨i.val / t, by
      have hi : i.val < q * t := by simpa [hm] using i.isLt
      exact (Nat.div_lt_iff_lt_mul ht).2 hi⟩
    sliceFW m q t hm s FW r = FW i := by
  let s : Fin t := ⟨i.val % t, Nat.mod_lt _ ht⟩
  let r : Fin q := ⟨i.val / t, by
    have hi : i.val < q * t := by simpa [hm] using i.isLt
    exact (Nat.div_lt_iff_lt_mul ht).2 hi⟩
  have hi : i.val = s.val + t * r.val := by
    dsimp [s, r]
    have := (Nat.mod_add_div i.val t).symm
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  exact sliceFW_eq_of_index m q t hm FW s r i hi

lemma periodic_mod_of_slice_const
    (m q t : ℕ) (hm : m = q * t) (ht : 0 < t)
    (FW : Fin m → ℕ)
    (h_const :
      ∀ s : Fin t, ∀ r₁ r₂ : Fin q,
        sliceFW m q t hm s FW r₁ = sliceFW m q t hm s FW r₂) :
    periodic_mod m t FW := by
  intro i j hmod
  let s : Fin t := ⟨i.val % t, Nat.mod_lt _ ht⟩
  have hs : s.val = j.val % t := by simpa [s] using hmod
  let r₁ : Fin q := ⟨i.val / t, by
    have hi : i.val < q * t := by simpa [hm] using i.isLt
    exact (Nat.div_lt_iff_lt_mul ht).2 hi⟩
  let r₂ : Fin q := ⟨j.val / t, by
    have hj : j.val < q * t := by simpa [hm] using j.isLt
    exact (Nat.div_lt_iff_lt_mul ht).2 hj⟩
  have h_i : sliceFW m q t hm s FW r₁ = FW i :=
    (sliceFW_eq_weight_of_mod m q t hm ht FW i)
  have h_j : sliceFW m q t hm s FW r₂ = FW j := by
    have hs' : s.val = j.val % t := hs
    have : (⟨j.val % t, Nat.mod_lt _ ht⟩ : Fin t) = s := by
      apply Fin.ext
      simpa [s] using hs'.symm
    simpa [this] using (sliceFW_eq_weight_of_mod m q t hm ht FW j)
  have h_const' := h_const s r₁ r₂
  simpa [h_i, h_j] using h_const'

lemma exists_nontrivial_slice_of_not_periodic
    (m q t : ℕ) (hm : m = q * t) (ht : 0 < t)
    (FW : Fin m → ℕ)
    (h_not_per : ¬ periodic_mod m t FW) :
    ∃ s : Fin t, ∃ r₁ r₂ : Fin q,
      sliceFW m q t hm s FW r₁ ≠ sliceFW m q t hm s FW r₂ := by
  by_contra h_all
  push_neg at h_all
  have h_per : periodic_mod m t FW :=
    periodic_mod_of_slice_const m q t hm ht FW h_all
  exact h_not_per h_per

end Collatz.PrimeQuotientCRT
