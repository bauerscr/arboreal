import DressedFRD.Norm

/-!
# The standard decomposition (`def:std`, `def:E`, `lem:std`(a),(b))

A standard decomposition is given by real symbols `C k` (`k = 1, …, N`). We write
`Cle j = ∑_{k ≤ j} C_k`, `A = λ + m²` and `ê_j = A · Cle j`.

The main theorem uses only the following consequences of `def:std`:
* (S1) `∑_{k=1}^N Ĉ_k = (λ + m²)^{-1}`, (S2) `Ĉ_k ≥ 0`, (S3) `rng C_k < L^k/2` for `k < N`
  (the structure `StdHyp`);
* `lem:std`(e), in the form `‖Cle_j (1 - E_j)‖_{(j)} ≤ c₂` (`StdLoc`).
`lem:std`(c),(d),(e) are derived from (S4),(S5) in `DressedFRD.StdBounds`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann

variable {d n : ℕ} [NeZero n]

/-- The symbol of `A = -Δ + m²`. -/
def Asym (msq : ℝ) : Sym d n := fun m => ((lam m + msq : ℝ) : ℂ)

/-- Real symbols as complex symbols. -/
def ofR (f : Torus d n → ℝ) : Sym d n := fun m => (f m : ℂ)

/-- `C_{≤j} = ∑_{k=1}^j C_k`. -/
def Cle (C : ℕ → Torus d n → ℝ) (j : ℕ) : Sym d n := ∑ k ∈ Icc 1 j, ofR (C k)

/-- `C_{>j} = ∑_{k=j+1}^N C_k`. -/
def Cgt (C : ℕ → Torus d n → ℝ) (N j : ℕ) : Sym d n := ∑ k ∈ Ioc j N, ofR (C k)

/-- `ê_j = (λ + m²) C_{≤j}`. -/
def Ehat (msq : ℝ) (C : ℕ → Torus d n → ℝ) (j : ℕ) : Sym d n := Asym msq * Cle C j

/-- (S1)–(S3) of `def:std`. -/
structure StdHyp (L N : ℕ) (msq : ℝ) (C : ℕ → Torus d n → ℝ) : Prop where
  msq_pos : 0 < msq
  nonneg : ∀ k m, 0 ≤ C k m
  sum_eq : ∀ m, ∑ k ∈ Icc 1 N, C k m = (lam m + msq)⁻¹
  range : ∀ k, 1 ≤ k → k < N → 2 * rng (ofR (C k)) < L ^ k

/-- `lem:std`(e) in norm form. -/
def StdLoc (L N q : ℕ) (msq c₂ : ℝ) (C : ℕ → Torus d n → ℝ) : Prop :=
  ∀ j < N, snorm (L : ℝ) q j (Cle C j * (1 - Ehat msq C j)) ≤ c₂

variable {L N : ℕ} {msq : ℝ} {C : ℕ → Torus d n → ℝ}

theorem lam_add_pos (h : StdHyp L N msq C) (m : Torus d n) : 0 < lam m + msq :=
  add_pos_of_nonneg_of_pos (lam_nonneg' m) h.msq_pos

theorem Cle_apply (C : ℕ → Torus d n → ℝ) (j : ℕ) (m : Torus d n) :
    Cle C j m = ((∑ k ∈ Icc 1 j, C k m : ℝ) : ℂ) := by
  simp [Cle, ofR, Finset.sum_apply]

theorem Cgt_apply (C : ℕ → Torus d n → ℝ) (N j : ℕ) (m : Torus d n) :
    Cgt C N j m = ((∑ k ∈ Ioc j N, C k m : ℝ) : ℂ) := by
  simp [Cgt, ofR, Finset.sum_apply]

/-- The real value of `ê_j`. -/
def ereal (msq : ℝ) (C : ℕ → Torus d n → ℝ) (j : ℕ) (m : Torus d n) : ℝ :=
  (lam m + msq) * ∑ k ∈ Icc 1 j, C k m

theorem Ehat_apply (msq : ℝ) (C : ℕ → Torus d n → ℝ) (j : ℕ) (m : Torus d n) :
    Ehat msq C j m = (ereal msq C j m : ℂ) := by
  simp [Ehat, Asym, Cle_apply, ereal]

theorem sum_Icc_le_N (h : StdHyp L N msq C) {j : ℕ} (hj : j ≤ N) (m : Torus d n) :
    ∑ k ∈ Icc 1 j, C k m ≤ ∑ k ∈ Icc 1 N, C k m :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hj) fun k _ _ => h.nonneg k m

/-- `lem:std`(a): `0 ≤ ê_j ≤ 1`. -/
theorem ereal_nonneg (h : StdHyp L N msq C) (j : ℕ) (m : Torus d n) : 0 ≤ ereal msq C j m :=
  mul_nonneg (lam_add_pos h m).le (sum_nonneg fun k _ => h.nonneg k m)

theorem ereal_le_one (h : StdHyp L N msq C) {j : ℕ} (hj : j ≤ N) (m : Torus d n) :
    ereal msq C j m ≤ 1 := by
  unfold ereal
  have hp := lam_add_pos h m
  calc (lam m + msq) * ∑ k ∈ Icc 1 j, C k m ≤ (lam m + msq) * ∑ k ∈ Icc 1 N, C k m :=
        mul_le_mul_of_nonneg_left (sum_Icc_le_N h hj m) hp.le
    _ = 1 := by rw [h.sum_eq m, mul_inv_cancel₀ hp.ne']

theorem norm_Ehat_le (h : StdHyp L N msq C) {j : ℕ} (hj : j ≤ N) (m : Torus d n) :
    ‖Ehat msq C j m‖ ≤ 1 := by
  rw [Ehat_apply, Complex.norm_real, Real.norm_of_nonneg (ereal_nonneg h j m)]
  exact ereal_le_one h hj m

theorem norm_one_sub_Ehat_le (h : StdHyp L N msq C) {j : ℕ} (hj : j ≤ N) (m : Torus d n) :
    ‖(1 - Ehat msq C j) m‖ ≤ 1 := by
  rw [Pi.sub_apply, Pi.one_apply, Ehat_apply, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_of_nonneg (by linarith [ereal_le_one h hj m])]
  linarith [ereal_nonneg h j m]

/-- `A (C_{≤j} + C_{>j}) = 1`. -/
theorem Cle_add_Cgt (h : StdHyp L N msq C) {j : ℕ} (hj : j ≤ N) :
    Asym msq * (Cle C j + Cgt C N j) = (1 : Sym d n) := by
  funext m
  have hs : ∑ k ∈ Icc 1 j, C k m + ∑ k ∈ Ioc j N, C k m = ∑ k ∈ Icc 1 N, C k m := by
    have hU : Icc 1 N = Icc 1 j ∪ Ioc j N := by
      ext k; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    rw [hU, sum_union (disjoint_left.2 fun k h1 h2 => by
      simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  simp only [Pi.mul_apply, Pi.add_apply, Asym, Cle_apply, Cgt_apply, Pi.one_apply]
  rw [← Complex.ofReal_add, hs, h.sum_eq m, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (lam_add_pos h m).ne', Complex.ofReal_one]

/-- `A C_{>j} = 1 - E_j`. -/
theorem A_Cgt (h : StdHyp L N msq C) {j : ℕ} (hj : j ≤ N) :
    Asym msq * Cgt C N j = 1 - Ehat msq C j := by
  have := Cle_add_Cgt h hj
  rw [mul_add] at this
  rw [Ehat, ← this]; ring

/-! ### Ranges (`lem:std`(b)) -/

theorem rng_Asym_le (msq : ℝ) : rng (Asym msq : Sym d n) ≤ 1 := by
  have : (Asym msq : Sym d n) = (fun m => (lam m : ℂ)) + fun _ => (msq : ℂ) := by
    funext m; simp [Asym]
  rw [this]
  refine (rng_add_le _ _).trans ?_
  rw [rng_const]
  exact max_le rng_lam_le (Nat.zero_le _)

theorem two_rng_Cle (h : StdHyp L N msq C) (hL : 1 ≤ L) {j : ℕ} (hj : j < N) :
    2 * rng (Cle C j) + 1 ≤ L ^ j := by
  have hpos : 1 ≤ L ^ j := Nat.one_le_pow _ _ hL
  by_cases hj0 : j = 0
  · subst hj0
    have : Cle C 0 = (0 : Sym d n) := by simp [Cle]
    rw [this, show (0 : Sym d n) = fun _ => (0 : ℂ) from rfl, rng_const]; simp
  have key : rng (Cle C j) ≤ (L ^ j - 1) / 2 := by
    refine rng_sum_le _ _ fun k hk => ?_
    simp only [mem_Icc] at hk
    have h1 := h.range k hk.1 (by omega)
    have h2 : L ^ k ≤ L ^ j := Nat.pow_le_pow_right hL hk.2
    omega
  omega

theorem two_rng_Ehat (h : StdHyp L N msq C) (hL : 1 ≤ L) {j : ℕ} (hj : j < N) :
    2 * rng (Ehat msq C j) ≤ L ^ j + 1 := by
  have := two_rng_Cle h hL hj
  have h1 := rng_mul_le (Asym msq : Sym d n) (Cle C j)
  have h2 := rng_Asym_le (d := d) (n := n) msq
  unfold Ehat; omega

theorem two_rng_one_sub_Ehat (h : StdHyp L N msq C) (hL : 1 ≤ L) {j : ℕ} (hj : j < N) :
    2 * rng (1 - Ehat msq C j) ≤ L ^ j + 1 := by
  have h1 := rng_sub_le (1 : Sym d n) (Ehat msq C j)
  have h0 : rng (1 : Sym d n) = 0 := rng_const 1
  have := two_rng_Ehat h hL hj
  omega

end

end DressedFRD
