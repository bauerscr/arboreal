import DressedFRD.Words

/-!
# The construction of `Γ_j` and `Γ^int_{j+1}` (`thm:main`, Section `sec:proof`)

Given increments `ζ_j`, put `Z_j = ∏_{i<j} (1 + ζ_i)` and `ζ'_j = ζ_j/(1 + ζ_j)`. At time `j`
the remaining covariance is `Γ_j = Z_j^{-1} C_{>j} + ∑_{r ∈ (j,N]} R_{j,r}` (hypothesis
(H_j)), and `ε_j = ê_j - ∑_r Z_j A R_{j,r}`.

The letters (`letV`) are
* `a`: `C_{≤j}` or `-Z_j R_{j,r}`;
* `b`: `1 - ê_j` or `Z_j A R_{j,r}`;
* `c`: `ê_j` or `-Z_j A R_{j,r}`.

Their range bounds (`rbV`, doubled) are `L^j`, `L^j + 2` and `L^r`, `L^r + 2`. The words of
scale `s < N` are collected in `wLow`. The scale-`N` part `wTop` is *defined* as the remainder
of the closed form `wTot = ζ' A^{-1} ε (1-ε)/(1 - ζ'ε)` of the second term of `lem:alg`. So the
splitting `thm:main`(i) is an exact algebraic identity (`split`). The series representation of
`wTop` is only needed for the estimates.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

/-- The data of the construction. -/
structure Data (d n : ℕ) where
  L : ℕ
  N : ℕ
  msq : ℝ
  C : ℕ → Torus d n → ℝ
  ζ : ℕ → ℂ

namespace Data

variable (D : Data d n)

/-- `Z_j = ∏_{i<j} (1 + ζ_i)`. -/
def Z (j : ℕ) : ℂ := ∏ i ∈ range j, (1 + D.ζ i)

/-- `ζ'_j = ζ_j / (1 + ζ_j)`. -/
def zp (j : ℕ) : ℂ := D.ζ j / (1 + D.ζ j)

theorem Z_succ (j : ℕ) : D.Z (j + 1) = D.Z j * (1 + D.ζ j) := by
  simp [Z, prod_range_succ]

/-- The letter values at time `j`, given the tails `R`. -/
def letV (j : ℕ) (R : ℕ → Sym d n) (κ : Fin 3) (ℓ : Option ℕ) : Sym d n :=
  match κ.val, ℓ with
  | 0, none => Cle D.C j
  | 0, some r => -(D.Z j • R r)
  | 1, none => 1 - Ehat D.msq D.C j
  | 1, some r => D.Z j • (Asym D.msq * R r)
  | _, none => Ehat D.msq D.C j
  | _, some r => -(D.Z j • (Asym D.msq * R r))

/-- The (doubled) range bounds of the letters. -/
def rbV (j : ℕ) (κ : Fin 3) (ℓ : Option ℕ) : ℕ :=
  match κ.val, ℓ with
  | 0, none => D.L ^ j
  | 0, some r => D.L ^ r
  | _, none => D.L ^ j + 2
  | _, some r => D.L ^ r + 2

/-- `ε_j = ê_j - ∑_r Z_j A R_{j,r}`. -/
def eps (j : ℕ) (R : ℕ → Sym d n) : Sym d n :=
  Ehat D.msq D.C j - ∑ r ∈ Ioc j D.N, D.Z j • (Asym D.msq * R r)

/-- The sum of the words of length `k + 2` and scale `s`. -/
def wLen (j : ℕ) (R : ℕ → Sym d n) (s k : ℕ) : Sym d n :=
  ∑ w ∈ (words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s),
    wordVal (D.letV j R) w

/-- The words assigned to a scale `s < N`: `ζ' ∑_w ζ'^{n(w)} O_w`. Only lengths `k < L^s` occur. -/
def wLow (j : ℕ) (R : ℕ → Sym d n) (s : ℕ) : Sym d n :=
  ∑ k ∈ range (D.L ^ s), D.zp j ^ (k + 1) • D.wLen j R s k

/-- The closed form `ζ' A^{-1} ε (1 - ε) / (1 - ζ' ε)`. -/
def wTot (j : ℕ) (R : ℕ → Sym d n) : Sym d n := fun m =>
  D.zp j * (Asym D.msq m)⁻¹ * D.eps j R m * (1 - D.eps j R m) / (1 - D.zp j * D.eps j R m)

/-- The words assigned to the last scale `N`: the remainder. -/
def wTop (j : ℕ) (R : ℕ → Sym d n) : Sym d n :=
  D.wTot j R - ∑ s ∈ Ico (j + 1) D.N, D.wLow j R s

/-- The words assigned to scale `s`. -/
def wSc (j : ℕ) (R : ℕ → Sym d n) (s : ℕ) : Sym d n :=
  if s < D.N then D.wLow j R s else D.wTop j R

/-- The tails `R_{j,r}`. -/
def tails : ℕ → ℕ → Sym d n
  | 0 => fun _ => 0
  | j + 1 => fun r =>
      if j + 2 ≤ r ∧ r ≤ D.N then
        (D.Z (j + 1))⁻¹ • (D.Z j • tails j r + D.wSc j (tails j) r)
      else 0

/-- `Γ_j = Z_j^{-1} C_{>j} + ∑_{r ∈ (j,N]} R_{j,r}`. -/
def Gam (j : ℕ) : Sym d n := (D.Z j)⁻¹ • Cgt D.C D.N j + ∑ r ∈ Ioc j D.N, D.tails j r

/-- The absorbed covariance `Γ_j (1 + z_j A Γ_j)^{-1}`, `z_j = ζ_j Z_j`. -/
def absorbed (j : ℕ) : Sym d n := fun m =>
  D.Gam j m / (1 + D.ζ j * D.Z j * Asym D.msq m * D.Gam j m)

/-- `Γ^int_{j+1}`. -/
def Gint (j : ℕ) : Sym d n :=
  if j + 1 < D.N then
    (D.Z (j + 1))⁻¹ • (ofR (D.C (j + 1)) + D.Z j • D.tails j (j + 1) + D.wSc j (D.tails j) (j + 1))
  else D.absorbed j

/-! ### The exact splitting -/

theorem sum_letV_a (j : ℕ) (R : ℕ → Sym d n) :
    ∑ ℓ ∈ alph j D.N, D.letV j R 0 ℓ = Cle D.C j - ∑ r ∈ Ioc j D.N, D.Z j • R r := by
  simp [alph, letV, sum_insert, sub_eq_add_neg, sum_neg_distrib]

theorem sum_letV_b (j : ℕ) (R : ℕ → Sym d n) :
    ∑ ℓ ∈ alph j D.N, D.letV j R 1 ℓ = 1 - D.eps j R := by
  simp [alph, letV, sum_insert, eps]; abel

theorem sum_letV_c (j : ℕ) (R : ℕ → Sym d n) :
    ∑ ℓ ∈ alph j D.N, D.letV j R 2 ℓ = D.eps j R := by
  simp [alph, letV, sum_insert, eps, sub_eq_add_neg, sum_neg_distrib]

theorem sum_wSc (j : ℕ) (R : ℕ → Sym d n) (hj : j + 1 ≤ D.N) :
    ∑ s ∈ Icc (j + 1) D.N, D.wSc j R s = D.wTot j R := by
  have hU : Icc (j + 1) D.N = insert D.N (Ico (j + 1) D.N) := by
    ext s; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  rw [hU, sum_insert (by simp)]
  have : ∑ s ∈ Ico (j + 1) D.N, D.wSc j R s = ∑ s ∈ Ico (j + 1) D.N, D.wLow j R s :=
    sum_congr rfl fun s hs => by simp only [wSc, if_pos (mem_Ico.1 hs).2]
  rw [this, wSc, if_neg (lt_irrefl _), wTop]; abel

variable {D}

theorem Asym_ne_zero (h : StdHyp D.L D.N D.msq D.C) (m : Torus d n) : Asym D.msq m ≠ (0 : ℂ) := by
  simp only [Asym]; exact_mod_cast (lam_add_pos h m).ne'

theorem eps_apply (j : ℕ) (R : ℕ → Sym d n) (m : Torus d n) :
    D.eps j R m = Ehat D.msq D.C j m - D.Z j * Asym D.msq m * (∑ r ∈ Ioc j D.N, R r) m := by
  simp only [eps, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Finset.mul_sum]
  congr 1
  exact sum_congr rfl fun r _ => by ring

/-- `Z_j A Γ_j = 1 - ε_j`. -/
theorem Z_A_Gam (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j ≤ D.N) (hZ : D.Z j ≠ 0)
    (m : Torus d n) :
    D.Z j * Asym D.msq m * D.Gam j m = 1 - D.eps j (D.tails j) m := by
  have hAC := congrFun (A_Cgt h hj) m
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at hAC
  rw [eps_apply]
  simp only [Gam, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, show D.Z j * Asym D.msq m * ((D.Z j)⁻¹ * Cgt D.C D.N j m) =
    Asym D.msq m * Cgt D.C D.N j m by field_simp, hAC]
  ring

/-- The scalar identity behind `lem:alg`. -/
theorem alg_key (Z ζ A ε : ℂ) (hZ : Z ≠ 0) (hζ : 1 + ζ ≠ 0) (hA : A ≠ 0)
    (hd : 1 + ζ - ζ * ε ≠ 0) :
    ((1 - ε) / (Z * A)) / (1 + ζ * Z * A * ((1 - ε) / (Z * A))) =
      (Z * (1 + ζ))⁻¹ * (Z * ((1 - ε) / (Z * A)) +
        ζ / (1 + ζ) * A⁻¹ * ε * (1 - ε) / (1 - ζ / (1 + ζ) * ε)) := by
  have e1 : 1 + ζ * Z * A * ((1 - ε) / (Z * A)) = 1 + ζ - ζ * ε := by
    rw [show ζ * Z * A * ((1 - ε) / (Z * A)) = ζ * (1 - ε) by field_simp]; ring
  have e2 : 1 - ζ / (1 + ζ) * ε = (1 + ζ - ζ * ε) / (1 + ζ) := by
    rw [eq_div_iff hζ, sub_mul, one_mul, div_mul_eq_mul_div, mul_comm, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hζ]
  have e3 : Z * ((1 - ε) / (Z * A)) = (1 - ε) / A := by field_simp
  rw [e1, e2, e3]
  generalize hD : 1 + ζ - ζ * ε = D at hd ⊢
  field_simp
  rw [← hD]
  ring

/-- The closed form of the absorbed covariance (`lem:alg`). -/
theorem absorbed_eq (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j ≤ D.N)
    (hZ : D.Z j ≠ 0) (hζ : 1 + D.ζ j ≠ 0) (m : Torus d n)
    (hden : 1 - D.zp j * D.eps j (D.tails j) m ≠ 0) :
    D.absorbed j m = (D.Z (j + 1))⁻¹ *
      (Cgt D.C D.N j m + D.Z j * (∑ r ∈ Ioc j D.N, D.tails j r) m + D.wTot j (D.tails j) m) := by
  have hA := Asym_ne_zero h m
  have hG := Z_A_Gam h hj hZ m
  have hAC := congrFun (A_Cgt h hj) m
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at hAC
  -- `C_{>j} + Z_j ∑ R = Z_j Γ_j`
  have hc : Cgt D.C D.N j m + D.Z j * (∑ r ∈ Ioc j D.N, D.tails j r) m = D.Z j * D.Gam j m := by
    simp only [Gam, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hGe : D.Gam j m = (1 - D.eps j (D.tails j) m) / (D.Z j * Asym D.msq m) := by
    rw [eq_div_iff (mul_ne_zero hZ hA), ← hG]; ring
  have hden' : 1 + D.ζ j - D.ζ j * D.eps j (D.tails j) m ≠ 0 := by
    have : 1 + D.ζ j - D.ζ j * D.eps j (D.tails j) m =
        (1 + D.ζ j) * (1 - D.zp j * D.eps j (D.tails j) m) := by
      unfold zp; field_simp
    rw [this]; exact mul_ne_zero hζ hden
  rw [hc, Z_succ]
  unfold absorbed wTot zp
  rw [hGe]
  exact alg_key _ _ _ _ hZ hζ hA hden'

/-- The exact splitting `thm:main`(i): `Γ_j (1 + z_j A Γ_j)^{-1} = Γ^int_{j+1} + Γ_{j+1}`. -/
theorem split (h : StdHyp D.L D.N D.msq D.C) {j : ℕ} (hj : j + 1 ≤ D.N)
    (hZ : D.Z j ≠ 0) (hζ : 1 + D.ζ j ≠ 0) (m : Torus d n)
    (hden : 1 - D.zp j * D.eps j (D.tails j) m ≠ 0) :
    D.absorbed j m = D.Gint j m + D.Gam (j + 1) m := by
  by_cases hjN : j + 1 < D.N
  · rw [absorbed_eq h (by omega) hZ hζ m hden, ← sum_wSc D j (D.tails j) hj]
    simp only [Gint, if_pos hjN, Gam]
    have hZ1 : D.Z (j + 1) ≠ 0 := by rw [Z_succ]; exact mul_ne_zero hZ hζ
    -- split the sums at `j + 1`
    have hI : Ioc j D.N = insert (j + 1) (Ioc (j + 1) D.N) := by
      ext r; simp only [mem_Ioc, mem_insert]; omega
    have hIcc : Icc (j + 1) D.N = insert (j + 1) (Ioc (j + 1) D.N) := by
      ext r; simp only [mem_Icc, mem_Ioc, mem_insert]; omega
    have hCgt : Cgt D.C D.N j = ofR (D.C (j + 1)) + Cgt D.C D.N (j + 1) := by
      rw [Cgt, Cgt, hI, sum_insert (by simp)]
    rw [hCgt, hI, hIcc, sum_insert (by simp), sum_insert (by simp)]
    have ht : ∀ r ∈ Ioc (j + 1) D.N, D.tails (j + 1) r =
        (D.Z (j + 1))⁻¹ • (D.Z j • D.tails j r + D.wSc j (D.tails j) r) := by
      intro r hr
      simp only [mem_Ioc] at hr
      simp only [tails, if_pos (⟨by omega, hr.2⟩ : j + 2 ≤ r ∧ r ≤ D.N)]
    rw [sum_congr rfl ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    ring
  · have hjN' : j + 1 = D.N := by omega
    simp only [Gint, if_neg hjN, Gam]
    have h0 : Cgt D.C D.N (j + 1) = 0 := by simp [Cgt, hjN']
    have h1 : Ioc (j + 1) D.N = ∅ := by rw [← hjN', Finset.Ioc_self]
    rw [h0, h1]; simp

end Data

end

end DressedFRD
