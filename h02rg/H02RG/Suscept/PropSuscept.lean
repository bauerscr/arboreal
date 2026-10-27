import Suscept.Bounds

/-!
# Proposition `prop:suscept`: the susceptibility

With `⟨F⟩ = 𝔼_C[Z_0 F] / 𝔼_C[Z_0]` (`e:avgV0`), `C = (-Δ + m²)^{-1}`, `Z_0 = e^{-V_0(Λ)}`:
`∑_{x ∈ Λ_N} ⟨ψ̄_0 ψ_x⟩ = 1/m² - (1/m⁴) ã_{N,N} / (1 + ũ_{N,N})` (`prop_suscept`), and without
normalisation `∑_x 𝔼_C[Z_0 ψ̄_0 ψ_x] = e^{-u_N|Λ|} ((1 + ũ_{N,N})/m² - ã_{N,N}/m⁴)`
(`sum_EC_Z0_psibar_psi`), with `𝔼_C[Z_0] = e^{-u_N|Λ|} (1 + ũ_{N,N})` (`EC_Z0`).

Proof: instead of the generating function with the shift `ψ ↦ ψ + Cσ`, we use Gaussian
integration by parts twice (`sum_omega_psibar_psi`, using `∑_y C_{xy} = m^{-2}`), which expresses
`∑_{x,y} 𝔼_C[Z_0 ψ̄_x ψ_y]` through the constant term and the `ψψ̄`-coefficient of
`Z_{N,N} = 𝔼_C θ Z_0` restricted to constant fields; these are given by `prop_ZNN`.  Translation
invariance of `C` and `V_0(Λ)` gives `∑_x ⟨ψ̄_0 ψ_x⟩ = |Λ|^{-1} ∑_{x,y} ⟨ψ̄_x ψ_y⟩`.
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

variable {d L : ℕ} [NeZero L]

local notation "Rl" N => Rc (Lam d L N)
local notation "PP" N => psiC (Lam d L N) * psibarC (Lam d L N)

/-! ### Translation invariance -/

theorem omega_autAlg {N : ℕ} (E : Lam d L N ≃ Lam d L N) {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : ∀ x y, C (E x) (E y) = C x y) (F : Alg d L N) : omega C (autAlg E F) = omega C F := by
  rw [omega_eq, omega_eq, theta_autAlg, EC_autAlg2 E hC, ε_autAlg]

theorem autAlg_Z0 {N : ℕ} (a : Lam d L N) (V₀ : Vcoup) :
    autAlg (Equiv.addRight a) (Z0 d L N V₀) = Z0 d L N V₀ := by
  have h := AE_gexp (AffAut.transl a) (isNilpotent_VE V₀ (univ : Finset (Lam d L N))).neg
  rw [map_neg, AE_VE (IsGen.transl a), img_univ] at h
  exact congrArg Subtype.val h

/-- `∑_x ⟨ψ̄_0 ψ_x⟩ = |Λ|^{-1} ∑_{x,y} ⟨ψ̄_x ψ_y⟩` (unnormalised). -/
theorem sum_transl {N : ℕ} (hN : 1 ≤ N) {msq : ℝ} (hmsq : 0 < msq) (V₀ : Vcoup) :
    ∑ x : Lam d L N, omega (Cov d L N msq) (Z0 d L N V₀ * (psibar 0 * psi x)) =
      ((Fintype.card (Lam d L N) : ℂ))⁻¹ *
        ∑ x : Lam d L N, ∑ y : Lam d L N,
          omega (Cov d L N msq) (Z0 d L N V₀ * (psibar x * psi y)) := by
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h : ∀ a : Lam d L N, ∑ y : Lam d L N,
      omega (Cov d L N msq) (Z0 d L N V₀ * (psibar a * psi y)) =
      ∑ x : Lam d L N, omega (Cov d L N msq) (Z0 d L N V₀ * (psibar 0 * psi x)) := by
    intro a
    rw [← Equiv.sum_comp (Equiv.addRight a)]
    refine sum_congr rfl fun x _ => ?_
    have := omega_autAlg (Equiv.addRight a) (C := Cov d L N msq)
      (fun x y => Cov_transl hmsq hN x y a) (Z0 d L N V₀ * (psibar 0 * psi x))
    rw [map_mul, map_mul, autAlg_Z0, autAlg_psibar, autAlg_psi] at this
    simpa using this
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-! ### The susceptibility -/

theorem even_ZtNN (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    inv' (ZtNN d L N msq V₀) = ZtNN d L N msq V₀ := by
  rw [ZtNN_eq hd hL hN hmsq hgood V₀]
  exact mem_Ev.1 (ECE (tNN d L N msq • QN) (thetaE ((gexp (-(VE (VN d L N msq V₀)
    (univ : Finset (Lam d L N)) : EvR (Lam d L N))) + KN d L N msq V₀ : EvR (Lam d L N))))).2

theorem ε_P {N : ℕ} : ε (PP N) = 0 := by
  simp [psiC, psibarC]

theorem ε_ZtNN (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    ε (ZtNN d L N msq V₀) = 1 + utN d L N msq V₀ := by
  rw [← ε_Rc, prop_ZNN hd hL hN hmsq hgood V₀, map_sub, map_smul, ε_P, AlgHom.commutes]
  simp

theorem c2_ZtNN (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    c2 (ZtNN d L N msq V₀) = -((Fintype.card (Lam d L N) : ℂ) * atN d L N msq V₀) := by
  rw [← c2_Rc (even_ZtNN hd hL hN hmsq hgood V₀), prop_ZNN hd hL hN hmsq hgood V₀, sub_eq_add_neg,
    c2_add, c2_algebraMap, ← neg_smul, c2_smul, c2_P]
  ring

theorem ZNN_eq_smul {N : ℕ} (msq : ℝ) (V₀ : Vcoup) :
    ZNN d L N msq V₀ =
      Complex.exp (-(uN d L N msq V₀ * Fintype.card (Lam d L N))) • ZtNN d L N msq V₀ := by
  rw [ZtNN, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]

/-- `𝔼_C[Z_0] = ε(Z_{N,N}) = e^{-u_N|Λ|} (1 + ũ_{N,N})`: the constant term of `Z_{N,N}`. -/
theorem EC_Z0 (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    omega (Cov d L N msq) (Z0 d L N V₀) =
      Complex.exp (-(uN d L N msq V₀ * Fintype.card (Lam d L N))) * (1 + utN d L N msq V₀) := by
  rw [omega_eq, ← ZNN, ZNN_eq_smul, map_smul, ε_ZtNN hd hL hN hmsq hgood V₀, smul_eq_mul]

/-- **`prop:suscept`** (unnormalised form):
`∑_x 𝔼_C[Z_0 ψ̄_0 ψ_x] = e^{-u_N|Λ|} ((1 + ũ_{N,N})/m² - ã_{N,N}/m⁴)`. -/
theorem sum_EC_Z0_psibar_psi (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N)
    {msq ℓ₀ : ℝ} (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    ∑ x : Lam d L N, omega (Cov d L N msq) (Z0 d L N V₀ * (psibar 0 * psi x)) =
      Complex.exp (-(uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        ((1 + utN d L N msq V₀) / (msq : ℂ) - atN d L N msq V₀ / (msq : ℂ) ^ 2) := by
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hm : (msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmsq.ne'
  rw [sum_transl hN hmsq V₀, sum_omega_psibar_psi _ (Cov_row_sum hmsq hN) (Cov_col_sum hmsq hN)
    (Z0_mem N V₀), EC_Z0 hd hL hN hmsq hgood V₀, ← ZNN, ZNN_eq_smul, c2_smul,
    c2_ZtNN hd hL hN hmsq hgood V₀]
  push_cast
  field_simp
  ring

/-- **Proposition `prop:suscept`** (`e:suscept-atilde`): with `⟨F⟩ = 𝔼_C[Z_0 F]/𝔼_C[Z_0]`,
`∑_{x ∈ Λ_N} ⟨ψ̄_0 ψ_x⟩ = 1/m² - (1/m⁴) ã_{N,N} / (1 + ũ_{N,N})`, provided
`1 + ũ_{N,N} ≠ 0` (equivalently `𝔼_C[Z_0] ≠ 0`). -/
theorem prop_suscept (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup)
    (hu : 1 + utN d L N msq V₀ ≠ 0) :
    ∑ x : Lam d L N, omega (Cov d L N msq) (Z0 d L N V₀ * (psibar 0 * psi x)) /
        omega (Cov d L N msq) (Z0 d L N V₀) =
      1 / (msq : ℂ) - 1 / (msq : ℂ) ^ 2 * (atN d L N msq V₀ / (1 + utN d L N msq V₀)) := by
  have hm : (msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmsq.ne'
  have he := Complex.exp_ne_zero (-(uN d L N msq V₀ * Fintype.card (Lam d L N)))
  rw [← sum_div, sum_EC_Z0_psibar_psi hd hL hN hmsq hgood V₀, EC_Z0 hd hL hN hmsq hgood V₀]
  field_simp

end

end Suscept
