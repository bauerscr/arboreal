import PtCorr.Bridge

/-!
# The finite-`N` identity for `λ^{(1)}` (`e:lambda1-pf2`) (WP1b)

In Case (1), with `G = 𝔼_C θ e^{-V_0(Λ)}` (`PtCorr.Gobs`, initial couplings `λ_a = λ_b = l₀`),
`C = (-Δ + m²)^{-1}` and `G̃ = e^{u_N|Λ|} G` (WP1's `ZtO`):

* `c1m_RcO_Gobs_one_a`: `∂_{ψ̄} ∂_{σ_a} G̃|_0 = c1m (Rc G̃_a) = l₀ (1 + ũ_{N,N} - ã_{N,N}/m²)`;
* `c1p_RcO_Gobs_one_b`: `∂_{ψ} G̃_b|_0 = c1p (Rc G̃_b) = -l₀ (1 + ũ_{N,N} - ã_{N,N}/m²)`.

(The versions without `e^{u_N|Λ|}` are `c1m_Gobs_one_a`, `c1p_Gobs_one_b`.)
This is `e:lambda1-pf2` of the text, with the sign conventions of `Obs.Coupling`
(`F_a = -λ_a ψ̄_a`, `F_b = +λ_b ψ_b`); the minus sign in the `b` version comes from
`ψ_b σ̄_b = -σ̄_b ψ_b`.

Proof (as in the text, but without generating functions):
1. The `a` component of `e^{-V_0(Λ)}` is `Z_0 · l₀ ψ̄_a` (`oexp_a`), the `b` component
   `-Z_0 · l₀ ψ_b` (`oexp_b`), so `G_a = 𝔼_C θ (Z_0 l₀ ψ̄_a)`.
2. `c1m (𝔼_C θ F) = ⟨∑_y ∂_{ψ̄_y} F⟩_C` (`PtCorr.c1m_EC_theta`).
3. One-sided Gaussian integration by parts (`omega_sum_psi_mul`, `omega_sum_psibar_mul`):
   `∑_x ⟨ψ_x F⟩_C = -c ⟨∑_y ∂_{ψ̄_y} F⟩_C` and `∑_x ⟨ψ̄_x F⟩_C = c ⟨∑_y ∂_{ψ_y} F⟩_C` for
   constant row (column) sums `c` of `C` (here `c = 1/m²`, `Suscept.Cov_row_sum`).
4. Translation invariance (`PtCorr.sum_omega_Z0_psibar_psi_row/col`, `Suscept.sum_transl`)
   and `Suscept.sum_EC_Z0_psibar_psi`.

No hypothesis `1 + ũ ≠ 0` and no `a ≠ b` is needed; `m² > 0` and the standard hypotheses of
`Suscept.prop_ZNN` are.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Obs Loc Step Flow SA

set_option linter.unusedSimpArgs false

variable {d L N : ℕ} [NeZero L]

/-! ### One-sided Gaussian integration by parts -/

section IBP

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem omega_sum (C : Matrix Λ Λ ℝ) {ι : Type*} (s : Finset ι) (F : ι → Grassmann.N Λ) :
    omega C (∑ i ∈ s, F i) = ∑ i ∈ s, omega C (F i) := by
  simp [omega, map_sum]

/-- `∑_x ⟨ψ_x F⟩_C = -c ⟨∑_y ∂_{ψ̄_y} F⟩_C` if `∑_y C_{xy} = c`. -/
theorem omega_sum_psi_mul (C : Matrix Λ Λ ℝ) {c : ℝ} (hrow : ∀ x, ∑ y, C x y = c)
    (F : Grassmann.N Λ) :
    ∑ x : Λ, omega C (psi x * F) = -((c : ℂ) * omega C (Dφ (Suscept.δs (-1)) F)) := by
  have e : ∑ x : Λ, psi x * F = ExteriorAlgebra.ι ℂ (Suscept.vs (Λ := Λ) 1) * F := by
    rw [Suscept.ι_vs, sum_mul]; rfl
  rw [← omega_sum, e, omega_ι_mul, Suscept.phiC_vs_one C hrow]
  rw [show Dφ (-((c : ℂ) • Suscept.δs (-1))) F = -((c : ℂ) • Dφ (Suscept.δs (-1)) F) by
    simp [Dφ], omega_neg, omega_smul']

/-- `∑_x ⟨ψ̄_x F⟩_C = c ⟨∑_y ∂_{ψ_y} F⟩_C` if `∑_x C_{xy} = c`. -/
theorem omega_sum_psibar_mul (C : Matrix Λ Λ ℝ) {c : ℝ} (hcol : ∀ y, ∑ x, C x y = c)
    (F : Grassmann.N Λ) :
    ∑ x : Λ, omega C (psibar x * F) = (c : ℂ) * omega C (Dφ (Suscept.δs 1) F) := by
  have e : ∑ x : Λ, psibar x * F = ExteriorAlgebra.ι ℂ (Suscept.vs (Λ := Λ) (-1)) * F := by
    rw [Suscept.ι_vs, sum_mul]; rfl
  rw [← omega_sum, e, omega_ι_mul, Suscept.phiC_vs_neg C hcol]
  rw [Dφ_smul, omega_smul']

end IBP

/-! ### The odd components of `e^{-V_0(Λ)}` -/

section Comp

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem oexp_neg_emb_add_a {Vb : Step.EvR Λ} (hVb : ε (Vb : Grassmann.N Λ) = 0) {W : OE c Λ}
    (hW : bulk W = 0) :
    ((oexp (-(emb Vb + W)) : OE c Λ) : SA c Λ).a =
      (Step.gexp (-Vb) : Grassmann.N Λ) * -(W : SA c Λ).a := by
  have hW0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [oexp_neg_emb_add hVb hW, OE.mul_a]
  have h2 : ((W ^ 2 : OE c Λ) : SA c Λ).a = 0 := by
    rw [sq, OE.mul_a, hW0, zero_mul, zero_add, mul_zero]
  have h2e : ((W ^ 2 : OE c Λ) : SA c Λ).e = 0 := by
    rw [sq, OE.mul_e, hW0, zero_mul]
  have h2' : ((W : SA c Λ) ^ 2).a = 0 := by rw [← SubmonoidClass.coe_pow]; exact h2
  simp [h2', h2e, hW0]

theorem oexp_neg_emb_add_b {Vb : Step.EvR Λ} (hVb : ε (Vb : Grassmann.N Λ) = 0) {W : OE c Λ}
    (hW : bulk W = 0) :
    ((oexp (-(emb Vb + W)) : OE c Λ) : SA c Λ).b =
      (Step.gexp (-Vb) : Grassmann.N Λ) * -(W : SA c Λ).b := by
  have hW0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [oexp_neg_emb_add hVb hW, OE.mul_b]
  have h2 : ((W ^ 2 : OE c Λ) : SA c Λ).b = 0 := by
    rw [sq, OE.mul_b, hW0, zero_mul, zero_add, mul_zero]
  have h2e : ((W ^ 2 : OE c Λ) : SA c Λ).e = 0 := by
    rw [sq, OE.mul_e, hW0, zero_mul]
  have h2' : ((W : SA c Λ) ^ 2).b = 0 := by rw [← SubmonoidClass.coe_pow]; exact h2
  simp [h2', h2e, hW0]

end Comp

variable (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

/-- The `a` component of `e^{-V_0(Λ)}` (Case (1)) is `Z_0 · l₀ ψ̄_a`. -/
theorem oexp_a :
    ((oexp (-(VfullX V₀ (initObs .one l₀) a b univ)) : OE .one (Lam d L N)) :
        SA .one (Lam d L N)).a = Suscept.Z0 d L N V₀ * (l₀ • psibar a) := by
  rw [VfullX_initObs_univ, oexp_neg_emb_add_a (ε_VE V₀ univ) (bulk_evalO _ _ a b univ)]
  simp [initObs, coe_evalO, evalS, Coup1.evalS_a, ind_pos (mem_univ _)]
  rfl

/-- The `b` component of `e^{-V_0(Λ)}` (Case (1)) is `-Z_0 · l₀ ψ_b`. -/
theorem oexp_b :
    ((oexp (-(VfullX V₀ (initObs .one l₀) a b univ)) : OE .one (Lam d L N)) :
        SA .one (Lam d L N)).b = Suscept.Z0 d L N V₀ * -(l₀ • psi b) := by
  rw [VfullX_initObs_univ, oexp_neg_emb_add_b (ε_VE V₀ univ) (bulk_evalO _ _ a b univ)]
  simp [initObs, coe_evalO, evalS, Coup1.evalS_b, ind_pos (mem_univ _)]
  rfl

/-! ### The identity -/

section Main

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) {msq ℓ₀ : ℝ} (hmsq : 0 < msq)
  (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j))
include hd hL hN hmsq hgood

/-- `∑_y 𝔼_C[Z_0 ψ̄_p ψ_y] = e^{-u_N|Λ|}((1+ũ)/m² - ã/m⁴)` for every `p`. -/
theorem sum_row_eq (p : Lam d L N) :
    ∑ y : Lam d L N, omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar p * psi y)) =
      Complex.exp (-(Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        ((1 + Suscept.utN d L N msq V₀) / (msq : ℂ) - Suscept.atN d L N msq V₀ / (msq : ℂ) ^ 2) := by
  rw [sum_omega_Z0_psibar_psi_row hmsq hN, ← Suscept.sum_transl hN hmsq V₀,
    Suscept.sum_EC_Z0_psibar_psi hd hL hN hmsq hgood V₀]

/-- `∑_x 𝔼_C[Z_0 ψ̄_x ψ_q] = e^{-u_N|Λ|}((1+ũ)/m² - ã/m⁴)` for every `q`. -/
theorem sum_col_eq (q : Lam d L N) :
    ∑ x : Lam d L N, omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi q)) =
      Complex.exp (-(Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        ((1 + Suscept.utN d L N msq V₀) / (msq : ℂ) - Suscept.atN d L N msq V₀ / (msq : ℂ) ^ 2) := by
  rw [sum_omega_Z0_psibar_psi_col hmsq hN, ← Suscept.sum_transl hN hmsq V₀,
    Suscept.sum_EC_Z0_psibar_psi hd hL hN hmsq hgood V₀]

/-- **`e:lambda1-pf2`** (unnormalised): `c1m (G_a) = e^{-u_N|Λ|} l₀ (1 + ũ - ã/m²)`. -/
theorem c1m_Gobs_one_a :
    c1m ((Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N)) : SA .one (Lam d L N)).a =
      Complex.exp (-(Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        (l₀ * (1 + Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ))) := by
  have hm : (msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmsq.ne'
  have hZ := Suscept.Z0_mem N V₀ (d := d) (L := L)
  have hIBP := omega_sum_psi_mul (Suscept.Cov d L N msq) (Suscept.Cov_row_sum hmsq hN)
    (Suscept.Z0 d L N V₀ * (l₀ • psibar a))
  have e : ∀ x : Lam d L N, psi x * (Suscept.Z0 d L N V₀ * (l₀ • psibar a)) =
      (-l₀) • (Suscept.Z0 d L N V₀ * (psibar a * psi x)) := by
    intro x
    rw [← mul_assoc, ← mul_comm_of_even hZ, mul_assoc, mul_smul_comm, psi_mul_psibar,
      mul_smul_comm, mul_neg, neg_smul, smul_neg]
  simp only [e, omega_smul', ← mul_sum, sum_row_eq V₀ hd hL hN hmsq hgood a] at hIBP
  show c1m (EC _ (theta ((oexp _ : OE .one (Lam d L N)) : SA .one (Lam d L N)).a)) = _
  rw [oexp_a, c1m_EC_theta]
  have hc : ((msq⁻¹ : ℝ) : ℂ) = (msq : ℂ)⁻¹ := by push_cast; rfl
  rw [hc] at hIBP
  have key : omega (Suscept.Cov d L N msq) (Dφ (Suscept.δs (-1))
      (Suscept.Z0 d L N V₀ * (l₀ • psibar a))) = -((msq : ℂ) * (-l₀ *
        (Complex.exp (-(Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        ((1 + Suscept.utN d L N msq V₀) / (msq : ℂ) -
          Suscept.atN d L N msq V₀ / (msq : ℂ) ^ 2)))) := by
    rw [hIBP]; field_simp
  rw [key]
  field_simp

/-- **`e:lambda1-pf2`**, `b` version (unnormalised):
`c1p (G_b) = -e^{-u_N|Λ|} l₀ (1 + ũ - ã/m²)`. -/
theorem c1p_Gobs_one_b :
    c1p ((Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N)) : SA .one (Lam d L N)).b =
      -(Complex.exp (-(Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        (l₀ * (1 + Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)))) := by
  have hm : (msq : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmsq.ne'
  have hZ := Suscept.Z0_mem N V₀ (d := d) (L := L)
  have hIBP := omega_sum_psibar_mul (Suscept.Cov d L N msq) (Suscept.Cov_col_sum hmsq hN)
    (Suscept.Z0 d L N V₀ * -(l₀ • psi b))
  have e : ∀ x : Lam d L N, psibar x * (Suscept.Z0 d L N V₀ * -(l₀ • psi b)) =
      (-l₀) • (Suscept.Z0 d L N V₀ * (psibar x * psi b)) := by
    intro x
    rw [← mul_assoc, ← mul_comm_of_even hZ, mul_assoc, mul_neg, mul_smul_comm, mul_neg,
      mul_smul_comm, neg_smul]
  simp only [e, omega_smul', ← mul_sum, sum_col_eq V₀ hd hL hN hmsq hgood b] at hIBP
  show c1p (EC _ (theta ((oexp _ : OE .one (Lam d L N)) : SA .one (Lam d L N)).b)) = _
  rw [oexp_b, c1p_EC_theta]
  have hc : ((msq⁻¹ : ℝ) : ℂ) = (msq : ℂ)⁻¹ := by push_cast; rfl
  rw [hc] at hIBP
  have key : omega (Suscept.Cov d L N msq) (Dφ (Suscept.δs 1)
      (Suscept.Z0 d L N V₀ * -(l₀ • psi b))) = (msq : ℂ) * (-l₀ *
        (Complex.exp (-(Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))) *
        ((1 + Suscept.utN d L N msq V₀) / (msq : ℂ) -
          Suscept.atN d L N msq V₀ / (msq : ℂ) ^ 2))) := by
    rw [hIBP]; field_simp
  rw [key]
  field_simp

/-- **`e:lambda1-pf2`**: `∂_{ψ̄}∂_{σ_a} Z̃|_0 = c1m (Rc G̃_a) = l₀ (1 + ũ_{N,N} - ã_{N,N}/m²)`,
`G̃ = e^{u_N|Λ|} G` (WP1's `ZtO … (initObs .one l₀) a b`). -/
theorem c1m_RcO_Gobs_one_a :
    c1m ((RcO .one _ (eu d L N msq V₀ • Gobs d L .one N msq V₀ l₀ a b) :
        OE .one (Lam d L N)) : SA .one (Lam d L N)).a =
      l₀ * (1 + Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ)) := by
  rw [coe_RcO_a, c1m_Rc, Subalgebra.coe_smul, smul_a, c1m_smul,
    c1m_Gobs_one_a V₀ l₀ a b hd hL hN hmsq hgood, ← mul_assoc, eu, ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero, one_mul]

/-- **`e:lambda1-pf2`**, `b` version: `c1p (Rc G̃_b) = -l₀ (1 + ũ_{N,N} - ã_{N,N}/m²)`. -/
theorem c1p_RcO_Gobs_one_b :
    c1p ((RcO .one _ (eu d L N msq V₀ • Gobs d L .one N msq V₀ l₀ a b) :
        OE .one (Lam d L N)) : SA .one (Lam d L N)).b =
      -(l₀ * (1 + Suscept.utN d L N msq V₀ - Suscept.atN d L N msq V₀ / (msq : ℂ))) := by
  rw [coe_RcO_b, c1p_Rc, Subalgebra.coe_smul, smul_b, c1p_smul,
    c1p_Gobs_one_b V₀ l₀ a b hd hL hN hmsq hgood, mul_neg, ← mul_assoc, eu, ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero, one_mul]

end Main

end

end PtCorr
