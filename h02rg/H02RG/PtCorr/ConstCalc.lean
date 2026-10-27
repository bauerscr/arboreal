import PtCorr.Coef
import Suscept.PropSuscept
import Obs.Corr

/-!
# Constant-field calculus for `lem:ZNN-obs`

Restricted to constant fields (`Suscept.Rc`), an even element is `F⁰ + F² ψψ̄` with
`F⁰ = ε F`, `F² = c2 F` (`Suscept.Rc_even`), an odd one `c1p F ψ + c1m F ψ̄`
(`PtCorr.Rc_odd`).  Consequences used for the component formulas of `lem:ZNN-obs`:

* `ε`, `c2` of products of even elements (`c2_mul_of_even`: `(FG)² = F⁰G² + F²G⁰`);
* `c2 (ψ̄_x ψ_y) = -1`, `ε (ψ̄_x ψ_y) = 0`;
* the Wick formula for the zero mode on the torus, for even `F`:
  `ε (𝔼_{t Q_N} θ F) = F⁰ - F² t/|Λ|` (`ε_EC_tQ_theta`);
* `c1m (G ψ̄_y) = ε G`, `c1p (G ψ_y) = ε G`, `c1p (G ψ̄_y) = c1m (G ψ_y) = 0` for even `G`;
* the components of `e^{-(V^∅ + W)}` for observable `W` (`coe_oexp_neg_emb_add`).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Obs

section Calc

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [Nonempty Λ]

local notation "P" => Suscept.psiC Λ * Suscept.psibarC Λ

theorem const_form_mul (a b a' b' : ℂ) :
    (algebraMap ℂ (Grassmann.N Λ) a + b • P) * (algebraMap ℂ (Grassmann.N Λ) a' + b' • P) =
      algebraMap ℂ (Grassmann.N Λ) (a * a') + (a * b' + b * a') • P := by
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_smul_comm, one_mul,
    mul_one, Suscept.P_mul_self, smul_zero, add_zero, add_smul]
  rw [mul_comm b a']
  abel

/-- `ε (FG) = F⁰ G⁰`, `(FG)² = F⁰ G² + F² G⁰` for even `F`, `G`. -/
theorem c2_mul_of_even {F G : Grassmann.N Λ} (hF : inv' F = F) (hG : inv' G = G) :
    Suscept.c2 (F * G) = ε F * Suscept.c2 G + Suscept.c2 F * ε G := by
  have hFG : inv' (F * G) = F * G := by rw [map_mul, hF, hG]
  rw [← Suscept.c2_Rc hFG, map_mul, Suscept.Rc_even hF, Suscept.Rc_even hG, const_form_mul,
    Suscept.c2_add, Suscept.c2_algebraMap, Suscept.c2_smul, Suscept.c2_P]
  ring

theorem ε_P' : ε (P) = 0 := by
  simp [Suscept.psiC, Suscept.psibarC]

theorem c2_psibar_psi (x y : Λ) : Suscept.c2 (psibar x * psi y) = -1 := by
  rw [← Suscept.c2_Rc (inv'_psibar_psi x y), map_mul, Suscept.Rc_psibar, Suscept.Rc_psi,
    Suscept.psibarC_mul_psiC, show -(P) = (-1 : ℂ) • (P) by simp, Suscept.c2_smul, Suscept.c2_P]
  ring

theorem ε_psibar_psi (x y : Λ) : ε (psibar x * psi y) = 0 := by
  rw [← Suscept.ε_Rc, map_mul, Suscept.Rc_psibar, Suscept.Rc_psi, Suscept.psibarC_mul_psiC,
    map_neg, ε_P', neg_zero]

theorem c2_neg (F : Grassmann.N Λ) : Suscept.c2 (-F) = -Suscept.c2 F := by
  rw [show -F = (-1 : ℂ) • F by simp, Suscept.c2_smul]; ring

theorem c2_sub (F G : Grassmann.N Λ) : Suscept.c2 (F - G) = Suscept.c2 F - Suscept.c2 G := by
  rw [sub_eq_add_neg, Suscept.c2_add, c2_neg]; ring

theorem c2_nr (ra rb : ℂ) (a b : Λ) : Suscept.c2 (nr ra rb a b) = -(ra + rb) := by
  rw [nr, Suscept.c2_add, Suscept.c2_smul, Suscept.c2_smul, c2_psibar_psi, c2_psibar_psi]; ring

theorem ε_nr (ra rb : ℂ) (a b : Λ) : ε (nr ra rb a b) = 0 := by
  simp [nr, ε_psibar_psi]

theorem c2_nx (a b : Λ) : Suscept.c2 (nx a b) = -2 := by
  rw [nx, Suscept.c2_add, c2_psibar_psi, c2_psibar_psi]; ring

theorem ε_nx (a b : Λ) : ε (nx a b) = 0 := by
  simp [nx, ε_psibar_psi]

/-- `P ψ̄ = 0`. -/
theorem P_mul_psibarC : (P) * Suscept.psibarC Λ = 0 := by
  rw [mul_assoc, Suscept.psibarC_mul_self, mul_zero]

/-- `P ψ = 0`. -/
theorem P_mul_psiC : (P) * Suscept.psiC Λ = 0 := by
  rw [mul_assoc, Suscept.psibarC_mul_psiC, mul_neg, ← mul_assoc, Suscept.psiC_mul_self,
    zero_mul, neg_zero]

theorem c1m_mul_psibar {G : Grassmann.N Λ} (hG : inv' G = G) (y : Λ) : c1m (G * psibar y) = ε G := by
  rw [← c1m_Rc, map_mul, Suscept.Rc_even hG, Suscept.Rc_psibar, add_mul, smul_mul_assoc,
    P_mul_psibarC, smul_zero, add_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    c1m_smul, c1m_psibarC, mul_one]

theorem c1p_mul_psi {G : Grassmann.N Λ} (hG : inv' G = G) (y : Λ) : c1p (G * psi y) = ε G := by
  rw [← c1p_Rc, map_mul, Suscept.Rc_even hG, Suscept.Rc_psi, add_mul, smul_mul_assoc,
    P_mul_psiC, smul_zero, add_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    c1p_smul, c1p_psiC, mul_one]

/-- **Wick formula for the zero mode**: `ε (𝔼_C θ F) = F⁰ - F² c` for the constant covariance
`C_{xy} = c` and even `F`. -/
theorem ε_EC_cst_theta (t : ℝ) {F : Grassmann.N Λ} (hF : inv' F = F) :
    ε (EC (Suscept.cst Λ t) (theta F)) = ε F - Suscept.c2 F * (t : ℂ) := by
  rw [← Suscept.ε_Rc, Suscept.Rc_EC_theta_const, Suscept.Rc_even hF, map_add, map_add, map_smul,
    map_smul, Suscept.EC_theta_algebraMap, Suscept.EC_theta_const_P, map_add, map_smul, map_sub,
    AlgHom.commutes, AlgHom.commutes, ε_P']
  simp [smul_eq_mul]
  ring

end Calc

section Torus

open Loc

variable {d L N : ℕ} [NeZero L]

/-- **Wick formula for `t_N Q_N`**: `ε (𝔼_{t Q_N} θ F) = F⁰ - F² t/|Λ|` for even `F`. -/
theorem ε_EC_tQ_theta (t : ℝ) {F : Grassmann.N (Lam d L N)} (hF : inv' F = F) :
    ε (EC (t • FRD.QN : Matrix (Lam d L N) (Lam d L N) ℝ) (theta F)) =
      ε F - Suscept.c2 F * ((t / Fintype.card (Lam d L N) : ℝ) : ℂ) := by
  rw [Suscept.tQ_eq_cst, ε_EC_cst_theta _ hF]

end Torus

/-! ### The components of `e^{-(V^∅ + W)}` -/

section Oexp

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- For `ε(V^∅) = 0` and observable `W`, with `g = e^{-V^∅}`:
`e^{-(V^∅+W)} = (g, -g W_a, -g W_b, g (-W_ab + (s W_a W_b + W_b W_a)/2))`. -/
theorem coe_oexp_neg_emb_add {Vb : Step.EvR Λ} (hVb : ε (Vb : N Λ) = 0) {W : OE c Λ}
    (hW : bulk W = 0) :
    (oexp (-(emb Vb + W)) : SA c Λ) =
      ⟨(Step.gexp (-Vb) : N Λ), (Step.gexp (-Vb) : N Λ) * -(W : SA c Λ).a,
        (Step.gexp (-Vb) : N Λ) * -(W : SA c Λ).b,
        (Step.gexp (-Vb) : N Λ) * (-(W : SA c Λ).ab + (1 / 2 : ℂ) •
          (c.s • ((W : SA c Λ).a * (W : SA c Λ).b) + (W : SA c Λ).b * (W : SA c Λ).a))⟩ := by
  have hW0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [oexp_neg_emb_add hVb hW]
  have hsq : ((W ^ 2 : OE c Λ) : SA c Λ) = ⟨0, 0, 0, c.s • ((W : SA c Λ).a * (W : SA c Λ).b) +
      (W : SA c Λ).b * (W : SA c Λ).a⟩ := by
    rw [sq]
    refine SA.ext ?_ ?_ ?_ ?_
    · rw [OE.mul_e, hW0, zero_mul]
    · rw [OE.mul_a, hW0, zero_mul, mul_zero, add_zero]
    · rw [OE.mul_b, hW0, zero_mul, mul_zero, add_zero]
    · rw [OE.mul_ab, hW0, zero_mul, mul_zero, zero_add, add_zero]
  refine SA.ext ?_ ?_ ?_ ?_
  · rw [OE.mul_e]; simp [hW0, hsq]
  · rw [OE.mul_a]; simp [hW0, hsq, sub_eq_add_neg]
  · rw [OE.mul_b]; simp [hW0, hsq, sub_eq_add_neg]
  · rw [OE.mul_ab]; simp [hW0, hsq, sub_eq_add_neg]

end Oexp

end

end PtCorr
