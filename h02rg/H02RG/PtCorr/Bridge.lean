import Obs.FlowObsBd
import Obs.Corr
import Suscept.PropSuscept
import PtCorr.Coef

/-!
# The correlation bridge (WP1b)

With `G = 𝔼_C θ e^{-V_0(Λ)}` (`Gobs`), `C = (-Δ + m²)^{-1}` and
`V_0(Λ) = V^∅_0(Λ) + V^obs_0(Λ)` evaluated at the initial observable couplings
`initObs c l₀` (`λ_a = λ_b = l₀`, all others `0`), the constant terms of the components of `G`
are Gaussian moments (`ε_Gobs_e`, `ε_Gobs_one_ab`, `ε_Gobs_two_a`, `ε_Gobs_two_b`,
`ε_Gobs_two_ab`), whence the correlations are ratios of these constant terms:

* Case (1): `⟨ψ̄_a ψ_b⟩ = ε(G_ab) / (l₀² ε(G_∅))` (`avg_one_eq`);
* Case (2): `⟨ψ̄_a ψ_a⟩ = ε(G_a) / (l₀ ε(G_∅))` (`avg_two_a_eq`), `⟨ψ̄_b ψ_b⟩ = ε(G_b)/(l₀ ε(G_∅))`
  (`avg_two_b_eq`), and the (full, not truncated) four-point function
  `⟨ψ̄_aψ_a ψ̄_bψ_b⟩ = ε(G_ab) / (l₀² ε(G_∅))` (`avg_two_ab_eq`).

With `ε(G_∅) = 𝔼_C[Z_0] = e^{-u_N|Λ|}(1 + ũ_{N,N})` (`Suscept.EC_Z0`) the versions `*_eq'`
are stated for `G̃ = e^{u_N|Λ|} G` (this is WP1's `ZtO … (initObs c l₀) a b`) and the
denominator `l₀^p (1 + ũ_{N,N})`.

**Hypotheses / deviations.**
* Only `l₀ ≠ 0` is needed for the unprimed versions: `⟨·⟩` is defined as a ratio
  (`Obs.avg`), and if `𝔼_C[Z_0] = 0` both sides are `x / 0 = 0` in Lean.  No `a ≠ b`
  hypothesis is needed (if `a = b`, both sides of the Case (2) `ab` formula vanish).
* We do not use `Obs.corr_one`/`corr_two_*` (which are about `log G`); the direct component
  formula `Obs.omO_oexp` is simpler and gives the untruncated four-point function.

`avg_transl`: `⟨T F⟩ = ⟨F⟩` for torus translations `T = autAlg (Equiv.addRight t)` (for
`m² > 0`, `N ≥ 1`), with the corollaries `avg_psibar_psi_transl`, `avg_psibar_psi_diag_transl`,
`avg_four_transl`, and the translation invariance of the row and column sums
(`sum_omega_Z0_psibar_psi_row`, `…_col`) used in `PtCorr.SusceptObs`.
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Obs Loc Step Flow SA

set_option linter.unusedSimpArgs false

variable {d L N : ℕ} [NeZero L]

/-! ### The initial potential -/

theorem toV_initObs (c : Case) (l₀ : ℂ) : Coup.toV c (initObs c l₀) = initObs c l₀ := by
  cases c <;> rfl

/-- `V_0(Λ) = V^∅_0(Λ) + V^obs_0(Λ)` at the initial couplings. -/
theorem VfullX_initObs_univ (c : Case) (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N) :
    VfullX V₀ (initObs c l₀) a b univ = emb (VE V₀ univ) + evalO c (initObs c l₀) a b univ := by
  rw [VfullX, toV_initObs, splitO_univ]

variable (d L) in
/-- `G = 𝔼_C θ e^{-V_0(Λ)}` with `C = (-Δ + m²)^{-1}` and the initial observable couplings. -/
def Gobs (c : Case) (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N) :
    OE c (Lam d L N) :=
  ECO (Suscept.Cov d L N msq) (thetaO (oexp (-(VfullX V₀ (initObs c l₀) a b univ))))

theorem ε_eq_of_omO (C : Matrix (Lam d L N) (Lam d L N) ℝ) {c : Case} (F : OE c (Lam d L N)) :
    ε ((ECO C (thetaO F) : OE c (Lam d L N)) : SA c (Lam d L N)).e =
      ε ((omO C F : OE c (Lam d L N)) : SA c (Lam d L N)).e ∧
    ε ((ECO C (thetaO F) : OE c (Lam d L N)) : SA c (Lam d L N)).a =
      ε ((omO C F : OE c (Lam d L N)) : SA c (Lam d L N)).a ∧
    ε ((ECO C (thetaO F) : OE c (Lam d L N)) : SA c (Lam d L N)).b =
      ε ((omO C F : OE c (Lam d L N)) : SA c (Lam d L N)).b ∧
    ε ((ECO C (thetaO F) : OE c (Lam d L N)) : SA c (Lam d L N)).ab =
      ε ((omO C F : OE c (Lam d L N)) : SA c (Lam d L N)).ab := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [omO]

section Components

variable (c : Case) (msq : ℝ) (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N)

/-- The components of `omO C e^{-V_0(Λ)}` at the initial couplings. -/
theorem omO_init :
    (omO (Suscept.Cov d L N msq) (oexp (-(VfullX V₀ (initObs c l₀) a b univ))) :
        SA c (Lam d L N)) =
      ⟨algebraMap ℂ _ (Zb (Suscept.Cov d L N msq) (VE V₀ univ)),
        algebraMap ℂ _ (-omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ *
          ((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) : SA c (Lam d L N)).a)),
        algebraMap ℂ _ (-omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ *
          ((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) : SA c (Lam d L N)).b)),
        algebraMap ℂ _ (omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ *
          (-((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) : SA c (Lam d L N)).ab +
            (1 / 2 : ℂ) • (c.s • (((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) :
              SA c (Lam d L N)).a * ((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) :
              SA c (Lam d L N)).b) + ((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) :
              SA c (Lam d L N)).b * ((evalO c (initObs c l₀) a b univ : OE c (Lam d L N)) :
              SA c (Lam d L N)).a))))⟩ := by
  rw [VfullX_initObs_univ]
  exact omO_oexp _ (ε_VE V₀ univ) (bulk_evalO c _ a b univ)

/-- `ε(G_∅) = 𝔼_C[Z_0]`. -/
theorem ε_Gobs_e :
    ε ((Gobs d L c N msq V₀ l₀ a b : OE c (Lam d L N)) : SA c (Lam d L N)).e =
      omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀) := by
  rw [Gobs, (ε_eq_of_omO _ _).1, omO_init]
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

/-- Case (1): `ε(G_ab) = l₀² 𝔼_C[Z_0 ψ̄_a ψ_b]`. -/
theorem ε_Gobs_one_ab :
    ε ((Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N)) : SA .one (Lam d L N)).ab =
      l₀ ^ 2 * omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar a * psi b)) := by
  rw [Gobs, (ε_eq_of_omO _ _).2.2.2, omO_init]
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [initObs, coe_evalO, evalS, Coup1.evalS_a, Coup1.evalS_b, Coup1.evalS_ab, ind_pos (mem_univ _),
    ind_pos (And.intro (mem_univ a) (mem_univ b)), one_smul, neg_zero, _root_.map_zero, nr_zero,
    add_zero, Case.s_one, zero_add]
  have e : (1 / 2 : ℂ) • ((-1 : ℂ) • ((-l₀) • psibar a * l₀ • psi b) +
      l₀ • psi b * (-l₀) • psibar a) = (l₀ ^ 2) • (psibar a * psi b) := by
    simp only [smul_mul_smul_comm, psi_mul_psibar]; module
  rw [e, mul_smul_comm, omega_smul']

/-- Case (2): `ε(G_a) = l₀ 𝔼_C[Z_0 ψ̄_a ψ_a]`. -/
theorem ε_Gobs_two_a :
    ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) : SA .two (Lam d L N)).a =
      l₀ * omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar a * psi a)) := by
  rw [Gobs, (ε_eq_of_omO _ _).2.1, omO_init]
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [initObs, coe_evalO, evalS, Coup2.evalS_a, ind_pos (mem_univ _), one_smul, neg_zero, _root_.map_zero,
    zero_sub, mul_neg, omega_neg, neg_neg, mul_smul_comm, omega_smul']

/-- Case (2): `ε(G_b) = l₀ 𝔼_C[Z_0 ψ̄_b ψ_b]`. -/
theorem ε_Gobs_two_b :
    ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) : SA .two (Lam d L N)).b =
      l₀ * omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar b * psi b)) := by
  rw [Gobs, (ε_eq_of_omO _ _).2.2.1, omO_init]
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [initObs, coe_evalO, evalS, Coup2.evalS_b, ind_pos (mem_univ _), one_smul, neg_zero, _root_.map_zero,
    zero_sub, mul_neg, omega_neg, neg_neg, mul_smul_comm, omega_smul']

/-- Case (2): `ε(G_ab) = l₀² 𝔼_C[Z_0 ψ̄_aψ_a ψ̄_bψ_b]`. -/
theorem ε_Gobs_two_ab :
    ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab =
      l₀ ^ 2 * omega (Suscept.Cov d L N msq)
        (Suscept.Z0 d L N V₀ * (psibar a * psi a * (psibar b * psi b))) := by
  rw [Gobs, (ε_eq_of_omO _ _).2.2.2, omO_init]
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [initObs, coe_evalO, evalS, Coup2.evalS_a, Coup2.evalS_b, Coup2.evalS_ab, ind_pos (mem_univ _),
    ind_pos (And.intro (mem_univ a) (mem_univ b)), one_smul, neg_zero, _root_.map_zero, zero_sub,
    nr_zero, zero_div, zero_smul, sub_zero, add_zero, Case.s_two, neg_zero, zero_add]
  have e : (1 / 2 : ℂ) • ((-(l₀ • (psibar a * psi a))) * (-(l₀ • (psibar b * psi b))) +
      (-(l₀ • (psibar b * psi b))) * (-(l₀ • (psibar a * psi a)))) =
      (l₀ ^ 2) • (psibar a * psi a * (psibar b * psi b)) := by
    simp only [neg_mul_neg, smul_mul_smul_comm]
    rw [psibar_psi_comm a b]; module
  rw [e, mul_smul_comm, omega_smul']

end Components

/-! ### Correlations as ratios -/

section Ratio

variable (msq : ℝ) (V₀ : Vcoup) {l₀ : ℂ} (hl : l₀ ≠ 0) (a b : Lam d L N)
include hl

omit hl in
theorem avg_eq_Z0 (F : Alg d L N) :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) F =
      omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * F) /
        omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀) := rfl

/-- Case (1): `⟨ψ̄_a ψ_b⟩ = ε(G_ab) / (l₀² ε(G_∅))`. -/
theorem avg_one_eq :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi b) =
      ε ((Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N)) : SA .one (Lam d L N)).ab /
        (l₀ ^ 2 * ε ((Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N)) :
          SA .one (Lam d L N)).e) := by
  rw [ε_Gobs_one_ab, ε_Gobs_e, avg_eq_Z0, mul_div_mul_left _ _ (pow_ne_zero 2 hl)]

/-- Case (2): `⟨ψ̄_a ψ_a⟩ = ε(G_a) / (l₀ ε(G_∅))`. -/
theorem avg_two_a_eq :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi a) =
      ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) : SA .two (Lam d L N)).a /
        (l₀ * ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).e) := by
  rw [ε_Gobs_two_a, ε_Gobs_e, avg_eq_Z0, mul_div_mul_left _ _ hl]

/-- Case (2): `⟨ψ̄_b ψ_b⟩ = ε(G_b) / (l₀ ε(G_∅))`. -/
theorem avg_two_b_eq :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar b * psi b) =
      ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) : SA .two (Lam d L N)).b /
        (l₀ * ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).e) := by
  rw [ε_Gobs_two_b, ε_Gobs_e, avg_eq_Z0, mul_div_mul_left _ _ hl]

/-- Case (2): `⟨ψ̄_aψ_a ψ̄_bψ_b⟩ = ε(G_ab) / (l₀² ε(G_∅))` (the full four-point function). -/
theorem avg_two_ab_eq :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi a * (psibar b * psi b)) =
      ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab /
        (l₀ ^ 2 * ε ((Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).e) := by
  rw [ε_Gobs_two_ab, ε_Gobs_e, avg_eq_Z0, mul_div_mul_left _ _ (pow_ne_zero 2 hl)]

end Ratio

/-! ### The normalised versions with `1 + ũ_{N,N}` -/

section Normalised

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) {msq ℓ₀ : ℝ} (hmsq : 0 < msq)
  (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup)
  {l₀ : ℂ} (hl : l₀ ≠ 0) (a b : Lam d L N)

/-- `e^{u_N |Λ|}`. -/
abbrev eu (d L N : ℕ) [NeZero L] (msq : ℝ) (V₀ : Vcoup) : ℂ :=
  Complex.exp (Suscept.uN d L N msq V₀ * Fintype.card (Lam d L N))

include hd hL hN hmsq hgood

/-- `ε(G̃_∅) = 1 + ũ_{N,N}` for `G̃ = e^{u_N|Λ|} G`. -/
theorem ε_eu_Gobs_e (c : Case) :
    ε (((eu d L N msq V₀ • Gobs d L c N msq V₀ l₀ a b : OE c (Lam d L N))) :
      SA c (Lam d L N)).e = 1 + Suscept.utN d L N msq V₀ := by
  rw [Subalgebra.coe_smul, smul_e, map_smul, ε_Gobs_e, Suscept.EC_Z0 hd hL hN hmsq hgood V₀,
    smul_eq_mul, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

include hl

/-- Case (1): `⟨ψ̄_a ψ_b⟩ = ε(G̃_ab) / (l₀² (1 + ũ))`. -/
theorem avg_one_eq' :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi b) =
      ε (((eu d L N msq V₀ • Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N))) :
        SA .one (Lam d L N)).ab / (l₀ ^ 2 * (1 + Suscept.utN d L N msq V₀)) := by
  rw [← ε_eu_Gobs_e hd hL hN hmsq hgood V₀ a b .one (l₀ := l₀), avg_one_eq msq V₀ hl a b]
  simp only [Subalgebra.coe_smul, smul_e, smul_ab, map_smul, smul_eq_mul]
  rw [mul_left_comm (l₀ ^ 2), mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-- Case (2): `⟨ψ̄_a ψ_a⟩ = ε(G̃_a) / (l₀ (1 + ũ))`. -/
theorem avg_two_a_eq' :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi a) =
      ε (((eu d L N msq V₀ • Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N))) :
        SA .two (Lam d L N)).a / (l₀ * (1 + Suscept.utN d L N msq V₀)) := by
  rw [← ε_eu_Gobs_e hd hL hN hmsq hgood V₀ a b .two (l₀ := l₀), avg_two_a_eq msq V₀ hl a b]
  simp only [Subalgebra.coe_smul, smul_e, smul_a, map_smul, smul_eq_mul]
  rw [mul_left_comm l₀, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-- Case (2): `⟨ψ̄_b ψ_b⟩ = ε(G̃_b) / (l₀ (1 + ũ))`. -/
theorem avg_two_b_eq' :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar b * psi b) =
      ε (((eu d L N msq V₀ • Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N))) :
        SA .two (Lam d L N)).b / (l₀ * (1 + Suscept.utN d L N msq V₀)) := by
  rw [← ε_eu_Gobs_e hd hL hN hmsq hgood V₀ a b .two (l₀ := l₀), avg_two_b_eq msq V₀ hl a b]
  simp only [Subalgebra.coe_smul, smul_e, smul_b, map_smul, smul_eq_mul]
  rw [mul_left_comm l₀, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/-- Case (2): `⟨ψ̄_aψ_a ψ̄_bψ_b⟩ = ε(G̃_ab) / (l₀² (1 + ũ))`. -/
theorem avg_two_ab_eq' :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi a * (psibar b * psi b)) =
      ε (((eu d L N msq V₀ • Gobs d L .two N msq V₀ l₀ a b : OE .two (Lam d L N))) :
        SA .two (Lam d L N)).ab / (l₀ ^ 2 * (1 + Suscept.utN d L N msq V₀)) := by
  rw [← ε_eu_Gobs_e hd hL hN hmsq hgood V₀ a b .two (l₀ := l₀), avg_two_ab_eq msq V₀ hl a b]
  simp only [Subalgebra.coe_smul, smul_e, smul_ab, map_smul, smul_eq_mul]
  rw [mul_left_comm (l₀ ^ 2), mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

end Normalised

/-! ### Translation invariance -/

section Transl

variable {msq : ℝ} (hmsq : 0 < msq) (hN : 1 ≤ N) (V₀ : Vcoup)
include hmsq hN

/-- `𝔼_C[Z_0 · T F] = 𝔼_C[Z_0 F]` for a torus translation `T`. -/
theorem omega_Z0_transl (t : Lam d L N) (F : Alg d L N) :
    omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * autAlg (Equiv.addRight t) F) =
      omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * F) := by
  have := Suscept.omega_autAlg (Equiv.addRight t) (C := Suscept.Cov d L N msq)
    (fun x y => Suscept.Cov_transl hmsq hN x y t) (Suscept.Z0 d L N V₀ * F)
  rw [map_mul, Suscept.autAlg_Z0] at this
  exact this

/-- **Translation invariance**: `⟨T F⟩ = ⟨F⟩` for `T = autAlg (Equiv.addRight t)`. -/
theorem avg_transl (t : Lam d L N) (F : Alg d L N) :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (autAlg (Equiv.addRight t) F) =
      avg (Suscept.Cov d L N msq) (VE V₀ univ) F := by
  rw [avg_eq_Z0, avg_eq_Z0, omega_Z0_transl hmsq hN]

/-- `⟨ψ̄_{p+t} ψ_{q+t}⟩ = ⟨ψ̄_p ψ_q⟩`. -/
theorem avg_psibar_psi_transl (t p q : Lam d L N) :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar (p + t) * psi (q + t)) =
      avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar p * psi q) := by
  have := avg_transl hmsq hN V₀ t (psibar p * psi q)
  rwa [map_mul, autAlg_psibar, autAlg_psi] at this

/-- `⟨ψ̄_{p+t} ψ_{p+t}⟩ = ⟨ψ̄_p ψ_p⟩`. -/
theorem avg_psibar_psi_diag_transl (t p : Lam d L N) :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar (p + t) * psi (p + t)) =
      avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar p * psi p) :=
  avg_psibar_psi_transl hmsq hN V₀ t p p

/-- `⟨ψ̄_{p+t}ψ_{p+t} ψ̄_{q+t}ψ_{q+t}⟩ = ⟨ψ̄_pψ_p ψ̄_qψ_q⟩`. -/
theorem avg_four_transl (t p q : Lam d L N) :
    avg (Suscept.Cov d L N msq) (VE V₀ univ)
        (psibar (p + t) * psi (p + t) * (psibar (q + t) * psi (q + t))) =
      avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar p * psi p * (psibar q * psi q)) := by
  have := avg_transl hmsq hN V₀ t (psibar p * psi p * (psibar q * psi q))
  rwa [map_mul, map_mul, map_mul, autAlg_psibar, autAlg_psi, autAlg_psibar, autAlg_psi]
    at this

/-- Row sums: `∑_y 𝔼_C[Z_0 ψ̄_p ψ_y] = |Λ|⁻¹ ∑_{x,y} 𝔼_C[Z_0 ψ̄_x ψ_y]`. -/
theorem sum_omega_Z0_psibar_psi_row (p : Lam d L N) :
    ∑ y : Lam d L N, omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar p * psi y)) =
      ((Fintype.card (Lam d L N) : ℂ))⁻¹ *
        ∑ x : Lam d L N, ∑ y : Lam d L N,
          omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi y)) := by
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h : ∀ x : Lam d L N, ∑ y : Lam d L N,
      omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi y)) =
      ∑ y : Lam d L N, omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar p * psi y)) := by
    intro x
    rw [← Equiv.sum_comp (Equiv.addRight (x - p))]
    refine sum_congr rfl fun y _ => ?_
    have := omega_Z0_transl hmsq hN V₀ (x - p) (psibar p * psi y)
    rw [map_mul, autAlg_psibar, autAlg_psi] at this
    simpa using this
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Column sums: `∑_x 𝔼_C[Z_0 ψ̄_x ψ_q] = |Λ|⁻¹ ∑_{x,y} 𝔼_C[Z_0 ψ̄_x ψ_y]`. -/
theorem sum_omega_Z0_psibar_psi_col (q : Lam d L N) :
    ∑ x : Lam d L N, omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi q)) =
      ((Fintype.card (Lam d L N) : ℂ))⁻¹ *
        ∑ x : Lam d L N, ∑ y : Lam d L N,
          omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi y)) := by
  have hc : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h : ∀ y : Lam d L N, ∑ x : Lam d L N,
      omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi y)) =
      ∑ x : Lam d L N, omega (Suscept.Cov d L N msq) (Suscept.Z0 d L N V₀ * (psibar x * psi q)) := by
    intro y
    rw [← Equiv.sum_comp (Equiv.addRight (y - q))]
    refine sum_congr rfl fun x _ => ?_
    have := omega_Z0_transl hmsq hN V₀ (y - q) (psibar x * psi q)
    rw [map_mul, autAlg_psibar, autAlg_psi] at this
    simpa using this
  rw [Finset.sum_comm]
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  field_simp

end Transl

end

end PtCorr
