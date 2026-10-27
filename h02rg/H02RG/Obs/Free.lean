import Obs.Coupling
import Step.Coupling

/-!
# The free observable flow (Section `sec:obs-free`)

For a covariance `C` (a real matrix; no positivity is needed for the algebra) and an even
element `W` of the amended algebra:

* `ECT C F G = 𝔼_C[θF; θG] = 𝔼_C[θF θG] - 𝔼_C[θF] 𝔼_C[θG]` (the truncated expectation; the
  text's `(𝔼_{C}[V])²` is read as `(𝔼_C[θV])²`);
* `freeStep C W = 𝔼_C[θW] - ½ 𝔼_C[θW; θW]`, the map `e:Vobspt`.  We apply it to the full
  `u^obs_j + V^obs_j` (not only to `V^obs_j`): since `u^obs_j` is a constant this adds `u^obs_j`
  to `u^obs_{j+1}`, so that the coupling constants `q, γ` accumulate as in
  Lemma `lem:Vobs-flow-free` (`freeStep_add_const`).
* `ECO_thetaO_oexp_neg`: for observable `W` (`bulk W = 0`),
  `𝔼_C[θ e^{-W}] = e^{-freeStep C W}` (the identity following `e:Vobspt`).
* `freeStep_one`, `freeStep_two` (Lemma `lem:Vobs-flow-free`): for `a, b ∈ X`,
  `freeStep C (u^obs + V^obs)(X) = (u^obs + V^obs)'(X)` with the explicit new coupling
  constants `Coup1.next`, `Coup2.next`:
  * Case (1): `λ' = λ`, `r_x' = r_x`, `q_a' = q_a + ½ λ_a λ_b C(a,b) - r_a C(a,a)`,
    `q_b' = q_b + ½ λ_a λ_b C(a,b) - r_b C(b,b)`, so
    `q' = q + λ_a λ_b C(a,b) - (r_a C(a,a) + r_b C(b,b))`;
  * Case (2) (for symmetric `C(a,b) = C(b,a)`): `λ' = λ`, `r_x' = r_x`,
    `γ_x' = γ_x + λ_x C(x,x)`, `q_x' = q_x + ½ η C(a,b) - r_x C(x,x) - ½ λ_a λ_b C(a,b)²`,
    so `q' = q + η C(a,b) - (r_a C(a,a) + r_b C(b,b)) - λ_a λ_b C(a,b)²`,
    and `η' = η - 2 λ_a λ_b C(a,b)`.
  (`r` is split into `r_a, r_b` and `q` into `q_a, q_b`, see `Obs.Coupling`; the text is
  `r_a = r_b = r/2`.  On sets containing `a` and `b` only `q = q_a + q_b` is determined; the
  split of the `q` recursion is the one of the block-additive evaluation, `Obs.MapEval`.)

**Deviation (sign of the `r` terms).**  With the conventions of Definition `def:cVobs`
(`u^obs = -σσ q`, `V^obs ∋ +σσ (r_a ψ̄_aψ_a + r_b ψ̄_bψ_b)`) and
`𝔼_C θ(ψ̄_xψ_x) = ψ̄_xψ_x + C(x,x)` (as for `γ_x`, whose recursion agrees with the text), the
constant produced by the `r` term is `+σσ (r_a C(a,a) + r_b C(b,b))`, i.e.
`q' ∋ -(r_a C(a,a) + r_b C(b,b)) = -r C(0,0)` for `r_a = r_b = r/2` and a translation invariant
`C`; the text has `+r C(0,0)`.  (This is immaterial for the free flow, which starts with
`r = 0`.)  We state the recursion with `C(a,a)`, `C(b,b)` separately (no translation invariance
needed).

* `expL_quartic`: the Wick formula
  `𝔼_C θ (ψ̄_aψ_a ψ̄_bψ_b) = (ψ̄_aψ_a + C_aa)(ψ̄_bψ_b + C_bb) - C_ab ψ̄_bψ_a - C_ba ψ̄_aψ_b
    - C_ab C_ba`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### Elements with only an `ab` component -/

/-- `F = σ_a σ̄_b F_ab` (resp. `σ_a σ_b F_ab`). -/
def IsAB (F : OE c Λ) : Prop :=
  (F : SA c Λ).e = 0 ∧ (F : SA c Λ).a = 0 ∧ (F : SA c Λ).b = 0

theorem IsAB.bulk_eq_zero {F : OE c Λ} (hF : IsAB F) : bulk F = 0 := Subtype.ext hF.1

theorem isAB_mul {F G : OE c Λ} (hF : bulk F = 0) (hG : bulk G = 0) : IsAB (F * G) := by
  have h := mul_of_isObs ((isObs_iff_bulk F).2 hF) ((isObs_iff_bulk G).2 hG)
  refine ⟨?_, ?_, ?_⟩ <;> simp [show ((F * G : OE c Λ) : SA c Λ) = (F : SA c Λ) * G from rfl, h]

theorem IsAB.mul_eq_zero {F G : OE c Λ} (hF : IsAB F) (hG : bulk G = 0) : F * G = 0 := by
  have hG' : (G : SA c Λ).e = 0 := congrArg Subtype.val hG
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · show ((F : SA c Λ) * G).e = 0; simp [hF.1]
  · show ((F : SA c Λ) * G).a = 0; simp [hF.1, hF.2.1, hG']
  · show ((F : SA c Λ) * G).b = 0; simp [hF.1, hF.2.2, hG']
  · show ((F : SA c Λ) * G).ab = 0; simp [hF.1, hF.2.1, hF.2.2, hG']

theorem IsAB.sub {F G : OE c Λ} (hF : IsAB F) (hG : IsAB G) : IsAB (F - G) := by
  refine ⟨?_, ?_, ?_⟩
  · show (F : SA c Λ).e - (G : SA c Λ).e = 0; rw [hF.1, hG.1, sub_zero]
  · show (F : SA c Λ).a - (G : SA c Λ).a = 0; rw [hF.2.1, hG.2.1, sub_zero]
  · show (F : SA c Λ).b - (G : SA c Λ).b = 0; rw [hF.2.2, hG.2.2, sub_zero]

theorem IsAB.add {F G : OE c Λ} (hF : IsAB F) (hG : IsAB G) : IsAB (F + G) := by
  refine ⟨?_, ?_, ?_⟩
  · show (F : SA c Λ).e + (G : SA c Λ).e = 0; rw [hF.1, hG.1, add_zero]
  · show (F : SA c Λ).a + (G : SA c Λ).a = 0; rw [hF.2.1, hG.2.1, add_zero]
  · show (F : SA c Λ).b + (G : SA c Λ).b = 0; rw [hF.2.2, hG.2.2, add_zero]

theorem IsAB.smul {F : OE c Λ} (hF : IsAB F) (r : ℂ) : IsAB (r • F) := by
  refine ⟨?_, ?_, ?_⟩
  · show r • (F : SA c Λ).e = 0; rw [hF.1, smul_zero]
  · show r • (F : SA c Λ).a = 0; rw [hF.2.1, smul_zero]
  · show r • (F : SA c Λ).b = 0; rw [hF.2.2, smul_zero]

theorem IsAB.ECO_thetaO {F : OE c Λ} (hF : IsAB F) (C : Matrix Λ Λ ℝ) :
    IsAB (ECO C (thetaO F)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hF.1, hF.2.1, hF.2.2]

theorem IsAB.ECO {F : OE c (Λ ⊕ Λ)} (hF : IsAB F) (C : Matrix Λ Λ ℝ) : IsAB (ECO C F) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hF.1, hF.2.1, hF.2.2]

theorem isAB_thetaO_mul {F G : OE c Λ} (hF : bulk F = 0) (hG : bulk G = 0) :
    IsAB (thetaO F * thetaO G) :=
  isAB_mul (by rw [bulk_thetaO, hF, map_zero]) (by rw [bulk_thetaO, hG, map_zero])

theorem bulk_ECO_thetaO {F : OE c Λ} (hF : bulk F = 0) (C : Matrix Λ Λ ℝ) :
    bulk (ECO C (thetaO F)) = 0 := by
  rw [bulk_ECO, bulk_thetaO, hF, map_zero, map_zero]

/-! ### The map `e:Vobspt` -/

/-- The truncated expectation `𝔼_C[θF; θG] = 𝔼_C[θF θG] - 𝔼_C[θF] 𝔼_C[θG]`. -/
def ECT (C : Matrix Λ Λ ℝ) (F G : OE c Λ) : OE c Λ :=
  ECO C (thetaO F * thetaO G) - ECO C (thetaO F) * ECO C (thetaO G)

/-- The free observable flow `e:Vobspt`: `u_{j+1} + V_{j+1} = 𝔼_C θW - ½ 𝔼_C[θW; θW]`. -/
def freeStep (C : Matrix Λ Λ ℝ) (W : OE c Λ) : OE c Λ :=
  ECO C (thetaO W) - (1 / 2 : ℂ) • ECT C W W

theorem isAB_ECT (C : Matrix Λ Λ ℝ) {F G : OE c Λ} (hF : bulk F = 0) (hG : bulk G = 0) :
    IsAB (ECT C F G) :=
  ((isAB_thetaO_mul hF hG).ECO C).sub (isAB_mul (bulk_ECO_thetaO hF C) (bulk_ECO_thetaO hG C))

theorem bulk_freeStep (C : Matrix Λ Λ ℝ) {W : OE c Λ} (hW : bulk W = 0) :
    bulk (freeStep C W) = 0 := by
  rw [freeStep, map_sub, map_smul, bulk_ECO_thetaO hW, (isAB_ECT C hW hW).bulk_eq_zero, smul_zero,
    sub_zero]

/-- `𝔼_C[θ e^{-W}] = e^{-u_{j+1} - V_{j+1}}` for observable `W`. -/
theorem ECO_thetaO_oexp_neg (C : Matrix Λ Λ ℝ) {W : OE c Λ} (hW : bulk W = 0) :
    ECO C (thetaO (oexp (-W))) = oexp (-freeStep C W) := by
  have hW' : bulk (-W) = 0 := by rw [map_neg, hW, neg_zero]
  obtain ⟨A, hAd⟩ : ∃ A, A = ECO C (thetaO W) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ECO C (thetaO W * thetaO W) := ⟨_, rfl⟩
  have hA : bulk A = 0 := hAd ▸ bulk_ECO_thetaO hW C
  have hB : IsAB B := hBd ▸ (isAB_thetaO_mul hW hW).ECO C
  have hD : IsAB (-(1 / 2 : ℂ) • B + (1 / 2 : ℂ) • (A * A)) :=
    (hB.smul _).add ((isAB_mul hA hA).smul _)
  have hfs : freeStep C W = A + (-(1 / 2 : ℂ) • B + (1 / 2 : ℂ) • (A * A)) := by
    rw [freeStep, ECT, ← hAd, ← hBd]; module
  have hsq : freeStep C W ^ 2 = A ^ 2 := by
    have h1 : (-(1 / 2 : ℂ) • B + (1 / 2 : ℂ) • (A * A)) * A = 0 := hD.mul_eq_zero hA
    have h2 : (-(1 / 2 : ℂ) • B + (1 / 2 : ℂ) • (A * A)) *
        (-(1 / 2 : ℂ) • B + (1 / 2 : ℂ) • (A * A)) = 0 := hD.mul_eq_zero hD.bulk_eq_zero
    rw [hfs]
    linear_combination (2 : OE c Λ) * h1 + h2
  have hfs0 : bulk (-freeStep C W) = 0 := by rw [map_neg, bulk_freeStep C hW, neg_zero]
  rw [oexp_of_obs hW', oexp_of_obs hfs0, neg_sq, neg_sq, hsq]
  simp only [map_add, map_smul, map_one, map_neg, map_pow, ECO_one]
  rw [sq, sq, hfs, ← hAd, ← hBd]
  module

/-! ### Wick formulas -/

section Wick

local notation "ι" => ExteriorAlgebra.ι ℂ

variable (C : Matrix Λ Λ ℝ)

theorem expL_of_cube' (F : N Λ) (h : Lop C (Lop C (Lop C F)) = 0) :
    expL C F = F + Lop C F + (1 / 2 : ℂ) • Lop C (Lop C F) := by
  have hk : (Lop C ^ 3) • F = 0 := by
    rw [Module.End.smul_def, pow_succ, pow_two, Module.End.mul_apply, Module.End.mul_apply]
    exact h
  have := IsNilpotent.exp_smul_eq_sum hk (Lop_isNilpotent C)
  rw [Module.End.smul_def] at this
  rw [expL, this]
  simp only [sum_range_succ, sum_range_zero, Module.End.smul_def, pow_zero, pow_one, pow_two,
    Module.End.mul_apply, Module.End.one_apply]
  rw [← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ, ← Rat.cast_smul_eq_qsmul ℂ]
  norm_num

theorem Bf_qp' (u w : Λ) : Step.Coup.Bf C (ev (u, -1)) (ev (w, 1)) = (C u w : ℂ) := by
  simp [Step.Coup.Bf, ev, Pi.single_apply, Prod.ext_iff, Loc.units_ne.symm]

theorem Bf_pq' (u w : Λ) : Step.Coup.Bf C (ev (u, 1)) (ev (w, -1)) = -(C w u : ℂ) := by
  simp [Step.Coup.Bf, ev, Pi.single_apply, Prod.ext_iff, Loc.units_ne.symm]

theorem Bf_pp' (u w : Λ) : Step.Coup.Bf C (ev (u, 1)) (ev (w, 1)) = 0 := by
  simp [Step.Coup.Bf, ev, Pi.single_apply, Prod.ext_iff, Loc.units_ne.symm]

theorem Bf_qq' (u w : Λ) : Step.Coup.Bf C (ev (u, -1)) (ev (w, -1)) = 0 := by
  simp [Step.Coup.Bf, ev, Pi.single_apply, Prod.ext_iff]

theorem expL_algebraMap (r : ℂ) : expL C (algebraMap ℂ (N Λ) r) = algebraMap ℂ (N Λ) r :=
  expL_eq_self C (Step.Coup.Lop_algebraMap C r)

theorem expL_psibar (x : Λ) : expL C (psibar x) = psibar x :=
  expL_eq_self C (Step.Coup.Lop_ι C _)

theorem expL_psi (x : Λ) : expL C (psi x) = psi x :=
  expL_eq_self C (Step.Coup.Lop_ι C _)

theorem expL_psibar_psi (x y : Λ) :
    expL C (psibar x * psi y) = psibar x * psi y + algebraMap ℂ (N Λ) (C x y : ℂ) := by
  rw [← EC_theta, EC_theta_psibar_psi]

theorem psi_mul_psibar (x y : Λ) : psi y * psibar x = -(psibar x * psi y) :=
  Grassmann.ι_anticomm _ _

theorem Lop_psibar_psi (x y : Λ) :
    Lop C (psibar x * psi y) = (C x y : ℂ) • (1 : N Λ) := by
  rw [psibar, psi, ψ, ψ, Step.Coup.Lop_ι2, Bf_qp']

/-- The Wick formula for `ψ̄_a ψ_a ψ̄_b ψ_b`. -/
theorem expL_quartic (a b : Λ) :
    expL C (psibar a * psi a * (psibar b * psi b)) =
      (psibar a * psi a + algebraMap ℂ (N Λ) (C a a : ℂ)) *
          (psibar b * psi b + algebraMap ℂ (N Λ) (C b b : ℂ)) -
        (C a b : ℂ) • (psibar b * psi a) - (C b a : ℂ) • (psibar a * psi b) -
        algebraMap ℂ (N Λ) ((C a b : ℂ) * (C b a : ℂ)) := by
  have hL : Lop C (psibar a * psi a * (psibar b * psi b)) =
      (C b b : ℂ) • (psibar a * psi a) + (C a a : ℂ) • (psibar b * psi b) -
        (C b a : ℂ) • (psibar a * psi b) - (C a b : ℂ) • (psibar b * psi a) := by
    rw [mul_assoc]
    simp only [psibar, psi, ψ]
    rw [Step.Coup.Lop_ι4, Bf_qp', Bf_pq', Bf_pp', Bf_qq', Bf_qp', Bf_qp']
    have e : ι (ev (a, 1)) * ι (ev (b, -1)) = -(ι (ev (b, -1)) * ι (ev (a, 1))) :=
      Grassmann.ι_anticomm _ _
    rw [e]
    simp only [zero_smul, sub_zero, add_zero, smul_neg, neg_smul]
    abel
  have hL2 : Lop C (Lop C (psibar a * psi a * (psibar b * psi b))) =
      ((C b b : ℂ) * C a a + C a a * C b b - C b a * C a b - C a b * C b a) • (1 : N Λ) := by
    rw [hL]
    simp only [map_add, map_sub, map_smul, Lop_psibar_psi, smul_smul]
    module
  have hL3 : Lop C (Lop C (Lop C (psibar a * psi a * (psibar b * psi b)))) = 0 := by
    rw [hL2, map_smul, Step.Coup.Lop_one', smul_zero]
  rw [expL_of_cube' C _ hL3, hL2, hL]
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_smul_comm, one_mul,
    mul_one, smul_mul_assoc, mul_smul_comm]
  module

end Wick

/-! ### Components of the free flow -/

section Comp

variable (C : Matrix Λ Λ ℝ)

theorem expL_zero : expL C (0 : N Λ) = 0 := map_zero _

theorem coe_freeStep (W : OE c Λ) : (freeStep C W : SA c Λ) =
    ECS C (thetaS (W : SA c Λ)) - (1 / 2 : ℂ) • (ECS C (thetaS ((W : SA c Λ) * (W : SA c Λ))) -
      ECS C (thetaS (W : SA c Λ)) * ECS C (thetaS (W : SA c Λ))) := by
  rw [map_mul]; rfl

theorem freeStep_e {W : OE c Λ} (hW : bulk W = 0) : (freeStep C W : SA c Λ).e = 0 :=
  congrArg Subtype.val (bulk_freeStep C hW)

theorem freeStep_a {W : OE c Λ} (hW : bulk W = 0) :
    (freeStep C W : SA c Λ).a = expL C (W : SA c Λ).a := by
  have h0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [coe_freeStep]; simp [ECS_thetaS, h0, expL_zero]

theorem freeStep_b {W : OE c Λ} (hW : bulk W = 0) :
    (freeStep C W : SA c Λ).b = expL C (W : SA c Λ).b := by
  have h0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [coe_freeStep]; simp [ECS_thetaS, h0, expL_zero]

theorem freeStep_ab {W : OE c Λ} (hW : bulk W = 0) :
    (freeStep C W : SA c Λ).ab = expL C (W : SA c Λ).ab - (1 / 2 : ℂ) •
      (expL C (c.tau (W : SA c Λ).a * (W : SA c Λ).b + c.s • (c.tau (W : SA c Λ).b * (W : SA c Λ).a)) -
        (c.tau (expL C (W : SA c Λ).a) * expL C (W : SA c Λ).b +
          c.s • (c.tau (expL C (W : SA c Λ).b) * expL C (W : SA c Λ).a))) := by
  have h0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [coe_freeStep]; simp [ECS_thetaS, h0, expL_zero]
  rw [Case.tau_comm c theta theta_inv', Case.tau_comm c theta theta_inv', ← map_mul, ← map_mul,
    EC_theta, EC_theta]

end Comp

/-! ### Lemma `lem:Vobs-flow-free` -/

/-- The new coupling constants in Case (1), with `c_ab = C(a,b)`, `c_aa = C(a,a)`,
`c_bb = C(b,b)`. -/
def Coup1.next (V : Coup1) (cab caa cbb : ℂ) : Coup1 :=
  ⟨V.la, V.lb, V.qa + V.la * V.lb * cab / 2 - V.ra * caa,
    V.qb + V.la * V.lb * cab / 2 - V.rb * cbb, V.ra, V.rb⟩

/-- The new coupling constants in Case (2). -/
def Coup2.next (V : Coup2) (cab caa cbb : ℂ) : Coup2 :=
  ⟨V.la, V.lb, V.ga + V.la * caa, V.gb + V.lb * cbb,
    V.qa + V.eta * cab / 2 - V.ra * caa - V.la * V.lb * cab ^ 2 / 2,
    V.qb + V.eta * cab / 2 - V.rb * cbb - V.la * V.lb * cab ^ 2 / 2,
    V.eta - 2 * V.la * V.lb * cab, V.ra, V.rb⟩

/-- Lemma `lem:Vobs-flow-free`, Case (1). -/
theorem freeStep_one (C : Matrix Λ Λ ℝ) (V : Coup1) {a b : Λ} {X : Finset Λ} (ha : a ∈ X)
    (hb : b ∈ X) :
    freeStep C (evalO .one V a b X) =
      evalO .one (V.next (C a b) (C a a) (C b b)) a b X := by
  have hW := bulk_evalO .one V a b X
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [freeStep_e C hW, coe_evalO]; simp [evalS]
  · rw [freeStep_a C hW, coe_evalO, coe_evalO]
    simp [evalS, Coup1.next, ha, expL_psibar]
  · rw [freeStep_b C hW, coe_evalO, coe_evalO]
    simp [evalS, Coup1.next, hb, expL_psi]
  · rw [freeStep_ab C hW, coe_evalO, coe_evalO]
    simp only [evalS, Coup1.evalS_a, Coup1.evalS_b, Coup1.evalS_ab, Coup1.next, ind_pos ha,
      ind_pos hb, ind_pos (And.intro ha hb), one_smul, map_smul, map_neg, map_add,
      expL_psibar, expL_psi, expL_algebraMap, Case.tau_one, isOdd_psibar', isOdd_psi',
      nr, expL_psibar_psi, Case.s_one]
    simp only [smul_mul_smul_comm, neg_mul, mul_neg, neg_neg, smul_neg, neg_smul,
      psi_mul_psibar, map_mul, expL_psibar_psi, expL_psibar, expL_psi]
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, expL_psibar_psi, map_neg,
      Algebra.algebraMap_eq_smul_one]
    module

/-- Lemma `lem:Vobs-flow-free`, Case (2), for `C(a, b) = C(b, a)`. -/
theorem freeStep_two (C : Matrix Λ Λ ℝ) (V : Coup2) {a b : Λ} {X : Finset Λ} (ha : a ∈ X)
    (hb : b ∈ X) (hC : C a b = C b a) :
    freeStep C (evalO .two V a b X) =
      evalO .two (V.next (C a b) (C a a) (C b b)) a b X := by
  have hW := bulk_evalO .two V a b X
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [freeStep_e C hW, coe_evalO]; simp [evalS]
  · rw [freeStep_a C hW, coe_evalO, coe_evalO]
    simp only [evalS, Coup2.evalS_a, Coup2.next, ind_pos ha, one_smul, map_sub, map_smul,
      expL_algebraMap, expL_psibar_psi]
    simp only [Algebra.algebraMap_eq_smul_one]; module
  · rw [freeStep_b C hW, coe_evalO, coe_evalO]
    simp only [evalS, Coup2.evalS_b, Coup2.next, ind_pos hb, one_smul, map_sub, map_smul,
      expL_algebraMap, expL_psibar_psi]
    simp only [Algebra.algebraMap_eq_smul_one]; module
  · rw [freeStep_ab C hW, coe_evalO, coe_evalO]
    simp only [evalS, Coup2.evalS_a, Coup2.evalS_b, Coup2.evalS_ab, Coup2.next, ind_pos ha,
      ind_pos hb, ind_pos (And.intro ha hb), one_smul, Case.tau_two, Case.s_two]
    have hba : psibar b * psi b * (psibar a * psi a) = psibar a * psi a * (psibar b * psi b) :=
      (mul_comm_of_even (inv'_psibar_psi b b) _)
    simp only [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, smul_mul_smul_comm,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hba, nr, nx]
    simp only [map_add, map_sub, map_smul, expL_psibar_psi, expL_quartic, Step.Coup.Lop_one',
      expL_eq_self C (Step.Coup.Lop_one' C), Algebra.algebraMap_eq_smul_one, hC]
    simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, hba]
    module

end

end Obs
