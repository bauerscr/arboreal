import Obs.Free

/-!
# Correlation functions from source fields (`e:s5cora`, `e:s5corb1`, `e:s5corb2`,
`e:warmupcor`, `e:warmupcor-conclusion`)

For a covariance `C` (any real matrix), a bulk potential `V^∅_0 = Vb` (an even element with
`ε(Vb) = 0`) and `⟨F⟩ = ⟨e^{-Vb} F⟩_C / ⟨e^{-Vb}⟩_C` (`avg C Vb F`, with `⟨·⟩_C = omega C` the
Gaussian expectation), let `V_0 = Vb + V^obs_0` with `V^obs_0 = -λ_a σ_a ψ̄_a - λ_b ψ_b σ̄_b`
(Case (1), `e:Vobs0-a`) resp. `-λ_a σ_a ψ̄_a ψ_a - λ_b σ_b ψ̄_b ψ_b` (Case (2), `e:Vobs0-b`),
and `G = 𝔼_C[e^{-V_0(Λ)}]|_{ψ=0} = omO C (e^{-V_0})`, an element with scalar components.
With `logObs G G_∅⁻¹ = log(G/G_∅)` (whose `a`, `ab` components are `∂_{σ_a} log G` and
`∂_{σ̄_b}∂_{σ_a} log G` resp. `∂_{σ_b}∂_{σ_a} log G` at `σ = 0`):

* `corr_one` (`e:s5cora`): `(log G)_ab = λ_a λ_b ⟨ψ̄_a ψ_b⟩`;
* `corr_two_a` (`e:s5corb1`): `(log G)_a = λ_a ⟨ψ̄_a ψ_a⟩` (no need to set `λ_b = 0`);
* `corr_two_ab` (`e:s5corb2`): `(log G)_ab = λ_a λ_b (⟨ψ̄_aψ_a ψ̄_bψ_b⟩ - ⟨ψ̄_aψ_a⟩⟨ψ̄_bψ_b⟩)`.

These hold for a general bulk potential (the text states them for `V^∅_0` of Section 3), not
only in the free case.

For the free case `Vb = 0` and a decomposition `C = ∑_{k < M} C_k` (`warmup_*`): iterating the
free observable flow (`freeIter`) with `𝔼_{C_k}[θ e^{-W}] = e^{-freeStep C_k W}` gives
`omO C (e^{-V_0}) = e^{-(u+V)_M}|_{ψ = 0}`, whence (`e:warmupcor`)
`⟨ψ̄_aψ_b⟩ = q_M/(λ_aλ_b)` (Case (1)), `⟨ψ̄_aψ_a⟩ = γ_{a,M}/λ_a`,
`⟨ψ̄_aψ_a; ψ̄_bψ_b⟩ = q_M/(λ_aλ_b)` (Case (2)), with the coupling constants `flow1`, `flow2`
of Lemma `lem:Vobs-flow-free`; explicitly (`flow2_q`) `q_M = -λ_aλ_b (∑_k C_k(a,b))²`, so
`⟨ψ̄_aψ_a; ψ̄_bψ_b⟩ = -C(a,b)²` (`warmup_conclusion`, `e:warmupcor-conclusion`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA

variable {c : Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-! ### Preliminaries -/

/-- `F ↦ 𝔼_C[θ F]|_{ψ=0}` on even elements (componentwise `⟨F_x⟩_C`). -/
def omO (C : Matrix Λ Λ ℝ) (F : OE c Λ) : OE c Λ := epsO (ECO C (thetaO F))

theorem coe_omO (C : Matrix Λ Λ ℝ) (F : OE c Λ) : (omO C F : SA c Λ) = omS C (F : SA c Λ) := rfl

theorem omega_eq_zero_of_isOdd (C : Matrix Λ Λ ℝ) {x : N Λ} (hx : Step.IsOdd x) :
    omega C x = 0 := by
  rw [omega_eq']
  refine ε_eq_zero_of_isOdd ?_
  show inv' _ = -_
  rw [← Step.EC_inv', ← theta_inv', show inv' x = -x from hx, map_neg, map_neg]

theorem omega_one (C : Matrix Λ Λ ℝ) : omega C (1 : N Λ) = 1 := by
  rw [omega_eq', map_one, EC_one, map_one]

theorem ECO_zero_thetaO (F : OE c Λ) : ECO (0 : Matrix Λ Λ ℝ) (thetaO F) = F := by
  have h : ∀ x : N Λ, EC (0 : Matrix Λ Λ ℝ) (theta x) = x := fun x => by
    rw [EC_theta, expL_eq_self]; simp [Lop_apply]
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [h]

/-- The Gaussian expectation with bulk potential: `⟨F⟩ = ⟨e^{-Vb} F⟩_C / ⟨e^{-Vb}⟩_C`. -/
def avg (C : Matrix Λ Λ ℝ) (Vb : Step.EvR Λ) (F : N Λ) : ℂ :=
  omega C ((Step.gexp (-Vb) : N Λ) * F) / omega C (Step.gexp (-Vb) : N Λ)

/-- The partition function `⟨e^{-Vb}⟩_C`. -/
def Zb (C : Matrix Λ Λ ℝ) (Vb : Step.EvR Λ) : ℂ := omega C (Step.gexp (-Vb) : N Λ)

theorem omega_neg (C : Matrix Λ Λ ℝ) (x : N Λ) : omega C (-x) = -omega C x := by
  simp [omega]

theorem omega_smul' (C : Matrix Λ Λ ℝ) (r : ℂ) (x : N Λ) : omega C (r • x) = r * omega C x := by
  simp [omega]

/-- `e^{-(Vb + W)} = e^{-Vb} (1 - W + W²/2)` for observable `W`. -/
theorem oexp_neg_emb_add {Vb : Step.EvR Λ} (hVb : ε (Vb : N Λ) = 0) {W : OE c Λ}
    (hW : bulk W = 0) :
    oexp (-(emb Vb + W)) = emb (Step.gexp (-Vb)) * (1 - W + (1 / 2 : ℂ) • W ^ 2) := by
  have h1 : ε (((-(emb Vb + W) : OE c Λ) : SA c Λ).e) = 0 := by
    show ε (-((Vb : N Λ) + (W : SA c Λ).e)) = 0
    rw [show (W : SA c Λ).e = 0 from congrArg Subtype.val hW]; simp [hVb]
  rw [oexp_eq_mul h1]
  have hb : bulk (-(emb Vb + W) : OE c Λ) = -Vb := by simp [hW]
  have hp : πobs (-(emb Vb + W) : OE c Λ) = -W := by
    rw [map_neg, map_add, πobs_emb, zero_add]
    have := eq_emb_add_πobs W
    rw [hW, map_zero, zero_add] at this
    rw [← this]
  rw [hb, hp, neg_sq]; congr 1; abel

section Corr

variable (C : Matrix Λ Λ ℝ) {Vb : Step.EvR Λ} (hVb : ε (Vb : N Λ) = 0) (a b : Λ)
include hVb

/-- The components of `G = omO C (e^{-(Vb + W)})` for observable `W`. -/
theorem omO_oexp {W : OE c Λ} (hW : bulk W = 0) :
    (omO C (oexp (-(emb Vb + W))) : SA c Λ) =
      ⟨algebraMap ℂ (N Λ) (Zb C Vb),
        algebraMap ℂ (N Λ) (-omega C ((Step.gexp (-Vb) : N Λ) * (W : SA c Λ).a)),
        algebraMap ℂ (N Λ) (-omega C ((Step.gexp (-Vb) : N Λ) * (W : SA c Λ).b)),
        algebraMap ℂ (N Λ) (omega C ((Step.gexp (-Vb) : N Λ) *
          (-(W : SA c Λ).ab + (1 / 2 : ℂ) • (c.s • ((W : SA c Λ).a * (W : SA c Λ).b) +
            (W : SA c Λ).b * (W : SA c Λ).a))))⟩ := by
  have hW0 : (W : SA c Λ).e = 0 := congrArg Subtype.val hW
  rw [oexp_neg_emb_add hVb hW, coe_omO]
  have hsq : ((W ^ 2 : OE c Λ) : SA c Λ) = ⟨0, 0, 0, c.s • ((W : SA c Λ).a * (W : SA c Λ).b) +
      (W : SA c Λ).b * (W : SA c Λ).a⟩ := by
    rw [sq]
    refine SA.ext ?_ ?_ ?_ ?_
    · rw [OE.mul_e, hW0, zero_mul]
    · rw [OE.mul_a, hW0, zero_mul, mul_zero, add_zero]
    · rw [OE.mul_b, hW0, zero_mul, mul_zero, add_zero]
    · rw [OE.mul_ab, hW0, zero_mul, mul_zero, zero_add, add_zero]
  have e1 : (((emb (Step.gexp (-Vb)) * (1 - W + (1 / 2 : ℂ) • W ^ 2) : OE c Λ)) : SA c Λ) =
      ofN (Step.gexp (-Vb) : N Λ) * ((1 : SA c Λ) - (W : SA c Λ) +
        (1 / 2 : ℂ) • ((W ^ 2 : OE c Λ) : SA c Λ)) := rfl
  rw [e1, hsq]
  refine SA.ext ?_ ?_ ?_ ?_ <;>
    simp [omS_e, omS_a, omS_b, omS_ab, hW0, Zb, Case.tau_of_even c (Step.mem_Ev.1 (Step.gexp (-Vb)).2),
      mul_add, mul_sub, mul_smul_comm, omega_smul', sub_eq_add_neg, mul_neg, omega]

omit hVb in
theorem algebraMap_EvR' (z : ℂ) :
    ((algebraMap ℂ (Step.EvR Λ) z : Step.EvR Λ) : N Λ) = algebraMap ℂ (N Λ) z := rfl

/-- `e:s5cora` (Case (1)): `∂_{σ̄_b} ∂_{σ_a} log 𝔼_C[e^{-V_0(Λ)}] = λ_a λ_b ⟨ψ̄_a ψ_b⟩`. -/
theorem corr_one (la lb : ℂ) (hZ : Zb C Vb ≠ 0) :
    ((logObs (omO C (oexp (-(emb Vb + evalO .one ⟨la, lb, 0, 0, 0, 0⟩ a b univ))))
      (algebraMap ℂ (Step.EvR Λ) (Zb C Vb)⁻¹) : OE .one Λ) : SA .one Λ).ab =
      algebraMap ℂ (N Λ) (la * lb * avg C Vb (psibar a * psi b)) := by
  have hW := bulk_evalO .one ⟨la, lb, 0, 0, 0, 0⟩ a b univ
  have hG := omO_oexp C hVb hW
  rw [logObs_ab, hG]
  simp only [coe_evalO, evalS, Coup1.evalS_a, Coup1.evalS_b, Coup1.evalS_ab, ind_pos (mem_univ _),
    ind_pos (And.intro (mem_univ a) (mem_univ b)), one_smul, neg_zero, map_zero, nr_zero,
    add_zero, Case.s_one, zero_add]
  have hodd : ∀ x : N Λ, Step.IsOdd x → omega C ((Step.gexp (-Vb) : N Λ) * x) = 0 := by
    intro x hx
    refine omega_eq_zero_of_isOdd C ?_
    show inv' _ = -_
    rw [map_mul, Step.mem_Ev.1 (Step.gexp (-Vb)).2, show inv' x = -x from hx, mul_neg]
  have h1 : omega C ((Step.gexp (-Vb) : N Λ) * ((-la) • psibar a)) = 0 :=
    hodd _ (Step.IsOdd.smul (isOdd_psibar' a) _)
  have h2 : omega C ((Step.gexp (-Vb) : N Λ) * (lb • psi b)) = 0 :=
    hodd _ (Step.IsOdd.smul (isOdd_psi' b) _)
  have e : (1 / 2 : ℂ) • ((-1 : ℂ) • ((-la) • psibar a * lb • psi b) +
      lb • psi b * (-la) • psibar a) = (la * lb) • (psibar a * psi b) := by
    simp only [smul_mul_smul_comm, psi_mul_psibar]; module
  rw [h1, h2, e, mul_smul_comm, omega_smul']
  simp only [neg_zero, map_zero, mul_zero, smul_zero, sub_zero, algebraMap_EvR', ← map_mul]
  congr 1
  rw [avg, ← Zb]
  field_simp

omit hVb in
theorem psibar_psi_comm (x y : Λ) :
    psibar y * psi y * (psibar x * psi x) = psibar x * psi x * (psibar y * psi y) :=
  mul_comm_of_even (inv'_psibar_psi y y) _

/-- `e:s5corb1` (Case (2)): `∂_{σ_a} log 𝔼_C[e^{-V_0(Λ)}] = λ_a ⟨ψ̄_a ψ_a⟩`. -/
theorem corr_two_a (la lb : ℂ) (hZ : Zb C Vb ≠ 0) :
    ((logObs (omO C (oexp (-(emb Vb + evalO .two ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ a b univ))))
      (algebraMap ℂ (Step.EvR Λ) (Zb C Vb)⁻¹) : OE .two Λ) : SA .two Λ).a =
      algebraMap ℂ (N Λ) (la * avg C Vb (psibar a * psi a)) := by
  have hW := bulk_evalO .two ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ a b univ
  rw [logObs_a, omO_oexp C hVb hW]
  simp only [coe_evalO, evalS, Coup2.evalS_a, ind_pos (mem_univ _), one_smul, neg_zero,
    map_zero, zero_sub, mul_neg, neg_neg, mul_smul_comm, omega_smul', omega_neg,
    algebraMap_EvR', ← map_mul]
  congr 1
  rw [avg, ← Zb]
  field_simp

/-- `e:s5corb2` (Case (2)): `∂_{σ_b} ∂_{σ_a} log 𝔼_C[e^{-V_0(Λ)}] =
λ_a λ_b (⟨ψ̄_aψ_a ψ̄_bψ_b⟩ - ⟨ψ̄_aψ_a⟩⟨ψ̄_bψ_b⟩)`. -/
theorem corr_two_ab (la lb : ℂ) (hZ : Zb C Vb ≠ 0) :
    ((logObs (omO C (oexp (-(emb Vb + evalO .two ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ a b univ))))
      (algebraMap ℂ (Step.EvR Λ) (Zb C Vb)⁻¹) : OE .two Λ) : SA .two Λ).ab =
      algebraMap ℂ (N Λ) (la * lb * (avg C Vb (psibar a * psi a * (psibar b * psi b)) -
        avg C Vb (psibar a * psi a) * avg C Vb (psibar b * psi b))) := by
  have hW := bulk_evalO .two ⟨la, lb, 0, 0, 0, 0, 0, 0, 0⟩ a b univ
  rw [logObs_ab, omO_oexp C hVb hW]
  simp only [coe_evalO, evalS, Coup2.evalS_a, Coup2.evalS_b, Coup2.evalS_ab, ind_pos (mem_univ _),
    ind_pos (And.intro (mem_univ a) (mem_univ b)), one_smul, neg_zero, map_zero, zero_sub, nr_zero,
    zero_div, zero_smul, sub_zero, add_zero, Case.s_two]
  have e : (0 : N Λ) + (1 / 2 : ℂ) • ((-(la • (psibar a * psi a))) * (-(lb • (psibar b * psi b))) +
      (-(lb • (psibar b * psi b))) * (-(la • (psibar a * psi a)))) =
      (la * lb) • (psibar a * psi a * (psibar b * psi b)) := by
    simp only [neg_mul_neg, smul_mul_smul_comm]
    rw [psibar_psi_comm a b]; module
  rw [e]
  simp only [mul_neg, neg_neg, mul_smul_comm, omega_smul', omega_neg, algebraMap_EvR', ← map_mul,
    one_smul]
  rw [← map_sub]
  congr 1
  simp only [avg]
  rw [← Zb]
  field_simp

end Corr

end

end Obs
