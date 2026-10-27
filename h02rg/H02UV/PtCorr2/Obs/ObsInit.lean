import PtCorr2.Obs.ObsChain
import PtCorr2.Zero.ZeroInit
import Obs2.Pair.CoalHist

/-!
# The initial object with sources and the correlations (`sec:corr`, observables)

The initial observable state `obsInit c V P` (`V^{obs}_0(B) = (u^{obs} + V^{obs})(B)`, `𝒲 = K = 0`)
along a trajectory started at `(b, μ₀, 0)`:

* `ZhO_zero_eq`: `Z_0^{obs} = Z_0 e^{-E}`, `E = ∑_B (u^{obs} + V^{obs})(B)` (bulk `Z_0 = Zh R 0 t`);
* the components of the Gaussian integral with sources at scale `0`:
  - bulk: `⟨Z_0⟩_{Γ_0}` (`omegaCO_ZhO_zero_e`);
  - Case (2), `σ_a`: `⟨Z_0 (γ_a + μ_a ψ̄_aψ_a)⟩_{Γ_0}` (**`omegaCO_ZhO_zero_two`**), i.e. with
    `γ_a = 0`, `μ_a = 1` the unnormalised one-point function `⟨ψ̄_aψ_a Z_0⟩`;
  - Case (1), `σ_aσ̄_b` (no `ab` couplings): `μ_aμ_b ⟨Z_0 ψ̄_aψ_b⟩_{Γ_0}`
    (**`omegaCO_ZhO_zero_one`**), the unnormalised two-point function.
* **`thm_obs_chain_onept`**, **`thm_obs_chain_twopt`**: combined with `hist_omegaO_traj`, these
  correlations (times `⟨Z_0⟩`) are the corresponding components of the RG product
  `∏_j [det_j e^{-u_{j+1}}] · det e^{-u_N} ⟨F_N^{obs}⟩_{t_raw Q}`, along every trajectory with the
  hypotheses of `hist_omega_traj` and the locality hypothesis `OLocH` at the steps `j ≤ N_h`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

/-! ### Generalities -/

section Gen

variable {c : Obs.Case} {L N : ℕ} [NeZero L]

theorem KextO_zeroAct (j : ℕ) {Z : Finset (Lam 2 L N)} (hZ : Z.Nonempty) :
    KextO j (0 : OAct c 2 L N) Z = 0 := by
  rw [KextO]
  obtain ⟨x, hx⟩ := hZ
  have : (Comp j Z).Nonempty := ⟨compOf j Z (blk j x), mem_image.2 ⟨_, blk_mem_blocks hx, rfl⟩⟩
  obtain ⟨c', hc⟩ := this
  exact prod_eq_zero hc rfl

theorem gZO_zeroK (j : ℕ) (I : OFam c 2 L N) :
    gZO j I (0 : OAct c 2 L N) = bpowO j I univ := by
  rw [gZO, sum_eq_single (∅ : Finset (Lam 2 L N))]
  · rw [KextO_empty, mul_one, sdiff_empty]
  · intro X _ hX
    rw [KextO_zeroAct j (Finset.nonempty_iff_ne_empty.2 hX), mul_zero]
  · intro h
    exact absurd (mem_Pj.2 ⟨empty_subset _, isPolymer_empty j⟩) h

theorem sum_ind_block (j : ℕ) (a : Lam 2 L N) :
    ∑ p ∈ blockIdx (L := L) (N := N) j, ind (a ∈ blockSet (L := L) (N := N) j p) = 1 := by
  rw [sum_eq_single (blk j a)]
  · rw [ind, if_pos (mem_blockSet_blk j a)]
  · intro p _ hp
    rw [ind, if_neg]
    intro h
    exact hp (mem_blockSet.1 h).symm
  · intro h
    exact absurd (mem_image.2 ⟨a, mem_univ _, rfl⟩) h

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem oexp_obs_e {F : OE c Λ} (hF : bulk F = 0) : ((oexp F : OE c Λ) : SA c Λ).e = 1 := by
  have he := e_eq_zero_of_bulk hF
  rw [oexp_of_obs hF, pow_two]
  simp [he]

theorem oexp_obs_a {F : OE c Λ} (hF : bulk F = 0) :
    ((oexp F : OE c Λ) : SA c Λ).a = (F : SA c Λ).a := by
  have he := e_eq_zero_of_bulk hF
  rw [oexp_of_obs hF, pow_two]
  simp [he]

theorem oexp_obs_ab {F : OE c Λ} (hF : bulk F = 0) :
    ((oexp F : OE c Λ) : SA c Λ).ab = (F : SA c Λ).ab +
      (1 / 2 : ℂ) • (c.s • ((F : SA c Λ).a * (F : SA c Λ).b) + (F : SA c Λ).b * (F : SA c Λ).a) := by
  have he := e_eq_zero_of_bulk hF
  rw [oexp_of_obs hF, pow_two]
  simp [he]
  simp only [c.tau_of_par F.par_a, c.tau_of_par F.par_b, smul_mul_assoc, smul_smul, Case.s_mul_s,
    one_smul]

/-- The Gaussian integral of `Z F` with bulk `Z`, componentwise. -/
theorem omegaCO_emb_mul_e (Γ : Matrix Λ Λ ℂ) (Z : EvR Λ) (G : OE c Λ) :
    ((omegaCO Γ (emb Z * G) : OE c Λ) : SA c Λ).e =
      algebraMap ℂ (Grassmann.N Λ) (omegaC Γ ((Z : Grassmann.N Λ) * (G : SA c Λ).e)) := by
  rw [omegaCO_e, OE.mul_e, coe_emb, ofN_e]

theorem omegaCO_emb_mul_a (Γ : Matrix Λ Λ ℂ) (Z : EvR Λ) (G : OE c Λ) :
    ((omegaCO Γ (emb Z * G) : OE c Λ) : SA c Λ).a =
      algebraMap ℂ (Grassmann.N Λ) (omegaC Γ ((Z : Grassmann.N Λ) * (G : SA c Λ).a)) := by
  rw [omegaCO_a, OE.mul_a, coe_emb, ofN_e, ofN_a, zero_mul, add_zero]

theorem omegaCO_emb_mul_ab (Γ : Matrix Λ Λ ℂ) (Z : EvR Λ) (G : OE c Λ) :
    ((omegaCO Γ (emb Z * G) : OE c Λ) : SA c Λ).ab =
      algebraMap ℂ (Grassmann.N Λ) (omegaC Γ ((Z : Grassmann.N Λ) * (G : SA c Λ).ab)) := by
  rw [omegaCO_ab, OE.mul_ab, coe_emb, ofN_e, ofN_a, ofN_b, ofN_ab, zero_mul, zero_mul, zero_mul,
    smul_zero, add_zero, add_zero, add_zero]

end Gen

/-! ### The initial object -/

section Init

variable {c : Obs.Case} {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N)

/-- **`Z_0^{obs} = Z_0 e^{-∑_B V^{obs}_0(B)}`** for an observable initial state with
`𝒲^{obs} = K^{obs} = 0`, along a history started at `(b, μ₀, 0)`. -/
theorem ZhO_zero_eq (o₀ : ObsSt c L N) (ho₀ : o₀.IsObs) (hW : o₀.W = 0) (hK : o₀.K = 0)
    (t : Hist.Seq (Xs R)) {b μ₀ : ℝ} (ht : t 0 = (b, μ₀, 0)) :
    ZhO R P o₀ 0 t =
      emb (Zh R 0 t) * oexp (-(∑ p ∈ blockIdx (L := L) (N := N) 0, o₀.V p)) := by
  have hX : (t 0).2.2 = 0 := by rw [ht]
  have hK0 : (embF (0 : Act 2 L N) + o₀.K : OAct c 2 L N) = 0 := by
    rw [hK]; funext Y; simp [embF]
  have hnil : ∀ p ∈ blockIdx (L := L) (N := N) 0, IsNilpotent (-o₀.V p) := fun p _ =>
    isNilpotent_of_obs (by rw [map_neg, ho₀.V p, neg_zero])
  unfold ZhO Zh
  rw [show obsHist R P o₀ 0 t = o₀ from rfl, hX, rawD_zeroX, rawK_zeroX, ZinO, hK0, gZO_zeroK, Zin, gZ_zeroK, ← sum_neg_distrib,
    ← (prod_oexp_nil _ _ hnil).2, bpowO, bpow, map_prod,
    show blocks 0 (univ : Finset (Lam 2 L N)) = blockIdx (L := L) (N := N) 0 from rfl,
    ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have h1 : ε ((stVf R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1 p : EvR (Lam 2 L N)) :
      Alg 2 L N) = 0 := eps_VfamL 0 _ p
  have hε : ε ((stVf R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1 p +
      stDelta R 0 (rawHist R 0 t) p : EvR (Lam 2 L N)) : Alg 2 L N) = 0 := by
    rw [AddMemClass.coe_add, map_add, h1, eps_stDelta, add_zero]
  show oexp (-(emb (stVf R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1 p +
      stDelta R 0 (rawHist R 0 t) p) + o₀.V p)) *
      (1 + (emb (((rawHist R 0 t).Wl + 0) p) + o₀.W p)) =
    emb (gexp (-(stVf R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1 p +
      stDelta R 0 (rawHist R 0 t) p)) * (1 + ((rawHist R 0 t).Wl + 0) p)) * oexp (-o₀.V p)
  rw [show -(emb (stVf R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1 p + stDelta R 0 (rawHist R 0 t) p) +
      o₀.V p) = emb (-(stVf R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1 p +
        stDelta R 0 (rawHist R 0 t) p)) + -o₀.V p by rw [map_neg]; abel,
    oexp_add (isNilpotent_emb (eps_neg_coe hε)) (hnil p hp),
    hW, map_mul, emb_gexp _ (eps_neg_coe hε), map_add, map_one]
  simp only [Pi.zero_apply, add_zero]
  ring

theorem bulk_sum_evalFam (c : Obs.Case) (V : OCoup c) :
    bulk (∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit c V P).V p) = 0 := by
  rw [map_sum]; exact sum_eq_zero fun p _ => bulk_evalO c V _ _ _

/-- The bulk component at scale `0`. -/
theorem omegaCO_ZhO_zero_e (c : Obs.Case) (V : OCoup c) (t : Hist.Seq (Xs R)) {b μ₀ : ℝ}
    (ht : t 0 = (b, μ₀, 0)) (Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    ((omegaCO Γ (ZhO R P (obsInit c V P) 0 t) : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e =
      algebraMap ℂ (Alg 2 L N) (omegaC Γ (Zh R 0 t : Alg 2 L N)) := by
  rw [ZhO_zero_eq R P _ (obsInit_isObs c V P) rfl rfl t ht, omegaCO_emb_mul_e,
    oexp_obs_e (by rw [map_neg, bulk_sum_evalFam, neg_zero]), mul_one]

/-- **Case (2), the `σ_a` component at scale `0`**: `⟨Z_0(γ_a + μ_aψ̄_aψ_a)⟩_{Γ}`. -/
theorem omegaCO_ZhO_zero_two (V : OCoup2) (t : Hist.Seq (Xs R)) {b μ₀ : ℝ}
    (ht : t 0 = (b, μ₀, 0)) (Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    ((omegaCO Γ (ZhO R P (obsInit .two V P) 0 t) : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).a =
      algebraMap ℂ (Alg 2 L N) (omegaC Γ ((Zh R 0 t : Alg 2 L N) *
        (algebraMap ℂ (Alg 2 L N) V.ga + V.mua • (psibar P.a * psi P.a)))) := by
  rw [ZhO_zero_eq R P _ (obsInit_isObs .two V P) rfl rfl t ht, omegaCO_emb_mul_a,
    oexp_obs_a (by rw [map_neg, bulk_sum_evalFam, neg_zero])]
  congr 3
  rw [NegMemClass.coe_neg, neg_a, AddSubmonoidClass.coe_finsetSum, sum_a]
  show -∑ p ∈ blockIdx (L := L) (N := N) 0, ind (P.a ∈ blockSet (L := L) (N := N) 0 p) •
      (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-V.ga) - V.mua • (psibar P.a * psi P.a)) = _
  rw [← sum_smul, sum_ind_block, one_smul, map_neg]
  abel

/-- **Case (1), the `σ_aσ̄_b` component at scale `0`** (no `ab` couplings):
`μ_aμ_b ⟨Z_0 ψ̄_aψ_b⟩_{Γ}`. -/
theorem omegaCO_ZhO_zero_one (V : OCoup1) (hV : AbFree .one V) (t : Hist.Seq (Xs R))
    {b μ₀ : ℝ} (ht : t 0 = (b, μ₀, 0)) (Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    ((omegaCO Γ (ZhO R P (obsInit .one V P) 0 t) : OE .one (Lam 2 L N)) :
        SA .one (Lam 2 L N)).ab =
      algebraMap ℂ (Alg 2 L N) (omegaC Γ ((Zh R 0 t : Alg 2 L N) *
        ((V.mua * V.mub) • (psibar P.a * psi P.b)))) := by
  have hb : bulk (-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .one V P).V p) = 0 := by
    rw [map_neg, bulk_sum_evalFam, neg_zero]
  rw [ZhO_zero_eq R P _ (obsInit_isObs .one V P) rfl rfl t ht, omegaCO_emb_mul_ab,
    oexp_obs_ab hb]
  congr 3
  have ea : ((-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .one V P).V p :
      OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).a = V.mua • psibar P.a := by
    rw [NegMemClass.coe_neg, neg_a, AddSubmonoidClass.coe_finsetSum, sum_a]
    show -∑ p ∈ blockIdx (L := L) (N := N) 0, ind (P.a ∈ blockSet (L := L) (N := N) 0 p) •
      (-V.mua • psibar P.a) = _
    rw [← sum_smul, sum_ind_block, one_smul, neg_smul, neg_neg]
  have eb : ((-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .one V P).V p :
      OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).b = -(V.mub • psi P.b) := by
    rw [NegMemClass.coe_neg, neg_b, AddSubmonoidClass.coe_finsetSum, sum_b]
    show -∑ p ∈ blockIdx (L := L) (N := N) 0, ind (P.b ∈ blockSet (L := L) (N := N) 0 p) •
      (V.mub • psi P.b) = _
    rw [← sum_smul, sum_ind_block, one_smul]
  have eab : ((-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .one V P).V p :
      OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).ab = 0 := by
    rw [NegMemClass.coe_neg, neg_ab, AddSubmonoidClass.coe_finsetSum, sum_ab, neg_eq_zero]
    exact sum_eq_zero fun p _ => evalO_ab .one hV _ _ _
  have hc : psi P.b * psibar P.a = -(psibar P.a * psi P.b) := ψ_anticomm _ _
  rw [ea, eb, eab, Case.s_one, zero_add, neg_mul, mul_neg, smul_mul_smul_comm,
    smul_mul_smul_comm, hc]
  module

end Init

/-! ### The correlations along the trajectories -/

section Traj

variable {c : Obs.Case} {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N)

/-- The right side of `hist_omegaO_traj` (the RG product with sources). -/
def rgProdO (o₀ : ObsSt c L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  (∏ j ∈ range (Nh + 1), chO R P o₀ j t) *
    (detStep R (Nh + 1) (histOut R Nh t).st • (uOutNO R P (Nh + 1) (histOut R Nh t).st
      (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
      (obsHist R P o₀ (Nh + 1) t) *
      omegaCO (cstC (Lam 2 L N) (zmRaw R (Nh + 1) (Function.update (histOut R Nh t).st.ζ
        (Nh + 1) (stZeta R (histOut R Nh t).st)) / Fintype.card (Lam 2 L N)))
        (finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
          (histOut R Nh t).D (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t))))

set_option maxHeartbeats 1000000 in
/-- **The one-point function along a trajectory** (Case (2), `σ_a`): with the hypotheses of
`hist_omegaO_traj` for `o₀ = obsInit .two V P`,
`⟨Z_0⟩_{Γ_0} = (rgProdO)_∅` and `⟨Z_0(γ_a + μ_aψ̄_aψ_a)⟩_{Γ_0} = (rgProdO)_a`. -/
theorem thm_obs_chain_onept {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (V : OCoup2)
    (hloc : ∀ j ≤ Nh, OLocH R P (obsInit .two V P) j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) =
        ((rgProdO R P (obsInit .two V P) Nh t : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ∧
      algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) *
        (algebraMap ℂ (Alg 2 L N) V.ga + V.mua • (psibar P.a * psi P.a)))) =
        ((rgProdO R P (obsInit .two V P) Nh t : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a := by
  dsimp only
  have h : omegaCO (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (ZhO R P (obsInit .two V P) 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
      rgProdO R P (obsInit .two V P) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
    have h0 := hist_omegaO_traj R P (obsInit .two V P) hN hρ1 hspl hm0 hm hV hVL b μ₀
      (obsInit_isObs .two V P) hloc
    dsimp only at h0
    exact h0
  have ht := traj_zero_eq R b μ₀
  exact ⟨(omegaCO_ZhO_zero_e R P .two V _ ht (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))).symm.trans
      (congrArg (fun F : OE .two (Lam 2 L N) => (F : SA .two (Lam 2 L N)).e) h),
    (omegaCO_ZhO_zero_two R P V _ ht (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))).symm.trans
      (congrArg (fun F : OE .two (Lam 2 L N) => (F : SA .two (Lam 2 L N)).a) h)⟩

set_option maxHeartbeats 1000000 in
/-- **The two-point function along a trajectory** (Case (1), `σ_aσ̄_b`, no `ab` couplings):
`μ_aμ_b⟨Z_0ψ̄_aψ_b⟩_{Γ_0} = (rgProdO)_{ab}`, together with `⟨Z_0⟩_{Γ_0} = (rgProdO)_∅`. -/
theorem thm_obs_chain_twopt {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (V : OCoup1) (hVab : AbFree .one V)
    (hloc : ∀ j ≤ Nh, OLocH R P (obsInit .one V P) j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) =
        ((rgProdO R P (obsInit .one V P) Nh t : OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).e ∧
      algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) *
        ((V.mua * V.mub) • (psibar P.a * psi P.b)))) =
        ((rgProdO R P (obsInit .one V P) Nh t : OE .one (Lam 2 L N)) :
          SA .one (Lam 2 L N)).ab := by
  dsimp only
  have h : omegaCO (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (ZhO R P (obsInit .one V P) 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
      rgProdO R P (obsInit .one V P) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
    have h0 := hist_omegaO_traj R P (obsInit .one V P) hN hρ1 hspl hm0 hm hV hVL b μ₀
      (obsInit_isObs .one V P) hloc
    dsimp only at h0
    exact h0
  have ht := traj_zero_eq R b μ₀
  exact ⟨(omegaCO_ZhO_zero_e R P .one V _ ht (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))).symm.trans
      (congrArg (fun F : OE .one (Lam 2 L N) => (F : SA .one (Lam 2 L N)).e) h),
    (omegaCO_ZhO_zero_one R P V hVab _ ht (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))).symm.trans
      (congrArg (fun F : OE .one (Lam 2 L N) => (F : SA .one (Lam 2 L N)).ab) h)⟩

end Traj

end

end PtCorr2
