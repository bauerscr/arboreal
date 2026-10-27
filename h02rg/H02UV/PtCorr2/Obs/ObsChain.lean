import PtCorr2.Obs.ObsStep
import PtCorr2.Zero.ChainFlow

/-!
# The Gaussian integral with sources along the trajectories (`sec:corr`, observables)

The analogue of `PtCorr2.hist_omega_traj` on the algebra with sources.

* `zoutO_eq` (**exactness with sources**): the output `Z_{j+1}` with sources of a raw step equals
  the input with sources of the next step built from the outputs of `rawStep` and of the observable
  flow `obsStep` (`Obs2.Flow.Hist`). The bulk parts are those of `PtCorr2.exactStep_of`; the observable
  parts are the definitions of `obsStep` (`π_obs` of the outputs) and the block identity
  `Ĩ_{j+1}(B_+) = e^{-V_{j+1}(B_+)}(1 + 𝒲_{j+1}(B_+))` (`ItO_eq`).
* **`hist_omegaO_traj`**: along every trajectory `t = traj (rgData R) L² b μ₀` (hypotheses of
  `hist_omega_traj`), for every observable initial state `o₀`,

  `⟨Z_0^{obs}⟩_{Γ_0} = ∏_{j ≤ N_h}[det(1 + a_jAΓ_j) e^{-u_{j+1}(Λ)}] · det(1 + a_{N-1}AΓ_{N-1})
  e^{-u_N(Λ)} ⟨F_N^{obs}⟩_{t_raw Q}`

  in `OE c Λ` (the constants `e^{-u}` carry the observable parts `u^{obs}`), provided the locality
  hypothesis `OLocHyp` holds for the inputs of the steps `j ≤ N_h` (named open input: the point
  support of the source components along the observable flow).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist Step2.LastN

/-! ### Products of exponentials -/

section Exp

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem prod_oexp_nil {ι : Type*} (s : Finset ι) (f : ι → OE c Λ)
    (hf : ∀ i ∈ s, IsNilpotent (f i)) :
    IsNilpotent (∑ i ∈ s, f i) ∧ ∏ i ∈ s, oexp (f i) = oexp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, by simp [oexp, IsNilpotent.exp_zero]⟩
  | insert i s hi ih =>
    obtain ⟨h1, h2⟩ := ih fun k hk => hf k (mem_insert_of_mem hk)
    have h0 := hf i (mem_insert_self i s)
    refine ⟨?_, ?_⟩
    · rw [sum_insert hi]; exact (Commute.all _ _).isNilpotent_add h0 h1
    · rw [prod_insert hi, sum_insert hi, h2, oexp, oexp, oexp,
        IsNilpotent.exp_add_of_commute (Commute.all _ _) h0 h1]

end Exp

/-! ### Exactness with sources -/

section Exact

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

theorem isNilpotent_VpO (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (V W : OFam c 2 L N) (K : OAct c 2 L N) (b : Fin 2 → ℕ) :
    IsNilpotent (-VpO P j C V W K b) := by
  refine isNilpotent_of_bulk ?_
  rw [map_neg, bulk_VpO]
  have h : ε ((Vp j C (bulkF V) (bulkF W) (bulkF K) b : EvR (Lam 2 L N)) : Alg 2 L N) = 0 := by
    simp [ε_Vp]
  exact ⟨_, Step.pow_eq_zero_of_ε' (eps_neg_coe h) (Nat.lt_succ_self _)⟩

/-- `Ĩ_{j+1}(B_+) = e^{-V_{j+1}(B_+)}(1 + 𝒲_{j+1}(B_+))` with sources. -/
theorem ItO_eq (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
    (V W : OFam c 2 L N) (K : OAct c 2 L N) (c' : Fin 2 → ℕ) :
    ItO P j C V W K c' = oexp (-Vnext2O P j C V W K c') * (1 + Wnext2O P j C V W c') := by
  rw [ItO, bpowO, Wnext2O, add_sub_cancel, Vnext2O, ← sum_neg_distrib,
    ← (prod_oexp_nil _ _ fun b _ => isNilpotent_VpO P j C V W K b).2, ← prod_mul_distrib]
  rfl

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ}
  {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N}

/-- **Exactness of one raw step with sources.** -/
theorem zoutO_eq (hV : ValidAtL R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (hρ1 : R.ρ < 1)
    (hnu : starRingEnd ℂ (rawStep R j st g μ D K).nu = (rawStep R j st g μ D K).nu)
    (hg : starRingEnd ℂ (rawStep R j st g μ D K).g = (rawStep R j st g μ D K).g)
    (ho : o.IsObs) :
    ZoutO R P j st g μ D K o =
      ZinO R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re
        (rawStep R j st g μ D K).nu.re (rawStep R j st g μ D K).D (rawStep R j st g μ D K).K
        (obsStep R P j st g μ D K o) := by
  have hρ0 : 0 ≤ R.ρ := hV.2.2.2.2.1
  have hZ : st.Z ≠ 0 := H.Z_ne_zero hρ1
  have hrec := stVf_add_stDelta_next R hZ hρ0 hρ1 hnu hg
  have hVn := Vnext2_st R (g := g) (μ := μ) hV H hD hK
  unfold ZoutO ZinO gZO
  refine sum_congr rfl fun X hX => ?_
  have hXp := (mem_Pj.1 hX).2
  congr 1
  · unfold bpowO
    refine prod_congr rfl fun c' hc => ?_
    have hcI : c' ∈ blockIdx (L := L) (N := N) (j + 1) := mem_blockIdx_of_mem_blocks hc
    have hb : stVf R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re
        (rawStep R j st g μ D K).nu.re c' + stDelta R (j + 1) (rawStep R j st g μ D K).st c' =
        Vnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) c' := by
      refine Subtype.ext ?_
      rw [hVn c' hcI]
      show ((stVf R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re
        (rawStep R j st g μ D K).nu.re + stDelta R (j + 1) (rawStep R j st g μ D K).st) c' :
          Alg 2 L N) = _
      rw [hrec]; rfl
    have hw : ((rawStep R j st g μ D K).st.Wl + (rawStep R j st g μ D K).D) c' =
        bulk (Wnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c') := by
      show WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl c' +
        (rawStep R j st g μ D K).D c' = _
      rw [full_bulk_D R P j st g μ D K ho c']; abel
    show ItO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) c' =
      oexp (-(emb (stVf R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re
        (rawStep R j st g μ D K).nu.re c' + stDelta R (j + 1) (rawStep R j st g μ D K).st c') +
          πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
            (fullK R j st K o) c'))) *
        (1 + (emb (((rawStep R j st g μ D K).st.Wl + (rawStep R j st g μ D K).D) c') +
          πobs (Wnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c')))
    rw [hb, hw, ← full_bulk_V R P j st g μ D K ho c', ← eq_emb_add_πobs, ← eq_emb_add_πobs,
      ItO_eq]
  · unfold KextO
    refine prod_congr rfl fun Y hY => ?_
    have hYc : IsConn (j + 1) Y := isConn_of_mem_comp hXp hY
    show KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) Y =
      emb ((rawStep R j st g μ D K).K Y) + πobs (KconnO (j + 1) (KplusO P j (stCov R j st)
        (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)) Y)
    rw [← full_bulk_K R P j st g μ D K ho Y, ← eq_emb_add_πobs, KconnO, if_pos hYc]

end Exact

/-! ### Along the trajectories -/

section Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt c L N)

/-- The input with sources of step `j` along the history. -/
def ZhO (j : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  ZinO R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)

/-- The factor `det(1 + a_jAΓ_j) e^{-u_{j+1}(Λ)}` with sources of step `j` along the history. -/
def chO (j : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  detStep R j (rawHist R j t) • uOutO R P j (rawHist R j t) (t j).1 (t j).2.1
    (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)

/-- The locality hypothesis with sources at step `j` along the history. -/
def OLocH (j : ℕ) (t : Hist.Seq (Xs R)) : Prop :=
  OLocHyp P j (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
    (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    (fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))

/-- The coordinates of the trajectory at `j + 1` are the outputs of step `j` (cf. `traj_exact`). -/
theorem traj_next (hρ1 : R.ρ < 1) (b μ₀ : ℝ) {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    (t (j + 1)).1 = (histOut R j t).g.re ∧ (t (j + 1)).2.1 = (histOut R j t).nu.re ∧
      rawD R (rawHist R (j + 1) t).u (t (j + 1)).2.2 = (histOut R j t).D ∧
      rawK R (rawHist R (j + 1) t).u (t (j + 1)).2.2 = (histOut R j t).K := by
  intro t
  have hρ0 : 0 ≤ R.ρ := (hV j le_rfl).2.2.2.1
  have HI' := rawInv_hist R hρ0 (j + 1) (fun i hi => hV i (by omega)) t
  have ht : t (j + 1) = Hist.stepS (rgData R) ((L : ℝ) ^ 2) j t := traj_succ_rg R _ b μ₀ j
  have hu0 : (rawHist R (j + 1) t).u ≠ 0 := by
    intro h
    have := HI'.hu
    rw [h, zero_pow two_ne_zero] at this
    exact HI'.Z_ne_zero hρ1 this.symm
  refine ⟨by rw [ht]; rfl, by rw [ht]; simp only [Hist.stepS, rgData]; ring, ?_, ?_⟩
  · rw [ht]
    show rawD R (rawHist R (j + 1) t).u (Tmap R j t) = _
    unfold Tmap; rw [dif_pos hV]
    show sigF (rawHist R (j + 1) t).u (sigF (histOut R j t).st.u⁻¹ (histOut R j t).D) = _
    rw [sigF_sigF, show (rawHist R (j + 1) t).u * (histOut R j t).st.u⁻¹ = 1 from
      mul_inv_cancel₀ hu0, sigF_one]
  · rw [ht]
    show rawK R (rawHist R (j + 1) t).u (Tmap R j t) = _
    unfold Tmap; rw [dif_pos hV]
    show sigK (rawHist R (j + 1) t).u (sigK (histOut R j t).st.u⁻¹ (histOut R j t).K) = _
    rw [sigK_sigK, show (rawHist R (j + 1) t).u * (histOut R j t).st.u⁻¹ = 1 from
      mul_inv_cancel₀ hu0, sigK_one]

/-- **The Gaussian integral with sources along a trajectory**: hypotheses of
`hist_omega_traj` (without the coupling form of the final object, which is not used), an
observable initial state `o₀`, and the locality hypothesis `OLocH` at the steps `j ≤ N_h`. -/
theorem hist_omegaO_traj {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (ho₀ : o₀.IsObs)
    (hloc : ∀ j ≤ Nh, OLocH R P o₀ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    omegaCO (Γh R 0 t) (ZhO R P o₀ 0 t) =
      (∏ j ∈ range (Nh + 1), chO R P o₀ j t) *
        (detStep R (Nh + 1) (histOut R Nh t).st • (uOutNO R P (Nh + 1) (histOut R Nh t).st
          (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
          (obsHist R P o₀ (Nh + 1) t) *
          omegaCO (cstC (Lam 2 L N) (zmRaw R (Nh + 1) (Function.update (histOut R Nh t).st.ζ
            (Nh + 1) (stZeta R (histOut R Nh t).st)) / Fintype.card (Lam 2 L N)))
            (finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
              (histOut R Nh t).D (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t)))) := by
  intro t
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hLg := hVL.1
  have hcore : ∀ j ≤ Nh, ValidCore R j := fun j hj => by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI : ∀ j ≤ Nh + 1, RawInv R j (rawHist R j t) := rawInv_histU R hV hVL t
  have hS : ∀ j ≤ Nh + 1, SplitOK R j (rawHist R j t) := fun j hj =>
    splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  have hO : ∀ j, (obsHist R P o₀ j t).IsObs := fun j => obsHist_isObs R P o₀ ho₀ j t
  have hstep : ∀ j ≤ Nh, omegaCO (Γh R j t) (ZhO R P o₀ j t) =
      chO R P o₀ j t * omegaCO (DressedFRD.kmat ((stData R j (rawHist R j t)).Gam (j + 1)))
        (ZoutO R P j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
          (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)) := fun j hj => by
    rw [chO, smul_mul_assoc]
    exact rawStepO_omega (hcore j hj) (hRI j (by omega)) (hS j (by omega)) (hO j) (hloc j hj)
  have hzout : ∀ j ≤ Nh, ZoutO R P j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2)
      (obsHist R P o₀ j t) = ZinO R (j + 1) (histOut R j t).st (histOut R j t).g.re
        (histOut R j t).nu.re (histOut R j t).D (histOut R j t).K (obsHist R P o₀ (j + 1) t) :=
    fun j hj => by
      have hVL' : ValidAtL R j := by
        rcases Nat.lt_or_ge j Nh with h | h
        · exact (hV j h).toValidAtL hLg
        · rw [show j = Nh by omega]; exact hVL
      obtain ⟨hnu, hg⟩ := traj_out_real R hρ0 hρ1 ((L : ℝ) ^ 2) b μ₀ j
      exact zoutO_eq R P hVL' (hRI j (by omega)) (rawD_mem R _ _) (rawK_mem R _ _) hρ1 hnu hg
        (hO j)
  have h1 := chain_omegaO (Γ := fun j => Γh R j t) (Zs := fun j => ZhO R P o₀ j t)
    (cs := fun j => chO R P o₀ j t) Nh fun i hi => by
      show omegaCO (Γh R i t) (ZhO R P o₀ i t) =
        chO R P o₀ i t * omegaCO (Γh R (i + 1) t) (ZhO R P o₀ (i + 1) t)
      have hVi : ∀ k ≤ i, ValidAt R k := fun k hk => hV k (by omega)
      obtain ⟨e1, e2, e3, e4⟩ := traj_next R hρ1 b μ₀ hVi
      rw [hstep i hi.le, hzout i hi.le, (traj_exact R hρ1 hLg b μ₀ hVi).2]
      unfold ZhO
      rw [e1, e2, e3, e4]
      rfl
  have h2 := hstep Nh le_rfl
  rw [hzout Nh le_rfl, (traj_exactL R hρ1 b μ₀ hV hVL).2] at h2
  have h3 := lastStepO_omega (R := R) (P := P) (j := Nh + 1) (st := (histOut R Nh t).st)
    (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (D := (histOut R Nh t).D)
    (K := (histOut R Nh t).K) (o := obsHist R P o₀ (Nh + 1) t) (by omega)
    (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl) (hO (Nh + 1))
  rw [h1, h2, h3, prod_range_succ, mul_assoc]

end Hist

end

end PtCorr2
