import PtCorr2.Obs.ObsInit
import Obs2.Loc.LocFlow

/-!
# Locality along the observable flow: `OLocH` discharged (`sec:obs-flow`, `sec:corr`)

The locality invariant `ObsLocInv P j o` of an observable state (`V^{obs}(B), 𝒲^{obs}(B) ∈
𝒩^{obs}(B^□)`, `K^{obs}(Y) ∈ 𝒩^{obs}(Y^□)` for connected `Y`, `Obs2.osub`) holds for the initial
state `obsInit c V P` (any couplings, `obsLocInv_init`) and is preserved by `obsStep`
(`obsLocInv_step`, from `Obs2.OLocS.step` and the locality of the bulk inputs). Hence:

* `obsLocInv_hist`: the invariant along `obsHist` at all steps with `ValidCore` and `RawInv`;
* **`oLocH_traj`**: the locality hypothesis `OLocH` of `hist_omegaO_traj` holds at every step
  `j ≤ N_h` of every trajectory (hypotheses of `hist_omega_traj`), for every initial state with
  `ObsLocInv P 0 o₀`;
* **`hist_omegaO_traj_loc`**, **`thm_obs_chain_onept_loc`**, **`thm_obs_chain_twopt_loc`**: the
  exact RG representation of the correlations with sources without the locality hypothesis.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **The locality invariant of an observable state at scale `j`.** -/
structure ObsLocInv (P : ObsPts 2 L N) (j : ℕ) (o : ObsSt c L N) : Prop where
  V : ∀ b, o.V b ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b))
  W : ∀ b, o.W b ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b))
  K : ∀ Y, IsConn j Y → o.K Y ∈ osub P (nbhd j Y)

/-! ### The initial state -/

section Init

theorem evalO_mem_osub (c : Obs.Case) (V : OCoup c) (P : ObsPts 2 L N) (X : Finset (Lam 2 L N)) :
    evalO c V P.a P.b X ∈ osub P X := by
  have pa : P.a ∈ X → psibar P.a ∈ NX (X : Set (Lam 2 L N)) := fun h => psibar_mem_NX' h
  have qa : P.a ∈ X → psi P.a ∈ NX (X : Set (Lam 2 L N)) := fun h => psi_mem_NX' h
  have pb : P.b ∈ X → psibar P.b ∈ NX (X : Set (Lam 2 L N)) := fun h => psibar_mem_NX' h
  have qb : P.b ∈ X → psi P.b ∈ NX (X : Set (Lam 2 L N)) := fun h => psi_mem_NX' h
  have hnn : P.a ∈ X → P.b ∈ X → nn P.a P.b ∈ NX (X : Set (Lam 2 L N)) := fun ha hb =>
    add_mem (mul_mem (pa ha) (qa ha)) (mul_mem (pb hb) (qb hb))
  have hnx : P.a ∈ X → P.b ∈ X → nx P.a P.b ∈ NX (X : Set (Lam 2 L N)) := fun ha hb =>
    add_mem (mul_mem (pa ha) (qb hb)) (mul_mem (pb hb) (qa ha))
  have hm4 : P.a ∈ X → P.b ∈ X → m4 P.a P.b ∈ NX (X : Set (Lam 2 L N)) := fun ha hb =>
    mul_mem (mul_mem (pa ha) (qa ha)) (mul_mem (pb hb) (qb hb))
  cases c
  · refine ⟨zero_mem _, ?_, ?_, ?_, fun ha => ⟨?_, ?_⟩, fun hb => ⟨?_, ?_⟩⟩
    · show ind (P.a ∈ X) • (-OCoup1.mua V • psibar P.a) ∈ _
      by_cases ha : P.a ∈ X
      · exact Subalgebra.smul_mem _ (Subalgebra.smul_mem _ (pa ha) _) _
      · rw [ind_neg ha, zero_smul]; exact zero_mem _
    · show ind (P.b ∈ X) • (OCoup1.mub V • psi P.b) ∈ _
      by_cases hb : P.b ∈ X
      · exact Subalgebra.smul_mem _ (Subalgebra.smul_mem _ (qb hb) _) _
      · rw [ind_neg hb, zero_smul]; exact zero_mem _
    · show ind (P.a ∈ X ∧ P.b ∈ X) • (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-OCoup1.q V) +
        (OCoup1.r V / 2) • nn P.a P.b + OCoup1.chi V • m4 P.a P.b) ∈ _
      by_cases h : P.a ∈ X ∧ P.b ∈ X
      · exact Subalgebra.smul_mem _ (add_mem (add_mem (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.smul_mem _ (hnn h.1 h.2) _)) (Subalgebra.smul_mem _ (hm4 h.1 h.2) _)) _
      · rw [ind_neg h, zero_smul]; exact zero_mem _
    · show ind (P.a ∈ X) • (-OCoup1.mua V • psibar P.a) = 0
      rw [ind_neg ha, zero_smul]
    · show ind (P.a ∈ X ∧ P.b ∈ X) • _ = 0
      rw [ind_neg fun h => ha h.1, zero_smul]
    · show ind (P.b ∈ X) • (OCoup1.mub V • psi P.b) = 0
      rw [ind_neg hb, zero_smul]
    · show ind (P.a ∈ X ∧ P.b ∈ X) • _ = 0
      rw [ind_neg fun h => hb h.2, zero_smul]
  · refine ⟨zero_mem _, ?_, ?_, ?_, fun ha => ⟨?_, ?_⟩, fun hb => ⟨?_, ?_⟩⟩
    · show ind (P.a ∈ X) • (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-OCoup2.ga V) -
        OCoup2.mua V • (psibar P.a * psi P.a)) ∈ _
      by_cases ha : P.a ∈ X
      · exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.smul_mem _ (mul_mem (pa ha) (qa ha)) _)) _
      · rw [ind_neg ha, zero_smul]; exact zero_mem _
    · show ind (P.b ∈ X) • (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-OCoup2.gb V) -
        OCoup2.mub V • (psibar P.b * psi P.b)) ∈ _
      by_cases hb : P.b ∈ X
      · exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.smul_mem _ (mul_mem (pb hb) (qb hb)) _)) _
      · rw [ind_neg hb, zero_smul]; exact zero_mem _
    · show ind (P.a ∈ X ∧ P.b ∈ X) • (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-OCoup2.q V) -
        (OCoup2.eta V / 2) • nx P.a P.b + (OCoup2.r V / 2) • nn P.a P.b +
        OCoup2.chi V • m4 P.a P.b) ∈ _
      by_cases h : P.a ∈ X ∧ P.b ∈ X
      · exact Subalgebra.smul_mem _ (add_mem (add_mem (sub_mem (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.smul_mem _ (hnx h.1 h.2) _)) (Subalgebra.smul_mem _ (hnn h.1 h.2) _))
          (Subalgebra.smul_mem _ (hm4 h.1 h.2) _)) _
      · rw [ind_neg h, zero_smul]; exact zero_mem _
    · show ind (P.a ∈ X) • _ = 0
      rw [ind_neg ha, zero_smul]
    · show ind (P.a ∈ X ∧ P.b ∈ X) • _ = 0
      rw [ind_neg fun h => ha h.1, zero_smul]
    · show ind (P.b ∈ X) • _ = 0
      rw [ind_neg hb, zero_smul]
    · show ind (P.a ∈ X ∧ P.b ∈ X) • _ = 0
      rw [ind_neg fun h => hb h.2, zero_smul]

/-- **The initial state is local** (any couplings). -/
theorem obsLocInv_init (c : Obs.Case) (V : OCoup c) (P : ObsPts 2 L N) :
    ObsLocInv P 0 (obsInit c V P) where
  V b := osub_mono (subset_nbhd (isPolymer_blockSet 0 b)) (evalO_mem_osub c V P _)
  W _ := zero_mem _
  K _ _ := zero_mem _

end Init

/-! ### One step -/

section Step

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N} (g μ : ℝ)
  {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N}

/-- The full inputs (bulk plus observable) of a step are local. -/
theorem olocS_full (hV : ValidCore R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (ho : ObsLocInv P j o) :
    OLocS P j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem H.hWl hD).1
  refine ⟨fun b => add_mem (emb_mem_osub (hVm.1.loc b)) (ho.V b),
    fun b => add_mem (emb_mem_osub (hW.loc b)) (ho.W b), fun Y hY => ?_⟩
  have hbp : ((bpow j (fun b => gexp (stDelta R j st b)) Y : EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j Y : Set (Lam 2 L N)) :=
    coe_prod_mem _ (blocks j Y) _ fun b hb =>
      NX_mono (coe_subset.2 (nbhd_mono (blockSet_subset hY.1 hb)))
        (gexp_mem_NX (eps_stDelta R j st b) (hΔm.1.loc b))
  exact mul_mem (emb_mem_osub hbp) (add_mem (emb_mem_osub (hK.1.loc Y hY)) (ho.K Y hY))

/-- **The locality invariant is preserved by one step of the observable flow.** -/
theorem obsLocInv_step (hV : ValidCore R j) (H : RawInv R j st)
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (ho : ObsLocInv P j o) : ObsLocInv P (j + 1) (obsStep R P j st g μ D K o) := by
  have hF := olocS_full R P g μ hV H hD hK ho
  obtain ⟨hC, -, -, -⟩ := RawInv.covL hV H
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hL' : 2 ^ (2 + 3) ≤ L := by omega
  have hCR : CovRange j (stCov R j st) := fun x y h => hC.range hj2 x y h
  have hS := hF.step hd hL' hj2 hCR
  exact ⟨fun c' => πobs_mem_osub (hS.hV c'), fun c' => πobs_mem_osub (hS.hW c'),
    fun Y hY => πobs_mem_osub (hS.hK Y hY)⟩

end Step

/-! ### Along the trajectories -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- **The locality invariant along the history.** -/
theorem obsLocInv_hist (h0 : ObsLocInv P 0 o₀) (t : Hist.Seq (Xs R)) :
    ∀ n, (∀ j < n, ValidCore R j ∧ RawInv R j (rawHist R j t)) →
      ObsLocInv P n (obsHist R P o₀ n t)
  | 0, _ => h0
  | n + 1, h => by
    rw [obsHist_succ]
    exact obsLocInv_step R P _ _ (h n (by omega)).1 (h n (by omega)).2 (rawD_mem R _ _)
      (rawK_mem R _ _) (obsLocInv_hist h0 t n fun j hj => h j (by omega))

theorem oLocH_of {j : ℕ} {t : Hist.Seq (Xs R)} (hV : ValidCore R j)
    (H : RawInv R j (rawHist R j t)) (ho : ObsLocInv P j (obsHist R P o₀ j t)) :
    OLocH R P o₀ j t :=
  (olocS_full R P _ _ hV H (rawD_mem R _ _) (rawK_mem R _ _) ho).toOLocHyp

/-- **`OLocH` holds along every trajectory** (hypotheses of `hist_omega_traj`, initial state
with `ObsLocInv P 0 o₀`). -/
theorem oLocH_traj {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (h0 : ObsLocInv P 0 o₀) (t : Hist.Seq (Xs R)) : ∀ j ≤ Nh, OLocH R P o₀ j t := by
  have hcore : ∀ j ≤ Nh, ValidCore R j := fun j hj => by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t
  intro j hj
  exact oLocH_of R P o₀ (hcore j hj) (hRI j (by omega))
    (obsLocInv_hist R P o₀ h0 t j fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩)

/-- **The Gaussian integral with sources along a trajectory**, without the locality
hypothesis: `hist_omegaO_traj` for every initial state with `ObsLocInv P 0 o₀`. -/
theorem hist_omegaO_traj_loc {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (ho₀ : o₀.IsObs) (h0 : ObsLocInv P 0 o₀) :
    omegaCO (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (ZhO R P o₀ 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
      rgProdO R P o₀ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
  have h := hist_omegaO_traj R P o₀ hN hρ1 hspl hm0 hm hV hVL b μ₀ ho₀
    (oLocH_traj R P o₀ hV hVL h0 _)
  dsimp only at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The one-point function along a trajectory** (Case (2), `σ_a`), unconditional apart from
the hypotheses of `hist_omega_traj`: `⟨Z_0⟩_{Γ_0} = (rgProdO)_∅` and
`⟨Z_0(γ_a + μ_aψ̄_aψ_a)⟩_{Γ_0} = (rgProdO)_a`. -/
theorem thm_obs_chain_onept_loc {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (V : OCoup2) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) =
        ((rgProdO R P (obsInit .two V P) Nh t : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ∧
      algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) *
        (algebraMap ℂ (Alg 2 L N) V.ga + V.mua • (psibar P.a * psi P.a)))) =
        ((rgProdO R P (obsInit .two V P) Nh t : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a :=
  thm_obs_chain_onept R P hN hρ1 hspl hm0 hm hV hVL b μ₀ V
    (oLocH_traj R P _ hV hVL (obsLocInv_init .two V P) _)

set_option maxHeartbeats 1000000 in
/-- **The two-point function along a trajectory** (Case (1), `σ_aσ̄_b`, no `ab` couplings),
unconditional apart from the hypotheses of `hist_omega_traj`:
`μ_aμ_b⟨Z_0ψ̄_aψ_b⟩_{Γ_0} = (rgProdO)_{ab}` and `⟨Z_0⟩_{Γ_0} = (rgProdO)_∅`. -/
theorem thm_obs_chain_twopt_loc {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (V : OCoup1) (hVab : AbFree .one V) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) (Zh R 0 t : Alg 2 L N)) =
        ((rgProdO R P (obsInit .one V P) Nh t : OE .one (Lam 2 L N)) : SA .one (Lam 2 L N)).e ∧
      algebraMap ℂ (Alg 2 L N) (omegaC (Γh R 0 t) ((Zh R 0 t : Alg 2 L N) *
        ((V.mua * V.mub) • (psibar P.a * psi P.b)))) =
        ((rgProdO R P (obsInit .one V P) Nh t : OE .one (Lam 2 L N)) :
          SA .one (Lam 2 L N)).ab :=
  thm_obs_chain_twopt R P hN hρ1 hspl hm0 hm hV hVL b μ₀ V hVab
    (oLocH_traj R P _ hV hVL (obsLocInv_init .one V P) _)

end Hist

end

end PtCorr2
