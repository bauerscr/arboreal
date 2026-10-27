import PtCorr2.Zero.TwoPtRep

/-!
# The Case-(2) pair observable along the flow: coalescence and the `d = 2` square (exact part)

Sources `σ_a, σ_b` (Case (2), commuting), initial observable `obsInit .two V P` with `AbFree`
(`q = η = r = χ = 0`). Write `z_a = γ_a + μ_aψ̄_aψ_a`, `z_b = γ_b + μ_bψ̄_bψ_b` (`zObsA`, `zObsB`).

* `omegaCO_ZhO_zero_b_two`, `omegaCO_ZhO_zero_ab_two`: the `σ_b`, `σ_aσ_b` components at scale `0`
  are `⟨Z_0z_b⟩`, `⟨Z_0z_az_b⟩`.
* **`zz_rg_ratio`**: along the trajectory (hypotheses of `twopt_rg_repr`), with `Π = rgProdO` and
  scalar components `sE, sA, sB, sAB` (`ε` of the components):
  `⟨z_a⟩ = sA Pr/sE Pr`, `⟨z_b⟩ = sB Pr/sE Pr`, `⟨z_az_b⟩ = sAB Pr/sE Pr`, `sE Pr = ⟨Z_0⟩ ≠ 0`.
* Split of the RG product at a scale `k`: `Π = Π^{<k}·Π^{≥k}` (`rgProdO_split`), `Π^{<k}` the step
  constants `chO_j`, `j < k`, `Π^{≥k}` the remaining steps, the last step and the zero mode.
* **Coalescence (`prodLo_rankOne`)**: below `j_ab` the per-step constants `e^{-u_{j+1}(Λ)}` have no
  `σ_aσ_b` part (`Obs2.obsHist_coal_valid`), so `Π^{<j_ab}` is *rank one*:
  `sAB·sE = sA·sB`, i.e. `Π^{<j_ab} = sE(1 + σ_aA)(1 + σ_bB)` — below coalescence the `ab` part is the
  product of the `a` and `b` parts.
* **The exact `d = 2` square (`zz_square_split`)**: with `A = sA Pr^</sE Pr^<`, `B = sB Pr^</sE Pr^<`
  (the one-point parts below `j_ab`) and `E = sAB Pr^≥/sE Pr^≥` (the pair part above `j_ab`):
  `⟨z_a⟩ = A + sA Pr^≥/sE Pr^≥`, `⟨z_b⟩ = B + sB Pr^≥/sE Pr^≥` and
  `⟨z_az_b⟩ = -AB + ⟨z_b⟩A + ⟨z_a⟩B + E` (`ratio_split`, pure). At `h = 0` (`⟨z⟩ = 0`) this is
  `-⟨z_az_b⟩ = AB - E`: the perfect square `M²` with `M ≈ A ≈ B`, the `d = 2` analogue of
  `lem:square` (the identity `A + A^≥ = ⟨z_a⟩` plays the role of `κ(γ + λτ) = 1 - r`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

/-! ### Scalar components and rank one -/

section Scal

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

omit [DecidableEq Λ] [Fintype Λ]

/-- The scalar parts `ε(F_∅)`, `ε(F_a)`, `ε(F_b)`, `ε(F_{ab})` (Case (2)). -/
def sE (F : OE .two Λ) : ℂ := ε (F : SA .two Λ).e
def sA (F : OE .two Λ) : ℂ := ε (F : SA .two Λ).a
def sB (F : OE .two Λ) : ℂ := ε (F : SA .two Λ).b
def sAB (F : OE .two Λ) : ℂ := ε (F : SA .two Λ).ab

theorem sE_mul (F G : OE .two Λ) : sE (F * G) = sE F * sE G := by
  simp only [sE, OE.mul_e, map_mul]

theorem sA_mul (F G : OE .two Λ) : sA (F * G) = sE F * sA G + sA F * sE G := by
  simp only [sA, sE, OE.mul_a, map_add, map_mul]

theorem sB_mul (F G : OE .two Λ) : sB (F * G) = sE F * sB G + sB F * sE G := by
  simp only [sB, sE, OE.mul_b, map_add, map_mul]

theorem sAB_mul (F G : OE .two Λ) :
    sAB (F * G) = sE F * sAB G + sA F * sB G + sB F * sA G + sAB F * sE G := by
  simp only [sAB, sA, sB, sE, OE.mul_ab, Case.s_two, one_smul, map_add, map_mul]

/-- `F = sE(1 + σ_aA)(1 + σ_bB)` on scalars: `sAB·sE = sA·sB`. -/
def RankOne (F : OE .two Λ) : Prop := sAB F * sE F = sA F * sB F

theorem rankOne_one : RankOne (1 : OE .two Λ) := by
  simp [RankOne, sAB, sA, sB, sE]

theorem RankOne.mul {F G : OE .two Λ} (hF : RankOne F) (hG : RankOne G) : RankOne (F * G) := by
  unfold RankOne at *
  rw [sAB_mul, sE_mul, sA_mul, sB_mul]
  linear_combination (sE F) ^ 2 * hG + (sE G) ^ 2 * hF

theorem RankOne.smul {F : OE .two Λ} (hF : RankOne F) (c : ℂ) : RankOne (c • F) := by
  unfold RankOne at *
  have e1 : sAB (c • F) = c * sAB F := by
    show ε (c • (F : SA .two Λ)).ab = _; rw [SA.smul_ab, map_smul, smul_eq_mul]; rfl
  have e2 : sE (c • F) = c * sE F := by
    show ε (c • (F : SA .two Λ)).e = _; rw [SA.smul_e, map_smul, smul_eq_mul]; rfl
  have e3 : sA (c • F) = c * sA F := by
    show ε (c • (F : SA .two Λ)).a = _; rw [SA.smul_a, map_smul, smul_eq_mul]; rfl
  have e4 : sB (c • F) = c * sB F := by
    show ε (c • (F : SA .two Λ)).b = _; rw [SA.smul_b, map_smul, smul_eq_mul]; rfl
  rw [e1, e2, e3, e4]
  linear_combination c ^ 2 * hF

variable [DecidableEq Λ] [Fintype Λ]

theorem oexp_obs_b' {c : Obs.Case} {F : OE c Λ} (hF : bulk F = 0) :
    ((oexp F : OE c Λ) : SA c Λ).b = (F : SA c Λ).b := by
  have he := e_eq_zero_of_bulk hF
  rw [oexp_of_obs hF, pow_two]
  simp [he]

/-- `e^F` of an observable `F` without `σ_aσ_b` part is rank one. -/
theorem rankOne_oexp {F : OE .two Λ} (hF : bulk F = 0) (hab : (F : SA .two Λ).ab = 0) :
    RankOne (oexp F) := by
  unfold RankOne sAB sE sA sB
  rw [oexp_obs_ab hF, oexp_obs_e hF, oexp_obs_a hF, oexp_obs_b' hF, hab]
  simp only [Case.s_two, one_smul, zero_add, map_smul, map_add, map_mul, map_one, smul_eq_mul]
  ring

omit [DecidableEq Λ] [Fintype Λ] in
/-- **The `d = 2` square, pure form.** For `Π = XY` with `X` rank one, `sE X, sE Y ≠ 0`, and
`A = sA X/sE X`, `B = sB X/sE X`, `r_a = sA Pr/sE Pr`, `r_b = sB Pr/sE Pr`, `E = sAB Y/sE Y`:
`sAB Pr/sE Pr = -AB + r_bA + r_aB + E`, `r_a = A + sA Y/sE Y`, `r_b = B + sB Y/sE Y`. -/
theorem ratio_split {X Y : OE .two Λ} (hX : RankOne X) (hX0 : sE X ≠ 0) (hY0 : sE Y ≠ 0) :
    sA (X * Y) / sE (X * Y) = sA X / sE X + sA Y / sE Y ∧
      sB (X * Y) / sE (X * Y) = sB X / sE X + sB Y / sE Y ∧
      sAB (X * Y) / sE (X * Y) =
        -(sA X / sE X * (sB X / sE X)) + sB (X * Y) / sE (X * Y) * (sA X / sE X) +
          sA (X * Y) / sE (X * Y) * (sB X / sE X) + sAB Y / sE Y := by
  unfold RankOne at hX
  rw [sAB_mul, sA_mul, sB_mul, sE_mul]
  refine ⟨by field_simp; ring, by field_simp; ring, ?_⟩
  field_simp
  linear_combination (sE Y) * hX

end Scal

variable {L N : ℕ} [NeZero L]

/-! ### The initial object: `σ_b` and `σ_aσ_b` components -/

section Init

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- `z_a = γ_a + μ_aψ̄_aψ_a`. -/
def zObsA (V : OCoup2) (P : ObsPts 2 L N) : Alg 2 L N :=
  algebraMap ℂ (Alg 2 L N) V.ga + V.mua • (psibar P.a * psi P.a)

/-- `z_b = γ_b + μ_bψ̄_bψ_b`. -/
def zObsB (V : OCoup2) (P : ObsPts 2 L N) : Alg 2 L N :=
  algebraMap ℂ (Alg 2 L N) V.gb + V.mub • (psibar P.b * psi P.b)

theorem omegaCO_emb_mul_b {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {c : Obs.Case}
    (Γ : Matrix Λ Λ ℂ) (Z : EvR Λ) (G : OE c Λ) :
    ((omegaCO Γ (emb Z * G) : OE c Λ) : SA c Λ).b =
      algebraMap ℂ (Grassmann.N Λ) (omegaC Γ ((Z : Grassmann.N Λ) * (G : SA c Λ).b)) := by
  rw [omegaCO_b, OE.mul_b, coe_emb, ofN_e, ofN_b, zero_mul, add_zero]

theorem obsInit_two_negsum_a (V : OCoup2) :
    ((-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .two V P).V p : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = zObsA V P := by
  rw [NegMemClass.coe_neg, neg_a, AddSubmonoidClass.coe_finsetSum, sum_a]
  show -∑ p ∈ blockIdx (L := L) (N := N) 0, ind (P.a ∈ blockSet (L := L) (N := N) 0 p) •
      (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-V.ga) - V.mua • (psibar P.a * psi P.a)) = _
  rw [← sum_smul, sum_ind_block, one_smul, map_neg, zObsA]
  abel

theorem obsInit_two_negsum_b (V : OCoup2) :
    ((-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .two V P).V p : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).b = zObsB V P := by
  rw [NegMemClass.coe_neg, neg_b, AddSubmonoidClass.coe_finsetSum, sum_b]
  show -∑ p ∈ blockIdx (L := L) (N := N) 0, ind (P.b ∈ blockSet (L := L) (N := N) 0 p) •
      (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-V.gb) - V.mub • (psibar P.b * psi P.b)) = _
  rw [← sum_smul, sum_ind_block, one_smul, map_neg, zObsB]
  abel

/-- **Case (2), the `σ_b` component at scale `0`**: `⟨Z_0 z_b⟩_Γ`. -/
theorem omegaCO_ZhO_zero_b_two (V : OCoup2) (t : Hist.Seq (Xs R)) {b μ₀ : ℝ}
    (ht : t 0 = (b, μ₀, 0)) (Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    ((omegaCO Γ (ZhO R P (obsInit .two V P) 0 t) : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).b =
      algebraMap ℂ (Alg 2 L N) (omegaC Γ ((Zh R 0 t : Alg 2 L N) * zObsB V P)) := by
  rw [ZhO_zero_eq R P _ (obsInit_isObs .two V P) rfl rfl t ht, omegaCO_emb_mul_b,
    oexp_obs_b' (by rw [map_neg, bulk_sum_evalFam, neg_zero]), obsInit_two_negsum_b]

/-- **Case (2), the `σ_aσ_b` component at scale `0`** (no `ab` couplings): `⟨Z_0 z_az_b⟩_Γ`. -/
theorem omegaCO_ZhO_zero_ab_two (V : OCoup2) (hV : AbFree .two V) (t : Hist.Seq (Xs R))
    {b μ₀ : ℝ} (ht : t 0 = (b, μ₀, 0)) (Γ : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) :
    ((omegaCO Γ (ZhO R P (obsInit .two V P) 0 t) : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).ab =
      algebraMap ℂ (Alg 2 L N) (omegaC Γ ((Zh R 0 t : Alg 2 L N) * (zObsA V P * zObsB V P))) := by
  have hb : bulk (-∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .two V P).V p) = 0 := by
    rw [map_neg, bulk_sum_evalFam, neg_zero]
  rw [ZhO_zero_eq R P _ (obsInit_isObs .two V P) rfl rfl t ht, omegaCO_emb_mul_ab,
    oexp_obs_ab hb]
  congr 3
  set F : OE .two (Lam 2 L N) := -∑ p ∈ blockIdx (L := L) (N := N) 0, (obsInit .two V P).V p
  have eab : (F : SA .two (Lam 2 L N)).ab = 0 := by
    rw [NegMemClass.coe_neg, neg_ab, AddSubmonoidClass.coe_finsetSum, sum_ab, neg_eq_zero]
    exact sum_eq_zero fun p _ => evalO_ab .two hV _ _ _
  have hc : (F : SA .two (Lam 2 L N)).b * (F : SA .two (Lam 2 L N)).a =
      (F : SA .two (Lam 2 L N)).a * (F : SA .two (Lam 2 L N)).b :=
    (Grassmann.mul_comm_of_even (by simpa using F.par_b) _)
  rw [hc, eab, Case.s_two, one_smul, zero_add, ← two_smul ℂ, smul_smul,
    show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul, obsInit_two_negsum_a, obsInit_two_negsum_b]

end Init

/-! ### Along the trajectory -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

set_option maxHeartbeats 1000000 in
/-- **The Case-(2) pair observable as a ratio of components of the RG product**: along the
trajectory from `(b, μ₀)` with `h ≥ 0`, `sE Pr = ⟨Z_0⟩_{Γ_0} ≠ 0` and
`⟨z_a⟩ = sA Π/sE Π`, `⟨z_b⟩ = sB Π/sE Π`, `⟨z_az_b⟩ = sAB Π/sE Π`, `Π = rgProdO`. -/
theorem zz_rg_ratio {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (hL7 : 7 ≤ L) {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq)
    (V : OCoup2) (hVab : AbFree .two V) :
    let Pr := rgProdO R P (obsInit .two V P) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)
    sE Pr ≠ 0 ∧ avg0 L N R.msq b μ₀ (zObsA V P) = sA Pr / sE Pr ∧
      avg0 L N R.msq b μ₀ (zObsB V P) = sB Pr / sE Pr ∧
      avg0 L N R.msq b μ₀ (zObsA V P * zObsB V P) = sAB Pr / sE Pr := by
  dsimp only
  set t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀ with htd
  set Pr := rgProdO R P (obsInit .two V P) Nh t with hPr
  have ht : t 0 = (b, μ₀, 0) := Hist.traj_zero _ _
  have h := hist_omegaO_traj_loc R P (obsInit .two V P) hN hρ1 hspl hm0 hm hV hVL b μ₀
    (obsInit_isObs .two V P) (obsLocInv_init .two V P)
  rw [← htd, ← hPr] at h
  have hZ := omega_Zh_zero_ne R hL7 hm0 (by omega) t hb hh ht
  set Γ := Γh R 0 t
  have ke : sE Pr = omegaC Γ (Zh R 0 t : Alg 2 L N) := by
    rw [sE, ← h, omegaCO_ZhO_zero_e R P .two V t ht Γ]; exact ε.commutes _
  have ka : sA Pr = omegaC Γ ((Zh R 0 t : Alg 2 L N) * zObsA V P) := by
    rw [sA, ← h, omegaCO_ZhO_zero_two R P V t ht Γ]; exact ε.commutes _
  have kb : sB Pr = omegaC Γ ((Zh R 0 t : Alg 2 L N) * zObsB V P) := by
    rw [sB, ← h, omegaCO_ZhO_zero_b_two R P V t ht Γ]; exact ε.commutes _
  have kab : sAB Pr = omegaC Γ ((Zh R 0 t : Alg 2 L N) * (zObsA V P * zObsB V P)) := by
    rw [sAB, ← h, omegaCO_ZhO_zero_ab_two R P V hVab t ht Γ]; exact ε.commutes _
  have hA := fun F => avg0_eq_omega_traj R hL7 hm0 (by omega) t ht F
  refine ⟨by rw [ke]; exact hZ, ?_, ?_, ?_⟩
  · rw [hA, ka, ke]
  · rw [hA, kb, ke]
  · rw [hA, kab, ke]

/-- The last factor of `rgProdO` (the step `N - 1` and the zero mode). -/
def lastO {c : Obs.Case} (o₀ : ObsSt c L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  detStep R (Nh + 1) (histOut R Nh t).st • (uOutNO R P (Nh + 1) (histOut R Nh t).st
    (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
    (obsHist R P o₀ (Nh + 1) t) *
    omegaCO (cstC (Lam 2 L N) (zmRaw R (Nh + 1) (Function.update (histOut R Nh t).st.ζ
      (Nh + 1) (stZeta R (histOut R Nh t).st)) / Fintype.card (Lam 2 L N)))
      (finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
        (histOut R Nh t).D (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t)))

/-- `Π^{<k} = ∏_{j<k} chO_j`: the step constants below scale `k`. -/
def prodLo {c : Obs.Case} (o₀ : ObsSt c L N) (k : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  ∏ j ∈ range k, chO R P o₀ j t

/-- `Π^{≥k}`: the step constants of scales `k, …, N_h`, the last step and the zero mode. -/
def prodHi {c : Obs.Case} (o₀ : ObsSt c L N) (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    OE c (Lam 2 L N) :=
  (∏ j ∈ Ico k (Nh + 1), chO R P o₀ j t) * lastO R P o₀ Nh t

theorem rgProdO_split {c : Obs.Case} (o₀ : ObsSt c L N) {Nh k : ℕ} (hk : k ≤ Nh + 1)
    (t : Hist.Seq (Xs R)) :
    rgProdO R P o₀ Nh t = prodLo R P o₀ k t * prodHi R P o₀ Nh k t := by
  rw [prodLo, prodHi, ← mul_assoc, prod_range_mul_prod_Ico _ hk]
  rfl

/-- The step constant `chO_j = det·e^{-u_{j+1}(Λ)}` is rank one if the accumulated `u^{obs}` has
no `σ_aσ_b` part at scales `j` and `j + 1`. -/
theorem chO_rankOne (o₀ : ObsSt .two L N) (j : ℕ) (t : Hist.Seq (Xs R))
    (h0 : ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).ab = 0)
    (h1 : ((obsHist R P o₀ (j + 1) t).u : SA .two (Lam 2 L N)).ab = 0) :
    RankOne (chO R P o₀ j t) := by
  set U := uObsTot P j (stCov R j (rawHist R j t))
    (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
    (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    (fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    with hUd
  have hu : (obsHist R P o₀ (j + 1) t).u = (obsHist R P o₀ j t).u + U := rfl
  have hUab : (U : SA .two (Lam 2 L N)).ab = 0 := by
    have := h1
    rw [hu] at this
    have e : (((obsHist R P o₀ j t).u + U : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab =
        ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).ab + (U : SA .two (Lam 2 L N)).ab := rfl
    rw [e, h0, zero_add] at this
    exact this
  have hUb : bulk U = 0 := by
    rw [hUd, uObsTot, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _
  have hro : RankOne (oexp (-U)) :=
    rankOne_oexp (by rw [map_neg, hUb, neg_zero])
      (by rw [NegMemClass.coe_neg, neg_ab, hUab, neg_zero])
  unfold chO uOutO expU
  exact (hro.smul _).smul _

/-- **Coalescence: below `j_ab` the RG product is rank one** (`ab` part = product of the `a` and
`b` parts), for `AbFree` initial data, `L > 48`, `ValidAt` below `j_ab`. -/
theorem prodLo_rankOne (V : OCoup2) (hV : AbFree .two V) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hρ : 0 ≤ R.ρ) (hVk : ∀ k < coal L P.a P.b, ValidAt R k) (t : Hist.Seq (Xs R)) :
    ∀ k ≤ coal L P.a P.b, RankOne (prodLo R P (obsInit .two V P) k t) := by
  have hc := obsHist_coal_valid R P (obsInit .two V P) (obsInit_isObs .two V P)
    (coalInv_init .two hV P) hL hρ hVk t
  intro k
  induction k with
  | zero => intro _; rw [prodLo, prod_range_zero]; exact rankOne_one
  | succ k ih =>
    intro hk
    have h := ih (by omega)
    rw [prodLo, prod_range_succ]
    exact h.mul (chO_rankOne R P _ k t (hc k (by omega)).2 (hc (k + 1) hk).2)


/-! ### The one-point parts below `k`: the accumulated `u^{obs}` -/

theorem chO_sA (o₀ : ObsSt .two L N) (j : ℕ) (t : Hist.Seq (Xs R)) :
    sA (chO R P o₀ j t) = sE (chO R P o₀ j t) *
      (ε ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).a -
        ε ((obsHist R P o₀ (j + 1) t).u : SA .two (Lam 2 L N)).a) := by
  set U := uObsTot P j (stCov R j (rawHist R j t))
    (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
    (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    (fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    with hUd
  have hu : (obsHist R P o₀ (j + 1) t).u = (obsHist R P o₀ j t).u + U := rfl
  have hUb0 : bulk U = 0 := by
    rw [hUd, uObsTot, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _
  have hUb : bulk (-U) = 0 := by rw [map_neg, hUb0, neg_zero]
  have e : (((obsHist R P o₀ j t).u + U : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).a + (U : SA .two (Lam 2 L N)).a := rfl
  rw [hu, e, map_add]
  unfold chO uOutO expU
  simp only [sA, sE, SetLike.val_smul, SA.smul_a, SA.smul_e, map_smul, smul_eq_mul]
  rw [oexp_obs_a hUb, oexp_obs_e hUb, NegMemClass.coe_neg, SA.neg_a, map_neg, map_one]
  ring

theorem chO_sB (o₀ : ObsSt .two L N) (j : ℕ) (t : Hist.Seq (Xs R)) :
    sB (chO R P o₀ j t) = sE (chO R P o₀ j t) *
      (ε ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).b -
        ε ((obsHist R P o₀ (j + 1) t).u : SA .two (Lam 2 L N)).b) := by
  set U := uObsTot P j (stCov R j (rawHist R j t))
    (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
    (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    (fullK R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t))
    with hUd
  have hu : (obsHist R P o₀ (j + 1) t).u = (obsHist R P o₀ j t).u + U := rfl
  have hUb0 : bulk U = 0 := by
    rw [hUd, uObsTot, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _
  have hUb : bulk (-U) = 0 := by rw [map_neg, hUb0, neg_zero]
  have e : (((obsHist R P o₀ j t).u + U : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ j t).u : SA .two (Lam 2 L N)).b + (U : SA .two (Lam 2 L N)).b := rfl
  rw [hu, e, map_add]
  unfold chO uOutO expU
  simp only [sB, sE, SetLike.val_smul, SA.smul_b, SA.smul_e, map_smul, smul_eq_mul]
  rw [oexp_obs_b' hUb, oexp_obs_e hUb, NegMemClass.coe_neg, SA.neg_b, map_neg, map_one]
  ring

/-- **The one-point parts below `k` are the accumulated observable constants**:
`sA Π^{<k} = -ε(u^{obs}_{k,a})·sE Π^{<k}` (for an initial state with `u^{obs} = 0`), the same for `b`.
So `A = sA Π^{<k}/sE Π^{<k} = -ε(u^{obs}_{k,a})`: the `γ_a` coupling at scale `k`. -/
theorem prodLo_sA_sB (o₀ : ObsSt .two L N) (hu0 : o₀.u = 0) (t : Hist.Seq (Xs R)) (k : ℕ) :
    sA (prodLo R P o₀ k t) =
        sE (prodLo R P o₀ k t) * -ε ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).a ∧
      sB (prodLo R P o₀ k t) =
        sE (prodLo R P o₀ k t) * -ε ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).b := by
  induction k with
  | zero =>
    have h0 : obsHist R P o₀ 0 t = o₀ := rfl
    rw [prodLo, prod_range_zero, h0, hu0]
    simp [sA, sB, sE]
  | succ k ih =>
    rw [prodLo, prod_range_succ, ← prodLo, sA_mul, sB_mul, sE_mul, ih.1, ih.2,
      chO_sA, chO_sB]
    constructor <;> ring

/-! ### The Gaussian integral at scale `k` -/

set_option maxHeartbeats 1000000 in
/-- **`ω_{Γ_k}(Z_k) = Π^{≥k}`**: the observable chain from scale `k ≤ N_h` on. -/
theorem hist_omegaO_from {c : Obs.Case} (o₀ : ObsSt c L N) {Nh : ℕ} (hN : Nh + 2 = N)
    (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (ho₀ : o₀.IsObs) (h0 : ObsLocInv P 0 o₀) {k : ℕ}
    (hk : k ≤ Nh) :
    omegaCO (Γh R k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (ZhO R P o₀ k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
      prodHi R P o₀ Nh k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
  set t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀ with htd
  have hloc := oLocH_traj R P o₀ hV hVL h0 t
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
  have hrec : ∀ i < Nh, omegaCO (Γh R i t) (ZhO R P o₀ i t) =
      chO R P o₀ i t * omegaCO (Γh R (i + 1) t) (ZhO R P o₀ (i + 1) t) := fun i hi => by
    have hVi : ∀ k ≤ i, ValidAt R k := fun k hk => hV k (by omega)
    obtain ⟨e1, e2, e3, e4⟩ := traj_next R hρ1 b μ₀ hVi
    rw [hstep i hi.le, hzout i hi.le, (traj_exact R hρ1 hLg b μ₀ hVi).2]
    unfold ZhO
    rw [e1, e2, e3, e4]
    rfl
  have hlast : omegaCO (Γh R Nh t) (ZhO R P o₀ Nh t) = chO R P o₀ Nh t * lastO R P o₀ Nh t := by
    have h2 := hstep Nh le_rfl
    rw [hzout Nh le_rfl, (traj_exactL R hρ1 b μ₀ hV hVL).2] at h2
    have h3 := lastStepO_omega (R := R) (P := P) (j := Nh + 1) (st := (histOut R Nh t).st)
      (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (D := (histOut R Nh t).D)
      (K := (histOut R Nh t).K) (o := obsHist R P o₀ (Nh + 1) t) (by omega)
      (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl) (hO (Nh + 1))
    rw [h2, h3]
    rfl
  have key : ∀ n k, k + n = Nh → omegaCO (Γh R k t) (ZhO R P o₀ k t) = prodHi R P o₀ Nh k t := by
    intro n
    induction n with
    | zero =>
      intro k hk'
      obtain rfl : k = Nh := by omega
      rw [hlast, prodHi, Nat.Ico_succ_singleton, prod_singleton]
    | succ n ih =>
      intro k hk'
      rw [hrec k (by omega), ih (k + 1) (by omega), prodHi, prodHi,
        prod_eq_prod_Ico_succ_bot (by omega : k < Nh + 1), mul_assoc]
  exact key (Nh - k) k (by omega)

set_option maxHeartbeats 1000000 in
/-- **The exact `d = 2` square along the trajectory.** With `X = Π^{<j_ab}`, `Y = Π^{≥j_ab}`,
`A = sA X/sE X`, `B = sB X/sE X` (one-point parts below coalescence), `E = sAB Y/sE Y` (pair part
above coalescence): `⟨z_a⟩ = A + sA Y/sE Y`, `⟨z_b⟩ = B + sB Y/sE Y` and
`⟨z_az_b⟩ = -AB + ⟨z_b⟩A + ⟨z_a⟩B + E`. -/
theorem zz_square_split {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hc : coal L P.a P.b ≤ Nh)
    {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq) (V : OCoup2) (hVab : AbFree .two V) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    let X := prodLo R P (obsInit .two V P) (coal L P.a P.b) t
    let Y := prodHi R P (obsInit .two V P) Nh (coal L P.a P.b) t
    sE X ≠ 0 ∧ sE Y ≠ 0 ∧
      avg0 L N R.msq b μ₀ (zObsA V P) = sA X / sE X + sA Y / sE Y ∧
      avg0 L N R.msq b μ₀ (zObsB V P) = sB X / sE X + sB Y / sE Y ∧
      avg0 L N R.msq b μ₀ (zObsA V P * zObsB V P) =
        -(sA X / sE X * (sB X / sE X)) + avg0 L N R.msq b μ₀ (zObsB V P) * (sA X / sE X) +
          avg0 L N R.msq b μ₀ (zObsA V P) * (sB X / sE X) + sAB Y / sE Y := by
  intro t X Y
  obtain ⟨hZ, ha, hb', hab⟩ := zz_rg_ratio R P hN hρ1 hspl hm0 hm hV hVL (by omega) hb hh V hVab
  have hs := rgProdO_split R P (obsInit .two V P) (k := coal L P.a P.b) (Nh := Nh) (by omega) t
  rw [hs] at hZ ha hb' hab
  have hX0 : sE X ≠ 0 := fun h0 => hZ (by rw [sE_mul]; simp [X, h0])
  have hY0 : sE Y ≠ 0 := fun h0 => hZ (by rw [sE_mul]; simp [Y, h0])
  have hX := prodLo_rankOne R P V hVab hL hVL.2.2.2.2.1 (fun k hk => hV k (by omega)) t _ le_rfl
  obtain ⟨e1, e2, e3⟩ := ratio_split hX hX0 hY0
  refine ⟨hX0, hY0, ha.trans e1, hb'.trans e2, ?_⟩
  rw [hab, ha, hb']
  exact e3

end Hist

end

end PtCorr2
