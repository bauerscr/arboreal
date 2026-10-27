import Spin2.Pair.PairInitSizes
import PtCorr2.Obs.WObsStepU

/-!
# The block bound `‖inI(B)‖_{wM} ≤ ι` at coalescence; `pairInit_traj` without `hI`

Item 2 of `Log.md` ("the initial `ab` activity of `oRed … dxStd` under master constants"):

* `oTj_emb_add_le`, **`oTj_inI_le`**: `‖e^{-V}(1 + 𝒲)‖ ≤ e^{‖V‖}(1 + ‖𝒲‖)` for the block factor
  `inI` of the unreduced input (`oT_oexp_le`, submultiplicativity for `w.Sub`).
* **`pairInit_trajW`**: `pairInit_traj` with `hI` discharged, `ι = ι_W = e^{7/2}(1 + e^{L²C_W(1+16c_W²)})`
  (`iotaW`): at `j_x`, `‖inV(B)‖_{wM} ≤ 7/2` (bulk `≤ c_Rg + 8c_Mℓ²η ≤ 3/2` by `rg_inputs`, one-point
  part `≤ x_{j_x} = 2`, no `ab` part by `obsHist_coal_valid`), and `‖fullW(B)‖_{wM} ≤ e^{L²C_W(1+16c_W²)}`
  (bulk `≤ r² ≤ 1`; observable part by the step `j_x − 1 → j_x`, `wobs_hist_fullWU`, with
  `m_{j_x-1} ≤ 2m_{j_x} = 4c_W`). New inputs: `WObsBoundsU L C_W`, `ValidCore R j_x` and
  `|m²|L^{2j_x} ≤ 1` (for `rg_inputs` at `j_x`, which may equal `N_h`).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

/-- The full norm of `emb x + F` with `F` observable. -/
theorem oTj_emb_add_le {c : Obs.Case} (w : Wt) (j : ℕ) (ℓ : ℝ) (x : EvR (Lam 2 L N))
    (F : OE c (Lam 2 L N)) (hF : bulk F = 0) :
    oTj 2 L w j ℓ (((emb x : OE c (Lam 2 L N)) + F : OE c (Lam 2 L N)) : SA c (Lam 2 L N)) ≤
      Tj 2 (L : ℝ) j ℓ (x : Alg 2 L N) + oTo w j ℓ F := by
  rw [oTj_eq_bulk_add, emb_add_e, ← coe_bulk, hF, ZeroMemClass.coe_zero, add_zero]
  exact add_le_add le_rfl (PtCorr2.oTo_emb_add_le w j ℓ x F)

/-- **`‖e^{-V(B)}(1 + 𝒲(B))‖ ≤ e^{‖V(B)‖}(1 + ‖𝒲(B)‖)`** for the block factor of the input. -/
theorem oTj_inI_le {c : Obs.Case} (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
    (Dw : Fam 2 L N) (o : ObsSt c L N) (ho : o.IsObs) (w : Wt) (hw : w.Sub) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (q : Fin 2 → ℕ) {v f : ℝ} (hv0 : 0 ≤ v) (hf0 : 0 ≤ f)
    (hv : oTj 2 L w j ℓ (inV R j st g μ o q : SA c (Lam 2 L N)) ≤ ENNReal.ofReal v)
    (hf : oTj 2 L w j ℓ (fullW st Dw o q : SA c (Lam 2 L N)) ≤ ENNReal.ofReal f) :
    oTj 2 L w j ℓ (inI R j st g μ Dw o q : SA c (Lam 2 L N)) ≤
      ENNReal.ofReal (Real.exp v * (1 + f)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos hL0 _
  have hε : ε (((-inV R j st g μ o q : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e) = 0 := by
    have e1 : ((inV R j st g μ o q : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e =
        ((stVf R j st g μ q + stDelta R j st q : EvR (Lam 2 L N)) : Alg 2 L N) +
          (o.V q : SA c (Lam 2 L N)).e := emb_add_e _ _
    have e2 : (o.V q : SA c (Lam 2 L N)).e = 0 := by
      rw [← coe_bulk, ho.V q, ZeroMemClass.coe_zero]
    have e3 : ε ((stVf R j st g μ q : EvR (Lam 2 L N)) : Alg 2 L N) = 0 := by
      rw [stVf_eq_kap]; exact eps_VfamL j _ q
    rw [NegMemClass.coe_neg, SA.neg_e, map_neg, e1, e2, add_zero, AddMemClass.coe_add, map_add, e3,
      eps_stDelta, add_zero, neg_zero]
  have h1 : oTj 2 L w j ℓ (oexp (-inV R j st g μ o q) : SA c (Lam 2 L N)) ≤
      ENNReal.ofReal (Real.exp v) :=
    oT_oexp_le (E := Dir 2) (p := pPhi 2) hh hℓ hw hε hv0
      (by rw [NegMemClass.coe_neg, oT_neg]; exact hv)
  have h2 : oTj 2 L w j ℓ ((1 + fullW st Dw o q : OE c (Lam 2 L N)) : SA c (Lam 2 L N)) ≤
      ENNReal.ofReal (1 + f) := by
    rw [AddMemClass.coe_add, OneMemClass.coe_one]
    refine (oT_add_le (E := Dir 2) (p := pPhi 2) _ _).trans ?_
    rw [ENNReal.ofReal_add zero_le_one hf0, ENNReal.ofReal_one]
    exact add_le_add (oT_one_le (E := Dir 2) (p := pPhi 2) hh hℓ) hf
  show oTj 2 L w j ℓ ((oexp (-inV R j st g μ o q) * (1 + fullW st Dw o q) : OE c (Lam 2 L N)) :
    SA c (Lam 2 L N)) ≤ _
  refine (oTj_mul_le hw hℓ _ _).trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' h1 h2

/-- The block constant `ι_W = e^{7/2}(1 + e^{L²C_W(1+16c_W²)})`. -/
def iotaW (L : ℕ) (Cw cW : ℝ) : ℝ :=
  Real.exp (7 / 2) * (1 + Real.exp ((L : ℝ) ^ 2 * (Cw * (1 + 16 * cW ^ 2))))

theorem one_le_iotaW (L : ℕ) (Cw cW : ℝ) : 1 ≤ iotaW L Cw cW := by
  unfold iotaW
  have h1 : 1 ≤ Real.exp (7 / 2) := Real.one_le_exp (by norm_num)
  have h2 : 0 ≤ Real.exp ((L : ℝ) ^ 2 * (Cw * (1 + 16 * cW ^ 2))) := (Real.exp_pos _).le
  nlinarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 2000000 in
/-- **The bulk parts of `inV`, `fullW` at a scale `j ≤ N_h`**: `‖V♭ + Δ‖ ≤ 3/2`, `‖W^{lin} + D‖ ≤ 1`
(from `rg_inputs`, `apriori`, `c_Rε ≤ 1`). -/
theorem inV_fullW_bulk_le (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (t : Hist.Seq (Xs R)) (j : ℕ) (hj : j ≤ Nh)
    (ht : InDh Λ β δ κ cg cm cT ε j t) (hVc : ValidCore R j)
    (hmj : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hε1 : cR R Λ cm C₂ * ε ≤ 1) :
    (∀ q ∈ blockIdx (L := L) (N := N) j, Tj 2 (L : ℝ) j (histS R j t)
      ((stVf R j (rawHist R j t) (t j).1 (t j).2.1 q +
        stDelta R j (rawHist R j t) q : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal (3 / 2)) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) j, Tj 2 (L : ℝ) j (histS R j t)
      (((rawHist R j t).Wl + rawD R (rawHist R j t).u (t j).2.2) q : Alg 2 L N) ≤
        ENNReal.ofReal 1) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have HI := rawInv_hist R hρ0 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hρ1 : R.ρ < 1 := by linarith [hVc.2.2.2.2.1]
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ Step2.cW R Λ cm C₂ := by unfold Step2.cW; have := H.hC₂; positivity
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : Step2.cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : Step2.cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + Step2.cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    have := H.h3
    nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hg3 H.hcx]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hcR0 : 0 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hr1 : r ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcR0).trans hε1
  have hr0 : 0 ≤ r := mul_nonneg hcR0 hg.le
  obtain ⟨hVv, hΔ⟩ := rg_inputs R j hVc st HI g μ hmj hg.le (cZ R * g) hz hy hη
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · rw [AddMemClass.coe_add]
    refine (tNorm_add_le _ _).trans ?_
    have h1 := (Tj_le_Fnorm (stVf R j st g μ) hq).trans (hVv.trans (ENNReal.ofReal_le_ofReal hvr))
    have h2 := (Tj_le_Fnorm (stDelta R j st) hq).trans (hΔ.trans (ENNReal.ofReal_le_ofReal hηs))
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add hr0 (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hw := Fnorm_add_le _ _ (by positivity) (norm_nonneg _) hWl
      (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    refine (Tj_le_Fnorm _ hq).trans (hw.trans (ENNReal.ofReal_le_ofReal ?_))
    nlinarith

set_option maxHeartbeats 4000000 in
/-- **The initial `ab` activity at coalescence along a trajectory, without `hI`** (pair vertex `zV b`), from the
one-point sizes of `obs_hist_rel2_baseX` at the two points (`zV0 b`, points `(0, x)` and the
mirror `(x, 0)`), the ratio of `β`, and the constants of `kab_hist`; the only remaining input is
the block bound `hI` of the unreduced input at `j_x`, here **discharged** (`ι = ι_W`, `iotaW`) from
`WObsBoundsU`, `ValidCore R j_x` and `|m²|L^{2j_x} ≤ 1`. `M_a = 2s_{j_x}²|β_{a,j_x}|`,
`M_b = 2s_{j_x}²|β^{mir}_{a,j_x}|`. -/
theorem pairInit_trajW {C₀u ηu ε₀u C₁u : ℝ} (hKB : KObsBoundsU L R.A C₀u ηu ε₀u C₁u)
    (hC₀u : 0 ≤ C₀u) (hC₁u : 0 ≤ C₁u)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hA1 : 1 ≤ R.A)
    (t : Hist.Seq (Xs R)) (ht0 : (t 0).2.2 = 0) (ht : InDh Λ β δ κ cg cm cT ε Nh t)
    (b : ℝ) (x : Lam 2 L N) (hx1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hxN : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (hNN : Nh ≤ N)
    {cW B : ℝ} (hcW : 1 ≤ cW) (hB : 0 ≤ B)
    (hX : ∀ j ≤ Nh, OneSz R (ptsX x) (zV0 b) t j (cR R Λ cm C₂ * (t j).1) cW B)
    (hS : ∀ j ≤ Nh, OneSz R (ptsS x) (zV0 b) t j (cR R Λ cm C₂ * (t j).1) cW B)
    (hrX : ∀ j < Nh,
      ‖betaTot2 (L := L) (N := N) j (histVO2 R (ptsX x) (obsInit .two (zV0 b) (ptsX x)) t j)‖ ≤
        64 / 49 * ‖betaTot2 (L := L) (N := N) (j + 1)
          (histVO2 R (ptsX x) (obsInit .two (zV0 b) (ptsX x)) t (j + 1))‖)
    (hrS : ∀ j < Nh,
      ‖betaTot2 (L := L) (N := N) j (histVO2 R (ptsS x) (obsInit .two (zV0 b) (ptsS x)) t j)‖ ≤
        64 / 49 * ‖betaTot2 (L := L) (N := N) (j + 1)
          (histVO2 R (ptsS x) (obsInit .two (zV0 b) (ptsS x)) t (j + 1))‖)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀u)
    (hkt1 : 8 * (cx κ cT + 8 * B + 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B)) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + 8 * B + 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B)) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀u)
    (hθ' : 8 * kθ0 L R.A C₀u ηu + 16 * C₁u * (cR R Λ cm C₂ * ε) +
      8 * C₁u * (8 * (cx κ cT + 8 * B + 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B)) *
        (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hsm : R.A ^ 4 * (cx κ cT * (cR R Λ cm C₂ * ε) ^ 3 +
      8 * B * (cR R Λ cm C₂ * ε) ^ 2 * (2 * cW) +
      10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) * (cR R Λ cm C₂ * ε) * (2 * cW) ^ 2) ≤ 1)
    {Cw : ℝ} (hWB : WObsBoundsU L Cw) (hCw : 0 ≤ Cw)
    (hVc : ValidCore R (Obs.coal L (0 : Lam 2 L N) x))
    (hmsj : |R.msq| * ((L : ℝ) ^ (Obs.coal L (0 : Lam 2 L N) x)) ^ 2 ≤ 1)
    (Y : Finset (Lam 2 L N)) :
    ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x) (histS R (Obs.coal L (0 : Lam 2 L N) x) t)
          ((redHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Obs.coal L (0 : Lam 2 L N) x)
            (dxStd (L := L) (N := N) x) t).K Y : SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (pM R (ptsX x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x) *
        pM R (ptsS x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x) *
        (2 * iotaW L Cw cW * R.A) ^ ((L + 18) ^ 2)) := by
  set j₀ := Obs.coal L (0 : Lam 2 L N) x with hj₀
  set c := cR R Λ cm C₂ with hc
  set oX := obsInit .two (zV0 b) (ptsX x) with hoX
  set oS := obsInit .two (zV0 b) (ptsS x) with hoS
  set aX : ℕ → ℝ := fun j => pM R (ptsX x) (zV0 b) t j with haX
  set aS : ℕ → ℝ := fun j => pM R (ptsS x) (zV0 b) t j with haS
  set Ma := aX j₀ with hMad
  set Mb := aS j₀ with hMbd
  have hc2 : 2 ≤ c := two_le_cR R H.hcmu H.hC₂
  have hs : ∀ j, 0 < histS R j t := fun j => histS_pos' R hρ0 hρ8 t j
  have haX0 : ∀ j, 0 ≤ aX j := fun j => by
    show 0 ≤ 2 * histS R j t ^ 2 * _; positivity
  have haS0 : ∀ j, 0 ≤ aS j := fun j => by
    show 0 ≤ 2 * histS R j t ^ 2 * _; positivity
  have hMa : 0 < Ma := by
    have := (hX j₀ hxN).1; have := hs j₀
    show 0 < 2 * histS R j₀ t ^ 2 * _; positivity
  have hMb : 0 < Mb := by
    have := (hS j₀ hxN).1; have := hs j₀
    show 0 < 2 * histS R j₀ t ^ 2 * _; positivity
  set xx : ℕ → ℝ := fun j => aX j / Ma + aS j / Mb with hxx
  set mm : ℕ → ℝ := fun j => max (cW * xx j) 1 with hmmd
  set k1 : ℕ → ℝ := fun j => 8 * B * (c * (t j).1) ^ 2 * mm j with hk1d
  have hxx0 : ∀ j, 0 ≤ xx j := fun j => by
    have := haX0 j; have := haS0 j; show 0 ≤ aX j / Ma + aS j / Mb; positivity
  have hmm1 : ∀ j, 1 ≤ mm j := fun j => le_max_right _ _
  have hmm0 : ∀ j, 0 < mm j := fun j => lt_of_lt_of_le one_pos (hmm1 j)
  have hcxx : ∀ j, cW * xx j ≤ mm j := fun j => le_max_left _ _
  have hxxm : ∀ j, xx j ≤ mm j := fun j =>
    (le_mul_of_one_le_left (hxx0 j) hcW).trans (hcxx j)
  have hg0 : ∀ j ≤ Nh, 0 ≤ (t j).1 := fun j hj => (ht.1 j hj).1.le
  have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
  have hc0 : 0 ≤ c := by linarith
  have hr0 : ∀ j ≤ Nh, 0 ≤ c * (t j).1 := fun j hj => mul_nonneg hc0 (hg0 j hj)
  have hrε : ∀ j ≤ Nh, c * (t j).1 ≤ c * ε := fun j hj => mul_le_mul_of_nonneg_left (hgε j hj) hc0
  -- the mirror
  have hcmp : ∀ j, _ := fun j => prjSt_eq_cmp (mirror_b_eq R t b x j)
  -- the coalescence invariant
  have hinv := obsHist_coalInv_valid R (ptsX x) oX (obsInit_isObs .two _ _)
    (coalInv_init .two (V := zV0 b) ⟨rfl, rfl, rfl, rfl⟩ (ptsX x)) hL hρ0
    (fun k hk => hV k (lt_of_lt_of_le (show k < j₀ from hk) hxN)) t
  -- the one-point components
  have hVa : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R (ptsX x) oX j t).V c' : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (aX j) := fun j hj c' hc' => by
    rw [← oTo_wA]; exact vobs_le_of_shA2 R (ptsX x) (zV0 b) rfl t j (hs j) (hX j hj).2.1 c' hc'
  have hVb : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R (ptsX x) oX j t).V c' : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (aS j) := fun j hj c' hc' => by
    rw [(hcmp j).1 c', ← oTo_wA]
    exact vobs_le_of_shA2 R (ptsS x) (zV0 b) rfl t j (hs j) (hS j hj).2.1 c' hc'
  have hWa : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R (ptsX x) oX j t).W c' : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (cW * (c * (t j).1) * aX j) := fun j hj c' hc' => by
    rw [← oTo_wA]; exact (hX j hj).2.2.1 c' hc'
  have hWb : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R (ptsX x) oX j t).W c' : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (cW * (c * (t j).1) * aS j) := fun j hj c' hc' => by
    rw [(hcmp j).2.1 c', ← oTo_wA]; exact (hS j hj).2.2.1 c' hc'
  have hKa : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R (ptsX x) oX j t).K X : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (8 * cW * B * (c * (t j).1) ^ 2 * aX j) := fun j hj Z hZ => by
    rw [← oTo_wA]
    refine ((hX j hj).2.2.2 Z hZ).trans (le_of_eq (congrArg _ ?_))
    show _ = 8 * cW * B * (c * (t j).1) ^ 2 * (2 * histS R j t ^ 2 * _); ring
  have hKb' : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS R j t) ((obsHist R (ptsX x) oX j t).K X : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (8 * cW * B * (c * (t j).1) ^ 2 * aS j) := fun j hj X hX => by
    rw [(hcmp j).2.2 X, ← oTo_wA]
    refine ((hS j hj).2.2.2 X hX).trans (le_of_eq (congrArg _ ?_))
    show _ = 8 * cW * B * (c * (t j).1) ^ 2 * (2 * histS R j t ^ 2 * _); ring
  -- the `wM` / `wM1` bounds
  have hK1 : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) j (histS R j t) ((obsHist R (ptsX x) oX j t).K X) ≤
        ENNReal.ofReal (8 * B * (c * (t j).1) ^ 2 * (cW * xx j)) := fun j hj X hX => by
    have hq : 0 ≤ 8 * cW * B * (c * (t j).1) ^ 2 := by
      have := hr0 j hj; positivity
    refine (reg_oTo_wM1_le hMa hMb j _ _ _ (mul_nonneg hq (haX0 j)) (mul_nonneg hq (haS0 j))
      (hKa j hj X hX) (hKb' j hj X hX)).trans (le_of_eq (congrArg _ ?_))
    show 8 * cW * B * (c * (t j).1) ^ 2 * aX j / Ma + 8 * cW * B * (c * (t j).1) ^ 2 * aS j / Mb =
      8 * B * (c * (t j).1) ^ 2 * (cW * (aX j / Ma + aS j / Mb))
    ring
  have hVo : ∀ j < j₀, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R (ptsX x) oX j t).V c') ≤
        ENNReal.ofReal (mm j) := fun j hj c' hc' =>
    (oTo_wM_le_of_ab hMa hMb j _ _ ((hinv j hj).Vab c') (haX0 j) (haS0 j)
      (hVa j (by omega) c' hc') (hVb j (by omega) c' hc')).trans
        (ENNReal.ofReal_le_ofReal (hxxm j))
  have hWo : ∀ j < j₀, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R (ptsX x) oX j t).W c') ≤
        ENNReal.ofReal (c * (t j).1 * mm j) := fun j hj c' hc' => by
    have hq : 0 ≤ cW * (c * (t j).1) := mul_nonneg (by linarith) (hr0 j (by omega))
    refine (oTo_wM_le_of_ab hMa hMb j _ _ ((hinv j hj).Wab c') (mul_nonneg hq (haX0 j))
      (mul_nonneg hq (haS0 j)) (hWa j (by omega) c' hc') (hWb j (by omega) c' hc')).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have e : cW * (c * (t j).1) * aX j / Ma + cW * (c * (t j).1) * aS j / Mb =
        c * (t j).1 * (cW * xx j) := by
      show _ = c * (t j).1 * (cW * (aX j / Ma + aS j / Mb)); ring
    rw [e]; exact mul_le_mul_of_nonneg_left (hcxx j) (hr0 j (by omega))
  -- the ratio
  have haXr : ∀ j < Nh, aX j ≤ 2 * aX (j + 1) := fun j hj => by
    have h1 := histS_sq_ratio R hρ0 hρ8 t j
    have h2 := hrX j hj
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ histS R (j + 1) t ^ 2 * ‖betaTot2 (L := L) (N := N) (j + 1)
        (histVO2 R (ptsX x) (obsInit .two (zV0 b) (ptsX x)) t (j + 1))‖ := by positivity
    show 2 * histS R j t ^ 2 * _ ≤ 2 * (2 * histS R (j + 1) t ^ 2 * _)
    nlinarith
  have haSr : ∀ j < Nh, aS j ≤ 2 * aS (j + 1) := fun j hj => by
    have h1 := histS_sq_ratio R hρ0 hρ8 t j
    have h2 := hrS j hj
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ histS R (j + 1) t ^ 2 * ‖betaTot2 (L := L) (N := N) (j + 1)
        (histVO2 R (ptsS x) (obsInit .two (zV0 b) (ptsS x)) t (j + 1))‖ := by positivity
    show 2 * histS R j t ^ 2 * _ ≤ 2 * (2 * histS R (j + 1) t ^ 2 * _)
    nlinarith
  have hmm' : ∀ j < j₀, mm j ≤ 2 * mm (j + 1) := fun j hj => by
    have h1 : xx j ≤ 2 * xx (j + 1) := by
      have e1 := div_le_div_of_nonneg_right (haXr j (by omega)) hMa.le
      have e2 := div_le_div_of_nonneg_right (haSr j (by omega)) hMb.le
      show aX j / Ma + aS j / Mb ≤ 2 * (aX (j + 1) / Ma + aS (j + 1) / Mb)
      rw [mul_div_assoc] at e1 e2
      linarith
    refine max_le ?_ (by linarith [hmm1 (j + 1)])
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ cW)
    linarith [hcxx (j + 1)]
  have hrm : ∀ j < j₀, c * (t j).1 ≤ mm j := fun j hj =>
    ((hrε j (by omega)).trans hε1).trans (hmm1 j)
  have hk10 : ∀ j, 0 ≤ k1 j := fun j => by
    have := hmm0 j; show 0 ≤ 8 * B * (c * (t j).1) ^ 2 * mm j; positivity
  -- the unreduced `ab` chain
  have hab := kab_hist R hKB hC₀u hC₁u hSB hV hm hβ hδ1 H (ptsX x) (wM Ma Mb) (wM_sub Ma Mb)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) oX
    (obsInit_isObs .two _ _) (obsLocInv_init .two _ _) (obsSymInv_init .two _ _) t
    (fun X => by simp [hoX, obsInit]) j₀ hxN
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
    (fun j hj X hX => (hinv j hj).Kab X hX) mm k1 (8 * B) (by positivity) hmm0 hmm' hk10
    (fun j _ => le_rfl) hrm hε1 hεε hkt1 hktε hθ' hVo hWo
    (fun j hj X hX => by
      rw [wOne_wM]
      refine (hK1 j (by omega) X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hcxx j) (by have := hr0 j (by omega); positivity))
    j₀ le_rfl
  have hxxj : xx j₀ = 2 := by
    show aX j₀ / Ma + aS j₀ / Mb = 2
    rw [← hMad, ← hMbd, div_self hMa.ne', div_self hMb.ne']; norm_num
  have hmj : mm j₀ = 2 * cW := by
    show max (cW * xx j₀) 1 = 2 * cW
    rw [hxxj, mul_comm]; exact max_eq_left (by linarith)
  obtain ⟨-, -, hKeq⟩ := obsHist_zV0 R (ptsX x) t b ht0 j₀ hx1
  -- the bulk activity
  have hVj : ∀ i < j₀, ValidAt R i := fun i hi => hV i (by omega)
  have HI := rawInv_hist R hρ0 j₀ hVj t
  have hZ : (rawHist R j₀ t).Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hKn := Knorm_rawK R HI.hu hZ (t j₀).2.2
  obtain ⟨hgj, hgεj, -, hxj⟩ := ht.1 j₀ hxN
  have hgc : (t j₀).1 ≤ c * ε := by
    have hε0 : 0 ≤ ε := hgj.le.trans hgεj
    nlinarith
  have hcx := H.hcx
  set kb : ℝ := cx κ cT * (c * ε) ^ 3 with hkb
  set kx : ℝ := 8 * B * (c * ε) ^ 2 * (2 * cW) with hkx
  set k2 : ℝ := 10 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) * (c * ε) * (2 * cW) ^ 2
    with hk2
  have hB2 : 0 ≤ kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) := by
    have hA0 : (0 : ℝ) ≤ R.A / 2 := by linarith
    have : 0 ≤ kθ0 L R.A C₀u ηu := by
      unfold kθ0; have := Real.rpow_nonneg hA0 (-ηu); positivity
    unfold kB2; positivity
  have hcε0 : 0 ≤ c * ε := (hr0 j₀ hxN).trans (hrε j₀ hxN)
  have hKb : ∀ X, IsConn j₀ X → ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j₀ (histS R j₀ t) (rawK R (rawHist R j₀ t).u (t j₀).2.2 X : Alg 2 L N) ≤
        ENNReal.ofReal kb := by
    intro X hX
    have h1 : ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
        Tj 2 (L : ℝ) j₀ (histS R j₀ t) (rawK R (rawHist R j₀ t).u (t j₀).2.2 X : Alg 2 L N) ≤
        Knorm j₀ (fscale (rawHist R j₀ t).Z * R.ℓ) R.A (rawK R (rawHist R j₀ t).u (t j₀).2.2) :=
      le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) j₀) =>
        ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
          Tj 2 (L : ℝ) j₀ (fscale (rawHist R j₀ t).Z * R.ℓ)
            (rawK R (rawHist R j₀ t).u (t j₀).2.2 X : Alg 2 L N)) X
        (by simp [connSets]; exact hX)
    refine (h1.trans (le_of_eq hKn)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : ‖(t j₀).2.2.2‖ ≤ cx κ cT * (t j₀).1 ^ 3 := (norm_snd_le _).trans hxj
    have h3 : (t j₀).1 ^ 3 ≤ (c * ε) ^ 3 := pow_le_pow_left₀ hgj.le hgc 3
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hcx)
  have hKx : ∀ X, IsConn j₀ X → ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
      oTo (wM1 Ma Mb) j₀ (histS R j₀ t)
        ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) j₀ t).K X) ≤ ENNReal.ofReal kx := by
    intro X hX
    rw [hKeq]
    refine (hK1 j₀ hxN X hX).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : cW * xx j₀ = 2 * cW := by rw [hxxj]; ring
    rw [e, hkx]
    have h1 : (c * (t j₀).1) ^ 2 ≤ (c * ε) ^ 2 := pow_le_pow_left₀ (hr0 j₀ hxN) (hrε j₀ hxN) 2
    have : 0 ≤ 2 * cW := by linarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * B)
    nlinarith
  have hK2 : ∀ X, IsConn j₀ X → ENNReal.ofReal (R.A ^ (nb j₀ X - 2 ^ 2)) *
      ((wM Ma Mb).ab * Tj 2 (L : ℝ) j₀ (histS R j₀ t)
        ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) j₀ t).K X :
          SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2 := by
    intro X hX
    rw [hKeq]
    refine (hab X hX).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hmj, hk2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrε j₀ hxN) (by positivity))
      (sq_nonneg _)
  -- the block bound `‖inI(B)‖_{wM} ≤ ι_W` (item 2)
  have hι : 1 ≤ iotaW L Cw cW := one_le_iotaW L Cw cW
  have htj : InDh Λ β δ κ cg cm cT ε j₀ t :=
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  obtain ⟨hbV, hbW⟩ := inV_fullW_bulk_le R hSB hV hm hβ hδ1 H hρ0 t j₀ hxN htj hVc hmsj hε1
  obtain ⟨hVeq, hWeq, -⟩ := obsHist_zV0 R (ptsX x) t b ht0 j₀ hx1
  have hVab := (obsHist_coal_valid R (ptsX x) oX (obsInit_isObs .two _ _)
    (coalInv_init .two (V := zV0 b) ⟨rfl, rfl, rfl, rfl⟩ (ptsX x)) hL hρ0
    (fun k hk => hV k (lt_of_lt_of_le (show k < j₀ from hk) hxN)) t j₀ le_rfl).1
  have hj1 : j₀ - 1 < j₀ := by omega
  have e1 : j₀ - 1 + 1 = j₀ := by omega
  set E := (L : ℝ) ^ 2 * (Cw * (1 + 16 * cW ^ 2)) with hE
  have hE0 : 0 ≤ E := mul_nonneg (by positivity) (mul_nonneg hCw (by positivity))
  have hWo' : ∀ q, oTo (wM Ma Mb) j₀ (histS R j₀ t) ((obsHist R (ptsX x) oX j₀ t).W q) ≤
      ENNReal.ofReal (Real.exp E - 1) := by
    intro q
    have h := wobs_hist_fullWU R hWB hSB hV hm hβ hδ1 H (ptsX x) (wM Ma Mb) (wM_sub Ma Mb)
      oX (obsInit_isObs .two _ _) (obsLocInv_init .two _ _) t (j₀ - 1) (by omega)
      ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩ (mm (j₀ - 1)) (hrm _ hj1)
      ((hrε _ (by omega)).trans hε1) (hVo _ hj1) (hWo _ hj1) q
    rw [e1] at h
    try rw [← hc] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm1 : mm (j₀ - 1) ≤ 4 * cW := by
      have := hmm' (j₀ - 1) hj1; rw [e1, hmj] at this; linarith
    have hm0' := hmm0 (j₀ - 1)
    have hr' : c * (t (j₀ - 1)).1 ≤ 1 := (hrε _ (by omega)).trans hε1
    have hsq : mm (j₀ - 1) ^ 2 ≤ 16 * cW ^ 2 := by nlinarith
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hin : Cw * (c * (t (j₀ - 1)).1 + mm (j₀ - 1) ^ 2) ≤ Cw * (1 + 16 * cW ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hCw
    have : (L : ℝ) ^ 2 * (Cw * (c * (t (j₀ - 1)).1 + mm (j₀ - 1) ^ 2)) ≤ E :=
      mul_le_mul_of_nonneg_left hin hL2
    linarith [Real.exp_le_exp.2 this]
  have hI : ∀ q ∈ blocks j₀ (dxStd (L := L) (N := N) x),
      oTj 2 L (wM Ma Mb) j₀ (histS R j₀ t)
        (inI R j₀ (rawHist R j₀ t) (t j₀).1 (t j₀).2.1 (rawD R (rawHist R j₀ t).u (t j₀).2.2)
          (obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) j₀ t) q : SA .two (Lam 2 L N)) ≤
        ENNReal.ofReal (iotaW L Cw cW) := by
    intro q hq
    have hqI : q ∈ blockIdx (L := L) (N := N) j₀ := mem_blockIdx_of_mem_blocks hq
    have ho := obsHist_isObs R (ptsX x) (obsInit .two (zV b) (ptsX x))
      (obsInit_isObs .two _ _) j₀ t
    refine (oTj_inI_le R j₀ _ _ _ _ _ ho (wM Ma Mb) (wM_sub Ma Mb) (hs j₀) q
      (v := 7 / 2) (f := Real.exp E) (by norm_num) (Real.exp_pos _).le ?_ ?_).trans (le_of_eq ?_)
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.V q)).trans ?_
      rw [hVeq]
      have hVo2 : oTo (wM Ma Mb) j₀ (histS R j₀ t) ((obsHist R (ptsX x) oX j₀ t).V q) ≤
          ENNReal.ofReal 2 :=
        (oTo_wM_le_of_ab hMa hMb j₀ _ _ (hVab q) (haX0 j₀) (haS0 j₀) (hVa j₀ hxN q hqI)
          (hVb j₀ hxN q hqI)).trans (le_of_eq (congrArg ENNReal.ofReal hxxj))
      refine (add_le_add (hbV q hqI) hVo2).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.W q)).trans ?_
      rw [hWeq]
      refine (add_le_add (hbW q hqI) (hWo' q)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add zero_le_one (by linarith [Real.one_le_exp hE0])]
      congr 1; ring
    · rfl
  have hmain := redHist_K_ab_le_sizes R (ptsX x) (obsInit .two (zV b) (ptsX x)) t
    (obsInit_isObs .two _ _) hMa hMb (hs j₀) hA1 hι (by positivity) (by positivity)
    (by positivity) hsm hI hKb hKx hK2 Y
  refine hmain.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by nlinarith) (nb_dxStd_le (by omega) x (by omega)))
    (mul_pos hMa hMb).le))

end Traj

/-! ### The conclusion along admissible trajectories, without `hI` -/

/-- **The initial `ab` activity of `oRed … dxStd` under master constants**, along every
admissible trajectory and every `x` with `1 ≤ j_x ≤ N_h`: `M_a = 2s_{j_x}²|β_{a,j_x}| > 0`,
`M_b = 2s_{j_x}²|β^{mir}_{a,j_x}| > 0` (vertex `zV0 b`, points `(0, x)` and `(x, 0)`), and
`A^{(|𝓑(Y)|-4)_+}‖K'_{j_x}(Y)_{ab}‖ ≤ M_aM_b(2ιA)^{(L+18)²}` for the given constant `ι` (no block
hypothesis: `PairInitConclU` with `hI` discharged). -/
def PairInitConclW (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε ι : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ x : Lam 2 L N, 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    0 < pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) ∧
    0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) ∧
    ∀ Y : Finset (Lam 2 L N),
        ENNReal.ofReal (A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) Y - 2 ^ 2)) *
            Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x)
              (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K Y : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x) *
            pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x) * (2 * ι * A) ^ ((L + 18) ^ 2))

end

end Spin2
