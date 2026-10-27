import Spin2.Pair.PairTop6
import Spin2.Pair.PairInitW
import PtCorr2.Last.TopCoal3

/-!
# Top coalescence: the seed of the reduced state at `N - 1` along one trajectory (T5)

For `x` with `j_x ≥ N_h + 1`, the reduced state `redTop` at scale `N_h + 1` (`V' = 𝒲' = 0`,
`K' = kRed` of the input of the last step, covering polymer `dxTop`). With the weights
`M_a = 2s_{N_h}²|β_{a,N_h}|`, `M_b` (mirror) of the `zV0 b` histories (`pM … N_h`):

* the unreduced `ab` chain up to `N_h + 1` (`kab_hist_top`: `kab_hist` and the step `N_h → N_h + 1`
  under `ValidAtL`), the coalescence invariant for `j ≤ N_h < j_x` (`obsHist_coalInv_le`);
* the `𝒲^{obs}` step `N_h → N_h + 1` in the full `wM` norm (`wobs_hist_fullWUL`);
* the bulk inputs of the last step (`GlueOut`, `bulk_last_in`): `‖V♭ + Δ‖ ≤ 3/2`, `‖W + D‖ ≤ 1`,
  `‖K‖_A ≤ C_fǧ³`;
* `‖inI(B)‖_{wM} ≤ ι_T = e^{3/2+v_T}(1 + e^{L²C_W(1+4c_W²)})` (`oTj_inI_le`) and
  `A^{|𝓑(X)|}‖inK(X)‖_{wM} ≤ 1`, hence (`kRed_poly_le`, `|𝓑_{N-1}(D)| ≤ L²`)

  `A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖_{wM(M_a,M_b)} ≤ (2ι_TA)^{L²}` (**`topSeed_traj`**).

The one-point sizes at `N_h + 1` (`v_T`, `k_{xT}`) are inputs (from `LastL1Concl`,
`LastObsConclK` in the master wrapper).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

/-- The block constant of the top seed. -/
def iotaT (L : ℕ) (Cw cW vT : ℝ) : ℝ :=
  Real.exp (3 / 2 + vT) * (1 + Real.exp ((L : ℝ) ^ 2 * (Cw * (1 + 4 * cW ^ 2))))

theorem one_le_iotaT (L : ℕ) (Cw cW : ℝ) {vT : ℝ} (hvT : 0 ≤ vT) : 1 ≤ iotaT L Cw cW vT := by
  unfold iotaT
  have h1 : 1 ≤ Real.exp (3 / 2 + vT) := Real.one_le_exp (by linarith)
  have h2 : 0 ≤ Real.exp ((L : ℝ) ^ 2 * (Cw * (1 + 4 * cW ^ 2))) := (Real.exp_pos _).le
  nlinarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The coalescence invariant up to `N_h`** for `j_x > N_h` (`ValidAt` below `N_h`). -/
theorem obsHist_coalInv_le {c : Obs.Case} (P : ObsPts 2 L N) (o₀ : ObsSt c L N)
    (h₀ : o₀.IsObs) (hinv₀ : ObsCoalInv P 0 o₀) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ : 0 ≤ R.ρ)
    (hV : ∀ k < Nh, ValidAt R k) (hc : Nh < coal L P.a P.b) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ j ≤ Nh, ObsCoalInv P j (obsHist R P o₀ j t) := by
  intro j
  induction j with
  | zero => intro _; exact hinv₀
  | succ k ih =>
    intro hk
    rw [obsHist_succ]
    have hVk := hV k (by omega)
    have hI := rawInv_hist R hρ k (fun i hi => hV i (by omega)) t
    exact obsStep_coalInv R P k _ _ _ _ _ (ih (by omega))
      (obsHist_isObs R P o₀ h₀ k t) hL (by have := hVk.1; omega)
      (fun x y hxy => (RawInv.cov hVk hI).1.range (by have := hVk.1; omega) x y hxy)
      (pow_le_of_lt_coal (by omega))

set_option maxHeartbeats 8000000 in
/-- **The seed of the reduced state at `N_h + 1`** (one trajectory, one `x` with `j_x ≥ N_h + 1`). -/
theorem topSeed_traj {C₀u ηu ε₀u C₁u : ℝ} (hKB : KObsBoundsU L R.A C₀u ηu ε₀u C₁u)
    (hC₀u : 0 ≤ C₀u) (hC₁u : 0 ≤ C₁u)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (hVN : LastN.ValidLast R (Nh + 1))
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1) (hmN : |R.msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8) (hA1 : 1 ≤ R.A)
    (t : Hist.Seq (Xs R)) (ht0 : (t 0).2.2 = 0) (ht : InDh Λ β δ κ cg cm cT ε Nh t)
    (b : ℝ) (x : Lam 2 L N) (hjx : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x) (hNN : Nh + 2 = N)
    (hNh1 : 1 ≤ Nh)
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
    {Cw : ℝ} (hWB : WObsBoundsU L Cw) (hCw : 0 ≤ Cw)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hG : GlueOut R Nh Cf t)
    (hs1 : 2 * (Cf * (t Nh).1) ≤ R.ρ) (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (t Nh).1) ≤ 1 / 2)
    (hvb : cM * R.ℓ ^ 2 * (4 * (Cf * (t Nh).1)) + 8 * R.ℓ ^ 4 * (Cf * (t Nh).1) ≤ 1)
    (hwb : 2 * (Cf * (t Nh).1 ^ 2) ≤ 1)
    {vT kxT : ℝ} (hvT : 0 ≤ vT) (hkxT : 0 ≤ kxT)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      oTo (wM (pM R (ptsX x) (zV0 b) t Nh) (pM R (ptsS x) (zV0 b) t Nh)) (Nh + 1)
        (histS R (Nh + 1) t) ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).V q) ≤
        ENNReal.ofReal vT)
    (hKt : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      oTo (wM1 (pM R (ptsX x) (zV0 b) t Nh) (pM R (ptsS x) (zV0 b) t Nh)) (Nh + 1)
        (histS R (Nh + 1) t) ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X) ≤
        ENNReal.ofReal kxT)
    (hsmT : R.A ^ 4 * (Cf * (t Nh).1 ^ 3 + kxT +
      2 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) * (cR R Λ cm C₂ * (t Nh).1) *
        (2 * cW) ^ 2) ≤ 1) :
    0 < pM R (ptsX x) (zV0 b) t Nh ∧ 0 < pM R (ptsS x) (zV0 b) t Nh ∧
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      oTo (wM (pM R (ptsX x) (zV0 b) t Nh) (pM R (ptsS x) (zV0 b) t Nh)) (Nh + 1)
        (histS R (Nh + 1) t)
        ((redTop R (ptsX x) (obsInit .two (zV b) (ptsX x)) (dxTop Nh x) Nh t).K X) ≤
      ENNReal.ofReal ((2 * iotaT L Cw cW vT * R.A) ^ (L ^ 2)) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : 0 < R.A := Fact.out
  set c := cR R Λ cm C₂ with hc
  set oX := obsInit .two (zV0 b) (ptsX x) with hoX
  set aX : ℕ → ℝ := fun j => pM R (ptsX x) (zV0 b) t j with haX
  set aS : ℕ → ℝ := fun j => pM R (ptsS x) (zV0 b) t j with haS
  set Ma := aX Nh with hMad
  set Mb := aS Nh with hMbd
  have hc2 : 2 ≤ c := two_le_cR R H.hcmu H.hC₂
  have hs : ∀ j, 0 < histS R j t := fun j => histS_pos' R hρ0 hρ8 t j
  have haX0 : ∀ j, 0 ≤ aX j := fun j => by
    show 0 ≤ 2 * histS R j t ^ 2 * _; positivity
  have haS0 : ∀ j, 0 ≤ aS j := fun j => by
    show 0 ≤ 2 * histS R j t ^ 2 * _; positivity
  have hMa : 0 < Ma := by
    have := (hX Nh le_rfl).1; have := hs Nh
    show 0 < 2 * histS R Nh t ^ 2 * _; positivity
  have hMb : 0 < Mb := by
    have := (hS Nh le_rfl).1; have := hs Nh
    show 0 < 2 * histS R Nh t ^ 2 * _; positivity
  refine ⟨hMa, hMb, ?_⟩
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
  -- the coalescence invariant up to `N_h`
  have hinv := obsHist_coalInv_le R (ptsX x) oX (obsInit_isObs .two _ _)
    (coalInv_init .two (V := zV0 b) ⟨rfl, rfl, rfl, rfl⟩ (ptsX x)) hL hρ0 hV
    (show Nh < coal L (ptsX x).a (ptsX x).b from hjx) t
  -- the one-point components up to `N_h`
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
  have hVo : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R (ptsX x) oX j t).V c') ≤
        ENNReal.ofReal (mm j) := fun j hj c' hc' =>
    (oTo_wM_le_of_ab hMa hMb j _ _ ((hinv j hj).Vab c') (haX0 j) (haS0 j)
      (hVa j hj c' hc') (hVb j hj c' hc')).trans (ENNReal.ofReal_le_ofReal (hxxm j))
  have hWo : ∀ j ≤ Nh, ∀ c' ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHist R (ptsX x) oX j t).W c') ≤
        ENNReal.ofReal (c * (t j).1 * mm j) := fun j hj c' hc' => by
    have hq : 0 ≤ cW * (c * (t j).1) := mul_nonneg (by linarith) (hr0 j hj)
    refine (oTo_wM_le_of_ab hMa hMb j _ _ ((hinv j hj).Wab c') (mul_nonneg hq (haX0 j))
      (mul_nonneg hq (haS0 j)) (hWa j hj c' hc') (hWb j hj c' hc')).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have e : cW * (c * (t j).1) * aX j / Ma + cW * (c * (t j).1) * aS j / Mb =
        c * (t j).1 * (cW * xx j) := by
      show _ = c * (t j).1 * (cW * (aX j / Ma + aS j / Mb)); ring
    rw [e]; exact mul_le_mul_of_nonneg_left (hcxx j) (hr0 j hj)
  -- the ratio
  have haXr : ∀ j < Nh, aX j ≤ 2 * aX (j + 1) := fun j hj => by
    have h1 := histS_sq_ratio R hρ0 hρ8 t j
    have h2 := hrX j hj
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ histS R (j + 1) t ^ 2 * ‖betaTot2 (L := L) (N := N) (j + 1)
        (histVO2 R (ptsX x) (obsInit .two (zV0 b) (ptsX x)) t (j + 1))‖ := by positivity
    show 2 * histS R j t ^ 2 * _ ≤ 2 * (2 * histS R (j + 1) t ^ 2 * _)
    linarith
  have haSr : ∀ j < Nh, aS j ≤ 2 * aS (j + 1) := fun j hj => by
    have h1 := histS_sq_ratio R hρ0 hρ8 t j
    have h2 := hrS j hj
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have h4 : 0 ≤ histS R (j + 1) t ^ 2 * ‖betaTot2 (L := L) (N := N) (j + 1)
        (histVO2 R (ptsS x) (obsInit .two (zV0 b) (ptsS x)) t (j + 1))‖ := by positivity
    show 2 * histS R j t ^ 2 * _ ≤ 2 * (2 * histS R (j + 1) t ^ 2 * _)
    linarith
  have hmm' : ∀ j < Nh, mm j ≤ 2 * mm (j + 1) := fun j hj => by
    have h1 : xx j ≤ 2 * xx (j + 1) := by
      have e1 := div_le_div_of_nonneg_right (haXr j hj) hMa.le
      have e2 := div_le_div_of_nonneg_right (haSr j hj) hMb.le
      show aX j / Ma + aS j / Mb ≤ 2 * (aX (j + 1) / Ma + aS (j + 1) / Mb)
      rw [mul_div_assoc] at e1 e2
      linarith
    refine max_le ?_ (by linarith [hmm1 (j + 1)])
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ cW)
    linarith [hcxx (j + 1)]
  have hrm : ∀ j ≤ Nh, c * (t j).1 ≤ mm j := fun j hj =>
    ((hrε j hj).trans hε1).trans (hmm1 j)
  have hk10 : ∀ j, 0 ≤ k1 j := fun j => by
    have := hmm0 j; show 0 ≤ 8 * B * (c * (t j).1) ^ 2 * mm j; positivity
  -- the unreduced `ab` chain up to `N_h + 1`
  have hab := kab_hist_top R hKB hC₀u hC₁u hSB hV hVL hm hmNh hβ hδ1 H (ptsX x) (wM Ma Mb)
    (wM_sub Ma Mb) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) oX
    (obsInit_isObs .two _ _) (obsLocInv_init .two _ _) (obsSymInv_init .two _ _) t
    (fun X => by simp [hoX, obsInit]) ht (fun j hj X hX => (hinv j hj).Kab X hX) mm k1 (8 * B)
    (by positivity) hmm0 hmm' hk10 (fun j _ => le_rfl) hrm hε1 hεε hkt1 hktε hθ' hVo hWo
    (fun j hj X hX => by
      rw [wOne_wM]
      refine (hK1 j hj X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hcxx j) (by have := hr0 j hj; positivity))
  have hxxj : xx Nh = 2 := by
    show aX Nh / Ma + aS Nh / Mb = 2
    rw [← hMad, ← hMbd, div_self hMa.ne', div_self hMb.ne']; norm_num
  have hmj : mm Nh = 2 * cW := by
    show max (cW * xx Nh) 1 = 2 * cW
    rw [hxxj, mul_comm]; exact max_eq_left (by linarith)
  obtain ⟨hVeq, hWeq, hKeq⟩ := obsHist_zV0 R (ptsX x) t b ht0 (Nh + 1) (by omega)
  -- the `𝒲^{obs}` step `N_h → N_h + 1`
  set E := (L : ℝ) ^ 2 * (Cw * (1 + 4 * cW ^ 2)) with hE
  have hE0 : 0 ≤ E := mul_nonneg (by positivity) (mul_nonneg hCw (by positivity))
  have hWo' : ∀ q, oTo (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
      ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).W q) ≤
      ENNReal.ofReal (Real.exp E - 1) := by
    intro q
    have h := wobs_hist_fullWUL R hWB hSB hV hVL hm hmNh hβ hδ1 H (ptsX x) (wM Ma Mb)
      (wM_sub Ma Mb) oX (obsInit_isObs .two _ _) (obsLocInv_init .two _ _) t Nh rfl ht
      (mm Nh) (hrm Nh le_rfl) ((hrε Nh le_rfl).trans hε1) (hVo Nh le_rfl) (hWo Nh le_rfl) q
    rw [hWeq]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hmj]
    have hr' : c * (t Nh).1 ≤ 1 := (hrε Nh le_rfl).trans hε1
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hin : Cw * (c * (t Nh).1 + (2 * cW) ^ 2) ≤ Cw * (1 + 4 * cW ^ 2) :=
      mul_le_mul_of_nonneg_left (by have e : (2 * cW) ^ 2 = 4 * cW ^ 2 := by ring
                                    linarith) hCw
    have : (L : ℝ) ^ 2 * (Cw * (c * (t Nh).1 + (2 * cW) ^ 2)) ≤ E :=
      mul_le_mul_of_nonneg_left hin hL2
    linarith [Real.exp_le_exp.2 this]
  -- the bulk inputs of the last step
  set st := (histOut R Nh t).st with hst
  have Hst : RawInv R (Nh + 1) st := rawInv_histU R hV hVL t (Nh + 1) le_rfl
  have hDm : (histOut R Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).2.1
  have hKm : (histOut R Nh t).K ∈ ASub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).2.2
  obtain ⟨⟨hz, hy, hnu, hgn, hgre, hWl, hDd, hKk⟩, -⟩ := hG
  set gg := (t Nh).1 with hgg
  have hgg0 : 0 ≤ gg := hg0 Nh le_rfl
  have hCg : 0 ≤ Cf * gg := mul_nonneg hCf hgg0
  obtain ⟨hVv, hWw, -, -, -, -, -, hΔ⟩ := bulk_last_in R hVN hL Hst (histOut R Nh t).g.re
    (histOut R Nh t).nu.re hDm hKm hmN hgre (Cf * gg) hz hy hs1 hs2 hA
    (by positivity) (by positivity) hWl hDd hKk
  have hνr : |(histOut R Nh t).nu.re| ≤ Cf * gg := (Complex.abs_re_le_norm _).trans hnu
  have hgr : (histOut R Nh t).g.re ≤ Cf * gg := (Complex.re_le_norm _).trans hgn
  have hv1 : cM * R.ℓ ^ 2 * (2 * |(histOut R Nh t).nu.re| + 2 * (Cf * gg)) +
      8 * R.ℓ ^ 4 * (histOut R Nh t).g.re ≤ 1 := by
    have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
    have h1 : cM * R.ℓ ^ 2 * (2 * |(histOut R Nh t).nu.re| + 2 * (Cf * gg)) ≤
        cM * R.ℓ ^ 2 * (4 * (Cf * gg)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 8 * R.ℓ ^ 4 * (histOut R Nh t).g.re ≤ 8 * R.ℓ ^ 4 * (Cf * gg) :=
      mul_le_mul_of_nonneg_left hgr (by positivity)
    linarith
  -- the block bound `‖inI(B)‖_{wM} ≤ ι_T`
  have hs' : 0 < histS R (Nh + 1) t := hs (Nh + 1)
  set ι := iotaT L Cw cW vT with hιd
  have hι : 1 ≤ ι := one_le_iotaT L Cw cW hvT
  have ho := obsHist_isObs R (ptsX x) (obsInit .two (zV b) (ptsX x)) (obsInit_isObs .two _ _)
    (Nh + 1) t
  have hI : ∀ q ∈ blocks (Nh + 1) (dxTop Nh x), oTj 2 L (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
      (inI R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D
        (obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t) q :
          SA .two (Lam 2 L N)) ≤ ENNReal.ofReal ι := by
    intro q hq
    have hqI : q ∈ blockIdx (L := L) (N := N) (Nh + 1) := mem_blockIdx_of_mem_blocks hq
    refine (oTj_inI_le R (Nh + 1) _ _ _ _ _ ho (wM Ma Mb) (wM_sub Ma Mb) hs' q
      (v := 3 / 2 + vT) (f := Real.exp E) (by linarith) (Real.exp_pos _).le ?_ ?_).trans
        (le_of_eq rfl)
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.V q)).trans ?_
      have hb1 : Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((stVf R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re q +
            stDelta R (Nh + 1) st q : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal (3 / 2) := by
        rw [AddMemClass.coe_add]
        refine (tNorm_add_le _ _).trans ?_
        have h1 := (Tj_le_Fnorm (stVf R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re)
          hqI).trans (hVv.trans (ENNReal.ofReal_le_ofReal hv1))
        have h2 := (Tj_le_Fnorm (stDelta R (Nh + 1) st) hqI).trans
          (hΔ.trans (ENNReal.ofReal_le_ofReal hs2))
        refine (add_le_add h1 h2).trans ?_
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      refine (add_le_add hb1 (hVt q hqI)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by norm_num) hvT]
    · refine (oTj_emb_add_le _ _ _ _ _ (ho.W q)).trans ?_
      have hb2 : Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((st.Wl + (histOut R Nh t).D) q : Alg 2 L N) ≤ ENNReal.ofReal 1 := by
        refine (Tj_le_Fnorm _ hqI).trans (hWw.trans (ENNReal.ofReal_le_ofReal ?_))
        linarith
      refine (add_le_add hb2 (hWo' q)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add zero_le_one (by linarith [Real.one_le_exp hE0])]
      congr 1; ring
  -- the activity: `A^{|𝓑(X)|}‖inK(X)‖_{wM} ≤ 1`
  set kb := Cf * gg ^ 3 with hkbd
  set k2 := 2 * kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) * (c * gg) * (2 * cW) ^ 2 with hk2d
  have hcx := H.hcx
  have hB2 : 0 ≤ kB2 (kθ0 L R.A C₀u ηu) C₁u (cx κ cT) (8 * B) := by
    have hA0 : (0 : ℝ) ≤ R.A / 2 := by linarith
    have : 0 ≤ kθ0 L R.A C₀u ηu := by
      unfold kθ0; have := Real.rpow_nonneg hA0 (-ηu); positivity
    unfold kB2; positivity
  have hkb0 : 0 ≤ kb := by positivity
  have hk20 : 0 ≤ k2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB2) (hr0 Nh le_rfl)) (sq_nonneg _)
  have hKb : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) ≤
        ENNReal.ofReal kb := by
    intro X hX
    have h1 : ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) ≤
        Knorm (Nh + 1) (fscale st.Z * R.ℓ) R.A (histOut R Nh t).K :=
      le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) (Nh + 1)) =>
        ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
          Tj 2 (L : ℝ) (Nh + 1) (fscale st.Z * R.ℓ) ((histOut R Nh t).K X : Alg 2 L N)) X
        (by simp [connSets]; exact hX)
    exact h1.trans hKk
  have hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM Ma Mb).ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
        ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X :
          SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2 := by
    intro X hX
    rw [hKeq]
    refine (hab X hX).trans (le_of_eq ?_)
    rw [hmj]
  have hK : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ nb (Nh + 1) X) *
      oTj 2 L (wM Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
        (inK (histOut R Nh t).K (obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t) X :
          SA .two (Lam 2 L N)) ≤ 1 := by
    intro X hX
    rw [oTj_inK_eq _ _ ho]
    have hA0 : 0 ≤ R.A := by linarith
    calc ENNReal.ofReal (R.A ^ nb (Nh + 1) X) *
          (Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) +
          oTo (wM1 Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
            ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X) +
          (wM Ma Mb).ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
            ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X :
              SA .two (Lam 2 L N)).ab)
        ≤ ENNReal.ofReal (R.A ^ 4) * (ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
          (Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t) ((histOut R Nh t).K X : Alg 2 L N) +
          oTo (wM1 Ma Mb) (Nh + 1) (histS R (Nh + 1) t)
            ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X) +
          (wM Ma Mb).ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
            ((obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t).K X :
              SA .two (Lam 2 L N)).ab)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (regA_le R.A hA1 _)) _
      _ ≤ ENNReal.ofReal (R.A ^ 4) * (ENNReal.ofReal kb + ENNReal.ofReal kxT +
          ENNReal.ofReal k2) := by
          refine mul_le_mul_right ?_ _
          rw [mul_add, mul_add]
          exact add_le_add (add_le_add (hKb X hX) (hKt X hX)) (hK2 X hX)
      _ = ENNReal.ofReal (R.A ^ 4 * (kb + kxT + k2)) := by
          rw [← ENNReal.ofReal_add hkb0 hkxT, ← ENNReal.ofReal_add (by positivity) hk20,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ 1 := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hsmT
  -- the reduced activity
  intro X hX
  have hmain := kRed_poly_le (z0 := (ptsX x).a) (D := dxTop Nh x) (wM_sub Ma Mb) hs' hA1 hι
    (inI R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D
      (obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t))
    (inK (histOut R Nh t).K (obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Nh + 1) t))
    hI hK X
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hnb : nb (Nh + 1) (dxTop Nh x) ≤ L ^ 2 := by
    have h1 : (blocks (Nh + 1) (dxTop Nh x)).card ≤ (blockIdx (L := L) (N := N) (Nh + 1)).card :=
      card_le_card (blocks_subset_blockIdx _)
    exact h1.trans (LastN.card_blockIdx_last (d := 2) (L := L) (N := N) (by omega))
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by linarith) hA1) hnb

end Traj

end

end Spin2
