import Spin2.Pair.PairDefAB2
import Spin2.Gam.GamFormB
import Spin2.Case2.Case2
import PtCorr2.Pair.PairInitU
import PtCorr2.Obs.ConstSplitHist
import PtCorr2.Obs.ObsHistLast

/-!
# The one-point sizes of the unreduced pair history in the weights `wM`, `wM1`

Wiring of `PtCorr2.redHist_K_ab_le_U` (items 1 and 3 of `Log.md`, "the seed and the unreduced
chain"):

* **`zV0 b`**: the pair vertex `zV b` with both constants `γ_a = γ_b = 0`; **`obsHist_zV0`**: for
  `j ≥ 1` the observable states `V`, `𝒲`, `K` from `zV b` and from `zV0 b` coincide
  (`obsHist_gaZero` and its `b` copy `obsHist_gbZero`).
* **`mirror_b_eq`**: the `σ_b` components along the history with points `(0, x)` are the `σ_a`
  components along the history with points `(x, 0)` (`Obs2.prj_obsHist`, `prjSt_obsInit_swap`).
* **`bt2_ratio`**: `‖β_k‖ ≤ (64/49)‖β_{k+1}‖` from `Case2Rel` and `Case2Loop` (`bt2_flow`).
* **`pairInit_traj`**: along a trajectory, the one-point bounds of `obs_hist_rel2_baseX` (weight
  `wA`) at the two points, the ratio of `β`, the bulk activity `‖x.2‖ ≤ c_xǧ³` and the constants
  of `kab_hist` give the initial `ab` activity of `oRed … dxStd`; the only remaining input is the
  block bound `‖inI(B)‖_{wM} ≤ ι` at `j_x` (named, item 2).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L N : ℕ} [NeZero L]

/-! ### `γ_b = 0` -/

/-- The Case-(2) vertex with `γ_b` set to `0`. -/
def gbZero (V : OCoup .two) : OCoup .two :=
  ⟨OCoup2.mua V, OCoup2.mub V, OCoup2.ga V, 0, OCoup2.q V, OCoup2.eta V, OCoup2.r V, OCoup2.chi V⟩

/-- The pair vertex with `γ_a = γ_b = 0`. -/
def zV0 (b : ℝ) : OCoup .two := ⟨-(b : ℂ), -(b : ℂ), 0, 0, 0, 0, 0, 0⟩

theorem gbZero_gaZero_zV (b : ℝ) : gbZero (gaZero (zV b)) = zV0 b := rfl

/-- The initial difference `−γ_bσ_b1_{b∈B}`. -/
def kapb0 (V : OCoup .two) (P : ObsPts 2 L N) : OFam .two 2 L N :=
  fun b => (obsInit .two V P).V b - (obsInit .two (gbZero V) P).V b

theorem kapb0_cst (V : OCoup .two) (P : ObsPts 2 L N) (b : Fin 2 → ℕ) :
    IsCstObs (kapb0 V P b) := by
  refine ⟨?_, ?_⟩
  · refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;>
      simp [kapb0, obsInit, Obs2.evalFam, Obs2.evalO, Obs2.evalS, Obs2.OCoup2.evalS, gbZero,
        psibar, psi, eps_ψ, smul_sub]
    all_goals rw [Algebra.smul_def]
  · show bulk (Obs2.evalO .two V P.a P.b _ - Obs2.evalO .two (gbZero V) P.a P.b _) = 0
    rw [map_sub, Obs2.bulk_evalO, Obs2.bulk_evalO, sub_zero]

theorem obsInit_V_kapb0 (V : OCoup .two) (P : ObsPts 2 L N) :
    (obsInit .two V P).V = (obsInit .two (gbZero V) P).V + kapb0 V P := by
  funext b; simp [kapb0]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

theorem obsStep_kapb0 (V : OCoup .two) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) :
    (obsStep R P 0 st g μ D 0 (obsInit .two V P)).V =
        (obsStep R P 0 st g μ D 0 (obsInit .two (gbZero V) P)).V ∧
      (obsStep R P 0 st g μ D 0 (obsInit .two V P)).W =
        (obsStep R P 0 st g μ D 0 (obsInit .two (gbZero V) P)).W ∧
      (obsStep R P 0 st g μ D 0 (obsInit .two V P)).K =
        (obsStep R P 0 st g μ D 0 (obsInit .two (gbZero V) P)).K := by
  have hκ := kapb0_cst V P
  have hV : fullV R 0 st g μ (obsInit .two V P) =
      fullV R 0 st g μ (obsInit .two (gbZero V) P) + kapb0 V P := by
    rw [fullV, fullV, obsInit_V_kapb0, add_assoc]
  have hW : fullW st D (obsInit .two V P) = fullW st D (obsInit .two (gbZero V) P) := rfl
  have hK := fullK_obsInit_zero R P V 0 st
  have hK' := fullK_obsInit_zero R P (gbZero V) 0 st
  simp only [obsStep, hV, hW, hK, hK', Vnext2O_addc _ _ _ _ _ _ hκ, Wnext2O_addc _ _ _ _ _ hκ,
    KplusO_addc _ _ _ _ _ hκ]
  refine ⟨?_, ?_, ?_⟩ <;> trivial

variable (t : Hist.Seq (Xs R))

theorem obsHist_gbZero (V : OCoup .two) (ht : (t 0).2.2 = 0) :
    ∀ j, 1 ≤ j →
      (obsHist R P (obsInit .two V P) j t).V = (obsHist R P (obsInit .two (gbZero V) P) j t).V ∧
      (obsHist R P (obsInit .two V P) j t).W = (obsHist R P (obsInit .two (gbZero V) P) j t).W ∧
      (obsHist R P (obsInit .two V P) j t).K = (obsHist R P (obsInit .two (gbZero V) P) j t).K
  | 0, h => absurd h (by omega)
  | 1, _ => by
    rw [obsHist_succ, obsHist_succ]
    have hK : rawK R (rawHist R 0 t).u (t 0).2.2 = 0 := by rw [ht]; exact rawK_zeroX R _
    rw [hK]
    exact obsStep_kapb0 R P V _ _ _ _
  | j + 2, _ => by
    obtain ⟨h1, h2, h3⟩ := obsHist_gbZero V ht (j + 1) (by omega)
    rw [obsHist_succ R P (obsInit .two V P) (j + 1) t,
      obsHist_succ R P (obsInit .two (gbZero V) P) (j + 1) t]
    exact obsStep_congrVWK R P _ _ _ _ _ _ h1 h2 h3

/-- **`zV b` and `zV0 b` give the same observable states from scale `1` on.** -/
theorem obsHist_zV0 (b : ℝ) (ht : (t 0).2.2 = 0) (j : ℕ) (hj : 1 ≤ j) :
    (obsHist R P (obsInit .two (zV b) P) j t).V = (obsHist R P (obsInit .two (zV0 b) P) j t).V ∧
      (obsHist R P (obsInit .two (zV b) P) j t).W =
        (obsHist R P (obsInit .two (zV0 b) P) j t).W ∧
      (obsHist R P (obsInit .two (zV b) P) j t).K =
        (obsHist R P (obsInit .two (zV0 b) P) j t).K := by
  obtain ⟨a1, a2, a3⟩ := obsHist_gaZero R P t (zV b) ht j hj
  obtain ⟨b1, b2, b3⟩ := obsHist_gbZero R P t (gaZero (zV b)) ht j hj
  rw [gbZero_gaZero_zV] at b1 b2 b3
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

/-! ### The mirror -/

/-- The `σ_b` part of `prjSt false o` and the `σ_a` part of `prjSt true o'`. -/
theorem prjSt_eq_cmp {o o' : ObsSt .two L N} (h : prjSt false o = prjSt true o') :
    (∀ b, (o.V b : SA .two (Lam 2 L N)).b = (o'.V b : SA .two (Lam 2 L N)).a) ∧
    (∀ b, (o.W b : SA .two (Lam 2 L N)).b = (o'.W b : SA .two (Lam 2 L N)).a) ∧
    (∀ X, (o.K X : SA .two (Lam 2 L N)).b = (o'.K X : SA .two (Lam 2 L N)).a) := by
  refine ⟨fun b => ?_, fun b => ?_, fun X => ?_⟩
  · have := congrArg (fun s : ObsSt .two L N => ((s.V b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_true, Obs2.cmp_false] using this
  · have := congrArg (fun s : ObsSt .two L N => ((s.W b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_true, Obs2.cmp_false] using this
  · have := congrArg (fun s : ObsSt .two L N => ((s.K X : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_true, Obs2.cmp_false] using this

/-- **The `σ_b` components at points `(0, x)` are the `σ_a` components at points `(x, 0)`.** -/
theorem mirror_b_eq (b : ℝ) (x : Lam 2 L N) (j : ℕ) :
    prjSt false (obsHist R (ptsX x) (obsInit .two (zV0 b) (ptsX x)) j t) =
      prjSt true (obsHist R (ptsS x) (obsInit .two (zV0 b) (ptsS x)) j t) := by
  rw [prj_obsHist R false (P := ptsX x) (P' := ptsS x) rfl,
    prj_obsHist R true (P := ptsS x) (P' := ptsS x) rfl,
    prjSt_obsInit_swap (zV0 b) rfl rfl (P := ptsX x) (P' := ptsS x) rfl]

end Hist

/-! ### Norm conversions -/

theorem oTo_wM1_le {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ) (ℓ : ℝ)
    (F : OE c (Lam 2 L N)) {u v : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a ≤ ENNReal.ofReal u)
    (hv : Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).b ≤ ENNReal.ofReal v) :
    oTo (wM1 Ma Mb) j ℓ F ≤ ENNReal.ofReal (u / Ma + v / Mb) := by
  rw [oTo_eq_comp (show (wM1 Ma Mb).ab = 0 from rfl)]
  show ENNReal.ofReal Ma⁻¹ * _ + ENNReal.ofReal Mb⁻¹ * _ ≤ _
  calc ENNReal.ofReal Ma⁻¹ * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a +
        ENNReal.ofReal Mb⁻¹ * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).b
      ≤ ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal u + ENNReal.ofReal Mb⁻¹ * ENNReal.ofReal v :=
        add_le_add (mul_le_mul_right hu _) (mul_le_mul_right hv _)
    _ = ENNReal.ofReal (u / Ma + v / Mb) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hMb.le),
          ← ENNReal.ofReal_add (by positivity) (by positivity), div_eq_inv_mul, div_eq_inv_mul]

theorem oTo_wM_le_of_ab {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ)
    (ℓ : ℝ) (F : OE c (Lam 2 L N)) (hab : (F : SA c (Lam 2 L N)).ab = 0) {u v : ℝ}
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a ≤ ENNReal.ofReal u)
    (hv : Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).b ≤ ENNReal.ofReal v) :
    oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal (u / Ma + v / Mb) := by
  rw [oTo_split_ab, hab, show Tj 2 (L : ℝ) j ℓ (0 : Alg 2 L N) = 0 from tNorm_zero', mul_zero,
    add_zero, wOne_wM]
  exact oTo_wM1_le hMa hMb j ℓ F hu0 hv0 hu hv

/-- The regulated version of `oTo_wM1_le`. -/
theorem reg_oTo_wM1_le {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ)
    (ℓ : ℝ) (F : OE c (Lam 2 L N)) (a : ℝ≥0∞) {u v : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : a * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a ≤ ENNReal.ofReal u)
    (hv : a * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).b ≤ ENNReal.ofReal v) :
    a * oTo (wM1 Ma Mb) j ℓ F ≤ ENNReal.ofReal (u / Ma + v / Mb) := by
  rw [oTo_eq_comp (show (wM1 Ma Mb).ab = 0 from rfl)]
  show a * (ENNReal.ofReal Ma⁻¹ * _ + ENNReal.ofReal Mb⁻¹ * _) ≤ _
  rw [mul_add, mul_left_comm, mul_left_comm a]
  calc ENNReal.ofReal Ma⁻¹ * (a * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a) +
        ENNReal.ofReal Mb⁻¹ * (a * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).b)
      ≤ ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal u + ENNReal.ofReal Mb⁻¹ * ENNReal.ofReal v :=
        add_le_add (mul_le_mul_right hu _) (mul_le_mul_right hv _)
    _ = ENNReal.ofReal (u / Ma + v / Mb) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hMb.le),
          ← ENNReal.ofReal_add (by positivity) (by positivity), div_eq_inv_mul, div_eq_inv_mul]

/-! ### The ratio of `β` -/

/-- **`‖β_k‖ ≤ (64/49)‖β_{k+1}‖`** from `Case2Rel` and `Case2Loop`. -/
theorem bt2_ratio (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (V : OCoup .two) {Nh : ℕ} (hNh : Nh < N) {m b μ₀ cδ B B' cq : ℝ}
    (hRel : Case2Rel R P V Nh m b μ₀ cδ) (hLoop : Case2Loop R P V Nh m b μ₀ B B' cq)
    {k : ℕ} (hk : k < Nh) :
    ‖bt2 R P V m b μ₀ k‖ ≤ 64 / 49 * ‖bt2 R P V m b μ₀ (k + 1)‖ := by
  obtain ⟨q, -, -, hl⟩ := hLoop
  have hn := (hl k hk).1
  obtain ⟨he, hδ⟩ := hRel k hk
  rw [bt2_flow R P V hNh m b μ₀ hk]
  set β := bt2 R P V m b μ₀ k
  set n := nn2 R P V m b μ₀ k
  set e := err2 R P V m b μ₀ k
  have h1 : 7 / 8 ≤ ‖1 - n‖ := by
    have := norm_sub_norm_le (1 : ℂ) n; rw [norm_one] at this; linarith
  have h2 : ‖e‖ ≤ 1 / 8 * ‖β * (1 - n)‖ :=
    he.trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
  have h3 := norm_sub_norm_le (β * (1 - n)) e
  rw [norm_mul] at h2 h3
  have h4 : 7 / 8 * ‖β‖ ≤ ‖β‖ * ‖1 - n‖ := by
    have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (bt2 R P V m b μ₀ k)); linarith
  nlinarith [norm_nonneg (bt2 R P V m b μ₀ k), norm_nonneg ((1 : ℂ) - n)]

/-! ### The initial `ab` activity along a trajectory -/

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- The block bound of `V^{obs}_j` (`γ_a = 0`) from the `ℓ¹` size. -/
theorem vobs_le_of_shA2 (P : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0)
    (t : Hist.Seq (Xs R)) (j : ℕ) (hs : 0 < histS R j t) {B : ℝ}
    (hA : shA2 (histVO2 R P (obsInit .two V P) t) j ≤ 2 * B) (b : Fin 2 → ℕ)
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo wA j (histS R j t) ((obsHist R P (obsInit .two V P) j t).V b) ≤
      ENNReal.ofReal (2 * histS R j t ^ 2 * B) := by
  refine (vobs2_block_le R P V hga t j hs b hb).trans (ENNReal.ofReal_le_ofReal ?_)
  have := mul_le_mul_of_nonneg_left hA (sq_nonneg (histS R j t))
  linarith

/-- `s_j² ≤ (6/5)s_{j+1}²`. -/
theorem histS_sq_ratio (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Hist.Seq (Xs R)) (j : ℕ) :
    histS R j t ^ 2 ≤ 6 / 5 * histS R (j + 1) t ^ 2 := by
  have e : histS R (j + 1) t = histS R j t * fscale (1 + zetaH R j t) := by
    unfold histS
    rw [rawHist_succ_Z, fscale_mul]; ring
  have hz : ‖zetaH R j t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
  have h1 := fscale_one_add_ge hz
  have h2 := histS_pos' R hρ0 hρ t j
  have h3 : histS R j t ≤ 15 / 14 * histS R (j + 1) t := by rw [e]; nlinarith
  have h4 : 0 ≤ histS R (j + 1) t := by rw [e]; nlinarith
  nlinarith

/-- The one-point outputs of `obs_hist_rel2_baseX` at scale `j`. -/
def OneSz (P : ObsPts 2 L N) (V : OCoup .two) (t : Hist.Seq (Xs R)) (j : ℕ) (r cW B : ℝ) :
    Prop :=
  0 < ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖ ∧
    shA2 (histVO2 R P (obsInit .two V P) t) j ≤
      2 * ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖ ∧
    WbHc R P (obsInit .two V P) t j (cW * r * (2 * histS R j t ^ 2 *
      ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖)) ∧
    KbHc R P (obsInit .two V P) t j (16 * cW * B * r ^ 2 * (histS R j t ^ 2 *
      ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖))

/-- `M = 2s_j²|β_j|` for the history with points `P`, vertex `V`. -/
def pM (P : ObsPts 2 L N) (V : OCoup .two) (t : Hist.Seq (Xs R)) (j : ℕ) : ℝ :=
  2 * histS R j t ^ 2 * ‖betaTot2 (L := L) (N := N) j (histVO2 R P (obsInit .two V P) t j)‖

set_option maxHeartbeats 4000000 in
/-- **The initial `ab` activity at coalescence along a trajectory** (pair vertex `zV b`), from the
one-point sizes of `obs_hist_rel2_baseX` at the two points (`zV0 b`, points `(0, x)` and the
mirror `(x, 0)`), the ratio of `β`, and the constants of `kab_hist`; the only remaining input is
the block bound `hI` of the unreduced input at `j_x`. `M_a = 2s_{j_x}²|β_{a,j_x}|`,
`M_b = 2s_{j_x}²|β^{mir}_{a,j_x}|`. -/
theorem pairInit_traj {C₀u ηu ε₀u C₁u : ℝ} (hKB : KObsBoundsU L R.A C₀u ηu ε₀u C₁u)
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
    {ι : ℝ} (hι : 1 ≤ ι)
    (hI : ∀ c ∈ blocks (Obs.coal L (0 : Lam 2 L N) x) (dxStd (L := L) (N := N) x),
      oTj 2 L (wM (pM R (ptsX x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x))
          (pM R (ptsS x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x)))
        (Obs.coal L (0 : Lam 2 L N) x) (histS R (Obs.coal L (0 : Lam 2 L N) x) t)
        (inI R (Obs.coal L (0 : Lam 2 L N) x) (rawHist R (Obs.coal L (0 : Lam 2 L N) x) t)
          (t (Obs.coal L (0 : Lam 2 L N) x)).1 (t (Obs.coal L (0 : Lam 2 L N) x)).2.1
          (rawD R (rawHist R (Obs.coal L (0 : Lam 2 L N) x) t).u
            (t (Obs.coal L (0 : Lam 2 L N) x)).2.2)
          (obsHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Obs.coal L (0 : Lam 2 L N) x) t)
          c : SA .two (Lam 2 L N)) ≤ ENNReal.ofReal ι)
    (Y : Finset (Lam 2 L N)) :
    ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x) (histS R (Obs.coal L (0 : Lam 2 L N) x) t)
          ((redHist R (ptsX x) (obsInit .two (zV b) (ptsX x)) (Obs.coal L (0 : Lam 2 L N) x)
            (dxStd (L := L) (N := N) x) t).K Y : SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (pM R (ptsX x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x) *
        pM R (ptsS x) (zV0 b) t (Obs.coal L (0 : Lam 2 L N) x) *
        (2 * ι * R.A) ^ ((L + 18) ^ 2)) := by
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
  have hmain := redHist_K_ab_le_sizes R (ptsX x) (obsInit .two (zV b) (ptsX x)) t
    (obsInit_isObs .two _ _) hMa hMb (hs j₀) hA1 hι (by positivity) (by positivity)
    (by positivity) hsm hI hKb hKx hK2 Y
  refine hmain.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by nlinarith) (nb_dxStd_le (by omega) x (by omega)))
    (mul_pos hMa hMb).le))

end Traj

/-! ### The conclusion along admissible trajectories -/

/-- **The initial `ab` activity of `oRed … dxStd` under master constants**, along every
admissible trajectory and every `x` with `1 ≤ j_x ≤ N_h`: `M_a = 2s_{j_x}²|β_{a,j_x}| > 0`,
`M_b = 2s_{j_x}²|β^{mir}_{a,j_x}| > 0` (vertex `zV0 b`, points `(0, x)` and `(x, 0)`), and for every
`ι ≥ 1` with the block bound `‖inI(B)‖_{wM} ≤ ι` of the unreduced input at `j_x` (item 2, named),
`A^{(|𝓑(Y)|-4)_+}‖K'_{j_x}(Y)_{ab}‖ ≤ M_aM_b(2ιA)^{(L+18)²}`. -/
def PairInitConclU (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ x : Lam 2 L N, 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    0 < pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) ∧
    0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) ∧
    ∀ ι : ℝ, 1 ≤ ι →
      (∀ c ∈ blocks (Obs.coal L (0 : Lam 2 L N) x) (dxStd (L := L) (N := N) x),
        oTj 2 L (wM (pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x))
            (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x)))
          (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (inI (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (rawHist (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) x)).1
            ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) x)).2.1
            (rawD (R.withMsq m) (rawHist (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u
              ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Obs.coal L (0 : Lam 2 L N) x)).2.2)
            (obsHist (R.withMsq m) (ptsX x) (obsInit .two (zV b) (ptsX x))
              (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) c :
            SA .two (Lam 2 L N)) ≤ ENNReal.ofReal ι) →
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
