import PtCorr2.Obs.KObsStep
import Obs2.Est.KObsInd
import Step2.Flow.FlowHist

/-!
# The `K^{obs}` bound along the flow

`KObsBounds`: the conclusion of `kobs_raw_step` (one step of `obsStep` at the raw level), as a
named property of the constants (as `Step2.StepBounds` for the bulk); `kobs_bounds` provides it.

Along a regular history in `D_ε` (`Flow2.Hist.InDh`), with the a priori bounds of the bulk flow
(`Step2.apriori`: clamps `O(g_j)`, `‖W^{lin}_j‖ ≤ c_W g_j²`), radius `r_j = c_R g_j` and
`c_b = 8c_x`:
* **`kobs_hist_step`**: one step, `k_{j+1} ≤ (θ₀ + C₁(2+2c_b+c_k) r_j) 8k_j + B r_j² m_j`
  (`B = kB θ₀ C₁ c_b`), given `‖V^{obs}_j‖ ≤ m_j`, `‖𝒲^{obs}_j‖ ≤ r_j m_j`,
  `8k_j ≤ c_k r_j² m_j`;
* **`kobs_hist`**: along the whole history, with `c_k = 64B` and `θ̄ = θ₀ + C₁(2+2c_b+c_k)c_R ε`,
  `A^{(|𝓑_j(X)|-4)_+}‖K^{obs}_j(X)‖_{T_j(s_j)} ≤ k_j := kseq (8θ̄) B r m j
  = ∑_{i<j} (8θ̄)^{j-1-i} B r_i² m_i` and `8k_j ≤ c_k r_j² m_j`, under `θ₀ ≤ 1/72`,
  `C₁(2+2c_b+c_k)c_R ε ≤ 1/72`, `c_R ε ≤ min(1, ε₀)`, `(c_b+c_k)c_R ε ≤ ε₀`, the observable
  sizes `m_j` (inputs, with `m_j ≤ 2m_{j+1}`) and `K^{obs}_0 = 0`.

Here `s_j = |Z_j|^{-1/2} ℓ` is the causal field scale and `θ₀ = C₀(L^{-1} + (A/2)^{-η})`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The conclusion of `kobs_raw_step` for given constants. -/
def KObsBounds (L : ℕ) [NeZero L] (A C₀ η ε₀ C₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.ab = 0 → w.a ≠ ⊤ → w.b ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o →
    ∀ wl dd kb r m k cb ck : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ kb → 0 < r → 0 < m → 0 ≤ k →
      0 ≤ cb → 0 ≤ ck →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal kb →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      r ≤ 1 → r ≤ ε₀ → 8 * kb ≤ cb * r ^ 3 → 8 * k ≤ ck * r ^ 2 * m →
      8 * kb + r / m * (8 * k) ≤ ε₀ →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal (r * m)) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        oTo w j (fscale st.Z * R.ℓ) (o.K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
        ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ 2)) *
          oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).K U) ≤
        ENNReal.ofReal ((C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η)) +
            C₁ * (2 + 2 * cb + ck) * r) * (8 * k) +
          (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η)) * cb +
            C₁ * (8 + 2 * cb + cb ^ 2)) * r ^ 2 * m)

/-- **The constants of the `K^{obs}` step.** -/
theorem kobs_bounds : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ :=
  kobs_raw_step

/-- `θ₀ = C₀(L^{-1} + (A/2)^{-η})`. -/
def kθ0 (L : ℕ) (A C₀ η : ℝ) : ℝ := C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η))

/-- The source constant `B = θ₀ c_b + C₁(8 + 2c_b + c_b²)`. -/
def kB (θ₀ C₁ cb : ℝ) : ℝ := θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)

/-- The causal field scale `s_j = |Z_j|^{-1/2} ℓ` along the history. -/
def histS (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (j : ℕ)
    (t : Flow2.Hist.Seq (Xs R)) : ℝ :=
  fscale (rawHist R j t).Z * R.ℓ

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

theorem hist_valid (hV : ∀ j < Nh, ValidAt R j) (t : Flow2.Hist.Seq (Xs R)) {n : ℕ}
    (hn : n ≤ Nh) : ∀ j < n, ValidCore R j ∧ RawInv R j (rawHist R j t) := fun j hj =>
  ⟨(hV j (by omega)).toValidCore,
    rawInv_hist R (hV j (by omega)).2.2.2.1 j (fun i hi => hV i (by omega)) t⟩

set_option maxHeartbeats 4000000 in
/-- **One step of the `K^{obs}` recursion along the history.** -/
theorem kobs_hist_step {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ck m k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < m) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t j).1) ^ 2 * m)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        oTo w (j + 1) (histS R (j + 1) t) ((obsHist R P o₀ (j + 1) t).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t j).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t j).1) ^ 2 * m) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  -- the radius
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  have hr3 : r ^ 3 ≤ r := by
    have : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
    nlinarith
  have hεk' : 8 * ‖x.2‖ + r / m * (8 * k) ≤ ε₀ := by
    have h1 : r / m * (8 * k) ≤ ck * r ^ 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
      have := mul_le_mul_of_nonneg_left hk8 hr0.le
      calc r * (8 * k) ≤ r * (ck * r ^ 2 * m) := this
        _ = ck * r ^ 3 * m := by ring
    have h2 : (8 * cx κ cT + ck) * r ^ 3 ≤ (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) :=
      mul_le_mul_of_nonneg_left (hr3.trans hrε) (by positivity)
    nlinarith
  -- the observable invariants
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hsym := obsSymInv_hist R P o₀ hs0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  exact hKB N R j hVj.toValidCore st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj) hg.le
    (cZ R * g) hz hy hη hηs c P w hw0 hwa hwb (obsHist R P o₀ j t) hobs hloc hsym
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 (hrε.trans hεε) hbr hk8 hεk' hVo hWo hKo

set_option maxHeartbeats 2000000 in
/-- **The `K^{obs}` bound along the history.** -/
theorem kobs_hist {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁) (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (hK0 : ∀ X, oTo w 0 (histS R 0 t) (o₀.K X) = 0)
    (n : ℕ) (hn : n ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hθ0 : 0 ≤ kθ0 L R.A C₀ η) (hθ : kθ0 L R.A C₀ η ≤ 1 / 72)
    (hsm : C₁ * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT)) *
      (cR R Λ cm C₂ * ε) ≤ 1 / 72)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + 64 * kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT)) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (m : ℕ → ℝ) (hm0 : ∀ j, 0 < m j) (hm' : ∀ j < n, m j ≤ 2 * m (j + 1))
    (hVo : ∀ j < n, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal (m j))
    (hWo : ∀ j < n, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m j)) :
    let B := kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT)
    let θb := kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
    let r := fun j => cR R Λ cm C₂ * (t j).1
    ∀ j ≤ n, 8 * kseq (8 * θb) B r m j ≤ 64 * B * r j ^ 2 * m j ∧
      ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) ≤
          ENNReal.ofReal (kseq (8 * θb) B r m j) := by
  intro B θb r
  have hcx := H.hcx
  have hcb : 0 ≤ 8 * cx κ cT := by positivity
  have hB : 0 ≤ B := by
    have h1 := mul_nonneg hθ0 hcb
    have h2 := mul_nonneg hC₁ (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L R.A C₀ η * (8 * cx κ cT) + C₁ * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  have hcv : 0 ≤ cV R Λ cm := by unfold cV cZ; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcR : 0 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hε0 := H.hε
  have hC1 : 0 ≤ C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) := by positivity
  have hθb0 : 0 ≤ θb := by
    have : 0 ≤ C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε) := by positivity
    show 0 ≤ kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
    linarith
  have hθb : θb ≤ 1 / 36 := by
    show kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε) ≤ 1 / 36
    linarith
  have hc : 72 * (8 * θb * (64 * B) + 8 * B) ≤ 25 * (64 * B) := by
    have := mul_le_mul_of_nonneg_right hθb hB
    linarith
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hr0 : ∀ j ≤ n, 0 ≤ r j := fun j hj => mul_nonneg hcR (ht.1 j hj).1.le
  have hr' : ∀ j < n, 5 / 6 * r j ≤ r (j + 1) := by
    intro j hj
    have := g_succ_ge (hDh (j + 1) hj) hβ hδ1 H.hcg H.hε1 H.h6
    have := mul_le_mul_of_nonneg_left this hcR
    show 5 / 6 * (cR R Λ cm C₂ * (t j).1) ≤ cR R Λ cm C₂ * (t (j + 1)).1
    linarith
  have hK := kseq_le (B := B) n (by positivity) (by positivity) hr0 (fun j _ => (hm0 j).le) hr'
    hm' hc
  have main : ∀ j ≤ n, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) ≤
        ENNReal.ofReal (kseq (8 * θb) B r m j) := by
    intro j
    induction j with
    | zero =>
      intro _ X _
      show _ * oTo w 0 (histS R 0 t) (o₀.K X) ≤ _
      rw [hK0 X, mul_zero]
      exact zero_le
    | succ j ih =>
      intro hj X hX
      have ih := ih (by omega)
      have hk0 := kseq_nonneg (r := r) (by positivity : 0 ≤ 8 * θb) hB (fun i => (hm0 i).le) j
      have hs : ENNReal.ofReal (R.A ^ (nb (j + 1) X - 2 ^ 2)) *
          oTo w (j + 1) (histS R (j + 1) t) ((obsHist R P o₀ (j + 1) t).K X) ≤
          ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) *
            (cR R Λ cm C₂ * (t j).1)) * (8 * kseq (8 * θb) B r m j) +
            B * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j) := kobs_hist_step R hKB hSB hV hm hβ hδ1 H P w hw0 hwa hwb o₀ h0 hl0 hs0 t j
        (by omega) (hDh j (by omega)) (64 * B) (m j) (kseq (8 * θb) B r m j) (by positivity)
        (hm0 j) hk0 hε1 hεε hεk (hK j (by omega)) (hVo j (by omega)) (hWo j (by omega)) ih X hX
      refine hs.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [kseq_succ]
      have hgj : (t j).1 ≤ ε := (ht.1 j (by omega)).2.1
      have h1 : kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) *
          (cR R Λ cm C₂ * (t j).1) ≤ θb := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgj hcR) hC1
        show _ ≤ kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + 64 * B) * (cR R Λ cm C₂ * ε)
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 8 * kseq (8 * θb) B r m j)
      show _ ≤ 8 * θb * kseq (8 * θb) B r m j + B * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j
      linarith
  exact fun j hj => ⟨hK j hj, main j hj⟩

end Hist

end

end PtCorr2
