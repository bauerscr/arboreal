import PtCorr2.Obs.KObsHist
import PtCorr2.Obs.ObsHist
import PtCorr2.Pair.KObsStepAB
import PtCorr2.Pair.WObsStepAB
import Obs2.Est.WObsAB2
import PtCorr2.Obs.ObsSymFrom

-- Merged from `PtCorr2/WObsStepAB2.lean` (phase 3).
section

/-!
# The `𝒲^{obs}` step on the `σ_aσ_b` sector, unconditional

**`wobs_raw_stepAB2`**: `PtCorr2.wobs_raw_stepAB` without the hypothesis `Obs2.EthSubLocAB 2`,
which is proved in `Obs2.Est.WObsAB2` (`Obs2.ethSubLocAB_two`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

/-- **The `𝒲^{obs}` step at the raw level on the `ab` sector** (unconditional). -/
theorem wobs_raw_stepAB2 : ∃ (Kw : ℝ) (L₀ : ℕ), 0 ≤ Kw ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ ε₁ → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).W c') ≤
          ENNReal.ofReal ((Kw / L + C₁ * r) * mW + C₁ * r * mV) :=
  wobs_raw_stepAB ethSubLocAB_two

end

end PtCorr2

end

/-!
# The `ab` step bounds along the history from scale `j₀` (`ab` copies of `KObsHist`, `ObsHist`)

Along `obsHistFrom j₀ o₀` from an observable, local, `U(1)`-invariant and anchored state
(`ObsAnchInv`, as `redSt` at coalescence: `redSt_isObs`, `obsLocInv_redSt`, `obsSymInv_redSt`,
`obsAnchInv_redSt`), for weights with `w.Sub` and finite components:

* `KObsBoundsAB`, `WObsBoundsAB`: the conclusions of `kobs_raw_stepAB`, `wobs_raw_stepAB` as named
  properties of the constants; `kobs_bounds_AB`, `wobs_bounds_AB` (from `wobs_raw_stepAB2`,
  unconditional since `EthSubLocAB 2` is proved, `Obs2.ethSubLocAB_two`);
* **`kobs_hist_stepAB`**, **`wobs_hist_stepAB`**: one step at scale `j ≥ j₀` along the history
  (plumbing as `kobs_hist_step`, `wobs_hist_step`; the invariants along `obsHistFrom` by
  `obsLocInv_histFrom'`, `obsSymInv_histFrom'`, `obsAnchInv_histFrom'`, `obsHistFrom_isObs`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The conclusion of `kobs_raw_stepAB` for given constants. -/
def KObsBoundsAB (L : ℕ) [NeZero L] (A C₀ η ε₀ C₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
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

/-- The conclusion of `wobs_raw_stepAB` for given constants. -/
def WObsBoundsAB (L : ℕ) [NeZero L] (Kw C₁ ε₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ ε₁ → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).W c') ≤
          ENNReal.ofReal ((Kw / L + C₁ * r) * mW + C₁ * r * mV)

/-- **The constants of the `ab` `𝒲^{obs}` step** (unconditional: `wobs_raw_stepAB2`). -/
theorem wobs_bounds_AB : ∃ (Kw : ℝ) (L₀ : ℕ), 0 ≤ Kw ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBoundsAB L Kw C₁ ε₁ :=
  wobs_raw_stepAB2

section Inv

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) {c : Obs.Case}

theorem obsLocInv_histFrom' {j : ℕ} {o' : ObsSt c L N} (h0 : ObsLocInv P j o')
    (t : Flow2.Hist.Seq (Xs R)) {k : ℕ} (hjk : j ≤ k)
    (h : ∀ i, j ≤ i → i < k → ValidCore R i ∧ RawInv R i (rawHist R i t)) :
    ObsLocInv P k (obsHistFrom R P j o' k t) := by
  have := obsLocInv_histFrom h0 t (k - j) (fun i hi1 hi2 => h i hi1 (by omega))
  rwa [Nat.add_sub_cancel' hjk] at this

theorem obsAnchInv_histFrom' {j : ℕ} {o' : ObsSt c L N} (h0 : ObsAnchInv P j o')
    (t : Flow2.Hist.Seq (Xs R)) {k : ℕ} (hjk : j ≤ k) :
    ObsAnchInv P k (obsHistFrom R P j o' k t) := by
  have := obsAnchInv_histFrom R P h0 t (k - j)
  rwa [Nat.add_sub_cancel' hjk] at this

end Inv

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **One step of the `K^{obs}` recursion along the history from `j₀` (`ab` version).** -/
theorem kobs_hist_stepAB {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsAB L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ck m k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < m) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t j).1) ^ 2 * m)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P j₀ o₀ (j + 1) t).K U) ≤
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
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  rw [obsHistFrom_succ hjj]
  exact hKB N R j hVj.toValidCore st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj) hg.le
    (cZ R * g) hz hy hη hηs c P w hws hwa hwb hwab (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 (hrε.trans hεε) hbr hk8 hεk' hVo hWo hKo

/-- **One step of `𝒲^{obs}` along the history from `j₀`** (`ab` version). -/
theorem wobs_hist_stepAB {Kw C₁ ε₁ : ℝ} (hWB : WObsBoundsAB L Kw C₁ ε₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P j₀ o₀ (j + 1) t).W c') ≤
        ENNReal.ofReal ((Kw / L + C₁ * (cR R Λ cm C₂ * (t j).1)) * mW +
          C₁ * (cR R Λ cm C₂ * (t j).1) * mV) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  rw [obsHistFrom_succ hjj]
  exact hWB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 _ _ (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs c P w hws (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc _ _ _
    mV mW (by positivity) (norm_nonneg _) hr0.le (hrε.trans hε₁) hmV hmW hWl hDd hvr hwr hVo hWo

end Hist

end

end PtCorr2
