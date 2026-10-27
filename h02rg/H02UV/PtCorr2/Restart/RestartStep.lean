import PtCorr2.Obs.ObsHistRelE
import PtCorr2.Pair.KObsHistAB
import PtCorr2.Obs.ObsSymFrom
import Obs2.Flow.RestartFlow

/-!
# The restarted one-point flow along the history: chain and one-step bounds (B3, T4)

Along `obsHistFrom R P m o'` (the observable flow started at scale `m` from a general Case-(2)
datum `o'`, Loc point `P.a`):

* `histVF2`, `histWF2`, `histKF2` (the full inputs), the `σ_a` components and their step;
  `hformF2` (`V_k(B)_a = α + βψ̄_aψ_a`, `k ≥ m`) and **`muChain2F_histFrom`**: the restarted
  chain `MuChain2F` along the history; `obsHistF2_pure`: the `σ_a` parts of `V_k(B)` have no
  constant (`k > m` always, `k = m` if the datum has none);
* `kobs_state_step`, `wobs_state_step`: the one-step `K^{obs}`, `𝒲^{obs}` bounds of
  `kobs_hist_step`, `wobs_hist_step` for an arbitrary observable, local, symmetric state at
  scale `j` (the history from scale `0` is not used); **`kobs_hist_stepF`**,
  **`wobs_hist_stepF`**: along `obsHistFrom`;
* `histKF2_hK1`, **`kobs_EK2F`**: the activity term in `ℓ¹` along `obsHistFrom`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-! ### The restarted chain along the history -/

section Chain

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (m : ℕ)
  (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))

/-- The full `V♭_k + V^{obs}_k` along the restarted history. -/
def histVF2 (k : ℕ) : OFam .two 2 L N :=
  fullV R k (rawHist R k t) (t k).1 (t k).2.1 (obsHistFrom R P m o' k t)

/-- The full `𝒲_k + 𝒲^{obs}_k` along the restarted history. -/
def histWF2 (k : ℕ) : OFam .two 2 L N :=
  fullW (rawHist R k t) (rawD R (rawHist R k t).u (t k).2.2) (obsHistFrom R P m o' k t)

/-- The full `K♭_k + K^{obs,♭}_k` along the restarted history. -/
def histKF2 (k : ℕ) : OAct .two 2 L N :=
  fullK R k (rawHist R k t) (rawK R (rawHist R k t).u (t k).2.2) (obsHistFrom R P m o' k t)

theorem histVF2_a (k : ℕ) (b : Fin 2 → ℕ) :
    (histVF2 R P m o' t k b : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o' k t).V b : SA .two (Lam 2 L N)).a :=
  emb_add_cmp true _ _

theorem histWF2_a (k : ℕ) (b : Fin 2 → ℕ) :
    (histWF2 R P m o' t k b : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o' k t).W b : SA .two (Lam 2 L N)).a :=
  emb_add_cmp true _ _

theorem histVF2_succ_a {k : ℕ} (hk : m ≤ k) (c' : Fin 2 → ℕ) :
    (histVF2 R P m o' t (k + 1) c' : SA .two (Lam 2 L N)).a =
      (Vnext2O P k (histCovO R t k) (histVF2 R P m o' t k) (histWF2 R P m o' t k)
        (histKF2 R P m o' t k) c' : SA .two (Lam 2 L N)).a := by
  rw [histVF2_a, obsHistFrom_succ hk]
  exact piobs_cmp true _

theorem histWF2_succ_a {k : ℕ} (hk : m ≤ k) (c' : Fin 2 → ℕ) :
    (histWF2 R P m o' t (k + 1) c' : SA .two (Lam 2 L N)).a =
      (Wnext2O P k (histCovO R t k) (histVF2 R P m o' t k) (histWF2 R P m o' t k) c' :
        SA .two (Lam 2 L N)).a := by
  rw [histWF2_a, obsHistFrom_succ hk]
  exact piobs_cmp true _

/-- `V_k(B)_a = α + βψ̄_aψ_a` along the restarted history (`k ≥ m`). -/
theorem hformF2 (h0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a) :
    ∀ k, m ≤ k → ∀ b, Loc2Form P.a (histVF2 R P m o' t k b : SA .two (Lam 2 L N)).a := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro b; rw [histVF2_a, obsHistFrom_self]; exact h0 b
  | succ k hk ih =>
    intro b
    rw [histVF2_succ_a R P m o' t hk]
    exact Vnext2O_a_two_form P k _ _ _ _ b ih

/-- **The restarted chain along the history.** -/
theorem muChain2F_histFrom {n : ℕ} (hmn : m ≤ n) (hN : n < N)
    (h0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a) :
    MuChain2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) (histKF2 R P m o' t)
      m n where
  hmn := hmn
  hN := hN
  hW k hk _ c' := histWF2_succ_a R P m o' t hk c'
  hV k hk _ c' := histVF2_succ_a R P m o' t hk c'
  hform k hk _ b := (hformF2 R P m o' t h0 k hk b).eq_mass2

/-- **`V_k(B)_a = m₂(V_k(B)_a)ψ̄_aψ_a`** along the restarted history, for a datum without
constants. -/
theorem obsHistF2_pure (h0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a) :
    ∀ k, m ≤ k → ∀ b, ((obsHistFrom R P m o' k t).V b : SA .two (Lam 2 L N)).a =
      mass2 ((obsHistFrom R P m o' k t).V b : SA .two (Lam 2 L N)).a • pbp P.a := by
  intro k hk b
  rcases Nat.eq_or_lt_of_le hk with rfl | hlt
  · rw [obsHistFrom_self]; exact hp b
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : m ≤ k' := by omega
    have e := histVF2_succ_a R P m o' t hk' b
    rw [histVF2_a] at e
    rw [e]
    refine eq_mass2_smul_of_eps (Vnext2O_a_two_form P k' _ _ _ _ b
      (hformF2 R P m o' t h0 k' hk')) ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]
    exact sum_eq_zero fun b' _ => eps_VpO_a P k' _ _ _ _ b'

end Chain

/-! ### One step for an arbitrary state -/

section Step

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **One step of the `K^{obs}` recursion for an arbitrary state** (copy of `kobs_hist_step`). -/
theorem kobs_state_step {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (o : ObsSt c L N) (hobs : o.IsObs) (hloc : ObsLocInv P j o) (hsym : ObsSymInv j o)
    (ck m k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < m) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t j).1) ^ 2 * m)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) (o.V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) (o.W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) (o.K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        oTo w (j + 1) (histS R (j + 1) t) ((obsStep R P j (rawHist R j t) (t j).1 (t j).2.1
          (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) o).K U) ≤
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
  exact hKB N R j hVj.toValidCore st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj) hg.le
    (cZ R * g) hz hy hη hηs c P w hw0 hwa hwb o hobs hloc hsym
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 (hrε.trans hεε) hbr hk8 hεk' hVo hWo hKo

/-- **One step of `𝒲^{obs}` for an arbitrary state** (copy of `wobs_hist_step`). -/
theorem wobs_state_step {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (o : ObsSt c L N) (hobs : o.IsObs) (hloc : ObsLocInv P j o) (hsym : ObsSymInv j o)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) (o.V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) (o.W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t) ((obsStep R P j (rawHist R j t) (t j).1 (t j).2.1
          (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) o).W c') ≤
        ENNReal.ofReal ((Kw / L + C₁ * (cR R Λ cm C₂ * (t j).1)) * mW +
          C₁ * (cR R Λ cm C₂ * (t j).1) * mV) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  exact hWB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 _ _ (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs c P w hw0 o hobs hloc hsym _ _ _ mV mW
    (by positivity) (norm_nonneg _) hr0.le (hrε.trans hε₁) hmV hmW hWl hDd hvr hwr hVo hWo

/-! ### Along the restarted history -/

theorem histFrom_inv {c : Obs.Case} (hV : ∀ j < Nh, ValidAt R j) (P : ObsPts 2 L N) {m : ℕ}
    {o' : ObsSt c L N} (h0 : o'.IsObs) (hl0 : ObsLocInv P m o') (hs0 : ObsSymInv m o')
    (t : Flow2.Hist.Seq (Xs R)) {j : ℕ} (hmj : m ≤ j) (hj : j < Nh) :
    (obsHistFrom R P m o' j t).IsObs ∧ ObsLocInv P j (obsHistFrom R P m o' j t) ∧
      ObsSymInv j (obsHistFrom R P m o' j t) := by
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  exact ⟨obsHistFrom_isObs h0 t j,
    obsLocInv_histFrom' R P hl0 t hmj fun i _ hi => hval i (by omega),
    obsSymInv_histFrom' R P hs0 t hmj fun i _ hi => hval i (by omega)⟩

set_option maxHeartbeats 1000000 in
/-- **One step of `K^{obs}` along the restarted history.** -/
theorem kobs_hist_stepF {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    {m : ℕ} (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o') (hs0 : ObsSymInv m o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : m ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ck mm k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < mm) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t j).1) ^ 2 * mm)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).V b) ≤ ENNReal.ofReal mm)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * mm))
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P m o' (j + 1) t).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t j).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t j).1) ^ 2 * mm) := by
  obtain ⟨hobs, hloc, hsym⟩ := histFrom_inv R hV P h0 hl0 hs0 t hmj hj
  rw [obsHistFrom_succ hmj]
  exact kobs_state_step R hKB hSB hV hm hβ hδ1 H P w hw0 hwa hwb t j hj ht _ hobs hloc hsym ck mm k
    hck hm0 hk0 hε1 hεε hεk hk8 hVo hWo hKo

/-- **One step of `𝒲^{obs}` along the restarted history.** -/
theorem wobs_hist_stepF {Kw C₁ ε₁ : ℝ} (hWB : WObsBounds L Kw C₁ ε₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0)
    {m : ℕ} (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o') (hs0 : ObsSymInv m o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : m ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P m o' j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P m o' (j + 1) t).W c') ≤
        ENNReal.ofReal ((Kw / L + C₁ * (cR R Λ cm C₂ * (t j).1)) * mW +
          C₁ * (cR R Λ cm C₂ * (t j).1) * mV) := by
  obtain ⟨hobs, hloc, hsym⟩ := histFrom_inv R hV P h0 hl0 hs0 t hmj hj
  rw [obsHistFrom_succ hmj]
  exact wobs_state_step R hWB hSB hV hm hβ hδ1 H P w hw0 t j hj ht _ hobs hloc hsym hε₁ mV mW
    hmV hmW hVo hWo

theorem histKF2_hK1 (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))
    (j : ℕ) (hmj : m ≤ j) (hl0 : ObsLocInv P m o')
    (h : ∀ i ≤ j, ValidCore R i ∧ RawInv R i (rawHist R i t))
    {ℓ k wa : ℝ} (hℓ : 0 < ℓ) (hwa : 0 < wa) (hk : 0 ≤ k)
    (hK : ∀ X, IsSmall j X → ENNReal.ofReal wa *
      Tj 2 (L : ℝ) j ℓ (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
      ‖mass2 (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a‖ ≤
        csN 2 * (k / wa) * ℓ⁻¹ ^ 2 := by
  have ho := obsLocInv_histFrom' R P hl0 t hmj fun i _ hi => h i hi.le
  have HL := olocS_full R P (t j).1 (t j).2.1 (st := rawHist R j t)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2)
    (h j le_rfl).1 (h j le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _) ho
  refine sum_norm_mass2_le P.a (histKF2 R P m o' t j) hℓ hwa hk (fun X hX ha => ?_) hK
  exact ((HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.2.1 ha).1

set_option maxHeartbeats 2000000 in
/-- **The activity term in `ℓ¹` along the restarted history** (copy of `kobs_EK2`). -/
theorem kobs_EK2F (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (hl0 : ObsLocInv P m o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : m ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (w : Wt) (hw0 : w.ab = 0) (wa : ℝ) (hwa0 : 0 < wa) (hwa : w.a = ENNReal.ofReal wa)
    (k : ℝ) (hk0 : 0 ≤ k)
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) ≤ ENNReal.ofReal k) :
    ∑ X ∈ smallSets (L := L) (N := N) j,
        ‖mass2 (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a‖ ≤
      csN 2 * (8 * k / wa) * (histS R j t)⁻¹ ^ 2 := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  have hZ : (rawHist R j t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 j le_rfl
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t j).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R j hVj.toValidCore _ HI (t j).1 (t j).2.1 (hm j hj) hg.le _ hz hy hη).2
  have hs : 0 < histS R j t := mul_pos (fscale_pos hZ) hℓ
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hA : 0 < R.A := Fact.out
  refine histKF2_hK1 R P o' t j hmj hl0 (fun i hi => hval i (by omega)) hs hwa0
    (by positivity : (0 : ℝ) ≤ 8 * k) (fun X hX => ?_)
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hnb : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2)
    (obsHistFrom R P m o' j t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) j (histS R j t)
        (histKF2 R P m o' t j X : SA .two (Lam 2 L N)).a
      ≤ oTo w j (histS R j t) (histKF2 R P m o' t j X) := wa_Tj_a_le_oTo w hwa j _ _
    _ ≤ ENNReal.ofReal 8 * oTo w j (histS R j t) ((obsHistFrom R P m o' j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

end Step

end

end PtCorr2
