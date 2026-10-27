import PtCorr2.Last.TopCoal3
import PtCorr2.Restart.RestartPairB

/-!
# T5: the `ab` chain along the restarted history (from scale `m`, nonzero initial `ab` part)

The unreduced `ab` recursion (`kab_hist`, `kab_hist_top`) along `obsHistFrom R P m δ`. The step
bound `KObsBoundsU` is state-general; only the induction changes: it starts at `m` from the datum's
own `ab` part, assumed of the form `A^{(|𝓑(X)|-4)_+}w_{ab}‖δ.K(X)_{ab}‖ ≤ c_{ab}r_mm_m²` with any
`c_{ab} ≥ 10B₂` (`B₂ = kB2 …`, the source constant).

* **`rpab_stepF`**: one step `j → j + 1` for `m ≤ j ≤ N_h` (`ValidAt` below `N_h`, `ValidAtL` at
  `N_h`; copy of `kobs_hist_stepU`/`kobs_hist_stepUL`).
* `rpab_next`: with `k₂ = c_{ab}r_jm_j²` at `j`, the `ab` size at `j + 1` is `≤ (c_{ab}/5)r_jm_j²`.
* **`rpab_hist`**: `A^{(…)}w_{ab}‖K_j(X)_{ab}‖ ≤ c_{ab}r_jm_j²` for `m ≤ j ≤ n ≤ N_h`.
* **`rpab_top`**: at `N_h + 1`: `≤ (c_{ab}/5)r_{N_h}m_{N_h}²`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **One step of the unreduced `ab` recursion along the restarted history** (`m ≤ j ≤ N_h`). -/
theorem rpab_stepF {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤) {ms : ℕ}
    (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o') (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : ms ≤ j) (hj : j ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hKs : ∀ X, IsSmall j X → ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ k₂ : ℝ) (hm0 : 0 < m) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hrm : cR R Λ cm C₂ * (t j).1 ≤ m)
    (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt : 8 * cx κ cT * (cR R Λ cm C₂ * (t j).1) ^ 3 +
      cR R Λ cm C₂ * (t j).1 / m * (8 * k₁) + (cR R Λ cm C₂ * (t j).1 / m) ^ 2 * (8 * k₂) ≤ ε₀)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hK1 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHistFrom R P ms o' j t).K X) ≤ ENNReal.ofReal k₁)
    (hK2 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (histS R j t)
        ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab) ≤ ENNReal.ofReal k₂) :
    let r := cR R Λ cm C₂ * (t j).1
    let kt := 8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal ((r / m) ^ 2) * (ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          ((obsHistFrom R P ms o' (j + 1) t).K U : SA c (Lam 2 L N)).ab)) ≤
      ENNReal.ofReal (kθ0 L R.A C₀ η * kt + C₁ * ((2 * r) ^ 3 + 2 * r * kt + kt ^ 2)) := by
  intro r0 kt0 U hU
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have hval := hist_validL R hV hVL t
  have HI := (hval j hj).2
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj t ht
  have hmj' : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact hm j h
    · obtain rfl : j = Nh := by omega
      exact hmNh
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
    have := H.h3
    nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hg3 H.hcx]
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
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  set ktr := 8 * ‖x.2‖ + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) with hktr
  have hkt' : ktr ≤ kt0 := by
    show 8 * ‖x.2‖ + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) ≤
      8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)
    linarith
  have hktr0 : 0 ≤ ktr := by positivity
  -- the observable invariants
  obtain ⟨hobs, hloc, hsym⟩ := rpb_inv_top R P hV hVL h0 hl0 hs0 t hmj (by omega)
  have key := hKB N R j (hval j hj).1 st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) hmj'
    hg.le (cZ R * g) hz hy hη hηs c P w hw hwa hwb hwab (obsHistFrom R P ms o' j t) hobs hloc
    hsym hKs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k₁ k₂ (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hrm hk₁ hk₂ hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr (by linarith) (hkt'.trans hkt) hVo hWo hK1 hK2 U hU
  rw [obsHistFrom_succ hmj]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ : 0 ≤ C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (R.A / 2) ^ (-η)) := by
    have := Real.rpow_nonneg hA0 (-η); positivity
  have h1 : C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (R.A / 2) ^ (-η)) * ktr ≤ kθ0 L R.A C₀ η * kt0 :=
    mul_le_mul_of_nonneg_left hkt' hθ
  have h2 : (2 * r) ^ 3 + 2 * r * ktr + ktr ^ 2 ≤ (2 * r) ^ 3 + 2 * r * kt0 + kt0 ^ 2 := by
    have : 2 * r * ktr ≤ 2 * r * kt0 := mul_le_mul_of_nonneg_left hkt' (by linarith)
    have : ktr ^ 2 ≤ kt0 ^ 2 := pow_le_pow_left₀ hktr0 hkt' 2
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hC₁
  linarith

set_option maxHeartbeats 4000000 in
/-- **The `ab` size after one step**: with `k₂ = c_{ab}r_jm_j²` at `j` (`c_{ab} ≥ 10B₂`), the `ab`
size at `j + 1` is `≤ (c_{ab}/5)r_jm_j²`. -/
theorem rpab_next {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤) {ms : ℕ}
    (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o') (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : ms ≤ j) (hj : j ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hKs : ∀ X, IsSmall j X → ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ c₁ cab : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : 0 < m) (hk₁0 : 0 ≤ k₁)
    (hk₁ : k₁ ≤ c₁ * (cR R Λ cm C₂ * (t j).1) ^ 2 * m)
    (hrm : cR R Λ cm C₂ * (t j).1 ≤ m)
    (hcab : 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ ≤ cab)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L R.A C₀ η + 16 * C₁ * (cR R Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hK1 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHistFrom R P ms o' j t).K X) ≤ ENNReal.ofReal k₁)
    (hK2 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (histS R j t)
        ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab * (cR R Λ cm C₂ * (t j).1) * m ^ 2)) :
    ∀ X, IsConn (j + 1) X → ENNReal.ofReal (R.A ^ (nb (j + 1) X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
        ((obsHistFrom R P ms o' (j + 1) t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab / 5 * ((cR R Λ cm C₂ * (t j).1) * m ^ 2)) := by
  set B₂ := kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ with hB₂
  have hcx := H.hcx
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ0 : 0 ≤ kθ0 L R.A C₀ η := by
    unfold kθ0; have := Real.rpow_nonneg hA0 (-η); positivity
  have hB0 : 0 ≤ B₂ := by rw [hB₂]; unfold kB2; positivity
  have hcab0 : 0 ≤ cab := le_trans (by positivity) hcab
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  intro X hX
  set r := cR R Λ cm C₂ * (t j).1 with hr
  have hg := (ht.1 j le_rfl)
  have hcv : 0 ≤ cV R Λ cm := by unfold cV cZ; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hr0 : 0 < r := by rw [hr]; have := hg.1; nlinarith
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hg.2.1 hcR
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hk₂0 : 0 ≤ cab * r * m ^ 2 := by positivity
  have hρk : r / m * k₁ ≤ c₁ * r ^ 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
    calc r * k₁ ≤ r * (c₁ * r ^ 2 * m) := mul_le_mul_of_nonneg_left hk₁ hr0.le
      _ = c₁ * r ^ 3 * m := by ring
  have hρ2 : (r / m) ^ 2 * (cab * r * m ^ 2) = cab * r ^ 3 := by field_simp
  have hr3 : r ^ 3 ≤ (cR R Λ cm C₂ * ε) ^ 3 := pow_le_pow_left₀ hr0.le hrε 3
  set kt := 8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * (cab * r * m ^ 2))
    with hkt
  have hktb : kt ≤ 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 := by
    have e : kt = 8 * cx κ cT * r ^ 3 + 8 * (r / m * k₁) +
        8 * ((r / m) ^ 2 * (cab * r * m ^ 2)) := by
      rw [hkt]; ring
    rw [e, hρ2]
    have : 8 * (cx κ cT + c₁ + cab) * r ^ 3 ≤
        8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 :=
      mul_le_mul_of_nonneg_left hr3 (by positivity)
    nlinarith
  have hstep := rpab_stepF R hKB hC₀ hC₁ hSB hV hVL hm hmNh hβ hδ1 H P w hw hwa hwb hwab o' h0
    hl0 hs0 t j hmj hj ht hKs m k₁ (cab * r * m ^ 2) hm0 hk₁0 hk₂0 hrm hεε (hktb.trans hktε)
    hVo hWo hK1 hK2 X hX
  have hreal := kab_real (θ₀ := kθ0 L R.A C₀ η) (C₁ := C₁) (cx := cx κ cT) (c₁ := c₁) hr0 hr1 hm0
    hk₁0 hk₂0 hθ0 hC₁ hcx hc₁ hk₁ (hktb.trans hkt1)
  have hρ0 : 0 < (r / m) ^ 2 := by positivity
  set Z := (8 * kθ0 L R.A C₀ η + 16 * C₁ * r + 8 * C₁ * kt) * (cab * r * m ^ 2) +
    B₂ * r * m ^ 2 with hZ
  have hY : ENNReal.ofReal (R.A ^ (nb (j + 1) X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
        ((obsHistFrom R P ms o' (j + 1) t).K X : SA c (Lam 2 L N)).ab) ≤ ENNReal.ofReal Z := by
    have h1 : ENNReal.ofReal ((r / m) ^ 2) * (ENNReal.ofReal (R.A ^ (nb (j + 1) X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          ((obsHistFrom R P ms o' (j + 1) t).K X : SA c (Lam 2 L N)).ab)) ≤
        ENNReal.ofReal ((r / m) ^ 2) * ENNReal.ofReal Z := by
      refine hstep.trans ?_
      rw [← ENNReal.ofReal_mul hρ0.le]
      exact ENNReal.ofReal_le_ofReal hreal
    exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.2 hρ0))
      ENNReal.ofReal_ne_top).1 h1
  refine hY.trans (ENNReal.ofReal_le_ofReal ?_)
  have hθt : 8 * kθ0 L R.A C₀ η + 16 * C₁ * r + 8 * C₁ * kt ≤ 1 / 10 := by
    have a1 : 16 * C₁ * r ≤ 16 * C₁ * (cR R Λ cm C₂ * ε) :=
      mul_le_mul_of_nonneg_left hrε (by positivity)
    have a2 : 8 * C₁ * kt ≤ 8 * C₁ * (8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3) :=
      mul_le_mul_of_nonneg_left hktb (by positivity)
    linarith
  have := mul_le_mul_of_nonneg_right hθt hk₂0
  have hB : B₂ * r * m ^ 2 ≤ cab / 10 * (r * m ^ 2) := by
    have : 0 ≤ r * m ^ 2 := by positivity
    nlinarith
  rw [hZ]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The `ab` part of the restarted activity**: from `c_{ab}r_mm_m²` at `m`, the bound
`A^{(…)}w_{ab}‖K_j(X)_{ab}‖ ≤ c_{ab}r_jm_j²` holds for `m ≤ j ≤ n ≤ N_h`. -/
theorem rpab_hist {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤) {ms : ℕ}
    (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o') (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R))
    (n : ℕ) (hn : n ≤ Nh) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε n t)
    (hKs : ∀ j, ms ≤ j → j < n → ∀ X, IsSmall j X →
      ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ : ℕ → ℝ) (c₁ cab : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : ∀ j, 0 < m j)
    (hmm : ∀ j, ms ≤ j → j < n → m j ≤ 2 * m (j + 1)) (hk₁0 : ∀ j, 0 ≤ k₁ j)
    (hk₁ : ∀ j, ms ≤ j → j < n → k₁ j ≤ c₁ * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j)
    (hrm : ∀ j, ms ≤ j → j < n → cR R Λ cm C₂ * (t j).1 ≤ m j)
    (hcab : 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ ≤ cab)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L R.A C₀ η + 16 * C₁ * (cR R Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ j, ms ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).V b) ≤ ENNReal.ofReal (m j))
    (hWo : ∀ j, ms ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m j))
    (hK1 : ∀ j, ms ≤ j → j < n → ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHistFrom R P ms o' j t).K X) ≤ ENNReal.ofReal (k₁ j))
    -- the datum's own `ab` part
    (hK20 : ∀ X, IsConn ms X → ENNReal.ofReal (R.A ^ (nb ms X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) ms (histS R ms t) (o'.K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab * (cR R Λ cm C₂ * (t ms).1) * m ms ^ 2)) :
    ∀ j, ms ≤ j → j ≤ n → ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (histS R j t)
        ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab * (cR R Λ cm C₂ * (t j).1) * m j ^ 2) := by
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hDh : ∀ j ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ0 : 0 ≤ kθ0 L R.A C₀ η := by
    unfold kθ0; have := Real.rpow_nonneg hA0 (-η); positivity
  have hcab0 : 0 ≤ cab := le_trans (by unfold kB2; have := H.hcx; positivity) hcab
  intro j
  induction j with
  | zero =>
    intro hm0' _ X hX
    obtain rfl : ms = 0 := by omega
    rw [obsHistFrom_self]; exact hK20 X hX
  | succ j ih =>
    intro hmj hj X hX
    rcases Nat.eq_or_lt_of_le hmj with e | hlt
    · rw [← e, obsHistFrom_self]; rw [← e] at hX; exact hK20 X hX
    have hjn : j < n := by omega
    have ih := ih (by omega) hjn.le
    have hnext := rpab_next R hKB hC₀ hC₁ hSB hV hVL hm hmNh hβ hδ1 H P w hw hwa hwb hwab o' h0
      hl0 hs0 t j (by omega) (by omega) (hDh j hjn.le) (hKs j (by omega) hjn) (m j) (k₁ j) c₁ cab
      hc₁ (hm0 j) (hk₁0 j) (hk₁ j (by omega) hjn) (hrm j (by omega) hjn) hcab hε1 hεε hkt1 hktε
      hθ' (hVo j (by omega) hjn) (hWo j (by omega) hjn) (hK1 j (by omega) hjn) ih X hX
    refine hnext.trans (ENNReal.ofReal_le_ofReal ?_)
    set r := cR R Λ cm C₂ * (t j).1 with hr
    have hr' : 5 / 6 * (t j).1 ≤ (t (j + 1)).1 :=
      g_succ_ge (hDh (j + 1) hj) hβ hδ1 H.hcg H.hε1 H.h6
    have hrr : r ≤ 6 / 5 * (cR R Λ cm C₂ * (t (j + 1)).1) := by
      rw [hr]; nlinarith
    have hmm' : m j ^ 2 ≤ 4 * m (j + 1) ^ 2 := by
      have := hmm j (by omega) hjn
      have := hm0 j
      nlinarith
    have hprod : r * m j ^ 2 ≤ 24 / 5 * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2) := by
      calc r * m j ^ 2 ≤ (6 / 5 * (cR R Λ cm C₂ * (t (j + 1)).1)) * (4 * m (j + 1) ^ 2) :=
            mul_le_mul hrr hmm' (sq_nonneg _) (by
              have : 0 ≤ (t (j + 1)).1 := (ht.1 (j + 1) hj).1.le
              positivity)
        _ = 24 / 5 * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2) := by ring
    have : 0 ≤ cab * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2) := by
      have : 0 ≤ (t (j + 1)).1 := (ht.1 (j + 1) hj).1.le
      positivity
    calc cab / 5 * (r * m j ^ 2)
        ≤ cab / 5 * (24 / 5 * ((cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ cab * (cR R Λ cm C₂ * (t (j + 1)).1) * m (j + 1) ^ 2 := by nlinarith

set_option maxHeartbeats 4000000 in
/-- **The `ab` part of the restarted activity at `N_h + 1`**: `rpab_hist` up to `N_h` and the
step `N_h → N_h + 1` (`rpab_next`): `≤ (c_{ab}/5)r_{N_h}m_{N_h}²`. -/
theorem rpab_top {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤) {ms : ℕ} (hmsN : ms ≤ Nh)
    (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o') (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (hKs : ∀ j, ms ≤ j → j ≤ Nh → ∀ X, IsSmall j X →
      ((obsHistFrom R P ms o' j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ : ℕ → ℝ) (c₁ cab : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : ∀ j, 0 < m j)
    (hmm : ∀ j, ms ≤ j → j < Nh → m j ≤ 2 * m (j + 1)) (hk₁0 : ∀ j, 0 ≤ k₁ j)
    (hk₁ : ∀ j, ms ≤ j → j ≤ Nh → k₁ j ≤ c₁ * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j)
    (hrm : ∀ j, ms ≤ j → j ≤ Nh → cR R Λ cm C₂ * (t j).1 ≤ m j)
    (hcab : 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ ≤ cab)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L R.A C₀ η + 16 * C₁ * (cR R Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + cab) * (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ j, ms ≤ j → j ≤ Nh → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).V b) ≤ ENNReal.ofReal (m j))
    (hWo : ∀ j, ms ≤ j → j ≤ Nh → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m j))
    (hK1 : ∀ j, ms ≤ j → j ≤ Nh → ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHistFrom R P ms o' j t).K X) ≤ ENNReal.ofReal (k₁ j))
    (hK20 : ∀ X, IsConn ms X → ENNReal.ofReal (R.A ^ (nb ms X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) ms (histS R ms t) (o'.K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab * (cR R Λ cm C₂ * (t ms).1) * m ms ^ 2)) :
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
        ((obsHistFrom R P ms o' (Nh + 1) t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (cab / 5 * ((cR R Λ cm C₂ * (t Nh).1) * m Nh ^ 2)) := by
  have hab := rpab_hist R hKB hC₀ hC₁ hSB hV hVL hm hmNh hβ hδ1 H P w hw hwa hwb hwab o' h0 hl0
    hs0 t Nh le_rfl ht (fun j h1 h2 => hKs j h1 h2.le) m k₁ c₁ cab hc₁ hm0 hmm hk₁0
    (fun j h1 h2 => hk₁ j h1 h2.le) (fun j h1 h2 => hrm j h1 h2.le) hcab hε1 hεε hkt1 hktε hθ'
    (fun j h1 h2 => hVo j h1 h2.le) (fun j h1 h2 => hWo j h1 h2.le)
    (fun j h1 h2 => hK1 j h1 h2.le) hK20
  exact rpab_next R hKB hC₀ hC₁ hSB hV hVL hm hmNh hβ hδ1 H P w hw hwa hwb hwab o' h0 hl0 hs0 t
    Nh hmsN le_rfl ht (hKs Nh hmsN le_rfl) (m Nh) (k₁ Nh) c₁ cab hc₁ (hm0 Nh) (hk₁0 Nh)
    (hk₁ Nh hmsN le_rfl) (hrm Nh hmsN le_rfl) hcab hε1 hεε hkt1 hktε hθ' (hVo Nh hmsN le_rfl)
    (hWo Nh hmsN le_rfl) (hK1 Nh hmsN le_rfl) (hab Nh hmsN le_rfl)

end Hist

end

end PtCorr2
