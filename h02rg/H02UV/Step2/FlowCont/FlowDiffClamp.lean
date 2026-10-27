import Step2.FlowCont.FlowDiffHist
import Step2.Flow.FlowF1

/-!
# The clamps of the RG map are strictly inactive on the open domain (`thm:flow`(iii))

For a history `t` in the open part of the domain (`Flow2.Hist.InDhs`: `InDh`, `g_i < ε` for
`i ≤ j` and `G_j(t) < ε`), all clamps of the steps `0, …, j` are strictly inactive
(`clamps_of_InDhs`):
* `|(z_i + y_i)/Z_i| ≤ 2 C_z g_i < 2 C_z ε ≤ ρ` and `|y_i/Z_i| < ρ` by the a priori bounds
  (`apriori`); at `i = j + 1` along the history continued by `(G_j(t), 0, 0)` (`contHist`);
* `|4 ν_raw w^{(1)}| ≤ 4 |μ_i| ℓ² ≤ 4 c_μ g_i ℓ² < 4 c_μ ε ℓ² ≤ 1/8` (`norm_Zw1_le`);
* `|4 κ_ν w'^{(1)}| ≤ 4 ℓ² |ν_{j+1}| ≤ 4 ℓ² (L² c_μ + c_m) g_j < 1/8`, by the complex form of (F2)
  (`F2c_rg`: `|ν_{j+1} - L² μ_j| ≤ c_m g_j`, including the imaginary part) and
  `norm_Zw1_succ_le`, under the smallness condition `4 ℓ² (L² c_μ + c_m) ε ≤ 1/8`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section F2c

variable {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **(F2) in complex form**: `|ν_{j+1} - L² μ_j| ≤ c_m g_j` (the proof of `F2_rg`). -/
theorem F2c_rg (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hF2 : cF2 R + (16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 +
      (L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS) * cmu ((L : ℝ) ^ 2) cm +
      2 * ((L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS)) * ε ≤ cm) :
    ∀ j < Nh, ∀ t, Flow2.Hist.InDh ((L : ℝ) ^ 2) β δ κ cg cm cT ε j t →
      ‖(histOut R j t).nu - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ)‖ ≤ cm * (t j).1 := by
  have hℓ : 0 < R.ℓ := Fact.out
  intro j hj t ht
  have hAP := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hz, hy, hWl⟩ := hAP
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R ((L : ℝ) ^ 2) cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R ((L : ℝ) ^ 2) cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤
      cV R ((L : ℝ) ^ 2) cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu ((L : ℝ) ^ 2) cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R ((L : ℝ) ^ 2) cm C₂ * g with hr
  have hcr : 0 ≤ cR R ((L : ℝ) ^ 2) cm C₂ := by unfold cR; positivity
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R ((L : ℝ) ^ 2) cm C₂ + 1 ≤
        (cV R ((L : ℝ) ^ 2) cm + cW R ((L : ℝ) ^ 2) cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hrε : r ≤ εs := by
    rw [hr]; have := H.h4
    calc cR R ((L : ℝ) ^ 2) cm C₂ * g ≤ cR R ((L : ℝ) ^ 2) cm C₂ * ε := by gcongr
      _ ≤ εs := this
  have hkε : 8 * ‖x.2‖ ≤ εs := by
    have : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
      have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
      exact mul_le_mul_of_nonneg_left this H.hcx
    linarith [H.h5]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  obtain ⟨-, -, cν, -, -, -⟩ := hSB N R j hVj st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj) hg.le (cZ R * g) hz hy hη hηs
    (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r (by positivity) (norm_nonneg _) (norm_nonneg _)
    hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hrε hkε
  refine cν.trans ?_
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g
  have hv0 : 0 ≤ v := by have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
  have hg2 : g ^ 2 ≤ ε * g := by nlinarith
  have hg3' : g ^ 3 ≤ ε * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
  have hE : (2 * (L : ℝ) ^ 2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) +
      Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖)))) /
        R.ℓ ^ 2 ≤ (L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS * ε * g := by
    have hs : BH.sig 2 L v (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖) ≤
        (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 := by
      unfold BH.sig
      have h1 : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv0 hvr 2
      rw [hr] at h1 hwr
      have h2 : (cR R ((L : ℝ) ^ 2) cm C₂ * g) ^ 2 = cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 := by ring
      rw [h2] at h1 hwr
      nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hN0 (sq_nonneg (Q1 2))),
        mul_le_mul_of_nonneg_left hwr (by linarith : (0 : ℝ) ≤ Q1 2)]
    have hk : ‖x.2‖ ≤ cx κ cT * (ε * g) := hx2.trans (mul_le_mul_of_nonneg_left hg3' H.hcx)
    have hCq := H.hCq; have hCl := H.hCl; have hcS := H.hcS
    unfold cE
    rw [div_le_iff₀ (by positivity)]
    have t1 : 2 * (L : ℝ) ^ 2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) ≤
        (L : ℝ) ^ 2 * (16 * Cq * cS * Cl * cx κ cT) * (ε * g) := by
      have := mul_le_mul_of_nonneg_left hk
        (by positivity : (0 : ℝ) ≤ 16 * (L : ℝ) ^ 2 * Cq * cS * Cl)
      nlinarith
    have t2 : Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖))) ≤
        (L : ℝ) ^ 2 * (Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
          cR R ((L : ℝ) ^ 2) cm C₂ ^ 2) * (ε * g) := by
      have h1 := mul_le_mul_of_nonneg_left hs
        (by positivity : (0 : ℝ) ≤ Cq * Cl * (L : ℝ) ^ 2)
      have h2 : (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 ≤
          (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * (ε * g) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Cq * Cl * (L : ℝ) ^ 2)
      have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 :=
        one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
      have h4 : 0 ≤ Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
          cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * (ε * g) := by have := H.hε; positivity
      nlinarith
    have e : (L : ℝ) ^ 2 * ((16 * Cq * cS * Cl * cx κ cT + Cq * Cl * (L : ℝ) ^ 2 *
        (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R ((L : ℝ) ^ 2) cm C₂ ^ 2) / R.ℓ ^ 2) * ε * g * R.ℓ ^ 2
        = (L : ℝ) ^ 2 * (16 * Cq * cS * Cl * cx κ cT) * (ε * g) +
          (L : ℝ) ^ 2 * (Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
            cR R ((L : ℝ) ^ 2) cm C₂ ^ 2) * (ε * g) := by field_simp
    linarith
  have hμ' : |μ| ≤ cmu ((L : ℝ) ^ 2) cm * g := hμ
  have hcmu := H.hcmu
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  set X := Cq * (cS * (Cl * (8 * ‖x.2‖))) with hX
  set Y := Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖)))
    with hY
  have hX0 : 0 ≤ X := by have := H.hCq; have := H.hCl; have := H.hcS; positivity
  have hY0 : 0 ≤ Y := by
    have := H.hCq; have := H.hCl
    have := BH.sig_nonneg (L := L) (d := 2) (by norm_num) v
      (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖) (by positivity)
    positivity
  have hℓ2 : 0 < R.ℓ ^ 2 := by positivity
  set E := (L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS with hEdef
  have hE0 : 0 ≤ E := by
    have := H.hCq; have := H.hCl; have := H.hcx
    have hcS0 : 0 ≤ cS := by linarith [H.hcS]
    rw [hEdef]; unfold cE; positivity
  have hE' : (2 * (L : ℝ) ^ 2 * X + Y) / R.ℓ ^ 2 ≤ E * ε * g := by
    have : 2 * (L : ℝ) ^ 2 * X = 2 * (L : ℝ) ^ 2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) := by
      rw [hX]; ring
    rw [this]; exact hE
  have hA : (2 * X + Y) / R.ℓ ^ 2 ≤ E * g := by
    have h1 : (2 * X + Y) / R.ℓ ^ 2 ≤ (2 * (L : ℝ) ^ 2 * X + Y) / R.ℓ ^ 2 := by
      gcongr; nlinarith
    have h2 : E * ε * g ≤ E * g := by
      have := mul_le_mul_of_nonneg_left H.hε1 hE0
      nlinarith [mul_le_mul_of_nonneg_right this hg.le]
    linarith
  have hB : 2 * ((L : ℝ) ^ 2 * X + Y) / R.ℓ ^ 2 ≤ 2 * (E * ε * g) := by
    have : 2 * ((L : ℝ) ^ 2 * X + Y) / R.ℓ ^ 2 ≤ 2 * ((2 * (L : ℝ) ^ 2 * X + Y) / R.ℓ ^ 2) := by
      rw [mul_div_assoc]; gcongr; nlinarith
    linarith
  have hμε : |μ| ≤ cmu ((L : ℝ) ^ 2) cm * ε := hμ'.trans (mul_le_mul_of_nonneg_left hgε hcmu)
  have hT1 : 16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 * g + (2 * X + Y) / R.ℓ ^ 2) * |μ| ≤
      16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 + E) * cmu ((L : ℝ) ^ 2) cm * ε * g := by
    have h1 : 8 * R.ℓ ^ 2 / 49 * g + (2 * X + Y) / R.ℓ ^ 2 ≤ (8 * R.ℓ ^ 2 / 49 + E) * g := by
      nlinarith
    have h0 : 0 ≤ 8 * R.ℓ ^ 2 / 49 * g + (2 * X + Y) / R.ℓ ^ 2 := by positivity
    have h2 := mul_le_mul h1 hμε (abs_nonneg μ) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 / 7 * (L : ℝ) ^ 2)
    calc _ = 16 / 7 * (L : ℝ) ^ 2 * ((8 * R.ℓ ^ 2 / 49 * g + (2 * X + Y) / R.ℓ ^ 2) * |μ|) := by
          ring
      _ ≤ _ := h3
      _ = _ := by ring
  have hF2' := mul_le_mul_of_nonneg_right hF2 hg.le
  unfold cF2 at hF2'
  have e1 : 2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) = 2 * X := by rw [hX]; ring
  have e2 : (L : ℝ) ^ 2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) = (L : ℝ) ^ 2 * X := by rw [hX]; ring
  rw [e1, e2]
  nlinarith


end F2c

section Zw

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `|Z_{j+2} w^{(1)}_{j+1}| ≤ ℓ² L^{2(j+1)}`, with validity only up to `j` (the variant of
`norm_Zw1_le` at the output of step `j`). -/
theorem norm_Zw1_succ_le (hρ : 0 ≤ R.ρ) (j : ℕ) (hV : ∀ i ≤ j, ValidAt R i)
    (t : Flow2.Hist.Seq (Xs R)) :
    ‖stZ' R (rawHist R (j + 1) t) * (rawHist R (j + 1) t).w1‖ ≤
      R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := by
    have ih := norm_Zw1_le R hρ j (fun i hi => hV i (by omega)) t
    have hVj := hV j le_rfl
    obtain ⟨hj2, -, hL8, -, hρ8, hℓ, -⟩ := hVj
    have H := rawInv_hist R hρ j (fun i hi => hV i (by omega)) t
    set st := rawHist R j t
    have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ st).trans hρ8
    have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
    have hZ'n : 0 < ‖stZ' R st‖ := norm_pos_iff.2 hZ'
    -- the new zero mode
    obtain ⟨hC, -⟩ := H.cov (hV j (by omega))
    have hz := zero_mode_le (by omega) hC
    have hℓC : (fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) * R.ℓ / 4) ^ 2 =
        R.ℓ ^ 2 / (16 * ‖stZ' R st‖) := by
      rw [div_pow, mul_pow, show fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) ^ 2 =
        ‖stZ' R st‖⁻¹ from by unfold fscale; rw [Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _))]; rfl]
      field_simp; ring
    rw [hℓC] at hz
    have hzZ : ‖stZ' R st * ∑ x, stCov R j st x 0‖ ≤ 9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := by
      rw [norm_mul]
      calc ‖stZ' R st‖ * ‖∑ x, stCov R j st x 0‖
          ≤ ‖stZ' R st‖ * (9 * ((L : ℝ) ^ (j + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * ‖stZ' R st‖))) :=
            mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ = _ := by field_simp
    -- the next normalisation
    set st' := rawHist R (j + 1) t
    have hst'Z : st'.Z = stZ' R st := rfl
    have hρ8' := hρ8
    have hζ' : ‖stZeta R st'‖ ≤ 1 / 8 := (norm_stZeta_le hρ st').trans hρ8'
    have e : stZ' R st' * st'.w1 = (1 + stZeta R st') *
        (stZ' R st * st.w1 + stZ' R st * ∑ x, stCov R j st x 0) := by
      show st'.Z * (1 + stZeta R st') * (st.w1 + ∑ x, stCov R j st x 0) = _
      rw [hst'Z]; ring
    rw [e, norm_mul]
    have h1 : ‖1 + stZeta R st'‖ ≤ 9 / 8 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have h2 := (norm_add_le _ _).trans (add_le_add ih hzZ)
    have hL2 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
      nlinarith
    have hP : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by ring
    rw [hP] at h2 ⊢
    have hl : 0 ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 := by positivity
    calc ‖1 + stZeta R st'‖ * ‖stZ' R st * st.w1 + stZ' R st * ∑ x, stCov R j st x 0‖
        ≤ 9 / 8 * (R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 +
            9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) := by nlinarith


end Zw

section Clamp

variable {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {β δ κ cg cm cT ε : ℝ}

/-- The history `t` continued at `j + 1` by `(G_j(t), 0, 0)`. -/
def contHist (j : ℕ) (t : Hist.Seq (Xs R)) : Hist.Seq (Xs R) :=
  Function.update t (j + 1) ((rgData R).G j t, 0, 0)

theorem contHist_le {j : ℕ} (t : Hist.Seq (Xs R)) {i : ℕ} (hi : i ≤ j) :
    contHist R j t i = t i :=
  Function.update_of_ne (by omega) _ _

theorem contHist_succ (j : ℕ) (t : Hist.Seq (Xs R)) :
    contHist R j t (j + 1) = ((rgData R).G j t, 0, 0) := Function.update_self _ _ _

theorem rawHist_contHist (j : ℕ) (t : Hist.Seq (Xs R)) :
    rawHist R (j + 1) (contHist R j t) = rawHist R (j + 1) t :=
  rawHist_causal R (j + 1) _ _ fun i hi => contHist_le R t (by omega)

/-- The continued history is a regular history in the domain up to `j + 1`. -/
theorem InDh_contHist {Λ : ℝ} {j : ℕ} {t : Hist.Seq (Xs R)}
    (ht : Hist.InDh Λ β δ κ cg cm cT ε j t) (hG0 : 0 < (rgData R).G j t)
    (hGε : (rgData R).G j t ≤ ε) (hcmu : 0 ≤ cmu Λ cm) (hcx : 0 ≤ cx κ cT)
    (hF1 : |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤
      δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    Hist.InDh Λ β δ κ cg cm cT ε (j + 1) (contHist R j t) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
    · rw [contHist_succ]
      refine ⟨hG0, hGε, ?_, ?_⟩
      · show |(0 : ℝ)| ≤ _
        rw [abs_zero]; exact mul_nonneg hcmu hG0.le
      · show ‖(0 : Xs R (j + 1))‖ ≤ _
        rw [norm_zero]; exact mul_nonneg hcx (pow_nonneg hG0.le 3)
    · rw [contHist_le R t hij]; exact ht.1 i hij
  · rcases (show i = j ∨ i < j by omega) with rfl | hij
    · rw [contHist_succ, contHist_le R t le_rfl]; exact hF1
    · rw [contHist_le R t (show i + 1 ≤ j by omega), contHist_le R t hij.le]; exact ht.2 i hij

set_option maxHeartbeats 4000000 in
/-- **All clamps are strictly inactive on the open part of the domain.** -/
theorem clamps_of_InDhs (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hF2 : cF2 R + (16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 +
      (L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS) * cmu ((L : ℝ) ^ 2) cm +
      2 * ((L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS)) * ε ≤ cm)
    (hcm : 0 < cm) (hΛ : 1 < (L : ℝ) ^ 2)
    (hnd : 4 * cmu ((L : ℝ) ^ 2) cm * ε * R.ℓ ^ 2 ≤ 1 / 8)
    (hn5 : 4 * R.ℓ ^ 2 * ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * ε ≤ 1 / 8)
    (F1 : ∀ j < Nh, ∀ t, Hist.InDh ((L : ℝ) ^ 2) β δ κ cg cm cT ε j t →
      |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3) :
    ∀ j < Nh, ∀ t, Hist.InDhs (rgData R) ((L : ℝ) ^ 2) β δ κ cg cm cT ε j t →
      ClampsIn R j t ∧ ClampsOut R j t := by
  intro j hj t hs
  obtain ⟨ht, hlt, hGlt⟩ := hs
  have hℓ : 0 < R.ℓ := Fact.out
  have hcZ : 0 < cZ R := by unfold cZ; positivity
  have hcmu : 0 < cmu ((L : ℝ) ^ 2) cm := cmu_pos hΛ hcm
  have hρ : 0 ≤ R.ρ := (hV j hj).2.2.2.1
  have hAP := apriori R hSB hV hm hβ hδ1 H
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  -- the absorbed couplings
  have k12 : ∀ i ≤ Nh, ∀ t' : Hist.Seq (Xs R), Hist.InDh ((L : ℝ) ^ 2) β δ κ cg cm cT ε i t' →
      (t' i).1 < ε →
      ‖((rawHist R i t').z + (rawHist R i t').y) / (rawHist R i t').Z‖ < R.ρ ∧
        ‖(rawHist R i t').y / (rawHist R i t').Z‖ < R.ρ := by
    intro i hi t' ht' hlt'
    obtain ⟨hz, hy, -⟩ := hAP i hi t' ht'
    have h1 : cZ R * (t' i).1 < cZ R * ε := mul_lt_mul_of_pos_left hlt' hcZ
    have h2 := H.h1
    have h3 : 0 ≤ cZ R * ε := by have := H.hε; positivity
    constructor
    · rw [add_div]
      refine (norm_add_le _ _).trans_lt ?_
      linarith
    · linarith
  -- the coordinate change at the input
  have k3 : ∀ i ≤ j, ‖4 * cNu R i (rawHist R i t) (t i).2.1 * (rawHist R i t).w1‖ < 1 / 8 := by
    intro i hi
    have hZw := norm_Zw1_le R hρ i (fun k hk => hV k (by omega)) t
    obtain ⟨hg, -, hμ, -⟩ := ht.1 i hi
    have e : 4 * cNu R i (rawHist R i t) (t i).2.1 * (rawHist R i t).w1 =
        (4 * ((t i).2.1 : ℂ)) * (stZ' R (rawHist R i t) * (rawHist R i t).w1) /
          (L : ℂ) ^ (2 * i) := by
      unfold cNu
      rw [show cZ1 R (rawHist R i t) = stZ' R (rawHist R i t) from rfl]
      ring
    have hL0 : (0 : ℝ) < ((L : ℝ) ^ i) ^ 2 := by positivity
    have hn : ‖(L : ℂ) ^ (2 * i)‖ = ((L : ℝ) ^ i) ^ 2 := by
      rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
    rw [e, norm_div, hn, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖(4 : ℂ)‖ = 4 by norm_num, div_lt_iff₀ hL0]
    have hμε : |(t i).2.1| < cmu ((L : ℝ) ^ 2) cm * ε :=
      hμ.trans_lt (mul_lt_mul_of_pos_left (hlt i hi) hcmu)
    have hP : 0 < R.ℓ ^ 2 * ((L : ℝ) ^ i) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hZw (by positivity : (0 : ℝ) ≤ 4 * |(t i).2.1|)
    have h2 : 4 * |(t i).2.1| * (R.ℓ ^ 2 * ((L : ℝ) ^ i) ^ 2) <
        4 * (cmu ((L : ℝ) ^ 2) cm * ε) * (R.ℓ ^ 2 * ((L : ℝ) ^ i) ^ 2) := by
      have := mul_lt_mul_of_pos_right hμε hP
      linarith
    have h3 : 4 * (cmu ((L : ℝ) ^ 2) cm * ε) * (R.ℓ ^ 2 * ((L : ℝ) ^ i) ^ 2) =
        (4 * cmu ((L : ℝ) ^ 2) cm * ε * R.ℓ ^ 2) * ((L : ℝ) ^ i) ^ 2 := by ring
    have h4 := mul_le_mul_of_nonneg_right hnd hL0.le
    linarith
  have hin : ClampsIn R j t := fun i hi =>
    ⟨(k12 i (by omega) t ⟨fun k hk => ht.1 k (by omega), fun k hk => ht.2 k (by omega)⟩
        (hlt i hi)).1,
      (k12 i (by omega) t ⟨fun k hk => ht.1 k (by omega), fun k hk => ht.2 k (by omega)⟩
        (hlt i hi)).2, k3 i hi⟩
  refine ⟨hin, ⟨?_, ?_⟩⟩
  · -- the absorbed coupling of the next step
    have hF1 := F1 j hj t ht
    obtain ⟨hg, hgε, -, -⟩ := ht.1 j le_rfl
    have hG0 : 0 < (rgData R).G j t := by
      have hr := (abs_le.1 hF1).1
      have hg1 : (t j).1 ≤ 1 := hgε.trans H.hε1
      have a1 : (t j).1 * (t j).1 ≤ 1 * (t j).1 := mul_le_mul_of_nonneg_right hg1 hg.le
      have a2 : (t j).1 * (t j).1 * (t j).1 ≤ 1 * (t j).1 * ε :=
        mul_le_mul a1 hgε hg.le (by positivity)
      have a3 : cg * ((t j).1 * (t j).1 * (t j).1) ≤ cg * (1 * (t j).1 * ε) :=
        mul_le_mul_of_nonneg_left a2 H.hcg
      have a4 : cg * ε * (t j).1 ≤ 1 / 6 * (t j).1 := mul_le_mul_of_nonneg_right H.h6 hg.le
      have hb : 0 ≤ β * (t j).1 ^ 2 * (1 - δ) := mul_nonneg (by positivity) (by linarith)
      have e1 : (t j).1 ^ 3 = (t j).1 * (t j).1 * (t j).1 := by ring
      have e2 : cg * (1 * (t j).1 * ε) = cg * ε * (t j).1 := by ring
      have e3 : β * (t j).1 ^ 2 * (1 - δ) = β * (t j).1 ^ 2 - δ * β * (t j).1 ^ 2 := by ring
      rw [e1] at hr
      linarith only [hr, a3, a4, hb, e2, e3, hg]
    have hc := InDh_contHist R ht hG0 hGlt.le hcmu.le H.hcx hF1
    have h := (k12 (j + 1) (by omega) (contHist R j t) hc
      (by rw [contHist_succ]; exact hGlt)).1
    rw [rawHist_contHist] at h
    exact h
  · -- the coordinate change at the output
    obtain ⟨hg, hgε, hμ, -⟩ := ht.1 j le_rfl
    have hF2c := F2c_rg R hSB hV hm hβ hδ1 H hF2 j hj t ht
    have hZw := norm_Zw1_succ_le R hρ j (fun i hi => hV i (by omega)) t
    have HI := rawInv_hist R hρ (j + 1) (fun i hi => hV i (by omega)) t
    have hρ1 : R.ρ < 1 := by linarith [(hV j hj).2.2.2.2.1]
    have hZ2 : stZ' R (rawHist R (j + 1) t) ≠ 0 :=
      mul_ne_zero (HI.Z_ne_zero hρ1) (one_add_ne_zero ((absorb_le R hρ _ _).trans_lt hρ1))
    obtain ⟨κ2, hκ2⟩ : ∃ x, x = cκ R j (rawHist R j t) (t j).1 (t j).2.1
        (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) 2 := ⟨_, rfl⟩
    have enu : (histOut R j t).nu =
        κ2 * (L : ℂ) ^ (2 * (j + 1)) / stZ' R (rawHist R (j + 1) t) := by rw [hκ2]; rfl
    have hLc : (L : ℂ) ^ (2 * (j + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hLpos.ne')
    have eκ : κ2 = (histOut R j t).nu * stZ' R (rawHist R (j + 1) t) / (L : ℂ) ^ (2 * (j + 1)) := by
      rw [enu]; field_simp
    show ‖4 * cκ R j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
      (rawK R (rawHist R j t).u (t j).2.2) 2 * (rawHist R (j + 1) t).w1‖ < 1 / 8
    rw [← hκ2, eκ]
    have e : 4 * ((histOut R j t).nu * stZ' R (rawHist R (j + 1) t) / (L : ℂ) ^ (2 * (j + 1))) *
        (rawHist R (j + 1) t).w1 = 4 * (histOut R j t).nu *
          (stZ' R (rawHist R (j + 1) t) * (rawHist R (j + 1) t).w1) / (L : ℂ) ^ (2 * (j + 1)) := by
      ring
    have hL0 : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by positivity
    have hn : ‖(L : ℂ) ^ (2 * (j + 1))‖ = ((L : ℝ) ^ (j + 1)) ^ 2 := by
      rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
    rw [e, norm_div, hn, norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num, div_lt_iff₀ hL0]
    have hnu : ‖(histOut R j t).nu‖ ≤ (L : ℝ) ^ 2 * |(t j).2.1| + cm * (t j).1 := by
      have h1 := norm_add_le ((histOut R j t).nu - (L : ℂ) ^ 2 * ((t j).2.1 : ℂ))
        ((L : ℂ) ^ 2 * ((t j).2.1 : ℂ))
      rw [sub_add_cancel, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs] at h1
      linarith
    have hnu2 : ‖(histOut R j t).nu‖ < ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * ε := by
      have h1 : (L : ℝ) ^ 2 * |(t j).2.1| ≤ (L : ℝ) ^ 2 * (cmu ((L : ℝ) ^ 2) cm * (t j).1) :=
        mul_le_mul_of_nonneg_left hμ (by positivity)
      have h2 : ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * (t j).1 <
          ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * ε :=
        mul_lt_mul_of_pos_left (hlt j le_rfl) (by positivity)
      have e : ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * (t j).1 =
          (L : ℝ) ^ 2 * (cmu ((L : ℝ) ^ 2) cm * (t j).1) + cm * (t j).1 := by ring
      linarith only [hnu, h1, h2, e]
    have hP : 0 < R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hZw
      (by positivity : (0 : ℝ) ≤ 4 * ‖(histOut R j t).nu‖)
    have h2 := mul_lt_mul_of_pos_right hnu2 (by positivity : (0 : ℝ) < 4 * (R.ℓ ^ 2 *
      ((L : ℝ) ^ (j + 1)) ^ 2))
    have h3 := mul_le_mul_of_nonneg_right hn5 hL0.le
    have e2 : ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * ε * (4 * (R.ℓ ^ 2 *
        ((L : ℝ) ^ (j + 1)) ^ 2)) = 4 * R.ℓ ^ 2 * ((L : ℝ) ^ 2 * cmu ((L : ℝ) ^ 2) cm + cm) * ε *
          ((L : ℝ) ^ (j + 1)) ^ 2 := by ring
    have e3 : 4 * ‖(histOut R j t).nu‖ * (R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2) =
        ‖(histOut R j t).nu‖ * (4 * (R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2)) := by ring
    linarith

end Clamp

end

end Step2
