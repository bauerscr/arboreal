import Step2.Last.FlowGlueStep

/-!
# The sharpened mass bound at the step `j = N - 2` (route (a1), task 1)

`glue_core` bounds `|ν' - L²μ| ≤ c_ν ǧ` with `c_ν = cNuL`, which contains the term
`(16/7) L² (8ℓ²/49 + 16ℓ²/147) c_μ` *without* a factor `ε`: in `nu_alg` the factor `ǧ` of the
coefficient of `|μ| ≤ c_μ ǧ` was dropped by `ǧ ≤ 1`. As in `F2_rg` (where this term is absorbed
into `c_m` with a factor `ε`) we keep it: `ǧ² ≤ εǧ`. The sharp constant is

  `cNuLs = (16/7) L² (8ℓ²/49 + 16ℓ²/147) c_μ ε + 3 L² c_Z + 8ℓ²/49 + L² (16ℓ²/147)`,

so that for `ε` small `cNuLs ≈ 3L²c_Z + 8ℓ²/49 + (16/147)L²ℓ²`, independent of `c_m`.

* `nu_alg_sharp` (scalar algebra), `cNuLs`, `cNuLs_le_cNuL` (for `ε ≤ 1`);
* `glue_nu_sharp`: the `ν` conclusion of `glue_core` with `cNuLs` (same hypotheses, minus those
  only used for the other conclusions);
* `glue_step_nu_sharp`: the same along a regular history at `j = N_h` (`histOut R N_h t`).

The existing statements (`glue_core`, `glue_step`, `cNuL`) are unchanged.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- **The sharp constant of `|ν' - L² μ|`**: the `c_μ`-term of `cNuL` with a factor `ε`. -/
def cNuLs (R : RGPar 2 L N) (Λ cm ε : ℝ) : ℝ :=
  16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 + 16 * R.ℓ ^ 2 / 147) * cmu Λ cm * ε +
    3 * (L : ℝ) ^ 2 * cZ R + 8 * R.ℓ ^ 2 / 49 + (L : ℝ) ^ 2 * (16 * R.ℓ ^ 2 / 147)

/-- The scalar algebra of the `ν` bound, keeping the factor `ǧ ≤ ε` of the `μ`-term. -/
theorem nu_alg_sharp {X Lsq ℓ2 g Cq RQ RL mu cmuv cZv ε : ℝ}
    (hX : X ≤ 16 / 7 * Lsq * (8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu +
      3 * Lsq * (cZv * g) + 8 * ℓ2 / 49 * g + 2 * (Lsq * Cq * RQ + Cq * RL) / ℓ2)
    (hE : (2 * Cq * RQ + Cq * RL) / ℓ2 ≤ 16 * ℓ2 / 147 * g) (hRQ : 0 ≤ Cq * RQ)
    (hRL : 0 ≤ Cq * RL) (hL : 2 ≤ Lsq) (hℓ : 0 < ℓ2) (hg0 : 0 ≤ g) (hgε : g ≤ ε)
    (hmu0 : 0 ≤ mu) (hmu : mu ≤ cmuv * g) :
    X ≤ (16 / 7 * Lsq * (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * cmuv * ε + 3 * Lsq * cZv +
      8 * ℓ2 / 49 + Lsq * (16 * ℓ2 / 147)) * g := by
  have hE0 : 0 ≤ (2 * Cq * RQ + Cq * RL) / ℓ2 := by
    apply div_nonneg _ hℓ.le; linarith only [hRQ, hRL]
  have hc0 : 0 ≤ 8 * ℓ2 / 49 + 16 * ℓ2 / 147 := by positivity
  have hA : 8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2 ≤
      (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * g := by
    linarith only [hE, show (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * g =
      8 * ℓ2 / 49 * g + 16 * ℓ2 / 147 * g by ring]
  have hA0 : 0 ≤ 8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2 := by
    have : 0 ≤ 8 * ℓ2 / 49 * g := by positivity
    linarith only [this, hE0]
  have hcm0 : 0 ≤ cmuv * g := hmu0.trans hmu
  have e1 : (8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu ≤
      (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * g * (cmuv * g) :=
    mul_le_mul hA hmu hmu0 (by positivity)
  -- `g · (c_μ g) ≤ c_μ ε g`
  have hcmuv : 0 ≤ cmuv * g := hcm0
  have e1' : (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * g * (cmuv * g) ≤
      (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * (cmuv * g) * ε := by
    have := mul_le_mul_of_nonneg_left hgε (mul_nonneg hc0 hcmuv)
    linarith only [this, show (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * g * (cmuv * g) =
      (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * (cmuv * g) * g by ring]
  have e2 := mul_le_mul_of_nonneg_left (e1.trans e1') (by positivity : (0 : ℝ) ≤ 16 / 7 * Lsq)
  have e3 : 2 * (Lsq * Cq * RQ + Cq * RL) / ℓ2 ≤ Lsq * ((2 * Cq * RQ + Cq * RL) / ℓ2) := by
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hℓ.le
    have := mul_le_mul_of_nonneg_right hL hRL
    linarith only [this, show Lsq * (2 * Cq * RQ + Cq * RL) = 2 * (Lsq * (Cq * RQ)) +
      Lsq * (Cq * RL) by ring, show 2 * (Lsq * Cq * RQ + Cq * RL) = 2 * (Lsq * (Cq * RQ)) +
      2 * (Cq * RL) by ring]
  have e4 := mul_le_mul_of_nonneg_left hE (by linarith only [hL] : (0 : ℝ) ≤ Lsq)
  have e5 : 16 / 7 * Lsq * (8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu =
      16 / 7 * Lsq * ((8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu) := by ring
  linarith only [hX, e2, e3, e4, e5, show 16 / 7 * Lsq * ((8 * ℓ2 / 49 + 16 * ℓ2 / 147) *
      (cmuv * g) * ε) = 16 / 7 * Lsq * (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * cmuv * ε * g by ring,
    show (16 / 7 * Lsq * (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * cmuv * ε + 3 * Lsq * cZv +
      8 * ℓ2 / 49 + Lsq * (16 * ℓ2 / 147)) * g = 16 / 7 * Lsq * (8 * ℓ2 / 49 + 16 * ℓ2 / 147) *
      cmuv * ε * g + 3 * Lsq * (cZv * g) + 8 * ℓ2 / 49 * g + Lsq * (16 * ℓ2 / 147 * g) by ring]

set_option maxHeartbeats 4000000 in
/-- **The sharpened step-`(N-2)` mass bound**: the `ν` conclusion of `glue_core` with the sharp
constant `cNuLs` (the `c_μ`-term carries a factor `ε`). -/
theorem glue_nu_sharp {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    {j : ℕ} (hVL : ValidAtL R j) {st : RawSt 2 L N} (HI : RawInv R j st)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ κ cg cm cT ε : ℝ} (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    {g μ : ℝ} (x : Xs R j) (hg : 0 < g) (hgε : g ≤ ε) (hμ : |μ| ≤ cmu Λ cm * g)
    (hx : ‖x‖ ≤ cx κ cT * g ^ 3)
    (hz : ‖st.z / st.Z‖ ≤ cZ R * g) (hy : ‖st.y / st.Z‖ ≤ cZ R * g)
    (hWl : Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2)) :
    ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).nu - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
      cNuLs R Λ cm ε * g := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hε0 : 0 ≤ ε := H.hε.le
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcr : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg2 : g ^ 2 ≤ ε * g := by nlinarith
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hg3' : g ^ 3 ≤ ε * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤
      cR R Λ cm C₂ * g := by
    refine hv.trans ?_; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ (cR R Λ cm C₂ * g) ^ 2 := by
    unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hrε : cR R Λ cm C₂ * g ≤ εs :=
    (mul_le_mul_of_nonneg_left hgε hcr).trans H.h4
  have hk3 : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
    have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
    exact mul_le_mul_of_nonneg_left this H.hcx
  have hkε : 8 * ‖x.2‖ ≤ εs := by linarith [H.h5]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g := by
    have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
  have hk : ‖x.2‖ ≤ cx κ cT * (ε * g) := hx2.trans (mul_le_mul_of_nonneg_left hg3' H.hcx)
  obtain ⟨-, -, c3, -, -, -⟩ := hSB N R j hVL st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) hm hg.le (cZ R * g) hz hy hη hηs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ (cR R Λ cm C₂ * g) (by positivity) (norm_nonneg _)
    (norm_nonneg _) hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x))
    hvr hwr hrε hkε
  have hE := rem_bound_cE R H.hCq H.hCl (le_trans zero_le_one H.hcS) H.hcx hg.le hε0 hk hv0 hvr
    hwr hg2
  have hE' : cE R Λ κ cm cT C₂ Cq Cl cS * ε * R.ℓ ^ 2 * g ≤ 16 * R.ℓ ^ 2 / 147 * R.ℓ ^ 2 * g := by
    have := mul_le_mul_of_nonneg_right H.h7 (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 * g)
    linarith only [this]
  have hEd : (2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) + Cq * (Cl * ((L : ℝ) ^ 2 *
      BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g)
        (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖)))) / R.ℓ ^ 2 ≤ 16 * R.ℓ ^ 2 / 147 * g := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hE, hE', show 16 * R.ℓ ^ 2 / 147 * g * R.ℓ ^ 2 =
      16 * R.ℓ ^ 2 / 147 * R.ℓ ^ 2 * g by ring]
  have hL2 : (2 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := hVL.1; omega)
    exact this.trans (le_self_pow₀ (by linarith only [this]) (by norm_num))
  have hRQ0 : 0 ≤ Cq * (cS * (Cl * (8 * ‖x.2‖))) := by
    have := H.hCq; have := H.hCl; have : (0 : ℝ) ≤ cS := le_trans zero_le_one H.hcS
    positivity
  have hRL0 : 0 ≤ Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L
      (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g)
        (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖))) := by
    have := BH.sig_nonneg (L := L) (d := 2) (by norm_num)
      (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g)
      (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖) (by positivity)
    have := H.hCq; have := H.hCl
    positivity
  exact nu_alg_sharp c3 hEd hRQ0 hRL0 hL2 (by positivity) hg.le hgε (abs_nonneg μ) hμ

set_option maxHeartbeats 4000000 in
/-- **The sharpened mass bound along a regular history at `j = N_h`** (`ValidAtL` at `N_h`):
`|ν_{N_h+1} - L² μ_{N_h}| ≤ cNuLs ǧ_{N_h}`. -/
theorem glue_step_nu_sharp {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j ≤ Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    ‖(histOut R Nh t).nu - (L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)‖ ≤ cNuLs R Λ cm ε * (t Nh).1 := by
  have hSB' := hSB.toStepBounds hVL.1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB' hV (fun j hj => hm j hj.le) hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 Nh le_rfl
  have HI := rawInv_hist R hVL.2.2.2.2.1 Nh hV t
  exact glue_nu_sharp R hSB hVL HI (hm Nh le_rfl) H (t Nh).2.2 hg hgε hμ hx hz hy hWl

end

end Step2
