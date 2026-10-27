import Step2.Flow.ZetaSharp1

/-!
# The sharp gradient coupling along regular histories (`e:zflow`)

`zeta_sharp_hist` (a copy of `zeta_hist` with the difference form `ZetaStepBound2`): along regular
histories, for `j < N_h`,

  `‖ζ_{j+1} + ǧ_{r,j} Z_{j+1} C_j(e₁, 0)‖ ≤ 2 c_E ǧ_j²`,

with `c_E = cE R Λ κ cm cT C₂ C_q' C_l' c_S'` (the constant of `zeta_hist`, which there was used
in the form `c_E ε ≤ 1`). Here `ζ_{j+1}` is the coupling absorbed in step `j + 1`, i.e.
`Z_{j+2} = Z_{j+1}(1 + ζ_{j+1})`. No smallness of `c_E ε` is needed.

`stGr_sub_le`: `|ǧ_r - ǧ| ≤ (32/7) |μ| ℓ² ǧ` (the coordinate change `ǧ_r = ǧ/(1 + n)`,
`n = 4 ν w⁽¹⁾`, `|Z_{j+1} w⁽¹⁾_j| ≤ ℓ² L^{2j}`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
theorem zeta_sharp_hist {C₀ η εs CK C₂ CD Cq Cl cS Cq' Cl' cS' : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hZB : ZetaStepBound2 L R.A Cq' Cl' cS')
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hCq' : 0 ≤ Cq') (hCl' : 0 ≤ Cl') (hcS' : 1 ≤ cS') (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1) :
    ∀ j < Nh, ∀ t : Flow2.Hist.Seq (Xs R), Flow2.Hist.InDh Λ β δ κ cg cm cT ε (j + 1) t →
      ‖stZeta R (rawHist R (j + 1) t) + stGr R j (rawHist R j t) (t j).1 (t j).2.1 *
          (stZ' R (rawHist R j t) * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0)‖ ≤
        2 * cE R Λ κ cm cT C₂ Cq' Cl' cS' * (t j).1 ^ 2 := by
  have hℓ : 0 < R.ℓ := Fact.out
  intro j hj t ht
  have hj' : j + 1 ≤ Nh := hj
  have htj := InDh_mono ht
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j (by omega) t htj
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j (by omega)
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hVj := hV j (by omega)
  have hρ0 : 0 ≤ R.ρ := hVj.2.2.2.1
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  -- the radius
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
  have hcr : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    have hdd : ‖x.1‖ ≤ g ^ 2 := by
      have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hr1' : r ≤ 1 := by
    rw [hr]
    calc cR R Λ cm C₂ * g ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε hcr
      _ ≤ 1 := hr1
  have hk8 : 8 * ‖x.2‖ ≤ 1 := by
    have : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
      have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
      exact mul_le_mul_of_nonneg_left this H.hcx
    linarith
  have hzη : ‖st.z / st.Z‖ ≤ cZ R * g := hz
  have hyη : ‖st.y / st.Z‖ ≤ cZ R * g := hy
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hc := hZB N R j hVj st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) (hm j (by omega)) hg.le (cZ R * g) hzη hyη hη hηs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r (by positivity) (norm_nonneg _) (norm_nonneg _) hWl
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1' hk8
  -- the remainder
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g
  have hv0 : 0 ≤ v := by have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
  have hE : (2 * Cq' * (cS' * (Cl' * (8 * ‖x.2‖))) +
      Cq' * (Cl' * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖)))) / R.ℓ ^ 2 ≤
      cE R Λ κ cm cT C₂ Cq' Cl' cS' * g ^ 2 := by
    have hs : BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖) ≤
        (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * g ^ 2 := by
      unfold BH.sig
      have h1 : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv0 hvr 2
      rw [hr] at h1 hwr
      have h2 : (cR R Λ cm C₂ * g) ^ 2 = cR R Λ cm C₂ ^ 2 * g ^ 2 := by ring
      rw [h2] at h1 hwr
      nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hN0 (sq_nonneg (Q1 2))),
        mul_le_mul_of_nonneg_left hwr (by linarith : (0 : ℝ) ≤ Q1 2)]
    have hg32 : g ^ 3 ≤ g ^ 2 := by
      rw [pow_succ]; exact mul_le_of_le_one_right (sq_nonneg g) hg1
    have hk : ‖x.2‖ ≤ cx κ cT * g ^ 2 := hx2.trans (mul_le_mul_of_nonneg_left hg32 H.hcx)
    have t1 : 2 * Cq' * (cS' * (Cl' * (8 * ‖x.2‖))) ≤ 16 * Cq' * cS' * Cl' * cx κ cT * g ^ 2 := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 16 * Cq' * cS' * Cl')
      linarith only [this]
    have t2 : Cq' * (Cl' * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖))) ≤
        Cq' * Cl' * (L : ℝ) ^ 2 * ((cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * g ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hs
        (by positivity : (0 : ℝ) ≤ Cq' * Cl' * (L : ℝ) ^ 2)
      linarith only [h1]
    unfold cE
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have e : (16 * Cq' * cS' * Cl' * cx κ cT + Cq' * Cl' * (L : ℝ) ^ 2 *
        (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2) * g ^ 2 =
        16 * Cq' * cS' * Cl' * cx κ cT * g ^ 2 + Cq' * Cl' * (L : ℝ) ^ 2 *
          ((cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * g ^ 2) := by ring
    linarith only [t1, t2, e]
  -- `ζ_{j+1}`: the clamp is inactive by the a priori bound at `j + 1`
  obtain ⟨hz1, hy1, -⟩ := apriori R hSB hV hm hβ hδ1 H (j + 1) hj' t ht
  have hg1ε := (ht.1 (j + 1) le_rfl).2.1
  have hcz0 : 0 ≤ cZ R := by unfold cZ; positivity
  have hcl : ‖((rawHist R (j + 1) t).z + (rawHist R (j + 1) t).y) / (rawHist R (j + 1) t).Z‖ ≤
      R.ρ := by
    rw [add_div]
    refine (norm_add_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hg1ε hcz0
    linarith only [hz1, hy1, this, H.h1]
  have hζeq : stZeta R (rawHist R (j + 1) t) =
      (stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 0 +
        stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 1) / stZ' R st := by
    show absorbZeta R (rawHist R (j + 1) t).Z
      ((rawHist R (j + 1) t).z + (rawHist R (j + 1) t).y) = _
    unfold absorbZeta
    rw [clampDisk_of_le hcl]
    rfl
  rw [hζeq]
  refine hc.trans ?_
  linarith only [hE]


/-- `|ǧ_r - ǧ| ≤ (32/7)|μ|ℓ² ǧ` if `|Z_{j+1} w⁽¹⁾| ≤ ℓ² L^{2j}`. -/
theorem stGr_sub_le (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) {g μ : ℝ} (hg : 0 ≤ g)
    (hw : ‖stZ' R st * st.w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2) :
    ‖stGr R j st g μ - g‖ ≤ 32 / 7 * |μ| * R.ℓ ^ 2 * g := by
  have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set n := nCor (stNu R j st μ) st.w1 with hn
  have h1n : 7 / 8 ≤ ‖1 + n‖ := by
    have := norm_nCor_le (stNu R j st μ) st.w1
    have h := norm_sub_norm_le (1 : ℂ) (-n)
    rw [sub_neg_eq_add, norm_one, norm_neg] at h
    linarith only [this, h]
  have h1n0 : (1 + n) ≠ 0 := by
    intro h; rw [h, norm_zero] at h1n; norm_num at h1n
  have hnb : ‖n‖ ≤ 4 * |μ| * R.ℓ ^ 2 := by
    rw [hn]; unfold nCor
    refine (norm_clampDisk_le_self (by norm_num) _).trans ?_
    have e : 4 * stNu R j st μ * st.w1 =
        4 * (μ : ℂ) * (stZ' R st * st.w1) / (L : ℂ) ^ (2 * j) := by
      unfold stNu; ring
    rw [e, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
    rw [div_le_iff₀ (by positivity)]
    have : ((L : ℝ) ^ (2 * j)) = ((L : ℝ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [this]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 4 * |μ|)
    linarith only [this]
  have e : stGr R j st g μ - g = -((g : ℂ) * n / (1 + n)) := by
    unfold stGr; rw [← hn]; field_simp; ring
  rw [e, norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg,
    div_le_iff₀ (by linarith only [h1n])]
  have h0 : 0 ≤ g * ‖n‖ := by positivity
  have := mul_le_mul_of_nonneg_left hnb hg
  have h2 : 32 / 7 * |μ| * R.ℓ ^ 2 * g * (7 / 8) ≤ 32 / 7 * |μ| * R.ℓ ^ 2 * g * ‖1 + n‖ :=
    mul_le_mul_of_nonneg_left h1n (by positivity)
  linarith only [this, h2]

end

end Step2
