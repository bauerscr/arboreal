import Step2.Lip.FlowZetaStep
import Step2.Lip.FlowZetaCov

/-!
# The sharp a priori bound on the dressed coupling `ζ_j`

`apriori` gives `|ζ_j| ≤ 2 c_z ǧ_j` with `c_z = 16ℓ²/49`, which is of order `L⁸` for the
admissible field scale `ℓ`. The leading part of `ζ_{j+1}` is `-ǧ_r Z_{j+1} C_j(e, 0)`
(`step_zeta_sharp`), and `|Z_{j+1} C_j(e, 0)| ≤ K_z` with `K_z = C₄ L² + 1` independent of `ℓ`
(`Zcov_hist`). Hence (`zeta_hist`)

  `|ζ_j| ≤ c_ζ ǧ_j`,   `c_ζ = (6/5)((8/7) K_z + 2)`,

once the remainders are `≤ ǧ` (a smallness condition on `ε`).

* `ZetaStepBound`, `zeta_step_bounds`: the one-step form of `step_zeta_sharp` with the inputs of
  `StepBounds`.
* `zeta_hist`: the bound along regular histories.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- **The sharp one-step bound on the absorbed gradient coupling**, with the inputs of
`StepBounds`. -/
def ZetaStepBound (L : ℕ) [NeZero L] (A Cq Cl cS : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
      ∀ η : ℝ, ‖st.z / st.Z‖ ≤ η → ‖st.y / st.Z‖ ≤ η → 2 * η ≤ R.ρ →
        8 * cM * R.ℓ ^ 2 * η ≤ 1 / 2 →
      ∀ wl dd k r : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 → r ≤ 1 →
      8 * k ≤ 1 →
      ‖(stCv R j st g μ D K 0 + stCv R j st g μ D K 1) / stZ' R st‖ ≤
        ‖stGr R j st g μ‖ * ‖stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0‖ +
          2 * ((2 * Cq * (cS * (Cl * (8 * k))) + Cq * (Cl * ((L : ℝ) ^ 2 *
            BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd)))) /
              R.ℓ ^ 2)

set_option maxHeartbeats 4000000 in
/-- **The sharp bound on `ζ_j` along regular histories.** -/
theorem zeta_hist {C₀ η εs CK C₂ CD Cq Cl cS Cq' Cl' cS' : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hZB : ZetaStepBound L R.A Cq' Cl' cS')
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hCq' : 0 ≤ Cq') (hCl' : 0 ≤ Cl') (hcS' : 1 ≤ cS')
    (hcE : cE R Λ κ cm cT C₂ Cq' Cl' cS' * ε ≤ 1) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1) {Kz : ℝ} (hKz : 0 ≤ Kz)
    (hcov : ∀ j < Nh, ∀ t : Flow2.Hist.Seq (Xs R), Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t →
      ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0‖ ≤ Kz) :
    ∀ j ≤ Nh, ∀ t : Flow2.Hist.Seq (Xs R), Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t →
      ‖stZeta R (rawHist R j t)‖ ≤ 6 / 5 * (8 / 7 * Kz + 2) * (t j).1 := by
  have hℓ : 0 < R.ℓ := Fact.out
  intro j hj t ht
  cases j with
  | zero =>
    have hg0 := (ht.1 0 le_rfl).1
    show ‖absorbZeta R (rawHist R 0 t).Z ((rawHist R 0 t).z + (rawHist R 0 t).y)‖ ≤ _
    unfold absorbZeta
    have e : (rawHist R 0 t).z + (rawHist R 0 t).y = 0 := by simp [rawHist]
    have e2 : clampDisk R.ρ (0 : ℂ) = 0 := by unfold clampDisk; simp
    rw [e, zero_div, e2, norm_zero]
    positivity
  | succ j =>
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
    have hgs := g_succ_ge ht hβ hδ1 H.hcg H.hε1 H.h6
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
    have hg2 : g ^ 2 ≤ ε * g := by nlinarith
    have hg3' : g ^ 3 ≤ ε * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
    have hE : (2 * Cq' * (cS' * (Cl' * (8 * ‖x.2‖))) +
        Cq' * (Cl' * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖)))) / R.ℓ ^ 2 ≤
        g := by
      have hs : BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖) ≤
          (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * g ^ 2 := by
        unfold BH.sig
        have h1 : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv0 hvr 2
        rw [hr] at h1 hwr
        have h2 : (cR R Λ cm C₂ * g) ^ 2 = cR R Λ cm C₂ ^ 2 * g ^ 2 := by ring
        rw [h2] at h1 hwr
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hN0 (sq_nonneg (Q1 2))),
          mul_le_mul_of_nonneg_left hwr (by linarith : (0 : ℝ) ≤ Q1 2)]
      have hk : ‖x.2‖ ≤ cx κ cT * (ε * g) := hx2.trans (mul_le_mul_of_nonneg_left hg3' H.hcx)
      have hcE' := hcE
      unfold cE at hcE'
      rw [div_le_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hcE'
      have t1 : 2 * Cq' * (cS' * (Cl' * (8 * ‖x.2‖))) ≤ 16 * Cq' * cS' * Cl' * cx κ cT * (ε * g) := by
        have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 16 * Cq' * cS' * Cl')
        nlinarith
      have t2 : Cq' * (Cl' * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖))) ≤
          Cq' * Cl' * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * (ε * g) := by
        have h1 := mul_le_mul_of_nonneg_left hs
          (by positivity : (0 : ℝ) ≤ Cq' * Cl' * (L : ℝ) ^ 2)
        have h2 : (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * g ^ 2 ≤
            (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * (ε * g) :=
          mul_le_mul_of_nonneg_left hg2 (by positivity)
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Cq' * Cl' * (L : ℝ) ^ 2)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcE' hg.le]
    -- `ζ_{j+1}`
    have hgr : ‖stGr R j st g μ‖ ≤ 8 / 7 * g := by
      have := norm_stGr_le R j st g μ; rwa [abs_of_pos hg] at this
    have hC := hcov j (by omega) t htj
    show ‖absorbZeta R (stZ' R st) (stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 0 +
      stCv R j st g μ (rawD R st.u x) (rawK R st.u x) 1)‖ ≤ _
    unfold absorbZeta
    refine (norm_clampDisk_le_self hρ0 _).trans (hc.trans ?_)
    have a1 : ‖stGr R j st g μ‖ * ‖stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0‖ ≤
        8 / 7 * g * Kz := mul_le_mul hgr hC (norm_nonneg _) (by positivity)
    have a2 : (8 / 7 * Kz + 2) * g ≤ 6 / 5 * (8 / 7 * Kz + 2) * (t (j + 1)).1 := by
      have := mul_le_mul_of_nonneg_left hgs (by positivity : (0 : ℝ) ≤ 8 / 7 * Kz + 2)
      nlinarith
    linarith only [a1, a2, hE]

end

end Step2
