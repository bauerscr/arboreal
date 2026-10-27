import Step2.Flow.FlowRG

/-!
# A priori bounds along regular histories, and (F3), (F2) for the RG map (`d = 2`)

Along a regular history in `D_ε` (`Flow2.Hist.InDh`), the raw state at scale `j` satisfies
`|z_j/Z_j|, |y_j/Z_j| ≤ C_z g_j` and `‖W^lin_j‖ ≤ C_w g_j²` at the causal field scale
(`apriori`). Hence the step bounds (`StepBounds`) apply with radius `O(g_j)`, which gives
`RGBound` (`rgBound_rg`) and (F2) (`F2_rg`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

section Norms

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem Fnorm_rawD {Z u : ℂ} (hu : u ^ 2 = Z) (hZ : Z ≠ 0) {j : ℕ} (x : Xs R j) :
    Fnorm j (fscale Z * R.ℓ) (rawD R u x) = ENNReal.ofReal ‖x.1‖ := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hs := fscale_pos hZ
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hu; exact hZ hu.symm
  rw [rawD, Fnorm_sigF_cscale (mul_pos hs hℓ) hu0, norm_eq_inv_fscale hu, ← mul_assoc,
    inv_mul_cancel₀ hs.ne', one_mul, BSp.Fnorm_le]

theorem Knorm_rawK {Z u : ℂ} (hu : u ^ 2 = Z) (hZ : Z ≠ 0) {j : ℕ} (x : Xs R j) :
    Knorm j (fscale Z * R.ℓ) R.A (rawK R u x) = ENNReal.ofReal ‖x.2‖ := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hs := fscale_pos hZ
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hu; exact hZ hu.symm
  rw [rawK, Knorm_sigK_cscale (mul_pos hs hℓ) hu0, norm_eq_inv_fscale hu, ← mul_assoc,
    inv_mul_cancel₀ hs.ne', one_mul, ASp.Knorm_eq]

theorem Tmap_norm_fst {j : ℕ} (h : ∀ i ≤ j, ValidAt R i) (t : Flow2.Hist.Seq (Xs R)) :
    ‖(Tmap R j t).1‖ =
      (Fnorm (j + 1) (fscale (histOut R j t).st.Z * R.ℓ) (histOut R j t).D).toReal := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [(h 0 (Nat.zero_le _)).2.2.2.2.1]
  have HI := rawInv_hist R (h 0 (Nat.zero_le _)).2.2.2.1 (j + 1) (fun i hi => h i (by omega)) t
  have hZ := HI.Z_ne_zero hρ1
  have hu := HI.hu
  rw [rawHist_succ] at hZ hu
  have hu0 : (histOut R j t).st.u ≠ 0 := by
    rintro h0; rw [h0, zero_pow two_ne_zero] at hu; exact hZ hu.symm
  simp only [Tmap, dif_pos h]
  rw [BSp.norm_def]
  show (Fnorm (j + 1) R.ℓ (sigF (histOut R j t).st.u⁻¹ (histOut R j t).D)).toReal = _
  rw [Fnorm_sigF_cscale hℓ (inv_ne_zero hu0), norm_inv, norm_eq_inv_fscale hu, inv_inv]

theorem Tmap_norm_snd {j : ℕ} (h : ∀ i ≤ j, ValidAt R i) (t : Flow2.Hist.Seq (Xs R)) :
    ‖(Tmap R j t).2‖ =
      (Knorm (j + 1) (fscale (histOut R j t).st.Z * R.ℓ) R.A (histOut R j t).K).toReal := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [(h 0 (Nat.zero_le _)).2.2.2.2.1]
  have HI := rawInv_hist R (h 0 (Nat.zero_le _)).2.2.2.1 (j + 1) (fun i hi => h i (by omega)) t
  have hZ := HI.Z_ne_zero hρ1
  have hu := HI.hu
  rw [rawHist_succ] at hZ hu
  have hu0 : (histOut R j t).st.u ≠ 0 := by
    rintro h0; rw [h0, zero_pow two_ne_zero] at hu; exact hZ hu.symm
  simp only [Tmap, dif_pos h]
  rw [ASp.norm_def]
  show (Knorm (j + 1) R.ℓ R.A (sigK (histOut R j t).st.u⁻¹ (histOut R j t).K)).toReal = _
  rw [Knorm_sigK_cscale hℓ (inv_ne_zero hu0), norm_inv, norm_eq_inv_fscale hu, inv_inv]

end Norms

/-! ### The a priori bounds -/

/-- The a priori bounds on the raw state at scale `j` in terms of `g_j`. -/
def APB (R : RGPar 2 L N) (Cz Cw g : ℝ) (st : RawSt 2 L N) (j : ℕ) : Prop :=
  ‖st.z / st.Z‖ ≤ Cz * g ∧ ‖st.y / st.Z‖ ≤ Cz * g ∧
    Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (Cw * g ^ 2)

section Apriori

variable {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- The constants of the a priori bounds. -/
def cZ (R : RGPar 2 L N) : ℝ := 16 * R.ℓ ^ 2 / 49
def cV (R : RGPar 2 L N) (Λ cm : ℝ) : ℝ := cM * R.ℓ ^ 2 * (2 * cmu Λ cm + 2 * cZ R) + 8 * R.ℓ ^ 4
def cW (R : RGPar 2 L N) (Λ cm C₂ : ℝ) : ℝ := 3 * C₂ * cV R Λ cm ^ 2 + 1
def cR (R : RGPar 2 L N) (Λ cm C₂ : ℝ) : ℝ := cV R Λ cm + cW R Λ cm C₂ + 2
def cE (R : RGPar 2 L N) (Λ κ cm cT C₂ Cq Cl cS : ℝ) : ℝ :=
  (16 * Cq * cS * Cl * cx κ cT + Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
    cR R Λ cm C₂ ^ 2) / R.ℓ ^ 2

/-- The smallness conditions on `ε`. -/
structure ApHyp (R : RGPar 2 L N) (Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS : ℝ) : Prop where
  hε : 0 < ε
  hε1 : ε ≤ 1
  hcm : 0 ≤ cm
  hcmu : 0 ≤ cmu Λ cm
  hcx : 0 ≤ cx κ cT
  hcg : 0 ≤ cg
  hC₀ : C₀ / L ≤ 1 / 4
  hC₂ : 0 ≤ C₂
  hCq : 0 ≤ Cq
  hCl : 0 ≤ Cl
  hcS : 1 ≤ cS
  h1 : 2 * cZ R * ε ≤ R.ρ
  h2 : 8 * cM * R.ℓ ^ 2 * cZ R * ε ≤ 1 / 2
  h3 : cx κ cT * ε ≤ 1
  h4 : cR R Λ cm C₂ * ε ≤ εs
  h5 : 8 * cx κ cT * ε ≤ εs
  h6 : cg * ε ≤ 1 / 6
  h7 : cE R Λ κ cm cT C₂ Cq Cl cS * ε ≤ 16 * R.ℓ ^ 2 / 147

end Apriori

section Apriori2

variable {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

theorem InDh_mono {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {j : ℕ} {t : Flow2.Hist.Seq X}
    (h : Flow2.Hist.InDh Λ β δ κ cg cm cT ε (j + 1) t) : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t :=
  ⟨fun i hi => h.1 i (by omega), fun i hi => h.2 i (by omega)⟩

/-- `g_{j+1} ≥ (5/6) g_j` along a regular history. -/
theorem g_succ_ge {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {j : ℕ} {t : Flow2.Hist.Seq X}
    (h : Flow2.Hist.InDh Λ β δ κ cg cm cT ε (j + 1) t) (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (hcg : 0 ≤ cg) (hε1 : ε ≤ 1) (h6 : cg * ε ≤ 1 / 6) : 5 / 6 * (t j).1 ≤ (t (j + 1)).1 := by
  have hr := abs_le.1 (h.2 j (Nat.lt_succ_self j))
  obtain ⟨hg, hgε, -, -⟩ := h.1 j (by omega)
  set g := (t j).1
  have hg1 : g ≤ 1 := hgε.trans hε1
  have h3 : cg * g ^ 3 ≤ 1 / 6 * g := by
    have : g ^ 3 ≤ ε * g := by nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hg1 hg.le]
    nlinarith
  have hb : 0 ≤ β * g ^ 2 * (1 - δ) := mul_nonneg (by positivity) (by linarith)
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The a priori bounds along regular histories.** -/
theorem apriori (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS) :
    ∀ j ≤ Nh, ∀ t : Flow2.Hist.Seq (Xs R), Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t →
      APB R (cZ R) (cW R Λ cm C₂) (t j).1 (rawHist R j t) j := by
  have hℓ : 0 < R.ℓ := Fact.out
  intro j
  induction j with
  | zero =>
    intro _ t ht0
    have hg0 : 0 ≤ cZ R * (t 0).1 :=
      mul_nonneg (by unfold cZ; positivity) (ht0.1 0 le_rfl).1.le
    refine ⟨by simpa [rawHist] using hg0, by simpa [rawHist] using hg0, ?_⟩
    have : (rawHist R 0 t).Wl = 0 := rfl
    rw [this]
    refine le_trans (le_of_eq ?_) zero_le
    unfold Fnorm; simp [Step.Tj_zero]
  | succ j ih =>
    intro hj t ht
    have htj := InDh_mono ht
    obtain ⟨hz, hy, hWl⟩ := ih (by omega) t htj
    obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j (by omega)
    set g := (t j).1 with hgdef
    set μ := (t j).2.1
    set x := (t j).2.2
    have hVj := hV j (by omega)
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
    have hrε : r ≤ εs := by
      rw [hr]; have := H.h4
      calc cR R Λ cm C₂ * g ≤ cR R Λ cm C₂ * ε := by
            gcongr; unfold cR; positivity
        _ ≤ εs := this
    have hkε : 8 * ‖x.2‖ ≤ εs := by
      have : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
        have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
        exact mul_le_mul_of_nonneg_left this H.hcx
      linarith [H.h5]
    -- apply the step bounds
    have hzη : ‖st.z / st.Z‖ ≤ cZ R * g := hz
    have hyη : ‖st.y / st.Z‖ ≤ cZ R * g := hy
    have hη : 2 * (cZ R * g) ≤ R.ρ := by
      have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
    have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
      have := H.h2
      have hM : 0 ≤ cM := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
        (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
    obtain ⟨c1, c2, -, cw, -, -⟩ := hSB N R j hVj st HI g μ (rawD R st.u x) (rawK R st.u x)
      (rawD_mem R _ _) (rawK_mem R _ _) (hm j (by omega)) hg.le (cZ R * g) hzη hyη hη hηs
      (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r (by positivity) (norm_nonneg _) (norm_nonneg _) hWl
      (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hrε hkε
    -- the error term
    set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g
    have hv0 : 0 ≤ v := by have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
    have hcr : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
    have hg2 : g ^ 2 ≤ ε * g := by nlinarith
    have hg3' : g ^ 3 ≤ ε * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
    have hE : (2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) +
        Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖)))) / R.ℓ ^ 2 ≤
        16 * R.ℓ ^ 2 / 147 * g := by
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
      have hcE := H.h7
      unfold cE at hcE
      rw [div_le_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hcE
      have hCq := H.hCq; have hCl := H.hCl; have hcS := H.hcS
      have t1 : 2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) ≤ 16 * Cq * cS * Cl * cx κ cT * (ε * g) := by
        have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 16 * Cq * cS * Cl)
        nlinarith
      have t2 : Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖))) ≤
          Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * (ε * g) := by
        have h1 := mul_le_mul_of_nonneg_left hs
          (by positivity : (0 : ℝ) ≤ Cq * Cl * (L : ℝ) ^ 2)
        have h2 : (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * g ^ 2 ≤
            (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R Λ cm C₂ ^ 2 * (ε * g) :=
          mul_le_mul_of_nonneg_left hg2 (by positivity)
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Cq * Cl * (L : ℝ) ^ 2)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcE hg.le]
    have hcz5 : 8 * R.ℓ ^ 2 / 49 * g + 16 * R.ℓ ^ 2 / 147 * g ≤ cZ R * (t (j + 1)).1 := by
      unfold cZ
      have := mul_le_mul_of_nonneg_left hgs (by positivity : (0 : ℝ) ≤ 16 * R.ℓ ^ 2 / 49)
      nlinarith
    refine ⟨(c1.trans (by linarith)).trans hcz5, (c2.trans (by linarith)).trans hcz5, ?_⟩
    -- `W^lin`
    refine cw.trans (ENNReal.ofReal_le_ofReal ?_)
    have hv' : v ^ 2 ≤ (cV R Λ cm * g) ^ 2 := pow_le_pow_left₀ hv0 hv 2
    have hgs2 : (5 / 6 * g) ^ 2 ≤ (t (j + 1)).1 ^ 2 := pow_le_pow_left₀ (by positivity) hgs 2
    have hC₀ := H.hC₀
    have hcwdef : cW R Λ cm C₂ = 3 * C₂ * cV R Λ cm ^ 2 + 1 := rfl
    have hC₂ := H.hC₂
    have hwl0 : 0 ≤ cW R Λ cm C₂ * g ^ 2 := by positivity
    have : C₀ / L * (cW R Λ cm C₂ * g ^ 2) ≤ 1 / 4 * (cW R Λ cm C₂ * g ^ 2) :=
      mul_le_mul_of_nonneg_right hC₀ hwl0
    have h2 : C₂ * v ^ 2 ≤ C₂ * cV R Λ cm ^ 2 * g ^ 2 := by
      have := mul_le_mul_of_nonneg_left hv' hC₂; nlinarith
    have h3 := mul_le_mul_of_nonneg_left hgs2 hcw
    nlinarith [sq_nonneg g]

end Apriori2

section Bounds

variable {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {β δ κ₁ cg cm cT ε : ℝ}

/-- The contraction factor of the irrelevant coordinates. -/
def kap1 (L : ℕ) (A C₀ η : ℝ) : ℝ := 8 * C₀ * ((L : ℝ)⁻¹ + (A / 2) ^ (-η))

/-- The constant of `RGBound`. -/
def cB (R : RGPar 2 L N) (Λ cm C₂ CK CD : ℝ) : ℝ :=
  max (CD * (cV R Λ cm ^ 2 + cW R Λ cm C₂ + 1) ^ 2)
    (CK * (cR R Λ cm C₂ ^ 3 + 8 * cR R Λ cm C₂ + 64))

set_option maxHeartbeats 4000000 in
/-- **(Kb), (Yb) for the RG map**: `RGBound`. -/
theorem rgBound_rg (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (hκ₁ : κ₁ = kap1 L R.A C₀ η) (hC₀ : 0 ≤ C₀) (hCK : 0 ≤ CK)
    (hCD : 0 ≤ CD)
    (H : ApHyp R ((L : ℝ) ^ 2) ((1 + κ₁) / 2) cg cm cT ε εs C₀ C₂ Cq Cl cS) :
    Flow2.Hist.RGBound (rgData R) ((L : ℝ) ^ 2) β δ κ₁ (cB R ((L : ℝ) ^ 2) cm C₂ CK CD) cg cm cT
      ε Nh := by
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
  have hx1 : ‖x.1‖ ≤ cx ((1 + κ₁) / 2) cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx ((1 + κ₁) / 2) cT * g ^ 3 := (norm_snd_le x).trans hx
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
    have h1 : cW R ((L : ℝ) ^ 2) cm C₂ + 1 ≤ (cV R ((L : ℝ) ^ 2) cm + cW R ((L : ℝ) ^ 2) cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hrε : r ≤ εs := by
    rw [hr]; have := H.h4
    calc cR R ((L : ℝ) ^ 2) cm C₂ * g ≤ cR R ((L : ℝ) ^ 2) cm C₂ * ε := by gcongr
      _ ≤ εs := this
  have hkε : 8 * ‖x.2‖ ≤ εs := by
    have : cx ((1 + κ₁) / 2) cT * g ^ 3 ≤ cx ((1 + κ₁) / 2) cT * ε := by
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
  obtain ⟨-, -, -, -, cD, cK⟩ := hSB N R j hVj st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj) hg.le (cZ R * g) hz hy hη hηs
    (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r (by positivity) (norm_nonneg _) (norm_nonneg _)
    hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hrε hkε
  have hval : ∀ i ≤ j, ValidAt R i := fun i hi => hV i (by omega)
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g
  have hv0 : 0 ≤ v := by have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
  have hκ0 : C₀ / L ≤ κ₁ := by
    rw [hκ₁]; unfold kap1
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have : 0 ≤ (R.A / 2) ^ (-η) := by
      have : 0 < R.A := Fact.out
      positivity
    rw [div_eq_mul_inv]; nlinarith [inv_nonneg.2 hL0.le]
  refine ⟨?_, ?_⟩
  · -- `K`
    show ‖(Tmap R j t).2‖ ≤ _
    rw [Tmap_norm_snd R hval t]
    refine (ENNReal.toReal_le_of_le_ofReal (by have hA : 0 < R.A := Fact.out; positivity) cK).trans ?_
    have hk0 : 0 ≤ ‖x.2‖ := norm_nonneg _
    have hcB : CK * (cR R ((L : ℝ) ^ 2) cm C₂ ^ 3 + 8 * cR R ((L : ℝ) ^ 2) cm C₂ + 64) ≤
        cB R ((L : ℝ) ^ 2) cm C₂ CK CD := le_max_right _ _
    have e1 : r ^ 3 + r * (8 * ‖x.2‖) + (8 * ‖x.2‖) ^ 2 ≤
        (cR R ((L : ℝ) ^ 2) cm C₂ ^ 3 + 8 * cR R ((L : ℝ) ^ 2) cm C₂ + 64) *
          (g ^ 3 + g * ‖x.2‖ + ‖x.2‖ ^ 2) := by
      rw [hr]
      set c := cR R ((L : ℝ) ^ 2) cm C₂
      set k := ‖x.2‖
      have e : (c ^ 3 + 8 * c + 64) * (g ^ 3 + g * k + k ^ 2) -
          ((c * g) ^ 3 + c * g * (8 * k) + (8 * k) ^ 2) =
          c ^ 3 * g * k + c ^ 3 * k ^ 2 + 8 * c * g ^ 3 + 8 * c * k ^ 2 + 64 * g ^ 3 +
            64 * g * k := by ring
      have : 0 ≤ c ^ 3 * g * k + c ^ 3 * k ^ 2 + 8 * c * g ^ 3 + 8 * c * k ^ 2 + 64 * g ^ 3 +
          64 * g * k := by positivity
      linarith
    have h2 := mul_le_mul_of_nonneg_left e1 hCK
    have h3 : CK * ((cR R ((L : ℝ) ^ 2) cm C₂ ^ 3 + 8 * cR R ((L : ℝ) ^ 2) cm C₂ + 64) *
        (g ^ 3 + g * ‖x.2‖ + ‖x.2‖ ^ 2)) ≤ cB R ((L : ℝ) ^ 2) cm C₂ CK CD *
        (g ^ 3 + g * ‖x.2‖ + ‖x.2‖ ^ 2) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcB (by positivity)
    have h1 : 8 * C₀ * ((L : ℝ)⁻¹ + (R.A / 2) ^ (-η)) * ‖x.2‖ = κ₁ * ‖x.2‖ := by
      rw [hκ₁]; rfl
    linarith
  · -- `D`
    show ‖(Tmap R j t).1‖ ≤ _
    rw [Tmap_norm_fst R hval t]
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) cD).trans ?_
    have hw : v ^ 2 + (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖) ≤
        (cV R ((L : ℝ) ^ 2) cm ^ 2 + cW R ((L : ℝ) ^ 2) cm C₂ + 1) * g ^ 2 := by
      have := pow_le_pow_left₀ hv0 hv 2
      nlinarith
    have hw2 := pow_le_pow_left₀ (by positivity) hw 2
    have hcB : CD * (cV R ((L : ℝ) ^ 2) cm ^ 2 + cW R ((L : ℝ) ^ 2) cm C₂ + 1) ^ 2 ≤
        cB R ((L : ℝ) ^ 2) cm C₂ CK CD := le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_left hw2 hCD
    have h2 : CD * ((cV R ((L : ℝ) ^ 2) cm ^ 2 + cW R ((L : ℝ) ^ 2) cm C₂ + 1) * g ^ 2) ^ 2 ≤
        cB R ((L : ℝ) ^ 2) cm C₂ CK CD * g ^ 4 := by
      rw [mul_pow, ← pow_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hcB (by positivity)
    have h3 := mul_le_mul_of_nonneg_right hκ0 (norm_nonneg x.1)
    linarith

end Bounds

section F2

variable {C₀ η εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {β δ κ cg cm cT ε : ℝ}

/-- The leading constant of (F2): `3 L² C_z + 8ℓ²/49`. -/
def cF2 (R : RGPar 2 L N) : ℝ := 3 * (L : ℝ) ^ 2 * cZ R + 8 * R.ℓ ^ 2 / 49

set_option maxHeartbeats 4000000 in
/-- **(F2) for the RG map**: `|m_j| ≤ c_m g_j`. -/
theorem F2_rg (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hF2 : cF2 R + (16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 +
      (L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS) * cmu ((L : ℝ) ^ 2) cm +
      2 * ((L : ℝ) ^ 2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq Cl cS)) * ε ≤ cm) :
    ∀ j < Nh, ∀ t, Flow2.Hist.InDh ((L : ℝ) ^ 2) β δ κ cg cm cT ε j t →
      |(rgData R).m j t| ≤ cm * (t j).1 := by
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
  have hmre : |(rgData R).m j t| ≤ ‖(histOut R j t).nu - (L : ℂ) ^ 2 * (μ : ℂ)‖ := by
    show |(histOut R j t).nu.re - (L : ℝ) ^ 2 * μ| ≤ _
    have : (histOut R j t).nu.re - (L : ℝ) ^ 2 * μ =
        ((histOut R j t).nu - (L : ℂ) ^ 2 * (μ : ℂ)).re := by
      rw [Complex.sub_re, show (L : ℂ) ^ 2 * (μ : ℂ) = (((L : ℝ) ^ 2 * μ : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [this]; exact Complex.abs_re_le_norm _
  refine hmre.trans (cν.trans ?_)
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

end F2

end

end Step2
