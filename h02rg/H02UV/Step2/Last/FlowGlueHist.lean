import Step2.Last.FlowGlueLast
import Step2.Flow.FlowBase
import Step2.Flow.FlowSharp1

/-!
# The steps `j = N - 2` and `j = N - 1` along a regular history

`lastOut R N_h t`: the final-scale object (`LastOut`) obtained by applying the last step
`rawStepN` at `j = N_h + 1` to the output of the step `N_h` along the history `t`, with the flow
coordinates `ǧ_{N_h+1} = Re ǧ'`, `μ_{N_h+1} = Re ν'` (as in `rgData`: `G_{N_h} = Re ǧ'`,
`L² μ_{N_h} + m_{N_h} = Re ν'`) and the raw `D_{N_h+1}`, `K_{N_h+1}` (the map `T_{N_h}` of
`rgData` vanishes at `N_h = N - 2`, since its `dif` requires `ValidAt`).

`GlueOut R N_h C t`: the bounds of both steps in terms of `ǧ = ǧ_{N_h}`. `glue_hist` proves it
for regular histories under `ValidAtL` at `N_h` and `ValidLast` at `N_h + 1`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- **The final-scale object along a history**: the last step `rawStepN` at `j = N_h + 1`
applied to the output of the step `N_h`. -/
def lastOut (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ)
    (t : Hist.Seq (Xs R)) : LastN.LastOut 2 L N :=
  LastN.rawStepN R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (histOut R Nh t).D (histOut R Nh t).K

/-- **The bounds on the last two steps** along the history `t`, in terms of `ǧ = ǧ_{N_h}`:
the output of the step `N_h` (couplings `z, y` of `Z_{N_h+1}`-normalised `V`, `ν_{N_h+1}`,
`ǧ_{N_h+1}`, and `W^lin`, `D`, `K` at scale `N_h + 1` and field scale `s_{N_h+1} ℓ`), and the
final-scale object `lastOut` (final couplings, `u_N(Λ)`, `V_N(B) = V_{κ_N}(B)`, `𝒲_N(B)`,
`K_N(Λ)`, at field scale `s_N ℓ`). -/
def GlueOut (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (C : ℝ)
    (t : Hist.Seq (Xs R)) : Prop :=
  (‖(histOut R Nh t).st.z / (histOut R Nh t).st.Z‖ ≤ C * (t Nh).1 ∧
    ‖(histOut R Nh t).st.y / (histOut R Nh t).st.Z‖ ≤ C * (t Nh).1 ∧
    ‖(histOut R Nh t).nu‖ ≤ C * (t Nh).1 ∧
    ‖(histOut R Nh t).g‖ ≤ C * (t Nh).1 ∧ 0 ≤ (histOut R Nh t).g.re ∧
    Fnorm (Nh + 1) (fscale (histOut R Nh t).st.Z * R.ℓ) (histOut R Nh t).st.Wl ≤
      ENNReal.ofReal (C * (t Nh).1 ^ 2) ∧
    Fnorm (Nh + 1) (fscale (histOut R Nh t).st.Z * R.ℓ) (histOut R Nh t).D ≤
      ENNReal.ofReal (C * (t Nh).1 ^ 2) ∧
    Knorm (Nh + 1) (fscale (histOut R Nh t).st.Z * R.ℓ) R.A (histOut R Nh t).K ≤
      ENNReal.ofReal (C * (t Nh).1 ^ 3)) ∧
  (‖(lastOut R Nh t).κ.z / (lastOut R Nh t).Z‖ ≤ C * (t Nh).1 ∧
    ‖(lastOut R Nh t).κ.y / (lastOut R Nh t).Z‖ ≤ C * (t Nh).1 ∧
    ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh t).κ.nu / (lastOut R Nh t).Z‖ ≤ C * (t Nh).1 ∧
    ‖(lastOut R Nh t).κ.g / (lastOut R Nh t).Z ^ 2‖ ≤ C * (t Nh).1 ∧
    ‖(lastOut R Nh t).u‖ ≤ C * (t Nh).1 ∧
    (∀ b ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh t).V b : Alg 2 L N) = Vcoup (lastOut R Nh t).κ (blockSet (Nh + 1) b) ∧
      Grassmann.Tj 2 (L : ℝ) (Nh + 1 + 1) (fscale (lastOut R Nh t).Z * R.ℓ) ((lastOut R Nh t).V b : Alg 2 L N) ≤
        ENNReal.ofReal (C * (t Nh).1) ∧
      Grassmann.Tj 2 (L : ℝ) (Nh + 1 + 1) (fscale (lastOut R Nh t).Z * R.ℓ) ((lastOut R Nh t).W b : Alg 2 L N) ≤
        ENNReal.ofReal (C * (t Nh).1 ^ 2)) ∧
    Grassmann.Tj 2 (L : ℝ) (Nh + 1 + 1) (fscale (lastOut R Nh t).Z * R.ℓ) ((lastOut R Nh t).K : Alg 2 L N) ≤
      ENNReal.ofReal (C * (t Nh).1 ^ 3))

/-- `|m²| L^{2j} ≤ 1` for `j ≤ N - 1`. -/
theorem msq_le_last {L : ℕ} (hL : (1 : ℝ) ≤ L) {msq : ℝ} (hm0 : 0 < msq) {N j : ℕ}
    (hm : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hN : 2 ≤ N) (hj : j + 1 ≤ N) :
    |msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := by
  have h := msq_horizon hL hm (Nh := N - 2) (k := 0) (by omega)
  have e : N - 2 + 1 = N - 1 := by omega
  rw [e, pow_zero, one_pow, inv_one] at h
  rw [abs_of_pos hm0]
  have h2 : ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ (N - 1)) ^ 2 := by
    have : (L : ℝ) ^ j ≤ (L : ℝ) ^ (N - 1) := pow_le_pow_right₀ hL (by omega)
    gcongr
  have := mul_le_mul_of_nonneg_left h2 hm0.le
  linarith only [this, h]

set_option maxHeartbeats 4000000 in
/-- **The last two steps along a regular history.** -/
theorem glue_hist {C₀ η εs CK C₂ CD Cq Cl cS Cqg Clg cSg εsN CKN C : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS) (hGB : GStepBound L R.A Cqg Clg cSg)
    (hLB : LastN.BoundsP L R.A εsN CKN)
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hVN : LastN.ValidLast R (Nh + 1))
    (hm : ∀ j ≤ Nh + 1, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hκ₁ : kap1 L R.A C₀ η ≤ 1) (hCK : 0 ≤ CK) (hCD : 0 ≤ CD) (hCKN : 0 ≤ CKN)
    (hCqg : 0 ≤ Cqg) (hClg : 0 ≤ Clg) (hcSg : 1 ≤ cSg)
    (hcE : cE R Λ κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1)
    (hrN : cRN R Λ κ cm cT C₂ CD * ε ≤ εsN) (hkN : 8 * cKL R Λ κ cm cT C₂ CK * ε ≤ εsN)
    (hC : cFin R Λ κ cm cT C₂ CD CK CKN ≤ C)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    GlueOut R Nh C t := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := glue_step R hSB hGB hV hVL
    (fun j hj => hm j (by omega)) hβ hδ1 H hκ₁ hCK hCD hCqg hClg hcSg hcE hr1 hk1 t ht
  obtain ⟨hg, hgε, hμ, -⟩ := ht.1 Nh le_rfl
  have hg1 : (t Nh).1 ≤ 1 := hgε.trans H.hε1
  have HI := rawInv_hist R hVL.2.2.2.2.1 Nh hV t
  obtain ⟨HI', hD', hK'⟩ := RawInv.stepL hVL HI (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
    (rawK_mem R _ _)
  have hcm := H.hcmu
  have hcx := H.hcx
  have hC₂ := H.hC₂
  obtain ⟨hz0, hmu0, hw0, hd0, hk0, -, -, hnu0⟩ := consts_nonneg R hcm hcx hC₂ hCD hCK hCKN
  obtain ⟨f1, f2, f3, f4, f5, f6, -⟩ := le_cFin R hcm hcx hC₂ hCD hCK hCKN
  have hg0 : 0 ≤ (t Nh).1 := hg.le
  -- `ν'` and `μ' = Re ν'`
  have hnu : ‖(histOut R Nh t).nu‖ ≤ cMu R Λ cm * (t Nh).1 := by
    have h1 := norm_le_insert' (histOut R Nh t).nu ((L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ))
    have e : ‖(L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)‖ = (L : ℝ) ^ 2 * |(t Nh).2.1| := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    rw [e] at h1
    have a1 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    unfold cMu
    linarith only [h1, o3, a1]
  have hμ' : |(histOut R Nh t).nu.re| ≤ cMu R Λ cm * (t Nh).1 :=
    (Complex.abs_re_le_norm _).trans hnu
  -- `ǧ' = Re ǧ'`
  have hg'0 : 0 ≤ (histOut R Nh t).g.re := le_trans (by positivity) o8
  have hg' : (histOut R Nh t).g.re ≤ 3 * (t Nh).1 :=
    (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans o7
  -- the clamps and radii at the last step
  have hη : 2 * (cZ R * (t Nh).1) ≤ R.ρ := by
    have := mul_le_mul_of_nonneg_left hgε (by positivity : (0 : ℝ) ≤ 2 * cZ R)
    linarith only [this, H.h1]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t Nh).1) ≤ 1 / 2 := by
    have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hgε
      (by positivity : (0 : ℝ) ≤ 8 * cM * R.ℓ ^ 2 * cZ R)
    linarith only [this, H.h2]
  have hrε : cRN R Λ κ cm cT C₂ CD * (t Nh).1 ≤ εsN := by
    have : 0 ≤ cRN R Λ κ cm cT C₂ CD := by
      have := (consts_nonneg R hcm hcx hC₂ hCD hCK hCKN).2.2.2.2.2.2.1; linarith
    exact (mul_le_mul_of_nonneg_left hgε this).trans hrN
  have hkε : 8 * (cKL R Λ κ cm cT C₂ CK * (t Nh).1 ^ 3) ≤ εsN := by
    have hg3 : (t Nh).1 ^ 3 ≤ ε := by
      have : (t Nh).1 ^ 3 ≤ (t Nh).1 := by
        nlinarith [pow_le_one₀ hg0 hg1 (n := 2)]
      linarith
    have := mul_le_mul_of_nonneg_left hg3 (by positivity : (0 : ℝ) ≤ 8 * cKL R Λ κ cm cT C₂ CK)
    linarith only [this, hkN]
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := glue_last R hLB hVN HI' hD' hK' (hm (Nh + 1) le_rfl)
    hcm hcx hC₂ hCD hCK hCKN hg0 hg1 hg'0 hg' hμ' o1 o2 hη hηs o4 o5 o6 hrε hkε
  have hCg : ∀ p : ℕ, cFin R Λ κ cm cT C₂ CD CK CKN * (t Nh).1 ^ p ≤ C * (t Nh).1 ^ p :=
    fun p => mul_le_mul_of_nonneg_right hC (by positivity)
  have hCg1 := hCg 1
  rw [pow_one] at hCg1
  have hCg2 := hCg 2
  have hCg3 := hCg 3
  have m1 : ∀ c : ℝ, c ≤ cFin R Λ κ cm cT C₂ CD CK CKN → c * (t Nh).1 ≤ C * (t Nh).1 :=
    fun c hc => (mul_le_mul_of_nonneg_right hc hg0).trans hCg1
  refine ⟨⟨o1.trans (m1 _ f1), o2.trans (m1 _ f1), hnu.trans (m1 _ f2), o7.trans (m1 _ f3),
    hg'0, o4.trans (ENNReal.ofReal_le_ofReal ?_), o5.trans (ENNReal.ofReal_le_ofReal ?_),
    o6.trans (ENNReal.ofReal_le_ofReal ?_)⟩,
    ⟨l1.trans hCg1, l2.trans hCg1, l3.trans hCg1, l4.trans hCg1, l5.trans hCg1,
      fun b hb => ?_, l7.trans (ENNReal.ofReal_le_ofReal hCg3)⟩⟩
  · exact (mul_le_mul_of_nonneg_right f4 (by positivity)).trans hCg2
  · exact (mul_le_mul_of_nonneg_right f5 (by positivity)).trans hCg2
  · exact (mul_le_mul_of_nonneg_right f6 (by positivity)).trans hCg3
  · obtain ⟨b1, b2, b3⟩ := l6 b hb
    exact ⟨b1, b2.trans (ENNReal.ofReal_le_ofReal hCg1), b3.trans (ENNReal.ofReal_le_ofReal hCg2)⟩

end

end Step2
