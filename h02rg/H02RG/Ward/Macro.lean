import Ward.CorWard
import FRD.Det
import Mathlib

-- Merged from `Ward/MacroAnalysis.lean` (phase 3).
section

/-!
# The real analysis in the proof of `cor:macro`

`macro_analysis`: for real functions of `m² ≥ 0` with
`D = m² + m² k⁰ + ã (m² t)`, `0 ≤ 1/m² - t ≤ K`, `D ≥ P` near `0`, `P(0) > 0`, and
`S = c²(1 + k⁰)/D + c² ã (t - 1/m²)/D` for `m² > 0`, continuity of `k⁰, ã, c², P, S` at
`0` gives `ã(0) > 0` and `|S(0) - c²(0)(1 + k⁰(0))/ã(0)| ≤ c²(0) K`.
-/

namespace Ward

open Filter Topology Set

theorem macro_analysis {D ar kr tt c2 S P : ℝ → ℝ} {K : ℝ}
    (hD : ∀ m, 0 < m → D m = m + m * kr m + ar m * (m * tt m))
    (hkr : ContinuousWithinAt kr (Ici 0) 0) (har : ContinuousWithinAt ar (Ici 0) 0)
    (hc2 : ContinuousWithinAt c2 (Ici 0) 0) (hP : ContinuousWithinAt P (Ici 0) 0)
    (hSc : ContinuousWithinAt S (Ici 0) 0)
    (ht : ∀ m, 0 < m → 0 ≤ 1 / m - tt m ∧ 1 / m - tt m ≤ K)
    (hDP : ∀ m, 0 < m → m ≤ 1 → P m ≤ D m) (hP0 : 0 < P 0) (hDpos : ∀ m, 0 < m → 0 < D m)
    (hc2nn : ∀ m, 0 < m → 0 ≤ c2 m)
    (hS : ∀ m, 0 < m → S m = c2 m * (1 + kr m) / D m + c2 m * ar m * (tt m - 1 / m) / D m) :
    0 < ar 0 ∧ |S 0 - c2 0 * (1 + kr 0) / ar 0| ≤ c2 0 * K := by
  have tends : ∀ {f : ℝ → ℝ}, ContinuousWithinAt f (Ici 0) 0 → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => (hf.mono Ioi_subset_Ici_self).tendsto
  have hid : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  -- `m t → 1`
  have hmt : Tendsto (fun m => m * tt m) (𝓝[>] 0) (𝓝 1) := by
    have hlow : Tendsto (fun m : ℝ => 1 - m * K) (𝓝[>] 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub (hid.mul_const K) : Tendsto (fun m : ℝ => 1 - m * K)
        (𝓝[>] 0) (𝓝 (1 - 0 * K)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
      have h := mul_le_mul_of_nonneg_left (ht m hm).2 hm.le
      rw [mul_sub, mul_one_div_cancel hm.ne'] at h
      linarith
    · filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
      have h := mul_le_mul_of_nonneg_left (ht m hm).1 hm.le
      rw [mul_sub, mul_one_div_cancel hm.ne', mul_zero] at h
      linarith
  have hDlim : Tendsto D (𝓝[>] 0) (𝓝 (ar 0)) := by
    have h := (hid.add (hid.mul (tends hkr))).add ((tends har).mul hmt)
    simp only [zero_mul, zero_add, mul_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
    exact (hD m hm).symm
  have ha0 : 0 < ar 0 := by
    have hle : P 0 ≤ ar 0 := le_of_tendsto_of_tendsto (tends hP) hDlim (by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with
        m (hm : 0 < m) hm1 using hDP m hm hm1.2.le)
    linarith
  refine ⟨ha0, ?_⟩
  have hT1 : Tendsto (fun m => c2 m * (1 + kr m) / D m) (𝓝[>] 0)
      (𝓝 (c2 0 * (1 + kr 0) / ar 0)) :=
    ((tends hc2).mul (tendsto_const_nhds.add (tends hkr))).div hDlim ha0.ne'
  have hT2 : Tendsto (fun m => c2 m * ar m * (tt m - 1 / m) / D m) (𝓝[>] 0)
      (𝓝 (S 0 - c2 0 * (1 + kr 0) / ar 0)) := by
    refine ((tends hSc).sub hT1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
    rw [hS m hm]; ring
  have hb2 : Tendsto (fun m => c2 m * |ar m / D m| * K) (𝓝[>] 0)
      (𝓝 (c2 0 * |ar 0 / ar 0| * K)) :=
    ((tends hc2).mul ((tends har).div hDlim ha0.ne').abs).mul tendsto_const_nhds
  rw [div_self ha0.ne', abs_one, mul_one] at hb2
  refine le_of_tendsto_of_tendsto hT2.abs hb2 ?_
  filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
  have htm : |tt m - 1 / m| ≤ K := by
    rw [abs_sub_comm, abs_of_nonneg (ht m hm).1]; exact (ht m hm).2
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (hc2nn m hm), abs_div]
  calc c2 m * |ar m| * |tt m - 1 / m| / |D m| = c2 m * (|ar m| / |D m|) * |tt m - 1 / m| := by
        ring
    _ ≤ c2 m * (|ar m| / |D m|) * K :=
        mul_le_mul_of_nonneg_left htm (mul_nonneg (hc2nn m hm) (by positivity))

end Ward

end

/-!
# Corollary `cor:macro` (Section `sec:finvol`)

Fix `N ≥ 1` and real `b ∈ (0, b̄]`, and put `β = β(b, 0)`, `c₀² = c²(b, 0)`,
`ã₀ = Re ã_{N,N}(0, V₀^c(0, b))` (`atR`). Then (`cor_macro`):

* `ã₀ > 0`;
* `𝔼_{β,0}|T_0| = c₀²(1 + E₁)/ã₀ + E₂` with `|E₁| ≤ C b L^{-κN}`, `|E₂| ≤ C b L^{2N}`;
* `1/ã₀ ≤ C |Λ_N|/b`.

## Proof, and a correction of the paper
The paper deduces `ã₀ > 0` from the divergence of `1 + ũ` as `m² ↓ 0`, which does not follow.
Instead: `m²(1 + ũ) = m²(1 + k⁰) + ã (m² t_N) → ã₀` (as `m² t_N → 1`, `tN_sub_inv`), while
`m²(1 + ũ) = m² Z_{β,h} (β/(1+s₀))^{-|Λ|} e^{u_N|Λ|}/det(-Δ+m²) ≥ Z_{β,h} (β/(1+s₀))^{-|Λ|}
e^{u_N|Λ|}/K_N` (`det(-Δ+m²) ≤ K_N m²`, `FRD.det_negLap_add_le`), whose limit is positive
(`Z_{β(b,0),0} > 0`).  All quantities are real by `thm_flow_real`. `(β, h) → (β(b,0), 0)` as
`m² ↓ 0` at fixed `b`, and the `ℍ^{0|2}` model is continuous in `(β, h)`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- `ã_{N,N}` at `m² = 0` (real part). -/
def atR (d L : ℕ) [NeZero L] (V₀c : ℝ → ℂ → Vcoup) (N : ℕ) (b : ℝ) : ℝ :=
  (Suscept.atN d L N 0 (V₀c 0 b)).re

theorem ofReal_re_of_im {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext rfl (by simp [h])

theorem contOn_expect_comp {N : ℕ} {S : Set ℝ} {f g : ℝ → ℝ} (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) (F : H02.Grassmann (Lam d L N)) :
    ContinuousOn (fun m => H02.expect (nnW d L N (f m)) (fun _ => g m) F) S := by
  have h := (continuous_expect_nnW (d := d) (L := L) (N := N) F).comp_continuousOn (hf.prodMk hg)
  exact h

theorem contOn_avg_comp {N : ℕ} {S : Set ℝ} {f g : ℝ → ℝ} (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) (hfg : ∀ m ∈ S, 0 ≤ f m ∧ 0 ≤ g m) (F : H02.Grassmann (Lam d L N)) :
    ContinuousOn (fun m => H02.avg (nnW d L N (f m)) (fun _ => g m) F) S := by
  have h := (continuousOn_avg_nnW (d := d) (L := L) (N := N) F).comp (hf.prodMk hg) hfg
  exact h

set_option maxHeartbeats 10000000 in
/-- **`cor:macro`** for a given `V₀c` with `FlowDataW`. -/
theorem cor_macro_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) :
    ∃ bbar Cm : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ 0 ≤ Cm ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ b, 0 < b → b ≤ bbar →
        0 < atR d L V₀c N b ∧
        (∃ E₁ E₂ : ℝ, |E₁| ≤ Cm * b * (L : ℝ) ^ (-(κ * N)) ∧ |E₂| ≤ Cm * b * (L : ℝ) ^ (2 * N) ∧
          H02.expTree (nnW d L N (betaF V₀c b 0)) (nnW_symm _) 0 =
            c2F V₀c b 0 * (1 + E₁) / atR d L V₀c N b + E₂) ∧
        1 / atR d L V₀c N b ≤ Cm * Fintype.card (Lam d L N) / b := by
  have HF := HW.toFlowData
  have hC := HF.C_nonneg
  have hl := HF.lbar_pos
  have hd1 : 1 ≤ d := by omega
  have hL2 := HF.hL2
  have hL3 : 3 ≤ L := by
    have h8 := HF.hL8
    have h23 : 2 ^ 3 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨bw, K, hbw0, hbw2, hbw1, hK0, hKb, h48, hall, hh0, -⟩ := cor_ward_i hd HW
  obtain ⟨Ct, hCt, HB⟩ := thm_psi4_full_of hd HF
  obtain ⟨-, -, -, -, -, -, hut, hZcorr⟩ := HB
  obtain ⟨Kt, hKt⟩ := FRD.tN_sub_inv stdPt hd1
  have hKt0 : 0 ≤ Kt := by
    have := (hKt 1 one_pos 1 le_rfl 0).2; simpa using (hKt 1 one_pos 1 le_rfl 0).1.trans this
  set bbar := min bw (1 / (2 * Ct + 2)) with hbbar
  have hbb1 : bbar ≤ bw := min_le_left _ _
  have hbb2 : bbar ≤ 1 / (2 * Ct + 2) := min_le_right _ _
  have hbpos : 0 < bbar := lt_min hbw0 (by positivity)
  have hCtb : Ct * bbar ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hbb2 (by positivity : (0 : ℝ) ≤ 2 * Ct + 2)
    rw [mul_one_div_cancel (by positivity)] at this
    nlinarith
  set Cm := Ct + 2 * Kt + 3 * (1 + 2 * Kt) with hCm
  refine ⟨bbar, Cm, hbpos, hbb1.trans hbw2, by positivity,
    fun b hb hbb => hh0 b hb (hbb.trans hbb1), fun N hN b hb hbb => ?_⟩
  have hbw : b ≤ bw := hbb.trans hbb1
  have hbl : b ≤ lbar := by linarith
  have hbl' : b < lbar := by linarith
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl
  have hbnorm : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
  -- `s₀` and the model parameters
  have hsb : ∀ m, 0 ≤ m → -(1 / 2) ≤ s0R V₀c b m ∧ s0R V₀c b m ≤ 1 / 2 := fun m hm => by
    have hs := abs_s0R_le HF hb.le hbl hm
    have : 2 * C * b ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hbw hC]
    constructor <;> linarith [(abs_le.1 hs).1, (abs_le.1 hs).2]
  have hs1 : ∀ m, 0 ≤ m → -1 < s0R V₀c b m := fun m hm => by linarith [(hsb m hm).1]
  have hβpos : ∀ m, 0 ≤ m → 0 < betaF V₀c b m := fun m hm => betaF_pos hb (hs1 m hm)
  have hhnn : ∀ m, 0 ≤ m → 0 ≤ hF V₀c b m := fun m hm => by
    have h := hall b m hb hbw hm
    have hmβ : 0 ≤ m * betaF V₀c b m := mul_nonneg hm (hβpos m hm).le
    have hKb' : K * b ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hbw hK0).trans hKb
    have := (abs_le.1 h).1
    nlinarith [mul_le_mul_of_nonneg_right hKb' hmβ]
  -- continuity in `m²` of the ingredients (on `[0, ∞)`)
  obtain ⟨hsc, -⟩ := s0R_a0R_cont HF
  obtain ⟨hβc, hhc⟩ := betaF_hF_cont HF
  have hmap : Set.MapsTo (fun m : ℝ => (b, m)) (Set.Ici 0) (Set.Ico 0 lbar ×ˢ Set.Ici 0) :=
    fun m hm => ⟨⟨hb.le, hbl'⟩, hm⟩
  have hmap' : Set.MapsTo (fun m : ℝ => (b, m)) (Set.Ici 0) (Set.Ioo 0 lbar ×ˢ Set.Ici 0) :=
    fun m hm => ⟨⟨hb, hbl'⟩, hm⟩
  have hc1 : ContinuousOn (fun m : ℝ => (b, m)) (Set.Ici 0) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have cs : ContinuousOn (fun m => s0R V₀c b m) (Set.Ici 0) := hsc.comp hc1 hmap
  have cβ : ContinuousOn (fun m => betaF V₀c b m) (Set.Ici 0) := hβc.comp hc1 hmap'
  have ch : ContinuousOn (fun m => hF V₀c b m) (Set.Ici 0) := hhc.comp hc1 hmap'
  obtain ⟨-, cu, ck, -, ca, -⟩ := Suscept.prop_ZNN_cont (N := N) hd1 HF.hL8 (ℓ₀ := ℓ₀)
    subset_rfl (HF.cv hbn) (fun m hm j hj => HF.good N m hm j hj)
  have cur : ContinuousOn (fun m => (Suscept.uN d L N m (V₀c m b)).re) (Set.Ici 0) :=
    Complex.continuous_re.comp_continuousOn cu
  have ckr : ContinuousOn (fun m => (Suscept.kN0 d L N m (V₀c m b)).re) (Set.Ici 0) :=
    Complex.continuous_re.comp_continuousOn ck
  have car : ContinuousOn (fun m => (Suscept.atN d L N m (V₀c m b)).re) (Set.Ici 0) :=
    Complex.continuous_re.comp_continuousOn ca
  have cc2 : ContinuousOn (fun m => c2F V₀c b m) (Set.Ici 0) :=
    continuousOn_const.div (continuousOn_const.add cs) fun m hm => (show (0:ℝ) < 1 + s0R V₀c b m by linarith [hs1 m hm]).ne'
  -- reality
  have hreal := fun m => Suscept.im_eq_zero_V0c (L := L) hd1 hL3 HW.conj N m b
  -- opaque abbreviations
  obtain ⟨ur, hur⟩ : ∃ f : ℝ → ℝ, f = fun m => (Suscept.uN d L N m (V₀c m b)).re := ⟨_, rfl⟩
  obtain ⟨kr, hkr⟩ : ∃ f : ℝ → ℝ, f = fun m => (Suscept.kN0 d L N m (V₀c m b)).re := ⟨_, rfl⟩
  obtain ⟨ar, har⟩ : ∃ f : ℝ → ℝ, f = fun m => (Suscept.atN d L N m (V₀c m b)).re := ⟨_, rfl⟩
  obtain ⟨utr, hutr⟩ : ∃ f : ℝ → ℝ, f = fun m => (Suscept.utN d L N m (V₀c m b)).re := ⟨_, rfl⟩
  obtain ⟨tt, htt⟩ : ∃ f : ℝ → ℝ, f = fun m => Suscept.tNN d L N m := ⟨_, rfl⟩
  have hut_eq : ∀ m, utr m = kr m + ar m * tt m := fun m => by
    simp only [hutr, hkr, har, htt, Suscept.utN, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hu_c : ∀ m, Suscept.uN d L N m (V₀c m b) = (ur m : ℂ) := fun m => by
    rw [hur]; exact (ofReal_re_of_im (hreal m).1).symm
  have hut_c : ∀ m, Suscept.utN d L N m (V₀c m b) = (utr m : ℂ) := fun m => by
    rw [hutr]; exact (ofReal_re_of_im (hreal m).2.2.2.2).symm
  have hat_c : ∀ m, Suscept.atN d L N m (V₀c m b) = (ar m : ℂ) := fun m => by
    rw [har]; exact (ofReal_re_of_im (hreal m).2.2.2.1).symm
  have cur' : ContinuousOn ur (Set.Ici 0) := hur ▸ cur
  have ckr' : ContinuousOn kr (Set.Ici 0) := hkr ▸ ckr
  have car' : ContinuousOn ar (Set.Ici 0) := har ▸ car
  obtain ⟨card, hcard⟩ : ∃ c : ℝ, c = (Fintype.card (Lam d L N) : ℝ) := ⟨_, rfl⟩
  have hcard0 : 0 < card := hcard ▸ Suscept.card_lam_pos N
  obtain ⟨Kd, hKd⟩ := FRD.det_negLap_add_le (d := d) (n := L ^ N)
  have hKd0 : 0 < Kd := by
    have h1 := hKd 1 one_pos le_rfl
    have h2 := FRD.det_negLap_add_pos (d := d) (n := L ^ N) (msq := 1) one_pos
    linarith
  obtain ⟨dt, hdt⟩ : ∃ f : ℝ → ℝ,
      f = fun m => (FRD.negLap + m • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det := ⟨_, rfl⟩
  have hdtpos : ∀ m, 0 < m → 0 < dt m := fun m hm => by
    rw [hdt]; exact FRD.det_negLap_add_pos hm
  have hdtle : ∀ m, 0 < m → m ≤ 1 → dt m ≤ Kd * m := fun m hm hm1 => by
    rw [hdt]; exact hKd m hm hm1
  obtain ⟨Z, hZ⟩ : ∃ f : ℝ → ℝ,
      f = fun m => H02.expect (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) 1 := ⟨_, rfl⟩
  have hZpos : ∀ m, 0 ≤ m → 0 < Z m := fun m hm => by
    rw [hZ]; exact expect_one_pos_nnW (hβpos m hm).le (hhnn m hm)
  obtain ⟨Q, hQ⟩ : ∃ f : ℝ → ℝ,
      f = fun m => (betaF V₀c b m / (1 + s0R V₀c b m)) ^ Fintype.card (Lam d L N) := ⟨_, rfl⟩
  have hQpos : ∀ m, 0 ≤ m → 0 < Q m := fun m hm => by
    rw [hQ]; exact pow_pos (div_pos (hβpos m hm) (by linarith [hs1 m hm])) _
  have hZeq : ∀ m, 0 < m → Z m = Q m * dt m * Real.exp (-(ur m * card)) * (1 + utr m) :=
    fun m hm => by
      have e1 := expect_one_eq (d := d) (L := L) (N := N) HW.conj hb (hs1 m hm.le) hm
      rw [(hZcorr N m b hN hm hbn).1, hu_c, hut_c] at e1
      have e2 : ((Z m : ℝ) : ℂ) = ((Q m * dt m * Real.exp (-(ur m * card)) * (1 + utr m) : ℝ) : ℂ) := by
        rw [hZ, hQ, hdt, hcard]
        simp only
        rw [e1]
        push_cast
        ring
      exact_mod_cast e2
  obtain ⟨D, hD⟩ : ∃ f : ℝ → ℝ, f = fun m => m * (1 + utr m) := ⟨_, rfl⟩
  have h1u : ∀ m, 0 < m → 0 < 1 + utr m := fun m hm => by
    have h := hZeq m hm
    have h1 : 0 < Q m * dt m * Real.exp (-(ur m * card)) :=
      mul_pos (mul_pos (hQpos m hm.le) (hdtpos m hm)) (Real.exp_pos _)
    by_contra hc
    push_neg at hc
    have := hZpos m hm.le
    nlinarith
  have hDpos : ∀ m, 0 < m → 0 < D m := fun m hm => by rw [hD]; exact mul_pos hm (h1u m hm)
  obtain ⟨P, hP⟩ : ∃ f : ℝ → ℝ, f = fun m => Z m / (Q m * Kd * Real.exp (-(ur m * card))) :=
    ⟨_, rfl⟩
  have hDP : ∀ m, 0 < m → m ≤ 1 → P m ≤ D m := fun m hm hm1 => by
    have hdet := hdtle m hm hm1
    have hdet0 := hdtpos m hm
    have hE := Real.exp_pos (-(ur m * card))
    have hQ0 := hQpos m hm.le
    have hZm := hZeq m hm
    have hu1 := h1u m hm
    rw [hP, hD]
    simp only
    rw [div_le_iff₀ (by positivity), hZm]
    have : Q m * dt m * Real.exp (-(ur m * card)) * (1 + utr m) ≤
        Q m * (Kd * m) * Real.exp (-(ur m * card)) * (1 + utr m) := by gcongr
    linarith
  have cZ : ContinuousOn Z (Set.Ici 0) := by
    rw [hZ]
    exact contOn_expect_comp cβ ch 1
  have cQ : ContinuousOn Q (Set.Ici 0) := by
    rw [hQ]
    exact (cβ.div (continuousOn_const.add cs) fun m hm => (show (0:ℝ) < 1 + s0R V₀c b m by linarith [hs1 m hm]).ne').pow _
  have cP : ContinuousOn P (Set.Ici 0) := by
    rw [hP]
    refine cZ.div ((cQ.mul continuousOn_const).mul
      (Real.continuous_exp.comp_continuousOn ((cur'.mul continuousOn_const).neg))) fun m hm => ?_
    exact (mul_pos (mul_pos (hQpos m hm) hKd0) (Real.exp_pos _)).ne'
  have hP0 : 0 < P 0 := by
    rw [hP]; exact div_pos (hZpos 0 le_rfl) (mul_pos (mul_pos (hQpos 0 le_rfl) hKd0) (Real.exp_pos _))
  -- the sum `∑_x ⟨ξ_0η_x⟩`
  obtain ⟨S, hS⟩ : ∃ f : ℝ → ℝ, f = fun m => ∑ x : Lam d L N,
      H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ 0 * H02.η x) := ⟨_, rfl⟩
  have hSeq : ∀ m, 0 < m → S m = c2F V₀c b m * (1 + kr m) / D m +
      c2F V₀c b m * ar m * (tt m - 1 / m) / D m := fun m hm => by
    have hu0 : 1 + Suscept.utN d L N m (V₀c m b) ≠ 0 := by
      rw [hut_c]; exact_mod_cast (h1u m hm).ne'
    have hsum := ((hZcorr N m b hN hm hbn).2 hu0).1
    have e1 : ((S m : ℝ) : ℂ) = (c2F V₀c b m : ℂ) *
        ∑ x : Lam d L N, avgM d L N V₀c m b (psibar 0 * psi x) := by
      rw [hS]
      simp only [Complex.ofReal_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => avg_ξη_eq HW.conj hb (hs1 m hm.le) hm 0 x
    rw [hsum, hut_c, hat_c] at e1
    have e2 : S m = c2F V₀c b m * (1 / m - 1 / m ^ 2 * (ar m / (1 + utr m))) := by
      have : ((S m : ℝ) : ℂ) =
          ((c2F V₀c b m * (1 / m - 1 / m ^ 2 * (ar m / (1 + utr m))) : ℝ) : ℂ) := by
        rw [e1]; push_cast; rfl
      exact_mod_cast this
    have hD0 := (hDpos m hm).ne'
    have hu1 := (h1u m hm).ne'
    rw [e2, hD]
    simp only
    rw [hut_eq] at hu1 ⊢
    field_simp
    ring
  have cS : ContinuousOn S (Set.Ici 0) := by
    rw [hS]
    refine continuousOn_finset_sum _ fun x _ => ?_
    exact contOn_avg_comp cβ ch (fun m hm => ⟨(hβpos m hm).le, hhnn m hm⟩) _
  have ht : ∀ m, 0 < m → 0 ≤ 1 / m - tt m ∧ 1 / m - tt m ≤ Kt * (L : ℝ) ^ (2 * N) :=
    fun m hm => by rw [htt]; exact hKt m hm L hL1 N
  have hDform : ∀ m, 0 < m → D m = m + m * kr m + ar m * (m * tt m) := fun m hm => by
    rw [hD]; simp only; rw [hut_eq]; ring
  obtain ⟨ha0, hE₂⟩ := macro_analysis (K := Kt * (L : ℝ) ^ (2 * N)) hDform
    (ckr' 0 Set.self_mem_Ici) (car' 0 Set.self_mem_Ici) (cc2 0 Set.self_mem_Ici)
    (cP 0 Set.self_mem_Ici) (cS 0 Set.self_mem_Ici) ht hDP hP0 hDpos
    (fun m hm => (c2F_pos hb (hs1 m hm.le)).le) hSeq
  have hatR : atR d L V₀c N b = ar 0 := by rw [har]; rfl
  refine ⟨hatR ▸ ha0, ?_⟩
  obtain ⟨E₂, hE₂def⟩ : ∃ e : ℝ, e = S 0 - c2F V₀c b 0 * (1 + kr 0) / ar 0 := ⟨_, rfl⟩
  rw [← hE₂def] at hE₂
  -- the identification with `𝔼|T_0|`
  have hexp : H02.expTree (nnW d L N (betaF V₀c b 0)) (nnW_symm _) 0 = S 0 := by
    rw [H02.expTree_eq_sum, hS]
    simp only [hh0 b hb hbw]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨e1, e2, e3, -⟩ := H02.cor_spin_conn (nnW_symm (d := d) (L := L) (N := N) (betaF V₀c b 0))
      (nnW_nonneg (hβpos 0 le_rfl).le) 0 x
    rw [e1, e2, e3]
    rfl
  -- `E₁ = k⁰`
  have hk0 : |kr 0| ≤ Ct * b * (L : ℝ) ^ (-(κ * N)) := by
    have h := (hut N 0 b le_rfl hbn).1
    rw [hbnorm] at h
    have e : Suscept.utN d L N 0 (V₀c 0 b) - Suscept.atN d L N 0 (V₀c 0 b) *
        (Suscept.tNN d L N 0 : ℂ) = Suscept.kN0 d L N 0 (V₀c 0 b) := by
      simp [Suscept.utN]
    rw [e] at h
    rw [hkr]
    exact (Complex.abs_re_le_norm _).trans h
  have hc20 : c2F V₀c b 0 ≤ 2 * b := by
    have := (hsb 0 le_rfl).1
    unfold c2F; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hLpow : (L : ℝ) ^ (2 * N) ≤ card := by
    rw [hcard, Suscept.card_lam]; push_cast
    rw [← pow_mul, mul_comm N d]
    exact pow_le_pow_right₀ hL1 (Nat.mul_le_mul_right N (by omega))
  have hθ1 : (L : ℝ) ^ (-(κ * N)) ≤ 1 := rpow_neg_mul_le_one hL1 HF.κ_pos.le N
  have hkr1 : |kr 0| ≤ 1 / 2 := by
    refine hk0.trans ?_
    have h1 : Ct * b ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hbb hCt).trans hCtb
    have := mul_le_mul h1 hθ1 (by positivity) (by norm_num)
    linarith
  refine ⟨⟨kr 0, E₂, ?_, ?_, ?_⟩, ?_⟩
  · exact hk0.trans (by gcongr; rw [hCm]; linarith)
  · refine hE₂.trans ?_
    have hKL : 0 ≤ Kt * (L : ℝ) ^ (2 * N) := by positivity
    calc c2F V₀c b 0 * (Kt * (L : ℝ) ^ (2 * N)) ≤ 2 * b * (Kt * (L : ℝ) ^ (2 * N)) :=
          mul_le_mul_of_nonneg_right hc20 hKL
      _ = 2 * Kt * b * (L : ℝ) ^ (2 * N) := by ring
      _ ≤ Cm * b * (L : ℝ) ^ (2 * N) := by gcongr; rw [hCm]; linarith
  · rw [hexp, hatR, hE₂def]; ring
  · -- `1/ã₀ ≤ C|Λ|/b`
    have hle := H02.expTree_le_card (nnW_symm (d := d) (L := L) (N := N) (betaF V₀c b 0))
      (nnW_nonneg (hβpos 0 le_rfl).le) 0
    rw [hexp, ← hcard] at hle
    have hS0 : S 0 = c2F V₀c b 0 * (1 + kr 0) / ar 0 + E₂ := by rw [hE₂def]; ring
    rw [hS0] at hle
    have hE₂' : E₂ ≥ -(2 * b * (Kt * card)) := by
      have := (abs_le.1 hE₂).1
      have h2 : c2F V₀c b 0 * (Kt * (L : ℝ) ^ (2 * N)) ≤ 2 * b * (Kt * card) :=
        mul_le_mul hc20 (mul_le_mul_of_nonneg_left hLpow hKt0) (by positivity) (by positivity)
      linarith
    have h1k : 1 / 2 ≤ 1 + kr 0 := by linarith [(abs_le.1 hkr1).1]
    have hc20' : 2 * b / 3 ≤ c2F V₀c b 0 := by
      have := (hsb 0 le_rfl).2
      have h1 := hs1 0 le_rfl
      unfold c2F; rw [le_div_iff₀ (by linarith)]; nlinarith
    have hmain : (b / 3) * (1 / ar 0) ≤ card + 2 * b * (Kt * card) := by
      have : (b / 3) * (1 / ar 0) ≤ c2F V₀c b 0 * (1 + kr 0) / ar 0 := by
        rw [mul_one_div, div_le_div_iff_of_pos_right ha0]
        nlinarith
      linarith
    rw [hatR, ← hcard, le_div_iff₀ hb]
    have hb1 : b ≤ 1 := hbw.trans hbw1
    have : 1 / ar 0 * b ≤ 3 * (card + 2 * b * (Kt * card)) := by nlinarith
    calc 1 / ar 0 * b ≤ 3 * (card + 2 * b * (Kt * card)) := this
      _ ≤ 3 * (1 + 2 * Kt) * card := by nlinarith [mul_le_mul_of_nonneg_left hb1 hKt0]
      _ ≤ Cm * card := by gcongr; rw [hCm]; linarith

end

end Ward
