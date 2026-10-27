import Ward.Anm0
import Ward.ObsLimitCorr

/-!
# `cor:anm0`: reality of `γ, λ` and the real form

* `GamA_real`: `γ^{(2)}_{a,∞}(m² = 0, b)` is real (a limit of the real `⟨ψ̄_0ψ_0⟩_{Λ_N}` at
  `m² > 0`, `avg_pbp_tendsto`, and continuity in `m²`, `GamA_cont`).
* `LamA_real`: `λ^{(2)}_{a,∞}(0, b)` is real (from the complex form of `cor:anm0` at all `N`:
  `Λ(1 + E_N) = |Λ_N| ã₀ (1/c₀² - γ)` is real and `E_N → 0`).
* **`cor_anm0_of`**: `1 = c₀² (γ + λ/(|Λ_N| ã₀) (1 + E))` with `γ = gamInf`, `λ = lamInf` and a
  real `E = O(b L^{-κ₁ N})`, `κ₁ = min(κ, 1)`, for `N ≥ 2`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem im_eq_zero_of_tendsto {f : ℕ → ℂ} {z : ℂ} (hf : Tendsto f atTop (𝓝 z))
    (h : ∀ᶠ N in atTop, (f N).im = 0) : z.im = 0 := by
  have h1 : Tendsto (fun N => (f N).im) atTop (𝓝 z.im) :=
    (Complex.continuous_im.tendsto _).comp hf
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h.mono fun N hN => hN.symm))

set_option maxHeartbeats 2000000 in
/-- `γ^{(2)}_{a,∞}(0, b)` is real (`0 < b`, `48 C b ≤ 1`, `b ≤ λ̄`). -/
theorem GamA_real (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) {b : ℝ}
    (hb : 0 < b) (hbl : b ≤ lbar) (hC48 : 48 * C * b ≤ 1) :
    (GamA d L V₀c lbar 0 b).im = 0 := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hC := HF.C_nonneg
  have H := ObsLimHyp.ofW HW hLodd
  obtain ⟨Cs, hCs, hSall⟩ := exists_stepBd d hd1
  have hS := hSall L A ℓ₀ V₀c lbar C κ H
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl
  have hpos : ∀ m : ℝ, 0 < m → (GamA d L V₀c lbar m b).im = 0 := by
    intro m hm
    refine im_eq_zero_of_tendsto (avg_pbp_tendsto H hCs hS hd hm hbn) (Eventually.of_forall
      fun N => ?_)
    have hs := abs_s0R_le HF hb.le hbl hm.le
    have hs1 : -1 < s0R V₀c b m := by
      have : 2 * C * b ≤ 1 / 2 := by linarith
      linarith [(abs_le.1 hs).1]
    have hc := c2F_pos (V₀c := V₀c) (m := m) hb hs1
    have e := avg_ξη_eq (N := N) HW.conj hb hs1 hm (0 : Lam d L N) 0
    rw [← avgM_eq (HF.hb m b)]
    have e2 : avgM d L N V₀c m b (psibar 0 * psi 0) =
        ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ 0 * H02.η 0) /
          c2F V₀c b m : ℝ) : ℂ) := by
      have hc' : (c2F V₀c b m : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [Complex.ofReal_div, e]
      field_simp
    rw [e2, Complex.ofReal_im]
  have hc := GamA_cont H hd1 hCs hS hd hbn
  have ht : Tendsto (fun m => (GamA d L V₀c lbar m b).im) (𝓝[>] 0)
      (𝓝 (GamA d L V₀c lbar 0 b).im) :=
    (Complex.continuous_im.tendsto _).comp
      ((hc 0 Set.self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self))
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
  exact (hpos m hm).symm

set_option maxHeartbeats 2000000 in
/-- **`cor:anm0`** (Tier 2, real form) for a given `V₀c` with `FlowDataW` (`L` odd). -/
theorem cor_anm0_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ∃ bbar Ca : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ bbar ≤ 1 ∧ 0 ≤ Ca ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0 ∧ (GamA d L V₀c lbar 0 b).im = 0 ∧
        (LamA d L V₀c lbar 0 b).im = 0 ∧ |lamInf d L V₀c lbar b - 1| ≤ 1 / 2) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ b, 0 < b → b ≤ bbar →
        0 < atR d L V₀c N b ∧ Fintype.card (Lam d L N) * atR d L V₀c N b ≤ 8 * b ∧
        ∃ E : ℝ, |E| ≤ Ca * b * (L : ℝ) ^ (-(min κ 1 * N)) ∧
          1 = c2F V₀c b 0 * (gamInf d L V₀c lbar b + lamInf d L V₀c lbar b /
            (Fintype.card (Lam d L N) * atR d L V₀c N b) * (1 + E)) := by
  have HF := HW.toFlowData
  have hC := HF.C_nonneg
  have hL2 := HF.hL2
  obtain ⟨ba, Ca, hba, hba2, hba1, hCa, hh0, hLam, hmain⟩ := anm0_complex hd HW hLodd
  set bbar := min ba (1 / (48 * C + 48)) with hbbar
  have hbb1 : bbar ≤ ba := min_le_left _ _
  have hbpos : 0 < bbar := lt_min hba (by positivity)
  have h48 : 48 * C * bbar ≤ 1 := by
    have h := min_le_right ba (1 / (48 * C + 48))
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 48 * C + 48)
    rw [mul_one_div_cancel (by positivity)] at this
    nlinarith
  have hκ1 : 0 < min κ 1 := lt_min HF.κ_pos one_pos
  -- reality
  have hreal : ∀ b, 0 < b → b ≤ bbar →
      (GamA d L V₀c lbar 0 b).im = 0 ∧ (LamA d L V₀c lbar 0 b).im = 0 := by
    intro b hb hbb
    have hC48 : 48 * C * b ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hbb hC]
    have hG := GamA_real hd HW hLodd hb (by linarith) hC48
    refine ⟨hG, ?_⟩
    have hN : ∀ N : ℕ, ∃ E : ℂ, 2 ≤ N → ‖E‖ ≤ Ca * b * (L : ℝ) ^ (-(min κ 1 * N)) ∧
        (1 : ℂ) = (c2F V₀c b 0 : ℂ) * (GamA d L V₀c lbar 0 b + LamA d L V₀c lbar 0 b /
          ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) * (1 + E)) := by
      intro N
      by_cases h2 : 2 ≤ N
      · obtain ⟨-, -, E, hE, hid⟩ := hmain N h2 b hb (hbb.trans hbb1)
        exact ⟨E, fun _ => ⟨hE, hid⟩⟩
      · exact ⟨0, fun h => absurd h h2⟩
    choose E hE using hN
    have hE0 : Tendsto E atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have ht := (tendsto_rpow_neg_mul (L := L) hL2 hκ1).const_mul (Ca * b)
      rw [mul_zero] at ht
      refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ ht
      filter_upwards [eventually_ge_atTop 2] with N hN using (hE N hN).1
    have hlim : Tendsto (fun N => LamA d L V₀c lbar 0 b * (1 + E N)) atTop
        (𝓝 (LamA d L V₀c lbar 0 b)) := by
      have := (tendsto_const_nhds (x := LamA d L V₀c lbar 0 b)).mul
        ((tendsto_const_nhds (x := (1 : ℂ))).add hE0)
      simpa using this
    refine im_eq_zero_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    obtain ⟨-, hid⟩ := hE N hN
    have ha0 := (hmain N hN b hb (hbb.trans hbb1)).1
    have hc0 : (c2F V₀c b 0 : ℂ) ≠ 0 := by
      have hs := abs_s0R_le HF hb.le (by linarith) le_rfl
      have hs1 : -1 < s0R V₀c b 0 := by
        have : 2 * C * b ≤ 1 / 2 := by linarith
        linarith [(abs_le.1 hs).1]
      exact_mod_cast (c2F_pos hb hs1).ne'
    have hM0 : ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (Suscept.card_lam_pos N) ha0).ne'
    have h1 : GamA d L V₀c lbar 0 b + LamA d L V₀c lbar 0 b /
        ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) * (1 + E N) =
        1 / (c2F V₀c b 0 : ℂ) := by
      rw [eq_div_iff hc0, mul_comm]; exact hid.symm
    have e : LamA d L V₀c lbar 0 b * (1 + E N) =
        ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) *
          (1 / (c2F V₀c b 0 : ℂ) - GamA d L V₀c lbar 0 b) := by
      rw [← h1]; field_simp; ring
    rw [e, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, hG]
    simp
  refine ⟨bbar, Ca, hbpos, hbb1.trans hba2, hbb1.trans hba1, hCa, fun b hb hbb => ?_,
    fun N hN b hb hbb => ?_⟩
  · obtain ⟨h1, h2⟩ := hreal b hb hbb
    refine ⟨hh0 b hb (hbb.trans hbb1), h1, h2, ?_⟩
    have := hLam b hb (hbb.trans hbb1)
    have e : LamA d L V₀c lbar 0 b - 1 = ((lamInf d L V₀c lbar b - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [lamInf, h2]
    rw [e, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  · obtain ⟨ha0, hM8, E, hE, hid⟩ := hmain N hN b hb (hbb.trans hbb1)
    obtain ⟨hG, hΛ⟩ := hreal b hb hbb
    have eG : GamA d L V₀c lbar 0 b = (gamInf d L V₀c lbar b : ℂ) :=
      Complex.ext rfl (by simp [hG])
    have eΛ : LamA d L V₀c lbar 0 b = (lamInf d L V₀c lbar b : ℂ) :=
      Complex.ext rfl (by simp [hΛ])
    have hΛ0 : lamInf d L V₀c lbar b ≠ 0 := by
      have := hLam b hb (hbb.trans hbb1)
      intro h
      rw [eΛ, h, Complex.ofReal_zero, zero_sub, norm_neg, norm_one] at this
      linarith
    have hM : 0 < (Fintype.card (Lam d L N) : ℝ) * atR d L V₀c N b :=
      mul_pos (Suscept.card_lam_pos N) ha0
    have hc0 : (c2F V₀c b 0 : ℂ) ≠ 0 := by
      have hs := abs_s0R_le HF hb.le (by linarith) le_rfl
      have hs1 : -1 < s0R V₀c b 0 := by
        have : 2 * C * b ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hbb hC]
        linarith [(abs_le.1 hs).1]
      exact_mod_cast (c2F_pos hb hs1).ne'
    -- `E` is real
    have hEim : E.im = 0 := by
      have hM0 : ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hM.ne'
      have h1 : (gamInf d L V₀c lbar b : ℂ) + (lamInf d L V₀c lbar b : ℂ) /
          ((Fintype.card (Lam d L N) * atR d L V₀c N b : ℝ) : ℂ) * (1 + E) =
          1 / (c2F V₀c b 0 : ℂ) := by
        rw [eq_div_iff hc0, mul_comm, ← eG, ← eΛ]; exact hid.symm
      have e : (lamInf d L V₀c lbar b : ℂ) * (1 + E) =
          (((Fintype.card (Lam d L N) * atR d L V₀c N b) *
            (1 / c2F V₀c b 0 - gamInf d L V₀c lbar b) : ℝ) : ℂ) := by
        have hat0 : (atR d L V₀c N b : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
        have hcd0 : (Fintype.card (Lam d L N) : ℂ) ≠ 0 := by
          exact_mod_cast (Suscept.card_lam_pos (d := d) (L := L) N).ne'
        push_cast at h1 ⊢
        rw [← h1]; field_simp; ring
      have h2 := congrArg Complex.im e
      rw [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, zero_add, zero_mul, add_zero] at h2
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h hΛ0
      · exact h
    have eE : E = (E.re : ℂ) := Complex.ext rfl (by simp [hEim])
    refine ⟨ha0, hM8, E.re, (Complex.abs_re_le_norm E).trans hE, ?_⟩
    rw [eG, eΛ, eE] at hid
    exact_mod_cast hid

end

end Ward
