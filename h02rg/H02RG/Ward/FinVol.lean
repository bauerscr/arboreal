import Ward.Macro

/-!
# Common facts for the finite-volume lemmas (`sec:finvol`)

For `V₀c` with `FlowDataW`, the output `b̄_w, K` of `cor_ward_i`, `N ≥ 1` and real `0 < b ≤ b̄_w`,
along `m² ↓ 0` at fixed `b`:

* `fv_model`: `|s₀(b, m²)| ≤ 1/2`, `β(b, m²) > 0`, `h(b, m²) ≥ 0` and the continuity of `s₀`,
  `β`, `h`, `c²` in `m² ≥ 0`;
* `fv_one_add_utN`: `1 + ũ_{N,N}(m²)` is real and positive for `m² > 0` (from `Z_{β,h} > 0`);
* `fv_D_tendsto`: `m²(1 + ũ_{N,N}(m²)) → ã_{N,N}(0)`, and `m² t_N → 1` (`fv_mt_tendsto`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- `m² t_N → 1` as `m² ↓ 0`. -/
theorem fv_mt_tendsto (hd1 : 1 ≤ d) (N : ℕ) :
    Tendsto (fun m => m * Suscept.tNN d L N m) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨Kt, hKt⟩ := FRD.tN_sub_inv stdPt hd1
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  have hid : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  have hlow : Tendsto (fun m : ℝ => 1 - m * (Kt * (L : ℝ) ^ (2 * N))) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (hid.mul_const (Kt * (L : ℝ) ^ (2 * N))) :
      Tendsto (fun m : ℝ => 1 - m * (Kt * (L : ℝ) ^ (2 * N))) (𝓝[>] 0)
        (𝓝 (1 - 0 * (Kt * (L : ℝ) ^ (2 * N)))))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
    have h := mul_le_mul_of_nonneg_left (hKt m hm L hL1 N).2 hm.le
    rw [mul_sub, mul_one_div_cancel hm.ne'] at h
    show 1 - m * (Kt * (L : ℝ) ^ (2 * N)) ≤ m * FRD.tN stdPt d m (L : ℝ) N
    linarith
  · filter_upwards [self_mem_nhdsWithin] with m (hm : 0 < m)
    have h := mul_le_mul_of_nonneg_left (hKt m hm L hL1 N).1 hm.le
    rw [mul_sub, mul_one_div_cancel hm.ne', mul_zero] at h
    show m * FRD.tN stdPt d m (L : ℝ) N ≤ 1
    linarith

section Fixed

variable (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) {bw K : ℝ}
  (hbw2 : bw ≤ lbar / 2) (hbw1 : bw ≤ 1) (hK0 : 0 ≤ K) (hKb : K * bw ≤ 1 / 2)
  (h48 : 48 * C * bw ≤ 1)
  (hall : ∀ b m, 0 < b → b ≤ bw → 0 ≤ m →
    |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m))
  {b : ℝ} (hb : 0 < b) (hbw : b ≤ bw)
include hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw

set_option maxHeartbeats 4000000 in
/-- The model parameters along `m² ≥ 0` at fixed `b`. -/
theorem fv_model :
    (∀ m, 0 ≤ m → -(1 / 2) ≤ s0R V₀c b m ∧ s0R V₀c b m ≤ 1 / 2) ∧
    (∀ m, 0 ≤ m → 0 < betaF V₀c b m) ∧ (∀ m, 0 ≤ m → 0 ≤ hF V₀c b m) ∧
    ContinuousOn (fun m => s0R V₀c b m) (Set.Ici 0) ∧
    ContinuousOn (fun m => betaF V₀c b m) (Set.Ici 0) ∧
    ContinuousOn (fun m => hF V₀c b m) (Set.Ici 0) ∧
    ContinuousOn (fun m => c2F V₀c b m) (Set.Ici 0) := by
  have HF := HW.toFlowData
  have hC := HF.C_nonneg
  have hl := HF.lbar_pos
  have hbl : b ≤ lbar := by linarith
  have hbl' : b < lbar := by linarith
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
  obtain ⟨hsc, -⟩ := s0R_a0R_cont HF
  obtain ⟨hβc, hhc⟩ := betaF_hF_cont HF
  have hmap : Set.MapsTo (fun m : ℝ => (b, m)) (Set.Ici 0) (Set.Ico 0 lbar ×ˢ Set.Ici 0) :=
    fun m hm => ⟨⟨hb.le, hbl'⟩, hm⟩
  have hmap' : Set.MapsTo (fun m : ℝ => (b, m)) (Set.Ici 0) (Set.Ioo 0 lbar ×ˢ Set.Ici 0) :=
    fun m hm => ⟨⟨hb, hbl'⟩, hm⟩
  have hc1 : ContinuousOn (fun m : ℝ => (b, m)) (Set.Ici 0) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have cs : ContinuousOn (fun m => s0R V₀c b m) (Set.Ici 0) := hsc.comp hc1 hmap
  refine ⟨hsb, hβpos, hhnn, cs, hβc.comp hc1 hmap', hhc.comp hc1 hmap', ?_⟩
  exact continuousOn_const.div (continuousOn_const.add cs)
    fun m hm => (show (0 : ℝ) < 1 + s0R V₀c b m by linarith [hs1 m hm]).ne'

set_option maxHeartbeats 4000000 in
/-- `1 + ũ_{N,N}(m²)` is real and positive for `m² > 0`. -/
theorem fv_one_add_utN {N : ℕ} (hN : 1 ≤ N) {m : ℝ} (hm : 0 < m) :
    Suscept.utN d L N m (V₀c m b) = ((Suscept.utN d L N m (V₀c m b)).re : ℂ) ∧
      0 < 1 + (Suscept.utN d L N m (V₀c m b)).re := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hL3 : 3 ≤ L := by
    have h8 := HF.hL8
    have h23 : 2 ^ 3 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hsb, hβpos, hhnn, -⟩ := fv_model hd HW hbw2 hbw1 hK0 hKb h48 hall hb hbw
  have hs1 : -1 < s0R V₀c b m := by linarith [(hsb m hm.le).1]
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith [HF.lbar_pos]
  have hreal := Suscept.im_eq_zero_V0c (L := L) hd1 hL3 HW.conj N m b
  have hut : Suscept.utN d L N m (V₀c m b) = ((Suscept.utN d L N m (V₀c m b)).re : ℂ) :=
    (ofReal_re_of_im hreal.2.2.2.2).symm
  have hu : Suscept.uN d L N m (V₀c m b) = ((Suscept.uN d L N m (V₀c m b)).re : ℂ) :=
    (ofReal_re_of_im hreal.1).symm
  refine ⟨hut, ?_⟩
  have e1 := expect_one_eq (d := d) (L := L) (N := N) HW.conj hb hs1 hm
  rw [ZM_eq (HF.hb m b), Suscept.EC_Z0 hd1 HF.hL8 hN hm (HF.good N m hm.le), hu, hut] at e1
  have hZ := expect_one_pos_nnW (d := d) (L := L) (N := N) (hβpos m hm.le).le (hhnn m hm.le)
  set Q := (betaF V₀c b m / (1 + s0R V₀c b m)) ^ Fintype.card (Lam d L N) *
    (FRD.negLap + m • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det
  have hQ : 0 < Q := mul_pos (pow_pos (div_pos (hβpos m hm.le) (by linarith)) _)
    (FRD.det_negLap_add_pos hm)
  have e2 : H02.expect (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) 1 =
      Q * Real.exp (-((Suscept.uN d L N m (V₀c m b)).re * Fintype.card (Lam d L N))) *
        (1 + (Suscept.utN d L N m (V₀c m b)).re) := by
    have : ((H02.expect (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) 1 : ℝ) : ℂ) =
        ((Q * Real.exp (-((Suscept.uN d L N m (V₀c m b)).re * Fintype.card (Lam d L N))) *
          (1 + (Suscept.utN d L N m (V₀c m b)).re) : ℝ) : ℂ) := by
      rw [e1]; push_cast; ring
    exact_mod_cast this
  rw [e2] at hZ
  have hE := Real.exp_pos (-((Suscept.uN d L N m (V₀c m b)).re * Fintype.card (Lam d L N)))
  by_contra hc
  rw [not_lt] at hc
  nlinarith [mul_pos hQ hE]

set_option maxHeartbeats 4000000 in
/-- `m²(1 + ũ_{N,N}(m²)) → ã_{N,N}(0)` as `m² ↓ 0`. -/
theorem fv_D_tendsto (N : ℕ) :
    Tendsto (fun m => m * (1 + (Suscept.utN d L N m (V₀c m b)).re)) (𝓝[>] 0)
      (𝓝 (atR d L V₀c N b)) := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hbn : ‖(b : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith [HF.lbar_pos]
  obtain ⟨-, -, ck, -, ca, -⟩ := Suscept.prop_ZNN_cont (N := N) hd1 HF.hL8 (ℓ₀ := ℓ₀)
    subset_rfl (HF.cv hbn) (fun m hm j hj => HF.good N m hm j hj)
  have tends : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Ici 0) →
      Tendsto (fun m => (f m).re) (𝓝[>] 0) (𝓝 (f 0).re) := fun hf =>
    (Complex.continuous_re.tendsto _).comp
      (((hf 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto)
  have hid : Tendsto (fun m : ℝ => m) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  have h := (hid.add (hid.mul (tends ck))).add ((tends ca).mul (fv_mt_tendsto (L := L) hd1 N))
  simp only [zero_mul, zero_add, mul_one] at h
  refine h.congr fun m => ?_
  simp only [Suscept.utN, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

end Fixed

end

end Ward
