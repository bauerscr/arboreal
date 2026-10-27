import Flow2.History

/-!
# The fixed-point machinery of `prop:C6` on an abstract range of initial couplings

In `Flow2.History`, the range `b ∈ (0, b_max]` enters the existence, uniqueness and continuity
of the admissible `μ₀(b)` only through the a priori bound `trajc_InDh`: *every* clamped
trajectory from `b` is a regular history in `D_ε` up to `N`. Here this property is isolated
(`KeepD`), and the existence (`exists_admissibleK`), the characterisation of `muc`
(`muc_specK`, `eq_mucK`), the continuity of `muc`, `gN` (`continuousOn_mucK`,
`continuousOn_gNK`) and shooting (`shootingK`) are proved on any set of `b` with `KeepD`.
`keepD_of_bmax` recovers the range `(0, b_max]` of `Flow2.History`; `Flow2.RangeSharp` gives
a much larger range from the sharp marginal flow.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]

variable (F : HData X) (Λ β δ κ cg cm cT : ℝ) in
/-- The a priori property of an initial coupling `b`: every clamped trajectory from `b` is a
regular history in `D_ε` up to `N`. -/
def KeepD (N : ℕ) (ε b : ℝ) : Prop :=
  0 < b ∧ ∀ μ₀ : ℝ, ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (trajc F Λ cm b μ₀)

variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

section Keep

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) (he : ε ≤ eps0u Λ β δ κ cg cm)
  (hε : 0 < ε)
include H he

omit H he in
lemma trajc_InDK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) (μ₀ : ℝ) {j : ℕ} (hj : j ≤ N) :
    InD3 Λ κ cm cT ε (trajc F Λ cm b μ₀ j) :=
  (hb.2 μ₀ j hj).1 j le_rfl

lemma trajc_topK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) (μ₀ : ℝ) {k : ℕ}
    (hk : (trajc F Λ cm b μ₀ k).2.1 = cmu Λ cm * (trajc F Λ cm b μ₀ k).1) :
    ∀ j, k ≤ j → j ≤ N → (trajc F Λ cm b μ₀ j).2.1 = cmu Λ cm * (trajc F Λ cm b μ₀ j).1 := by
  intro j
  induction j with
  | zero => intro h _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    rw [trajc_succ H b μ₀ (by omega)]
    exact top_step H he (by omega) (hb.2 μ₀ j (by omega)) (ih h1' (by omega))

lemma trajc_botK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) (μ₀ : ℝ) {k : ℕ}
    (hk : (trajc F Λ cm b μ₀ k).2.1 = -(cmu Λ cm * (trajc F Λ cm b μ₀ k).1)) :
    ∀ j, k ≤ j → j ≤ N → (trajc F Λ cm b μ₀ j).2.1 = -(cmu Λ cm * (trajc F Λ cm b μ₀ j).1) := by
  intro j
  induction j with
  | zero => intro h _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    rw [trajc_succ H b μ₀ (by omega)]
    exact bot_step H he (by omega) (hb.2 μ₀ j (by omega)) (ih h1' (by omega))

lemma trajc_strictK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) {μ₀ : ℝ}
    (h0 : (trajc F Λ cm b μ₀ N).2.1 = 0) :
    ∀ k ≤ N, |(trajc F Λ cm b μ₀ k).2.1| < cmu Λ cm * (trajc F Λ cm b μ₀ k).1 := by
  intro k hk
  have hD := trajc_InDK hb μ₀ hk
  have hN := trajc_InDK hb μ₀ (le_refl N)
  have hcp := cmu_pos H.hΛ H.hcm
  have hpos : 0 < cmu Λ cm * (trajc F Λ cm b μ₀ N).1 := mul_pos hcp hN.1
  rcases hD.2.2.1.lt_or_eq with h | h
  · exact h
  exfalso
  rcases (abs_eq (mul_nonneg hcp.le hD.1.le)).1 h with h' | h'
  · have := trajc_topK H he hb μ₀ h' N hk le_rfl; linarith
  · have := trajc_botK H he hb μ₀ h' N hk le_rfl; linarith

lemma admissible_of_zeroK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) {μ₀ : ℝ}
    (h0 : (trajc F Λ cm b μ₀ N).2.1 = 0) : Admissible F Λ κ cm cT N ε b μ₀ := by
  have hs := trajc_strictK H he hb h0
  have e : ∀ k ≤ N, ∀ i ≤ k, trajc F Λ cm b μ₀ i = traj F Λ b μ₀ i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      obtain rfl : i = 0 := by omega
      have h := hs 0 (Nat.zero_le _)
      rw [trajc_zero, traj_zero, clamp_eq_of_abs_lt (r := cmu Λ cm * b) h]
    | succ k ih =>
      intro hk i hi
      rcases (show i = k + 1 ∨ i ≤ k by omega) with rfl | hik
      · have hall := ih (by omega)
        have h := hs (k + 1) hk
        have hkN : k < N := by omega
        rw [trajc_succ H b μ₀ hkN] at h ⊢
        rw [clamp_eq_of_abs_lt h, traj_succ H b μ₀ hkN, H.causG k hkN _ _ hall,
          H.causm k hkN _ _ hall, H.causT k hkN _ _ hall, hall k le_rfl]
      · exact ih (by omega) i hik
  refine ⟨fun k hk => e N le_rfl k hk ▸ trajc_InDK hb μ₀ hk, ?_⟩
  rw [← e N le_rfl N le_rfl]; exact h0

lemma phi_pos_of_geK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) {μ₀ : ℝ}
    (h : cmu Λ cm * b ≤ μ₀) : 0 < (trajc F Λ cm b μ₀ N).2.1 := by
  have hcp := cmu_pos H.hΛ H.hcm
  have h0 : (trajc F Λ cm b μ₀ 0).2.1 = cmu Λ cm * (trajc F Λ cm b μ₀ 0).1 :=
    clamp_of_le (mul_nonneg hcp.le hb.1.le) h
  rw [trajc_topK H he hb μ₀ h0 N (Nat.zero_le _) le_rfl]
  exact mul_pos hcp (trajc_InDK hb μ₀ (le_refl N)).1

lemma phi_neg_of_leK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) {μ₀ : ℝ}
    (h : μ₀ ≤ -(cmu Λ cm * b)) : (trajc F Λ cm b μ₀ N).2.1 < 0 := by
  have hcp := cmu_pos H.hΛ H.hcm
  have h0 : (trajc F Λ cm b μ₀ 0).2.1 = -(cmu Λ cm * (trajc F Λ cm b μ₀ 0).1) :=
    clamp_of_le' (mul_nonneg hcp.le hb.1.le) h
  rw [trajc_botK H he hb μ₀ h0 N (Nat.zero_le _) le_rfl]
  have := mul_pos hcp (trajc_InDK hb μ₀ (le_refl N)).1
  linarith

/-- **Existence** on the range `KeepD`. -/
theorem exists_admissibleK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) :
    ∃ μ₀, Admissible F Λ κ cm cT N ε b μ₀ := by
  have hr : 0 ≤ cmu Λ cm * b := mul_nonneg (cmu_pos H.hΛ H.hcm).le hb.1.le
  obtain ⟨μ₀, -, hμ⟩ := intermediate_value_Icc (by linarith : -(cmu Λ cm * b) ≤ cmu Λ cm * b)
    (continuous_phi H b).continuousOn
    ⟨(phi_neg_of_leK H he hb le_rfl).le, (phi_pos_of_geK H he hb le_rfl).le⟩
  exact ⟨μ₀, admissible_of_zeroK H he hb hμ⟩

lemma muc_specK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) :
    Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := by
  have h := exists_admissibleK H he hb
  simp only [muc, dif_pos h]
  exact h.choose_spec

variable (ha0 : a ≤ a0h Λ κ A)
include ha0

lemma eq_mucK {b μ₀ : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b)
    (h : Admissible F Λ κ cm cT N ε b μ₀) : μ₀ = muc F Λ κ cm cT N ε b :=
  admissible_unique H ha0 h (muc_specK H he hb)

lemma phi_pos_of_gtK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) {μ : ℝ}
    (h : muc F Λ κ cm cT N ε b < μ) : 0 < (trajc F Λ cm b μ N).2.1 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (le_max_left μ (cmu Λ cm * b))
    (continuous_phi H b).continuousOn ⟨hn, (phi_pos_of_geK H he hb (le_max_right _ _)).le⟩
  have := eq_mucK H he ha0 hb (admissible_of_zeroK H he hb hz)
  linarith [hmem.1]

lemma phi_neg_of_ltK {b : ℝ} (hb : KeepD F Λ β δ κ cg cm cT N ε b) {μ : ℝ}
    (h : μ < muc F Λ κ cm cT N ε b) : (trajc F Λ cm b μ N).2.1 < 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (min_le_left μ (-(cmu Λ cm * b)))
    (continuous_phi H b).continuousOn ⟨(phi_neg_of_leK H he hb (min_le_right _ _)).le, hn⟩
  have := eq_mucK H he ha0 hb (admissible_of_zeroK H he hb hz)
  linarith [hmem.2]

/-- **Continuity of `μ₀(b)`** on any set of initial couplings with `KeepD`. -/
theorem continuousOn_mucK {S : Set ℝ} (hS : ∀ b ∈ S, KeepD F Λ β δ κ cg cm cT N ε b) :
    ContinuousOn (muc F Λ κ cm cT N ε) S := by
  intro b hb
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro η hη
  obtain ⟨μs, hμs⟩ : ∃ μs, μs = muc F Λ κ cm cT N ε b := ⟨_, rfl⟩
  have hp := phi_pos_of_gtK H he ha0 (hS b hb) (show muc F Λ κ cm cT N ε b < μs + η / 2 by
    rw [← hμs]; linarith)
  have hn := phi_neg_of_ltK H he ha0 (hS b hb) (show μs - η / 2 < muc F Λ κ cm cT N ε b by
    rw [← hμs]; linarith)
  have e1 : ∀ᶠ b' in 𝓝 b, 0 < (trajc F Λ cm b' (μs + η / 2) N).2.1 :=
    (continuous_phi' H _).continuousAt.eventually (lt_mem_nhds hp)
  have e2 : ∀ᶠ b' in 𝓝 b, (trajc F Λ cm b' (μs - η / 2) N).2.1 < 0 :=
    (continuous_phi' H _).continuousAt.eventually (gt_mem_nhds hn)
  filter_upwards [eventually_mem_nhdsWithin, (e1.and e2).filter_mono nhdsWithin_le_nhds]
    with b' hb' ⟨h1, h2⟩
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (by linarith : μs - η / 2 ≤ μs + η / 2)
    (continuous_phi H b').continuousOn ⟨h2.le, h1.le⟩
  have := eq_mucK H he ha0 (hS b' hb') (admissible_of_zeroK H he (hS b' hb') hz)
  rw [Real.dist_eq, ← this, ← hμs, abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **Continuity of `ǧ_N(b)`** on any set of initial couplings with `KeepD`. -/
theorem continuousOn_gNK {S : Set ℝ} (hS : ∀ b ∈ S, KeepD F Λ β δ κ cg cm cT N ε b) :
    ContinuousOn (gN F Λ κ cm cT N ε) S := by
  have h : ContinuousOn (fun b => (trajc F Λ cm b (muc F Λ κ cm cT N ε b) N).1) S :=
    (continuous_fst.comp (continuous_trajc H le_rfl)).comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_mucK H he ha0 hS))
  refine h.congr fun b hb => ?_
  simp only [gN]
  rw [trajc_eq_traj H (muc_specK H he (hS b hb)) N le_rfl N le_rfl]

/-- **Shooting** on an order-connected set of initial couplings with `KeepD`. -/
theorem shootingK {S : Set ℝ} (hS : ∀ b ∈ S, KeepD F Λ β δ κ cg cm cT N ε b) (hSc : S.OrdConnected)
    {b₁ b₂ : ℝ} (h₁ : b₁ ∈ S) (h₂ : b₂ ∈ S) {y : ℝ}
    (hy : y ∈ uIcc (gN F Λ κ cm cT N ε b₁) (gN F Λ κ cm cT N ε b₂)) :
    ∃ b ∈ uIcc b₁ b₂, gN F Λ κ cm cT N ε b = y :=
  intermediate_value_uIcc ((continuousOn_gNK H he ha0 hS).mono (hSc.uIcc_subset h₁ h₂)) hy

/-- **`prop:C6` on the range `KeepD`**: existence and uniqueness of the admissible `μ₀`, and
continuity of `μ₀(b)` and `ǧ_N(b)`, on any set `S` of initial couplings with `KeepD`. -/
theorem fh_flow_histK {S : Set ℝ} (hS : ∀ b ∈ S, KeepD F Λ β δ κ cg cm cT N ε b) :
    (∀ b ∈ S, ∃! μ₀, Admissible F Λ κ cm cT N ε b μ₀) ∧
    ContinuousOn (muc F Λ κ cm cT N ε) S ∧ ContinuousOn (gN F Λ κ cm cT N ε) S := by
  refine ⟨fun b hb => ?_, continuousOn_mucK H he ha0 hS, continuousOn_gNK H he ha0 hS⟩
  obtain ⟨μ₀, h⟩ := exists_admissibleK H he (hS b hb)
  exact ⟨μ₀, h, fun μ₁ h₁ => admissible_unique H ha0 h₁ h⟩

end Keep

end Hist

end Flow2
