import Flow2.Shoot

/-!
# Shooting at fixed `β_R`: the local continuation of the admissible `μ₀`

The existence of the admissible `μ₀(b)` in `Flow2.History` / `Flow2.RangeKeep` is an
intermediate value argument in `μ₀` for the *clamped* flow, and needs *every* clamped trajectory
from `b` to stay in `D_ε` (`KeepD`). By the unsigned history-dependent `c_g g³` error of (F1) this
holds only for `1/b ≥ 1/ε + β N + O(1) + O(log(1 + βNε))`, so the final coupling of the
admissible flow reaches only `1/ǧ_N ≥ 1/ε + O(log(1 + βNε))`.

Here the existence is obtained by **continuation in `b`** instead. Only the admissible trajectory
itself (and its neighbours) has to stay in `D_ε`, and since the coupling is nondecreasing, this is
controlled by the final coupling `ǧ_N` alone.

* `adm_strict`: along an admissible trajectory `|μ_j| < c_μ g_j` (the faces `μ = ± c_μ g` are
  forward invariant, and `μ_N = 0`);
* `OKR`: the open condition `0 < b`, `g_j < y`, `|μ_j| < c_μ g_j` (`j ≤ N`) on the *unclamped*
  flow; for `y ≤ ε` it implies that the trajectory is a regular history in `D_ε`
  (`inDh_of_OKR`);
* `cone_signed`: the cone argument of `admissible_unique` with signs: two trajectories in `D_ε`
  from the same `b` with `μ' ≤ μ` have `μ - μ' ≤ μ_N - μ'_N`;
* `local_adm`: if `μ₁` is admissible for `b₁` with `ǧ_N < y ≤ ε`, then every `b` near `b₁` has
  an admissible `μ` near `μ₁` with `ǧ_N < y` (intermediate value theorem in `μ` on a small
  interval around `μ₁`, with the signs from `cone_signed`);
* `muc_eq_of_adm`, `continuousAt_muc_fixed`, `continuousAt_gN_fixed`, `isOpen_Ufix`: the set
  `Ufix` of `b` with an admissible trajectory and `ǧ_N < ε` is open, and `μ₀(b)`, `ǧ_N(b)` are
  continuous on it.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

variable (F Λ cm) in
/-- The open condition at the target `y`: `0 < b` and `g_j < y`, `|μ_j| < c_μ g_j` for `j ≤ N`
along the (unclamped) flow from `(b, μ)`. -/
def OKR (N : ℕ) (y b μ : ℝ) : Prop :=
  0 < b ∧ ∀ j ≤ N, (traj F Λ b μ j).1 < y ∧
    |(traj F Λ b μ j).2.1| < cmu Λ cm * (traj F Λ b μ j).1

variable (F Λ κ cm cT) in
/-- The initial couplings with an admissible trajectory and `ǧ_N < ε`. -/
def Ufix (N : ℕ) (ε : ℝ) : Set ℝ :=
  {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ ∧ (traj F Λ b μ N).1 < ε}

section Local

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
include H

/-- The unclamped flow is continuous in `(b, μ₀)`. -/
lemma continuous_traj {j : ℕ} (hj : j ≤ N) :
    Continuous (fun p : ℝ × ℝ => traj F Λ p.1 p.2 j) := by
  refine continuous_tr (s0 := fun p : ℝ × ℝ => fun _ => (p.1, p.2, 0))
    (stepS F Λ) ?_ (fun k hk => ?_) hj
  · exact continuous_pi fun _ => continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  · have hG := H.contG k hk
    have hm := H.contm k hk
    have hT := H.contT k hk
    exact hG.prodMk (((continuous_const.mul
      (continuous_fst.comp (continuous_snd.comp (continuous_apply k)))).add hm).prodMk hT)

lemma continuous_traj_mu (b : ℝ) : Continuous (fun μ => (traj F Λ b μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_traj H le_rfl))).comp
    (continuous_const.prodMk continuous_id)

lemma continuous_traj_b (μ : ℝ) : Continuous (fun b => (traj F Λ b μ N).2.1) :=
  (continuous_fst.comp (continuous_snd.comp (continuous_traj H le_rfl))).comp
    (continuous_id.prodMk continuous_const)

variable (he : ε ≤ eps0u Λ β δ κ cg cm)
include he

/-- On the upper face `μ = c_μ g` the unclamped step leaves `[-c_μ G, c_μ G]` upwards. -/
lemma top_ineq {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (htop : (t j).2.1 = cmu Λ cm * (t j).1) :
    cmu Λ cm * F.G j t ≤ Λ * (t j).2.1 + F.m j t := by
  have hm := (abs_le.1 (H.F2 j hj t ht)).1
  have hcm := cmu_mul (c := cm) H.hΛ
  have hG := cmu_G_le H he hj ht
  rw [htop]
  have e : cmu Λ cm * (t j).1 * Λ = cmu Λ cm * (t j).1 + 2 * cm * (t j).1 := by
    linear_combination (t j).1 * hcm
  linarith

/-- On the lower face `μ = -c_μ g` the unclamped step leaves `[-c_μ G, c_μ G]` downwards. -/
lemma bot_ineq {j : ℕ} (hj : j < N) {t : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (hbot : (t j).2.1 = -(cmu Λ cm * (t j).1)) :
    Λ * (t j).2.1 + F.m j t ≤ -(cmu Λ cm * F.G j t) := by
  have hm := (abs_le.1 (H.F2 j hj t ht)).2
  have hcm := cmu_mul (c := cm) H.hΛ
  have hG := cmu_G_le H he hj ht
  rw [hbot]
  have e : cmu Λ cm * (t j).1 * Λ = cmu Λ cm * (t j).1 + 2 * cm * (t j).1 := by
    linear_combination (t j).1 * hcm
  linarith

lemma adm_top {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {k : ℕ}
    (hk : (traj F Λ b μ₀ k).2.1 = cmu Λ cm * (traj F Λ b μ₀ k).1) :
    ∀ j, k ≤ j → j ≤ N → (traj F Λ b μ₀ j).2.1 = cmu Λ cm * (traj F Λ b μ₀ j).1 := by
  intro j
  induction j with
  | zero => intro h1 _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    have hD := h.1 (j + 1) h2
    have hs := admissible_InDh H h j (by omega)
    have hup := (abs_le.1 hD.2.2.1).2
    have hlow := top_ineq H he (by omega : j < N) hs (ih h1' (by omega))
    rw [traj_succ H b μ₀ (by omega)] at hup ⊢
    exact le_antisymm hup hlow

lemma adm_bot {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {k : ℕ}
    (hk : (traj F Λ b μ₀ k).2.1 = -(cmu Λ cm * (traj F Λ b μ₀ k).1)) :
    ∀ j, k ≤ j → j ≤ N → (traj F Λ b μ₀ j).2.1 = -(cmu Λ cm * (traj F Λ b μ₀ j).1) := by
  intro j
  induction j with
  | zero => intro h1 _; obtain rfl : k = 0 := by omega
            exact hk
  | succ j ih =>
    intro h1 h2
    rcases (show k = j + 1 ∨ k ≤ j by omega) with rfl | h1'
    · exact hk
    have hD := h.1 (j + 1) h2
    have hs := admissible_InDh H h j (by omega)
    have hlo := (abs_le.1 hD.2.2.1).1
    have hup := bot_ineq H he (by omega : j < N) hs (ih h1' (by omega))
    rw [traj_succ H b μ₀ (by omega)] at hlo ⊢
    exact le_antisymm hup hlo

/-- Along an admissible trajectory `|μ_j| < c_μ g_j`. -/
lemma adm_strict {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) :
    ∀ k ≤ N, |(traj F Λ b μ₀ k).2.1| < cmu Λ cm * (traj F Λ b μ₀ k).1 := by
  intro k hk
  have hD := h.1 k hk
  have hN := h.1 N le_rfl
  have hcp := cmu_pos H.hΛ H.hcm
  have hpos : 0 < cmu Λ cm * (traj F Λ b μ₀ N).1 := mul_pos hcp hN.1
  rcases hD.2.2.1.lt_or_eq with h' | h'
  · exact h'
  exfalso
  rcases (abs_eq (mul_nonneg hcp.le hD.1.le)).1 h' with h'' | h''
  · have := adm_top H he h h'' N hk le_rfl
    rw [h.2] at this; linarith
  · have := adm_bot H he h h'' N hk le_rfl
    rw [h.2] at this; linarith

omit he in
/-- The coupling at `j ≤ N` is at most the final one. -/
lemma traj_le_N (hgβ : cg * ε ≤ (1 - δ) * β) {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) :
    ∀ j ≤ N, (traj F Λ b μ₀ j).1 ≤ (traj F Λ b μ₀ N).1 := by
  have key : ∀ m j, j + m ≤ N → (traj F Λ b μ₀ j).1 ≤ (traj F Λ b μ₀ (j + m)).1 := by
    intro m
    induction m with
    | zero => intro j _; exact le_rfl
    | succ m ih =>
      intro j hj
      exact (ih j (by omega)).trans (traj_fst_mono H hgβ h (by omega : j + m < N))
  intro j hj
  have := key (N - j) j (by omega)
  rwa [Nat.add_sub_cancel' hj] at this

/-- An admissible trajectory with `ǧ_N < y` satisfies the open condition `OKR`. -/
lemma OKR_of_adm (hgβ : cg * ε ≤ (1 - δ) * β) {y b μ₀ : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μ₀) (hy : (traj F Λ b μ₀ N).1 < y) :
    OKR F Λ cm N y b μ₀ := by
  refine ⟨?_, fun j hj => ⟨(traj_le_N H hgβ h j hj).trans_lt hy, adm_strict H he h j hj⟩⟩
  have := (h.1 0 (Nat.zero_le _)).1
  rwa [traj_zero] at this

/-- `OKR` at a target `y ≤ ε` keeps the flow in `D_ε`. -/
lemma inDh_of_OKR {y b μ : ℝ} (hy : y ≤ ε) (hO : OKR F Λ cm N y b μ) :
    ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 := hO.2 0 (Nat.zero_le _)
    rw [traj_zero] at h0
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    obtain rfl : i = 0 := by omega
    rw [traj_zero]
    exact ⟨hO.1, h0.1.le.trans hy, h0.2.le, by
      simp only [norm_zero]; exact mul_nonneg (cx_pos H.hκ1 H.hcT).le (by
        have := hO.1; positivity)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    have h1 := hO.2 (j + 1) hj
    rw [traj_succ H b μ (by omega)] at h1
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
      · rw [traj_succ H b μ (by omega)]
        exact step_InD H he (by omega) hs (h1.1.le.trans hy) h1.2.le
      · exact hs.1 i hij
    · rcases (show i = j ∨ i < j by omega) with rfl | hij
      · rw [traj_succ H b μ (by omega)]; exact H.F1 i (by omega) _ hs
      · exact hs.2 i hij

/-- `OKR` with `μ_N = 0` is admissibility. -/
lemma adm_of_OKR {y b μ : ℝ} (hy : y ≤ ε) (hO : OKR F Λ cm N y b μ)
    (h0 : (traj F Λ b μ N).2.1 = 0) : Admissible F Λ κ cm cT N ε b μ :=
  ⟨fun j hj => (inDh_of_OKR H he hy hO j hj).1 j le_rfl, h0⟩

end Local

/-! ### The signed cone -/

section Cone

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
include H

/-- One step of the signed cone: `δμ ≥ 0` in the cone gives `δμ' ≥ δμ`. -/
lemma step_signed {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * (1 + p + q)))
    {j : ℕ} (hj : j < N) {t t' : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (ht' : InDh Λ β δ κ cg cm cT ε j t') (hd : 0 ≤ (t j).2.1 - (t' j).2.1)
    (hg : |(t j).1 - (t' j).1| ≤ p * |(t j).2.1 - (t' j).2.1|)
    (hx : ‖(t j).2.2 - (t' j).2.2‖ ≤ q * |(t j).2.1 - (t' j).2.1|)
    (hh : ∀ i < j, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t j).2.1 - (t' j).2.1|) :
    (t j).2.1 - (t' j).2.1 ≤ Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t') := by
  have hM : 0 ≤ (1 + p + q) * |(t j).2.1 - (t' j).2.1| := by positivity
  have Lm := H.Lm j hj t t' ht ht' _ hM hh
  rw [abs_of_nonneg hd] at hg hx Lm
  have hm := (abs_le.1 Lm).1
  have a1 : A * |(t j).1 - (t' j).1| ≤ A * (p * ((t j).2.1 - (t' j).2.1)) :=
    mul_le_mul_of_nonneg_left hg H.hA
  have a2 : A * ‖(t j).2.2 - (t' j).2.2‖ ≤ A * (q * ((t j).2.1 - (t' j).2.1)) :=
    mul_le_mul_of_nonneg_left hx H.hA
  have b1 := mul_le_mul_of_nonneg_right em hd
  have b2 : 0 ≤ (Λ - 1) / 2 * ((t j).2.1 - (t' j).2.1) :=
    mul_nonneg (by linarith [H.hΛ]) hd
  linarith

variable (ha0 : a ≤ a0h Λ κ A)
include ha0

/-- **The signed cone**: two trajectories in `D_ε` from the same `b` with `μ' ≤ μ` have
`μ - μ' ≤ μ_N - μ'_N`. -/
theorem cone_signed {b μ μ' : ℝ} (hμ : μ' ≤ μ)
    (h : ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ))
    (h' : ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ')) :
    μ - μ' ≤ (traj F Λ b μ N).2.1 - (traj F Λ b μ' N).2.1 := by
  obtain ⟨hp0, hq0, eg, ex, em⟩ := coef_h H.hΛ H.hκ1 H.hA H.ha ha0
  set p := Kh Λ κ A * a
  set q := Qh κ * a
  set t := traj F Λ b μ
  set t' := traj F Λ b μ'
  have key : ∀ k ≤ N,
      |(t k).1 - (t' k).1| ≤ p * |(t k).2.1 - (t' k).2.1| ∧
      ‖(t k).2.2 - (t' k).2.2‖ ≤ q * |(t k).2.1 - (t' k).2.1| ∧
      (∀ i < k, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t k).2.1 - (t' k).2.1|) ∧
      μ - μ' ≤ (t k).2.1 - (t' k).2.1 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [t, t', traj_zero, sub_self, abs_zero, norm_zero, le_refl, and_true]
      exact ⟨mul_nonneg hp0 (abs_nonneg _), mul_nonneg hq0 (abs_nonneg _),
        fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨ig, ix, ih', iμ⟩ := ih (by omega)
      have hd : 0 ≤ (t k).2.1 - (t' k).2.1 := by linarith
      obtain ⟨s1, s2, s3, s4⟩ := unique_step H hp0 hq0 eg ex em hkN
        (h k (by omega)) (h' k (by omega)) ig ix ih'
      have s5 := step_signed H hp0 hq0 em hkN (h k (by omega)) (h' k (by omega)) hd ig ix ih'
      have e0 := traj_succ H b μ hkN
      have e1 := traj_succ H b μ' hkN
      simp only [t, t'] at s1 s2 s3 s4 s5 ih' ig ix iμ hd ⊢
      rw [e0, e1]
      refine ⟨s2, s3, fun i hi => ?_, iμ.trans s5⟩
      rcases (show i = k ∨ i < k by omega) with rfl | hik
      · have : dist3 (traj F Λ b μ i) (traj F Λ b μ' i) ≤
            (1 + p + q) * |(traj F Λ b μ i).2.1 - (traj F Λ b μ' i).2.1| := by
          unfold dist3
          nlinarith [abs_nonneg ((traj F Λ b μ i).2.1 - (traj F Λ b μ' i).2.1)]
        exact this.trans (mul_le_mul_of_nonneg_left s4 (by positivity))
      · exact (ih' i hik).trans (mul_le_mul_of_nonneg_left s4 (by positivity))
  exact (key N le_rfl).2.2.2

end Cone

end Hist

end Flow2
