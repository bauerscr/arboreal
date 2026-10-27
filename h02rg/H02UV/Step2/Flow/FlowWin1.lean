import Flow2.FixedRParamG1
import Flow2.Complete2

/-!
# Windowed flow: a shifted final condition `μ_N = c'` (route (a1), task 2, abstract part)

`Admissible` fixes the final condition `μ_N = 0`. Route (a1) replaces it by the window
`|μ_N| ≤ c ǧ_N`. Here the target is a parameter: `AdmW … b μ₀ c'` means "in `D_ε` up to `N` and
`μ_N = c'`" (`AdmW … 0 = Admissible`, `admW_zero_iff`). The per-step hypotheses (`HHyp`,
`ZHyp`, `MonoZHyp`) are unchanged; only the statements that used `μ_N = 0` are re-proved.

* `traj_fst_mono_D`, `traj_le_N_D`, `face_top_D`, `face_bot_D`, **`strict_of_D`** (`adm_strict`
  for any trajectory in `D_ε` with `|μ_N| < c_μ g_N`), **`admW_strict`**, `inDh_of_OKRc`
  (closed version of `inDh_of_OKR`), `OKR_of_D_lt`, `admW_of_OKR`.
* Uniqueness: **`unique_of_coneS_W`** (same `b`, same target), **`expand_W`** (`|μ₀ - μ₁| ≤
  |c - c'|`), **`mono_W`** (`c < c'` ⇒ `μ₀(c) < μ₀(c')`).
* `ConeSG p`: the signed cone with the `ǧ`-part `|δǧ_N| ≤ p δμ_N`; **`coneSG_of_Z`** (copy of
  `cone_signed_z` returning the `ǧ`-part), `ConeSG.coneS`.
* Existence by continuation in the target at fixed `b`: **`win_up`**, **`win_down`**: from a
  point with target `c₀` to every target `c₁` (above/below) with `ǧ_N` controlled, together with
  the whole segment of initial data in between; **`win_interval`**: around an admissible
  `μ₀^c` (target `0`) the window `[μ₋, μ₊]` of initial data with targets `c₋ ≤ 0 ≤ c₊`.
* Same-target versions of the `ǧ`-cone: **`not_mu_cone_zD`**, **`traj_cone_top_zD`**
  (`traj_cone_top_z` for two trajectories in `D_ε` with equal final `μ_N`),
  **`traj_cone_top_zW`**, **`traj_strict_mono_zW`**.
* `win_sym_conds`: the symmetric window `∓c₁`, `c₁ ≤ θǧ`, from `θ(1 + 2pc_μ) < c_μ`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {E : Type*} [NormedAddCommGroup E]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

variable (F Λ κ cm cT) in
/-- **Windowed admissibility with target `c`**: in `D_ε` up to `N` and `μ_N = c`. -/
def AdmW (N : ℕ) (ε b μ₀ c : ℝ) : Prop :=
  (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) ∧ (traj F Λ b μ₀ N).2.1 = c

variable (F Λ cm) in
/-- The closed version of `OKR` (without `0 < b`). -/
def OKRc (N : ℕ) (y b μ : ℝ) : Prop :=
  ∀ j ≤ N, (traj F Λ b μ j).1 ≤ y ∧ |(traj F Λ b μ j).2.1| ≤ cmu Λ cm * (traj F Λ b μ j).1

variable (F Λ β δ κ cg cm cT) in
/-- **The signed cone with its `ǧ`-part** (as a hypothesis). -/
def ConeSG (N : ℕ) (ε p : ℝ) : Prop :=
  ∀ b μ μ', μ' ≤ μ → (∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ)) →
    (∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ')) →
    μ - μ' ≤ (traj F Λ b μ N).2.1 - (traj F Λ b μ' N).2.1 ∧
    |(traj F Λ b μ N).1 - (traj F Λ b μ' N).1| ≤
      p * ((traj F Λ b μ N).2.1 - (traj F Λ b μ' N).2.1)

/-! ### The domain without the final condition -/

section Dom

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
include H

lemma traj_fst_mono_D (hgβ : cg * ε ≤ (1 - δ) * β) {b μ₀ : ℝ}
    (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) {j : ℕ} (hj : j < N) :
    (traj F Λ b μ₀ j).1 ≤ (traj F Λ b μ₀ (j + 1)).1 := by
  have ht : InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := traj_InDh_of H h j hj.le
  have hF1 := (abs_le.1 (H.F1 j hj _ ht)).1
  rw [traj_succ H b μ₀ hj]
  show (traj F Λ b μ₀ j).1 ≤ F.G j (traj F Λ b μ₀)
  have hs := ht.1 j le_rfl
  set g := (traj F Λ b μ₀ j).1
  have hgε := hs.2.1
  have h1 : cg * g ≤ (1 - δ) * β := le_trans (mul_le_mul_of_nonneg_left hgε H.hcg.le) hgβ
  have h2 : 0 ≤ g ^ 2 * ((1 - δ) * β - cg * g) :=
    mul_nonneg (sq_nonneg g) (by linarith only [h1])
  have e : g ^ 2 * ((1 - δ) * β - cg * g) = β * g ^ 2 - (δ * β * g ^ 2 + cg * g ^ 3) := by ring
  linarith only [hF1, h2, e]

lemma traj_le_N_D (hgβ : cg * ε ≤ (1 - δ) * β) {b μ₀ : ℝ}
    (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) :
    ∀ j ≤ N, (traj F Λ b μ₀ j).1 ≤ (traj F Λ b μ₀ N).1 := by
  have key : ∀ m j, j + m ≤ N → (traj F Λ b μ₀ j).1 ≤ (traj F Λ b μ₀ (j + m)).1 := by
    intro m
    induction m with
    | zero => intro j _; exact le_rfl
    | succ m ih =>
      intro j hj
      exact (ih j (by omega)).trans (traj_fst_mono_D H hgβ h (by omega : j + m < N))
  intro j hj
  have := key (N - j) j (by omega)
  rwa [Nat.add_sub_cancel' hj] at this

variable (he : ε ≤ eps0u Λ β δ κ cg cm)
include he

lemma face_top_D {b μ₀ : ℝ} (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) {k : ℕ}
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
    have hD := h (j + 1) h2
    have hs := traj_InDh_of H h j (by omega)
    have hup := (abs_le.1 hD.2.2.1).2
    have hlow := top_ineq H he (by omega : j < N) hs (ih h1' (by omega))
    rw [traj_succ H b μ₀ (by omega)] at hup ⊢
    exact le_antisymm hup hlow

lemma face_bot_D {b μ₀ : ℝ} (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) {k : ℕ}
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
    have hD := h (j + 1) h2
    have hs := traj_InDh_of H h j (by omega)
    have hlo := (abs_le.1 hD.2.2.1).1
    have hup := bot_ineq H he (by omega : j < N) hs (ih h1' (by omega))
    rw [traj_succ H b μ₀ (by omega)] at hlo ⊢
    exact le_antisymm hup hlo

/-- **`adm_strict` without the final condition**: in `D_ε` with `|μ_N| < c_μ g_N`, all
`|μ_k| < c_μ g_k`. -/
lemma strict_of_D {b μ₀ : ℝ} (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j))
    (hN : |(traj F Λ b μ₀ N).2.1| < cmu Λ cm * (traj F Λ b μ₀ N).1) :
    ∀ k ≤ N, |(traj F Λ b μ₀ k).2.1| < cmu Λ cm * (traj F Λ b μ₀ k).1 := by
  intro k hk
  have hD := h k hk
  have hcp := cmu_pos H.hΛ H.hcm
  rcases hD.2.2.1.lt_or_eq with h' | h'
  · exact h'
  exfalso
  rcases (abs_eq (mul_nonneg hcp.le hD.1.le)).1 h' with h'' | h''
  · have := face_top_D H he h h'' N hk le_rfl
    rw [this, abs_of_nonneg (mul_nonneg hcp.le (h N le_rfl).1.le)] at hN
    exact lt_irrefl _ hN
  · have := face_bot_D H he h h'' N hk le_rfl
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg hcp.le (h N le_rfl).1.le)] at hN
    exact lt_irrefl _ hN

/-- The closed `OKRc` at a target `y ≤ ε` keeps the flow in `D_ε`. -/
lemma inDh_of_OKRc {y b μ : ℝ} (hb : 0 < b) (hy : y ≤ ε) (hO : OKRc F Λ cm N y b μ) :
    ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 := hO 0 (Nat.zero_le _)
    rw [traj_zero] at h0
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    obtain rfl : i = 0 := by omega
    rw [traj_zero]
    exact ⟨hb, h0.1.trans hy, h0.2, by
      simp only [norm_zero]; exact mul_nonneg (cx_pos H.hκ1 H.hcT).le (by positivity)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    have h1 := hO (j + 1) hj
    rw [traj_succ H b μ (by omega)] at h1
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases (show i = j + 1 ∨ i ≤ j by omega) with rfl | hij
      · rw [traj_succ H b μ (by omega)]
        exact step_InD H he (by omega) hs (h1.1.trans hy) h1.2
      · exact hs.1 i hij
    · rcases (show i = j ∨ i < j by omega) with rfl | hij
      · rw [traj_succ H b μ (by omega)]; exact H.F1 i (by omega) _ hs
      · exact hs.2 i hij

/-- `OKR` at a point of `D_ε` with `ǧ_N < y` and a strict final value. -/
lemma OKR_of_D_lt (hgβ : cg * ε ≤ (1 - δ) * β) {y b μ : ℝ} (hb : 0 < b)
    (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ j)) (hy : (traj F Λ b μ N).1 < y)
    (hN : |(traj F Λ b μ N).2.1| < cmu Λ cm * (traj F Λ b μ N).1) : OKR F Λ cm N y b μ :=
  ⟨hb, fun j hj => ⟨(traj_le_N_D H hgβ h j hj).trans_lt hy, strict_of_D H he h hN j hj⟩⟩

end Dom

/-! ### Uniqueness and monotonicity in the target -/

section Unique

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (hC : ConeS F Λ β δ κ cg cm cT N ε)
include H hC

end Unique

/-! ### The signed cone with its `ǧ`-part from the hidden coupling -/

/-- **`cone_signed_z` with the `ǧ`-part** `|δǧ_N| ≤ p δμ_N`, `p = K_h((1+Λ)/2, κ, A)·a`. -/
theorem coneSG_of_Z {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ aζ bζ ε : ℝ}
    (H : HHyp F Λ β δ κ cg cm cT N A' a' ε) (HZ : ZHyp F Λ β δ κ cg cm cT N Z A a Aζ aζ bζ ε)
    (ha0 : a ≤ a0h ((1 + Λ) / 2) κ A)
    (hs : bζ * sZ Aζ aζ (Kh ((1 + Λ) / 2) κ A * a) (Qh κ * a) ≤ (Λ - 1) / 4) :
    ConeSG F Λ β δ κ cg cm cT N ε (Kh ((1 + Λ) / 2) κ A * a) := by
  intro b μ μ' hμ h h'
  have hΛ := H.hΛ
  have hΛ2 : 1 < (1 + Λ) / 2 := by linarith
  obtain ⟨hp0, hq0, eg0, ex, em0⟩ := coef_h hΛ2 H.hκ1 HZ.hA HZ.ha ha0
  set p := Kh ((1 + Λ) / 2) κ A * a
  set q := Qh κ * a
  have eg : (1 + a) * p + a + A * q + a * (1 + p + q) ≤ p * ((1 + Λ) / 2) := by
    refine eg0.trans (mul_le_mul_of_nonneg_left ?_ hp0); linarith
  have em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * (1 + p + q) + bζ * sZ Aζ aζ p q) := by
    linarith
  set t := traj F Λ b μ
  set t' := traj F Λ b μ'
  set s := sZ Aζ aζ p q
  have hs0 : 0 ≤ s := by
    have := HZ.hAζ; have := HZ.haζ
    simp only [s]; unfold sZ; positivity
  have key : ∀ k ≤ N,
      |(t k).1 - (t' k).1| ≤ p * |(t k).2.1 - (t' k).2.1| ∧
      ‖(t k).2.2 - (t' k).2.2‖ ≤ q * |(t k).2.1 - (t' k).2.1| ∧
      (∀ i < k, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t k).2.1 - (t' k).2.1|) ∧
      ‖Z k t - Z k t'‖ ≤ s * |(t k).2.1 - (t' k).2.1| ∧
      μ - μ' ≤ (t k).2.1 - (t' k).2.1 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [t, t', traj_zero, sub_self, abs_zero, norm_zero, le_refl, and_true]
      refine ⟨mul_nonneg hp0 (abs_nonneg _), mul_nonneg hq0 (abs_nonneg _),
        fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      rw [HZ.Z0 (traj F Λ b μ) (traj F Λ b μ'), sub_self, norm_zero]
      exact mul_nonneg hs0 (abs_nonneg _)
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨ig, ix, ih', iz, iμ⟩ := ih (by omega)
      have hd : 0 ≤ (t k).2.1 - (t' k).2.1 := by linarith
      obtain ⟨s1, s2, s3, s4, s5⟩ := unique_step_z HZ H.hκ0 hΛ hp0 hq0 eg ex em hkN
        (h k (by omega)) (h' k (by omega)) ig ix ih' iz
      have s6 := step_signed_z HZ hΛ hp0 hq0 em hkN (h k (by omega)) (h' k (by omega)) hd ig ix
        ih' iz
      have e0 := traj_succ H b μ hkN
      have e1 := traj_succ H b μ' hkN
      simp only [t, t'] at s1 s2 s3 s4 s5 s6 ih' ig ix iz iμ hd ⊢
      rw [e0, e1]
      refine ⟨s2, s3, fun i hi => ?_, ?_, iμ.trans s6⟩
      · rcases (show i = k ∨ i < k by omega) with rfl | hik
        · have : dist3 (traj F Λ b μ i) (traj F Λ b μ' i) ≤
              (1 + p + q) * |(traj F Λ b μ i).2.1 - (traj F Λ b μ' i).2.1| := by
            unfold dist3
            nlinarith [abs_nonneg ((traj F Λ b μ i).2.1 - (traj F Λ b μ' i).2.1)]
          exact this.trans (mul_le_mul_of_nonneg_left s4 (by positivity))
        · exact (ih' i hik).trans (mul_le_mul_of_nonneg_left s4 (by positivity))
      · simpa only [e0, e1] using s5
  obtain ⟨k1, -, -, -, k5⟩ := key N le_rfl
  have hd : 0 ≤ (t N).2.1 - (t' N).2.1 := by linarith
  rw [abs_of_nonneg hd] at k1
  exact ⟨k5, k1⟩

/-! ### Continuation in the target at fixed `b` -/

section Window

variable {N : ℕ} {A a ε p : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β)
  (hC : ConeSG F Λ β δ κ cg cm cT N ε p)
include H he hgβ hC

omit he hgβ hC in
/-- `OKR` is open in `μ` (at fixed `b`). -/
lemma OKR_nhds {y b μ : ℝ} (hO : OKR F Λ cm N y b μ) :
    ∀ᶠ μ' in 𝓝 μ, OKR F Λ cm N y b μ' := by
  refine (Filter.Eventually.of_forall (fun _ => hO.1)).and ?_
  refine (eventually_all_finite (finite_le_nat N)).2 fun j hj => ?_
  have hc : Continuous fun μ' : ℝ => traj F Λ b μ' j :=
    (continuous_traj H (show j ≤ N from hj)).comp (continuous_const.prodMk continuous_id)
  have hg : Continuous fun μ' : ℝ => (traj F Λ b μ' j).1 := continuous_fst.comp hc
  have hμ : Continuous fun μ' : ℝ => |(traj F Λ b μ' j).2.1| :=
    (continuous_fst.comp (continuous_snd.comp hc)).abs
  exact (hg.continuousAt.eventually_lt continuousAt_const (hO.2 j hj).1).and
    (hμ.continuousAt.eventually_lt (continuousAt_const.mul hg.continuousAt) (hO.2 j hj).2)

omit he hgβ hC in
lemma isClosed_OKRc (y b : ℝ) : IsClosed {μ | OKRc F Λ cm N y b μ} := by
  have e : {μ | OKRc F Λ cm N y b μ} = ⋂ j ∈ {j | j ≤ N},
      ({μ | (traj F Λ b μ j).1 ≤ y} ∩
        {μ | |(traj F Λ b μ j).2.1| ≤ cmu Λ cm * (traj F Λ b μ j).1}) := by
    ext μ; simp [OKRc]
  rw [e]
  refine isClosed_biInter fun j hj => ?_
  have hc : Continuous fun μ' : ℝ => traj F Λ b μ' j :=
    (continuous_traj H (show j ≤ N from hj)).comp (continuous_const.prodMk continuous_id)
  have hg : Continuous fun μ' : ℝ => (traj F Λ b μ' j).1 := continuous_fst.comp hc
  have hμ : Continuous fun μ' : ℝ => |(traj F Λ b μ' j).2.1| :=
    (continuous_fst.comp (continuous_snd.comp hc)).abs
  exact (isClosed_le hg continuous_const).inter (isClosed_le hμ (continuous_const.mul hg))

/-- **Continuation upwards in the target.** From `μ⁰` with target `c₀` to the target `c₁ ≥ c₀`,
provided `ǧ_N` stays below `y ≤ ε` and `c₀, c₁` stay strictly inside `c_μ ǧ_N` along the
`ǧ`-cone: there is `μ₁ ≥ μ⁰` with target `c₁`, and every `μ ∈ [μ⁰, μ₁]` is in `D_ε` with
`c₀ ≤ μ_N ≤ c₁` and `|ǧ_N(μ) - ǧ_N(μ⁰)| ≤ p (μ_N - c₀)`. -/
theorem win_up {b μ0 c₀ c₁ y : ℝ} (hb : 0 < b) (hy : y ≤ ε)
    (h0 : AdmW F Λ κ cm cT N ε b μ0 c₀) (hc : c₀ ≤ c₁) (hp : 0 ≤ p)
    (hgy : (traj F Λ b μ0 N).1 + p * (c₁ - c₀) < y)
    (hc₀ : |c₀| < cmu Λ cm * ((traj F Λ b μ0 N).1 - p * (c₁ - c₀)))
    (hc₁ : |c₁| < cmu Λ cm * ((traj F Λ b μ0 N).1 - p * (c₁ - c₀))) :
    ∃ μ₁, μ0 ≤ μ₁ ∧ AdmW F Λ κ cm cT N ε b μ₁ c₁ ∧ ∀ μ ∈ Icc μ0 μ₁,
      (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ j)) ∧ c₀ ≤ (traj F Λ b μ N).2.1 ∧
      (traj F Λ b μ N).2.1 ≤ c₁ ∧
      |(traj F Λ b μ N).1 - (traj F Λ b μ0 N).1| ≤ p * ((traj F Λ b μ N).2.1 - c₀) := by
  set g0 := (traj F Λ b μ0 N).1
  set s : Set ℝ := {μ | OKRc F Λ cm N y b μ} ∩ {μ | (traj F Λ b μ N).2.1 ≤ c₁}
  have hcont := continuous_traj_mu H (N := N) b
  have hscl : IsClosed s := (isClosed_OKRc H y b).inter (isClosed_le hcont continuous_const)
  have hp0 : 0 ≤ p * (c₁ - c₀) := mul_nonneg hp (by linarith)
  have hcmu := (cmu_pos H.hΛ H.hcm).le
  have hD0 := traj_InDh_of H h0.1
  -- the start
  have hs0 : μ0 ∈ s := by
    refine ⟨fun j hj => ⟨?_, (h0.1 j hj).2.2.1⟩, by rw [Set.mem_setOf_eq, h0.2]; exact hc⟩
    exact (traj_le_N_D H hgβ h0.1 j hj).trans (by linarith)
  -- the information at a point of `s` above `μ⁰`
  have info : ∀ x ∈ s, μ0 ≤ x → (∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b x)) ∧
      x - μ0 ≤ (traj F Λ b x N).2.1 - c₀ ∧
      |(traj F Λ b x N).1 - g0| ≤ p * ((traj F Λ b x N).2.1 - c₀) := by
    intro x hx hx0
    have hD := inDh_of_OKRc H he hb hy hx.1
    obtain ⟨k1, k2⟩ := hC b x μ0 hx0 hD hD0
    rw [h0.2] at k1 k2
    exact ⟨hD, k1, k2⟩
  -- the extension step
  have ext : ∀ x ∈ s, μ0 ≤ x → (traj F Λ b x N).2.1 < c₁ →
      ∀ z ∈ Ioi x, (s ∩ Ioc x z).Nonempty := by
    intro x hx hx0 hlt z hz
    obtain ⟨hD, k1, k2⟩ := info x hx hx0
    have hD3 : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b x j) := fun j hj => (hD j hj).1 j le_rfl
    have hk2 := abs_le.1 k2
    have hμlo : c₀ ≤ (traj F Λ b x N).2.1 := by linarith
    have hgx : (traj F Λ b x N).1 < y := by
      have : p * ((traj F Λ b x N).2.1 - c₀) ≤ p * (c₁ - c₀) :=
        mul_le_mul_of_nonneg_left (by linarith) hp
      linarith
    have hglo : g0 - p * (c₁ - c₀) ≤ (traj F Λ b x N).1 := by
      have : p * ((traj F Λ b x N).2.1 - c₀) ≤ p * (c₁ - c₀) :=
        mul_le_mul_of_nonneg_left (by linarith) hp
      linarith
    have hN : |(traj F Λ b x N).2.1| < cmu Λ cm * (traj F Λ b x N).1 := by
      have hK := mul_le_mul_of_nonneg_left hglo hcmu
      rw [abs_lt] at hc₀ hc₁ ⊢
      constructor <;> linarith
    have hO := OKR_of_D_lt H he hgβ hb hD3 hgx hN
    have hev := (OKR_nhds H hO).and
      (hcont.continuousAt.eventually (gt_mem_nhds hlt))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨m, hm⟩ : ∃ m, m = min (x + r / 2) z := ⟨_, rfl⟩
    have m1 : x < m := by rw [hm]; exact lt_min (by linarith) hz
    have m2 : m ≤ z := by rw [hm]; exact min_le_right _ _
    have m3 : m ≤ x + r / 2 := by rw [hm]; exact min_le_left _ _
    obtain ⟨hOm, hlm⟩ := hball (y := m) (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    exact ⟨m, ⟨fun j hj => ⟨(hOm.2 j hj).1.le, (hOm.2 j hj).2.le⟩, hlm.le⟩, m1, m2⟩
  -- a point with target `c₁`
  obtain ⟨μ₁, hμ₁I, hμ₁s, hμ₁c⟩ : ∃ μ₁ ∈ Icc μ0 (μ0 + (c₁ - c₀)), μ₁ ∈ s ∧
      (traj F Λ b μ₁ N).2.1 = c₁ := by
    by_contra hn
    push Not at hn
    have hsub : Icc μ0 (μ0 + (c₁ - c₀)) ⊆ s := by
      refine (hscl.inter isClosed_Icc).Icc_subset_of_forall_exists_gt hs0 ?_
      rintro x ⟨hx, hxI⟩
      exact ext x hx hxI.1 (lt_of_le_of_ne hx.2 (hn x ⟨hxI.1, hxI.2.le⟩ hx))
    have he' : μ0 + (c₁ - c₀) ∈ s := hsub ⟨by linarith, le_rfl⟩
    obtain ⟨-, k1, -⟩ := info _ he' (by linarith)
    exact hn _ ⟨by linarith, le_rfl⟩ he' (le_antisymm he'.2 (by linarith))
  -- the whole segment
  have hsub : Icc μ0 μ₁ ⊆ s := by
    refine (hscl.inter isClosed_Icc).Icc_subset_of_forall_exists_gt hs0 ?_
    rintro x ⟨hx, hxI⟩
    refine ext x hx hxI.1 ?_
    obtain ⟨hD₁, -, -⟩ := info μ₁ hμ₁s hμ₁I.1
    obtain ⟨hDx, -, -⟩ := info x hx hxI.1
    have := (hC b μ₁ x hxI.2.le hD₁ hDx).1
    rw [hμ₁c] at this
    linarith [hxI.2]
  refine ⟨μ₁, hμ₁I.1, ⟨fun j hj => (inDh_of_OKRc H he hb hy hμ₁s.1 j hj).1 j le_rfl, hμ₁c⟩,
    fun μ hμ => ?_⟩
  have hμs := hsub hμ
  obtain ⟨hD, k1, k2⟩ := info μ hμs hμ.1
  exact ⟨fun j hj => (hD j hj).1 j le_rfl, by linarith [hμ.1], hμs.2, k2⟩

/-- **Continuation downwards in the target** (the mirror of `win_up`). -/
theorem win_down {b μ0 c₀ c₁ y : ℝ} (hb : 0 < b) (hy : y ≤ ε)
    (h0 : AdmW F Λ κ cm cT N ε b μ0 c₀) (hc : c₁ ≤ c₀) (hp : 0 ≤ p)
    (hgy : (traj F Λ b μ0 N).1 + p * (c₀ - c₁) < y)
    (hc₀ : |c₀| < cmu Λ cm * ((traj F Λ b μ0 N).1 - p * (c₀ - c₁)))
    (hc₁ : |c₁| < cmu Λ cm * ((traj F Λ b μ0 N).1 - p * (c₀ - c₁))) :
    ∃ μ₁, μ₁ ≤ μ0 ∧ AdmW F Λ κ cm cT N ε b μ₁ c₁ ∧ ∀ μ ∈ Icc μ₁ μ0,
      (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ j)) ∧ c₁ ≤ (traj F Λ b μ N).2.1 ∧
      (traj F Λ b μ N).2.1 ≤ c₀ ∧
      |(traj F Λ b μ N).1 - (traj F Λ b μ0 N).1| ≤ p * (c₀ - (traj F Λ b μ N).2.1) := by
  set g0 := (traj F Λ b μ0 N).1
  set s : Set ℝ := {μ | OKRc F Λ cm N y b μ} ∩ {μ | c₁ ≤ (traj F Λ b μ N).2.1}
  have hcont := continuous_traj_mu H (N := N) b
  have hscl : IsClosed s := (isClosed_OKRc H y b).inter (isClosed_le continuous_const hcont)
  have hp0 : 0 ≤ p * (c₀ - c₁) := mul_nonneg hp (by linarith)
  have hcmu := (cmu_pos H.hΛ H.hcm).le
  have hD0 := traj_InDh_of H h0.1
  have hs0 : μ0 ∈ s := by
    refine ⟨fun j hj => ⟨?_, (h0.1 j hj).2.2.1⟩, by rw [Set.mem_setOf_eq, h0.2]; exact hc⟩
    exact (traj_le_N_D H hgβ h0.1 j hj).trans (by linarith)
  have info : ∀ x ∈ s, x ≤ μ0 → (∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b x)) ∧
      μ0 - x ≤ c₀ - (traj F Λ b x N).2.1 ∧
      |(traj F Λ b x N).1 - g0| ≤ p * (c₀ - (traj F Λ b x N).2.1) := by
    intro x hx hx0
    have hD := inDh_of_OKRc H he hb hy hx.1
    obtain ⟨k1, k2⟩ := hC b μ0 x hx0 hD0 hD
    rw [h0.2] at k1 k2
    rw [abs_sub_comm] at k2
    exact ⟨hD, k1, k2⟩
  have ext : ∀ x ∈ s, x ≤ μ0 → c₁ < (traj F Λ b x N).2.1 →
      ∀ z ∈ Iio x, (s ∩ Ico z x).Nonempty := by
    intro x hx hx0 hlt z hz
    obtain ⟨hD, k1, k2⟩ := info x hx hx0
    have hD3 : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b x j) := fun j hj => (hD j hj).1 j le_rfl
    have hk2 := abs_le.1 k2
    have hμhi : (traj F Λ b x N).2.1 ≤ c₀ := by linarith
    have hpb : p * (c₀ - (traj F Λ b x N).2.1) ≤ p * (c₀ - c₁) :=
      mul_le_mul_of_nonneg_left (by linarith) hp
    have hgx : (traj F Λ b x N).1 < y := by linarith
    have hglo : g0 - p * (c₀ - c₁) ≤ (traj F Λ b x N).1 := by linarith
    have hN : |(traj F Λ b x N).2.1| < cmu Λ cm * (traj F Λ b x N).1 := by
      have hK := mul_le_mul_of_nonneg_left hglo hcmu
      rw [abs_lt] at hc₀ hc₁ ⊢
      constructor <;> linarith
    have hO := OKR_of_D_lt H he hgβ hb hD3 hgx hN
    have hev := (OKR_nhds H hO).and
      (hcont.continuousAt.eventually (lt_mem_nhds hlt))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨m, hm⟩ : ∃ m, m = max (x - r / 2) z := ⟨_, rfl⟩
    have m1 : m < x := by rw [hm]; exact max_lt (by linarith) hz
    have m2 : z ≤ m := by rw [hm]; exact le_max_right _ _
    have m3 : x - r / 2 ≤ m := by rw [hm]; exact le_max_left _ _
    obtain ⟨hOm, hlm⟩ := hball (y := m)
      (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)
    exact ⟨m, ⟨fun j hj => ⟨(hOm.2 j hj).1.le, (hOm.2 j hj).2.le⟩, hlm.le⟩, m2, m1⟩
  obtain ⟨μ₁, hμ₁I, hμ₁s, hμ₁c⟩ : ∃ μ₁ ∈ Icc (μ0 - (c₀ - c₁)) μ0, μ₁ ∈ s ∧
      (traj F Λ b μ₁ N).2.1 = c₁ := by
    by_contra hn
    push Not at hn
    have hsub : Icc (μ0 - (c₀ - c₁)) μ0 ⊆ s := by
      refine (hscl.inter isClosed_Icc).Icc_subset_of_forall_exists_lt hs0 ?_
      rintro x ⟨hx, hxI⟩
      exact ext x hx hxI.2 (lt_of_le_of_ne hx.2 (fun h => hn x ⟨hxI.1.le, hxI.2⟩ hx h.symm))
    have he' : μ0 - (c₀ - c₁) ∈ s := hsub ⟨le_rfl, by linarith⟩
    obtain ⟨-, k1, -⟩ := info _ he' (by linarith)
    exact hn _ ⟨le_rfl, by linarith⟩ he' (le_antisymm (by linarith) he'.2)
  have hsub : Icc μ₁ μ0 ⊆ s := by
    refine (hscl.inter isClosed_Icc).Icc_subset_of_forall_exists_lt hs0 ?_
    rintro x ⟨hx, hxI⟩
    refine ext x hx hxI.2 ?_
    obtain ⟨hD₁, -, -⟩ := info μ₁ hμ₁s hμ₁I.2
    obtain ⟨hDx, -, -⟩ := info x hx hxI.2
    have := (hC b x μ₁ hxI.1.le hDx hD₁).1
    rw [hμ₁c] at this
    linarith [hxI.1]
  refine ⟨μ₁, hμ₁I.2, ⟨fun j hj => (inDh_of_OKRc H he hb hy hμ₁s.1 j hj).1 j le_rfl, hμ₁c⟩,
    fun μ hμ => ?_⟩
  have hμs := hsub hμ
  obtain ⟨hD, k1, k2⟩ := info μ hμs hμ.2
  exact ⟨fun j hj => (hD j hj).1 j le_rfl, hμs.2, by linarith [hμ.2], k2⟩

/-- **The window of initial data around an admissible `μ₀^c`.** For targets `c₋ ≤ 0 ≤ c₊`
with `ǧ_N + p d < y ≤ ε` and `|c_±| < c_μ(ǧ_N - p d)`, `d = c₊ - c₋`, there are `μ₋ ≤ μ₀^c ≤ μ₊`
with targets `c₋`, `c₊`, and every `μ ∈ [μ₋, μ₊]` is in `D_ε` with `c₋ ≤ μ_N ≤ c₊` and
`|ǧ_N(μ) - ǧ_N(μ₀^c)| ≤ p d`. -/
theorem win_interval {b μc cl cu y : ℝ} (hb : 0 < b) (hy : y ≤ ε)
    (h0 : Admissible F Λ κ cm cT N ε b μc) (hl : cl ≤ 0) (hu : 0 ≤ cu) (hp : 0 ≤ p)
    (hgy : (traj F Λ b μc N).1 + p * (cu - cl) < y)
    (hcl : |cl| < cmu Λ cm * ((traj F Λ b μc N).1 - p * (cu - cl)))
    (hcu : |cu| < cmu Λ cm * ((traj F Λ b μc N).1 - p * (cu - cl))) :
    ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW F Λ κ cm cT N ε b μl cl ∧
      AdmW F Λ κ cm cT N ε b μu cu ∧ ∀ μ ∈ Icc μl μu,
      (∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ j)) ∧ cl ≤ (traj F Λ b μ N).2.1 ∧
      (traj F Λ b μ N).2.1 ≤ cu ∧
      |(traj F Λ b μ N).1 - (traj F Λ b μc N).1| ≤ p * (cu - cl) := by
  have h0' : AdmW F Λ κ cm cT N ε b μc 0 := h0
  have hcmu := (cmu_pos H.hΛ H.hcm).le
  have hpd : p * (cu - 0) ≤ p * (cu - cl) := mul_le_mul_of_nonneg_left (by linarith) hp
  have hpd' : p * (0 - cl) ≤ p * (cu - cl) := mul_le_mul_of_nonneg_left (by linarith) hp
  have hmono : ∀ e, e ≤ p * (cu - cl) → cmu Λ cm * ((traj F Λ b μc N).1 - p * (cu - cl)) ≤
      cmu Λ cm * ((traj F Λ b μc N).1 - e) := fun e he =>
    mul_le_mul_of_nonneg_left (by linarith) hcmu
  have hz : |(0 : ℝ)| < cmu Λ cm * ((traj F Λ b μc N).1 - p * (cu - cl)) :=
    by rw [abs_zero]; exact (abs_nonneg cl).trans_lt hcl
  obtain ⟨μu, hu1, hu2, hu3⟩ := win_up H he hgβ hC hb hy h0' hu hp (by linarith)
    (hz.trans_le (hmono _ hpd)) (hcu.trans_le (hmono _ hpd))
  obtain ⟨μl, hl1, hl2, hl3⟩ := win_down H he hgβ hC hb hy h0' hl hp (by linarith)
    (hz.trans_le (hmono _ hpd')) (hcl.trans_le (hmono _ hpd'))
  refine ⟨μl, μu, hl1, hu1, hl2, hu2, fun μ hμ => ?_⟩
  rcases le_total μ μc with h | h
  · obtain ⟨k1, k2, k3, k4⟩ := hl3 μ ⟨hμ.1, h⟩
    refine ⟨k1, k2, by linarith, k4.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hp
  · obtain ⟨k1, k2, k3, k4⟩ := hu3 μ ⟨h, hμ.2⟩
    refine ⟨k1, by linarith, k3, k4.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hp

end Window

/-! ### The `ǧ`-cone for two trajectories with the same target -/

section Two

variable {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ bζ ε w : ℝ}
  (H : HHyp F Λ β δ κ cg cm cT N A' a' ε)
  (HM : MonoZHyp F Λ β δ κ cg cm cT N Z A a Aζ bζ ε w)
include H HM

end Two

/-- **Symmetric window conditions.** For the targets `∓c₁` with `0 ≤ c₁ ≤ θ ǧ`, the hypotheses of
`win_interval` follow from `θ(1 + 2pc_μ) < c_μ` and `ǧ(1 + 2pθ) < y` (e.g. `θ = (3/4)c_μ` needs
`p c_μ < 1/6`). -/
theorem win_sym_conds {g p θ cμ c₁ y : ℝ} (hg : 0 < g) (hp : 0 ≤ p) (hcμ : 0 ≤ cμ)
    (hθ : θ * (1 + 2 * p * cμ) < cμ) (hgy : g * (1 + 2 * p * θ) < y) (hc0 : 0 ≤ c₁)
    (hc1 : c₁ ≤ θ * g) :
    g + p * (c₁ - -c₁) < y ∧ |-c₁| < cμ * (g - p * (c₁ - -c₁)) ∧
      |c₁| < cμ * (g - p * (c₁ - -c₁)) := by
  have e1 : p * (c₁ - -c₁) ≤ 2 * p * θ * g := by
    have := mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ 2 * p)
    linarith only [this, show p * (c₁ - -c₁) = 2 * p * c₁ by ring,
      show 2 * p * (θ * g) = 2 * p * θ * g by ring]
  have e2 : cμ * (g - 2 * p * θ * g) ≤ cμ * (g - p * (c₁ - -c₁)) :=
    mul_le_mul_of_nonneg_left (by linarith only [e1]) hcμ
  have e3 : θ * g < cμ * (g - 2 * p * θ * g) := by
    have := mul_lt_mul_of_pos_right hθ hg
    linarith only [this, show θ * (1 + 2 * p * cμ) * g = θ * g + cμ * (2 * p * θ * g) by ring,
      show cμ * (g - 2 * p * θ * g) = cμ * g - cμ * (2 * p * θ * g) by ring]
  refine ⟨by linarith only [e1, hgy, show g * (1 + 2 * p * θ) = g + 2 * p * θ * g by ring], ?_, ?_⟩
  · rw [abs_neg, abs_of_nonneg hc0]; linarith only [hc1, e2, e3]
  · rw [abs_of_nonneg hc0]; linarith only [hc1, e2, e3]

end Hist

end Flow2
