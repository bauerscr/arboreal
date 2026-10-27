import Flow2.History

/-!
# Shooting for `ǧ_N` (`h02uv-outline.tex`, Expected result `thm:flow`(ii))

Generic in the `b`-range:
* `exists_eq_of_continuousOn_Ioc`: a function continuous on `(0, b₁]` that takes arbitrarily
  small values attains every value in `(0, g(b₁)]`;
* `traj_fst_mono`, `b_le_traj_fst`: along any admissible trajectory the coupling does not
  decrease if `c_g ε ≤ (1 - δ) β` (by (F1), `G_j ≥ g_j + ((1-δ)β - c_g g_j) g_j²`);
* `unique_of_strictMonoOn`: uniqueness of the shooting parameter under strict monotonicity
  (`Flow2.Hist.strictMonoOn_of_admissible`).

On the range `(0, b_max]` of `prop:C6`:
* `gN_le`: `ǧ_N(b) ≤ (1/b - N β₊)⁻¹` (the invariant `1/g_j ≥ 1/b - j β₊`), so `ǧ_N(b) → 0`;
* `gN_surj`: **every value in `(0, ǧ_N(b_max)]` is attained** on `(0, b_max]`;
  `exists_gN_eq_inv`: for every `β_R ≥ 1/ǧ_N(b_max)` there is `b ∈ (0, b_max]` with
  `ǧ_N(b) = 1/β_R`. Since `b_max ≤ ǧ_N(b_max) ≤ (1/b_max - Nβ₊)⁻¹ = ε`, this range of `β_R`
  contains `[1/b_max, ∞)` and is contained in `[1/ε, ∞)`; it depends on `N` through `b_max`.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

/-! ### Generic intermediate value statement -/

/-- A function continuous on `(0, b₁]` that takes arbitrarily small values attains every value in
`(0, g(b₁)]`. -/
theorem exists_eq_of_continuousOn_Ioc {g : ℝ → ℝ} {b₁ : ℝ} (hg : ContinuousOn g (Ioc 0 b₁))
    (hsmall : ∀ y, 0 < y → ∃ b ∈ Ioc 0 b₁, g b ≤ y) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ g b₁) :
    ∃ b ∈ Ioc 0 b₁, g b = y := by
  obtain ⟨b₀, hb₀, hgb₀⟩ := hsmall y hy
  have hb₁ : b₁ ∈ Ioc 0 b₁ := ⟨hb₀.1.trans_le hb₀.2, le_rfl⟩
  obtain ⟨b, hbI, hbv⟩ := intermediate_value_uIcc (hg.mono
    (ordConnected_Ioc.uIcc_subset hb₀ hb₁)) (Set.mem_uIcc.2 (Or.inl ⟨hgb₀, hy1⟩))
  exact ⟨b, ordConnected_Ioc.uIcc_subset hb₀ hb₁ hbI, hbv⟩

/-- Uniqueness of the shooting parameter under strict monotonicity. -/
theorem unique_of_strictMonoOn {g : ℝ → ℝ} {I : Set ℝ} (hg : StrictMonoOn g I) {b b' y : ℝ}
    (hb : b ∈ I) (hb' : b' ∈ I) (h : g b = y) (h' : g b' = y) : b = b' :=
  hg.injOn hb hb' (h.trans h'.symm)

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

/-! ### The coupling along admissible trajectories -/

section Mono

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
include H

/-- The coupling does not decrease along an admissible trajectory. -/
lemma traj_fst_mono (hgβ : cg * ε ≤ (1 - δ) * β) {b μ₀ : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μ₀) {j : ℕ} (hj : j < N) :
    (traj F Λ b μ₀ j).1 ≤ (traj F Λ b μ₀ (j + 1)).1 := by
  have ht : InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := admissible_InDh H h j hj.le
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

/-- `b ≤ g_j` along an admissible trajectory. -/
lemma b_le_traj_fst (hgβ : cg * ε ≤ (1 - δ) * β) {b μ₀ : ℝ}
    (h : Admissible F Λ κ cm cT N ε b μ₀) : ∀ j ≤ N, b ≤ (traj F Λ b μ₀ j).1 := by
  intro j
  induction j with
  | zero => intro _; simp [traj_zero]
  | succ j ih =>
    intro hj
    exact (ih (by omega)).trans (traj_fst_mono H hgβ h (by omega))

end Mono

/-! ### On the range `(0, b_max]` -/

section Range

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hε : 0 < ε)
include H he hε

/-- **`ǧ_N(b) ≤ (1/b - N β₊)⁻¹`.** -/
lemma gN_le {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) :
    gN F Λ κ cm cT N ε b ≤ 1 / (1 / b - N * betap β δ cg) := by
  have hadm := muc_spec H he hε hb
  have hinv := (trajc_InDh H he hε hb (muc F Λ κ cm cT N ε b) N le_rfl).2 N le_rfl
  have hD := trajc_InD H he hε hb (muc F Λ κ cm cT N ε b) (le_refl N)
  rw [trajc_eq_traj H hadm N le_rfl N le_rfl] at hinv hD
  have hpos : 0 < 1 / b - N * betap β δ cg := by
    have := inv_b_of_mem hε H.hβ H.hδ H.hcg hb
    have : 0 < 1 / ε := by positivity
    linarith
  show (traj F Λ b (muc F Λ κ cm cT N ε b) N).1 ≤ _
  rw [le_one_div (hD.1) hpos]
  exact hinv

/-- `ǧ_N` takes arbitrarily small values on `(0, b_max]`. -/
lemma gN_small {y : ℝ} (hy : 0 < y) :
    ∃ b ∈ Ioc 0 (bmax β δ cg N ε), gN F Λ κ cm cT N ε b ≤ y := by
  have hbp : 0 ≤ N * betap β δ cg := by
    have := H.hβ; have := H.hδ; have := H.hcg; unfold betap; positivity
  have hbm0 : 0 < bmax β δ cg N ε := by
    unfold bmax; have : 0 < 1 / ε := by positivity
    positivity
  -- `b₁ = min (b_max, (1/y + N β₊)⁻¹)`
  set b₁ := min (bmax β δ cg N ε) (1 / (1 / y + N * betap β δ cg)) with hb₁
  have hd : 0 < 1 / y + N * betap β δ cg := by positivity
  have hb₁0 : 0 < b₁ := lt_min hbm0 (by positivity)
  have hb₁m : b₁ ∈ Ioc 0 (bmax β δ cg N ε) := ⟨hb₁0, min_le_left _ _⟩
  refine ⟨b₁, hb₁m, (gN_le H he hε hb₁m).trans ?_⟩
  have hb₁le : b₁ ≤ 1 / (1 / y + N * betap β δ cg) := min_le_right _ _
  have hinv : 1 / y + N * betap β δ cg ≤ 1 / b₁ := by
    rw [le_one_div hd hb₁0]; exact hb₁le
  have hpos : 0 < 1 / b₁ - N * betap β δ cg := by
    have : 0 < 1 / y := by positivity
    linarith
  rw [div_le_iff₀ hpos]
  have : 1 ≤ y * (1 / y) := by rw [mul_one_div_cancel hy.ne']
  nlinarith

/-- **Every value in `(0, ǧ_N(b_max)]` is attained by `ǧ_N` on `(0, b_max]`.** -/
theorem gN_surj (ha0 : a ≤ a0h Λ κ A) {y : ℝ} (hy : 0 < y)
    (hy1 : y ≤ gN F Λ κ cm cT N ε (bmax β δ cg N ε)) :
    ∃ b ∈ Ioc 0 (bmax β δ cg N ε), gN F Λ κ cm cT N ε b = y :=
  exists_eq_of_continuousOn_Ioc (continuousOn_gN H he hε ha0)
    (fun _ hy' => gN_small H he hε hy') hy hy1

/-- **Shooting for the renormalised coupling on `(0, b_max]`**: for every
`β_R ≥ 1/ǧ_N(b_max)` there is `b ∈ (0, b_max]` with `ǧ_N(b) = 1/β_R`. -/
theorem exists_gN_eq_inv (ha0 : a ≤ a0h Λ κ A) {βR : ℝ}
    (hpos : 0 < gN F Λ κ cm cT N ε (bmax β δ cg N ε))
    (hβR : 1 / gN F Λ κ cm cT N ε (bmax β δ cg N ε) ≤ βR) :
    ∃ b ∈ Ioc 0 (bmax β δ cg N ε), gN F Λ κ cm cT N ε b = 1 / βR := by
  have hβR0 : 0 < βR := (one_div_pos.2 hpos).trans_le hβR
  refine gN_surj H he hε ha0 (one_div_pos.2 hβR0) ?_
  rw [div_le_iff₀ hβR0]
  rw [div_le_iff₀ hpos] at hβR
  linarith

end Range

end Hist

end Flow2
