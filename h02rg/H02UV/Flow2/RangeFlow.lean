import Flow2.RangeSharp

/-!
# The sharp range: the flow theorem (`h02uv-outline.tex`, Expected result `thm:flow`)

On the sharp range `b ∈ (0, b_maxS]` of `Flow2.RangeSharp`:

* `fh_flow_range`: existence and uniqueness of the admissible `μ₀(b)`, continuity of `μ₀(b)` and
  `ǧ_N(b)`, the a priori bound `1/ǧ_j ≥ 1/ε + β (N - j)`, the bound
  `1/ǧ_N(b_maxS) ≤ ginvS` on the final coupling at the edge of the range, and the attained
  final couplings `ǧ_N(b) = 1/β_R` for every `β_R ≥ ginvS`;
* `ginv_log`: along every admissible trajectory, if `c_g ε ≤ (1-δ)β/2`,
  `|1/ǧ_n - 1/b + β n| ≤ 2(1+β) E + (5C/β) log(ǧ_n/b)`.
-/

open Set Filter Topology Finset

noncomputable section

namespace Flow2

namespace Hist

/-- Telescoping a per-step bound for `x_{j+1} - x_j + β`. -/
lemma tele_abs {x d : ℕ → ℝ} {β : ℝ} :
    ∀ n, (∀ j < n, |x (j + 1) - x j + β| ≤ d j) → |x n - x 0 + β * n| ≤ ∑ j ∈ range n, d j
  | 0, _ => by simp
  | n + 1, h => by
    have ih := tele_abs n fun j hj => h j (by omega)
    have hs := h n (by omega)
    rw [sum_range_succ]
    have e : x (n + 1) - x 0 + β * ((n + 1 : ℕ) : ℝ) =
        (x n - x 0 + β * n) + (x (n + 1) - x n + β) := by push_cast; ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add ih hs)

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {F : HData X} {Λ β δ κ cg cm cT : ℝ}

section Flow

variable {N : ℕ} {A a ε c E : ℝ} {e : ℕ → ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (S : SharpHyp F Λ β δ κ cg cm cT N ε c E e)
include H he

/-- **A sharp (F1) step in `1/g` form** (as `Step2`'s `ginv_sharp`):
`|1/g_{j+1} - 1/g_j + β| ≤ 2(1+β) e + C g_j`, `C = 2(β² + (1+β) c)`. -/
theorem ginv_sharpR {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {j : ℕ}
    (hj : j < N) {e c : ℝ} (he0 : 0 ≤ e) (hc : 0 ≤ c)
    (hF : ∀ t, InDh Λ β δ κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e * (t j).1 ^ 2 + c * (t j).1 ^ 3) :
    |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
      2 * (1 + β) * e + Cgu β c * (traj F Λ b μ₀ j).1 := by
  have ht : InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := admissible_InDh H h j (by omega)
  obtain ⟨hlow, -, -⟩ := step_D H he hj ht
  have hF1 := hF _ ht
  have hβ := H.hβ
  have hs := ht.1 j le_rfl
  have hg := hs.1
  have hg1 : (traj F Λ b μ₀ j).1 ≤ 1 := hs.2.1.trans (eps_facts H.hcg hβ (eps0u_le he)).1
  rw [traj_succ H b μ₀ hj]
  show |1 / F.G j (traj F Λ b μ₀) - 1 / (traj F Λ b μ₀ j).1 + β| ≤ _
  set g := (traj F Λ b μ₀ j).1
  set G := F.G j (traj F Λ b μ₀)
  have hG : 0 < G := by linarith
  set r := G - g - β * g ^ 2
  have e1 : 1 / G - 1 / g + β = (β ^ 2 * g ^ 3 + β * g * r - r) / (g * G) := by
    field_simp; ring
  rw [e1, abs_div, abs_of_pos (mul_pos hg hG), div_le_iff₀ (mul_pos hg hG)]
  have hr : |r| ≤ e * g ^ 2 + c * g ^ 3 := hF1
  have hn : |β ^ 2 * g ^ 3 + β * g * r - r| ≤ β ^ 2 * g ^ 3 + (1 + β * g) * |r| := by
    calc _ ≤ |β ^ 2 * g ^ 3 + β * g * r| + |r| := abs_sub _ _
      _ ≤ |β ^ 2 * g ^ 3| + |β * g * r| + |r| := by gcongr; exact abs_add_le _ _
      _ = β ^ 2 * g ^ 3 + (1 + β * g) * |r| := by
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ β ^ 2 * g ^ 3), abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < β * g)]; ring
  have h1 : (1 + β * g) * |r| ≤ (1 + β) * (e * g ^ 2 + c * g ^ 3) := by
    have : 1 + β * g ≤ 1 + β := by nlinarith
    exact mul_le_mul this hr (abs_nonneg _) (by linarith)
  have h2 : g ^ 2 * (5 / 6 * g) ≤ g ^ 2 * G := mul_le_mul_of_nonneg_left hlow (sq_nonneg g)
  have h2' : g * (5 / 6 * g) ≤ g * G := mul_le_mul_of_nonneg_left hlow hg.le
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ β ^ 2 + (1 + β) * c)
  have h4 := mul_le_mul_of_nonneg_left h2' (by positivity : (0 : ℝ) ≤ (1 + β) * e)
  have h6 : 0 ≤ (1 + β) * e * g ^ 2 := by positivity
  have h7 : 0 ≤ (β ^ 2 + (1 + β) * c) * g ^ 3 := by positivity
  have hfin : β ^ 2 * g ^ 3 + (1 + β) * (e * g ^ 2 + c * g ^ 3) ≤
      (2 * (1 + β) * e + Cgu β c * g) * (g * G) := by
    unfold Cgu
    have e1 : (2 * (1 + β) * e + 2 * (β ^ 2 + (1 + β) * c) * g) * (g * G) =
        2 * ((1 + β) * e * (g * G)) + 2 * ((β ^ 2 + (1 + β) * c) * (g ^ 2 * G)) := by ring
    have e2 : (1 + β) * e * (g * (5 / 6 * g)) = 5 / 6 * ((1 + β) * e * g ^ 2) := by ring
    have e3 : (β ^ 2 + (1 + β) * c) * (g ^ 2 * (5 / 6 * g)) =
        5 / 6 * ((β ^ 2 + (1 + β) * c) * g ^ 3) := by ring
    rw [e1]
    nlinarith
  linarith

include S

/-- **The summed sharp flow**: along any admissible trajectory, for `n ≤ N`,
`|1/ǧ_n - 1/b + β n| ≤ 2(1+β) E + C ∑_{j<n} ǧ_j`. -/
theorem ginv_sum_sharpR {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {n : ℕ} (hn : n ≤ N) :
    |1 / (traj F Λ b μ₀ n).1 - 1 / b + β * n| ≤
      2 * (1 + β) * E + Cgu β c * ∑ j ∈ range n, (traj F Λ b μ₀ j).1 := by
  have ht := tele_abs (x := fun j => 1 / (traj F Λ b μ₀ j).1)
    (d := fun j => 2 * (1 + β) * e j + Cgu β c * (traj F Λ b μ₀ j).1) (β := β) n
    (fun j hj => ginv_sharpR H he h (by omega) (S.he j) S.hc (S.F1s j (by omega)))
  simp only [traj_zero] at ht
  refine ht.trans (le_of_eq_of_le (by rw [sum_add_distrib, ← mul_sum, ← mul_sum]) ?_)
  have hsub : ∑ j ∈ range n, e j ≤ E :=
    (sum_le_sum_of_subset_of_nonneg (range_mono hn) fun j _ _ => S.he j).trans S.hE
  have := H.hβ
  have := mul_le_mul_of_nonneg_left hsub (by positivity : (0 : ℝ) ≤ 2 * (1 + β))
  linarith

variable (hε : 0 < ε)
include hε

/-- On the sharp range: `∑_{j<N} ǧ_j ≤ log(1 + β N ε)/β`. -/
lemma sum_g_le_log {b μ₀ : ℝ} (hb : b ∈ Ioc 0 (bmaxS β c E N ε))
    (h : Admissible F Λ κ cm cT N ε b μ₀) :
    ∑ j ∈ range N, (traj F Λ b μ₀ j).1 ≤ Real.log (1 + β * N * ε) / β := by
  refine le_trans (sum_le_sum fun j hj => ?_) (sum_inv_le_log H.hβ hε N)
  have hjN : j ≤ N := (mem_range.1 hj).le
  have hlow := (admissible_lowerS H he hε S hb h hjN).2
  have hg := (h.1 j hjN).1
  have hden : 0 < 1 / ε + β * ((N : ℝ) - j) := by
    have hj' : (j : ℝ) ≤ N := by exact_mod_cast hjN
    have : 0 ≤ β * ((N : ℝ) - j) := mul_nonneg H.hβ.le (by linarith)
    have : 0 < 1 / ε := by positivity
    linarith
  rw [le_one_div hg hden]; exact hlow

/-- The final coupling on the sharp range:
`1/ǧ_N ≤ 1/b - β N + 2(1+β) E + (C/β) log(1 + β N ε)`. -/
lemma ginv_N_le {b μ₀ : ℝ} (hb : b ∈ Ioc 0 (bmaxS β c E N ε))
    (h : Admissible F Λ κ cm cT N ε b μ₀) :
    1 / (traj F Λ b μ₀ N).1 ≤
      1 / b - β * N + 2 * (1 + β) * E + Cgu β c / β * Real.log (1 + β * N * ε) := by
  have h1 := (abs_le.1 (ginv_sum_sharpR H he S h le_rfl)).2
  have h2 := sum_g_le_log H he S hε hb h
  have hC : 0 ≤ Cgu β c := by have := H.hβ; have := S.hc; unfold Cgu; positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hC
  have e1 : Cgu β c * (Real.log (1 + β * N * ε) / β) =
      Cgu β c / β * Real.log (1 + β * N * ε) := by ring
  linarith

/-- **The final coupling at the edge of the sharp range**: `1/ǧ_N(b_maxS) ≤ ginvS`. -/
theorem ginv_gN_bmaxS :
    1 / gN F Λ κ cm cT N ε (bmaxS β c E N ε) ≤ ginvS β c E N ε := by
  have hmem : bmaxS β c E N ε ∈ Ioc 0 (bmaxS β c E N ε) :=
    ⟨bmaxS_pos H.hβ hε S.hc S.hE0, le_rfl⟩
  have h := ginv_N_le H he S hε hmem (muc_specK H he (keepD_of_bmaxS H he hε S hmem))
  have e1 : 1 / bmaxS β c E N ε = 1 / ε + β * N + E + c / β * Real.log (1 + β * N * ε) := by
    unfold bmaxS; rw [one_div_one_div]
  rw [e1] at h
  unfold ginvS
  have e2 : (c + Cgu β c) / β * Real.log (1 + β * N * ε) =
      c / β * Real.log (1 + β * N * ε) + Cgu β c / β * Real.log (1 + β * N * ε) := by ring
  unfold gN
  linarith

/-- **The attained final couplings**: for every `β_R ≥ ginvS` there is `b ∈ (0, b_maxS]` with
`ǧ_N(b) = 1/β_R`. -/
theorem exists_gN_eq_invS (ha0 : a ≤ a0h Λ κ A) {βR : ℝ} (hβR : ginvS β c E N ε ≤ βR) :
    ∃ b ∈ Ioc 0 (bmaxS β c E N ε), gN F Λ κ cm cT N ε b = 1 / βR := by
  have hβ := H.hβ
  have hE0 := S.hE0
  have hlog := log_nonneg_N (N := N) hβ hε
  have hC : 0 ≤ Cgu β c := by have := S.hc; unfold Cgu; positivity
  have hεR : 1 / ε ≤ βR := by
    refine le_trans ?_ hβR
    unfold ginvS
    have : 0 ≤ (3 + 2 * β) * E := by positivity
    have : 0 ≤ (c + Cgu β c) / β * Real.log (1 + β * N * ε) := by
      have := S.hc; positivity
    linarith
  have hβR0 : 0 < βR := lt_of_lt_of_le (by positivity) hεR
  obtain ⟨K, hK⟩ : ∃ K, K = β * N + E + c / β * Real.log (1 + β * N * ε) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; have := S.hc; positivity
  -- the small endpoint
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = 1 / (βR + K) := ⟨_, rfl⟩
  have hb₁0 : 0 < b₁ := by rw [hb₁]; positivity
  have hb₁m : b₁ ∈ Ioc 0 (bmaxS β c E N ε) := by
    refine ⟨hb₁0, ?_⟩
    rw [hb₁, bmaxS]
    apply one_div_le_one_div_of_le (bmaxS_den_pos hβ hε S.hc hE0)
    rw [hK] at *
    linarith
  have hbm : bmaxS β c E N ε ∈ Ioc 0 (bmaxS β c E N ε) := ⟨bmaxS_pos hβ hε S.hc hE0, le_rfl⟩
  have h1 : gN F Λ κ cm cT N ε b₁ ≤ 1 / βR := by
    have hadm := muc_specK H he (keepD_of_bmaxS H he hε S hb₁m)
    have hl := (admissible_lowerS H he hε S hb₁m hadm le_rfl).1
    have hp := phiS_le (e := e) hβ hε S.hc S.hE
    have hg := (hadm.1 N le_rfl).1
    have hinv : βR ≤ 1 / (traj F Λ b₁ (muc F Λ κ cm cT N ε b₁) N).1 := by
      have : 1 / b₁ = βR + K := by rw [hb₁, one_div_one_div]
      rw [this, hK] at hl
      linarith
    unfold gN
    rw [le_one_div hg hβR0]
    exact hinv
  have h2 : 1 / βR ≤ gN F Λ κ cm cT N ε (bmaxS β c E N ε) := by
    have hg := ((muc_specK H he (keepD_of_bmaxS H he hε S hbm)).1 N le_rfl).1
    have := ginv_gN_bmaxS H he S hε
    unfold gN at this ⊢
    rw [one_div_le hβR0 hg]
    linarith
  have hS : ∀ b ∈ Ioc 0 (bmaxS β c E N ε), KeepD F Λ β δ κ cg cm cT N ε b :=
    fun b hb => keepD_of_bmaxS H he hε S hb
  obtain ⟨b, hbI, hbv⟩ := shootingK H he ha0 hS ordConnected_Ioc hb₁m hbm
    (y := 1 / βR) (Set.mem_uIcc.2 (Or.inl ⟨h1, h2⟩))
  refine ⟨b, (ordConnected_Ioc.uIcc_subset hb₁m hbm) hbI, hbv⟩

/-- **The flow theorem on the sharp range.** For `b ∈ (0, b_maxS]`: a unique admissible `μ₀`;
continuity of `μ₀(b)` and `ǧ_N(b)`; `1/ǧ_j ≥ 1/ε + β (N - j)` along the admissible flow;
`1/ǧ_N(b_maxS) ≤ ginvS`; and every final coupling `1/β_R ≤ 1/ginvS` is attained. -/
theorem fh_flow_range (ha0 : a ≤ a0h Λ κ A) :
    (∀ b ∈ Ioc 0 (bmaxS β c E N ε), ∃! μ₀, Admissible F Λ κ cm cT N ε b μ₀) ∧
    ContinuousOn (muc F Λ κ cm cT N ε) (Ioc 0 (bmaxS β c E N ε)) ∧
    ContinuousOn (gN F Λ κ cm cT N ε) (Ioc 0 (bmaxS β c E N ε)) ∧
    (∀ b ∈ Ioc 0 (bmaxS β c E N ε), ∀ μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ j ≤ N,
      1 / ε + β * ((N : ℝ) - j) ≤ 1 / (traj F Λ b μ₀ j).1) ∧
    1 / gN F Λ κ cm cT N ε (bmaxS β c E N ε) ≤ ginvS β c E N ε ∧
    (∀ βR, ginvS β c E N ε ≤ βR →
      ∃ b ∈ Ioc 0 (bmaxS β c E N ε), gN F Λ κ cm cT N ε b = 1 / βR) := by
  obtain ⟨r1, r2, r3⟩ := fh_flow_histK H he ha0 (S := Ioc 0 (bmaxS β c E N ε))
    fun b hb => keepD_of_bmaxS H he hε S hb
  exact ⟨r1, r2, r3, fun b hb μ₀ h j hj => (admissible_lowerS H he hε S hb h hj).2,
    ginv_gN_bmaxS H he S hε, fun βR hβR => exists_gN_eq_invS H he S hε ha0 hβR⟩

end Flow

/-! ### The logarithmic form of (i) -/

section Log

variable {N : ℕ} {A a ε c E : ℝ} {e : ℕ → ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (he : ε ≤ eps0u Λ β δ κ cg cm) (hgβ : cg * ε ≤ (1 - δ) * β / 2)
include H he hgβ

/-- `1/g` decreases by at least `β/5` per step along admissible trajectories. -/
lemma ginv_dec {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {j : ℕ} (hj : j < N) :
    1 / (traj F Λ b μ₀ (j + 1)).1 + β / 5 ≤ 1 / (traj F Λ b μ₀ j).1 := by
  have ht : InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := admissible_InDh H h j hj.le
  obtain ⟨hlow, hup, -⟩ := step_D H he hj ht
  have hF1 := (abs_le.1 (H.F1 j hj _ ht)).1
  have hs := ht.1 j le_rfl
  have hg := hs.1
  have hgε := hs.2.1
  have hβ := H.hβ; have hδ := H.hδ; have hδ1 := H.hδ1; have hcg := H.hcg
  obtain ⟨-, -, he3⟩ := eps_facts hcg hβ (eps0u_le he)
  have hκ := H.hκ0
  rw [traj_succ H b μ₀ hj]
  show 1 / F.G j (traj F Λ b μ₀) + β / 5 ≤ 1 / (traj F Λ b μ₀ j).1
  generalize (traj F Λ b μ₀ j).1 = g at *
  generalize F.G j (traj F Λ b μ₀) = G at *
  have hG : 0 < G := by linarith
  -- `G ≤ 5g/4`
  have hbp : betap β δ cg * g ≤ 1 / 4 := by
    unfold betap
    have h1 : ((1 + δ) * β + cg) * g ≤ ((1 + δ) * β + cg) * ε :=
      mul_le_mul_of_nonneg_left hgε (by positivity)
    have h2 : ((1 + δ) * β + cg) * ε ≤ 3 / 2 * ((β + cg) * ε) := by
      have hε0 : 0 ≤ ε := hg.le.trans hgε
      have : 0 ≤ ((1 / 2 - δ) * β + cg / 2) * ε :=
        mul_nonneg (add_nonneg (mul_nonneg (by linarith) hβ.le) (by linarith)) hε0
      linarith
    linarith
  have hG54 : G ≤ 5 / 4 * g := by
    have e1 : betap β δ cg * g ^ 2 = (betap β δ cg * g) * g := by ring
    have := mul_le_mul_of_nonneg_right hbp hg.le
    linarith
  -- `G - g ≥ (β/4) g²`
  have hcgg : cg * g ≤ (1 - δ) * β / 2 := (mul_le_mul_of_nonneg_left hgε hcg.le).trans hgβ
  have hGg : β / 4 * g ^ 2 ≤ G - g := by
    have h1 : cg * g ^ 3 ≤ (1 - δ) * β / 2 * g ^ 2 := by
      have e1 : cg * g ^ 3 = (cg * g) * g ^ 2 := by ring
      rw [e1]; exact mul_le_mul_of_nonneg_right hcgg (sq_nonneg g)
    have h2 : β / 4 * g ^ 2 ≤ (1 - δ) * β / 2 * g ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg g)
    have e2 : δ * β * g ^ 2 = (δ * β) * g ^ 2 := rfl
    nlinarith
  have hfin : β / 5 * (g * G) ≤ G - g := by
    have h1 : β / 5 * (g * G) ≤ β / 5 * (g * (5 / 4 * g)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG54 hg.le) (by positivity)
    have e1 : β / 5 * (g * (5 / 4 * g)) = β / 4 * g ^ 2 := by ring
    linarith
  have e1 : 1 / g - 1 / G = (G - g) / (g * G) := by field_simp
  have h3 : β / 5 ≤ (G - g) / (g * G) := by rw [le_div_iff₀ (mul_pos hg hG)]; exact hfin
  linarith

variable (S : SharpHyp F Λ β δ κ cg cm cT N ε c E e)
include S

/-- **The logarithmic form of Expected result `thm:flow` (i)**: along any admissible trajectory,
for `n ≤ N`, `|1/ǧ_n - 1/b + β n| ≤ 2(1+β) E + (5C/β) log(ǧ_n/b)`. -/
theorem ginv_log {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {n : ℕ} (hn : n ≤ N) :
    |1 / (traj F Λ b μ₀ n).1 - 1 / b + β * n| ≤
      2 * (1 + β) * E + 5 * Cgu β c / β * Real.log ((traj F Λ b μ₀ n).1 / b) := by
  have hβ := H.hβ
  have hsum : ∑ j ∈ range n, (traj F Λ b μ₀ j).1 ≤
      5 / β * Real.log ((traj F Λ b μ₀ n).1 / b) := by
    have hterm : ∀ j ∈ range n, (traj F Λ b μ₀ j).1 ≤
        5 / β * (Real.log (1 / (traj F Λ b μ₀ j).1) - Real.log (1 / (traj F Λ b μ₀ (j + 1)).1)) := by
      intro j hj
      have hjn := mem_range.1 hj
      have hd := ginv_dec H he hgβ h (show j < N by omega)
      have hg1 := (h.1 (j + 1) (by omega)).1
      have hg0 := (h.1 j (by omega)).1
      have hl := div_le_log_sub (d := β / 5) (one_div_pos.2 hg1) (by positivity) hd
      rw [div_div_eq_mul_div, div_one] at hl
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ]
      nlinarith
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← mul_sum, sum_range_sub' (fun j => Real.log (1 / (traj F Λ b μ₀ j).1)) n]
    have hgn := (h.1 n hn).1
    have hb : 0 < b := by have := (h.1 0 (Nat.zero_le _)).1; rwa [traj_zero] at this
    simp only [traj_zero]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 2
    field_simp
  have h1 := ginv_sum_sharpR H he S h hn
  have hC : 0 ≤ Cgu β c := by have := S.hc; unfold Cgu; positivity
  have h2 := mul_le_mul_of_nonneg_left hsum hC
  have e1 : Cgu β c * (5 / β * Real.log ((traj F Λ b μ₀ n).1 / b)) =
      5 * Cgu β c / β * Real.log ((traj F Λ b μ₀ n).1 / b) := by ring
  linarith

end Log

end Hist

end Flow2
