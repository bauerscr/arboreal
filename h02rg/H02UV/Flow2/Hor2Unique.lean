import Flow2.History

/-!
# Uniqueness with a separate channel for a hidden history coupling

In `HHyp` the dependence of `m_j` on the past is bounded by `a M`, where `M` bounds the past
distances `dist3(t_i, t'_i)`, and uniqueness (`admissible_unique`) needs `a ≤ a0h`. For the RG map
the mass part of `m_j` depends on the past through one *hidden* coupling `ζ_j` (a causal function
of `t_0, …, t_{j-1}`) with a coefficient of order one, which is not small compared with `a0h`.

Here this dependence gets its own channel:
* (Lmz) `|δm_j| ≤ A|δg_j| + a|δμ_j| + A‖δx_j‖ + a M + b_ζ ‖δζ_j‖`;
* (LZ) `‖δζ_{j+1}‖ ≤ A_ζ(|δg_j| + ‖δx_j‖) + a_ζ(|δμ_j| + M)`, `δζ_0 = 0`.

Along the uniqueness cone `|δg| ≤ p|δμ|`, `‖δx‖ ≤ q|δμ|` the hidden differences are
`‖δζ‖ ≤ s|δμ|` with `s = A_ζ(p + q) + a_ζ(2 + p + q)`, small when `a`, `a_ζ` are small, and
`b_ζ s ≤ (Λ - 1)/4` suffices (`admissible_unique_z`, with `p, q` from `coef_h` at `(1 + Λ)/2`).

`fh_flow_hist_u`: `prop:C6` (existence, band, continuity) from `HHyp` with arbitrary `(A, a)` and a
separate uniqueness statement.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {E : Type*} [NormedAddCommGroup E]

variable (F : HData X) (Λ β δ κ cg cm cT : ℝ)

/-- **The uniqueness hypotheses with a hidden coupling `Z`.** -/
structure ZHyp (N : ℕ) (Z : ℕ → Seq X → E) (A a Aζ aζ bζ ε : ℝ) : Prop where
  hA : 0 ≤ A
  ha : 0 ≤ a
  hAζ : 0 ≤ Aζ
  haζ : 0 ≤ aζ
  hbζ : 0 ≤ bζ
  Z0 : ∀ t t' : Seq X, Z 0 t = Z 0 t'
  LG : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    |F.G j t - F.G j t'| ≤ (1 + a) * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
      A * ‖(t j).2.2 - (t' j).2.2‖ + a * M
  Lmz : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
      A * ‖(t j).2.2 - (t' j).2.2‖ + a * M + bζ * ‖Z j t - Z j t'‖
  LT : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    ‖F.T j t - F.T j t'‖ ≤ κ * ‖(t j).2.2 - (t' j).2.2‖ +
      a * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + a * M
  LZ : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' → ∀ M, 0 ≤ M →
    (∀ i < j, dist3 (t i) (t' i) ≤ M) →
    ‖Z (j + 1) t - Z (j + 1) t'‖ ≤ Aζ * (|(t j).1 - (t' j).1| + ‖(t j).2.2 - (t' j).2.2‖) +
      aζ * (|(t j).2.1 - (t' j).2.1| + M)

variable {F Λ β δ κ cg cm cT}

/-- The size of the hidden differences along the uniqueness cone. -/
def sZ (Aζ aζ p q : ℝ) : ℝ := Aζ * (p + q) + aζ * (2 + p + q)

lemma unique_step_z {N : ℕ} {Z : ℕ → Seq X → E} {A a Aζ aζ bζ ε : ℝ}
    (HZ : ZHyp F Λ β δ κ cg cm cT N Z A a Aζ aζ bζ ε) (hκ0 : 0 ≤ κ) (hΛ : 1 < Λ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (eg : (1 + a) * p + a + A * q + a * (1 + p + q) ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) + a * (1 + p + q) ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * (1 + p + q) + bζ * sZ Aζ aζ p q))
    {j : ℕ} (hj : j < N) {t t' : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (ht' : InDh Λ β δ κ cg cm cT ε j t')
    (hg : |(t j).1 - (t' j).1| ≤ p * |(t j).2.1 - (t' j).2.1|)
    (hx : ‖(t j).2.2 - (t' j).2.2‖ ≤ q * |(t j).2.1 - (t' j).2.1|)
    (hh : ∀ i < j, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t j).2.1 - (t' j).2.1|)
    (hz : ‖Z j t - Z j t'‖ ≤ sZ Aζ aζ p q * |(t j).2.1 - (t' j).2.1|) :
    (1 + Λ) / 2 * |(t j).2.1 - (t' j).2.1| ≤
        |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      |F.G j t - F.G j t'| ≤ p * |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      ‖F.T j t - F.T j t'‖ ≤ q * |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      |(t j).2.1 - (t' j).2.1| ≤ |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| ∧
      ‖Z (j + 1) t - Z (j + 1) t'‖ ≤
        sZ Aζ aζ p q * |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')| := by
  set D := |(t j).2.1 - (t' j).2.1|
  have hD : 0 ≤ D := abs_nonneg _
  have hM : 0 ≤ (1 + p + q) * D := by positivity
  have LG := HZ.LG j hj t t' ht ht' _ hM hh
  have Lm := HZ.Lmz j hj t t' ht ht' _ hM hh
  have LT := HZ.LT j hj t t' ht ht' _ hM hh
  have LZ := HZ.LZ j hj t t' ht ht' _ hM hh
  have hA := HZ.hA; have ha := HZ.ha; have hAζ := HZ.hAζ; have haζ := HZ.haζ; have hbζ := HZ.hbζ
  set s := sZ Aζ aζ p q with hsd
  have hs0 : 0 ≤ s := by rw [hsd]; unfold sZ; positivity
  set D' := |Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')|
  have h1 : Λ * D ≤ D' + |F.m j t - F.m j t'| := by
    have := abs_sub (Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t')) (F.m j t - F.m j t')
    rw [show Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t') - (F.m j t - F.m j t')
      = Λ * ((t j).2.1 - (t' j).2.1) by ring, abs_mul, abs_of_pos (by linarith : 0 < Λ)] at this
    exact this
  have a1 : A * |(t j).1 - (t' j).1| ≤ A * (p * D) := mul_le_mul_of_nonneg_left hg hA
  have a2 : A * ‖(t j).2.2 - (t' j).2.2‖ ≤ A * (q * D) := mul_le_mul_of_nonneg_left hx hA
  have a3 : (1 + a) * |(t j).1 - (t' j).1| ≤ (1 + a) * (p * D) :=
    mul_le_mul_of_nonneg_left hg (by linarith)
  have a4 : κ * ‖(t j).2.2 - (t' j).2.2‖ ≤ κ * (q * D) := mul_le_mul_of_nonneg_left hx hκ0
  have a5 : a * |(t j).1 - (t' j).1| ≤ a * (p * D) := mul_le_mul_of_nonneg_left hg ha
  have a6 : bζ * ‖Z j t - Z j t'‖ ≤ bζ * (s * D) := mul_le_mul_of_nonneg_left hz hbζ
  have b1 := mul_le_mul_of_nonneg_right em hD
  have b2 := mul_le_mul_of_nonneg_right eg hD
  have b3 := mul_le_mul_of_nonneg_right ex hD
  have hmle : |F.m j t - F.m j t'| ≤ (A * p + a + A * q + a * (1 + p + q) + bζ * s) * D := by
    have e : (A * p + a + A * q + a * (1 + p + q) + bζ * s) * D =
        A * (p * D) + a * D + A * (q * D) + a * ((1 + p + q) * D) + bζ * (s * D) := by ring
    rw [e]; linarith only [Lm, a1, a2, a6]
  have hD' : (1 + Λ) / 2 * D ≤ D' := by
    have e2 : (Λ - (A * p + a + A * q + a * (1 + p + q) + bζ * s)) * D =
        Λ * D - (A * p + a + A * q + a * (1 + p + q) + bζ * s) * D := by ring
    linarith only [b1, e2, h1, hmle]
  have hDD : D ≤ D' := by
    have : D ≤ (1 + Λ) / 2 * D := le_mul_of_one_le_left hD (by linarith)
    linarith only [this, hD']
  have b4 := mul_le_mul_of_nonneg_left hD' hp0
  have b5 := mul_le_mul_of_nonneg_left hDD hq0
  have b6 := mul_le_mul_of_nonneg_left hDD hs0
  have hG : |F.G j t - F.G j t'| ≤ p * D' := by
    have e : ((1 + a) * p + a + A * q + a * (1 + p + q)) * D =
        (1 + a) * (p * D) + a * D + A * (q * D) + a * ((1 + p + q) * D) := by ring
    have e2 : p * ((1 + Λ) / 2) * D = p * ((1 + Λ) / 2 * D) := by ring
    linarith only [LG, a3, a2, e, b2, e2, b4]
  have hT : ‖F.T j t - F.T j t'‖ ≤ q * D' := by
    have c1 : a * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) ≤ a * ((p + 1) * D) :=
      mul_le_mul_of_nonneg_left (by simp only [D] at hg ⊢; linarith only [hg]) ha
    have e : (κ * q + a * (p + 1) + a * (1 + p + q)) * D =
        κ * (q * D) + a * ((p + 1) * D) + a * ((1 + p + q) * D) := by ring
    linarith only [LT, a4, c1, e, b3, b5]
  have hZ : ‖Z (j + 1) t - Z (j + 1) t'‖ ≤ s * D := by
    have c1 : Aζ * (|(t j).1 - (t' j).1| + ‖(t j).2.2 - (t' j).2.2‖) ≤ Aζ * ((p + q) * D) := by
      refine mul_le_mul_of_nonneg_left ?_ hAζ
      have e : (p + q) * D = p * D + q * D := by ring
      linarith only [hg, hx, e]
    have c2 : aζ * (|(t j).2.1 - (t' j).2.1| + (1 + p + q) * D) = aζ * (2 + p + q) * D := by
      simp only [D]; ring
    have c3 : s * D = Aζ * ((p + q) * D) + aζ * (2 + p + q) * D := by rw [hsd]; unfold sZ; ring
    linarith only [LZ, c1, c2, c3]
  exact ⟨hD', hG, hT, hDD, hZ.trans b6⟩

/-- **Uniqueness with a hidden coupling.** -/
theorem admissible_unique_z {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ aζ bζ ε : ℝ}
    (H : HHyp F Λ β δ κ cg cm cT N A' a' ε) (HZ : ZHyp F Λ β δ κ cg cm cT N Z A a Aζ aζ bζ ε)
    (ha0 : a ≤ a0h ((1 + Λ) / 2) κ A)
    (hs : bζ * sZ Aζ aζ (Kh ((1 + Λ) / 2) κ A * a) (Qh κ * a) ≤ (Λ - 1) / 4)
    {b μ₀ μ₁ : ℝ} (h₀ : Admissible F Λ κ cm cT N ε b μ₀) (h₁ : Admissible F Λ κ cm cT N ε b μ₁) :
    μ₀ = μ₁ := by
  have hΛ := H.hΛ
  have hΛ2 : 1 < (1 + Λ) / 2 := by linarith
  obtain ⟨hp0, hq0, eg0, ex, em0⟩ := coef_h hΛ2 H.hκ1 HZ.hA HZ.ha ha0
  set p := Kh ((1 + Λ) / 2) κ A * a
  set q := Qh κ * a
  have eg : (1 + a) * p + a + A * q + a * (1 + p + q) ≤ p * ((1 + Λ) / 2) := by
    refine eg0.trans (mul_le_mul_of_nonneg_left ?_ hp0); linarith
  have em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * (1 + p + q) + bζ * sZ Aζ aζ p q) := by
    linarith
  set t := traj F Λ b μ₀
  set t' := traj F Λ b μ₁
  set s := sZ Aζ aζ p q
  have hs0 : 0 ≤ s := by
    have := HZ.hAζ; have := HZ.haζ
    simp only [s]; unfold sZ; positivity
  have key : ∀ k ≤ N,
      |(t k).1 - (t' k).1| ≤ p * |(t k).2.1 - (t' k).2.1| ∧
      ‖(t k).2.2 - (t' k).2.2‖ ≤ q * |(t k).2.1 - (t' k).2.1| ∧
      (∀ i < k, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t k).2.1 - (t' k).2.1|) ∧
      ‖Z k t - Z k t'‖ ≤ s * |(t k).2.1 - (t' k).2.1| ∧
      |μ₀ - μ₁| ≤ |(t k).2.1 - (t' k).2.1| := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [t, t', traj_zero, sub_self, abs_zero, norm_zero, le_refl, and_true]
      refine ⟨mul_nonneg hp0 (abs_nonneg _), mul_nonneg hq0 (abs_nonneg _),
        fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      rw [HZ.Z0 (traj F Λ b μ₀) (traj F Λ b μ₁), sub_self, norm_zero]
      exact mul_nonneg hs0 (abs_nonneg _)
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨ig, ix, ih', iz, iμ⟩ := ih (by omega)
      obtain ⟨s1, s2, s3, s4, s5⟩ := unique_step_z HZ H.hκ0 hΛ hp0 hq0 eg ex em hkN
        (admissible_InDh H h₀ k (by omega)) (admissible_InDh H h₁ k (by omega)) ig ix ih' iz
      have e0 := traj_succ H b μ₀ hkN
      have e1 := traj_succ H b μ₁ hkN
      simp only [t, t'] at s1 s2 s3 s4 s5 ih' ig ix iz ⊢
      rw [e0, e1]
      refine ⟨s2, s3, fun i hi => ?_, ?_, iμ.trans s4⟩
      · rcases (show i = k ∨ i < k by omega) with rfl | hik
        · have : dist3 (traj F Λ b μ₀ i) (traj F Λ b μ₁ i) ≤
              (1 + p + q) * |(traj F Λ b μ₀ i).2.1 - (traj F Λ b μ₁ i).2.1| := by
            unfold dist3
            nlinarith [abs_nonneg ((traj F Λ b μ₀ i).2.1 - (traj F Λ b μ₁ i).2.1)]
          exact this.trans (mul_le_mul_of_nonneg_left s4 (by positivity))
        · exact (ih' i hik).trans (mul_le_mul_of_nonneg_left s4 (by positivity))
      · have e2 : Z (k + 1) (traj F Λ b μ₀) - Z (k + 1) (traj F Λ b μ₁) =
            Z (k + 1) t - Z (k + 1) t' := rfl
        simpa only [e0, e1] using s5
  have := (key N le_rfl).2.2.2.2
  rw [h₀.2, h₁.2, sub_self, abs_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### `prop:C6` with a separate uniqueness statement -/

section Cont

variable {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε) (he : ε ≤ eps0u Λ β δ κ cg cm)
  (hε : 0 < ε)
  (U : ∀ b μ₀ μ₁, Admissible F Λ κ cm cT N ε b μ₀ → Admissible F Λ κ cm cT N ε b μ₁ → μ₀ = μ₁)
include H he hε U

lemma eq_muc_u {b μ₀ : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) (h : Admissible F Λ κ cm cT N ε b μ₀) :
    μ₀ = muc F Λ κ cm cT N ε b :=
  U b _ _ h (muc_spec H he hε hb)

lemma phi_pos_of_gt_u {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ : ℝ}
    (h : muc F Λ κ cm cT N ε b < μ) : 0 < (trajc F Λ cm b μ N).2.1 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (le_max_left μ (cmu Λ cm * b))
    (continuous_phi H b).continuousOn ⟨hn, (phi_pos_of_ge H he hε hb (le_max_right _ _)).le⟩
  have := eq_muc_u H he hε U hb (admissible_of_zero H he hε hb hz)
  linarith [hmem.1]

lemma phi_neg_of_lt_u {b : ℝ} (hb : b ∈ Ioc 0 (bmax β δ cg N ε)) {μ : ℝ}
    (h : μ < muc F Λ κ cm cT N ε b) : (trajc F Λ cm b μ N).2.1 < 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (min_le_left μ (-(cmu Λ cm * b)))
    (continuous_phi H b).continuousOn ⟨(phi_neg_of_le H he hε hb (min_le_right _ _)).le, hn⟩
  have := eq_muc_u H he hε U hb (admissible_of_zero H he hε hb hz)
  linarith [hmem.2]

theorem continuousOn_muc_u : ContinuousOn (muc F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  intro b hb
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro η hη
  set μs := muc F Λ κ cm cT N ε b
  have hp := phi_pos_of_gt_u H he hε U hb (show μs < μs + η / 2 by linarith)
  have hn := phi_neg_of_lt_u H he hε U hb (show μs - η / 2 < μs by linarith)
  have e1 : ∀ᶠ b' in 𝓝 b, 0 < (trajc F Λ cm b' (μs + η / 2) N).2.1 :=
    (continuous_phi' H _).continuousAt.eventually (lt_mem_nhds hp)
  have e2 : ∀ᶠ b' in 𝓝 b, (trajc F Λ cm b' (μs - η / 2) N).2.1 < 0 :=
    (continuous_phi' H _).continuousAt.eventually (gt_mem_nhds hn)
  filter_upwards [eventually_mem_nhdsWithin, (e1.and e2).filter_mono nhdsWithin_le_nhds]
    with b' hb' ⟨h1, h2⟩
  obtain ⟨μ'', hmem, hz⟩ := intermediate_value_Icc (by linarith : μs - η / 2 ≤ μs + η / 2)
    (continuous_phi H b').continuousOn ⟨h2.le, h1.le⟩
  have := eq_muc_u H he hε U hb' (admissible_of_zero H he hε hb' hz)
  rw [Real.dist_eq, ← this, abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

theorem continuousOn_gN_u : ContinuousOn (gN F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  have h : ContinuousOn (fun b => (trajc F Λ cm b (muc F Λ κ cm cT N ε b) N).1)
      (Ioc 0 (bmax β δ cg N ε)) :=
    (continuous_fst.comp (continuous_trajc H le_rfl)).comp_continuousOn
      (continuousOn_id.prodMk (continuousOn_muc_u H he hε U))
  refine h.congr fun b hb => ?_
  simp only [gN]
  rw [trajc_eq_traj H (muc_spec H he hε hb) N le_rfl N le_rfl]

/-- **`prop:C6` with a separate uniqueness statement.** The constants `(A, a)` of `H` are
arbitrary (only (F1)–(F3), causality and continuity are used). -/
theorem fh_flow_hist_u :
    (∀ b ∈ Ioc 0 (bmax β δ cg N ε), ∃! μ₀, Admissible F Λ κ cm cT N ε b μ₀) ∧
    (∀ b μ₀, Admissible F Λ κ cm cT N ε b μ₀ → ∀ j < N,
      |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
        2 * (1 + β) * δ * β + Cgu β cg * (traj F Λ b μ₀ j).1) ∧
    ContinuousOn (muc F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) ∧
    ContinuousOn (gN F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  refine ⟨fun b hb => ?_, fun b μ₀ h j hj => ginv_admissible H he h hj,
    continuousOn_muc_u H he hε U, continuousOn_gN_u H he hε U⟩
  obtain ⟨μ₀, h⟩ := exists_admissible H he hε hb
  exact ⟨μ₀, h, fun μ₁ h₁ => U b _ _ h₁ h⟩

end Cont

lemma a0h_pos' (hΛ : 1 < Λ) (hκ1 : κ < 1) {A : ℝ} (hA : 0 ≤ A) : 0 < a0h ((1 + Λ) / 2) κ A :=
  a0h_pos (by linarith) hκ1 hA

end Hist

end Flow2
