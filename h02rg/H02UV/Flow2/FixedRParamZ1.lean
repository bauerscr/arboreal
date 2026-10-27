import Flow2.FixedR
import Flow2.Hor2Unique
import Flow2.DiffHist

/-!
# The signed cone as a hypothesis (`ConeS`), and its proof with a hidden `ζ`-channel

The fixed-`β_R` continuation (`Flow2.FixedR*`) uses the smallness `a ≤ a0h` of the `HHyp`
constant only through the signed cone `cone_signed`: two trajectories in `D_ε` from the same `b`
with `μ' ≤ μ` have `μ - μ' ≤ μ_N - μ'_N`. Here this property is a predicate:

* `ConeS F … N ε`: the signed cone;
* `coneS_of_ha0`: it holds under `HHyp` with `a ≤ a0h` (`cone_signed`);
* `cone_signed_z`, `coneS_of_Z`: it holds under `HHyp` with **arbitrary** constants plus the
  uniqueness hypotheses with a hidden coupling `ZHyp` (`Flow2/Hor2Unique.lean`), with
  `a ≤ a0h((1+Λ)/2, κ, A)` and `b_ζ s ≤ (Λ-1)/4`: the cone of `admissible_unique_z` with signs;
* `unique_of_coneS`: uniqueness of the admissible `μ₀`;
* `expand_of_coneS`: the expansion `|μ₀ - μ₁| ≤ |μ_N - μ'_N|` (replaces `traj_expand`).
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {E : Type*} [NormedAddCommGroup E]

variable (F : HData X) (Λ β δ κ cg cm cT : ℝ) in
/-- **The signed cone** (as a hypothesis). -/
def ConeS (N : ℕ) (ε : ℝ) : Prop :=
  ∀ b μ μ', μ' ≤ μ → (∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ)) →
    (∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ')) →
    μ - μ' ≤ (traj F Λ b μ N).2.1 - (traj F Λ b μ' N).2.1

variable {F : HData X} {Λ β δ κ cg cm cT : ℝ}

/-- Uniqueness of the admissible `μ₀` from the signed cone. -/
theorem unique_of_coneS {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (hC : ConeS F Λ β δ κ cg cm cT N ε) {b μ₀ μ₁ : ℝ} (h₀ : Admissible F Λ κ cm cT N ε b μ₀)
    (h₁ : Admissible F Λ κ cm cT N ε b μ₁) : μ₀ = μ₁ := by
  have H₀ := admissible_InDh H h₀
  have H₁ := admissible_InDh H h₁
  rcases le_total μ₁ μ₀ with h | h
  · have := hC b μ₀ μ₁ h H₀ H₁
    rw [h₀.2, h₁.2, sub_self] at this
    linarith
  · have := hC b μ₁ μ₀ h H₁ H₀
    rw [h₀.2, h₁.2, sub_self] at this
    linarith

/-- The expansion of the relevant coordinate from the signed cone. -/
theorem expand_of_coneS {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (hC : ConeS F Λ β δ κ cg cm cT N ε) {b μ₀ μ₁ : ℝ}
    (h₀ : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j))
    (h₁ : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₁ j)) :
    |μ₀ - μ₁| ≤ |(traj F Λ b μ₀ N).2.1 - (traj F Λ b μ₁ N).2.1| := by
  have H₀ := traj_InDh_of H h₀
  have H₁ := traj_InDh_of H h₁
  rcases le_total μ₁ μ₀ with h | h
  · have := hC b μ₀ μ₁ h H₀ H₁
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact this
  · have := hC b μ₁ μ₀ h H₁ H₀
    rw [abs_sub_comm, abs_sub_comm (traj F Λ b μ₀ N).2.1, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact this

/-! ### The signed cone with a hidden coupling -/

/-- One step of the signed cone with a hidden coupling. -/
lemma step_signed_z {N : ℕ} {Z : ℕ → Seq X → E} {A a Aζ aζ bζ ε : ℝ}
    (HZ : ZHyp F Λ β δ κ cg cm cT N Z A a Aζ aζ bζ ε) (hΛ : 1 < Λ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * (1 + p + q) + bζ * sZ Aζ aζ p q))
    {j : ℕ} (hj : j < N) {t t' : Seq X} (ht : InDh Λ β δ κ cg cm cT ε j t)
    (ht' : InDh Λ β δ κ cg cm cT ε j t') (hd : 0 ≤ (t j).2.1 - (t' j).2.1)
    (hg : |(t j).1 - (t' j).1| ≤ p * |(t j).2.1 - (t' j).2.1|)
    (hx : ‖(t j).2.2 - (t' j).2.2‖ ≤ q * |(t j).2.1 - (t' j).2.1|)
    (hh : ∀ i < j, dist3 (t i) (t' i) ≤ (1 + p + q) * |(t j).2.1 - (t' j).2.1|)
    (hz : ‖Z j t - Z j t'‖ ≤ sZ Aζ aζ p q * |(t j).2.1 - (t' j).2.1|) :
    (t j).2.1 - (t' j).2.1 ≤ Λ * (t j).2.1 + F.m j t - (Λ * (t' j).2.1 + F.m j t') := by
  have hM : 0 ≤ (1 + p + q) * |(t j).2.1 - (t' j).2.1| := by positivity
  have Lm := HZ.Lmz j hj t t' ht ht' _ hM hh
  rw [abs_of_nonneg hd] at hg hx Lm hz
  have hm := (abs_le.1 Lm).1
  have a1 : A * |(t j).1 - (t' j).1| ≤ A * (p * ((t j).2.1 - (t' j).2.1)) :=
    mul_le_mul_of_nonneg_left hg HZ.hA
  have a2 : A * ‖(t j).2.2 - (t' j).2.2‖ ≤ A * (q * ((t j).2.1 - (t' j).2.1)) :=
    mul_le_mul_of_nonneg_left hx HZ.hA
  have a6 : bζ * ‖Z j t - Z j t'‖ ≤ bζ * (sZ Aζ aζ p q * ((t j).2.1 - (t' j).2.1)) :=
    mul_le_mul_of_nonneg_left hz HZ.hbζ
  have b1 := mul_le_mul_of_nonneg_right em hd
  have b2 : 0 ≤ (Λ - 1) / 2 * ((t j).2.1 - (t' j).2.1) :=
    mul_nonneg (by linarith) hd
  linarith

/-- **The signed cone with a hidden coupling.** -/
theorem cone_signed_z {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ aζ bζ ε : ℝ}
    (H : HHyp F Λ β δ κ cg cm cT N A' a' ε) (HZ : ZHyp F Λ β δ κ cg cm cT N Z A a Aζ aζ bζ ε)
    (ha0 : a ≤ a0h ((1 + Λ) / 2) κ A)
    (hs : bζ * sZ Aζ aζ (Kh ((1 + Λ) / 2) κ A * a) (Qh κ * a) ≤ (Λ - 1) / 4)
    {b μ μ' : ℝ} (hμ : μ' ≤ μ)
    (h : ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ))
    (h' : ∀ j ≤ N, InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ')) :
    μ - μ' ≤ (traj F Λ b μ N).2.1 - (traj F Λ b μ' N).2.1 := by
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
  exact (key N le_rfl).2.2.2.2

theorem coneS_of_Z {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ aζ bζ ε : ℝ}
    (H : HHyp F Λ β δ κ cg cm cT N A' a' ε) (HZ : ZHyp F Λ β δ κ cg cm cT N Z A a Aζ aζ bζ ε)
    (ha0 : a ≤ a0h ((1 + Λ) / 2) κ A)
    (hs : bζ * sZ Aζ aζ (Kh ((1 + Λ) / 2) κ A * a) (Qh κ * a) ≤ (Λ - 1) / 4) :
    ConeS F Λ β δ κ cg cm cT N ε :=
  fun _ _ _ hμ h h' => cone_signed_z H HZ ha0 hs hμ h h'

end Hist

end Flow2
