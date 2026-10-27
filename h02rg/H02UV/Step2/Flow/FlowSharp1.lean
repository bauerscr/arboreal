import Step2.Flow.FlowF1S3
import Step2.Flow.FlowHV
import Step2.D2.D2Sh13
import Flow2.DiffHist

/-!
# The sharp one-loop coefficient along histories

* `htad_eq`: the history tadpole `htad = 16 Z_{j+1}² (C_j(e₁,0) - C_j(0,0)) w⁽¹⁾_j` is the dressed
  tadpole `tadTil` of `Step2.HV_sharp` (`Cp D (j+1) = Z_{j+1} Γ^int_j`, `wp D j 0 = Z_{j+1} w⁽¹⁾_j`);
* `htad_zero`: `htad = 0` at `j = 0` (no accumulated zero mode);
* `HVs_hist`: `HV_sharp` along histories;
* `Flow2.Hist.ginv_sharp`: the `1/g` form of a sharp (F1) step on an admissible trajectory;
* `tele_sum`, `geom_inv_le`, `geom_Lsq_le`: summation helpers.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The history tadpole is the dressed tadpole.** -/
theorem htad_eq (hP : R.P = Pc) {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) (t : Hist.Seq (Xs R)) :
    htad R j t = tadTil (dData L N R.msq (zh R j t)) j := by
  obtain ⟨hz, -⟩ := hist_dData_hyps R hP hV t
  have hρ8 := (hV 0 (Nat.zero_le _)).2.2.2.2.1
  set D := dData L N R.msq (zh R j t) with hD
  have hZ : ∀ i, D.Z i ≠ 0 :=
    DressedFRD.Data.Z_ne_zero (fun i => (hz i).trans (by linarith only [hρ8]))
  have e1 : (rawHist R j t).w1 = ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern (D.Gint k) x := by
    rw [rawHist_w1_eq]
    refine sum_congr rfl fun k hk => sum_congr rfl fun x _ => ?_
    rw [stCov_eq_dData R hP t (mem_range.1 hk).le]
    simp only [DressedFRD.kmat, sub_zero]
    rfl
  unfold htad tadTil
  rw [e1, stZ'_eq_dData R hV t, stCov_eq_dData R hP t le_rfl, wp_eq_smul D hZ j]
  simp only [DressedFRD.kmat, sub_zero, Cp, Nat.add_sub_cancel, DressedFRD.kern_smul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [show (∑ k ∈ range j, D.Gint k 0) = ∑ k ∈ range j, ∑ x : Lam 2 L N, DressedFRD.kern (D.Gint k) x
    from sum_congr rfl fun k _ => (sum_kern_eq _).symm]
  ring

/-- At `j = 0` there is no accumulated zero mode, so no tadpole. -/
theorem htad_zero (t : Hist.Seq (Xs R)) : htad R 0 t = 0 := by
  unfold htad
  rw [rawHist_w1_eq]
  simp

/-- **`HV_sharp` along histories.** -/
theorem HVs_hist : ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ E1 : ℝ, 0 ≤ E1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ j, 1 ≤ j → j + 1 < N → (∀ i ≤ j, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        |(f1Coef R j t + htad R j t).re - 3 * (Real.log L / (2 * Real.pi))| ≤
          C0sh * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) +
            E1 * (dData L N R.msq (zh R j t)).Mz (j + 1) := by
  intro L _ hL
  obtain ⟨ζbar, hζ, E1, hE1, h'⟩ := HV_sharp L hL
  refine ⟨ζbar, hζ, E1, hE1, fun N R _ _ hP hi0 hN hm0 hm hρ j hj1 hj hV t => ?_⟩
  obtain ⟨hz, hG⟩ := hist_dData_hyps R hP hV t
  rw [f1Coef_eq R hP hi0 hV t, htad_eq R hP hV t]
  exact h' N R.msq (zh R j t) hN hm0 hm (fun i => (hz i).trans hρ) j hj1 hj (ellM R j t)
    (ellM_nonneg R t) hG (histFS R j t).κ

/-! ### Summation helpers -/

/-- Telescoping a per-step bound for `x_{j+1} - x_j + β`. -/
theorem tele_sum {x a g : ℕ → ℝ} {β C : ℝ} {m : ℕ} :
    ∀ n, m ≤ n → (∀ j, m ≤ j → j < n → |x (j + 1) - x j + β| ≤ C * a j + C * g j) →
      |x n - x m + β * ((n : ℝ) - m)| ≤ C * ∑ j ∈ Ico m n, (a j + g j)
  | 0, hn, _ => by
    have : m = 0 := by omega
    subst this; simp
  | n + 1, hn, h => by
    rcases Nat.eq_or_lt_of_le hn with e | hlt
    · rw [← e]; simp
    have ih := tele_sum n (by omega) (fun j hj1 hj2 => h j hj1 (by omega))
    have hs := h n (by omega) (by omega)
    rw [Finset.sum_Ico_succ_top (by omega), mul_add]
    have e2 : x (n + 1) - x m + β * (((n + 1 : ℕ) : ℝ) - m) =
        (x n - x m + β * ((n : ℝ) - m)) + (x (n + 1) - x n + β) := by push_cast; ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    have e3 : C * (a n + g n) = C * a n + C * g n := by ring
    linarith only [ih, hs, e3]

/-- `∑_{1 ≤ j < n} L^{-2j} ≤ 1` for `L ≥ 2`. -/
theorem geom_inv_le {L : ℝ} (hL : 2 ≤ L) (n : ℕ) :
    ∑ j ∈ Ico 1 n, ((L ^ j) ^ 2)⁻¹ ≤ 1 := by
  have hq0 : 0 ≤ (L ^ 2)⁻¹ := by positivity
  have hq1 : (L ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have e : ∀ j, ((L ^ j) ^ 2)⁻¹ = ((L ^ 2)⁻¹) ^ j := fun j => by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow]
  simp only [e]
  refine (geom_sum_Ico_le_of_lt_one hq0 (by linarith)).trans ?_
  rw [pow_one, div_le_one (by linarith)]
  linarith

/-- `∑_{j < n} L^{2(j+1)} ≤ 2 L^{2n}` for `L ≥ 2`. -/
theorem geom_Lsq_le {L : ℝ} (hL : 2 ≤ L) :
    ∀ n : ℕ, ∑ j ∈ range n, (L ^ (j + 1)) ^ 2 ≤ 2 * (L ^ n) ^ 2
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ]
    have ih := geom_Lsq_le hL n
    have h4 : 4 * (L ^ n) ^ 2 ≤ (L ^ (n + 1)) ^ 2 := by
      rw [pow_succ L n, mul_pow]
      have : (4 : ℝ) ≤ L ^ 2 := by nlinarith
      have h0 : 0 ≤ (L ^ n) ^ 2 := sq_nonneg _
      nlinarith
    have h0 : 0 ≤ (L ^ n) ^ 2 := sq_nonneg _
    linarith only [ih, h4, h0]

end

end Step2

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)] {F : HData X} {Λ β δ κ cg cm cT : ℝ}

/-- **A sharp (F1) step in `1/g` form.** If at step `j` the history map satisfies
`|G - g - β g²| ≤ e g² + c g³` on regular histories, then along any trajectory in `D_ε` up to `N`
(no final condition; route (a1))
`|1/g_{j+1} - 1/g_j + β| ≤ 2(1+β) e + 2(β² + (1+β)c) g_j`. -/
theorem ginv_sharpD {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) {b μ₀ : ℝ}
    (h : ∀ j ≤ N, InD3 Λ κ cm cT ε (traj F Λ b μ₀ j)) {j : ℕ}
    (hj : j < N) {e c : ℝ} (he0 : 0 ≤ e) (hc : 0 ≤ c)
    (hF : ∀ t, InDh Λ β δ κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e * (t j).1 ^ 2 + c * (t j).1 ^ 3) :
    |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
      2 * (1 + β) * e + Cgu β c * (traj F Λ b μ₀ j).1 := by
  have ht : InDh Λ β δ κ cg cm cT ε j (traj F Λ b μ₀) := traj_InDh_of H h j (by omega)
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

/-- `ginv_sharpD` along an admissible trajectory (the original statement). -/
theorem ginv_sharp {N : ℕ} {A a ε : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
    (he : ε ≤ eps0u Λ β δ κ cg cm) {b μ₀ : ℝ} (h : Admissible F Λ κ cm cT N ε b μ₀) {j : ℕ}
    (hj : j < N) {e c : ℝ} (he0 : 0 ≤ e) (hc : 0 ≤ c)
    (hF : ∀ t, InDh Λ β δ κ cg cm cT ε j t →
      |F.G j t - (t j).1 - β * (t j).1 ^ 2| ≤ e * (t j).1 ^ 2 + c * (t j).1 ^ 3) :
    |1 / (traj F Λ b μ₀ (j + 1)).1 - 1 / (traj F Λ b μ₀ j).1 + β| ≤
      2 * (1 + β) * e + Cgu β c * (traj F Λ b μ₀ j).1 :=
  ginv_sharpD H he h.1 hj he0 hc hF

end Hist

end Flow2
