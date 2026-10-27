import Obs2.Flow.RestartFlow
import Obs2.Flow.RestartRec2

/-!
# The restarted `μ^{(2)}` flow and the restart recursion with large transients (B3, T4′)

Copies of `MuChain2F.relRecK2`/`restart_flow2` (`Obs2/Flow/RestartFlow`) for `RelInT`
(`Obs2/Flow/RestartRec2`): **`MuChain2F.relRecT2`**, **`MuChain2F.restart_flowT`**
(`|β_{m+j}| ≤ (|β_m| + (1/8 + 10c_t)M₀)∏_{k<j}|1 − 𝔫F_{m+k}|`, `c_t = c_Kk₀/(s_0M₀) + x_h + t_n + x_p`,
with the `𝒲`/`K` sizes `c_W r_j·2s_jM_j + 6^{-j}w₀`, `(8/15)^jk₀ + 15c_WBr_j²s_jM_j`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

namespace MuChain2F

variable {P : ObsPts d L N} {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : ℕ → OFam .two d L N} {K : ℕ → OAct .two d L N} {m n : ℕ} (H : MuChain2F P C V W K m n)
include H

/-- **The restarted per-block flow gives `RelRecT`** (sequences shifted to start at `m`). -/
theorem relRecT2 {s rr θW θK G : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ} (Tt : ℕ → ℕ → ℝ)
    (hG : ∀ i < n - m, 0 ≤ G i)
    (hTt : ∀ k j, k < j → j < n - m → ∀ i ∈ Ico k j,
      ‖tadInc2 P C V (m + k) (m + j)‖ ≤ Tt k j * G i)
    (I : RelInT (n - m) (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (V (m + i))‖)
      (fun i => shA2 V (m + i)) (fun i => shareDev2 P.a (m + i) (V (m + i)))
      (fun i => shareErrL1_2F P C V W K m (m + i))
      (fun i => ‖1 - frakN2F P C V m (m + i)‖) s rr (fun i => shKt2 K (m + i))
      (fun i => if i = 0 then 0 else shPr2F P C V W m (m + i))
      (fun i => shInit2 C W m (m + i) + if i = 0 then shPr2F P C V W m m else 0)
      G (fun i => ‖frakN2F P C V m (m + i)‖)
      θW θK Tt Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp) :
    RelRecT (n - m) (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (V (m + i))‖)
      (fun i => shA2 V (m + i)) (fun i => shareDev2 P.a (m + i) (V (m + i)))
      (fun i => shareErrL1_2F P C V W K m (m + i))
      (fun i => ‖1 - frakN2F P C V m (m + i)‖) s rr (fun i => shKt2 K (m + i))
      (fun i => if i = 0 then 0 else shPr2F P C V W m (m + i))
      (fun i => shInit2 C W m (m + i) + if i = 0 then shPr2F P C V W m m else 0)
      G (fun i => ‖frakN2F P C V m (m + i)‖)
      θW θK Tt Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp where
  toRelInT := I
  hb := fun _ _ => norm_nonneg _
  hD0' := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hA0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hE0 := fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  hDstep := fun j hj => by
    have := H.shareDev2_succ_leF (j := m + j) (by omega) (by omega)
    simpa only [add_assoc] using this
  hbup := fun j hj => by
    have := H.norm_betaTot2_succ_le (j := m + j) (by omega) (by omega)
    simpa only [add_assoc] using this
  hA := fun j _ => sum_norm_share2_le P.a (m + j) (V (m + j))
  hE := by
    intro j hj
    refine (H.hE2_rawF (j := m + j) (by omega) (by omega)).trans ?_
    have hsplit : shPr2F P C V W m (m + j) + shInit2 C W m (m + j) =
        (if j = 0 then 0 else shPr2F P C V W m (m + j)) +
          (shInit2 C W m (m + j) + if j = 0 then shPr2F P C V W m m else 0) := by
      rcases Nat.eq_zero_or_pos j with rfl | h0
      · simp only [add_zero, if_true]; ring
      · rw [if_neg (by omega), if_neg (by omega)]; ring
    have hdr : ∑ k ∈ Ico m (m + j), ‖tadInc2 P C V k (m + j)‖ *
        ∑ i ∈ Ico k (m + j), (‖frakN2F P C V m i‖ * shA2 V i + shareErrL1_2F P C V W K m i) ≤
        ∑ k ∈ range j, Tt k j * ∑ i ∈ Ico k j, G i *
          (‖frakN2F P C V m (m + i)‖ * shA2 V (m + i) + shareErrL1_2F P C V W K m (m + i)) := by
      rw [sum_Ico_eq_sum_range, show m + j - m = j by omega]
      refine sum_le_sum fun k hk => ?_
      have hkj := mem_range.1 hk
      have e : ∑ i ∈ Ico (m + k) (m + j),
          (‖frakN2F P C V m i‖ * shA2 V i + shareErrL1_2F P C V W K m i) =
          ∑ i ∈ Ico k j, (‖frakN2F P C V m (m + i)‖ * shA2 V (m + i) +
            shareErrL1_2F P C V W K m (m + i)) := by
        rw [sum_Ico_add (fun i => ‖frakN2F P C V m i‖ * shA2 V i +
          shareErrL1_2F P C V W K m i) k j m, add_comm k m, add_comm j m]
      rw [e, mul_sum, mul_sum]
      refine sum_le_sum fun i hi => ?_
      have hi' := mem_Ico.1 hi
      have hGi := hG i (by omega)
      have hT := hTt k j hkj (by omega) i hi
      set x := ‖frakN2F P C V m (m + i)‖ * shA2 V (m + i) + shareErrL1_2F P C V W K m (m + i)
      have hx0 : 0 ≤ x := by
        have h2 : 0 ≤ shA2 V (m + i) := sum_nonneg fun _ _ => norm_nonneg _
        have h3 : 0 ≤ shareErrL1_2F P C V W K m (m + i) := sum_nonneg fun _ _ => norm_nonneg _
        have := norm_nonneg (frakN2F P C V m (m + i))
        positivity
      calc ‖tadInc2 P C V (m + k) (m + j)‖ * x ≤ (Tt k j * G i) * x :=
            mul_le_mul_of_nonneg_right hT hx0
        _ = Tt k j * (G i * x) := by ring
    linarith

/-- **The restart estimate along the restarted chain**: the conclusions of `RelRecK.close`
and `|β_{m+j}| ≤ (|β_m| + (1/8 + 10c_t)M₀) ∏_{k<j}|1 − 𝔫F_{m+k}|`. -/
theorem restart_flowT {s rr θW θK G : ℕ → ℝ} {Wb Kb : ℕ → ℝ → Prop}
    {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ} (Tt : ℕ → ℕ → ℝ)
    (hG : ∀ i < n - m, 0 ≤ G i)
    (hTt : ∀ k j, k < j → j < n - m → ∀ i ∈ Ico k j,
      ‖tadInc2 P C V (m + k) (m + j)‖ ≤ Tt k j * G i)
    (I : RelInT (n - m) (fun i => ‖betaTot2 (L := L) (N := N) (m + i) (V (m + i))‖)
      (fun i => shA2 V (m + i)) (fun i => shareDev2 P.a (m + i) (V (m + i)))
      (fun i => shareErrL1_2F P C V W K m (m + i))
      (fun i => ‖1 - frakN2F P C V m (m + i)‖) s rr (fun i => shKt2 K (m + i))
      (fun i => if i = 0 then 0 else shPr2F P C V W m (m + i))
      (fun i => shInit2 C W m (m + i) + if i = 0 then shPr2F P C V W m m else 0)
      G (fun i => ‖frakN2F P C V m (m + i)‖)
      θW θK Tt Wb Kb C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp) :
    (∀ j ≤ n - m,
      ‖betaTot2 (L := L) (N := N) (m + j) (V (m + j))‖ ≤
        (‖betaTot2 (L := L) (N := N) m (V m)‖ +
          (1 / 8 + 10 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp)) * M₀) *
          ∏ k ∈ range j, ‖1 - frakN2F P C V m (m + k)‖) ∧
    (∀ j ≤ n - m,
      Wb j (cW * rr j * (2 * s j * rkEnv M₀ (fun i => ‖1 - frakN2F P C V m (m + i)‖) j) +
        (1 / 6) ^ j * w₀) ∧
      Kb j ((8 / 15) ^ j * k₀ + 15 * cW * Bk * rr j ^ 2 *
        (s j * rkEnv M₀ (fun i => ‖1 - frakN2F P C V m (m + i)‖) j))) := by
  have R := H.relRecT2 Tt hG hTt I
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h := R.restart_le hj
    simpa only [add_zero] using h
  · obtain ⟨-, -, hW, hK⟩ := (R.close j hj).1 j le_rfl
    exact ⟨hW, hK⟩


end MuChain2F

end

end Obs2
