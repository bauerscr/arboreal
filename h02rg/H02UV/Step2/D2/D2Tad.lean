import Step2.D2.D2Past

/-!
# The tadpole term: `T_j = 8d δ_j ∑_x w(x, 0)`

`tadT_eq`: for a translation-invariant symmetric `w` of range `r` (`CovH w r`) and `C_j` with
`C_j(x,x) = c₀`, `C_j(x ± e, x) = c₀ + δ`,

  `T_j = tadT B_+ i₀ w C_j = 8 d δ ∑_x w(x, 0)`   (`= 16 δ ŵ(0)` in `d = 2`).

The `c₀` (gradient) and `y` parts drop out (`betaQ_g_z`, `betaQ_g_y`); only the mass shift
`2dδ` survives (`betaQ_g_nu`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem shift_sub_eg (c₀ δ : ℂ) :
    shiftL d c₀ δ (eC 3) - eC 3 = (-c₀) • eC 0 + (-δ) • eC 1 + (2 * d * δ) • eC 2 := by
  funext a; fin_cases a <;> simp [shiftL, eC]

/-- **The tadpole term.** `T_j = 8 d δ ∑_x w(x, 0)`. -/
theorem tadT_eq (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d)
    {w C : Matrix (Lam d L N) (Lam d L N) ℂ} {r : ℕ} (Hw : CovH w r)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + r + 4) < L ^ N)
    {c₀ δ : ℂ} (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) :
    tadT (Bp (L := L) (N := N) j b) i₀ w C = 8 * d * δ * ∑ x, w x 0 := by
  let D : FlowSeq d L N := ⟨fun _ => w, fun _ => 1, fun _ => ⟨0, 0, 0, 0⟩⟩
  have hDC : D.C j = w := rfl
  set X := Bp (L := L) (N := N) j b
  have hc : (X.card : ℂ) ≠ 0 := by
    have := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1.card_pos
    exact_mod_cast this.ne'
  set s := shiftL d c₀ δ (eC 3) - eC 3
  have hs3 : s 3 = 0 := by simp [s, shiftL, eC, Matrix.vecHead, Matrix.vecTail]
  have ev : ∀ (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ), inv' (VcoupL Y v) = VcoupL Y v :=
    fun Y v => mem_Ev.1 (unif_mem_Ev _ _ _ _)
  have e1 : mu4 (base X) i₀ i₀ (Xc w (VcoupL X s) (VcoupL univ (eC 3))) =
      2 * X.card * D.betaQ j j b i₀ s (eC 3) 3 := by
    rw [D.betaQ_self_g_eq hL hj hb, hDC,
      mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ hs3) (degLe_VcoupL _ _)]
    simp only [X] at hc ⊢
    field_simp
  have e2 : mu4 (base X) i₀ i₀ (Xc w (VcoupL univ s) (VcoupL X (eC 3))) =
      2 * X.card * D.betaQ j j b i₀ (eC 3) s 3 := by
    rw [D.betaQ_self_g_eq hL hj hb, hDC, FC_comm _ (ev _ _) (ev _ _),
      mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ hs3) (degLe_VcoupL _ _)]
    simp only [X] at hc ⊢
    field_simp
  have hH : CovH (D.C j) r := Hw
  have hz := D.betaQ_g_z hL hj hb i₀ hH hX
  have hy := D.betaQ_g_y hL hj hb i₀ hH hX
  have hn := D.betaQ_g_nu hL hj hb i₀ hH hX
  rw [hDC] at hn
  rw [tadT_shift hc₀ hδ hδ', e1, e2]
  have hsv : s = (-c₀) • eC 0 + (-δ) • eC 1 + (2 * d * δ) • eC 2 := shift_sub_eg c₀ δ
  rw [← mul_add, mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hc), hsv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (-c₀) * hz + (-δ) * hy + (2 * d * δ) * hn

/-! ### The bound in normalised units -/

theorem sum_norm_ball_le {F : Lam d L N → ℂ} {R : ℕ} (hF : ∀ x, R < supNorm x → F x = 0) {M : ℝ}
    (hM : ∀ x, ‖F x‖ ≤ M) : ∑ x, ‖F x‖ ≤ (2 * R + 1) ^ d * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set S := univ.filter fun y : Lam d L N => supNorm (y - 0) ≤ R
  have hS : ∀ x ∉ S, ‖F x‖ = 0 := by
    intro x hx
    simp only [S, mem_filter, mem_univ, true_and, sub_zero, not_le] at hx
    rw [hF x hx, norm_zero]
  rw [← sum_subset (subset_univ S) (fun x _ hx => hS x hx)]
  have hc : (S.card : ℝ) ≤ (2 * R + 1) ^ d := by
    have h := card_ball_le (d := d) (L := L) (N := N) 0 R
    exact_mod_cast h
  calc ∑ x ∈ S, ‖F x‖ ≤ ∑ _x ∈ S, M := sum_le_sum fun x _ => hM x
    _ = S.card * M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * R + 1) ^ d * M := by gcongr

theorem geom_sq_le {L : ℝ} (hL : 2 ≤ L) : ∀ j : ℕ,
    ∑ k ∈ range (j + 1), L ^ (2 * k) ≤ 4 / 3 * L ^ (2 * j)
  | 0 => by norm_num
  | j + 1 => by
    rw [sum_range_succ]
    have ih := geom_sq_le hL j
    have h4 : 4 ≤ L ^ 2 := by nlinarith
    have hp : 0 ≤ L ^ (2 * j) := by positivity
    have e : L ^ (2 * (j + 1)) = L ^ 2 * L ^ (2 * j) := by ring
    rw [e]; nlinarith

section D2

variable {L N : ℕ} [NeZero L]

end D2

end

end Step2
