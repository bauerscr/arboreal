import PtCorr2.Cont.ContWire1
import PtCorr2.Obs.ProdBd2Top

set_option autoImplicit false

/-!
# Top coalescence: the error `E_{N_h}` of the restart with large transients (pure part and the
top-scale product/initial-tadpole bounds)

* **`Obs2.RelRecT.ct_bD_le`**: `b_j + D_j ≤ 2M_j` (the bound inside `cw2_A_le`).
* **`Obs2.RelRecT.ct_E_top`**: the error `E_n` of the step `n` itself, from `close` at horizon `n`
  and the inputs at the index `n` only (split of `E_n`, tadpole decay `T_{k,n}`, `6/7 ≤ a_n`,
  activity, product parts, initial tadpole at `n`):
  `E_n ≤ (c_δr_n²a_n + 2c_t(3/4)^n)M_n` (copy of `RelRecT.E_le` at `j = n`; analogue of
  `RelRec.E_top`).
* **`PtCorr2.ct_prodBd2F_top`**, **`PtCorr2.ct_initBd2F_top`**: `ProdBd2F`, `InitBd2F` with horizon
  `N_h + 1` along the restarted history (only `ValidAtL` at `N_h`; copies of `prodBd2F_hist`,
  `initBd2F_hist` with `delta_hist_le2L`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset

namespace RelRecT

variable {n : ℕ} {b A D E a s r Kt Pr X G nn θW θK : ℕ → ℝ} {T : ℕ → ℕ → ℝ}
  {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk ck cK cP cg Bτ q rb cδ M₀ k₀ xh tn w₀ κb xp : ℝ}

/-- `b_j + D_j ≤ 2M_j` along the restart. -/
theorem ct_bD_le (H : RelRecT n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ
    q rb cδ M₀ k₀ xh tn w₀ κb xp) {j : ℕ} (hj : j ≤ n) : b j + D j ≤ 2 * rkEnv M₀ a j := by
  obtain ⟨hbj, hDj, -, -⟩ := (H.close j hj).1 j le_rfl
  have hM := H.hM0
  have hct0 := H.ct_nonneg
  have hctb := H.hct
  have hS := H.sum_le hj
  have hT := rk_geom_rho j
  have henv := H.env_pos hj
  have hbD := H.hbD0
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn + xp
  set Gs := ∑ k ∈ range j, (3 / 4 : ℝ) ^ k
  set Sm := cδ * ∑ k ∈ range j, r k ^ 2
  have hG0 : 0 ≤ Gs := sum_nonneg fun _ _ => by positivity
  have hS0 : 0 ≤ Sm := mul_nonneg H.hcδ0 (sum_nonneg fun _ _ => sq_nonneg _)
  have h1 : b 0 / M₀ + D 0 / M₀ ≤ 1 := by rw [← add_div, div_le_one hM]; exact hbD
  have hctG : ct * Gs ≤ 1 / 48 * 4 := mul_le_mul hctb hT hG0 (by norm_num)
  have hsum : (b 0 / M₀ + Sm + 7 / 3 * ct * Gs) + (D 0 / M₀ + 2 * Sm + 14 / 3 * ct * Gs) ≤ 2 := by
    nlinarith
  calc b j + D j
      ≤ (b 0 / M₀ + Sm + 7 / 3 * ct * Gs) * rkEnv M₀ a j +
        (D 0 / M₀ + 2 * Sm + 14 / 3 * ct * Gs) * rkEnv M₀ a j := add_le_add hbj hDj
    _ = ((b 0 / M₀ + Sm + 7 / 3 * ct * Gs) + (D 0 / M₀ + 2 * Sm + 14 / 3 * ct * Gs)) *
        rkEnv M₀ a j := by ring
    _ ≤ 2 * rkEnv M₀ a j := mul_le_mul_of_nonneg_right hsum henv.le

set_option maxHeartbeats 1000000 in
/-- **The error of the top step `n`** of the restart with large transients:
`E_n ≤ (c_δr_n²a_n + 2c_t(3/4)^n)M_n`, from `close` at horizon `n` and the inputs at `n`. -/
theorem ct_E_top (H : RelRecT n b A D E a s r Kt Pr X G nn θW θK T Wb Kb C₁ cW Bk ck cK cP cg Bτ
    q rb cδ M₀ k₀ xh tn w₀ κb xp)
    (hEn : E n ≤ Kt n + ∑ k ∈ range n, T k n *
      ∑ i ∈ Ico k n, G i * (nn i * A i + E i) + Pr n + X n)
    (hTn : ∀ k < n, 0 ≤ T k n ∧ T k n ≤ Bτ * q ^ (n - k))
    (han : 6 / 7 ≤ a n)
    (hKtn : ∀ k, 0 ≤ k → Kb n k → Kt n ≤ cK * k / s n)
    (hPrn : ∀ m : ℕ → ℝ, (∀ i ≤ n, 0 ≤ m i ∧ s i * A i ≤ m i ∧ Wb i (r i * m i)) →
      Pr n ≤ cP * ∑ i ∈ range (n + 1), q ^ (n - i) * (r i ^ 2 * m i / s i))
    (hXn : X n ≤ xh * (1 / 2) ^ n * M₀) :
    E n ≤ (cδ * r n ^ 2 * a n +
      2 * (cK * k₀ / (s 0 * M₀) + xh + tn + xp) * (3 / 4) ^ n) * rkEnv M₀ a n := by
  obtain ⟨hB, hEi⟩ := H.close n le_rfl
  have hAi : ∀ i ≤ n, A i ≤ 2 * rkEnv M₀ a i := fun i hi => H.cw2_A_le hi
  have hKj := (hB n le_rfl).2.2.2
  have hWi : ∀ i ≤ n, Wb i (cW * r i * (2 * s i * rkEnv M₀ a i) + (1 / 6) ^ i * w₀) :=
    fun i hi => (hB i hi).2.2.1
  have hXj0 : X n ≤ xh * (3 / 4) ^ n * rkEnv M₀ a n := by
    have h2 := H.env_le (le_refl n) 0 (Nat.zero_le _)
    rw [rkEnv_zero, Nat.sub_zero] at h2
    have hxh := H.hxh
    have hMj := H.env_pos (le_refl n)
    refine hXn.trans ?_
    calc xh * (1 / 2) ^ n * M₀ ≤ xh * (1 / 2) ^ n * ((7 / 6) ^ n * rkEnv M₀ a n) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = xh * (7 / 12) ^ n * rkEnv M₀ a n := by
          rw [show (7 / 12 : ℝ) = 1 / 2 * (7 / 6) by norm_num, mul_pow]; ring
      _ ≤ xh * (3 / 4) ^ n * rkEnv M₀ a n := by
          have h7 : (7 / 12 : ℝ) ^ n ≤ (3 / 4) ^ n :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) n
          have := mul_le_mul_of_nonneg_left h7 hxh
          exact mul_le_mul_of_nonneg_right this hMj.le
  have hjle : n ≤ n := le_rfl
  set j := n with hjn
  set M := rkEnv M₀ a with hMdef
  set ct := cK * k₀ / (s 0 * M₀) + xh + tn + xp with hct
  have hMj := H.env_pos hjle
  have hsj := H.hs j hjle
  have hrj := H.hr0 j hjle
  have hcW0 : 0 ≤ cW := by linarith [H.hcW1]
  have hcg := H.hcg
  have hcδ0 := H.hcδ0
  have hBk := H.hBk
  have hcK := H.hcK
  have hrb0 : 0 ≤ rb := hrj.trans (H.hrb j hjle)
  have hct0 : 0 ≤ ct := H.ct_nonneg
  have hri := H.r_mono hjle
  have hMi := H.env_le hjle
  -- the activity term
  have hKt : Kt j ≤ 16 * cK * cW * Bk * r j ^ 2 * M j + cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * M j := by
    have h := hKtn _ (by have := H.hk₀; positivity) hKj
    have h2 := H.kt_tr_le hjle
    have e : cK * ((8 / 15) ^ j * k₀ + 15 * cW * Bk * r j ^ 2 * (s j * M j)) / s j =
        cK * ((8 / 15) ^ j * k₀) / s j + 15 * cK * cW * Bk * r j ^ 2 * M j := by
      field_simp
    have : 0 ≤ cK * cW * Bk * r j ^ 2 * M j := by positivity
    linarith
  -- the drift: steady and transient summands
  set Xs := 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * M j with hXs
  have hXs0 : 0 ≤ Xs := by positivity
  have htn := H.htn
  set Xt := cg * rb * (2 * (ct + tn)) * (3 / 4) ^ j * M j with hXt
  have hXt0 : 0 ≤ Xt := by positivity
  have hterm : ∀ i < j, G i * (nn i * A i + E i) ≤ (Xs + Xt) * (14 / 9) ^ (j - i) := by
    intro i hij
    have hin : i < n := by omega
    have hMi' : M i ≤ (4 / 3) ^ (j - i) * M j := by
      refine (hMi i hij.le).trans (mul_le_mul_of_nonneg_right ?_ hMj.le)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hMi0 : 0 < M i := H.env_pos (by omega)
    have hri' := hri i hij.le
    have hr0i := H.hr0 i hin.le
    have hrbi := H.hrb i hin.le
    obtain ⟨hG0, hG1⟩ := H.hG i hin
    obtain ⟨hnn0, hnn1⟩ := H.hnn i hin
    obtain ⟨ha1, ha2⟩ := H.ha i hin
    set Pm := (4 / 3 : ℝ) ^ (j - i) * M j with hPm
    have hPm0 : 0 ≤ Pm := by positivity
    have hAi' : A i ≤ 2 * Pm := (hAi i hij.le).trans (by linarith)
    have hGi : G i ≤ cg * r j := hG1.trans (mul_le_mul_of_nonneg_left hri' hcg)
    -- steady part of `E_i`
    have hE1 : cδ * r i ^ 2 * a i * M i ≤ cδ * (rb * r j) * (2 * Pm) := by
      have h1 : r i ^ 2 ≤ rb * r j := by rw [sq]; exact mul_le_mul hrbi hri' hr0i hrb0
      have h2 : a i * M i ≤ 2 * Pm := mul_le_mul ha2 hMi' hMi0.le (by norm_num)
      have e : cδ * r i ^ 2 * a i * M i = (cδ * r i ^ 2) * (a i * M i) := by ring
      rw [e]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hcδ0) h2
        (mul_nonneg (by linarith) hMi0.le) (by positivity)
    -- transient part of `E_i`
    have h1ρ : (3 / 4 : ℝ) ^ i * M i ≤ (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
        have e : (3 / 4 : ℝ) ^ j * (14 / 9) ^ (j - i) = (3 / 4) ^ i * (7 / 6) ^ (j - i) := by
          have hji : (3 / 4 : ℝ) ^ j = (3 / 4) ^ i * (3 / 4) ^ (j - i) := by
            rw [← pow_add]; congr 1; omega
          rw [hji, mul_assoc, ← mul_pow]; norm_num
        rw [← mul_assoc, e, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hMi i hij.le) (by positivity)
    have hE2 : 2 * ct * (3 / 4) ^ i * M i ≤ 2 * ct * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
      have := mul_le_mul_of_nonneg_left h1ρ (by positivity : (0 : ℝ) ≤ 2 * ct)
      linarith
    have hE3 : 2 * tn * (3 / 4) ^ i * M i ≤ 2 * tn * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
      have := mul_le_mul_of_nonneg_left h1ρ (by positivity : (0 : ℝ) ≤ 2 * tn)
      linarith
    have hEi' := hEi i hij
    have hEsplit : E i ≤ cδ * (rb * r j) * (2 * Pm) +
        2 * ct * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by
      have e : (cδ * r i ^ 2 * a i + 2 * ct * (3 / 4) ^ i) * M i =
          cδ * r i ^ 2 * a i * M i + 2 * ct * (3 / 4) ^ i * M i := by ring
      linarith
    have t2 : nn i * A i ≤ cg * r j * (2 * Pm) + 2 * tn * (3 / 4) ^ i * M i := by
      have hA0i := H.hA0 _ hin.le
      have h1 : nn i * A i ≤ (cg * r i + tn * (1 / 2) ^ i) * A i :=
        mul_le_mul_of_nonneg_right hnn1 hA0i
      have h2 : cg * r i * A i ≤ cg * r j * (2 * Pm) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hri' hcg) hAi' hA0i (by positivity)
      have h3 : tn * (1 / 2) ^ i * A i ≤ tn * (1 / 2) ^ i * (2 * M i) :=
        mul_le_mul_of_nonneg_left (hAi i hij.le) (by positivity)
      have h4 : (1 / 2 : ℝ) ^ i ≤ (3 / 4) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
      have h5 : tn * (1 / 2) ^ i * (2 * M i) ≤ 2 * tn * (3 / 4) ^ i * M i := by
        have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * tn * M i)
        linarith
      linarith [show (cg * r i + tn * (1 / 2) ^ i) * A i = cg * r i * A i +
        tn * (1 / 2) ^ i * A i by ring]
    have hsum0 : 0 ≤ nn i * A i + E i := add_nonneg (mul_nonneg hnn0 (H.hA0 _ hin.le)) (H.hE0 i hin)
    have t3 : G i * (nn i * A i + E i) ≤ cg * r j * (cg * r j * (2 * Pm) +
        (cδ * (rb * r j) * (2 * Pm) +
          2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j))) :=
      mul_le_mul hGi (by linarith) hsum0 (by positivity)
    have hP43 : Pm ≤ (14 / 9) ^ (j - i) * M j := by
      refine mul_le_mul_of_nonneg_right ?_ hMj.le
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hrj' : cg * r j * (2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j)) ≤
        Xt * (14 / 9) ^ (j - i) := by
      have h1 : cg * r j ≤ cg * rb := mul_le_mul_of_nonneg_left (H.hrb j hjle) hcg
      have h2 : 0 ≤ 2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j) := by positivity
      have := mul_le_mul_of_nonneg_right h1 h2
      rw [hXt]
      linarith [show cg * rb * (2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j)) =
        cg * rb * (2 * (ct + tn)) * (3 / 4) ^ j * M j * (14 / 9) ^ (j - i) by ring]
    have hst : cg * r j * (cg * r j * (2 * Pm) + cδ * (rb * r j) * (2 * Pm)) ≤
        Xs * (14 / 9) ^ (j - i) := by
      have e : cg * r j * (cg * r j * (2 * Pm) + cδ * (rb * r j) * (2 * Pm)) =
          2 * cg * (cg + cδ * rb) * r j ^ 2 * Pm := by ring
      rw [e, hXs]
      have h1 : 2 * cg * (cg + cδ * rb) * r j ^ 2 * Pm ≤
          2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * Pm := by
        have : 0 ≤ 2 * cg * r j ^ 2 * Pm := by positivity
        have e1 : 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * Pm =
            2 * cg * (cg + cδ * rb) * r j ^ 2 * Pm + 2 * cg * r j ^ 2 * Pm := by ring
        linarith
      have h2 : 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * Pm ≤
          2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * ((14 / 9) ^ (j - i) * M j) :=
        mul_le_mul_of_nonneg_left hP43 (by positivity)
      linarith [show 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * ((14 / 9) ^ (j - i) * M j) =
        2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * M j * (14 / 9) ^ (j - i) by ring]
    have e : cg * r j * (cg * r j * (2 * Pm) +
        (cδ * (rb * r j) * (2 * Pm) + 2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j))) =
        cg * r j * (cg * r j * (2 * Pm) + cδ * (rb * r j) * (2 * Pm)) +
          cg * r j * (2 * (ct + tn) * (3 / 4) ^ j * ((14 / 9) ^ (j - i) * M j)) := by ring
    rw [e] at t3
    linarith [show (Xs + Xt) * (14 / 9) ^ (j - i) = Xs * (14 / 9) ^ (j - i) +
      Xt * (14 / 9) ^ (j - i) by ring]
  have hdrift := rk_drift (f := fun i => G i * (nn i * A i + E i)) (T := fun k => T k j)
    (add_nonneg hXs0 hXt0) H.hBτ H.hq0 H.hq hterm fun k hk => hTn k hk
  -- the product parts
  have hprod : Pr j ≤ 3 * cP * cW * r j ^ 2 * M j + xp * (3 / 4) ^ j * M j := by
    have h := hPrn (fun i => cW * (2 * s i * M i) + (1 / 6) ^ i * w₀ / r i) fun i hi => by
      have hsi := H.hs i (by omega)
      have hMi0 := H.env_pos (j := i) (by omega)
      have hri0 := H.r_pos (j := i) (by omega)
      have hw := H.hw₀
      refine ⟨by positivity, ?_, H.hWm i _ _ (hWi i hi) (le_of_eq (by field_simp))⟩
      have h1 : s i * A i ≤ s i * (2 * M i) := mul_le_mul_of_nonneg_left (hAi i hi) hsi.le
      have h2 : 2 * s i * M i ≤ cW * (2 * s i * M i) :=
        le_mul_of_one_le_left (by positivity) H.hcW1
      have h3 : 0 ≤ (1 / 6 : ℝ) ^ i * w₀ / r i := by positivity
      linarith [show s i * (2 * M i) = 2 * s i * M i by ring]
    refine h.trans ?_
    have hsplit : ∑ i ∈ range (j + 1), q ^ (j - i) *
        (r i ^ 2 * (cW * (2 * s i * M i) + (1 / 6) ^ i * w₀ / r i) / s i) =
        ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (cW * (2 * s i * M i)) / s i) +
          ∑ i ∈ range (j + 1), q ^ (j - i) * (r i * ((1 / 6) ^ i * w₀) / s i) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      have hri0 := H.r_pos (j := i) (by have := mem_range.1 hi; omega)
      have hsi := H.hs i (by have := mem_range.1 hi; omega)
      field_simp
    rw [hsplit, mul_add]
    have hP2 := H.pr_tr_le hjle
    suffices hP1 : cP * ∑ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (cW * (2 * s i * M i)) / s i)
        ≤ 3 * cP * cW * r j ^ 2 * M j by linarith
    have h1 : ∀ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (cW * (2 * s i * M i)) / s i) ≤
        2 * cW * r j ^ 2 * M j * (4 / 3 * q) ^ (j - i) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have hsi := H.hs i (by omega)
      have hr2 : r i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ (H.hr0 i (by omega)) (hri i hij) 2
      have hMi' : M i ≤ (4 / 3) ^ (j - i) * M j := by
        refine (hMi i hij).trans (mul_le_mul_of_nonneg_right ?_ hMj.le)
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have e : r i ^ 2 * (cW * (2 * s i * M i)) / s i = r i ^ 2 * (2 * cW * M i) := by
        field_simp
      rw [e]
      have hMi0 := H.env_pos (j := i) (by omega)
      have h2 : r i ^ 2 * (2 * cW * M i) ≤ r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * M j)) :=
        mul_le_mul hr2 (mul_le_mul_of_nonneg_left hMi' (by positivity)) (by positivity)
          (sq_nonneg _)
      calc _ ≤ q ^ (j - i) * (r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * M j))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg H.hq0 _)
        _ = _ := by rw [mul_pow]; ring
    have h2 := sum_le_sum h1
    rw [← mul_sum] at h2
    have hg := geom_tail_le' (y := 4 / 3 * q) (by have := H.hq0; positivity)
      (by have := H.hq; linarith) j
    have h3 : 0 ≤ 2 * cW * r j ^ 2 * M j := by positivity
    have h4 := mul_le_mul_of_nonneg_left hg h3
    have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) H.hcP
    linarith
  have hXj : X j ≤ xh * (3 / 4) ^ j * M j := hXj0
  have hE := hEn
  -- the steady and transient totals
  have hτ := H.hτ
  have hBτ := H.hBτ
  have hdt : 2 * Bτ * Xt ≤ (ct + tn) * (3 / 4) ^ j * M j := by
    rw [hXt]
    have h1 : 0 ≤ (ct + tn) * (3 / 4) ^ j * M j := by positivity
    have e : 2 * Bτ * (cg * rb * (2 * (ct + tn)) * (3 / 4) ^ j * M j) =
        (2 * Bτ * cg * rb) * (2 * ((ct + tn) * (3 / 4) ^ j * M j)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hτ
      (by positivity : (0 : ℝ) ≤ 2 * ((ct + tn) * (3 / 4) ^ j * M j))
    linarith
  have hsteady : 16 * cK * cW * Bk * r j ^ 2 * M j + 2 * Bτ * Xs + 3 * cP * cW * r j ^ 2 * M j ≤
      cδ * r j ^ 2 * a j * M j := by
    have e : 16 * cK * cW * Bk * r j ^ 2 * M j + 2 * Bτ * Xs + 3 * cP * cW * r j ^ 2 * M j =
        (16 * cK * cW * Bk + 3 * cP * cW + 4 * Bτ * cg * (1 + cg) +
          4 * Bτ * cg * cδ * rb) * (r j ^ 2 * M j) := by rw [hXs]; ring
    rw [e]
    have hrM : 0 ≤ r j ^ 2 * M j := by positivity
    have h6 := mul_le_mul_of_nonneg_right H.hcδ hrM
    have h7 : 6 / 7 * cδ * (r j ^ 2 * M j) ≤ cδ * r j ^ 2 * a j * M j := by
      have := mul_le_mul_of_nonneg_left han (mul_nonneg hcδ0 hrM)
      linarith
    linarith
  have hct' : cK * k₀ / (s 0 * M₀) * (3 / 4) ^ j * M j + (ct + tn) * (3 / 4) ^ j * M j +
      xh * (3 / 4) ^ j * M j + xp * (3 / 4) ^ j * M j = 2 * ct * (3 / 4) ^ j * M j := by
    rw [hct]; ring
  have hfin : E j ≤ cδ * r j ^ 2 * a j * M j + 2 * ct * (3 / 4) ^ j * M j := by
    have e2 : 2 * Bτ * (Xs + Xt) = 2 * Bτ * Xs + 2 * Bτ * Xt := by ring
    linarith
  linarith [show (cδ * r j ^ 2 * a j + 2 * ct * (3 / 4) ^ j) * M j =
    cδ * r j ^ 2 * a j * M j + 2 * ct * (3 / 4) ^ j * M j by ring]


end RelRecT

end

end Obs2

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 2000000 in
/-- **`ProdBd2F` up to the step `N_h`** (horizon `N_h + 1`; copy of `prodBd2F_hist` with
`delta_hist_le2L`). -/
theorem ct_prodBd2F_top {Cp εp : ℝ} (hPB : PObsBounds L Cp εp) (hCp : 0 ≤ Cp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1) (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) {m : ℕ} (o' : ObsSt .two L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P m o')
    (hs0 : ObsSymInv m o') (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a)
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n = Nh + 1) (hmn : m ≤ Nh) (hnN : n < N)
    (hVL : ValidAtL R Nh) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (hL : prodLb ≤ L) :
    ProdBd2F R P m o' t n (fun i => cR R Λ cm C₂ * (t (m + i)).1) (prodCP2 L Cp) (2 / L) := by
  intro j hj0 hj mm hmm
  set rr : ℕ → ℝ := fun i => cR R Λ cm C₂ * (t (m + i)).1 with hrr
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  have HC := muChain2F_histFrom R P m o' t (by omega) hnN hf0
  have hDh : ∀ k ≤ Nh, Flow2.Hist.InDh Λ β δ κ cg cm cT ε k t := fun k hk =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hr0 : ∀ k ≤ Nh - m, 0 ≤ rr k := fun k hk => mul_nonneg hcR (ht.1 (m + k) (by omega)).1.le
  have hs : ∀ i, 0 < histS R i t := histS_pos' R hρ0 hρ t
  have hm0 : ∀ k ≤ j, 0 ≤ mm k := fun k hk => (hmm k hk).1
  -- the product parts of the steps `m + i`, `i < j`
  have hPk : ∀ i < j, ∀ c'' ∈ blockIdx (L := L) (N := N) (m + i + 1),
      Tj 2 (L : ℝ) (m + i + 1) (histS R (m + i + 1) t)
        ((prodO P (m + i) (histCovO R t (m + i)) (histVF2 R P m o' t (m + i))
          (histWF2 R P m o' t (m + i)) c'' : SA .two (Lam 2 L N)).a) ≤
        ENNReal.ofReal (2 * Cp * rr i ^ 2 * mm i) ∧
      prodO P (m + i) (histCovO R t (m + i)) (histVF2 R P m o' t (m + i))
          (histWF2 R P m o' t (m + i)) c'' ∈
        osub P (nbhd (m + i + 1) (blockSet (L := L) (N := N) (m + i + 1) c'')) := by
    intro i hi c'' hc''
    have hrk := hr0 i (by omega)
    obtain ⟨h1, h2⟩ := prod_hist_stepF R hPB hSB hV hm hβ hδ1 H P Obs2.wA Obs2.wA_ab o' h0 hl0
      hs0 t (m + i) (by omega) (by omega) (hDh (m + i) (by omega)) hεp (mm i) (rr i * mm i)
      (hm0 i hi.le) (mul_nonneg hrk (hm0 i hi.le))
      (hVo_F R hρ0 hρ P o' hf0 hp0 t (m + i) (by omega) (mm i) (hmm i hi.le).2.1)
      (hmm i hi.le).2.2 c'' hc''
    refine ⟨?_, h2⟩
    rw [← Obs2.oTo_wA]
    refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [hrr]; ring
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 2 / L := by
    rw [hx, div_le_div_iff₀ (by positivity) hL0]; nlinarith
  have hss1 : ∀ k, (histS R (k + 1) t)⁻¹ ≤ 15 / 14 * (histS R k t)⁻¹ := by
    intro k
    have e : histS R (k + 1) t = histS R k t * fscale (1 + zetaH R k t) := by
      unfold histS; rw [rawHist_succ_Z, fscale_mul]; ring
    have hz : ‖zetaH R k t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ
    have h1 := fscale_one_add_ge hz
    have hf : 0 < fscale (1 + zetaH R k t) := by linarith
    have hfi : (fscale (1 + zetaH R k t))⁻¹ ≤ 15 / 14 := by
      rw [inv_le_iff_one_le_mul₀ hf]; nlinarith
    rw [e, mul_inv]
    calc (histS R k t)⁻¹ * (fscale (1 + zetaH R k t))⁻¹ ≤ (histS R k t)⁻¹ * (15 / 14) :=
          mul_le_mul_of_nonneg_left hfi (inv_nonneg.2 (hs k).le)
      _ = _ := by ring
  set J := m + j with hJ
  set gterm : (Fin 2 → ℕ) → ℝ := fun c'' =>
    if P.a ∈ nbhd J (blockSet (L := L) (N := N) J c'') then
      2 * Cp * rr (j - 1) ^ 2 * mm (j - 1) / histS R J t ^ 2 else 0 with hgterm
  set dterm : ℕ → (Fin 2 → ℕ) → ℝ := fun i c'' =>
    if P.a ∈ nbhd (m + i + 1) (blockSet (L := L) (N := N) (m + i + 1) c'') then
      1280 * K ^ 2 * x ^ (j - i) * (2 * Cp * rr i ^ 2 * mm i) / histS R (m + i + 1) t ^ 2
    else 0 with hdterm
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  -- the term `G_J(B_+; 0)`
  have hG : ∀ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖wTadX J mass2L (histWF2 R P m o' t J) (blockSet (L := L) (N := N) (J + 1) c') 0‖ ≤
        ∑ c'' ∈ blocks J (blockSet (L := L) (N := N) (J + 1) c'), gterm c'' := by
    intro c' hc'
    have hX : IsPolymer (m + j' + 1) (blockSet (L := L) (N := N) (J + 1) c') :=
      IsPolymer.of_succ (isPolymer_blockSet _ c')
    have hJ' : J = m + j' + 1 := by rw [hJ]; ring
    rw [hJ'] at hX ⊢
    rw [HC.wTadX_succ (by omega) (by omega) hX 0, tau2, expLC_zero, sub_self, mul_zero, zero_add,
      zero_add, sub_self, add_zero, wProdX_eq_prodO]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    rw [expLC_zero]
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk j' (by omega) c'' hc''I
    simp only [hgterm, hJ', Nat.add_sub_cancel]
    split_ifs with ha
    · show ‖mass2 _‖ ≤ _
      refine (norm_mass2_le (hs (m + j' + 1)) (m + j' + 1) _).trans ?_
      have hB : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' := by
        have := hm0 j' (by omega); positivity
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
      rw [ENNReal.toReal_ofReal hB] at this
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · rw [osub_a_zero hmem ha, map_zero, norm_zero]
  -- the increments
  have hD : ∀ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖muProdIncX2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m J
          (blockSet (L := L) (N := N) (J + 1) c')‖ ≤
        ∑ i ∈ range (j' + 1), ∑ c'' ∈ blocks (m + i + 1) (blockSet (L := L) (N := N) (J + 1) c'),
          dterm i c'' := by
    intro c' hc'
    unfold muProdIncX2F
    rw [sum_Ico_eq_sum_range, show J - m = j' + 1 by omega]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    rw [wProdX_eq_prodO, wProdX_eq_prodO, ← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c'' hc'' => ?_)
    have hi' : i < j' + 1 := mem_range.1 hi
    have hc''I := mem_blockIdx_of_mem_blocks hc''
    obtain ⟨hT, hmem⟩ := hPk i hi' c'' hc''I
    simp only [hdterm]
    split_ifs with ha
    · have hB : 0 ≤ 2 * Cp * rr i ^ 2 * mm i := by
        have := hm0 i hi'.le; have := hr0 i (by omega); positivity
      have h := delta_hist_le2L R hρ0 hρ (by omega) hV hVL t P (k := m + i) (j := J) (by omega)
        (by omega) hL hc''I hmem.2.1 ha hB hT
      rw [show J - (m + i) = j' + 1 - i by omega] at h
      exact h
    · rw [osub_a_zero hmem ha]; simp
  -- the sum over the `(J+1)`-blocks
  show ∑ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖wTadX J mass2L (histWF2 R P m o' t J) (blockSet (L := L) (N := N) (J + 1) c') 0 +
        muProdIncX2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m J
          (blockSet (L := L) (N := N) (J + 1) c')‖ ≤ _
  have hS1 : ∑ c' ∈ blockIdx (L := L) (N := N) (J + 1),
      ‖wTadX J mass2L (histWF2 R P m o' t J) (blockSet (L := L) (N := N) (J + 1) c') 0 +
        muProdIncX2F P (histCovO R t) (histVF2 R P m o' t) (histWF2 R P m o' t) m J
          (blockSet (L := L) (N := N) (J + 1) c')‖ ≤
      ∑ c'' ∈ blockIdx (L := L) (N := N) J, gterm c'' +
        ∑ i ∈ range (j' + 1), ∑ c'' ∈ blockIdx (L := L) (N := N) (m + i + 1), dterm i c'' := by
    refine (sum_le_sum fun c' hc' => (norm_add_le _ _).trans
      (add_le_add (hG c' hc') (hD c' hc'))).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_blockIdx_le gterm (by omega : J ≤ J + 1), sum_comm]
    congr 1
    exact sum_congr rfl fun i hi => sum_blockIdx_le (dterm i) (by have := mem_range.1 hi; omega)
  have hS2 : ∑ c'' ∈ blockIdx (L := L) (N := N) J, gterm c'' ≤
      cbnC * (2 * Cp * (rr j' ^ 2 * mm j')) / histS R (m + (j' + 1)) t ^ 2 := by
    simp only [hgterm, Nat.add_sub_cancel]
    have hv : 0 ≤ 2 * Cp * rr j' ^ 2 * mm j' / histS R J t ^ 2 := by
      have := hm0 j' (by omega); have := hs J; positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    rw [hJ]; ring
  have hS3 : ∑ i ∈ range (j' + 1), ∑ c'' ∈ blockIdx (L := L) (N := N) (m + i + 1), dterm i c'' ≤
      ∑ i ∈ range (j' + 1), cbnC * (1280 * K ^ 2 * x ^ (j' + 1 - i) * (2 * Cp * (rr i ^ 2 * mm i)) /
        histS R (m + (i + 1)) t ^ 2) := by
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.1 hi
    have hv : 0 ≤ 1280 * K ^ 2 * x ^ (j' + 1 - i) * (2 * Cp * rr i ^ 2 * mm i) /
        histS R (m + i + 1) t ^ 2 := by
      have := hm0 i hi'.le; have := hs (m + i + 1); positivity
    refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
    rw [← add_assoc]; ring
  have hss : ∀ k, (histS R (m + (k + 1)) t ^ 2)⁻¹ ≤ 6 / 5 * (histS R (m + k) t ^ 2)⁻¹ := by
    intro k
    have h1 := hss1 (m + k)
    have h2 : 0 ≤ (histS R (m + k + 1) t)⁻¹ := inv_nonneg.2 (hs _).le
    rw [← inv_pow, ← inv_pow, ← add_assoc]
    have h3 : (histS R (m + k + 1) t)⁻¹ ^ 2 ≤ (15 / 14 * (histS R (m + k) t)⁻¹) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h4 : 0 ≤ (histS R (m + k) t)⁻¹ ^ 2 := sq_nonneg _
    nlinarith
  have hfin := prodBd_real2 (K := K) hL0 (Nat.cast_nonneg cbnC) hCp (by positivity) hx0 hx2
    (j' + 1) (fun k => rr k ^ 2 * mm k) (fun k => histS R (m + k) t ^ 2)
    (fun k hk => mul_nonneg (sq_nonneg _) (hm0 k hk)) (fun k => pow_pos (hs (m + k)) 2) hss
  rw [if_neg (Nat.succ_ne_zero j'), Nat.add_sub_cancel] at hfin
  refine hS1.trans ((add_le_add hS2 hS3).trans (hfin.trans (le_of_eq ?_)))
  rw [prodCP2]

set_option maxHeartbeats 1000000 in
/-- **`InitBd2F` up to the step `N_h`** (horizon `N_h + 1`; copy of `initBd2F_hist` with
`delta_hist_le2L`). -/
theorem ct_initBd2F_top (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8)
    (P : ObsPts 2 L N) {m : ℕ} (hm1 : 0 < m) (o' : ObsSt .two L N) (hl0 : ObsLocInv P m o')
    (t : Flow2.Hist.Seq (Xs R)) (n : ℕ) (hn : n = Nh + 1) (hnN : n < N) (hV : ∀ i < Nh, ValidAt R i)
    (hVL : ValidAtL R Nh) (hL : prodLb ≤ L) {w₀ M₀ : ℝ} (hw₀ : 0 ≤ w₀) (hM0 : 0 < M₀)
    (hW0 : WbHF R P m o' t m w₀) :
    InitBd2F R P m o' t n (cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) * w₀ /
      (histS R m t ^ 2 * M₀)) M₀ := by
  intro i hi
  set K := locK 2
  have hK := one_le_locK 2
  have hLK : 1000 * K ^ 2 + 10 ≤ (L : ℝ) := hL
  have hL10 : (10 : ℝ) ≤ L := by nlinarith [sq_nonneg K]
  have hL0 : (0 : ℝ) < L := by linarith
  set x : ℝ := 8 / (7 * L) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  have hs := histS_pos' R hρ0 hρ t m
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- the datum's `𝒲`: local and bounded
  have hWb : ∀ b, (o'.W b : OE .two (Lam 2 L N)) ∈ osub P
      (nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b)) := hl0.W
  have hWT : ∀ b ∈ blockIdx (L := L) (N := N) (k + 1),
      Tj 2 (L : ℝ) (k + 1) (histS R (k + 1) t) (histWF2 R P (k + 1) o' t (k + 1) b :
        SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal w₀ := by
    intro b hb
    have h := hW0 b hb
    rw [Obs2.oTo_wA, obsHistFrom_self] at h
    rw [histWF2_a, obsHistFrom_self]
    exact h
  have hWa : ∀ b, (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a =
      (o'.W b : SA .two (Lam 2 L N)).a := fun b => by rw [histWF2_a, obsHistFrom_self]
  -- the tadpole term at `J = m + i`
  set J := k + 1 + i with hJ
  have hcum : cumFrom (histCovO R t) (k + 1) J = cumBetween (histCovO R t) k J := by
    unfold cumFrom cumBetween
    congr 1
  have hterm : ∀ b ∈ blockIdx (L := L) (N := N) (k + 1),
      ‖mass2L (expLC (histCovO R t J + cumFrom (histCovO R t) (k + 1) J)
          (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a) -
        mass2L (expLC (cumFrom (histCovO R t) (k + 1) J)
          (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a)‖ ≤
      (if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b) then
        1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 else 0) := by
    intro b hb
    rw [hcum]
    split_ifs with ha
    · rw [hWa]
      have hF := (hWb b).2.1
      have h := delta_hist_le2L R hρ0 hρ (by omega) hV hVL t P (k := k) (j := J) (by omega) (by omega)
        hL hb hF ha hw₀ (by rw [← hWa]; exact hWT b hb)
      exact h
    · rw [hWa, osub_a_zero (hWb b) ha]; simp
  have hinit : shInit2 (histCovO R t) (histWF2 R P (k + 1) o' t) (k + 1) J ≤
      cbnC * (1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2) := by
    unfold shInit2 wInitX2 wTadX
    have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (J + 1),
        ‖∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (J + 1) c'),
            mass2L (expLC (histCovO R t J + cumFrom (histCovO R t) (k + 1) J)
              (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a) -
          ∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (J + 1) c'),
            mass2L (expLC (cumFrom (histCovO R t) (k + 1) J)
              (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a)‖ ≤
        ∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (J + 1) c'),
          (if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b) then
            1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 else 0) := by
      intro c' _
      rw [← sum_sub_distrib]
      exact (norm_sum_le _ _).trans (sum_le_sum fun b hb =>
        hterm b (mem_blockIdx_of_mem_blocks hb))
    refine (sum_le_sum h1).trans ?_
    rw [sum_blockIdx_le _ (by omega : k + 1 ≤ J + 1)]
    have hv : 0 ≤ 1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 := by positivity
    exact sum_ite_near_le P.a hv
  have hxp : x ^ (J - k) ≤ x * (1 / 2) ^ i := by
    rw [show J - k = i + 1 by omega, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 i) hx0
  have hcb : (0 : ℝ) ≤ cbnC := Nat.cast_nonneg _
  have hinit' : shInit2 (histCovO R t) (histWF2 R P (k + 1) o' t) (k + 1) J ≤
      cbnC * (1280 * K ^ 2 * x) * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i := by
    refine hinit.trans (le_of_eq_of_le rfl ?_)
    have h2 : 1280 * K ^ 2 * x ^ (J - k) * w₀ / histS R (k + 1) t ^ 2 ≤
        1280 * K ^ 2 * (x * (1 / 2) ^ i) * w₀ / histS R (k + 1) t ^ 2 := by
      gcongr
    have := mul_le_mul_of_nonneg_left h2 hcb
    calc _ ≤ _ := this
      _ = _ := by ring
  -- the `𝒲`-mass of the datum
  have hmass : (if i = 0 then shPr2F P (histCovO R t) (histVF2 R P (k + 1) o' t)
      (histWF2 R P (k + 1) o' t) (k + 1) (k + 1) else 0) ≤
      cbnC * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i := by
    split_ifs with hi0
    · subst hi0
      rw [pow_zero, mul_one]
      unfold shPr2F muProdIncX2F
      simp only [Ico_self, sum_empty, add_zero]
      unfold wTadX
      have h1 : ∀ c' ∈ blockIdx (L := L) (N := N) (k + 1 + 1),
          ‖∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (k + 1 + 1) c'),
              mass2L (expLC 0 (histWF2 R P (k + 1) o' t (k + 1) b : SA .two (Lam 2 L N)).a)‖ ≤
            ∑ b ∈ blocks (k + 1) (blockSet (L := L) (N := N) (k + 1 + 1) c'),
              (if P.a ∈ nbhd (k + 1) (blockSet (L := L) (N := N) (k + 1) b) then
                w₀ / histS R (k + 1) t ^ 2 else 0) := by
        intro c' _
        refine (norm_sum_le _ _).trans (sum_le_sum fun b hb => ?_)
        rw [expLC_zero]
        split_ifs with ha
        · show ‖mass2 _‖ ≤ _
          refine (norm_mass2_le hs (k + 1) _).trans ?_
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hWT b (mem_blockIdx_of_mem_blocks hb))
          rw [ENNReal.toReal_ofReal hw₀] at this
          rw [div_eq_mul_inv, ← inv_pow]
          exact mul_le_mul_of_nonneg_right this (by positivity)
        · rw [hWa, osub_a_zero (hWb b) ha]; simp
      refine (sum_le_sum h1).trans ?_
      rw [sum_blockIdx_le _ (by omega : k + 1 ≤ k + 1 + 1)]
      have hv : 0 ≤ w₀ / histS R (k + 1) t ^ 2 := by positivity
      refine (sum_ite_near_le P.a hv).trans (le_of_eq ?_)
      ring
    · positivity
  have e : cbnC * (1280 * locK 2 ^ 2 * (8 / (7 * L)) + 1) * w₀ / (histS R (k + 1) t ^ 2 * M₀) *
      (1 / 2) ^ i * M₀ = cbnC * (1280 * K ^ 2 * x) * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i +
        cbnC * w₀ / histS R (k + 1) t ^ 2 * (1 / 2) ^ i := by
    rw [hx]; field_simp; ring
  rw [e]
  exact add_le_add hinit' hmass

end Hist

end

end PtCorr2
