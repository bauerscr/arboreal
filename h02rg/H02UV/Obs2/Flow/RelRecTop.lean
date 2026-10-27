import Obs2.Flow.RelRec

/-!
# One more error bound of the relative recursion (pure)

`RelRec.close` at horizon `n` gives the bounds at the scales `≤ n` and the errors `E_i`, `i < n`.
**`RelRec.E_top`**: the error `E_n` of the step `n` itself satisfies `E_n ≤ c_δr_n²a_nb_n`, given
at the index `n` only

* the split of `E_n` (activity term, drift, product parts),
* `6/7 ≤ a_n`, the tadpole decay `T_{k,n} ≤ B_τq^{n−k}`,
* the activity bound `Kt_n ≤ c_K k/s_n` (from `Kb_n k`) and the product bound at `n`,
* `c_δr_n² ≤ 1/8`.

No step of `𝒲`/`K` at `n` and no summability up to `n + 1` is needed. `E_le_n` is a copy of
`RelRec.E_le` with the fields at the index `n` passed explicitly.
-/

open Finset

namespace Obs2

namespace RelRec

variable {n : ℕ} {b A D E a s r Kt Pr dg G nn θW θK : ℕ → ℝ} {T : ℕ → ℕ → ℝ}
  {Wb Kb : ℕ → ℝ → Prop} {C₁ cW Bk cK cP cg Bτ q rb cδ : ℝ}
  (H : RelRec n b A D E a s r Kt Pr dg G nn θW θK T Wb Kb C₁ cW Bk cK cP cg Bτ q rb cδ)
include H

/-- `RelRec.E_le` at `j = n`, the fields at `n` passed explicitly. -/
theorem E_le_n (hbi : ∀ i ≤ n, b i ≤ (4 / 3) ^ (n - i) * b n)
    (hAi : ∀ i ≤ n, A i ≤ 2 * b i)
    (hEi : ∀ i < n, E i ≤ cδ * r i ^ 2 * (a i * b i)) (hri : ∀ i ≤ n, r i ≤ r n)
    (hKtj : Kt n ≤ 16 * cK * cW * Bk * r n ^ 2 * b n)
    (hPrj : Pr n ≤ cP * ∑ i ∈ range (n + 1), q ^ (n - i) * (r i ^ 2 * (2 * cW * b i)))
    (hTn : ∀ k < n, 0 ≤ T k n ∧ T k n ≤ Bτ * q ^ (n - k))
    (hEn : E n ≤ Kt n + ∑ k ∈ range n, T k n *
      ∑ i ∈ Ico k n, (dg i * A (i + 1) + G i * (nn i * A i + E i)) + Pr n)
    (han : 6 / 7 ≤ a n) :
    E n ≤ cδ * r n ^ 2 * (a n * b n) := by
  set j := n with hjn
  have hbj := H.hb j le_rfl
  have hrj := H.hr0 j le_rfl
  have hcW0 : 0 ≤ cW := by linarith [H.hcW1]
  have hcg := H.hcg
  have hcδ0 := H.hcδ0
  have hrb0 : 0 ≤ rb := hrj.trans (H.hrb j le_rfl)
  set X := 2 * cg * (1 + cg + cδ * rb) * r j ^ 2 * b j with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ i < j, dg i * A (i + 1) + G i * (nn i * A i + E i) ≤
      X * (4 / 3) ^ (j - i) := by
    intro i hij
    have hin : i < n := hij
    set P := (4 / 3 : ℝ) ^ (j - i) * b j with hP
    have hP0 : 0 ≤ P := by positivity
    have hbi' : b i ≤ P := hbi i hij.le
    have hbi1 : b (i + 1) ≤ P := by
      refine (hbi (i + 1) hij).trans (mul_le_mul_of_nonneg_right ?_ hbj)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hri' := hri i hij.le
    have hr0i := H.hr0 i hin.le
    have hrbi := H.hrb i hin.le
    obtain ⟨hdg0, hdg1⟩ := H.hdg i hin
    obtain ⟨hG0, hG1⟩ := H.hG i hin
    obtain ⟨hnn0, hnn1⟩ := H.hnn i hin
    obtain ⟨-, ha2⟩ := H.ha i hin
    have hA1 : A (i + 1) ≤ 2 * P := (hAi (i + 1) hij).trans (by linarith)
    have hAi' : A i ≤ 2 * P := (hAi i hij.le).trans (by linarith)
    have hE1 : E i ≤ cδ * (rb * r j) * (2 * P) := by
      refine (hEi i hij).trans ?_
      have h1 : r i ^ 2 ≤ rb * r j := by
        rw [sq]; exact mul_le_mul hrbi hri' hr0i hrb0
      have h2 : a i * b i ≤ 2 * P := mul_le_mul ha2 hbi' (H.hb i hin.le) (by norm_num)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hcδ0) h2
        (mul_nonneg (by linarith [(H.ha i hin).1]) (H.hb i hin.le)) (by positivity)
    have hr2 : r i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ hr0i hri' 2
    have t1 : dg i * A (i + 1) ≤ cg * r j ^ 2 * (2 * P) :=
      mul_le_mul (hdg1.trans (mul_le_mul_of_nonneg_left hr2 hcg)) hA1 (H.hA0 _ (by omega))
        (by positivity)
    have t2 : nn i * A i ≤ cg * r j * (2 * P) :=
      mul_le_mul (hnn1.trans (mul_le_mul_of_nonneg_left hri' hcg)) hAi' (H.hA0 _ hin.le)
        (by positivity)
    have t3 : G i * (nn i * A i + E i) ≤
        cg * r j * (cg * r j * (2 * P) + cδ * (rb * r j) * (2 * P)) :=
      mul_le_mul (hG1.trans (mul_le_mul_of_nonneg_left hri' hcg)) (add_le_add t2 hE1)
        (add_nonneg (mul_nonneg hnn0 (H.hA0 _ hin.le)) (H.hE0 i hin)) (by positivity)
    have e : cg * r j ^ 2 * (2 * P) + cg * r j * (cg * r j * (2 * P) + cδ * (rb * r j) * (2 * P)) =
        X * (4 / 3) ^ (j - i) := by rw [hX, hP]; ring
    linarith
  have hdrift : ∑ k ∈ range j, T k j *
      ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) ≤ 2 * Bτ * X := by
    have h1 : ∀ k ∈ range j, T k j *
        ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) ≤
        4 * Bτ * X * ((4 / 3 * q) ^ (j - k)) := by
      intro k hk
      have hkj := mem_range.1 hk
      obtain ⟨hT0, hT1⟩ := hTn k hkj
      have hs : ∑ i ∈ Ico k j, (dg i * A (i + 1) + G i * (nn i * A i + E i)) ≤
          X * (4 * (4 / 3 : ℝ) ^ (j - k)) := by
        refine (sum_le_sum fun i hi => hterm i (mem_Ico.1 hi).2).trans ?_
        rw [← mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hX0
        have := geom_Ico_le j hkj.le
        linarith
      calc _ ≤ T k j * (X * (4 * (4 / 3 : ℝ) ^ (j - k))) := mul_le_mul_of_nonneg_left hs hT0
        _ ≤ Bτ * q ^ (j - k) * (X * (4 * (4 / 3 : ℝ) ^ (j - k))) :=
            mul_le_mul_of_nonneg_right hT1 (by positivity)
        _ = 4 * Bτ * X * ((4 / 3 * q) ^ (j - k)) := by rw [mul_pow]; ring
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    have hg := geom_tail_le (y := 4 / 3 * q) (by have := H.hq0; positivity)
      (by have := H.hq; linarith) j
    have : 0 ≤ 4 * Bτ * X := by have := H.hBτ; positivity
    nlinarith
  have hprod : Pr j ≤ 3 * cP * cW * r j ^ 2 * b j := by
    refine hPrj.trans ?_
    have hc : 0 ≤ cW := hcW0
    have h1 : ∀ i ∈ range (j + 1), q ^ (j - i) * (r i ^ 2 * (2 * cW * b i)) ≤
        2 * cW * r j ^ 2 * b j * (4 / 3 * q) ^ (j - i) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have hr2 : r i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ (H.hr0 i (by omega)) (hri i hij) 2
      have hbb := hbi i hij
      have h2 : r i ^ 2 * (2 * cW * b i) ≤
          r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * b j)) :=
        mul_le_mul hr2 (mul_le_mul_of_nonneg_left hbb (by positivity))
          (by have := H.hb i (by omega); positivity) (sq_nonneg _)
      calc _ ≤ q ^ (j - i) * (r j ^ 2 * (2 * cW * ((4 / 3) ^ (j - i) * b j))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg H.hq0 _)
        _ = _ := by rw [mul_pow]; ring
    have h2 := sum_le_sum h1
    rw [← mul_sum] at h2
    have hg := geom_tail_le' (y := 4 / 3 * q) (by have := H.hq0; positivity)
      (by have := H.hq; linarith) j
    have h3 : 0 ≤ 2 * cW * r j ^ 2 * b j :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg _)) hbj
    have h4 := mul_le_mul_of_nonneg_left hg h3
    have h5 := mul_le_mul_of_nonneg_left (h2.trans h4) H.hcP
    nlinarith
  have hsum : E j ≤ (16 * cK * cW * Bk + 3 * cP * cW +
      4 * Bτ * cg * (1 + cg) + 4 * Bτ * cg * cδ * rb) * (r j ^ 2 * b j) := by
    have e : 2 * Bτ * X = (4 * Bτ * cg * (1 + cg) + 4 * Bτ * cg * cδ * rb) * (r j ^ 2 * b j) := by
      rw [hX]; ring
    nlinarith
  have hrb2 : 0 ≤ r j ^ 2 * b j := by positivity
  have h6 := mul_le_mul_of_nonneg_right H.hcδ hrb2
  have h7 : 6 / 7 * cδ * (r j ^ 2 * b j) ≤ cδ * r j ^ 2 * (a j * b j) := by
    have := mul_le_mul_of_nonneg_left han (mul_nonneg hcδ0 hrb2)
    nlinarith
  linarith

/-- **The error of the step `n`** from `close` at horizon `n` and the inputs at `n`:
`E_n ≤ c_δr_n²a_nb_n`. -/
theorem E_top (hTn : ∀ k < n, 0 ≤ T k n ∧ T k n ≤ Bτ * q ^ (n - k))
    (hEn : E n ≤ Kt n + ∑ k ∈ range n, T k n *
      ∑ i ∈ Ico k n, (dg i * A (i + 1) + G i * (nn i * A i + E i)) + Pr n)
    (han : 6 / 7 ≤ a n)
    (hKtn : ∀ k, 0 ≤ k → Kb n k → Kt n ≤ cK * k / s n)
    (hPrn : ∀ m : ℕ → ℝ, (∀ i ≤ n, 0 ≤ m i ∧ s i * A i ≤ m i ∧ Wb i (r i * m i)) →
      Pr n ≤ cP * ∑ i ∈ range (n + 1), q ^ (n - i) * (r i ^ 2 * m i / s i)) :
    E n ≤ cδ * r n ^ 2 * (a n * b n) := by
  have hcW : 1 ≤ cW := H.hcW1
  have hcW0 : 0 ≤ cW := by linarith
  have hBk := H.hBk
  obtain ⟨hB, hEs⟩ := H.close n le_rfl
  have hstep : ∀ l < n, b l ≤ 4 / 3 * b (l + 1) := by
    intro l hln
    have h1 := H.hbstep l hln
    have h2 := hEs l hln
    have h3 := H.rsq_le hln
    obtain ⟨ha1, -⟩ := H.ha l hln
    have hbl := H.hb l (by omega)
    have h4 : a l * b l * (1 - cδ * r l ^ 2) ≤ b (l + 1) := by
      linarith [show a l * b l * (1 - cδ * r l ^ 2) = a l * b l - cδ * r l ^ 2 * (a l * b l) by ring]
    have hx : 3 / 4 ≤ a l * (1 - cδ * r l ^ 2) := by
      have := mul_le_mul ha1 (show 7 / 8 ≤ 1 - cδ * r l ^ 2 by linarith) (by norm_num)
        (by linarith)
      linarith
    have h5 : 3 / 4 * b l ≤ a l * b l * (1 - cδ * r l ^ 2) := by
      have := mul_le_mul_of_nonneg_right hx hbl
      linarith [show a l * b l * (1 - cδ * r l ^ 2) = a l * (1 - cδ * r l ^ 2) * b l by ring]
    linarith
  have hbi := le_pow_mul_of_step (by norm_num : (0 : ℝ) ≤ 4 / 3) hstep
  have hri : ∀ i ≤ n, r i ≤ r n := by
    have := le_pow_mul_of_step (x := r) (by norm_num : (0 : ℝ) ≤ 1)
      (j := n) (fun l hl => by rw [one_mul]; exact H.hrm l (by omega))
    intro i hi; simpa using this i hi
  have hAi : ∀ i ≤ n, A i ≤ 2 * b i := by
    intro i hi
    obtain ⟨hbp, hD, -, -⟩ := hB i hi
    have h1 := H.hA i (by omega)
    have h2 := H.sum_le (j := i) (by omega)
    nlinarith
  obtain ⟨hbj, -, -, hKj⟩ := hB n le_rfl
  have hsj := H.hs n le_rfl
  have hrj := H.hr0 n le_rfl
  have hKtj : Kt n ≤ 16 * cK * cW * Bk * r n ^ 2 * b n := by
    refine (hKtn _ (by positivity) hKj).trans (le_of_eq ?_)
    field_simp
  have hPrj : Pr n ≤ cP * ∑ i ∈ range (n + 1), q ^ (n - i) *
      (r i ^ 2 * (2 * cW * b i)) := by
    have h := hPrn (fun i => cW * (2 * s i * b i)) fun i hi => by
      obtain ⟨hbp, -, hW, -⟩ := hB i hi
      have hsi := H.hs i (by omega)
      refine ⟨by positivity, ?_, H.hWm i _ _ hW (le_of_eq (by ring))⟩
      have h1 : s i * A i ≤ s i * (2 * b i) := mul_le_mul_of_nonneg_left (hAi i hi) hsi.le
      have h2 : 2 * s i * b i ≤ cW * (2 * s i * b i) :=
        le_mul_of_one_le_left (by positivity) hcW
      linarith [show s i * (2 * b i) = 2 * s i * b i by ring]
    refine h.trans (le_of_eq ?_)
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hsi := H.hs i (by have := mem_range.1 hi; omega)
    field_simp
  exact H.E_le_n hbi hAi hEs hri hKtj hPrj hTn hEn han

end RelRec

end Obs2
