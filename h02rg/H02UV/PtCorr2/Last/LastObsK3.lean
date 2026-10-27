import PtCorr2.Last.LastObsK2

/-!
# A weighted norm on the jet algebra and the jet bound of the last step

On `𝔻₂ = (ℂ[δ]/δ²)[σ]/σ²` the weighted `ℓ¹` norm
`‖z‖_{α,β} = |z₀₀| + α|z₀₁| + β|z₁₀| + αβ|z₁₁|` (`z = z₀₀ + δz₀₁ + σ(z₁₀ + δz₁₁)`) is
submultiplicative (`nw_mul_le`). With it:

* `nw_prod_rem`: `‖∏(1 + S_b) - 1 - ∑S_b‖ ≤ e^{∑‖S_b‖} - 1 - ∑‖S_b‖`;
* **`jet_main`**: for `F = e^x(1 + σu)(∏_b(1 - Y_b)(1 + S_b) + k)` with `Y_b = δ(y_b + σβ_b)`,
  `u = -∑_b(S_b)₁₀`, `∑‖S_b‖ ≤ ρ`, `∑α|y_b| ≤ ρ`, `∑αβ|β_b| ≤ B`, `‖k‖ ≤ κ`, `|x| ≤ ρ`,
  `ρ, κ ≤ 1`:
  `‖F - (1 - ∑Y_b + ∑S_b + σu)‖ ≤ 60(1 + B)(ρ + κ)`.
  Since `(1 - ∑Y_b + ∑S_b + σu)₁₀ = 0` and its `σδ` component is `∑(S_b)₁₁ - ∑β_b`, this bounds
  `ε(F_a)` and `c2(F_a) + ∑β_b - ∑(S_b)₁₁`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset TrivSqZeroExt

/-! ### The weighted norm -/

section NW

variable (α β : ℝ)

/-- The weighted norm on `𝔻₂`. -/
def nw (z : D2) : ℝ :=
  ‖z.fst.fst‖ + α * ‖z.fst.snd‖ + β * ‖z.snd.fst‖ + α * β * ‖z.snd.snd‖

variable {α β}

theorem nw_nonneg (hα : 0 ≤ α) (hβ : 0 ≤ β) (z : D2) : 0 ≤ nw α β z := by
  unfold nw; positivity

theorem nw_add_le (hα : 0 ≤ α) (hβ : 0 ≤ β) (z w : D2) : nw α β (z + w) ≤ nw α β z + nw α β w := by
  unfold nw
  simp only [fst_add, snd_add]
  have h1 := norm_add_le z.fst.fst w.fst.fst
  have h2 := mul_le_mul_of_nonneg_left (norm_add_le z.fst.snd w.fst.snd) hα
  have h3 := mul_le_mul_of_nonneg_left (norm_add_le z.snd.fst w.snd.fst) hβ
  have h4 := mul_le_mul_of_nonneg_left (norm_add_le z.snd.snd w.snd.snd) (mul_nonneg hα hβ)
  nlinarith

theorem nw_neg (z : D2) : nw α β (-z) = nw α β z := by
  unfold nw; simp

theorem nw_sub_le (hα : 0 ≤ α) (hβ : 0 ≤ β) (z w : D2) : nw α β (z - w) ≤ nw α β z + nw α β w := by
  rw [sub_eq_add_neg]; exact (nw_add_le hα hβ _ _).trans (by rw [nw_neg])

theorem nw_one : nw α β (1 : D2) = 1 := by
  unfold nw; simp

theorem nw_sum_le (hα : 0 ≤ α) (hβ : 0 ≤ β) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → D2) : nw α β (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nw α β (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [nw]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (nw_add_le hα hβ _ _).trans (add_le_add le_rfl ih)

theorem nw_mul_le (hα : 0 ≤ α) (hβ : 0 ≤ β) (z w : D2) : nw α β (z * w) ≤ nw α β z * nw α β w := by
  have hf : (z * w).fst = z.fst * w.fst := fst_mul _ _
  have hs : (z * w).snd = z.fst * w.snd + z.snd * w.fst := by
    rw [snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  unfold nw
  rw [hf, hs]
  set a := ‖z.fst.fst‖; set b := ‖z.fst.snd‖; set c := ‖z.snd.fst‖; set e := ‖z.snd.snd‖
  set a' := ‖w.fst.fst‖; set b' := ‖w.fst.snd‖; set c' := ‖w.snd.fst‖; set e' := ‖w.snd.snd‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have ha' : 0 ≤ a' := norm_nonneg _
  have hb' : 0 ≤ b' := norm_nonneg _
  have hc' : 0 ≤ c' := norm_nonneg _
  have he' : 0 ≤ e' := norm_nonneg _
  have t1 : ‖(z.fst * w.fst).fst‖ ≤ a * a' := by
    rw [fst_mul, norm_mul]
  have t2 : ‖(z.fst * w.fst).snd‖ ≤ a * b' + b * a' := by
    rw [snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have t3 : ‖(z.fst * w.snd + z.snd * w.fst).fst‖ ≤ a * c' + c * a' := by
    rw [fst_add, fst_mul, fst_mul]
    exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have t4 : ‖(z.fst * w.snd + z.snd * w.fst).snd‖ ≤ a * e' + b * c' + c * b' + e * a' := by
    rw [snd_add, snd_mul, snd_mul, smul_eq_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    linarith
  have hab := mul_nonneg hα hβ
  calc ‖(z.fst * w.fst).fst‖ + α * ‖(z.fst * w.fst).snd‖ +
        β * ‖(z.fst * w.snd + z.snd * w.fst).fst‖ +
        α * β * ‖(z.fst * w.snd + z.snd * w.fst).snd‖
      ≤ a * a' + α * (a * b' + b * a') + β * (a * c' + c * a') +
        α * β * (a * e' + b * c' + c * b' + e * a') := by
        have := mul_le_mul_of_nonneg_left t2 hα
        have := mul_le_mul_of_nonneg_left t3 hβ
        have := mul_le_mul_of_nonneg_left t4 hab
        linarith
    _ ≤ (a + α * b + β * c + α * β * e) * (a' + α * b' + β * c' + α * β * e') := by
        have hx : 0 ≤ α ^ 2 * b * b' + α ^ 2 * β * b * e' + β ^ 2 * c * c' + α * β ^ 2 * c * e' +
            α ^ 2 * β * e * b' + α * β ^ 2 * e * c' + α ^ 2 * β ^ 2 * e * e' := by positivity
        nlinarith [hx]

end NW

/-! ### Products -/

section Prod

variable {α β : ℝ}

theorem exp_rem_step {σ t r : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t) (hr : r ≤ Real.exp σ - 1 - σ) :
    r + t * (r + σ) ≤ Real.exp (σ + t) - 1 - (σ + t) := by
  have h1 : Real.exp σ * (1 + t) ≤ Real.exp (σ + t) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (Real.exp_pos σ).le
  have h2 : r * (1 + t) ≤ (Real.exp σ - 1 - σ) * (1 + t) := mul_le_mul_of_nonneg_right hr (by linarith)
  nlinarith

/-- `‖∏(1 + S_b) - 1 - ∑S_b‖ ≤ e^{∑‖S_b‖} - 1 - ∑‖S_b‖`. -/
theorem nw_prod_rem (hα : 0 ≤ α) (hβ : 0 ≤ β) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (S : ι → D2) :
    nw α β (∏ i ∈ s, (1 + S i) - 1 - ∑ i ∈ s, S i) ≤
      Real.exp (∑ i ∈ s, nw α β (S i)) - 1 - ∑ i ∈ s, nw α β (S i) := by
  induction s using Finset.induction_on with
  | empty => simp [nw]
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, sum_insert hi]
    set P := ∏ k ∈ s, (1 + S k)
    set Sg := ∑ k ∈ s, S k
    have e : (1 + S i) * P - 1 - (S i + Sg) = (P - 1 - Sg) + S i * ((P - 1 - Sg) + Sg) := by ring
    rw [e]
    have h0 : 0 ≤ ∑ k ∈ s, nw α β (S k) := sum_nonneg fun k _ => nw_nonneg hα hβ _
    have hti := nw_nonneg hα hβ (S i)
    refine (nw_add_le hα hβ _ _).trans ?_
    refine (add_le_add le_rfl (nw_mul_le hα hβ _ _)).trans ?_
    have hR := nw_nonneg hα hβ (P - 1 - Sg)
    have h3 : nw α β ((P - 1 - Sg) + Sg) ≤ nw α β (P - 1 - Sg) + ∑ k ∈ s, nw α β (S k) :=
      (nw_add_le hα hβ _ _).trans (add_le_add le_rfl (nw_sum_le hα hβ _ _))
    have h4 := exp_rem_step h0 hti ih
    have h5 : nw α β (P - 1 - Sg) + nw α β (S i) * nw α β ((P - 1 - Sg) + Sg) ≤
        nw α β (P - 1 - Sg) + nw α β (S i) * (nw α β (P - 1 - Sg) + ∑ k ∈ s, nw α β (S k)) := by
      gcongr
    have e2 : nw α β (S i) + ∑ k ∈ s, nw α β (S k) = ∑ k ∈ s, nw α β (S k) + nw α β (S i) := by ring
    rw [e2]
    have h6 : nw α β (P - 1 - Sg) ≤ Real.exp (∑ k ∈ s, nw α β (S k)) - 1 - ∑ k ∈ s, nw α β (S k) := ih
    nlinarith [h4, h5, h6]

/-- `∏(1 - Y_b) = 1 - ∑Y_b` if all products `Y_bY_c` vanish. -/
theorem prod_one_sub_of_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y : ι → D2)
    (h : ∀ i k, Y i * Y k = 0) : ∏ i ∈ s, (1 - Y i) = 1 - ∑ i ∈ s, Y i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, ih, sum_insert hi]
    have : Y i * ∑ k ∈ s, Y k = 0 := by rw [mul_sum]; exact sum_eq_zero fun k _ => h i k
    linear_combination this

theorem mul_eq_zero_of_delta {z w : D2} (hz1 : z.fst.fst = 0) (hz2 : z.snd.fst = 0)
    (hw1 : w.fst.fst = 0) (hw2 : w.snd.fst = 0) : z * w = 0 := by
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_)
  · simp [fst_mul, hz1]
  · simp [snd_mul, hz1, hw1]
  · simp [snd_mul, hz1, hw1, hz2, hw2]
  · simp [snd_mul, hz1, hw1, hz2, hw2]

theorem nw_inr_inl (u : ℂ) : nw α β (inr (inl u) : D2) = β * ‖u‖ := by
  unfold nw; simp

theorem nw_inl_inl (c : ℂ) : nw α β (inl (inl c) : D2) = ‖c‖ := by
  unfold nw; simp

theorem nw_delta {z : D2} (h1 : z.fst.fst = 0) (h2 : z.snd.fst = 0) :
    nw α β z = α * ‖z.fst.snd‖ + α * β * ‖z.snd.snd‖ := by
  unfold nw; rw [h1, h2]; simp

end Prod

/-! ### The jet bound -/

section JetMain

variable {α β : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The jet bound of the last step** (pure algebra in `𝔻₂`). -/
theorem jet_main (hα : 0 ≤ α) (hβ : 0 ≤ β) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (Y S : ι → D2) (k : D2) (x : ℂ) {ρ κ B : ℝ}
    (hY1 : ∀ i, (Y i).fst.fst = 0) (hY2 : ∀ i, (Y i).snd.fst = 0)
    (hS : ∑ i ∈ s, nw α β (S i) ≤ ρ) (hy : ∑ i ∈ s, α * ‖(Y i).fst.snd‖ ≤ ρ)
    (hB : ∑ i ∈ s, α * β * ‖(Y i).snd.snd‖ ≤ B) (hk : nw α β k ≤ κ) (hx : ‖x‖ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    nw α β ((inl (inl (Complex.exp x)) : D2) * (1 + inr (inl (-∑ i ∈ s, (S i).snd.fst))) *
        ((∏ i ∈ s, ((1 - Y i) * (1 + S i))) + k) -
      (1 - ∑ i ∈ s, Y i + ∑ i ∈ s, S i + inr (inl (-∑ i ∈ s, (S i).snd.fst)))) ≤
      60 * (1 + B) * (ρ + κ) := by
  set Sg := ∑ i ∈ s, S i with hSg
  set Ys := ∑ i ∈ s, Y i with hYs
  set u : ℂ := -∑ i ∈ s, (S i).snd.fst with hu
  set U : D2 := inr (inl u) with hU
  set T : D2 := ∏ i ∈ s, (1 + S i) - 1 - Sg with hT
  set X' : D2 := T - Ys * (Sg + T) + k with hX'
  have hYY : ∀ i k, Y i * Y k = 0 := fun i k => mul_eq_zero_of_delta (hY1 i) (hY2 i) (hY1 k) (hY2 k)
  have hprod : ∏ i ∈ s, ((1 - Y i) * (1 + S i)) = (1 - Ys) * (1 + Sg + T) := by
    rw [prod_mul_distrib, prod_one_sub_of_sq s Y hYY, hT]; ring
  have hid : (inl (inl (Complex.exp x)) : D2) * (1 + U) * ((∏ i ∈ s, ((1 - Y i) * (1 + S i))) + k) -
      (1 - Ys + Sg + U) = (inl (inl (Complex.exp x - 1)) : D2) * ((1 + U) * (1 + Sg - Ys + X')) +
        (U * (Sg - Ys + X') + X') := by
    have e1 : (inl (inl (Complex.exp x - 1)) : D2) = inl (inl (Complex.exp x)) - 1 := by
      rw [inl_sub, inl_sub, inl_one, inl_one]
    rw [hprod, hX', e1]; ring
  rw [hid]
  -- the sizes
  have hρ0' : 0 ≤ ∑ i ∈ s, nw α β (S i) := sum_nonneg fun i _ => nw_nonneg hα hβ _
  have hρ0 : 0 ≤ ρ := hρ0'.trans hS
  have hB0 : 0 ≤ B := (sum_nonneg fun i _ => by positivity).trans hB
  have nSg : nw α β Sg ≤ ρ := (nw_sum_le hα hβ _ _).trans hS
  have nYs : nw α β Ys ≤ ρ + B := by
    refine (nw_sum_le hα hβ _ _).trans ?_
    rw [sum_congr rfl fun i _ => nw_delta (hY1 i) (hY2 i), sum_add_distrib]
    linarith
  have nT : nw α β T ≤ ρ := by
    have h1 := nw_prod_rem hα hβ s S
    have h2 : |Real.exp (∑ i ∈ s, nw α β (S i)) - 1 - ∑ i ∈ s, nw α β (S i)| ≤
        (∑ i ∈ s, nw α β (S i)) ^ 2 :=
      Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hρ0']; linarith)
    have h3 : (∑ i ∈ s, nw α β (S i)) ^ 2 ≤ ρ := by nlinarith
    exact h1.trans ((le_abs_self _).trans (h2.trans h3))
  have nU : nw α β U ≤ ρ := by
    rw [hU, nw_inr_inl, hu, norm_neg]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hβ).trans ?_
    rw [mul_sum]
    refine (sum_le_sum fun i _ => ?_).trans hS
    unfold nw
    have := norm_nonneg (S i).fst.fst
    have := mul_nonneg hα (norm_nonneg (S i).fst.snd)
    have := mul_nonneg (mul_nonneg hα hβ) (norm_nonneg (S i).snd.snd)
    linarith
  have nX' : nw α β X' ≤ (3 + 2 * B) * ρ + κ := by
    have h1 : nw α β (Ys * (Sg + T)) ≤ (ρ + B) * (ρ + ρ) :=
      (nw_mul_le hα hβ _ _).trans (mul_le_mul nYs ((nw_add_le hα hβ _ _).trans
        (add_le_add nSg nT)) (nw_nonneg hα hβ _) (by linarith))
    have h2 : nw α β X' ≤ nw α β T + nw α β (Ys * (Sg + T)) + nw α β k := by
      rw [hX']
      exact (nw_add_le hα hβ _ _).trans (add_le_add (nw_sub_le hα hβ _ _) le_rfl)
    nlinarith
  have nX : nw α β (1 + Sg - Ys + X') ≤ 7 + 3 * B := by
    have h := (nw_add_le hα hβ _ _).trans (add_le_add ((nw_sub_le hα hβ _ _).trans
      (add_le_add ((nw_add_le hα hβ _ _).trans (add_le_add (le_of_eq nw_one) nSg)) nYs)) nX')
    nlinarith
  have n1U : nw α β (1 + U) ≤ 2 := by
    have := (nw_add_le hα hβ (1 : D2) U).trans (add_le_add (le_of_eq nw_one) nU)
    linarith
  have hex : ‖Complex.exp x - 1‖ ≤ 2 * ρ :=
    (Complex.norm_exp_sub_one_le (hx.trans hρ1)).trans (by linarith)
  have t1 : nw α β ((inl (inl (Complex.exp x - 1)) : D2) * ((1 + U) * (1 + Sg - Ys + X'))) ≤
      2 * ρ * (2 * (7 + 3 * B)) := by
    refine (nw_mul_le hα hβ _ _).trans ?_
    rw [nw_inl_inl]
    exact mul_le_mul hex ((nw_mul_le hα hβ _ _).trans (mul_le_mul n1U nX (nw_nonneg hα hβ _)
      (by norm_num))) (nw_nonneg hα hβ _) (by linarith)
  have t2 : nw α β (U * (Sg - Ys + X')) ≤ ρ * (ρ + (ρ + B) + ((3 + 2 * B) * ρ + κ)) :=
    (nw_mul_le hα hβ _ _).trans (mul_le_mul nU ((nw_add_le hα hβ _ _).trans
      (add_le_add ((nw_sub_le hα hβ _ _).trans (add_le_add nSg nYs)) nX')) (nw_nonneg hα hβ _) hρ0)
  refine (nw_add_le hα hβ _ _).trans ((add_le_add t1 ((nw_add_le hα hβ _ _).trans
    (add_le_add t2 nX'))).trans ?_)
  have hρρ : ρ * ρ ≤ ρ := by nlinarith
  have hρκ : ρ * κ ≤ ρ := by nlinarith
  have hBρρ : B * ρ * ρ ≤ B * ρ := by nlinarith [mul_nonneg hB0 hρ0]
  nlinarith [mul_nonneg hB0 hκ0, mul_nonneg hB0 hρ0]

end JetMain

end

end PtCorr2
