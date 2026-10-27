module

public import ArborealDecay.TLaw.Sabot
public import ArborealDecay.TLaw.Finite

/-!
# Consequences of `thm:sabot`: the BCHS (4.6) form and `cor:sabot` (`a = 3/2`)

* `sabot_bchs`: BCHS (4.6) as printed, with `½ γ² q² ∑_{i,k}` over all ordered pairs.
* `sabot_two_thirds` (`cor:sabot`(i), `s = 2/3`) and `sabot_one_third` (`cor:sabot`(ii),
  `s = 1/3`), and `sabot_one_third_note` (the note's `eq:BCHS-specialized`).

The hypotheses (H1), (H2) are kept as hypotheses (they are BCHS (4.4), proved elsewhere for
`a = 3/2`: supplement `prop:A`, `cor:Zmon`, `thm:B`).
-/

open Finset Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeSum_le_half_sum (w : V → V → ℝ) {g : V → V → ℝ} (hg : ∀ i k, 0 ≤ g i k) :
    edgeSum w g ≤ (1 / 2) * ∑ i, ∑ k, g i k := by
  unfold edgeSum
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_)
    (by norm_num)
  split_ifs
  · rfl
  · exact hg i k

theorem edgeSum_nonneg (w : V → V → ℝ) {g : V → V → ℝ} (hg : ∀ i k, 0 ≤ g i k) :
    0 ≤ edgeSum w g := by
  unfold edgeSum
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_)
  split_ifs
  · exact hg i k
  · rfl

/-- **BCHS Lemma 4.1, (4.6) as printed** (sum over all ordered pairs `i, k`):
`E e^{2as t_j} ≤ e^{-2asγ} e^{½ γ² q² ∑_{i,k} (w_{ik} + 2a)(v_i - v_k)²}`. -/
theorem sabot_bchs {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {ρ j : V} (hj : j ≠ ρ) {a s γ : ℝ} (ha : 0 ≤ a) (hs0 : 0 < s) (hs1 : s < 1) (hγ : 0 < γ)
    (v : V → ℝ) (hvρ : v ρ = 0) (hvj : v j = 1)
    (hgrad : ∀ i k, 0 < w i k → γ * |v i - v k| ≤ (1 - s) ^ 2 / 2)
    (H1 : ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ a < ⊤ ∧ Z w' ρ a ≤ Z w ρ a)
    (H2 : expect w ρ a (fun τ => exp (2 * a * ext ρ τ j)) = 1) :
    expect w ρ a (fun τ => exp (2 * a * s * ext ρ τ j)) ≤
      exp (-2 * a * s * γ) * exp (1 / 2 * γ ^ 2 * (1 - s)⁻¹ ^ 2 *
        ∑ i, ∑ k, (w i k + 2 * a) * (v i - v k) ^ 2) := by
  refine (sabot hW hconn hj ha hs0 hs1 hγ v hvρ hvj hgrad H1 H2).2.trans ?_
  rw [← exp_add]
  refine exp_le_exp.2 ?_
  have hg : ∀ i k, 0 ≤ (w i k + 2 * a) * (v i - v k) ^ 2 := fun i k =>
    mul_nonneg (by linarith [hW.nonneg i k]) (sq_nonneg _)
  have h1 := edgeSum_le_half_sum w hg
  have h0 := edgeSum_nonneg w hg
  have hq : 0 < (1 - s)⁻¹ := inv_pos.2 (by linarith)
  have hqq : (1 - s)⁻¹ * ((1 - s)⁻¹ - 1) ≤ (1 - s)⁻¹ ^ 2 := by nlinarith
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  have := mul_le_mul hqq h1 h0 (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left this hγ2]

/-- **`cor:sabot`(i)** (`a = 3/2`, `s = 2/3`, `q = 3`): if `γ |∇_e v| ≤ 1/18` on support edges,
`E e^{2 t_y} ≤ exp(-2γ + 6 γ² ∑_{e ∈ E(w)} (w_e + 3)(∇_e v)²)`. -/
theorem sabot_two_thirds {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {ρ y : V} (hy : y ≠ ρ) {γ : ℝ} (hγ : 0 < γ) (v : V → ℝ) (hvρ : v ρ = 0) (hvy : v y = 1)
    (hgrad : ∀ i k, 0 < w i k → γ * |v i - v k| ≤ 1 / 18)
    (H1 : ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ (3 / 2) < ⊤ ∧ Z w' ρ (3 / 2) ≤ Z w ρ (3 / 2))
    (H2 : expect w ρ (3 / 2) (fun τ => exp (3 * ext ρ τ y)) = 1) :
    Integrable (fun τ => exp (2 * ext ρ τ y) * density w ρ (3 / 2) τ) ∧
      expect w ρ (3 / 2) (fun τ => exp (2 * ext ρ τ y)) ≤
        exp (-2 * γ + 6 * γ ^ 2 * edgeSum w (fun i k => (w i k + 3) * (v i - v k) ^ 2)) := by
  have H2' : expect w ρ (3 / 2) (fun τ => exp (2 * (3 / 2) * ext ρ τ y)) = 1 := by
    rw [← H2]; norm_num
  have h := sabot hW hconn hy (a := 3 / 2) (s := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
    hγ v hvρ hvy (fun i k hik => by norm_num; linarith [hgrad i k hik]) H1 H2'
  have e1 : (fun τ : {i // i ≠ ρ} → ℝ => exp (2 * (3 / 2 : ℝ) * (2 / 3) * ext ρ τ y)) =
      fun τ => exp (2 * ext ρ τ y) := by funext τ; norm_num
  have e2 : (fun i k => (w i k + 2 * (3 / 2 : ℝ)) * (v i - v k) ^ 2) =
      fun i k => (w i k + 3) * (v i - v k) ^ 2 := by funext i k; norm_num
  have e3 : (fun τ : {i // i ≠ ρ} → ℝ =>
      exp (2 * (3 / 2 : ℝ) * (2 / 3) * ext ρ τ y) * density w ρ (3 / 2) τ) =
      fun τ => exp (2 * ext ρ τ y) * density w ρ (3 / 2) τ := by funext τ; norm_num
  rw [e1, e2, e3] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  congr 1; norm_num

/-- **`cor:sabot`(ii)** (`a = 3/2`, `s = 1/3`, `q = 3/2`): if `γ |∇_e v| ≤ 2/9` on support edges,
`E e^{t_y} ≤ exp(-γ + ¾ γ² ∑_{e ∈ E(w)} (w_e + 3)(∇_e v)²)`. -/
theorem sabot_one_third {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {ρ y : V} (hy : y ≠ ρ) {γ : ℝ} (hγ : 0 < γ) (v : V → ℝ) (hvρ : v ρ = 0) (hvy : v y = 1)
    (hgrad : ∀ i k, 0 < w i k → γ * |v i - v k| ≤ 2 / 9)
    (H1 : ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ (3 / 2) < ⊤ ∧ Z w' ρ (3 / 2) ≤ Z w ρ (3 / 2))
    (H2 : expect w ρ (3 / 2) (fun τ => exp (3 * ext ρ τ y)) = 1) :
    Integrable (fun τ => exp (ext ρ τ y) * density w ρ (3 / 2) τ) ∧
      expect w ρ (3 / 2) (fun τ => exp (ext ρ τ y)) ≤
        exp (-γ + 3 / 4 * γ ^ 2 * edgeSum w (fun i k => (w i k + 3) * (v i - v k) ^ 2)) := by
  have H2' : expect w ρ (3 / 2) (fun τ => exp (2 * (3 / 2) * ext ρ τ y)) = 1 := by
    rw [← H2]; norm_num
  have h := sabot hW hconn hy (a := 3 / 2) (s := 1 / 3) (by norm_num) (by norm_num) (by norm_num)
    hγ v hvρ hvy (fun i k hik => by norm_num; linarith [hgrad i k hik]) H1 H2'
  have e1 : (fun τ : {i // i ≠ ρ} → ℝ => exp (2 * (3 / 2 : ℝ) * (1 / 3) * ext ρ τ y)) =
      fun τ => exp (ext ρ τ y) := by funext τ; norm_num
  have e2 : (fun i k => (w i k + 2 * (3 / 2 : ℝ)) * (v i - v k) ^ 2) =
      fun i k => (w i k + 3) * (v i - v k) ^ 2 := by funext i k; norm_num
  have e3 : (fun τ : {i // i ≠ ρ} → ℝ =>
      exp (2 * (3 / 2 : ℝ) * (1 / 3) * ext ρ τ y) * density w ρ (3 / 2) τ) =
      fun τ => exp (ext ρ τ y) * density w ρ (3 / 2) τ := by funext τ; norm_num
  rw [e1, e2, e3] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  congr 1; norm_num

/-- The note's `eq:BCHS-specialized`: under the hypotheses of `sabot_one_third`,
`E e^{t_y} ≤ exp(-γ + (9/8) γ² ∑_{i,k} (w_{ik} + 3)(v_i - v_k)²)` (all ordered pairs). -/
theorem sabot_one_third_note {w : V → V → ℝ} (hW : IsWGraph w)
    (hconn : (supportGraph w).Connected)
    {ρ y : V} (hy : y ≠ ρ) {γ : ℝ} (hγ : 0 < γ) (v : V → ℝ) (hvρ : v ρ = 0) (hvy : v y = 1)
    (hgrad : ∀ i k, 0 < w i k → γ * |v i - v k| ≤ 2 / 9)
    (H1 : ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ (3 / 2) < ⊤ ∧ Z w' ρ (3 / 2) ≤ Z w ρ (3 / 2))
    (H2 : expect w ρ (3 / 2) (fun τ => exp (3 * ext ρ τ y)) = 1) :
    expect w ρ (3 / 2) (fun τ => exp (ext ρ τ y)) ≤
      exp (-γ + 9 / 8 * γ ^ 2 * ∑ i, ∑ k, (w i k + 3) * (v i - v k) ^ 2) := by
  refine (sabot_one_third hW hconn hy hγ v hvρ hvy hgrad H1 H2).2.trans (exp_le_exp.2 ?_)
  have hg : ∀ i k, 0 ≤ (w i k + 3) * (v i - v k) ^ 2 := fun i k =>
    mul_nonneg (by linarith [hW.nonneg i k]) (sq_nonneg _)
  have h1 := edgeSum_le_half_sum w hg
  have h0 := edgeSum_nonneg w hg
  have hs : 0 ≤ ∑ i, ∑ k, (w i k + 3) * (v i - v k) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hg i k
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  nlinarith [mul_le_mul_of_nonneg_left h1 hγ2, mul_nonneg hγ2 hs]

/-- `thm:sabot` with the finiteness half of (H1) discharged by `Z_lt_top`: only the
monotonicity `Z_{w',a} ≤ Z_{w,a}` (same support, `w' ≤ w`) and (H2) are assumed. -/
theorem sabot_of_mono {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected)
    {ρ j : V} (hj : j ≠ ρ) {a s γ : ℝ} (ha : 0 ≤ a) (hs0 : 0 < s) (hs1 : s < 1) (hγ : 0 < γ)
    (v : V → ℝ) (hvρ : v ρ = 0) (hvj : v j = 1)
    (hgrad : ∀ i k, 0 < w i k → γ * |v i - v k| ≤ (1 - s) ^ 2 / 2)
    (Hmono : ∀ w' : V → V → ℝ, IsWGraph w' → (∀ i k, 0 < w' i k ↔ 0 < w i k) →
      (∀ i k, w' i k ≤ w i k) → Z w' ρ a ≤ Z w ρ a)
    (H2 : expect w ρ a (fun τ => exp (2 * a * ext ρ τ j)) = 1) :
    Integrable (fun τ => exp (2 * a * s * ext ρ τ j) * density w ρ a τ) ∧
      expect w ρ a (fun τ => exp (2 * a * s * ext ρ τ j)) ≤
        exp (-2 * a * s * γ + (1 - s)⁻¹ * ((1 - s)⁻¹ - 1) * γ ^ 2 *
          edgeSum w (fun i k => (w i k + 2 * a) * (v i - v k) ^ 2)) := by
  refine sabot hW hconn hj ha hs0 hs1 hγ v hvρ hvj hgrad (fun w' hW' hsupp hle => ?_) H2
  have hG : supportGraph w' = supportGraph w := by
    ext i k; simp only [supportGraph, SimpleGraph.fromRel_adj, hsupp]
  exact ⟨Z_lt_top hW' (hG ▸ hconn) ρ ha, Hmono w' hW' hsupp hle⟩

end ArborealDecay.TLaw
