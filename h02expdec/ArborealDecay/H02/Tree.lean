module

public import ArborealDecay.H02.Spin

/-!
# The expected tree size, the ghost vertex

* `expTree w hw a = 𝔼_w |T_a|`, the expected number of vertices of the tree `T_a` containing `a`
  in the arboreal gas (at `h = 0`) with edge weights `w`.
* `expTree_eq_sum`: `𝔼|T_a| = ∑_x P[a ↔ x]`.
* `expTree_le_card`, `one_le_expTree`: `1 ≤ 𝔼|T_a| ≤ |Λ|` (for non-negative weights).
* `ghostW w h`: the weights of the extended graph `Λ ∪ {g}` (`Option Λ`, ghost `g = none`),
  with `w` on the edges of `Λ` and `h_i` on the edges `ig`.
* `base F`: the restriction of a graph on `Option Λ` to `Λ`.
-/

@[expose] public section

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The expected size `𝔼_w |T_a| = Z_w⁻¹ ∑_{F ∈ 𝓕} ∏_{ij ∈ F} w_ij · |T_a(F)|` of the tree
containing `a` in the arboreal gas with edge weights `w`. -/
def expTree (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i) (a : Λ) : ℝ :=
  (∑ F : SimpleGraph Λ with F.IsAcyclic,
      forestWeight w hw F * ((univ.filter fun x => F.Reachable a x).card : ℝ)) / Zforest w hw

/-- `𝔼|T_a| = ∑_x P[a ↔ x]`. -/
theorem expTree_eq_sum (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i) (a : Λ) :
    expTree w hw a = ∑ x, arborealProb w hw (fun F => F.Reachable a x) := by
  simp only [expTree, arborealProb, ← Finset.sum_div]
  congr 1
  have h1 : ∀ x : Λ, (∑ F : SimpleGraph Λ with F.IsAcyclic ∧ F.Reachable a x,
      forestWeight w hw F) = ∑ F : SimpleGraph Λ with F.IsAcyclic,
        if F.Reachable a x then forestWeight w hw F else 0 := by
    intro x
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h1 : F.IsAcyclic <;> by_cases h2 : F.Reachable a x <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem arborealProb_nonneg {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (P : SimpleGraph Λ → Prop) : 0 ≤ arborealProb w hw P :=
  div_nonneg (Finset.sum_nonneg fun F _ => forestWeight_nonneg hw hw0 F)
    (Zforest_pos hw hw0).le

theorem arborealProb_le_one {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (P : SimpleGraph Λ → Prop) : arborealProb w hw P ≤ 1 := by
  rw [arborealProb, div_le_one (Zforest_pos hw hw0), Zforest]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun F _ _ => forestWeight_nonneg hw hw0 F
  intro F hF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
  exact hF.1

theorem arborealProb_true {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j) :
    arborealProb w hw (fun _ => True) = 1 := by
  rw [arborealProb, div_eq_one_iff_eq (Zforest_pos hw hw0).ne', Zforest]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext F; simp

/-- `𝔼|T_a| ≤ |Λ|`. -/
theorem expTree_le_card {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (a : Λ) : expTree w hw a ≤ Fintype.card Λ := by
  rw [expTree_eq_sum]
  calc ∑ x, arborealProb w hw (fun F => F.Reachable a x) ≤ ∑ _x : Λ, (1 : ℝ) :=
        Finset.sum_le_sum fun x _ => arborealProb_le_one hw hw0 _
    _ = Fintype.card Λ := by simp

/-! ### The ghost vertex -/

/-- The weights of the extended graph on `Λ ∪ {g}` (`g = none`): `w_ij` on `ij`, `h_i` on `ig`. -/
def ghostW (w : Λ → Λ → ℝ) (h : Λ → ℝ) : Option Λ → Option Λ → ℝ
  | some i, some j => w i j
  | some i, none => h i
  | none, some j => h j
  | none, none => 0

@[simp] theorem ghostW_some_some (w : Λ → Λ → ℝ) (h : Λ → ℝ) (i j : Λ) :
    ghostW w h (some i) (some j) = w i j := rfl
@[simp] theorem ghostW_some_none (w : Λ → Λ → ℝ) (h : Λ → ℝ) (i : Λ) :
    ghostW w h (some i) none = h i := rfl
@[simp] theorem ghostW_none_some (w : Λ → Λ → ℝ) (h : Λ → ℝ) (j : Λ) :
    ghostW w h none (some j) = h j := rfl
@[simp] theorem ghostW_none_none (w : Λ → Λ → ℝ) (h : Λ → ℝ) : ghostW w h none none = 0 := rfl

theorem ghostW_symm {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    ∀ i j, ghostW w h i j = ghostW w h j i := by
  rintro (_ | i) (_ | j) <;> simp [hw]

theorem ghostW_nonneg {w : Λ → Λ → ℝ} (hw0 : ∀ i j, 0 ≤ w i j) {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) :
    ∀ i j, 0 ≤ ghostW w h i j := by
  rintro (_ | i) (_ | j) <;> simp [hw0, hh]

/-- The restriction `F|_Λ` of a graph on `Λ ∪ {g}` to `Λ`. -/
def base (F : SimpleGraph (Option Λ)) : SimpleGraph Λ := F.comap some

@[simp] theorem base_adj (F : SimpleGraph (Option Λ)) (i j : Λ) :
    (base F).Adj i j ↔ F.Adj (some i) (some j) := Iff.rfl

end

end H02

end
