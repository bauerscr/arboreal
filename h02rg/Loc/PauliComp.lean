import Loc.PauliOps

/-!
# Composition of the one-variable operators (Lemma `lem:pauli`)

Blocks `B ∈ Bk` carry cut-offs `χ_B : X → ℝ` and centres `c_B ∈ X`. For an assignment
`α : Fin m → Bk × Bool` of the first `m` variables to a block and to "frozen" (`true`) or
"remainder" (`false`), `G g m α` applies `Pop` resp. `Rop` of the block `α k` in the variable
`k`, for `k = 0, …, m-1`.

* `sum_G`: `∑_α G g m α (z) = g(z)` if `∑_B χ_B(x) = 1` at the first `m` points of `z`.
* `bd_G`: the product bounds of `bd_Pop`, `bd_Rop` propagate.
* `G_fact`: `G g m α (w) = ∏_{frozen k} χ_{B_k}(x_k) · K(w with the frozen points moved to
  the centres)`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {n : ℕ}
variable {Bk : Type*} [Fintype Bk] [DecidableEq Bk]

/-- The centre map of the block with centre `c`: `(x, σ) ↦ (c, σ)`. -/
def cenAt (c : X) (y : Sf X) : Sf X := (c, y.2)

theorem cenAt_sh (c : X) (b : E → ℕ) (y : Sf X) : cenAt c (sh b y) = cenAt c y := rfl

variable (χ : Bk → X → ℝ) (cB : Bk → X)

/-- The operator of `o = (B, frozen?)` in the variable `i`. -/
def op (o : Bk × Bool) (i : Fin n) (H : (Fin n → Sf X) → ℂ) : (Fin n → Sf X) → ℂ :=
  if o.2 then Pop i (χ o.1) (cenAt (cB o.1)) H else Rop i (χ o.1) (cenAt (cB o.1)) H

/-- The composition over the first `m` variables. -/
def G (g : (Fin n → Sf X) → ℂ) : (m : ℕ) → m ≤ n → (Fin m → Bk × Bool) → (Fin n → Sf X) → ℂ
  | 0, _, _ => g
  | m + 1, h, α => op χ cB (α (Fin.last m)) ⟨m, h⟩ (G g m (Nat.le_of_succ_le h) (Fin.init α))

variable {χ cB}

theorem op_sum {ι : Type*} (s : Finset ι) (o : Bk × Bool) (i : Fin n)
    (H : ι → (Fin n → Sf X) → ℂ) (w : Fin n → Sf X) :
    op χ cB o i (fun w => ∑ a ∈ s, H a w) w = ∑ a ∈ s, op χ cB o i (H a) w := by
  unfold op
  split_ifs
  · simp [Pop, frz, mul_sum]
  · simp only [Rop, frz]
    rw [← sum_sub_distrib, mul_sum]

theorem sum_op (i : Fin n) (H : (Fin n → Sf X) → ℂ) (w : Fin n → Sf X) :
    ∑ o : Bk × Bool, op χ cB o i H w = (∑ B, (χ B (w i).1 : ℂ)) * H w := by
  rw [Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun B _ => ?_
  rw [Fintype.sum_bool]
  simp only [op, if_true, Bool.false_eq_true, if_false, Pop, Rop]
  ring

/-- `∑_α G g m α = g` where the cut-offs sum to one. -/
theorem sum_G (g : (Fin n → Sf X) → ℂ) :
    ∀ (m : ℕ) (hm : m ≤ n) (z : Fin n → Sf X),
      (∀ k : Fin n, k.val < m → ∑ B, χ B (z k).1 = 1) →
      ∑ α : Fin m → Bk × Bool, G χ cB g m hm α z = g z
  | 0, _, z, _ => by simp [G]
  | m + 1, hm, z, hz => by
    rw [← (Fin.snocEquiv fun _ => Bk × Bool).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, G, Fin.init_snoc, Fin.snoc_last]
    rw [show (∑ o : Bk × Bool, ∑ α' : Fin m → Bk × Bool,
        op χ cB o ⟨m, hm⟩ (G χ cB g m (Nat.le_of_succ_le hm) α') z) =
        ∑ o : Bk × Bool, op χ cB o ⟨m, hm⟩
          (fun w => ∑ α' : Fin m → Bk × Bool, G χ cB g m (Nat.le_of_succ_le hm) α' w) z from
      sum_congr rfl fun o _ => (op_sum _ o _ _ z).symm, sum_op]
    rw [sum_G g m _ z fun k hk => hz k (by omega)]
    have h1 := hz ⟨m, hm⟩ (by simp)
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]


/-! ### The product bounds -/

variable (χ) in
/-- The weight of the operator `o` in its variable. -/
def wt (Dst : Bk → Sf X → ℝ) (τ : ℝ) (o : Bk × Bool) : Sf X → (E → ℕ) → ℝ :=
  if o.2 then fun y b => 2 ^ Grassmann.mabs b * |D1 sh b (fun a => χ o.1 a.1) y|
  else wR (χ o.1) (Dst o.1) τ

variable (χ) in
/-- The weights after processing the first `m` variables. -/
def ρm (Dst : Bk → Sf X → ℝ) (τ : ℝ) (m : ℕ) (α : Fin m → Bk × Bool) :
    Fin n → Sf X → (E → ℕ) → ℝ :=
  fun k => if h : k.val < m then wt χ Dst τ (α ⟨k, h⟩) else fun _ b => τ ^ Grassmann.mabs b

theorem wt_nonneg {Dst : Bk → Sf X → ℝ} (hDst : ∀ B y, 0 ≤ Dst B y) {τ : ℝ} (hτ : 0 ≤ τ)
    (o : Bk × Bool) (y : Sf X) (b : E → ℕ) : 0 ≤ wt χ Dst τ o y b := by
  unfold wt
  split_ifs
  · positivity
  · unfold wR
    refine mul_nonneg (by positivity) (sum_nonneg fun γ _ => mul_nonneg (abs_nonneg _) ?_)
    split_ifs
    · exact mul_nonneg (hDst _ _) hτ
    · positivity

theorem ρm_nonneg {Dst : Bk → Sf X → ℝ} (hDst : ∀ B y, 0 ≤ Dst B y) {τ : ℝ} (hτ : 0 ≤ τ)
    (m : ℕ) (α : Fin m → Bk × Bool) (k : Fin n) (y : Sf X) (b : E → ℕ) :
    0 ≤ ρm χ (n := n) Dst τ m α k y b := by
  unfold ρm
  split_ifs
  · exact wt_nonneg hDst hτ _ y b
  · positivity

theorem ρm_succ (Dst : Bk → Sf X → ℝ) (τ : ℝ) (m : ℕ) (hm : m + 1 ≤ n)
    (α : Fin (m + 1) → Bk × Bool) :
    Function.update (ρm (E := E) χ Dst τ m (Fin.init α)) (⟨m, hm⟩ : Fin n)
      (wt χ Dst τ (α (Fin.last m))) = ρm χ Dst τ (m + 1) α := by
  funext k
  by_cases hk : k = ⟨m, hm⟩
  · subst hk
    simp [ρm, Fin.last]
  · rw [Function.update_of_ne hk]
    have hk' : k.val ≠ m := fun h => hk (Fin.ext h)
    unfold ρm
    by_cases hlt : k.val < m
    · rw [dif_pos hlt, dif_pos (by omega)]
      rfl
    · rw [dif_neg hlt, dif_neg (by omega)]

/-- The product bounds propagate through the composition. -/
theorem bd_G {Dst : Bk → Sf X → ℝ} (hDst : ∀ B y, 0 ≤ Dst B y)
    (hpath : ∀ B, PathH (E := E) (cenAt (cB B)) (Dst B)) {p : ℕ} (hp : 1 ≤ p) {M τ : ℝ}
    (hτ : 0 ≤ τ) (hM : 0 ≤ M) {g : (Fin n → Sf X) → ℂ}
    (hg : Bd p M (fun _ _ (b : E → ℕ) => τ ^ Grassmann.mabs b) g) :
    ∀ (m : ℕ) (hm : m ≤ n) (α : Fin m → Bk × Bool),
      Bd p M (ρm (E := E) χ Dst τ m α) (G χ cB g m hm α)
  | 0, _, α => by
    have : ρm (E := E) χ (n := n) Dst τ 0 α = fun _ _ b => τ ^ Grassmann.mabs b := by
      funext k; simp [ρm]
    rw [this]; exact hg
  | m + 1, hm, α => by
    have ih := bd_G hDst hpath hp hτ hM hg m (Nat.le_of_succ_le hm) (Fin.init α)
    have hu : ∀ y (b : E → ℕ), ρm χ Dst τ m (Fin.init α) (⟨m, hm⟩ : Fin n) y b = τ ^ Grassmann.mabs b := by
      intro y b; simp [ρm]
    rw [← ρm_succ]
    simp only [G, op, wt]
    split_ifs with ho
    · exact bd_Pop (cenAt_sh _) (ρm_nonneg hDst hτ _ _) hM hu ih
    · exact bd_Rop (cenAt_sh _) (hDst _) (hpath _) hp hτ (ρm_nonneg hDst hτ _ _) hM hu ih

/-! ### Factorisation in the frozen variables -/

variable (χ cB) in
/-- `∏_{frozen k} χ_{B_k}(x_k)`. -/
def frozenProd (m : ℕ) (hm : m ≤ n) (α : Fin m → Bk × Bool) (w : Fin n → Sf X) : ℝ :=
  ∏ k : Fin m, if (α k).2 then χ (α k).1 (w (Fin.castLE hm k)).1 else 1

variable (cB) in
/-- The frozen points moved to the centres. -/
def updF (m : ℕ) (α : Fin m → Bk × Bool) (w : Fin n → Sf X) : Fin n → Sf X :=
  fun q => if h : q.val < m then
    (if (α ⟨q, h⟩).2 then cenAt (cB (α ⟨q, h⟩).1) (w q) else w q) else w q

theorem frozenProd_update (m : ℕ) (hm : m + 1 ≤ n) (α : Fin m → Bk × Bool)
    (w : Fin n → Sf X) (y : Sf X) :
    frozenProd χ m (Nat.le_of_succ_le hm) α (Function.update w ⟨m, hm⟩ y) =
      frozenProd χ m (Nat.le_of_succ_le hm) α w := by
  unfold frozenProd
  refine prod_congr rfl fun k _ => ?_
  have : Fin.castLE (Nat.le_of_succ_le hm) k ≠ ⟨m, hm⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [Function.update_of_ne this]

theorem frozenProd_succ (m : ℕ) (hm : m + 1 ≤ n) (α : Fin (m + 1) → Bk × Bool)
    (w : Fin n → Sf X) :
    frozenProd χ (m + 1) hm α w =
      frozenProd χ m (Nat.le_of_succ_le hm) (Fin.init α) w *
        (if (α (Fin.last m)).2 then χ (α (Fin.last m)).1 (w ⟨m, hm⟩).1 else 1) := by
  unfold frozenProd
  rw [Fin.prod_univ_castSucc]
  rfl

theorem G_fact (g : (Fin n → Sf X) → ℂ) :
    ∀ (m : ℕ) (hm : m ≤ n) (α : Fin m → Bk × Bool), ∃ K : (Fin n → Sf X) → ℂ,
      ∀ w, G χ cB g m hm α w = (frozenProd χ m hm α w : ℂ) * K (updF cB m α w)
  | 0, _, α => ⟨g, fun w => by
      have : updF cB (n := n) 0 α w = w := by funext q; simp [updF]
      simp [G, frozenProd, this]⟩
  | m + 1, hm, α => by
    obtain ⟨K', hK'⟩ := G_fact g m (Nat.le_of_succ_le hm) (Fin.init α)
    set i : Fin n := ⟨m, hm⟩
    set o := α (Fin.last m)
    have hupd_ne : ∀ (w : Fin n → Sf X) (y : Sf X),
        updF cB m (Fin.init α) (Function.update w i y) =
          Function.update (updF cB m (Fin.init α) w) i y := by
      intro w y
      funext q
      by_cases hq : q = i
      · subst hq; simp [updF, i]
      · rw [Function.update_of_ne hq]
        unfold updF
        split_ifs <;> simp [Function.update_of_ne hq]
    have hupd_i : ∀ w : Fin n → Sf X, updF cB m (Fin.init α) w i = w i := by
      intro w; simp [updF, i]
    by_cases ho : o.2
    · refine ⟨K', fun w => ?_⟩
      have e1 : updF cB m (Fin.init α) (Function.update w i (cenAt (cB o.1) (w i))) =
          updF cB (m + 1) α w := by
        rw [hupd_ne]
        funext q
        by_cases hq : q = i
        · subst hq
          rw [Function.update_self]
          change _ = if h : m < m + 1 then (if o.2 then cenAt (cB o.1) (w i) else w i) else w i
          rw [dif_pos (Nat.lt_succ_self m), if_pos ho]
        · rw [Function.update_of_ne hq]
          have hq' : q.val ≠ m := fun h => hq (Fin.ext h)
          unfold updF
          by_cases hlt : q.val < m
          · rw [dif_pos hlt, dif_pos (by omega)]; rfl
          · rw [dif_neg hlt, dif_neg (by omega)]
      simp only [G, op, ← show o = α (Fin.last m) from rfl, ho, if_true, Pop, frz]
      rw [hK', frozenProd_update, e1, frozenProd_succ, if_pos ho]
      push_cast; ring
    · refine ⟨fun v => (χ o.1 (v i).1 : ℂ) *
        (K' v - K' (Function.update v i (cenAt (cB o.1) (v i)))), fun w => ?_⟩
      have e1 : updF cB (m + 1) α w = updF cB m (Fin.init α) w := by
        funext q
        by_cases hq : q = i
        · subst hq
          change (if h : m < m + 1 then (if o.2 then cenAt (cB o.1) (w i) else w i) else w i) = _
          rw [dif_pos (Nat.lt_succ_self m), if_neg ho, hupd_i]
        · have hq' : q.val ≠ m := fun h => hq (Fin.ext h)
          unfold updF
          by_cases hlt : q.val < m
          · rw [dif_pos hlt, dif_pos (by omega)]; rfl
          · rw [dif_neg hlt, dif_neg (by omega)]
      simp only [G, op, ← show o = α (Fin.last m) from rfl, ho, Bool.false_eq_true, if_false,
        Rop, frz]
      rw [hK', hK', frozenProd_update, hupd_ne, e1, hupd_i, frozenProd_succ, if_neg ho]
      push_cast; ring

end

end Loc
