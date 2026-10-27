import Loc.EstLeibniz

/-!
# One-variable operators for the Pauli gain (`h02uv-outline.tex`, Lemma `lem:pauli`)

For functions `H` of `n` points of `Λ_f = X × {±1}` and a variable `i`, a cut-off `χ` and a
centre map `cen` (which keeps the spin), the two operators are

* `Pop i H w = χ(x_i) H(w with w_i ↦ cen w_i)` (the frozen part),
* `Rop i H w = χ(x_i) (H(w) - H(w with w_i ↦ cen w_i))` (the remainder).

`Bd p M ρ H` is a product bound on all derivatives of order `≤ p` in each variable:
`‖∇^β H(w)‖ ≤ M ∏_k ρ_k(w_k, β_k)`. If the weight of variable `i` is uniform,
`ρ_i(y, b) = τ^{|b|}`, then `Pop i H` and `Rop i H` again satisfy product bounds, with only the
weight of variable `i` changed (`bd_Pop`, `bd_Rop`). For `Rop` this uses a path estimate
from `cen y` to `y`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {n : ℕ}

theorem sh_add' (b b' : E → ℕ) (y : Sf X) : sh (b + b') y = sh b (sh b' y) := by
  simp [sh, add_vadd]

theorem sh_zero' (y : Sf X) : sh (0 : E → ℕ) y = y := by simp [sh]

/-! ### Composition of derivatives -/

theorem nabla_add_aux {W : Type*} [AddCommGroup W] [Module ℝ W] (k : ℕ) :
    ∀ (β : Fin n → E → ℕ), ord β = k → ∀ (α : Fin n → E → ℕ) (f : (Fin n → Sf X) → W),
      nab (α + β) f = nab α (nab β f) := by
  induction k with
  | zero =>
    intro β hβ α f
    rw [ord_eq_zero hβ, add_zero, nabla_zero _ sh_zero']
  | succ k ih =>
    intro β hβ α f
    have hne : β ≠ 0 := by rintro rfl; simp [ord_zero] at hβ
    obtain ⟨β', i, e, rfl⟩ := exists_eq_add_single hne
    have hord : ord β' = k := by rw [ord_add, ord_single] at hβ; omega
    rw [← add_assoc, nabla_succ _ sh_add', ih β' hord, nabla_succ _ sh_add']

/-- `∇^{α + β} = ∇^α ∇^β`. -/
theorem nab_add {W : Type*} [AddCommGroup W] [Module ℝ W] (α β : Fin n → E → ℕ)
    (f : (Fin n → Sf X) → W) : nab (α + β) f = nab α (nab β f) :=
  nabla_add_aux _ β rfl α f

/-! ### Functions of one point -/

/-- The part of `β` at the variable `i`. -/
def atI (i : Fin n) (β : Fin n → E → ℕ) : Fin n → E → ℕ := Pi.single i (β i)

/-- The part of `β` away from the variable `i`. -/
def offI (i : Fin n) (β : Fin n → E → ℕ) : Fin n → E → ℕ := Function.update β i 0

theorem atI_add_offI (i : Fin n) (β : Fin n → E → ℕ) : atI i β + offI i β = β := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [atI, offI]
  · simp [atI, offI, hk]

theorem offI_self (i : Fin n) (β : Fin n → E → ℕ) : offI i β i = 0 := by simp [offI]

theorem ord_atI (i : Fin n) (β : Fin n → E → ℕ) : ord (atI i β) = mabs (β i) := by
  rw [ord, Finset.sum_eq_single i]
  · simp [atI]
  · intro k _ hk; simp [atI, hk, Grassmann.mabs]
  · simp

/-- A function of the point `i` alone passes through derivatives not acting on `i`. -/
theorem nab_mul_of_off {W : Type*} [AddCommGroup W] [Module ℂ W] [Module ℝ W]
    [IsScalarTower ℝ ℂ W] (i : Fin n) (c : Sf X → ℂ) (u : (Fin n → Sf X) → W)
    (β : Fin n → E → ℕ) (hβ : β i = 0) (w : Fin n → Sf X) :
    nab β (fun w => c (w i) • u w) w = c (w i) • nab β u w := by
  simp only [nabla_apply, Finset.smul_sum]
  refine sum_congr rfl fun b hb => ?_
  have hbi : b i = 0 := by
    have := (Fintype.mem_piFinset.1 hb) i
    rw [hβ, mem_Iic, nonpos_iff_eq_zero] at this
    exact this
  rw [hbi, sh_zero', smul_comm]

/-- The derivative of a function of the point `i` alone. -/
theorem nab_point (i : Fin n) (f : Sf X → ℝ) (γ : Fin n → E → ℕ) (hγ : ∀ k, k ≠ i → γ k = 0)
    (w : Fin n → Sf X) : nab γ (fun w => f (w i)) w = D1 sh (γ i) f (w i) := by
  have h := nabla_prod (sh (X := X)) γ (fun k => if k = i then f else fun _ => 1) w
  have e1 : (fun w : Fin n → Sf X => ∏ k, (if k = i then f else fun _ => (1 : ℝ)) (w k)) =
      fun w => f (w i) := by
    funext w'
    rw [Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [e1] at h
  rw [h, Finset.prod_eq_single i]
  · simp
  · intro k _ hk
    rw [if_neg hk, hγ k hk, D1_zero _ sh_zero']
  · simp


/-- `∇^α f(z)` only depends on the values of `f` at the translates in the range of `α`. -/
theorem nabla_congr_range {W : Type*} [AddCommGroup W] [Module ℝ W] (α : Fin n → E → ℕ)
    {f g : (Fin n → Sf X) → W} (z : Fin n → Sf X)
    (h : ∀ b ∈ Fintype.piFinset fun k => Iic (α k), f (fun k => sh (b k) (z k)) =
      g (fun k => sh (b k) (z k))) :
    nab α f z = nab α g z := by
  simp only [nabla_apply]
  exact sum_congr rfl fun b hb => by rw [h b hb]

theorem eq_zero_of_mem_piFinset_atI {i : Fin n} {β : Fin n → E → ℕ} {b : Fin n → E → ℕ}
    (hb : b ∈ Fintype.piFinset fun k => Iic (atI i β k)) {k : Fin n} (hk : k ≠ i) : b k = 0 := by
  have := (Fintype.mem_piFinset.1 hb) k
  simp only [atI, Pi.single_apply, hk, if_false, mem_Iic, nonpos_iff_eq_zero] at this
  exact this

theorem eq_zero_of_mem_piFinset_zero_at {i : Fin n} {β : Fin n → E → ℕ} (hβ : β i = 0)
    {b : Fin n → E → ℕ} (hb : b ∈ Fintype.piFinset fun k => Iic (β k)) : b i = 0 := by
  have := (Fintype.mem_piFinset.1 hb) i
  rw [hβ, mem_Iic, nonpos_iff_eq_zero] at this
  exact this

/-! ### Freezing a variable -/

section Freeze

variable (i : Fin n) (cen : Sf X → Sf X)

/-- `H(w with w_i ↦ cen w_i)`. -/
def frz (H : (Fin n → Sf X) → ℂ) : (Fin n → Sf X) → ℂ :=
  fun w => H (Function.update w i (cen (w i)))

variable {i cen}

theorem shifted_atI {β : Fin n → E → ℕ} {b : Fin n → E → ℕ}
    (hb : b ∈ Fintype.piFinset fun k => Iic (atI i β k)) (w : Fin n → Sf X) :
    (fun k => sh (b k) (w k)) = Function.update w i (sh (b i) (w i)) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Function.update_of_ne hk, eq_zero_of_mem_piFinset_atI hb hk, sh_zero']

/-- A frozen variable has no derivatives. -/
theorem nab_frz_of_ne (hcen : ∀ (b : E → ℕ) y, cen (sh b y) = cen y) (H : (Fin n → Sf X) → ℂ)
    {β : Fin n → E → ℕ} (hβ : β i ≠ 0) (w : Fin n → Sf X) : nab β (frz i cen H) w = 0 := by
  have hsplit : β = offI i β + atI i β := by rw [add_comm, atI_add_offI]
  rw [hsplit, nab_add]
  have h0 : nab (atI i β) (frz i cen H) = 0 := by
    funext w'
    have hne : atI i β ≠ 0 := by
      intro h; apply hβ; have := congrFun h i; simpa [atI] using this
    rw [nabla_congr_range (atI i β) (g := fun _ => frz i cen H w') w' fun b hb => ?_,
      nabla_const _ hne]
    · rfl
    · rw [shifted_atI hb]
      simp [frz, hcen]
  rw [h0]
  simp [nabla_apply]

theorem nab_frz_of_eq (hcen : ∀ (b : E → ℕ) y, cen (sh b y) = cen y) (H : (Fin n → Sf X) → ℂ)
    {β : Fin n → E → ℕ} (hβ : β i = 0) (w : Fin n → Sf X) :
    nab β (frz i cen H) w = nab β H (Function.update w i (cen (w i))) := by
  simp only [nabla_apply, frz]
  refine sum_congr rfl fun b hb => ?_
  have hbi := eq_zero_of_mem_piFinset_zero_at hβ hb
  congr 2
  funext k
  by_cases hk : k = i
  · subst hk; simp [hbi, hcen, sh_zero']
  · simp [Function.update_of_ne hk]

end Freeze

/-! ### Product bounds -/

/-- The product bound `‖∇^β H(w)‖ ≤ M ∏_k ρ_k(w_k, β_k)` for `|β_k| ≤ p`. -/
def Bd (p : ℕ) (M : ℝ) (ρ : Fin n → Sf X → (E → ℕ) → ℝ) (H : (Fin n → Sf X) → ℂ) : Prop :=
  ∀ (w : Fin n → Sf X) (β : Fin n → E → ℕ), (∀ k, mabs (β k) ≤ p) →
    ‖nab β H w‖ ≤ M * ∏ k, ρ k (w k) (β k)

/-- The frozen part `Pop i H = χ(x_i) H(w_i ↦ cen w_i)`. -/
def Pop (i : Fin n) (χ : X → ℝ) (cen : Sf X → Sf X) (H : (Fin n → Sf X) → ℂ) :
    (Fin n → Sf X) → ℂ :=
  fun w => (χ (w i).1 : ℂ) * frz i cen H w

/-- The remainder `Rop i H = χ(x_i) (H - H(w_i ↦ cen w_i))`. -/
def Rop (i : Fin n) (χ : X → ℝ) (cen : Sf X → Sf X) (H : (Fin n → Sf X) → ℂ) :
    (Fin n → Sf X) → ℂ :=
  fun w => (χ (w i).1 : ℂ) * (H w - frz i cen H w)

theorem prod_update_eq {ρ : Fin n → Sf X → (E → ℕ) → ℝ} (i : Fin n)
    (ρ' : Sf X → (E → ℕ) → ℝ) (w : Fin n → Sf X) (β : Fin n → E → ℕ) :
    ∏ k, Function.update ρ i ρ' k (w k) (β k) =
      ρ' (w i) (β i) * ∏ k ∈ univ.erase i, ρ k (w k) (β k) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  congr 1
  · simp
  · refine prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hk)]

theorem prod_eq_at {ρ : Fin n → Sf X → (E → ℕ) → ℝ} (i : Fin n) (w : Fin n → Sf X)
    (β : Fin n → E → ℕ) :
    ∏ k, ρ k (w k) (β k) = ρ i (w i) (β i) * ∏ k ∈ univ.erase i, ρ k (w k) (β k) :=
  (Finset.mul_prod_erase univ _ (mem_univ i)).symm

/-- The Leibniz step in the variable `i`: the derivative of `χ(x_i) V(w)`. -/
theorem nab_cut_mul (i : Fin n) (χ : X → ℝ) (V : (Fin n → Sf X) → ℂ) (β : Fin n → E → ℕ)
    (w : Fin n → Sf X) {Mx : ℝ}
    (hM : ∀ γ : Fin n → E → ℕ, γ ≤ atI i β →
      |D1 sh (γ i) (fun a => χ a.1) (w i)| *
        ‖nab (atI i β - γ) (nab (offI i β) V) (fun k => sh (γ k) (w k))‖ ≤ Mx) :
    ‖nab β (fun w => (χ (w i).1 : ℂ) * V w) w‖ ≤ 2 ^ mabs (β i) * Mx := by
  conv_lhs => rw [← atI_add_offI i β, nab_add]
  have e1 : nab (offI i β) (fun w => (χ (w i).1 : ℂ) * V w) =
      fun w => (χ (w i).1 : ℂ) * nab (offI i β) V w := by
    funext w'
    exact nab_mul_of_off i (fun a => (χ a.1 : ℂ)) V (offI i β) (offI_self i β) w'
  rw [e1]
  have := abs_nabla_mul_le (sh (X := X)) sh_zero' sh_add' (atI i β)
    (fun w => (χ (w i).1 : ℂ)) (nab (offI i β) V) w (M := Mx) (fun γ hγ => by
      have hγk : ∀ k, k ≠ i → γ k = 0 := fun k hk => by
        have := hγ k
        funext e
        have h' := this e
        simp only [atI, Pi.single_apply, hk, if_false, Pi.zero_apply, nonpos_iff_eq_zero] at h'
        exact h'
      have hc : nab γ (fun w => (χ (w i).1 : ℂ)) w = (D1 sh (γ i) (fun a => χ a.1) (w i) : ℂ) := by
        rw [show (fun w : Fin n → Sf X => (χ (w i).1 : ℂ)) = fun w => ((fun a => χ a.1) (w i) : ℂ)
          from rfl, nabla_ofReal]
        congr 1
        convert nab_point i (fun a => χ a.1) γ hγk w using 1
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
      exact hM γ hγ)
  rwa [ord_atI] at this


theorem mabs_sub_le' (a b : E → ℕ) : mabs (a - b) ≤ mabs a :=
  Finset.sum_le_sum fun e _ => Nat.sub_le _ _

theorem atI_sub_add_offI_apply (i : Fin n) (β γ : Fin n → E → ℕ) :
    (atI i β - γ + offI i β) i = β i - γ i := by
  simp [atI, offI]

theorem le_atI_eq_zero {i : Fin n} {β γ : Fin n → E → ℕ} (hγ : γ ≤ atI i β) {k : Fin n}
    (hk : k ≠ i) : γ k = 0 := by
  funext e
  have h' := hγ k e
  simp only [atI, Pi.single_apply, hk, if_false, Pi.zero_apply, nonpos_iff_eq_zero] at h'
  exact h'

theorem le_atI_at {i : Fin n} {β γ : Fin n → E → ℕ} (hγ : γ ≤ atI i β) : γ i ≤ β i := by
  intro e; have := hγ i e; simpa [atI] using this

theorem shift_of_le_atI {i : Fin n} {β γ : Fin n → E → ℕ} (hγ : γ ≤ atI i β)
    (w : Fin n → Sf X) {k : Fin n} (hk : k ≠ i) : sh (γ k) (w k) = w k := by
  rw [le_atI_eq_zero hγ hk, sh_zero']

theorem atI_sub_add_offI_of_ne {i : Fin n} {β γ : Fin n → E → ℕ} {k : Fin n} (hk : k ≠ i)
    (hγ : γ ≤ atI i β) : (atI i β - γ + offI i β) k = β k := by
  simp [atI, offI, hk, le_atI_eq_zero hγ hk]

theorem prod_erase_shift {ρ : Fin n → Sf X → (E → ℕ) → ℝ} {i : Fin n} {β γ : Fin n → E → ℕ}
    (hγ : γ ≤ atI i β) (w : Fin n → Sf X) (u : Fin n → Sf X)
    (hu : ∀ k, k ≠ i → u k = sh (γ k) (w k)) (β' : Fin n → E → ℕ)
    (hβ' : ∀ k, k ≠ i → β' k = β k) :
    ∏ k ∈ univ.erase i, ρ k (u k) (β' k) = ∏ k ∈ univ.erase i, ρ k (w k) (β k) := by
  refine prod_congr rfl fun k hk => ?_
  have hk' := ne_of_mem_erase hk
  rw [hu k hk', shift_of_le_atI hγ w hk', hβ' k hk']

variable {i : Fin n} {χ : X → ℝ} {cen : Sf X → Sf X}

/-- The frozen part: only the weight of the variable `i` changes, to `2^{|b|} |∇^b χ(y)|`. -/
theorem bd_Pop (hcen : ∀ (b : E → ℕ) y, cen (sh b y) = cen y) {p : ℕ} {M τ : ℝ}
    {ρ : Fin n → Sf X → (E → ℕ) → ℝ} (hρ : ∀ k y b, 0 ≤ ρ k y b) (hM : 0 ≤ M)
    (hu : ∀ y b, ρ i y b = τ ^ mabs b) {H : (Fin n → Sf X) → ℂ} (hH : Bd p M ρ H) :
    Bd p M (Function.update ρ i fun y b => 2 ^ mabs b * |D1 sh b (fun a => χ a.1) y|)
      (Pop i χ cen H) := by
  intro w β hβ
  set Pr := ∏ k ∈ univ.erase i, ρ k (w k) (β k)
  have hPr : 0 ≤ Pr := prod_nonneg fun k _ => hρ k _ _
  have hMx : 0 ≤ |D1 sh (β i) (fun a => χ a.1) (w i)| * (M * Pr) := by positivity
  refine (nab_cut_mul i χ (frz i cen H) β w (Mx := |D1 sh (β i) (fun a => χ a.1) (w i)| * (M * Pr))
    fun γ hγ => ?_).trans (le_of_eq ?_)
  · rw [← nab_add]
    by_cases hγe : γ i = β i
    · have hz : atI i β - γ = 0 := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [atI, hγe]
        · simp [atI, hk, le_atI_eq_zero hγ hk]
      rw [hz, zero_add, nab_frz_of_eq hcen H (offI_self i β), hγe]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (hH _ _ fun k => ?_).trans (le_of_eq ?_)
      · by_cases hk : k = i
        · subst hk; simp [offI, Grassmann.mabs]
        · simpa [offI, hk] using hβ k
      · rw [prod_eq_at i, offI_self, hu, show mabs (0 : E → ℕ) = 0 by simp [Grassmann.mabs],
          pow_zero, one_mul,
          prod_erase_shift hγ w _ (fun k hk => by rw [Function.update_of_ne hk]) _
            (fun k hk => by simp [offI, hk])]
    · have hne : (atI i β - γ + offI i β) i ≠ 0 := by
        rw [atI_sub_add_offI_apply]
        intro h0
        apply hγe
        funext e
        have h1 : β i e - γ i e = 0 := by simpa using congrFun h0 e
        have h2 : γ i e ≤ β i e := le_atI_at hγ e
        omega
      rw [nab_frz_of_ne hcen H hne, norm_zero, mul_zero]
      exact hMx
  · rw [prod_update_eq]
    ring

/-- The path hypothesis: `‖φ(y) - φ(cen y)‖ ≤ Dst(y) K` if all unit differences of `φ` are
`≤ K`. -/
def PathH (cen : Sf X → Sf X) (Dst : Sf X → ℝ) : Prop :=
  ∀ (φ : Sf X → ℂ) (K : ℝ), (∀ y (e : E), ‖φ (sh (Pi.single e 1) y) - φ y‖ ≤ K) →
    ∀ y, ‖φ y - φ (cen y)‖ ≤ Dst y * K

/-- The weight of the remainder in the variable `i`. -/
def wR (χ : X → ℝ) (Dst : Sf X → ℝ) (τ : ℝ) (y : Sf X) (b : E → ℕ) : ℝ :=
  2 ^ mabs b * ∑ γ ∈ Iic b, |D1 sh γ (fun a => χ a.1) y| *
    (if γ = b then Dst (sh b y) * τ else τ ^ mabs (b - γ))

/-- The remainder: only the weight of the variable `i` changes, to `wR`. -/
theorem bd_Rop (hcen : ∀ (b : E → ℕ) y, cen (sh b y) = cen y) {Dst : Sf X → ℝ}
    (hDst : ∀ y, 0 ≤ Dst y) (hpath : PathH (E := E) cen Dst) {p : ℕ} (hp : 1 ≤ p) {M τ : ℝ}
    (hτ : 0 ≤ τ) {ρ : Fin n → Sf X → (E → ℕ) → ℝ} (hρ : ∀ k y b, 0 ≤ ρ k y b) (hM : 0 ≤ M)
    (hu : ∀ y b, ρ i y b = τ ^ mabs b) {H : (Fin n → Sf X) → ℂ} (hH : Bd p M ρ H) :
    Bd p M (Function.update ρ i (wR χ Dst τ)) (Rop i χ cen H) := by
  intro w β hβ
  set Pr := ∏ k ∈ univ.erase i, ρ k (w k) (β k)
  have hPr : 0 ≤ Pr := prod_nonneg fun k _ => hρ k _ _
  set term : (E → ℕ) → ℝ := fun γ' => |D1 sh γ' (fun a => χ a.1) (w i)| *
    (if γ' = β i then Dst (sh (β i) (w i)) * τ else τ ^ mabs (β i - γ')) * (M * Pr)
  have hterm : ∀ γ', 0 ≤ term γ' := fun γ' => by
    simp only [term]
    have : 0 ≤ (if γ' = β i then Dst (sh (β i) (w i)) * τ else τ ^ mabs (β i - γ')) := by
      split_ifs
      · exact mul_nonneg (hDst _) hτ
      · positivity
    positivity
  refine (nab_cut_mul i χ (fun w => H w - frz i cen H w) β w (Mx := ∑ γ' ∈ Iic (β i), term γ')
    fun γ hγ => ?_).trans (le_of_eq ?_)
  · refine le_trans ?_ (single_le_sum (fun γ' _ => hterm γ') (mem_Iic.2 (le_atI_at hγ)))
    simp only [term]
    rw [← nab_add, show (fun w => H w - frz i cen H w) = H - frz i cen H from rfl, map_sub,
      Pi.sub_apply, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    by_cases hγe : γ i = β i
    · -- the difference along a path
      have hz : atI i β - γ = 0 := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [atI, hγe]
        · simp [atI, hk, le_atI_eq_zero hγ hk]
      rw [hz, zero_add, nab_frz_of_eq hcen H (offI_self i β), if_pos hγe]
      set w' : Fin n → Sf X := fun k => sh (γ k) (w k)
      set φ : Sf X → ℂ := fun y => nab (offI i β) H (Function.update w' i y)
      have hφK : ∀ y (e : E), ‖φ (sh (Pi.single e 1) y) - φ y‖ ≤ M * τ * Pr := by
        intro y e
        have h1 : φ (sh (Pi.single e 1) y) - φ y =
            nab (offI i β + Pi.single i (Pi.single e 1)) H (Function.update w' i y) := by
          rw [← ediff_nabla _ sh_add']
          simp only [φ, ediff, Function.update_idem, Function.update_self]
        rw [h1]
        refine (hH _ _ fun k => ?_).trans (le_of_eq ?_)
        · by_cases hk : k = i
          · subst hk; simp [offI, Grassmann.mabs]; exact hp
          · simpa [offI, hk] using hβ k
        · rw [prod_eq_at i, hu]
          have hi : (offI i β + Pi.single i (Pi.single e 1) : Fin n → E → ℕ) i = Pi.single e 1 := by
            simp [offI]
          rw [hi, show mabs (Pi.single e 1 : E → ℕ) = 1 by
            simp [Grassmann.mabs], pow_one,
            prod_erase_shift hγ w _ (fun k hk => by simp [w', Function.update_of_ne hk]) _
              (fun k hk => by simp [offI, hk])]
          ring
      have hp' := hpath φ _ hφK (w' i)
      have e1 : φ (w' i) = nab (offI i β) H w' := by simp [φ]
      have e2 : φ (cen (w' i)) = nab (offI i β) H (Function.update w' i (cen (w' i))) := rfl
      rw [e1, e2] at hp'
      have hw'i : w' i = sh (β i) (w i) := by simp [w', hγe]
      rw [show cen (sh (γ i) (w i)) = cen (w' i) from rfl, ← hw'i]
      calc _ ≤ Dst (w' i) * (M * τ * Pr) := hp'
        _ = _ := by ring
    · have hne : (atI i β - γ + offI i β) i ≠ 0 := by
        rw [atI_sub_add_offI_apply]
        intro h0
        apply hγe
        funext e
        have h1 : β i e - γ i e = 0 := by simpa using congrFun h0 e
        have h2 : γ i e ≤ β i e := le_atI_at hγ e
        omega
      rw [nab_frz_of_ne hcen H hne, sub_zero, if_neg (Ne.symm (Ne.symm hγe))]
      refine (hH _ _ fun k => ?_).trans (le_of_eq ?_)
      · by_cases hk : k = i
        · subst hk
          rw [atI_sub_add_offI_apply]
          exact (mabs_sub_le' _ _).trans (hβ k)
        · rw [atI_sub_add_offI_of_ne hk hγ]; exact hβ k
      · rw [prod_eq_at i, hu, atI_sub_add_offI_apply,
          prod_erase_shift hγ w _ (fun k _ => rfl) _ (fun k hk => atI_sub_add_offI_of_ne hk hγ)]
        ring
  · simp only [term, prod_update_eq, wR, Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun γ' _ => by ring

end

end Loc
