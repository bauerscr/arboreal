import Mathlib

/-!
# Discrete derivatives

Let `E` be a finite set of lattice directions (for the torus, `𝓔_d = {±e_1, …, ±e_d}`) and let
`s b y` denote the translate of a point `y` by the multi-index `b ∈ ℕ^E`, i.e. by
`∑_{e ∈ E} b(e) e`.  For a multi-index `a ∈ ℕ^E` the discrete derivative
`∇^a = ∏_{e ∈ E} ∇_e^{a(e)}`, `∇_e f(x) = f(x + e) - f(x)`, is given by the binomial formula
`∇^a f(x) = ∑_{b ≤ a} ∏_e (-1)^{a(e) - b(e)} (a(e) choose b(e)) f(x + b)`.

For functions of several points `z = (z_i)_{i ∈ κ}` and a family `α = (α_i)_{i ∈ κ}` of
multi-indices, `nabla s α f` is `∇^{α_1}_{z_1} ⋯ ∇^{α_n}_{z_n} f`, each `∇_{z_i}` acting on
the `i`-th point only.  We take the binomial formula as the definition; `Grassmann.NablaRec` proves the recursion
`∇^{α + δ_{i,e}} = ∇^α ∇_{i,e}` (`nabla_succ`) and `∇^{δ_{i,e}} f = f(z + e) - f(z)`
(`nabla_single`), which together with `nabla_zero` show that `nabla` is the product of the
elementary differences `∏_e ∇_e^{α(e)}`.
-/

namespace Grassmann

noncomputable section

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `|a| = ∑_e a(e)`, the order of the multi-index `a`. -/
def mabs (a : E → ℕ) : ℕ := ∑ e, a e

/-- The coefficient `∏_e (-1)^{a(e) - b(e)} (a(e) choose b(e))` in the binomial formula. -/
def cf (a b : E → ℕ) : ℝ := ∏ e, (-1 : ℝ) ^ (a e - b e) * (a e).choose (b e)

variable {Y Y' W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']

/-- `∇^{α_i}_{z_i}` for all `i ∈ κ` simultaneously, with respect to the translation `s`. -/
def nabla {κ : Type*} [Fintype κ] [DecidableEq κ] (s : (E → ℕ) → Y → Y) (α : κ → E → ℕ) :
    ((κ → Y) → W) →ₗ[ℝ] ((κ → Y) → W) where
  toFun f z := ∑ β ∈ Fintype.piFinset fun i => Iic (α i),
    (∏ i, cf (α i) (β i)) • f fun i => s (β i) (z i)
  map_add' f g := by ext z; simp [Finset.sum_add_distrib]
  map_smul' c f := by ext z; simp [Finset.smul_sum, smul_comm c]

section
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (s : (E → ℕ) → Y → Y)

theorem nabla_apply (α : κ → E → ℕ) (f : (κ → Y) → W) (z : κ → Y) :
    nabla s α f z = ∑ β ∈ Fintype.piFinset fun i => Iic (α i),
      (∏ i, cf (α i) (β i)) • f fun i => s (β i) (z i) := rfl

theorem cf_zero : cf (0 : E → ℕ) 0 = 1 := by simp [cf]

/-- `∇^0 f = f` (for a translation with `s 0 = id`). -/
theorem nabla_zero (hs : ∀ y, s 0 y = y) (f : (κ → Y) → W) : nabla s (0 : κ → E → ℕ) f = f := by
  ext z
  rw [nabla_apply]
  have : Fintype.piFinset (fun i : κ => Iic ((0 : κ → E → ℕ) i)) = {0} := by
    ext β
    simp only [Fintype.mem_piFinset, mem_Iic, Pi.zero_apply, nonpos_iff_eq_zero, mem_singleton]
    exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩
  rw [this, sum_singleton]
  simp [cf_zero, hs]

theorem nabla_sum {ι : Type*} (t : Finset ι) (α : κ → E → ℕ) (f : ι → (κ → Y) → W)
    (z : κ → Y) : nabla s α (fun z => ∑ j ∈ t, f j z) z = ∑ j ∈ t, nabla s α (f j) z := by
  rw [show (fun z => ∑ j ∈ t, f j z) = ∑ j ∈ t, f j by ext; simp, map_sum]
  simp

/-- `∇` commutes with scalar multiplication (by reals, or e.g. complex numbers when `W` is a
complex vector space). -/
theorem nabla_smul {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass ℝ S W]
    (α : κ → E → ℕ) (c : S) (f : (κ → Y) → W) (z : κ → Y) :
    nabla s α (fun z => c • f z) z = c • nabla s α f z := by
  simp only [nabla_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

/-- Linear maps commute with `∇`. -/
theorem nabla_comp_linear (α : κ → E → ℕ) (T : W →ₗ[ℝ] W') (f : (κ → Y) → W) (z : κ → Y) :
    nabla s α (fun z => T (f z)) z = T (nabla s α f z) := by
  simp [nabla_apply, map_sum, map_smul]

/-- `∇` commutes with the inclusion `ℝ → ℂ`. -/
theorem nabla_ofReal (α : κ → E → ℕ) (f : (κ → Y) → ℝ) (z : κ → Y) :
    nabla s α (fun z => (f z : ℂ)) z = ((nabla s α f z : ℝ) : ℂ) :=
  nabla_comp_linear s α Complex.ofRealCLM.toLinearMap f z

/-- `∇` commutes with equivariant maps `φ` of the points. -/
theorem nabla_comp_equivariant (s' : (E → ℕ) → Y' → Y') (φ : Y → Y')
    (hφ : ∀ b y, φ (s b y) = s' b (φ y)) (α : κ → E → ℕ) (f : (κ → Y') → W) (z : κ → Y) :
    nabla s α (fun z => f (φ ∘ z)) z = nabla s' α f (φ ∘ z) := by
  simp only [nabla_apply]
  refine sum_congr rfl fun β _ => ?_
  congr 2; ext i; simp [hφ]

/-- `∇` commutes with componentwise equivariant maps of the points. -/
theorem nabla_comp_pi (s' : (E → ℕ) → Y' → Y') (φ : κ → Y → Y')
    (hφ : ∀ i b y, φ i (s b y) = s' b (φ i y)) (α : κ → E → ℕ) (f : (κ → Y') → W) (z : κ → Y) :
    nabla s α (fun z => f fun i => φ i (z i)) z = nabla s' α f (fun i => φ i (z i)) := by
  simp only [nabla_apply]
  refine sum_congr rfl fun β _ => ?_
  congr 2; ext i; simp [hφ]

/-- `∇^α f(z)` only depends on the values of `f` at translates of `z`. -/
theorem nabla_congr (α : κ → E → ℕ) {f g : (κ → Y) → W} (z : κ → Y)
    (h : ∀ β : κ → E → ℕ, f (fun i => s (β i) (z i)) = g (fun i => s (β i) (z i))) :
    nabla s α f z = nabla s α g z := by
  simp only [nabla_apply]
  exact sum_congr rfl fun β _ => by rw [h]

end

/-- Reindexing the points by an equivalence `e : κ ≃ κ'`. -/
theorem nabla_reindex {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (s : (E → ℕ) → Y → Y) (e : κ ≃ κ') (α : κ' → E → ℕ) (f : (κ' → Y) → W) (z : κ' → Y) :
    nabla s (α ∘ e) (fun w => f (w ∘ e.symm)) (z ∘ e) = nabla s α f z := by
  simp only [nabla_apply]
  refine Finset.sum_nbij' (fun β => β ∘ e.symm) (fun β => β ∘ e) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [Fintype.mem_piFinset, mem_Iic, Function.comp_apply] at hβ ⊢
    intro i; simpa using hβ (e.symm i)
  · intro β hβ
    simp only [Fintype.mem_piFinset, mem_Iic, Function.comp_apply] at hβ ⊢
    intro i; exact hβ (e i)
  · intro β _; ext; simp
  · intro β _; ext; simp
  · intro β _
    congr 1
    · exact Fintype.prod_equiv e _ _ fun i => by simp
    · congr 1; ext i; simp

/-- Splitting the points into two blocks: `∇^{α} f = ∇^{α_2}_{z_2} ∇^{α_1}_{z_1} f(z_1, z_2)`. -/
theorem nabla_sumElim {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂]
    [DecidableEq κ₂] (s : (E → ℕ) → Y → Y) (α : κ₁ ⊕ κ₂ → E → ℕ) (f : (κ₁ ⊕ κ₂ → Y) → W)
    (z : κ₁ ⊕ κ₂ → Y) :
    nabla s α f z = nabla s (α ∘ Sum.inr)
      (fun z₂ => nabla s (α ∘ Sum.inl) (fun z₁ => f (Sum.elim z₁ z₂)) (z ∘ Sum.inl))
      (z ∘ Sum.inr) := by
  simp only [nabla_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun β => (β ∘ Sum.inl, β ∘ Sum.inr)) (fun p => Sum.elim p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [Fintype.mem_piFinset, mem_Iic, mem_product, Function.comp_apply] at hβ ⊢
    exact ⟨fun i => hβ _, fun i => hβ _⟩
  · intro p hp
    simp only [Fintype.mem_piFinset, mem_Iic, mem_product, Function.comp_apply] at hp ⊢
    intro i; cases i with
    | inl i => exact hp.1 i
    | inr i => exact hp.2 i
  · intro β _; ext i; cases i <;> rfl
  · intro p _; rfl
  · intro β _
    simp only [Fintype.prod_sum_type, Function.comp_apply, smul_smul]
    congr 1
    · ring
    · congr 1; ext i; cases i <;> rfl

/-- `∇` of a function of the form `Φ(v_1(z_1), …, v_n(z_n))` with `Φ` multilinear. -/
theorem nabla_multilinear {κ : Type*} [Fintype κ] [DecidableEq κ] (s : (E → ℕ) → Y → Y)
    (α : κ → E → ℕ) (Φ : MultilinearMap ℝ (fun _ : κ => W') W) (v : κ → Y → W') (z : κ → Y) :
    nabla s α (fun z => Φ fun i => v i (z i)) z =
      Φ fun i => ∑ b ∈ Iic (α i), cf (α i) b • v i (s b (z i)) := by
  rw [MultilinearMap.map_sum_finset, nabla_apply]
  refine sum_congr rfl fun β _ => ?_
  rw [MultilinearMap.map_smul_univ]

/-- The coefficients of a nonzero multi-index sum to zero: `∇^a` kills constants. -/
theorem sum_cf_eq_zero {a : E → ℕ} (ha : a ≠ 0) : ∑ b ∈ Iic a, cf a b = 0 := by
  obtain ⟨e₀, he₀⟩ : ∃ e, a e ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  have hIic : Iic a = Fintype.piFinset fun e => Iic (a e) := rfl
  rw [hIic]
  simp_rw [cf]
  rw [← Finset.prod_univ_sum (fun e => Iic (a e))
    (fun e b => (-1 : ℝ) ^ (a e - b) * (a e).choose b)]
  refine Finset.prod_eq_zero (mem_univ e₀) ?_
  have h2 : ∑ b ∈ Iic (a e₀), (-1 : ℝ) ^ (a e₀ - b) * (a e₀).choose b =
      ∑ b ∈ range (a e₀ + 1), (-1 : ℝ) ^ (a e₀ - b) * (a e₀).choose b := by
    congr 1; ext b; simp
  rw [h2]
  have h3 := Commute.add_pow (Commute.one_left (-1 : ℝ)) (a e₀)
  rw [add_neg_cancel, zero_pow he₀] at h3
  rw [h3]
  refine sum_congr rfl fun b _ => ?_
  rw [one_pow, one_mul]

/-- A constant function has vanishing derivatives of positive order. -/
theorem nabla_const {κ : Type*} [Fintype κ] [DecidableEq κ] (s : (E → ℕ) → Y → Y)
    {α : κ → E → ℕ} (hα : α ≠ 0) (w : W) (z : κ → Y) :
    nabla s α (fun _ => w) z = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, α i ≠ 0 := by
    by_contra h; push Not at h; exact hα (funext h)
  rw [nabla_apply, ← Finset.sum_smul]
  have : Fintype.piFinset (fun i => Iic (α i)) = Fintype.piFinset fun i => Iic (α i) := rfl
  rw [← Finset.prod_univ_sum (fun i => Iic (α i)) (fun i b => cf (α i) b),
    Finset.prod_eq_zero (mem_univ i₀) (sum_cf_eq_zero hi₀), zero_smul]

end

end Grassmann
