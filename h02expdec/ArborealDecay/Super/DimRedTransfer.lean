module

public import ArborealDecay.Super.H24
public import ArborealDecay.H02.Integral

/-!
# Transfer from the `ℍ^{2|4}` algebra to the `ℍ^{0|2}` algebra

The algebra homomorphism `tr : SG Λ (Λ ⊕ Λ) → H02.Grassmann Λ` kills the integrated generators
`ξ²_i = ξ_i, η²_i = η_i` and sends the parameter generators `ξ¹_i, η¹_i` to the generators
`ξ_i, η_i` of `H02.Grassmann Λ`.  It preserves bodies and parity, intertwines the fermionic
derivatives in the parameters with those of `H02` (`tr_dgen_inr`), and satisfies
`tr ∘ π_0 = tr` (`tr_pi0`).

We also define the parameter Berezin integral `B1 l = ∏_{i ∈ l} ∂_{η¹_i} ∂_{ξ¹_i}` and the plain
`H02` Berezin integral `bplain l = ∏_{i ∈ l} ∂_{η_i} ∂_{ξ_i}`, prove
`tr ∘ B1 l = bplain l ∘ tr` (`tr_B1`), and relate `bplain` to the hyperbolic integral of `H02`
(`H02.berezin l F = bplain l ((∏_{i ∈ l} z_i⁻¹) F)`, `berezin_eq_bplain`).
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann Finset

set_option linter.unusedSectionVars false

namespace H24

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ### The transfer homomorphism -/

/-- The transfer map: kill `ξ², η²`, send `ξ¹_i ↦ ξ_i`, `η¹_i ↦ η_i`. -/
def tr : A Λ →ₐ[ℝ] H02.Grassmann Λ :=
  ExteriorAlgebra.map (LinearMap.funLeft ℝ ℝ (Sum.inr : Λ ⊕ Λ → (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ)))

theorem tr_ι (v : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ) → ℝ) :
    tr (ExteriorAlgebra.ι ℝ v) = ExteriorAlgebra.ι ℝ (fun o => v (.inr o)) := by
  simp [tr, ExteriorAlgebra.map_apply_ι]; rfl

theorem tr_gen_inr (o : Λ ⊕ Λ) : tr (gen (.inr o) : A Λ) = gen o := by
  rw [gen, tr_ι, gen]
  congr 1; ext o'
  simp [Pi.single_apply]

theorem tr_gen_inl (o : Λ ⊕ Λ) : tr (gen (.inl o) : A Λ) = 0 := by
  rw [gen, tr_ι]
  have : (fun o' : Λ ⊕ Λ => (Pi.single (Sum.inl o) 1 : (Λ ⊕ Λ) ⊕ (Λ ⊕ Λ) → ℝ) (.inr o')) = 0 := by
    ext o'; simp
  rw [this, map_zero]

@[simp] theorem tr_ξ (i : Λ) : tr (ξ i : A Λ) = 0 := tr_gen_inl _
@[simp] theorem tr_η (i : Λ) : tr (η i : A Λ) = 0 := tr_gen_inl _
@[simp] theorem tr_ξ1 (i : Λ) : tr (ξ1 i : A Λ) = H02.ξ i := tr_gen_inr _
@[simp] theorem tr_η1 (i : Λ) : tr (η1 i : A Λ) = H02.η i := tr_gen_inr _

theorem body_tr (x : A Λ) : body (tr x) = body x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change body (tr (ExteriorAlgebra.ι ℝ v)) = body (ExteriorAlgebra.ι ℝ v)
    rw [tr_ι, body_ι, body_ι]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem inv'_tr (x : A Λ) : inv' (tr x) = tr (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change inv' (tr (ExteriorAlgebra.ι ℝ v)) = tr (inv' (ExteriorAlgebra.ι ℝ v))
    rw [tr_ι, inv'_ι, inv'_ι, map_neg, tr_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem isEven_tr {x : A Λ} (hx : IsEven x) : IsEven (tr x) := by
  unfold IsEven at *; rw [inv'_tr, hx]

/-- `tr` intertwines the parameter derivatives with the `H02` derivatives. -/
theorem tr_dgen_inr (o : Λ ⊕ Λ) (x : A Λ) : tr (dgen (.inr o) x) = dgen o (tr x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change tr (dgen (.inr o) (ExteriorAlgebra.ι ℝ v)) = dgen o (tr (ExteriorAlgebra.ι ℝ v))
    rw [tr_ι]
    simp [dgen, ExteriorAlgebra.ι, contractLeft_ι]
  | mul a b ha hb => rw [dgen_mul, map_add, map_mul, map_mul, ha, hb, map_mul, dgen_mul, inv'_tr]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem tr_killA_inl {S : Set ((Λ ⊕ Λ) ⊕ (Λ ⊕ Λ))} (hS : S ⊆ Set.range Sum.inl) (x : A Λ) :
    tr (killA S x) = tr x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    change tr (killA S (ExteriorAlgebra.ι ℝ v)) = tr (ExteriorAlgebra.ι ℝ v)
    simp only [killA, ExteriorAlgebra.map_apply_ι]
    rw [tr_ι, tr_ι]
    congr 1; ext o
    rw [killV_apply, Set.indicator_of_mem]
    intro h
    obtain ⟨o', ho'⟩ := hS h
    exact Sum.inl_ne_inr ho'
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem tr_pi0 (x : A Λ) : tr (pi0 x) = tr x := tr_killA_inl subset_rfl x

theorem tr_scomp (g : ℝ → ℝ) {a : A Λ} (ha : IsEven a) : tr (scomp g a) = scomp g (tr a) :=
  map_scomp tr body_tr g (isNilpotent_soul ha)

/-! ### Berezin integrals in the parameters -/

/-- `∂_{η¹_i} ∂_{ξ¹_i}`. -/
def bpar (i : Λ) : A Λ →ₗ[ℝ] A Λ := dgen (.inr (.inr i)) ∘ₗ dgen (.inr (.inl i))

/-- `∏_{i ∈ l} ∂_{η¹_i} ∂_{ξ¹_i}` (head of `l` applied first, as in `H02.berezin`). -/
def B1 (l : List Λ) : A Λ →ₗ[ℝ] A Λ := l.foldl (fun L i => bpar i ∘ₗ L) LinearMap.id

/-- `∂_{η_i} ∂_{ξ_i}` in `H02.Grassmann Λ`. -/
def bstep (i : Λ) : H02.Grassmann Λ →ₗ[ℝ] H02.Grassmann Λ := H02.dη i ∘ₗ H02.dξ i

/-- The plain Berezin integral `∏_{i ∈ l} ∂_{η_i} ∂_{ξ_i}` of `H02` (no `z⁻¹` factors). -/
def bplain (l : List Λ) : H02.Grassmann Λ →ₗ[ℝ] H02.Grassmann Λ :=
  l.foldl (fun L i => bstep i ∘ₗ L) LinearMap.id

theorem tr_bpar (i : Λ) (x : A Λ) : tr (bpar i x) = bstep i (tr x) := by
  simp only [bpar, bstep, LinearMap.coe_comp, Function.comp_apply, tr_dgen_inr]
  rfl

theorem tr_foldl (l : List Λ) (L : A Λ →ₗ[ℝ] A Λ) (L' : H02.Grassmann Λ →ₗ[ℝ] H02.Grassmann Λ)
    (h : ∀ x, tr (L x) = L' (tr x)) (x : A Λ) :
    tr (l.foldl (fun L i => bpar i ∘ₗ L) L x) = l.foldl (fun L i => bstep i ∘ₗ L) L' (tr x) := by
  induction l generalizing L L' with
  | nil => exact h x
  | cons i l ih =>
    simp only [List.foldl_cons]
    exact ih _ _ fun y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, tr_bpar, h]

theorem tr_B1 (l : List Λ) (x : A Λ) : tr (B1 l x) = bplain l (tr x) :=
  tr_foldl l _ _ (fun _ => rfl) x

theorem bplain_foldl (l : List Λ) (L : H02.Grassmann Λ →ₗ[ℝ] H02.Grassmann Λ) :
    l.foldl (fun L i => bstep i ∘ₗ L) L = bplain l ∘ₗ L := by
  induction l generalizing L with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, bplain]
    rw [ih, ih (bstep a ∘ₗ LinearMap.id)]
    rfl

theorem bplain_cons (i : Λ) (l : List Λ) (F : H02.Grassmann Λ) :
    bplain (i :: l) F = bplain l (bstep i F) := by
  simp only [bplain, List.foldl_cons]
  rw [bplain_foldl]; rfl

/-- `∏_{i ∈ l} (1 + ξ_i η_i) = ∏_{i ∈ l} z_i⁻¹`. -/
def wprod (l : List Λ) : H02.Grassmann Λ := (l.map fun i => 1 + H02.ξ i * H02.η i).prod

theorem isFree_wprod {v : Λ} {l : List Λ} (hv : v ∉ l) : H02.IsFree v (wprod l) := by
  induction l with
  | nil => simpa [wprod] using H02.isFree_algebraMap v 1
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at hv
    simp only [wprod, List.map_cons, List.prod_cons]
    exact (H02.isFree_w (Ne.symm hv.1)).mul (ih hv.2)

/-- The hyperbolic integral of `H02` in terms of the plain one. -/
theorem berezin_eq_bplain {l : List Λ} (hl : l.Nodup) (F : H02.Grassmann Λ) :
    H02.berezin l F = bplain l (wprod l * F) := by
  induction l generalizing F with
  | nil => simp [wprod, bplain]
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [H02.berezin_cons, ih hl.2, H02.intStep_apply, bplain_cons, bstep]
    have hw := isFree_wprod hl.1
    simp only [LinearMap.coe_comp, Function.comp_apply]
    have e : wprod (i :: l) = (1 + H02.ξ i * H02.η i) * wprod l := by simp [wprod]
    rw [← H02.dη_free_mul hw, ← H02.dξ_free_mul hw, e, ← mul_assoc,
      H02.mul_comm_of_even hw.1]

end H24

end

end ArborealDecay.Super

end
