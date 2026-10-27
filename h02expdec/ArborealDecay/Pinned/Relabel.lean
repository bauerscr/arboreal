module

public import ArborealDecay.Pinned.Pinning
public import ArborealDecay.Pinned.Transport

/-!
# Relabelling the vertices of the Grassmann algebra; `lem:pinning` on `V`

For an equivalence `e : W ≃ V`, `relabel e : Ω(W) → Ω(V)` is the algebra isomorphism
`ξ_w ↦ ξ_{e w}`, `η_w ↦ η_{e w}`.  It preserves the fermionic integral and transports the
action.  Composing with the ghost embedding along `Equiv.optionSubtypeNe ρ` gives the embedding
`embSub ρ : Ω(Λ_ρ) → Ω(V)` (`ξ_i ↦ ξ_i`, `η_i ↦ η_i`), and supplement `lem:pinning` on `V`:
`[(1 - z_ρ) F]^V_{β,0} = [ξ_ρ η_ρ F]^V_{β,0} = [F]^{Λ_ρ}_{β|, β_{ρ·}}` for every `F ∈ Ω(Λ_ρ)`.
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02 CliffordAlgebra

section Relabel

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

/-- The linear map on generators induced by `e : W ≃ V`. -/
def relabelLin (e : W ≃ V) : Gen W →ₗ[ℝ] Gen V :=
  LinearMap.funLeft ℝ ℝ (Sum.map e.symm e.symm)

/-- `relabel e : Ω(W) → Ω(V)`, `ξ_w ↦ ξ_{e w}`, `η_w ↦ η_{e w}`. -/
def relabel (e : W ≃ V) : Grassmann W →ₐ[ℝ] Grassmann V := ExteriorAlgebra.map (relabelLin e)

theorem relabelLin_single_inl (e : W ≃ V) (w : W) :
    relabelLin e (Pi.single (Sum.inl w) 1) = Pi.single (Sum.inl (e w)) 1 := by
  funext s
  rcases s with v | v <;>
    simp [relabelLin, LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem relabelLin_single_inr (e : W ≃ V) (w : W) :
    relabelLin e (Pi.single (Sum.inr w) 1) = Pi.single (Sum.inr (e w)) 1 := by
  funext s
  rcases s with v | v <;>
    simp [relabelLin, LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

@[simp] theorem relabel_ξ (e : W ≃ V) (w : W) : relabel e (ξ w) = ξ (e w) := by
  rw [relabel, ξ, ExteriorAlgebra.map_apply_ι, relabelLin_single_inl, ξ]

@[simp] theorem relabel_η (e : W ≃ V) (w : W) : relabel e (η w) = η (e w) := by
  rw [relabel, η, ExteriorAlgebra.map_apply_ι, relabelLin_single_inr, η]

@[simp] theorem relabel_z (e : W ≃ V) (w : W) : relabel e (z w) = z (e w) := by
  simp [z]

@[simp] theorem relabel_dot (e : W ≃ V) (i j : W) : relabel e (dot i j) = dot (e i) (e j) := by
  simp [dot]

theorem proj_comp_relabelLin_inl (e : W ≃ V) (w : W) :
    (LinearMap.proj (R := ℝ) (φ := fun _ : V ⊕ V => ℝ) (Sum.inl (e w))) ∘ₗ relabelLin e =
      LinearMap.proj (R := ℝ) (φ := fun _ : W ⊕ W => ℝ) (Sum.inl w) := by
  ext v; simp [relabelLin, LinearMap.funLeft_apply]

theorem proj_comp_relabelLin_inr (e : W ≃ V) (w : W) :
    (LinearMap.proj (R := ℝ) (φ := fun _ : V ⊕ V => ℝ) (Sum.inr (e w))) ∘ₗ relabelLin e =
      LinearMap.proj (R := ℝ) (φ := fun _ : W ⊕ W => ℝ) (Sum.inr w) := by
  ext v; simp [relabelLin, LinearMap.funLeft_apply]

theorem dξ_relabel (e : W ≃ V) (w : W) (X : Grassmann W) :
    dξ (e w) (relabel e X) = relabel e (dξ w X) := by
  rw [dξ, relabel, contractLeft_map', proj_comp_relabelLin_inl]; rfl

theorem dη_relabel (e : W ≃ V) (w : W) (X : Grassmann W) :
    dη (e w) (relabel e X) = relabel e (dη w X) := by
  rw [dη, relabel, contractLeft_map', proj_comp_relabelLin_inr]; rfl

theorem intStep_relabel (e : W ≃ V) (w : W) (X : Grassmann W) :
    intStep (e w) (relabel e X) = relabel e (intStep w X) := by
  rw [intStep_apply, intStep_apply, ← dη_relabel, ← dξ_relabel, map_mul (relabel e),
    map_add (relabel e), map_one (relabel e), map_mul (relabel e), relabel_ξ, relabel_η]

theorem berezin_relabel (e : W ≃ V) (l : List W) (X : Grassmann W) :
    berezin (l.map e) (relabel e X) = relabel e (berezin l X) := by
  induction l generalizing X with
  | nil => rfl
  | cons i l ih => rw [List.map_cons, berezin_cons, berezin_cons, intStep_relabel, ih]

theorem algebraMapInv_relabel (e : W ≃ V) (X : Grassmann W) :
    ExteriorAlgebra.algebraMapInv (relabel e X) = ExteriorAlgebra.algebraMapInv X := by
  have : (ExteriorAlgebra.algebraMapInv : Grassmann V →ₐ[ℝ] ℝ).comp (relabel e) =
      ExteriorAlgebra.algebraMapInv := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [relabel, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : Grassmann W →ₐ[ℝ] ℝ => f X) this

variable [Fintype W] [Fintype V]

theorem univ_toList_perm_map (e : W ≃ V) :
    (univ : Finset V).toList.Perm ((univ : Finset W).toList.map e) := by
  refine (List.perm_ext_iff_of_nodup (nodup_toList _) ?_).2 fun x => ?_
  · exact (nodup_toList _).map e.injective
  · simp only [Finset.mem_toList, Finset.mem_univ, List.mem_map, true_and, true_iff]
    exact ⟨e.symm x, e.apply_symm_apply x⟩

/-- The fermionic integral is invariant under relabelling. -/
theorem int0_relabel (e : W ≃ V) (X : Grassmann W) : int0 (relabel e X) = int0 X := by
  rw [int0, berezin_perm (univ_toList_perm_map e), berezin_relabel, algebraMapInv_relabel, int0]

theorem relabel_action (e : W ≃ V) (β : V → V → ℝ) (h : V → ℝ) :
    relabel e (action (fun x y => β (e x) (e y)) (fun x => h (e x))) = action β h := by
  simp only [action, map_add, map_smul, map_sum, map_sub, map_one, relabel_dot, relabel_z]
  congr 1
  · congr 1
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e]
  · rw [← Equiv.sum_comp e]

/-- `[relabel e F]^V_{β,h} = [F]^W_{β ∘ e, h ∘ e}`. -/
theorem expect_relabel (e : W ≃ V) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (h : V → ℝ)
    (F : Grassmann W) :
    expect β h (relabel e F) = expect (fun x y => β (e x) (e y)) (fun x => h (e x)) F := by
  have hn := isNilpotent_neg_action (fun x y => β (e x) (e y)) (fun x y => hβ _ _)
    (fun x => h (e x))
  rw [H02.expect, H02.expect, ← relabel_action e β h, ← map_neg, ← IsNilpotent.map_exp hn,
    ← map_mul, int0_relabel]

end Relabel

/-- The action only depends on the off-diagonal weights. -/
theorem action_congr_offDiag {V : Type*} [DecidableEq V] [Fintype V] {β β' : V → V → ℝ}
    (hββ' : ∀ x y, x ≠ y → β x y = β' x y) (h : V → ℝ) : action β h = action β' h := by
  simp only [action]
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · rw [hββ' i j hij]

section Sub

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The embedding `Ω(Λ_ρ) → Ω(V)`, `ξ_i ↦ ξ_i`, `η_i ↦ η_i`. -/
def embSub (ρ : V) : Grassmann {v // v ≠ ρ} →ₐ[ℝ] Grassmann V :=
  (relabel (Equiv.optionSubtypeNe ρ)).comp emb

@[simp] theorem embSub_ξ (ρ : V) (i : {v // v ≠ ρ}) : embSub ρ (ξ i) = ξ (i : V) := by
  simp [embSub, emb_ξ]

@[simp] theorem embSub_η (ρ : V) (i : {v // v ≠ ρ}) : embSub ρ (η i) = η (i : V) := by
  simp [embSub, emb_η]

/-- **Supplement `lem:pinning`** (pinning for general forms, on `V`): for real symmetric
weights `β` on `V`, `ρ ∈ V` and every `F ∈ Ω(Λ_ρ)` (forms free of `ξ_ρ, η_ρ`),
`[(1 - z_ρ) F]^V_{β,0} = [ξ_ρ η_ρ F]^V_{β,0} = [F]^{Λ_ρ}_{β|, h}` with `h_j = β_{ρ j}`. -/
theorem lem_pinning {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V)
    (F : Grassmann {v // v ≠ ρ}) :
    expect β 0 ((1 - z ρ) * embSub ρ F) = expect β 0 (ξ ρ * η ρ * embSub ρ F) ∧
    expect β 0 (ξ ρ * η ρ * embSub ρ F) =
      expect (fun a b : {v // v ≠ ρ} => β a b) (fun a => β ρ a) F := by
  refine ⟨by rw [one_sub_z], ?_⟩
  set e := Equiv.optionSubtypeNe ρ
  have h1 : ξ ρ * η ρ * embSub ρ F = relabel e (ξ none * η none * emb F) := by
    rw [map_mul, map_mul, relabel_ξ, relabel_η]; rfl
  have hoff : ∀ x y : Option {v // v ≠ ρ}, x ≠ y →
      (fun x y => β (e x) (e y)) x y = ghostW (restrictW β ρ) (pinField β ρ) x y :=
    fun x y hxy => (ghostW_restrict_comp hβ ρ x y hxy).symm
  rw [h1, expect_relabel e hβ, show (fun x : Option {v // v ≠ ρ} => (0 : V → ℝ) (e x)) = 0 from rfl]
  rw [H02.expect, action_congr_offDiag (β := fun x y => β (e x) (e y)) hoff, ← H02.expect,
    expect_ghost_pin (restrictW_symm hβ ρ) (pinField β ρ)]

end Sub

end

end ArborealDecay.Pinned

end
