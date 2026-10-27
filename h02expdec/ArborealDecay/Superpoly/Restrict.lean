module

public import ArborealDecay.Surgery
public import ArborealDecay.Superpoly.Equiv

/-!
# Restriction of the two-point function to one side of a one-vertex union

* `arborealProb_reach_restrict`: `μ_β(x ↔ ρ) = μ_{β|V₁}(x ↔ ρ)` for `x ∈ V₁`.
* `arborealProb_reach_restrW`: the same with the weights outside `K × K` set to zero.
* `arborealProb_reach_embed`: pushing forward along an injective map, with extra isolated
  vertices, does not change the two-point function.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem oneVertexUnion_symm {V₁ V₂ : Finset Λ} {ρ : Λ} (h : OneVertexUnion V₁ V₂ ρ) :
    OneVertexUnion V₂ V₁ ρ where
  cover x := (h.cover x).symm
  inter x h2 h1 := h.inter x h1 h2
  mem₁ := h.mem₂
  mem₂ := h.mem₁

/-- `μ_β(x ↔ ρ) = μ_{β|V₁}(x ↔ ρ)` for `x ∈ V₁`. -/
theorem arborealProb_reach_restrict {V₁ V₂ : Finset Λ} {ρ : Λ} (hU : OneVertexUnion V₁ V₂ ρ)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hcross : ∀ u v, u ∈ V₁ → u ≠ ρ → v ∈ V₂ → v ≠ ρ → β u v = 0) {x : Λ} (hx : x ∈ V₁) :
    H02.arborealProb β hβ (fun F => F.Reachable x ρ) =
      H02.arborealProb (fun a b : V₁ => β a b) (fun a b => hβ a b)
        (fun G => G.Reachable ⟨x, hx⟩ ⟨ρ, hU.mem₁⟩) := by
  have t2 := H02.arborealProb_true (w := fun a b : V₂ => β a b) (fun a b => hβ a b)
    (fun a b => hβ0 a b)
  have e2 := arborealProb_union hU hβ hcross
    (fun G => G.Reachable ⟨x, hx⟩ ⟨ρ, hU.mem₁⟩) (fun _ => True)
  rw [t2, mul_one] at e2
  have c2 := arborealProb_congr_noCross hβ hcross (fun F => F.Reachable x ρ)
    (fun F => (resFin V₁ F).Reachable ⟨x, hx⟩ ⟨ρ, hU.mem₁⟩ ∧ True)
    (fun F _ hF => (reach_iff_res₁ hU hF hx).trans (and_true _).symm.to_iff)
  rw [c2, e2]

/-- The weights restricted to `K × K` (zero elsewhere). -/
def restrW (K : Finset Λ) (β : Λ → Λ → ℝ) (u v : Λ) : ℝ :=
  if u ∈ K ∧ v ∈ K then β u v else 0

theorem restrW_symm (K : Finset Λ) {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (i j : Λ) :
    restrW K β i j = restrW K β j i := by
  unfold restrW
  by_cases h : i ∈ K ∧ j ∈ K
  · simp [h.1, h.2, hβ i j]
  · have h' : ¬ (j ∈ K ∧ i ∈ K) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [h, h', ite_false]

theorem restrW_nonneg (K : Finset Λ) {β : Λ → Λ → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) (i j : Λ) :
    0 ≤ restrW K β i j := by
  unfold restrW; split_ifs
  · exact hβ0 i j
  · exact le_rfl

/-- Zeroing the weights on the other side of a one-vertex union does not change `μ(x ↔ ρ)`. -/
theorem arborealProb_reach_restrW {K O : Finset Λ} {ρ : Λ} (hU : OneVertexUnion K O ρ)
    {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hcross : ∀ u v, u ∈ K → u ≠ ρ → v ∈ O → v ≠ ρ → β u v = 0) {x : Λ} (hx : x ∈ K) :
    H02.arborealProb β hβ (fun F => F.Reachable x ρ) =
      H02.arborealProb (restrW K β) (restrW_symm K hβ) (fun F => F.Reachable x ρ) := by
  rw [arborealProb_reach_restrict hU hβ hβ0 hcross hx]
  have hc' : ∀ u v, u ∈ K → u ≠ ρ → v ∈ O → v ≠ ρ → restrW K β u v = 0 := by
    intro u v _ _ hv hvρ
    unfold restrW
    have : v ∉ K := fun hvK => hvρ (hU.inter v hvK hv)
    simp [this]
  rw [arborealProb_reach_restrict hU (restrW_symm K hβ) (restrW_nonneg K hβ0) hc' hx]
  have : (fun a b : K => restrW K β a b) = (fun a b : K => β a b) := by
    funext a b
    unfold restrW
    simp [a.2, b.2]
  simp only [this]

theorem arborealProb_congr_weights {β γ : Λ → Λ → ℝ} (e : β = γ) (hβ : ∀ i j, β i j = β j i)
    (hγ : ∀ i j, γ i j = γ j i) (P : SimpleGraph Λ → Prop) :
    H02.arborealProb β hβ P = H02.arborealProb γ hγ P := by
  subst e; rfl

/-- Pushing forward along an injective map with extra isolated vertices. -/
theorem arborealProb_reach_embed {W : Type*} [Fintype W] [DecidableEq W] (j : W → Λ)
    (hj : Function.Injective j) {β : Λ → Λ → ℝ} {γ : W → W → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hγ : ∀ i j, γ i j = γ j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hsupp : ∀ u v, (∀ w, j w ≠ u) ∨ (∀ w, j w ≠ v) → β u v = 0)
    (hw : ∀ a b, β (j a) (j b) = γ a b) (a b : W) :
    H02.arborealProb β hβ (fun F => F.Reachable (j b) (j a)) =
      H02.arborealProb γ hγ (fun G => G.Reachable b a) := by
  set V₁ : Finset Λ := univ.filter (fun u => ∃ w, j w = u) with hV₁
  set V₂ : Finset Λ := insert (j a) V₁ᶜ with hV₂
  have hja : j a ∈ V₁ := by simp [hV₁]
  have hU : OneVertexUnion V₁ V₂ (j a) :=
    { cover := fun x => by
        by_cases hx : x ∈ V₁
        · exact Or.inl hx
        · exact Or.inr (by simp [hV₂, hx])
      inter := fun x h1 h2 => by
        simp only [hV₂, mem_insert, mem_compl] at h2
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd h1 h2
      mem₁ := hja
      mem₂ := by simp [hV₂] }
  have hcross : ∀ u v, u ∈ V₁ → u ≠ j a → v ∈ V₂ → v ≠ j a → β u v = 0 := by
    intro u v _ _ hv hvρ
    apply hsupp
    right
    intro w hw
    simp only [hV₂, mem_insert, mem_compl, hV₁, mem_filter, mem_univ, true_and] at hv
    rcases hv with hv | hv
    · exact hvρ hv
    · exact hv ⟨w, hw⟩
  have hjb : j b ∈ V₁ := by simp [hV₁]
  rw [arborealProb_reach_restrict hU hβ hβ0 hcross hjb]
  let e : W ≃ V₁ := Equiv.ofBijective (fun w => ⟨j w, by simp [hV₁]⟩) ⟨by
      intro w w' h
      exact hj (congrArg Subtype.val h), by
      rintro ⟨u, hu⟩
      simp only [hV₁, mem_filter, mem_univ, true_and] at hu
      obtain ⟨w, rfl⟩ := hu
      exact ⟨w, rfl⟩⟩
  have := arborealProb_reach_equiv e hγ (fun a b : V₁ => hβ a b)
    (fun a b => hw a b) b a
  rw [this]
  rfl

end

end ArborealDecay.Superpoly
