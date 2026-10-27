module

public import ArborealDecay.Pinned.Unpinned
public import ArborealDecay.Pinned.Pinning
public import ArborealDecay.Pinned.Transport

/-!
# Supplement `thm:H02-pinned` and `cor:pinned-fermion`

`Γ = (V, β)` is a finite graph given by real symmetric weights `β`, `ρ ∈ V`,
`Λ_ρ = {v // v ≠ ρ}`, the pinned model is the `ℍ^{0|2}` model on `Λ_ρ` with weights
`β|_{Λ_ρ}` (`restrictW β ρ`) and field `h_j = β_{ρ j}` (`pinField β ρ`).

* (i)  `[1]^{Λ_ρ}_{β,h} = Z_Γ` (real weights);
* (ii) `[ξ_a η_b]^{Λ_ρ}_{β,h} = ∑_{F ∈ 𝓕(Γ) : a ↔ b, a ↮ ρ} β(F)` (real weights, `a = b` allowed);
* (iii) for `β ≥ 0`: `Z_Γ ≥ 1` and `⟨ξ_a η_b⟩^{Λ_ρ}_{β,h} = P_Γ(a ↔ b, a ↮ ρ)`.

No connectivity hypothesis is needed (supplement `rem:conn-hyp`).
-/

@[expose] public section

namespace ArborealDecay.Pinned

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical H02

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fsum_eq_filter_sum (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i)
    (P : SimpleGraph V → Prop) [DecidablePred P] :
    fsum β hβ P = ∑ F : SimpleGraph V with P F, forestWeight β hβ F := by
  rw [fsum, fset]
  exact Finset.sum_congr (by ext F; simp) fun _ _ => rfl

/-- **Supplement `thm:H02-pinned` (i)** (denominator): `[1]^{Λ_ρ}_{β|, h} = Z_Γ`, for real
symmetric weights `β`. -/
theorem thm_H02_pinned_denominator {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V) :
    expect (fun a b : {v // v ≠ ρ} => β a b) (fun a => β ρ a) 1 = Zforest β hβ := by
  rw [← Zforest_ghostW (restrictW_symm hβ ρ) (pinField β ρ), Zforest_eq_fsum, Zforest_eq_fsum]
  have := fsum_ghost_eq hβ ρ (fun F => F.IsAcyclic)
  rw [← this]
  congr 1
  funext F
  exact propext (isAcyclic_comap_equiv _ F).symm

/-- **Supplement `thm:H02-pinned` (ii)** (numerator): for `a, b ∈ Λ_ρ` (`a = b` allowed),
`[ξ_a η_b]^{Λ_ρ}_{β|, h} = ∑_{F ∈ 𝓕(Γ) : a ↔ b, a ↮ ρ} β(F)`, for real symmetric weights. -/
theorem thm_H02_pinned_numerator {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (ρ : V)
    (a b : {v // v ≠ ρ}) :
    expect (fun a b : {v // v ≠ ρ} => β a b) (fun a => β ρ a) (ξ a * η b) =
      ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b ∧ ¬F.Reachable a ρ,
        forestWeight β hβ F := by
  rw [← fsum_eq_filter_sum, ← fsum_ghost_eq hβ ρ,
    ← expect_ghost_pin (restrictW_symm hβ ρ) (pinField β ρ), map_mul, emb_ξ, emb_η,
    expect_pin_ξη _ (ghostW_symm (restrictW_symm hβ ρ) _) (Option.some_ne_none a)
      (Option.some_ne_none b)]
  congr 1
  funext F
  rw [isAcyclic_comap_equiv, reachable_comap_equiv, reachable_comap_equiv,
    optionSubtypeNe_symm_coe, optionSubtypeNe_symm_coe, Equiv.optionSubtypeNe_symm_self]

/-- `Z_Γ ≥ 1` for non-negative weights (the empty forest has weight `1`). -/
theorem one_le_Zforest {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) :
    1 ≤ Zforest β hβ := by
  have h1 : forestWeight β hβ ⊥ = 1 := Finset.prod_eq_one fun e he => by simp at he
  have := Finset.single_le_sum (s := univ.filter fun F : SimpleGraph V => F.IsAcyclic)
    (fun F _ => forestWeight_nonneg hβ hβ0 F) (a := ⊥) (by simp)
  rw [h1] at this
  exact this

/-- **Supplement `thm:H02-pinned` (iii)**: for non-negative symmetric weights `β` on `V`, `ρ ∈ V`
and `a, b ∈ Λ_ρ = V \ {ρ}` (`a = b` allowed), the pinned `ℍ^{0|2}` model on `Λ_ρ` with weights
`β|_{Λ_ρ}` and field `h_j = β_{ρ j}` satisfies `Z_Γ ≥ 1` and
`⟨ξ_a η_b⟩^{Λ_ρ}_{β|, h} = P_Γ(a ↔ b, a ↮ ρ)`. No connectivity hypothesis. -/
theorem thm_H02_pinned {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (ρ : V) (a b : {v // v ≠ ρ}) :
    1 ≤ Zforest β hβ ∧
    avg (fun a b : {v // v ≠ ρ} => β a b) (fun a => β ρ a) (ξ a * η b) =
      arborealProb β hβ (fun F => F.Reachable a b ∧ ¬F.Reachable a ρ) := by
  refine ⟨one_le_Zforest hβ hβ0, ?_⟩
  rw [avg, thm_H02_pinned_numerator hβ, thm_H02_pinned_denominator hβ, arborealProb]
  congr 1
  exact Finset.sum_congr (by ext F; simp) fun _ _ => rfl

/-- **Supplement `cor:pinned-fermion`**: for non-negative symmetric weights, the two readings of
the pinned fermionic expectation (the pinned model on `Λ_ρ` with field `β_{ρ ·}`, and the
unpinned zero-field model on `V` with the insertion `ξ_ρ η_ρ`) both equal
`P_Γ(i ↔ j, i ↮ ρ)` for `i, j ≠ ρ`, and both partition functions equal `Z_Γ`. -/
theorem cor_pinned_fermion {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (ρ : V) (i j : {v // v ≠ ρ}) :
    avg (fun a b : {v // v ≠ ρ} => β a b) (fun a => β ρ a) (ξ i * η j) =
      arborealProb β hβ (fun F => F.Reachable i j ∧ ¬F.Reachable i ρ) ∧
    expect β 0 (ξ ρ * η ρ * (ξ (i : V) * η (j : V))) / expect β 0 (ξ ρ * η ρ) =
      arborealProb β hβ (fun F => F.Reachable i j ∧ ¬F.Reachable i ρ) ∧
    expect (fun a b : {v // v ≠ ρ} => β a b) (fun a => β ρ a) 1 = Zforest β hβ ∧
    expect β 0 (ξ ρ * η ρ) = Zforest β hβ := by
  refine ⟨(thm_H02_pinned hβ hβ0 ρ i j).2, ?_, thm_H02_pinned_denominator hβ ρ,
    expect_pin β hβ ρ⟩
  rw [expect_pin_ξη β hβ i.2 j.2, expect_pin β hβ ρ, arborealProb, fsum_eq_filter_sum]
  congr 1
  exact Finset.sum_congr (by ext F; simp) fun _ _ => rfl

end

end ArborealDecay.Pinned

end
