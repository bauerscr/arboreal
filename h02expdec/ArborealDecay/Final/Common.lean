module

public import ArborealDecay.Bridge
public import ArborealDecay.Annulus
public import ArborealDecay.Superpoly
public import ArborealDecay.ExpDecay
public import ArborealDecay.Wiring
public import ArborealDecay.SimonLieb

/-!
# Shared discharges for the final assembly

Unconditional library inputs (`hSL`, `hW`) in the forms consumed by `ExpDecay` and `Superpoly`,
and the transfer of the `Annulus` conclusion to the `Superpoly` annulus collapse (`hAN`).
-/

@[expose] public section

namespace ArborealDecay.Final

open ArborealDecay.ExpDecay ArborealDecay.Surgery

/-- `hSL` of `ExpDecay`, from the unconditional Simon–Lieb inequality. -/
theorem hSL_lib : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
    (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j) (D : Finset V) (x z : V),
    x ∈ D → z ∉ D →
    connProb β hβ x z ≤ ∑ u ∈ D, ∑ v ∈ Dᶜ,
      (if u ≠ v ∧ β u v ≠ 0 then
        adjProb β hβ u v * connProb β hβ x u * connProb β hβ v z else 0) :=
  fun V _ _ β hβ hβ0 D x z hx hz =>
    ArborealDecay.SimonLieb.simon_lieb hβ hβ0 D x z hx hz

/-- `hW` of `Superpoly`, from the unconditional separator wiring. -/
theorem hW_lib : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
    (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
    ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
      (∀ p : (ArborealDecay.Superpoly.suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
      connProb β hβ a b ≤
        connProb (mapW β (ArborealDecay.Superpoly.collapse S)) (mapW_symm hβ _)
          (ArborealDecay.Superpoly.collapse S a) (ArborealDecay.Superpoly.collapse S b) :=
  fun V _ _ β hβ hβ0 S a b ha hb hsep =>
    ArborealDecay.Wiring.separator_wiring β hβ hβ0 a b S ha hb hsep

/-- `arborealProb` depends only on the weight function. -/
theorem arborealProb_congr {V : Type*} [Fintype V] [DecidableEq V] {w w' : V → V → ℝ}
    (h : w = w') {hw : ∀ i j, w i j = w j i} (hw' : ∀ i j, w' i j = w' j i)
    {P : SimpleGraph V → Prop} :
    H02.arborealProb w hw P = H02.arborealProb w' hw' P := by
  subst h; rfl

end ArborealDecay.Final

end
