module

public import ArborealDecay.H02
public import ArborealDecay.Forest
public import ArborealDecay.Lattice
public import ArborealDecay.ExpDecay.Elem

/-!
# Notation and elementary bounds for the one-step contraction

`connProb β hβ x z = P_β[x ↔ z]` and `adjProb β hβ u v = P_β[uv ∈ F]` for the arboreal gas
`H02.arborealProb`.
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two-point function `P_β[x ↔ z]` of the arboreal gas. -/
noncomputable def connProb (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (x z : V) : ℝ :=
  H02.arborealProb β hβ (fun F => F.Reachable x z)

/-- The edge probability `P_β[uv ∈ F]`. -/
noncomputable def adjProb (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (u v : V) : ℝ :=
  H02.arborealProb β hβ (fun F => F.Adj u v)

theorem connProb_nonneg {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (x z : V) : 0 ≤ connProb β hβ x z :=
  H02.arborealProb_nonneg hβ hβ0 _

theorem connProb_le_one {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (x z : V) : connProb β hβ x z ≤ 1 :=
  H02.arborealProb_le_one hβ hβ0 _

theorem adjProb_nonneg {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (u v : V) : 0 ≤ adjProb β hβ u v :=
  H02.arborealProb_nonneg hβ hβ0 _

/-- `eq:single-edge-bound` with the weight bound `β ≤ B`. -/
theorem adjProb_le {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {B : ℝ} (hB : ∀ i j, β i j ≤ B) {u v : V} (huv : u ≠ v) :
    adjProb β hβ u v ≤ B / (1 + B) := by
  refine (Forest.arborealProb_adj_le hβ hβ0 huv).trans ?_
  have h0 := hβ0 u v
  have h1 := hB u v
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Counting the terms of the Simon–Lieb sum. -/
theorem sum_ite_le_card_mul (D : Finset V) (Q : V → V → Prop) [∀ u v, Decidable (Q u v)]
    (g : V → V → ℝ) (c : ℝ) (hg : ∀ u ∈ D, ∀ v ∈ Dᶜ, Q u v → g u v ≤ c) :
    ∑ u ∈ D, ∑ v ∈ Dᶜ, (if Q u v then g u v else 0)
      ≤ ((D ×ˢ Dᶜ).filter (fun p => Q p.1 p.2)).card * c := by
  rw [← Finset.sum_product' (f := fun u v => if Q u v then g u v else 0), Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  calc _ ≤ ∑ _p ∈ (D ×ˢ Dᶜ).filter (fun p => Q p.1 p.2), c :=
        Finset.sum_le_sum fun p hp => by
          simp only [Finset.mem_filter, Finset.mem_product] at hp
          exact hg p.1 hp.1.1 p.2 hp.1.2 hp.2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end ArborealDecay.ExpDecay
