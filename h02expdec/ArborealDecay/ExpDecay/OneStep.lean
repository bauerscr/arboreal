module

public import ArborealDecay.ExpDecay.Defs

/-!
# One-step contraction for finite `ℤ²` subgraphs (`eq:one-step-contraction`)

Vertices of the graph `G` are the elements of `Λ : Finset (ℤ × ℤ)` (as a subtype).
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Finset ArborealDecay.Lattice

/-- `eq:one-step-contraction` for finite nearest-neighbour subgraphs of `ℤ²`, from the
Simon–Lieb inequality (for all finite weighted graphs) and the superpolynomial bound `hSP`
for the given profile `(A, a)` and weight bound `B`. -/
theorem oneStep_finite_of_inputs
    (hSL : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j) (D : Finset V) (x z : V),
      x ∈ D → z ∉ D →
      connProb β hβ x z ≤ ∑ u ∈ D, ∑ v ∈ Dᶜ,
        (if u ≠ v ∧ β u v ≠ 0 then
          adjProb β hβ u v * connProb β hβ x u * connProb β hβ v z else 0))
    {A a B : ℝ} (hA : 0 ≤ A)
    (hSP : ∀ (Λ : Finset (ℤ × ℤ)) (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i)
      (_ : ∀ i j, 0 ≤ β i j) (_ : ∀ i j, β i j ≠ 0 → IsNN (i : ℤ × ℤ) j) (_ : ∀ i j, β i j ≤ B)
      (x z : Λ),
      connProb β hβ x z ≤ min 1 (A * Real.exp (-a * Real.log (2 + (supDist x z : ℝ)) ^ 2)))
    (R : ℕ) (Λ : Finset (ℤ × ℤ)) (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hNN : ∀ i j, β i j ≠ 0 → IsNN (i : ℤ × ℤ) j)
    (hB : ∀ i j, β i j ≤ B) (y z : Λ) (hyz : (R : ℤ) < supDist y z) (M : ℝ)
    (hM : ∀ v : Λ, supDist (y : ℤ × ℤ) v ≤ (R : ℤ) + 1 → connProb β hβ v z ≤ M) :
    connProb β hβ y z ≤ (8 * (R : ℝ) + 4) * (B / (1 + B)) * qFun A a R * M := by
  classical
  set D : Finset Λ := Finset.univ.filter (fun u : Λ => supDist (y : ℤ × ℤ) u ≤ R) with hD
  have hyD : y ∈ D := by simp [hD, supDist_self]
  have hzD : z ∉ D := by simp [hD]; exact hyz
  have h1 := hSL Λ β hβ hβ0 D y z hyD hzD
  have hM0 : 0 ≤ M := (connProb_nonneg hβ hβ0 y z).trans (hM y (by simp [supDist_self]; positivity))
  have hB0 : 0 ≤ B := (hβ0 y y).trans (hB y y)
  have hq := qFun_nonneg hA (a := a) R
  have hp : 0 ≤ B / (1 + B) := by positivity
  -- the terms
  have hterm : ∀ u ∈ D, ∀ v ∈ Dᶜ, (u ≠ v ∧ β u v ≠ 0) →
      adjProb β hβ u v * connProb β hβ y u * connProb β hβ v z
        ≤ B / (1 + B) * qFun A a R * M := by
    intro u hu v hv ⟨huv, hb⟩
    have hu' : supDist (y : ℤ × ℤ) u ≤ R := by simpa [hD] using hu
    have hv' : (R : ℤ) < supDist (y : ℤ × ℤ) v := by simpa [hD] using hv
    have hex : ((u : ℤ × ℤ), (v : ℤ × ℤ)) ∈ exitEdges (y : ℤ × ℤ) R :=
      mem_exitEdges.mpr ⟨hu', hv', hNN u v hb⟩
    obtain ⟨e1, e2⟩ := exitEdges_supDist hex
    have c1 : connProb β hβ y u ≤ qFun A a R := by
      refine (hSP Λ β hβ hβ0 hNN hB y u).trans ?_
      rw [e1, qFun]; simp
    have c2 : connProb β hβ v z ≤ M := hM v (by omega)
    have c3 := adjProb_le hβ hβ0 hB huv
    exact mul_le_mul (mul_le_mul c3 c1 (connProb_nonneg hβ hβ0 _ _) hp) c2
      (connProb_nonneg hβ hβ0 _ _) (by positivity)
  have h2 := sum_ite_le_card_mul D (fun u v => u ≠ v ∧ β u v ≠ 0)
    (fun u v => adjProb β hβ u v * connProb β hβ y u * connProb β hβ v z)
    (B / (1 + B) * qFun A a R * M) hterm
  have hcard : (((D ×ˢ Dᶜ).filter (fun p : Λ × Λ => p.1 ≠ p.2 ∧ β p.1 p.2 ≠ 0)).card : ℝ)
      ≤ 8 * (R : ℝ) + 4 := by
    have hle : ((D ×ˢ Dᶜ).filter (fun p : Λ × Λ => p.1 ≠ p.2 ∧ β p.1 p.2 ≠ 0)).card
        ≤ (exitEdges (y : ℤ × ℤ) R).card := by
      refine Finset.card_le_card_of_injOn
        (fun p : Λ × Λ => ((p.1 : ℤ × ℤ), (p.2 : ℤ × ℤ))) ?_ ?_
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_compl, Set.mem_ofPred_eq,
          hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact mem_exitEdges.mpr ⟨hp.1.1, by simpa using hp.1.2, hNN _ _ hp.2.2⟩
      · intro p _ q _ h
        simp only [Prod.mk.injEq, Subtype.coe_inj] at h
        exact Prod.ext h.1 h.2
    have h3 := card_exitEdges_le (y : ℤ × ℤ) (R := (R : ℤ)) (by positivity)
    have h4 : ((exitEdges (y : ℤ × ℤ) R).card : ℝ) ≤ 8 * (R : ℝ) + 4 := by
      exact_mod_cast h3
    exact (Nat.cast_le.mpr hle).trans h4
  calc connProb β hβ y z ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ (8 * (R : ℝ) + 4) * (B / (1 + B) * qFun A a R * M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end ArborealDecay.ExpDecay
