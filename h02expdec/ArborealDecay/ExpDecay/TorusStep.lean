module

public import ArborealDecay.ExpDecay.TorusCard

/-!
# One-step contraction on the torus (`eq:one-step-contraction`, `L > 2R + 2`)
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Finset ArborealDecay.Lattice

/-- `eq:one-step-contraction` on the torus `(ℤ/L)²` for `L > 2R + 2`. -/
theorem oneStep_torus_of_inputs
    (hSL : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j) (D : Finset V) (x z : V),
      x ∈ D → z ∉ D →
      connProb β hβ x z ≤ ∑ u ∈ D, ∑ v ∈ Dᶜ,
        (if u ≠ v ∧ β u v ≠ 0 then
          adjProb β hβ u v * connProb β hβ x u * connProb β hβ v z else 0))
    {A a B : ℝ} (hA : 0 ≤ A)
    (hSP : ∀ (L : ℕ) [NeZero L] (β : ZMod L × ZMod L → ZMod L × ZMod L → ℝ)
      (hβ : ∀ i j, β i j = β j i) (_ : ∀ i j, 0 ≤ β i j)
      (_ : ∀ i j, β i j ≠ 0 → IsTorusNN L i j) (_ : ∀ i j, β i j ≤ B)
      (x z : ZMod L × ZMod L),
      connProb β hβ x z ≤ min 1 (A * Real.exp (-a * Real.log (2 + (torusSupDist L x z : ℝ)) ^ 2)))
    (R : ℕ) (L : ℕ) [NeZero L] (hL : 2 * R + 2 < L)
    (β : ZMod L × ZMod L → ZMod L × ZMod L → ℝ) (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hNN : ∀ i j, β i j ≠ 0 → IsTorusNN L i j)
    (hB : ∀ i j, β i j ≤ B) (y z : ZMod L × ZMod L) (hyz : R < torusSupDist L y z) (M : ℝ)
    (hM : ∀ v : ZMod L × ZMod L, torusSupDist L y v ≤ R + 1 → connProb β hβ v z ≤ M) :
    connProb β hβ y z ≤ (8 * (R : ℝ) + 4) * (B / (1 + B)) * qFun A a R * M := by
  classical
  set D : Finset (ZMod L × ZMod L) :=
    Finset.univ.filter (fun u => torusSupDist L y u ≤ R) with hD
  have hyD : y ∈ D := by simp [hD, torusSupDist_self]
  have hzD : z ∉ D := by simp [hD]; exact hyz
  have h1 := hSL _ β hβ hβ0 D y z hyD hzD
  have hM0 : 0 ≤ M :=
    (connProb_nonneg hβ hβ0 y z).trans (hM y (by simp [torusSupDist_self]))
  have hB0 : 0 ≤ B := (hβ0 y y).trans (hB y y)
  have hq := qFun_nonneg hA (a := a) R
  have hp : 0 ≤ B / (1 + B) := by positivity
  have hterm : ∀ u ∈ D, ∀ v ∈ Dᶜ, (u ≠ v ∧ β u v ≠ 0) →
      adjProb β hβ u v * connProb β hβ y u * connProb β hβ v z
        ≤ B / (1 + B) * qFun A a R * M := by
    intro u hu v hv ⟨huv, hb⟩
    have hu' : torusSupDist L y u ≤ R := by simpa [hD] using hu
    have hv' : R < torusSupDist L y v := by simpa [hD] using hv
    have n1 := (hNN u v hb).torusSupDist_le_one
    have t1 := torusSupDist_triangle y u v
    have t2 := torusSupDist_triangle y v u
    have n2 := (hNN u v hb).symm.torusSupDist_le_one
    have e1 : torusSupDist L y u = R := by omega
    have c1 : connProb β hβ y u ≤ qFun A a R := by
      refine (hSP L β hβ hβ0 hNN hB y u).trans ?_
      rw [e1, qFun]
    have c2 : connProb β hβ v z ≤ M := hM v (by omega)
    have c3 := adjProb_le hβ hβ0 hB huv
    exact mul_le_mul (mul_le_mul c3 c1 (connProb_nonneg hβ hβ0 _ _) hp) c2
      (connProb_nonneg hβ hβ0 _ _) (by positivity)
  have h2 := sum_ite_le_card_mul D (fun u v => u ≠ v ∧ β u v ≠ 0)
    (fun u v => adjProb β hβ u v * connProb β hβ y u * connProb β hβ v z)
    (B / (1 + B) * qFun A a R * M) hterm
  have hcard : (((D ×ˢ Dᶜ).filter
      (fun p : (ZMod L × ZMod L) × (ZMod L × ZMod L) => p.1 ≠ p.2 ∧ β p.1 p.2 ≠ 0)).card : ℝ)
      ≤ 8 * (R : ℝ) + 4 := by
    have hL' : 2 * (R : ℤ) + 2 < L := by exact_mod_cast hL
    have hle : ((D ×ˢ Dᶜ).filter
        (fun p : (ZMod L × ZMod L) × (ZMod L × ZMod L) => p.1 ≠ p.2 ∧ β p.1 p.2 ≠ 0)).card
        ≤ (exitEdges (0 : ℤ × ℤ) R).card := by
      refine Finset.card_le_card_of_injOn
        (fun p => (torusLift y p.1, torusLift y p.2)) ?_ ?_
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_compl, Set.mem_ofPred_eq,
          hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨hu, hv⟩, _, hb⟩ := hp
        have n1 := (hNN _ _ hb).torusSupDist_le_one
        have t1 := torusSupDist_triangle y p.1 p.2
        rw [Finset.mem_coe, mem_exitEdges, supDist_zero_torusLift, supDist_zero_torusLift]
        exact ⟨by exact_mod_cast hu, by exact_mod_cast not_le.mp hv,
          isNN_torusLift hL' hu (by omega) (hNN _ _ hb)⟩
      · intro p _ q _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (torusLift_injective y h.1) (torusLift_injective y h.2)
    have h3 := card_exitEdges_le (0 : ℤ × ℤ) (R := (R : ℤ)) (by positivity)
    have h4 : ((exitEdges (0 : ℤ × ℤ) R).card : ℝ) ≤ 8 * (R : ℝ) + 4 := by
      exact_mod_cast h3
    exact (Nat.cast_le.mpr hle).trans h4
  calc connProb β hβ y z ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ (8 * (R : ℝ) + 4) * (B / (1 + B) * qFun A a R * M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end ArborealDecay.ExpDecay
