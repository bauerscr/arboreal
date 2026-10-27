module

public import ArborealDecay.Final.Common
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.Frozen.TorusUniform
public import ArborealDecay.Frozen.TorusEuclNorm
public import ArborealDecay.Frozen.EdgeWeightsMap
public import ArborealDecay.Frozen.SupNorm
public import ArborealDecay.Frozen.AnnulusCollapse

/-!
# Final assembly: `expDecay_*` from (A), (C)
-/

@[expose] public section

namespace ArborealDecay.Final

open ArborealDecay.TLaw ArborealDecay.Wiring ArborealDecay.CondComb ArborealDecay.Bridge

/-- Frozen `expDecay_finite`, conditional only on (A), (C). -/
theorem expDecay_finite_of_AC
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (W : ArborealDecay.EdgeWeights Λ),
        (∀ x y : Λ, W.w x y ≠ 0 → ArborealDecay.IsNN x y) →
        (∀ x y : Λ, W.w x y ≤ β) →
        ∀ x y : Λ, ArborealDecay.twoPoint W x y ≤
          2 * Real.exp (-c * ArborealDecay.supDist x y) := by
  have hSP := ArborealDecay.Superpoly.superpoly_finite_of_inputs hW_lib
    (fun B hB => ArborealDecay.Annulus.annulus_of_inputs hA hC B hB)
  obtain ⟨c, hc, h⟩ := ArborealDecay.ExpDecay.expDecay_finite_of_inputs hSL_lib hSP β hβ
  refine ⟨c, hc, fun Λ W hnn hle x y => ?_⟩
  rw [twoPoint_eq]
  exact h Λ W.w W.symm W.nonneg hnn hle x y

/-- Frozen `expDecay_torus`, conditional only on (A), (C). -/
theorem expDecay_torus_of_AC
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (W : ArborealDecay.EdgeWeights (ZMod L × ZMod L)),
        (∀ x y, W.w x y ≠ 0 → ArborealDecay.IsTorusNN L x y) →
        (∀ x y, W.w x y ≤ β) →
        ∀ x y, ArborealDecay.twoPoint W x y ≤
          2 * Real.exp (-c * ArborealDecay.torusSupDist L x y) := by
  have hSP := ArborealDecay.Superpoly.superpoly_torus_of_inputs hW_lib
    (fun B hB => ArborealDecay.Annulus.annulus_of_inputs hA hC B hB)
  obtain ⟨c, hc, h⟩ := ArborealDecay.ExpDecay.expDecay_torus_of_inputs hSL_lib hSP β hβ
  refine ⟨c, hc, fun L _ W hnn hle x y => ?_⟩
  rw [twoPoint_eq]
  exact h L W.w W.symm W.nonneg hnn hle x y

/-- Frozen `expDecay_torus_eucl`, conditional only on (A), (C). -/
theorem expDecay_torus_eucl_of_AC
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (x : ZMod L × ZMod L),
        ArborealDecay.twoPoint (ArborealDecay.torusUniform L β hβ) 0 x ≤
          C * Real.exp (-c * ArborealDecay.torusEuclNorm L x) := by
  have hSP := ArborealDecay.Superpoly.superpoly_torus_of_inputs hW_lib
    (fun B hB => ArborealDecay.Annulus.annulus_of_inputs hA hC B hB)
  obtain ⟨C, c, hC0, hc, h⟩ :=
    ArborealDecay.ExpDecay.expDecay_torus_eucl_of_inputs hSL_lib hSP β hβ
  refine ⟨C, c, hC0, hc, fun L _ x => ?_⟩
  rw [twoPoint_eq, arborealProb_congr (w := (ArborealDecay.torusUniform L β hβ).w) (w' := ArborealDecay.ExpDecay.torusUniformWeight L β) rfl
    (ArborealDecay.ExpDecay.torusUniformWeight_symm L β)]
  exact h L x

end ArborealDecay.Final

end
