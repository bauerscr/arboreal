import Obs2.Map.Ops
import Obs.Norm
import Obs.StepObsNonlinGen
import Step2.Map.TNorm2

/-!
# Submultiplicative norms with sources (`SNorm` instances on `OE`)

The generic estimates of `Obs.Gen` (`KHypG`, `RHypG`, `Obs2.Est.CrudeG`) are stated for a
submultiplicative seminorm `Obs.Gen.SNorm`. This file provides the instances on the even algebra
with sources `OE c X`:

* `NrmP nrm`: a bulk norm on `𝒩(X)` that is subadditive, absolutely homogeneous,
  submultiplicative, with `nrm 1 ≤ 1`; instances `nrmP_tNorm` (`T(h, ℓ)`) and `nrmP_T2` (the
  two-scale norm `T(ℓ' ⊔ ℓ_C)` of the doubled algebra);
* `oNorm_mul_le'`: the product property of `oNorm nrm w` on `OE` under `w_ab ≤ w_a w_b`, for any
  `NrmP` norm (`Obs.oT_mul_le` is the case of `tNorm`);
* **`oSN hn w hw`**: the `SNorm` `F ↦ ‖F_∅‖ + w_a ‖F_a‖ + w_b ‖F_b‖ + w_ab ‖F_ab‖`;
* `oNorm_ECCO_le`: `‖𝔼_C F‖_{T(ℓ')} ≤ ‖F‖_{T(ℓ' ⊔ ℓ_C)}` with sources, for a covariance with a
  Gram bound at `ℓ_C` (the hypothesis `hE` of `KHypG.KnextG_le`).
-/

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA ENNReal

variable {c : Obs.Case} {X : Type*} [DecidableEq X] [Fintype X]

/-- The properties of a bulk norm used by the product property. -/
structure NrmP (nrm : Grassmann.N X → ℝ≥0∞) : Prop where
  zero : nrm 0 = 0
  add : ∀ x y, nrm (x + y) ≤ nrm x + nrm y
  smul : ∀ (r : ℂ) x, nrm (r • x) = ENNReal.ofReal ‖r‖ * nrm x
  mul : ∀ x y, nrm (x * y) ≤ nrm x * nrm y
  one : nrm 1 ≤ 1

namespace NrmP

variable {nrm : Grassmann.N X → ℝ≥0∞} (hn : NrmP nrm)
include hn

theorem neg (x : Grassmann.N X) : nrm (-x) = nrm x := by
  rw [← neg_one_smul ℂ x, hn.smul]; simp

theorem smul_s (x : Grassmann.N X) : nrm (c.s • x) = nrm x := by
  rw [hn.smul, Case.norm_s]; simp

end NrmP

theorem nrmP_tNorm {E : Type*} [Fintype E] [DecidableEq E] [AddAction (E → ℕ) X] {p : ℕ}
    {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) : NrmP (tNorm E p h ℓ (X := X)) where
  zero := tNorm_zero'
  add := Loc.tNorm_add_le
  smul := Step.tNorm_smul
  mul := tNorm_mul_le hh hℓ
  one := Loc.tNorm_one_le hh hℓ

theorem nrmP_T2 {E : Type*} [Fintype E] [DecidableEq E] [AddAction (E → ℕ) X] {p : ℕ}
    {h ℓ' ℓC : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ') : NrmP (Step2.T2 E p h ℓ' ℓC (Λ := X)) where
  zero := Step2.T2_zero
  add := Step2.T2_add_le
  smul := Step2.T2_smul
  mul := Step2.T2_mul_le hh hℓ
  one := Step2.T2_one_le hh hℓ

variable {nrm : Grassmann.N X → ℝ≥0∞} {w : Wt}

theorem oNorm_add_le' (hn : NrmP nrm) (F G : SA c X) :
    oNorm nrm w (F + G) ≤ oNorm nrm w F + oNorm nrm w G := by
  simp only [oNorm, add_e, add_a, add_b, add_ab]
  calc _ ≤ (nrm F.e + nrm G.e) + w.a * (nrm F.a + nrm G.a) + w.b * (nrm F.b + nrm G.b)
        + w.ab * (nrm F.ab + nrm G.ab) := by gcongr <;> exact hn.add _ _
    _ = _ := by ring

theorem oNorm_neg' (hn : NrmP nrm) (F : SA c X) : oNorm nrm w (-F) = oNorm nrm w F := by
  simp only [oNorm, neg_e, neg_a, neg_b, neg_ab, hn.neg]

theorem oNorm_zero' (hn : NrmP nrm) : oNorm nrm w (0 : SA c X) = 0 := by
  simp [oNorm, zero_e, zero_a, zero_b, zero_ab, hn.zero]

theorem oNorm_one_le' (hn : NrmP nrm) : oNorm nrm w (1 : SA c X) ≤ 1 := by
  simp only [oNorm, one_e, one_a, one_b, one_ab, hn.zero, mul_zero, add_zero]
  exact hn.one

/-- **The product property** of `oNorm nrm w` on even elements, `w_ab ≤ w_a w_b`. -/
theorem oNorm_mul_le' (hn : NrmP nrm) (hw : w.Sub) (F G : OE c X) :
    oNorm nrm w ((F * G : OE c X) : SA c X) ≤
      oNorm nrm w (F : SA c X) * oNorm nrm w (G : SA c X) := by
  set n := nrm
  rw [oNorm, OE.mul_e, OE.mul_a, OE.mul_b, OE.mul_ab]
  have hm : ∀ x y : Grassmann.N X, n (x * y) ≤ n x * n y := hn.mul
  have ha : ∀ x y : Grassmann.N X, n (x + y) ≤ n x + n y := hn.add
  set fe := n (F : SA c X).e; set fa := n (F : SA c X).a; set fb := n (F : SA c X).b
  set fab := n (F : SA c X).ab; set ge := n (G : SA c X).e; set ga := n (G : SA c X).a
  set gb := n (G : SA c X).b; set gab := n (G : SA c X).ab
  have h1 : n ((F : SA c X).e * (G : SA c X).a + (F : SA c X).a * (G : SA c X).e) ≤
      fe * ga + fa * ge := (ha _ _).trans (add_le_add (hm _ _) (hm _ _))
  have h2 : n ((F : SA c X).e * (G : SA c X).b + (F : SA c X).b * (G : SA c X).e) ≤
      fe * gb + fb * ge := (ha _ _).trans (add_le_add (hm _ _) (hm _ _))
  have h3 : n ((F : SA c X).e * (G : SA c X).ab + c.s • ((F : SA c X).a * (G : SA c X).b) +
      (F : SA c X).b * (G : SA c X).a + (F : SA c X).ab * (G : SA c X).e) ≤
      fe * gab + fa * gb + fb * ga + fab * ge := by
    refine (ha _ _).trans (add_le_add ((ha _ _).trans (add_le_add ((ha _ _).trans
      (add_le_add (hm _ _) ?_)) (hm _ _))) (hm _ _))
    exact (hn.smul_s _).trans_le (hm _ _)
  have hw' : w.ab ≤ w.a * w.b := hw
  calc n ((F : SA c X).e * (G : SA c X).e) + w.a * n _ + w.b * n _ + w.ab * n _
      ≤ fe * ge + w.a * (fe * ga + fa * ge) + w.b * (fe * gb + fb * ge) +
        w.ab * (fe * gab + fa * gb + fb * ga + fab * ge) := by
        gcongr
        exact hm _ _
    _ ≤ fe * ge + w.a * (fe * ga + fa * ge) + w.b * (fe * gb + fb * ge) +
        (w.ab * (fe * gab) + (w.a * w.b) * (fa * gb) + (w.a * w.b) * (fb * ga) +
          w.ab * (fab * ge)) := by
        rw [mul_add w.ab, mul_add w.ab, mul_add w.ab]
        gcongr
    _ ≤ (fe * ge + w.a * (fe * ga + fa * ge) + w.b * (fe * gb + fb * ge) +
        (w.ab * (fe * gab) + (w.a * w.b) * (fa * gb) + (w.a * w.b) * (fb * ga) +
          w.ab * (fab * ge))) + (w.a * fa * (w.a * ga) + w.a * fa * (w.ab * gab) +
          w.b * fb * (w.b * gb) + w.b * fb * (w.ab * gab) + w.ab * fab * (w.a * ga) +
          w.ab * fab * (w.b * gb) + w.ab * fab * (w.ab * gab)) := le_self_add
    _ = (fe + w.a * fa + w.b * fb + w.ab * fab) * (ge + w.a * ga + w.b * gb + w.ab * gab) := by
        ring

/-- **The `SNorm` with sources**: `F ↦ ‖F_∅‖ + w_a ‖F_a‖ + w_b ‖F_b‖ + w_ab ‖F_ab‖`. -/
def oSN (hn : NrmP nrm) (w : Wt) (hw : w.Sub) : Obs.Gen.SNorm (OE c X) where
  nrm F := oNorm nrm w (F : SA c X)
  zero := oNorm_zero' hn
  add F G := oNorm_add_le' hn (F : SA c X) G
  neg F := oNorm_neg' hn (F : SA c X)
  mul F G := oNorm_mul_le' hn hw F G
  one := oNorm_one_le' hn

theorem oSN_nrm (hn : NrmP nrm) (w : Wt) (hw : w.Sub) (F : OE c X) :
    (oSN hn w hw).nrm F = oNorm nrm w (F : SA c X) := rfl

end

end Obs2
