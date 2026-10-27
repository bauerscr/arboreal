import Obs2.Map.ExactStep
import Obs2.Map.HolO
import Step2.Last.LastNDefs

/-!
# The last step with sources without localisation: the reference map

At the last step `j + 1 = N` the map of `Obs2.Map.Map` contains `Loc_{Λ,B}S(Λ)`, and `Λ` is not a
small set at any scale `< N`: there is no bound of this localisation (the lifted coordinates of
`Loc` wrap around the torus). As `Step2.LastN` does for the bulk, we use the **reference map
without localisation** (no `Loc`, no `Q`, no `J`):

* `u'(B) = ε(V'_B)` (bulk `upBN`, observable `upON = π_obs ε(V'_B)`), `Y(B) = V'_B - u'(B)`;
* `G'(B) = e^{-Y(B)}(1 + S(B))` (`GpN`, `S(B) = SbO`, the sharp `S` of `Obs2.Map.Map`);
* `K'(U) = KNO U`: the generic polymer map `Obs.Gen.KnextG` with these block factors and `J = 0`.

Its bulk part is `Step2.LastN.KN` (`bulk_GpN`, `upBN_eq`). Results:

* **`stepN_ZVK`**, **`stepN_ZVK_last`**: `𝔼_Cθ Z_j = e^{-u'(Λ)} ∑_U G'^{Λ∖U} K'(U)`, and at the last
  scale `𝔼_Cθ Z_{N-1} = e^{-u'(Λ)}(∏_BG'(B) + K'(Λ))`;
* **`KNO_holW`**: holomorphy in holomorphic families of inputs.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD Obs.Gen

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

section RefMap

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N) (K : OAct c d L N)

/-- The bulk constant `u'^∅(B) = ε(V'_B)^∅` (no localisation). -/
def upBN (b : Fin d → ℕ) : ℂ := ε ((bulk (VprO C V b) : EvR (Lam d L N)) : Alg d L N)

/-- The observable constant `u'^{obs}(B) = π_obs ε(V'_B)`. -/
def upON (b : Fin d → ℕ) : OE c (Lam d L N) := πobs (epsO (VprO C V b))

/-- `Y(B) = V'_B - u'(B)`. -/
def YpN (b : Fin d → ℕ) : OE c (Lam d L N) :=
  VprO C V b - algebraMap ℂ _ (upBN C V b) - upON C V b

/-- `G'(B) = e^{-Y(B)}(1 + S(B))`. -/
def GpN (b : Fin d → ℕ) : OE c (Lam d L N) := oexp (-YpN C V b) * (1 + SbO j C V W b)

/-- The ingredients of the reference map. -/
def ingrN : RGIngr d L N (OE c (Lam d L N)) where
  I0 := IbO V W
  eV := GpN j C V W
  eu b := expU (upBN C V b) (upON C V b)
  eum b := expU (-upBN C V b) (-upON C V b)
  J _ _ := 0
  K := K

/-- **The reference activity `K'(U)`.** -/
def KNO (U : Finset (Lam d L N)) : OE c (Lam d L N) := KnextG (algO C) j (ingrN j C V W K) U

/-- `u'^∅(X)`. -/
def uXBN (X : Finset (Lam d L N)) : ℂ := ∑ b ∈ blocks j X, upBN C V b

/-- `u'^{obs}(X)`. -/
def uXON (X : Finset (Lam d L N)) : OE c (Lam d L N) := ∑ b ∈ blocks j X, upON C V b

theorem bulk_upON (b : Fin d → ℕ) : bulk (upON C V b) = 0 := bulk_πobs _

theorem bulk_uXON (X : Finset (Lam d L N)) : bulk (uXON j C V X) = 0 := by
  rw [uXON, map_sum]; exact sum_eq_zero fun b _ => bulk_upON C V b

theorem upBN_eq (b : Fin d → ℕ) : upBN C V b = Step2.LastN.upN C (bulkF V) b := rfl

theorem bulk_YpN (b : Fin d → ℕ) : bulk (YpN C V b) = Step2.LastN.VpN C (bulkF V) b := by
  rw [YpN, map_sub, map_sub, bulk_upON, sub_zero, AlgHom.commutes]; rfl

theorem eps_YpN (b : Fin d → ℕ) : ε ((YpN C V b : SA c (Lam d L N)).e) = 0 := by
  rw [← coe_bulk, bulk_YpN]; exact Step2.LastN.ε_VpN C _ b

theorem PrefG_ingrN (U : Finset (Lam d L N)) :
    PrefG j (ingrN j C V W K) U = expU (uXBN j C V U) (uXON j C V U) := by
  show ∏ b ∈ blocks j U, expU (upBN C V b) (upON C V b) = _
  exact prod_expU _ _ _ fun b _ => bulk_upON C V b

theorem bpow_eum_ingrN :
    bpow j (ingrN j C V W K).eum (univ : Finset (Lam d L N)) =
      expU (-uXBN j C V univ) (-uXON j C V univ) := by
  show ∏ b ∈ blocks j univ, expU (-upBN C V b) (-upON C V b) = _
  rw [prod_expU _ _ _ fun b _ => by rw [map_neg, bulk_upON, neg_zero], sum_neg_distrib,
    sum_neg_distrib]
  rfl

/-- **`prop:ZVK` for the reference map.** -/
theorem stepN_ZVK :
    ECCO C (thetaO (gZO j (IbO V W) K)) =
      expU (-uXBN j C V univ) (-uXON j C V univ) *
        ∑ U ∈ Pj (j + 1) (univ : Finset (Lam d L N)),
          bpowO j (GpN j C V W) (univ \ U) * KNO j C V W K U := by
  have h := ZVK_G (algO C) j (ingrN j C V W K) (fun a g => ECCO_inclO_mul C a g)
    (fun _ _ _ => rfl) (fun b _ => expU_mul_expU_neg _ (bulk_upON C V b))
  rw [ZnextG, bpow_eum_ingrN] at h
  exact h

theorem KNO_empty : KNO j C V W K ∅ = 1 :=
  KnextG_empty (algO C) j (ingrN j C V W K) (ECCO_one C)

/-- **The reference map at the last scale**: `𝔼_Cθ Z_{N-1} = e^{-u'(Λ)}(∏_BG'(B) + K'(Λ))`. -/
theorem stepN_ZVK_last (hj : j + 1 = N) :
    ECCO C (thetaO (gZO j (IbO V W) K)) =
      expU (-uXBN j C V univ) (-uXON j C V univ) *
        (bpowO j (GpN j C V W) univ + KNO j C V W K univ) := by
  rw [stepN_ZVK]
  congr 1
  subst hj
  have hne : (∅ : Finset (Lam d L (j + 1))) ≠ univ := fun h =>
    (univ_nonempty (α := Lam d L (j + 1))).ne_empty h.symm
  rw [Step2.LastN.Pj_top, sum_pair hne, KNO_empty, sdiff_empty, sdiff_self, mul_one]
  simp only [bpowO, blocks, Finset.bot_eq_empty, image_empty, prod_empty, one_mul]

set_option maxHeartbeats 4000000 in
/-- `K'(U) = e^{u'(U)} × (the generic polymer sum)` in the form of `Obs2.Map.gKnextO`. -/
theorem KNO_eq (U : Finset (Lam d L N)) :
    KNO j C V W K U = expU (uXBN j C V U) (uXON j C V U) *
      gKnextO j C (IbO V W) (fun b => expU (-upBN C V b) (-upON C V b) * GpN j C V W b) K
        (fun _ _ => 0) U := by
  show PrefG j (ingrN j C V W K) U * ∑ g ∈ Gset j U, KtermG (algO C) j (ingrN j C V W K) U g = _
  rw [PrefG_ingrN]
  congr 1

end RefMap

/-! ### Holomorphy -/

section Hol

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  {Vf Wf : E → OFam c d L N} {Kf : E → OAct c d L N}
  (hVf : ∀ b, HolW (fun e => Vf e b)) (hWf : ∀ b, HolW (fun e => Wf e b))
  (hKf : ∀ X, HolW (fun e => Kf e X))

include hVf in
theorem upBN_diff (b : Fin d → ℕ) : Differentiable ℂ (fun e => upBN C (Vf e) b) :=
  (VprO_holW C hVf b).eps_e

include hVf in
theorem upON_holW (b : Fin d → ℕ) : HolW (fun e => upON C (Vf e) b) :=
  (VprO_holW C hVf b).epsO.πobs

include hVf in
theorem YpN_holW (b : Fin d → ℕ) : HolW (fun e => YpN C (Vf e) b) :=
  ((VprO_holW C hVf b).sub (HolW.algMap (upBN_diff C hVf b))).sub (upON_holW C hVf b)

include hVf hWf in
theorem GpN_holW (b : Fin d → ℕ) : HolW (fun e => GpN j C (Vf e) (Wf e) b) :=
  ((YpN_holW C hVf b).neg.oexp fun e => by
    show ε (-(YpN C (Vf e) b : SA c (Lam d L N))).e = 0
    rw [neg_e, map_neg, eps_YpN, neg_zero]).mul ((HolW.const 1).add (SbO_holW j C hVf hWf b))

include hVf hWf hKf in
/-- **Holomorphy of the reference activity.** -/
theorem KNO_holW (hV0 : ∀ e b, ε ((Vf e b : SA c (Lam d L N)).e) = 0) (U : Finset (Lam d L N)) :
    HolW (fun e => KNO j C (Vf e) (Wf e) (Kf e) U) := by
  simp only [KNO_eq]
  refine (HolW.expU (Differentiable.fun_sum fun b _ => upBN_diff C hVf b)
    (HolW.sum _ fun b _ => upON_holW C hVf b) fun e => ?_).mul
    (gKnextO_holW j C hKf (IbO_holW hVf hWf hV0)
      (fun b => (HolW.expU (upBN_diff C hVf b).neg (upON_holW C hVf b).neg fun e =>
        ε_bulk_eq_zero_of_obs (by rw [map_neg, bulk_upON, neg_zero])).mul (GpN_holW j C hVf hWf b))
      (fun _ _ => HolW.const 0) U)
  exact ε_bulk_eq_zero_of_obs (bulk_uXON j C (Vf e) U)

end Hol

end

end Obs2
