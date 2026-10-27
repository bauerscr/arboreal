import Obs2.Map.HolW
import Obs2.Map.Map

/-!
# Holomorphy of the second-order map with sources

The analogue of `Step2.Map.Hol` for the map with sources of `Obs2.Map.Map`, with the weak holomorphy
`HolW` on `OE c Λ` (every linear functional is differentiable; equivalently each component is
coefficient-wise holomorphic, `HolW.e`, `HolW.a`, …). For holomorphic families
`e ↦ (V(e), 𝒲(e), K(e))` with `ε(V(e)(B)_∅) = 0`, `e ↦ K_{j+1}(U)` is holomorphic
(`Knext2O_holW`), and so are `K^♯_{j+1}` and `K_{j+1}` after the change of variables
(`KnewO_holW`, `KplusO_holW`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Prim

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem HolW.thetaO {f : E → OE c Λ} (hf : HolW f) : HolW (fun e => Obs.thetaO (f e)) :=
  hf.map (Obs.thetaO (c := c) (Λ := Λ)).toLinearMap

theorem HolW.inclO {f : E → OE c Λ} (hf : HolW f) : HolW (fun e => Obs.inclO (f e)) :=
  hf.map (Obs.inclO (c := c) (Λ := Λ)).toLinearMap

theorem HolW.EthO (C : Matrix Λ Λ ℂ) {f : E → OE c Λ} (hf : HolW f) :
    HolW (fun e => Obs2.EthO C (f e)) :=
  hf.map (EthOL C)

theorem HolW.FCO (C : Matrix Λ Λ ℂ) {f g : E → OE c Λ} (hf : HolW f) (hg : HolW g) :
    HolW (fun e => Obs2.FCO C (f e) (g e)) :=
  (((hf.map (expO (-C))).mul (hg.map (expO (-C)))).map (expO C)).sub (hf.mul hg)

theorem HolW.πobs {f : E → OE c Λ} (hf : HolW f) : HolW (fun e => Obs.πobs (f e)) :=
  hf.map Obs.πobs

theorem HolW.epsO {f : E → OE c Λ} (hf : HolW f) : HolW (fun e => Obs.epsO (f e)) :=
  hf.map (Obs.epsO (c := c) (Λ := Λ)).toLinearMap

end Prim

theorem HolW.LocO2 (P : ObsPts d L N) (X Y : Finset (Lam d L N)) {f : E → OE c (Lam d L N)}
    (hf : HolW f) : HolW (fun e => Obs2.LocO2 P X Y (f e)) :=
  hf.map (Obs2.LocO2 P X Y)

section Map

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  {Vf Wf : E → OFam c d L N} {Kf : E → OAct c d L N}
  (hVf : ∀ b, HolW (fun e => Vf e b)) (hWf : ∀ b, HolW (fun e => Wf e b))
  (hKf : ∀ X, HolW (fun e => Kf e X))

include hVf in
theorem VprO_holW (b : Fin d → ℕ) : HolW (fun e => VprO C (Vf e) b) := (hVf b).EthO C

include hVf in
theorem VprLO_holW : HolW (fun e => VprLO j C (Vf e)) :=
  HolW.sum _ fun b _ => VprO_holW C hVf b

include hVf in
theorem SCorO_holW (b : Fin d → ℕ) : HolW (fun e => SCorO j C (Vf e) b) :=
  HolW.smul (differentiable_const _)
    ((HolW.FCO C (VprO_holW C hVf b).πobs (VprLO_holW j C hVf)).sub
      (HolW.FCO C (VprO_holW C hVf b) (VprLO_holW j C hVf).πobs))

include hVf hWf in
theorem SbO_holW (b : Fin d → ℕ) : HolW (fun e => SbO j C (Vf e) (Wf e) b) :=
  ((HolW.smul (differentiable_const _)
    (HolW.FCO C (VprO_holW C hVf b) (VprLO_holW j C hVf))).add (SCorO_holW j C hVf b)).add
    ((hWf b).EthO C)

include hVf hWf in
theorem SXO_holW (X : Finset (Lam d L N)) : HolW (fun e => SXO j C (Vf e) (Wf e) X) :=
  HolW.sum _ fun b _ => SbO_holW j C hVf hWf b

include hVf hWf in
theorem LSO_holW (b : Fin d → ℕ) : HolW (fun e => LSO P j C (Vf e) (Wf e) b) :=
  (SXO_holW j C hVf hWf _).LocO2 P _ _

include hKf in
theorem Q2O_holW (b : Fin d → ℕ) : HolW (fun e => Q2O P j (Kf e) b) := by
  unfold Q2O
  split_ifs
  · exact HolW.sum _ fun X _ => (hKf X).LocO2 P _ _
  · exact HolW.const 0

include hKf in
theorem J2O_holW (b : Fin d → ℕ) (X : Finset (Lam d L N)) : HolW (fun e => J2O P j (Kf e) b X) := by
  unfold J2O
  split_ifs
  · exact (HolW.sum _ fun Y _ => (hKf Y).LocO2 P _ _).neg
  · exact (hKf X).LocO2 P _ _
  · exact HolW.const 0

include hVf hWf hKf in
theorem uVpO_holW (b : Fin d → ℕ) : HolW (fun e => uVpO P j C (Vf e) (Wf e) (Kf e) b) :=
  ((VprO_holW C hVf b).sub ((Q2O_holW P j hKf b).EthO C)).sub (LSO_holW P j C hVf hWf b)

include hVf hWf hKf in
theorem upB_diff (b : Fin d → ℕ) : Differentiable ℂ (fun e => upB P j C (Vf e) (Wf e) (Kf e) b) :=
  (uVpO_holW P j C hVf hWf hKf b).eps_e

include hVf hWf hKf in
theorem upO_holW (b : Fin d → ℕ) : HolW (fun e => upO P j C (Vf e) (Wf e) (Kf e) b) :=
  (uVpO_holW P j C hVf hWf hKf b).epsO.πobs

include hVf hWf hKf in
theorem VpO_holW (b : Fin d → ℕ) : HolW (fun e => VpO P j C (Vf e) (Wf e) (Kf e) b) :=
  ((uVpO_holW P j C hVf hWf hKf b).sub (HolW.algMap (upB_diff P j C hVf hWf hKf b))).sub
    (upO_holW P j C hVf hWf hKf b)

include hVf hWf in
theorem WpO_holW (b : Fin d → ℕ) : HolW (fun e => WpO P j C (Vf e) (Wf e) b) :=
  (SbO_holW j C hVf hWf b).sub (LSO_holW P j C hVf hWf b)

theorem eps_VpO (V W : OFam c d L N) (K : OAct c d L N) (b : Fin d → ℕ) :
    ε ((VpO P j C V W K b : SA c (Lam d L N)).e) = 0 := by
  rw [← coe_bulk, bulk_VpO]; exact Step2.ε_Vp j C _ _ _ b

theorem eps_neg_upO (V W : OFam c d L N) (K : OAct c d L N) (b : Fin d → ℕ) :
    ε ((-upO P j C V W K b : OE c (Lam d L N)) : SA c (Lam d L N)).e = 0 :=
  ε_bulk_eq_zero_of_obs (by rw [map_neg, bulk_upO, neg_zero])

theorem eps_uXO (V W : OFam c d L N) (K : OAct c d L N) (X : Finset (Lam d L N)) :
    ε ((uXO P j C V W K X : SA c (Lam d L N)).e) = 0 :=
  ε_bulk_eq_zero_of_obs (bulk_uXO P j C V W K X)

include hVf hWf in
theorem IbO_holW (hV0 : ∀ e b, ε ((Vf e b : SA c (Lam d L N)).e) = 0) (b : Fin d → ℕ) :
    HolW (fun e => IbO (Vf e) (Wf e) b) :=
  ((hVf b).neg.oexp fun e => by
    show ε (-(Vf e b : SA c (Lam d L N))).e = 0
    rw [neg_e, map_neg, hV0, neg_zero]).mul ((HolW.const 1).add (hWf b))

include hVf hWf hKf in
theorem GpO_holW (b : Fin d → ℕ) : HolW (fun e => GpO P j C (Vf e) (Wf e) (Kf e) b) :=
  ((VpO_holW P j C hVf hWf hKf b).neg.oexp fun e => by
    show ε (-(VpO P j C (Vf e) (Wf e) (Kf e) b : SA c (Lam d L N))).e = 0
    rw [neg_e, map_neg, eps_VpO, neg_zero]).mul ((HolW.const 1).add (WpO_holW P j C hVf hWf b))

include hVf hWf hKf in
theorem IpO_holW (b : Fin d → ℕ) : HolW (fun e => IpO P j C (Vf e) (Wf e) (Kf e) b) :=
  (HolW.expU (upB_diff P j C hVf hWf hKf b).neg (upO_holW P j C hVf hWf hKf b).neg
    fun e => eps_neg_upO P j C _ _ _ b).mul (GpO_holW P j C hVf hWf hKf b)

include hVf hWf hKf in
theorem uXB_diff (X : Finset (Lam d L N)) :
    Differentiable ℂ (fun e => uXB P j C (Vf e) (Wf e) (Kf e) X) :=
  Differentiable.fun_sum fun b _ => upB_diff P j C hVf hWf hKf b

include hVf hWf hKf in
theorem uXO_holW (X : Finset (Lam d L N)) : HolW (fun e => uXO P j C (Vf e) (Wf e) (Kf e) X) :=
  HolW.sum _ fun b _ => upO_holW P j C hVf hWf hKf b

section GenMap

variable {Ibf Ipf : E → OFam c d L N}
  {Jf : E → (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)}
  (hIb : ∀ b, HolW (fun e => Ibf e b)) (hIp : ∀ b, HolW (fun e => Ipf e b))
  (hJ : ∀ b X, HolW (fun e => Jf e b X))

include hKf in
theorem KextO_holW (X : Finset (Lam d L N)) : HolW (fun e => KextO j (Kf e) X) :=
  HolW.prod _ fun W _ => hKf W

include hIp in
theorem bpowO_holW (X : Finset (Lam d L N)) : HolW (fun e => bpowO j (Ipf e) X) :=
  HolW.prod _ fun b _ => hIp b

include hIb hIp in
theorem gdIPowO_holW (X : Finset (Lam d L N)) : HolW (fun e => gdIPowO j (Ibf e) (Ipf e) X) :=
  HolW.prod _ fun b _ => (hIb b).thetaO.sub (hIp b).inclO

include hIb hIp hKf hJ in
theorem gKchkO_holW (X : Finset (Lam d L N)) :
    HolW (fun e => gKchkO j (Ibf e) (Ipf e) (Kf e) (Jf e) X) :=
  HolW.prod _ fun W _ => HolW.sub (HolW.sum _ fun Y _ =>
    (KextO_holW j hKf _).thetaO.mul (gdIPowO_holW j hIb hIp Y)) (HolW.sum _ fun b _ => (hJ b W).thetaO)

include hIb hIp hKf hJ in
theorem gKnextO_holW (U : Finset (Lam d L N)) :
    HolW (fun e => gKnextO j C (Ibf e) (Ipf e) (Kf e) (Jf e) U) :=
  HolW.sum _ fun _ _ => (bpowO_holW j hIp _).mul
    (((gKchkO_holW j hKf hIb hIp hJ _).mul
      (HolW.prod _ fun p _ => (hJ p.1 p.2).thetaO)).map (ECCO C))

end GenMap

include hVf hWf hKf in
/-- **Holomorphy of `K_{j+1}` with sources.** -/
theorem Knext2O_holW (hV0 : ∀ e b, ε ((Vf e b : SA c (Lam d L N)).e) = 0) (U : Finset (Lam d L N)) :
    HolW (fun e => Knext2O P j C (Vf e) (Wf e) (Kf e) U) :=
  (HolW.expU (uXB_diff P j C hVf hWf hKf U) (uXO_holW P j C hVf hWf hKf U)
    fun e => eps_uXO P j C _ _ _ U).mul
    (gKnextO_holW j C hKf (IbO_holW hVf hWf hV0) (IpO_holW P j C hVf hWf hKf)
      (J2O_holW P j hKf) U)

/-! ### `K^{(2)}`, `K^♯` and `K_{j+1}` after the change of variables -/

include hVf in
theorem k2O_holW (X : Finset (Lam d L N)) : HolW (fun e => k2O j C (Vf e) X) := by
  unfold k2O
  split_ifs
  · exact HolW.sum _ fun b _ => (HolW.smul (differentiable_const _)
      (HolW.FCO C (VprO_holW C hVf b) ((VprLO_holW j C hVf).sub (VprO_holW C hVf b)))).sub
      (SCorO_holW j C hVf b)
  · exact HolW.smul (differentiable_const _) (HolW.sum _ fun b _ => HolW.sum _ fun b' _ =>
      HolW.FCO C (VprO_holW C hVf b) (VprO_holW C hVf b'))
  · exact HolW.const 0

include hVf in
theorem K2O_holW (U : Finset (Lam d L N)) : HolW (fun e => K2O j C (Vf e) U) :=
  HolW.sum _ fun X _ => k2O_holW j C hVf X

include hVf hWf hKf in
theorem KnewO_holW (hV0 : ∀ e b, ε ((Vf e b : SA c (Lam d L N)).e) = 0) (U : Finset (Lam d L N)) :
    HolW (fun e => KnewO P j C (Vf e) (Wf e) (Kf e) U) :=
  (Knext2O_holW P j C hVf hWf hKf hV0 U).sub
    ((bpowO_holW j (GpO_holW P j C hVf hWf hKf) U).mul (K2O_holW j C hVf U))

include hVf hWf hKf in
theorem ItO_holW (c' : Fin d → ℕ) : HolW (fun e => ItO P j C (Vf e) (Wf e) (Kf e) c') :=
  bpowO_holW j (GpO_holW P j C hVf hWf hKf) _

include hVf in
theorem kapO_holW (X : Finset (Lam d L N)) (c' : Fin d → ℕ) :
    HolW (fun e => kapO j C (Vf e) X c') := by
  unfold kapO
  split_ifs
  · exact HolW.sum _ fun b _ => (HolW.smul (differentiable_const _)
      (HolW.FCO C (VprO_holW C hVf b) ((VprLO_holW j C hVf).sub (VprO_holW C hVf b)))).sub
      (SCorO_holW j C hVf b)
  · exact HolW.smul (differentiable_const _) (HolW.sum _ fun b _ => HolW.sum _ fun b' _ =>
      (HolW.FCO C (VprO_holW C hVf b) (VprO_holW C hVf b')).add
        ((HolW.FCO C (VprO_holW C hVf b).πobs (VprO_holW C hVf b')).sub
          (HolW.FCO C (VprO_holW C hVf b) (VprO_holW C hVf b').πobs)))
  · exact HolW.const 0

include hVf in
theorem JhO_holW (c' : Fin d → ℕ) (U : Finset (Lam d L N)) : HolW (fun e => JhO j C (Vf e) c' U) := by
  unfold JhO
  split_ifs
  · exact HolW.sum _ fun X _ => kapO_holW j C hVf X c'
  · exact HolW.const 0

theorem KoutO_holW (k : ℕ) {If : E → OFam c d L N} {Mf : E → OAct c d L N}
    {Jf : E → (Fin d → ℕ) → Finset (Lam d L N) → OE c (Lam d L N)}
    (hI : ∀ b, HolW (fun e => If e b)) (hM : ∀ X, HolW (fun e => Mf e X))
    (hJ : ∀ b X, HolW (fun e => Jf e b X)) (W : Finset (Lam d L N)) :
    HolW (fun e => KoutO k (If e) (Mf e) (Jf e) W) :=
  HolW.sum _ fun g _ => (bpowO_holW k hI _).mul ((KextO_holW k hM _).mul
    (HolW.prod _ fun p _ => (bpowO_holW k hI _).mul (hJ p.1 p.2)))

include hVf hWf hKf in
/-- **Holomorphy of `K_{j+1}` with sources after the change of variables.** -/
theorem KplusO_holW (hV0 : ∀ e b, ε ((Vf e b : SA c (Lam d L N)).e) = 0) (U : Finset (Lam d L N)) :
    HolW (fun e => KplusO P j C (Vf e) (Wf e) (Kf e) U) :=
  KoutO_holW (j + 1) (ItO_holW P j C hVf hWf hKf) (KnewO_holW P j C hVf hWf hKf hV0)
    (JhO_holW j C hVf) U

end Map

end

end Obs2
