import Step2.Map.Block

/-!
# Holomorphy of the second-order map

For holomorphic families `e ↦ (V(e), 𝒲(e), K(e))` (coefficient-wise, `HolE`) with
`ε(V(e)(B)) = 0`, the map `e ↦ K_{j+1}(U)` of `Step2.Map.Defs` is coefficient-wise holomorphic
(`Knext2_hol`). Every ingredient is a fixed linear or bilinear map (`𝔼θ`, `F_C`, `Loc`, `ε`), a
product, or an exponential.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem _root_.Step.HolE.EthE (C : Matrix Λ Λ ℂ) {f : E → EvR Λ} (hf : HolE f) :
    HolE (fun e => Step2.EthE C (f e)) :=
  hf.thetaE.map (ECCE C)

theorem _root_.Step.HolE.FCE (C : Matrix Λ Λ ℂ) {f g : E → EvR Λ} (hf : HolE f) (hg : HolE g) :
    HolE (fun e => Step2.FCE C (f e) (g e)) := by
  unfold HolE
  simp only [coe_FCE, FC]
  exact Hol.sub (Hol.map (Hol.mul (Hol.map hf _) (Hol.map hg _)) _) (Hol.mul hf hg)

theorem _root_.Step.HolE.ε {f : E → EvR Λ} (hf : HolE f) :
    Differentiable ℂ (fun e => Grassmann.ε (f e : Grassmann.N Λ)) :=
  Hol.lin hf (Grassmann.ε (Λ := Λ)).toLinearMap

theorem _root_.Step.HolE.algMap {c : E → ℂ} (hc : Differentiable ℂ c) :
    HolE (fun e => (algebraMap ℂ (EvR Λ) (c e))) := by
  refine Hol.congr (HolE.smul hc (HolE.const (1 : EvR Λ))) fun e => ?_
  simp only [Algebra.algebraMap_eq_smul_one]

end Gen

variable {d L N : ℕ} [NeZero L]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `Loc_{X,Y}` as a linear map on even elements. -/
def Loc2EL (X Y : Finset (Lam d L N)) : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N) where
  toFun := Loc2E X Y
  map_add' := Loc2E_add X Y
  map_smul' c F := Loc2E_smul X Y c F

theorem _root_.Step.HolE.Loc2E (X Y : Finset (Lam d L N)) {f : E → EvR (Lam d L N)} (hf : HolE f) :
    HolE (fun e => Step2.Loc2E X Y (f e)) :=
  hf.map (Loc2EL X Y)

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {Vf Wf : E → Fam d L N}
  {Kf : E → Act d L N} (hVf : ∀ b, HolE (fun e => Vf e b)) (hWf : ∀ b, HolE (fun e => Wf e b))
  (hKf : ∀ X, HolE (fun e => Kf e X))

include hVf in
theorem Vpr_hol (b : Fin d → ℕ) : HolE (fun e => Vpr C (Vf e) b) := (hVf b).EthE C

include hVf in
theorem VprL_hol : HolE (fun e => VprL j C (Vf e)) :=
  HolE.sum _ fun b _ => Vpr_hol C hVf b

include hVf hWf in
theorem Sb_hol (b : Fin d → ℕ) : HolE (fun e => Sb j C (Vf e) (Wf e) b) :=
  HolE.add (HolE.smul (differentiable_const _)
    (HolE.FCE C (Vpr_hol C hVf b) (VprL_hol j C hVf))) ((hWf b).EthE C)

include hVf hWf in
theorem SX_hol (X : Finset (Lam d L N)) : HolE (fun e => SX j C (Vf e) (Wf e) X) :=
  HolE.sum _ fun b _ => Sb_hol j C hVf hWf b

include hVf hWf in
theorem LS_hol (b : Fin d → ℕ) : HolE (fun e => LS j C (Vf e) (Wf e) b) :=
  HolE.Loc2E _ _ (SX_hol j C hVf hWf _)

include hKf in
theorem Q2_hol (b : Fin d → ℕ) : HolE (fun e => Q2 j (Kf e) b) := by
  unfold Q2
  split_ifs
  · exact HolE.sum _ fun X _ => HolE.Loc2E _ _ (hKf X)
  · exact HolE.const 0

include hKf in
theorem J2_hol (b : Fin d → ℕ) (X : Finset (Lam d L N)) : HolE (fun e => J2 j (Kf e) b X) := by
  unfold J2
  split_ifs
  · exact (HolE.sum _ fun Y _ => HolE.Loc2E _ _ (hKf Y)).neg
  · exact HolE.Loc2E _ _ (hKf X)
  · exact HolE.const 0

include hVf hWf hKf in
theorem uVp_hol (b : Fin d → ℕ) : HolE (fun e => uVp j C (Vf e) (Wf e) (Kf e) b) :=
  ((Vpr_hol C hVf b).sub ((Q2_hol j hKf b).EthE C)).sub (LS_hol j C hVf hWf b)

include hVf hWf hKf in
theorem up_diff (b : Fin d → ℕ) : Differentiable ℂ (fun e => up j C (Vf e) (Wf e) (Kf e) b) :=
  (uVp_hol j C hVf hWf hKf b).ε

include hVf hWf hKf in
theorem Vp_hol (b : Fin d → ℕ) : HolE (fun e => Vp j C (Vf e) (Wf e) (Kf e) b) :=
  (uVp_hol j C hVf hWf hKf b).sub (HolE.algMap (up_diff j C hVf hWf hKf b))

include hVf hWf in
theorem Wp_hol (b : Fin d → ℕ) : HolE (fun e => Wp j C (Vf e) (Wf e) b) :=
  (Sb_hol j C hVf hWf b).sub (LS_hol j C hVf hWf b)

include hVf hWf in
theorem Ib_hol (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (b : Fin d → ℕ) :
    HolE (fun e => Ib (Vf e) (Wf e) b) :=
  ((hVf b).neg.gexp fun e => by rw [NegMemClass.coe_neg, map_neg, hV0, neg_zero]).mul
    ((HolE.const 1).add (hWf b))

include hVf hWf hKf in
theorem Ip_hol (b : Fin d → ℕ) : HolE (fun e => Ip j C (Vf e) (Wf e) (Kf e) b) :=
  HolE.smul ((up_diff j C hVf hWf hKf b).neg.cexp)
    (((Vp_hol j C hVf hWf hKf b).neg.gexp fun e => by
      rw [NegMemClass.coe_neg, map_neg, ε_Vp, neg_zero]).mul ((HolE.const 1).add (Wp_hol j C hVf hWf b)))

include hVf hWf hKf in
theorem uX_diff (X : Finset (Lam d L N)) :
    Differentiable ℂ (fun e => uX j C (Vf e) (Wf e) (Kf e) X) :=
  Differentiable.fun_sum fun b _ => up_diff j C hVf hWf hKf b

section GenMap

variable {Ibf Ipf : E → (Fin d → ℕ) → EvR (Lam d L N)}
  {Jf : E → (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)}
  (hIb : ∀ b, HolE (fun e => Ibf e b)) (hIp : ∀ b, HolE (fun e => Ipf e b))
  (hJ : ∀ b X, HolE (fun e => Jf e b X))

include hKf in
theorem Kext_hol (X : Finset (Lam d L N)) : HolE (fun e => Kext j (Kf e) X) :=
  HolE.prod _ fun W _ => hKf W

include hIb hIp in
theorem gdIPow_hol (X : Finset (Lam d L N)) : HolE (fun e => gdIPow j (Ibf e) (Ipf e) X) :=
  HolE.prod _ fun b _ => (hIb b).thetaE.sub (hIp b).inclE

include hIb hIp hKf hJ in
theorem gKchk_hol (X : Finset (Lam d L N)) :
    HolE (fun e => gKchk j (Ibf e) (Ipf e) (Kf e) (Jf e) X) :=
  HolE.prod _ fun W _ => HolE.sub (HolE.sum _ fun Y _ =>
    (Kext_hol j hKf _).thetaE.mul (gdIPow_hol j hIb hIp Y)) (HolE.sum _ fun b _ => (hJ b W).thetaE)

include hIb hIp hKf hJ in
theorem gKnext_hol (U : Finset (Lam d L N)) :
    HolE (fun e => gKnext j C (Ibf e) (Ipf e) (Kf e) (Jf e) U) :=
  HolE.sum _ fun _ _ => (HolE.prod _ fun b _ => hIp b).mul
    (((gKchk_hol j hKf hIb hIp hJ _).mul (HolE.prod _ fun p _ => (hJ p.1 p.2).thetaE)).map (ECCE C))

end GenMap

include hVf hWf hKf in
/-- **Holomorphy of `K_{j+1}`.** -/
theorem Knext2_hol (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    HolE (fun e => Knext2 j C (Vf e) (Wf e) (Kf e) U) :=
  HolE.smul (uX_diff j C hVf hWf hKf U).cexp
    (gKnext_hol j C hKf (Ib_hol hVf hWf hV0) (Ip_hol j C hVf hWf hKf) (J2_hol j hKf) U)

end Map

end

end Step2
