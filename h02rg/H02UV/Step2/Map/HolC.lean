import Step2.Map.StepFinal
import Step2.Map.Hol

/-!
# Holomorphy of the step map in the covariance

For a covariance `e ↦ C(e)` whose entries are entire, and holomorphic families
`e ↦ (V(e), 𝒲(e), K(e))` with `ε(V(e)(B)) = 0`, the outputs `K_{j+1}` (`Kplus`), `𝒲_{j+1}`
(`Wnext2`) and `V_{j+1}` (`Vnext2`) are coefficient-wise holomorphic in `e` (`Kplus_holC`,
`Wnext2_holC`, `Vnext2_holC`). `𝔼_C` and `e^{ℒ_C}` are finite sums of powers of `ℒ_C`, which is
linear in `C` (`Hol.ECC_var`, `Hol.expLC_var`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Cf : E → Matrix Λ Λ ℂ} (hCf : ∀ x y, Differentiable ℂ (fun e => Cf e x y))

theorem LζC_pow_eq_zero (C : Matrix Λ Λ ℂ) : LζC C ^ (Nf (Λ ⊕ Λ) + 1) = 0 :=
  pow_eq_zero_of_degLe _
    (fun n x hx => by
      rw [LζC_apply]
      exact DegLe.sum _ fun a _ => DegLe.sum _ fun b _ => (DD_degLe hx _ _).smul _)
    fun x hx => by
      rw [LζC_apply]
      exact sum_eq_zero fun a _ => sum_eq_zero fun b _ => by
        rw [D_eq_zero_of_degLe_zero hx, map_zero, smul_zero]

include hCf in
theorem _root_.Step.Hol.LζC_var {f : E → Grassmann.N (Λ ⊕ Λ)} (hf : Hol f) :
    Hol (fun e => LζC (Cf e) (f e)) := by
  refine Hol.congr (f := fun e => ∑ x, ∑ y, Cf e x y •
    D (Sum.inr y, 1) (D (Sum.inr x, -1) (f e))) ?_ fun e => LζC_apply _ _
  exact Hol.sum _ fun x _ => Hol.sum _ fun y _ => Hol.smul (hCf x y) ((hf.map _).map _)

include hCf in
theorem _root_.Step.Hol.LζC_pow_var {f : E → Grassmann.N (Λ ⊕ Λ)} (hf : Hol f) (n : ℕ) :
    Hol (fun e => (LζC (Cf e) ^ n) (f e)) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    refine Hol.congr (Hol.LζC_var hCf ih) fun e => ?_
    rw [pow_succ', Module.End.mul_apply]

include hCf in
theorem _root_.Step.Hol.ECC_var {f : E → Grassmann.N (Λ ⊕ Λ)} (hf : Hol f) :
    Hol (fun e => ECC (Cf e) (f e)) := by
  refine Hol.congr (f := fun e => proj (∑ i ∈ range (Nf (Λ ⊕ Λ) + 1),
    ((i.factorial : ℂ)⁻¹) • (LζC (Cf e) ^ i) (f e))) ?_ fun e => ?_
  · exact (Hol.sum _ fun i _ => Hol.smul (differentiable_const _)
      (Hol.LζC_pow_var hCf hf i)).map proj.toLinearMap
  · rw [ECC, LinearMap.comp_apply, IsNilpotent.exp_eq_sum (LζC_pow_eq_zero (Cf e))]
    simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [← Rat.cast_smul_eq_qsmul ℂ]
    simp

include hCf in
theorem _root_.Step.HolE.ECCE_var {f : E → EvR (Λ ⊕ Λ)} (hf : HolE f) :
    HolE (fun e => ECCE (Cf e) (f e)) := Hol.ECC_var hCf hf

include hCf in
theorem _root_.Step.HolE.EthE_var {f : E → EvR Λ} (hf : HolE f) :
    HolE (fun e => EthE (Cf e) (f e)) := HolE.ECCE_var hCf hf.thetaE

include hCf in
theorem _root_.Step.Hol.expLC_var {f : E → Grassmann.N Λ} (hf : Hol f) :
    Hol (fun e => expLC (Cf e) (f e)) := by
  refine Hol.congr (f := fun e => ECC (Cf e) (theta (f e))) (Hol.ECC_var hCf (hf.map theta.toLinearMap))
    fun e => (ECC_theta _ _).symm

include hCf in
theorem _root_.Step.HolE.FCE_var {f g : E → EvR Λ} (hf : HolE f) (hg : HolE g) :
    HolE (fun e => FCE (Cf e) (f e) (g e)) := by
  have hCn : ∀ x y, Differentiable ℂ (fun e => (-Cf e) x y) := fun x y => (hCf x y).neg
  unfold HolE
  simp only [coe_FCE, FC]
  exact Hol.sub (Hol.expLC_var hCf (Hol.mul (Hol.expLC_var hCn hf) (Hol.expLC_var hCn hg)))
    (Hol.mul hf hg)

end Gen

variable {d L N : ℕ} [NeZero L]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Map

variable (j : ℕ) {Cf : E → Matrix (Lam d L N) (Lam d L N) ℂ} {Vf Wf : E → Fam d L N}
  {Kf : E → Act d L N} (hCf : ∀ x y, Differentiable ℂ (fun e => Cf e x y))
  (hVf : ∀ b, HolE (fun e => Vf e b)) (hWf : ∀ b, HolE (fun e => Wf e b))
  (hKf : ∀ X, HolE (fun e => Kf e X))

include hCf hVf in
theorem Vpr_holC (b : Fin d → ℕ) : HolE (fun e => Vpr (Cf e) (Vf e) b) := (hVf b).EthE_var hCf

include hCf hVf in
theorem VprL_holC : HolE (fun e => VprL j (Cf e) (Vf e)) :=
  HolE.sum _ fun b _ => Vpr_holC hCf hVf b

include hCf hVf hWf in
theorem Sb_holC (b : Fin d → ℕ) : HolE (fun e => Sb j (Cf e) (Vf e) (Wf e) b) :=
  HolE.add (HolE.smul (differentiable_const _)
    (HolE.FCE_var hCf (Vpr_holC hCf hVf b) (VprL_holC j hCf hVf))) ((hWf b).EthE_var hCf)

include hCf hVf hWf in
theorem SX_holC (X : Finset (Lam d L N)) : HolE (fun e => SX j (Cf e) (Vf e) (Wf e) X) :=
  HolE.sum _ fun b _ => Sb_holC j hCf hVf hWf b

include hCf hVf hWf in
theorem LS_holC (b : Fin d → ℕ) : HolE (fun e => LS j (Cf e) (Vf e) (Wf e) b) :=
  HolE.Loc2E _ _ (SX_holC j hCf hVf hWf _)

include hCf hVf hWf hKf in
theorem uVp_holC (b : Fin d → ℕ) : HolE (fun e => uVp j (Cf e) (Vf e) (Wf e) (Kf e) b) :=
  ((Vpr_holC hCf hVf b).sub ((Q2_hol j hKf b).EthE_var hCf)).sub (LS_holC j hCf hVf hWf b)

include hCf hVf hWf hKf in
theorem up_diffC (b : Fin d → ℕ) :
    Differentiable ℂ (fun e => up j (Cf e) (Vf e) (Wf e) (Kf e) b) :=
  (uVp_holC j hCf hVf hWf hKf b).ε

include hCf hVf hWf hKf in
theorem Vp_holC (b : Fin d → ℕ) : HolE (fun e => Vp j (Cf e) (Vf e) (Wf e) (Kf e) b) :=
  (uVp_holC j hCf hVf hWf hKf b).sub (HolE.algMap (up_diffC j hCf hVf hWf hKf b))

include hCf hVf hWf in
theorem Wp_holC (b : Fin d → ℕ) : HolE (fun e => Wp j (Cf e) (Vf e) (Wf e) b) :=
  (Sb_holC j hCf hVf hWf b).sub (LS_holC j hCf hVf hWf b)

include hCf hVf hWf hKf in
theorem Ip_holC (b : Fin d → ℕ) : HolE (fun e => Ip j (Cf e) (Vf e) (Wf e) (Kf e) b) :=
  HolE.smul ((up_diffC j hCf hVf hWf hKf b).neg.cexp)
    (((Vp_holC j hCf hVf hWf hKf b).neg.gexp fun e => by
      rw [NegMemClass.coe_neg, map_neg, ε_Vp, neg_zero]).mul
      ((HolE.const 1).add (Wp_holC j hCf hVf hWf b)))

include hCf hVf hWf hKf in
theorem Gp_holC (b : Fin d → ℕ) : HolE (fun e => Gp j (Cf e) (Vf e) (Wf e) (Kf e) b) :=
  ((Vp_holC j hCf hVf hWf hKf b).neg.gexp fun e => by
      rw [NegMemClass.coe_neg, map_neg, ε_Vp, neg_zero]).mul
    ((HolE.const 1).add (Wp_holC j hCf hVf hWf b))

include hCf hVf hWf hKf in
theorem uX_diffC (X : Finset (Lam d L N)) :
    Differentiable ℂ (fun e => uX j (Cf e) (Vf e) (Wf e) (Kf e) X) :=
  Differentiable.fun_sum fun b _ => up_diffC j hCf hVf hWf hKf b

include hCf hKf in
/-- A covariance-dependent version of `gKnext_hol`. -/
theorem gKnext_holC {Ibf Ipf : E → (Fin d → ℕ) → EvR (Lam d L N)}
    {Jf : E → (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)}
    (hIb : ∀ b, HolE (fun e => Ibf e b)) (hIp : ∀ b, HolE (fun e => Ipf e b))
    (hJ : ∀ b X, HolE (fun e => Jf e b X)) (U : Finset (Lam d L N)) :
    HolE (fun e => gKnext j (Cf e) (Ibf e) (Ipf e) (Kf e) (Jf e) U) :=
  HolE.sum _ fun _ _ => (HolE.prod _ fun b _ => hIp b).mul
    (HolE.ECCE_var hCf ((gKchk_hol j hKf hIb hIp hJ _).mul
      (HolE.prod _ fun p _ => (hJ p.1 p.2).thetaE)))

include hCf hVf hWf hKf in
theorem Knext2_holC (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    HolE (fun e => Knext2 j (Cf e) (Vf e) (Wf e) (Kf e) U) :=
  HolE.smul (uX_diffC j hCf hVf hWf hKf U).cexp
    (gKnext_holC j hCf hKf (Ib_hol hVf hWf hV0) (Ip_holC j hCf hVf hWf hKf) (J2_hol j hKf) U)

include hCf hVf in
theorem k2_holC (X : Finset (Lam d L N)) : HolE (fun e => k2 j (Cf e) (Vf e) X) := by
  unfold k2
  split_ifs
  · exact HolE.sum _ fun b _ => HolE.smul (differentiable_const _)
      (HolE.FCE_var hCf (Vpr_holC hCf hVf b) ((VprL_holC j hCf hVf).sub (Vpr_holC hCf hVf b)))
  · exact HolE.smul (differentiable_const _) (HolE.sum _ fun b _ => HolE.sum _ fun b' _ =>
      HolE.FCE_var hCf (Vpr_holC hCf hVf b) (Vpr_holC hCf hVf b'))
  · exact HolE.const 0

include hCf hVf in
theorem K2_holC (U : Finset (Lam d L N)) : HolE (fun e => K2 j (Cf e) (Vf e) U) :=
  HolE.sum _ fun X _ => k2_holC j hCf hVf X

include hCf hVf hWf hKf in
theorem Knew_holC (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    HolE (fun e => Knew j (Cf e) (Vf e) (Wf e) (Kf e) U) :=
  (Knext2_holC j hCf hVf hWf hKf hV0 U).sub
    ((HolE.prod _ fun b _ => Gp_holC j hCf hVf hWf hKf b).mul (K2_holC j hCf hVf U))

include hCf hVf hWf hKf in
theorem It_holC (c : Fin d → ℕ) : HolE (fun e => It j (Cf e) (Vf e) (Wf e) (Kf e) c) :=
  HolE.prod _ fun b _ => Gp_holC j hCf hVf hWf hKf b

include hCf hVf in
theorem kap_holC (X : Finset (Lam d L N)) (c : Fin d → ℕ) :
    HolE (fun e => kap j (Cf e) (Vf e) X c) := by
  unfold kap
  split_ifs
  · exact HolE.sum _ fun b _ => HolE.smul (differentiable_const _)
      (HolE.FCE_var hCf (Vpr_holC hCf hVf b) ((VprL_holC j hCf hVf).sub (Vpr_holC hCf hVf b)))
  · exact HolE.smul (differentiable_const _) (HolE.sum _ fun b _ => HolE.sum _ fun b' _ =>
      HolE.FCE_var hCf (Vpr_holC hCf hVf b) (Vpr_holC hCf hVf b'))
  · exact HolE.const 0

include hCf hVf in
theorem Jh_holC (c : Fin d → ℕ) (U : Finset (Lam d L N)) :
    HolE (fun e => Jh j (Cf e) (Vf e) c U) := by
  unfold Jh
  split_ifs
  · exact HolE.sum _ fun X _ => kap_holC j hCf hVf X c
  · exact HolE.const 0

/-- Holomorphy of `K_out` in its data. -/
theorem Kout_hol (k : ℕ) {If : E → (Fin d → ℕ) → EvR (Lam d L N)} {Mf : E → Act d L N}
    {Jf : E → (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)}
    (hI : ∀ b, HolE (fun e => If e b)) (hM : ∀ X, HolE (fun e => Mf e X))
    (hJ : ∀ b X, HolE (fun e => Jf e b X)) (W : Finset (Lam d L N)) :
    HolE (fun e => Kout k (If e) (Mf e) (Jf e) W) :=
  HolE.sum _ fun g _ => (HolE.prod _ fun b _ => hI b).mul ((Kext_hol k hM g.2).mul
    (HolE.prod _ fun p _ => (HolE.prod _ fun b _ => hI b).mul (hJ p.1 p.2)))

include hCf hVf hWf hKf in
/-- **Holomorphy of `K_{j+1}` in `(C, V, 𝒲, K)`.** -/
theorem Kplus_holC (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    HolE (fun e => Kplus j (Cf e) (Vf e) (Wf e) (Kf e) U) :=
  Kout_hol (j + 1) (It_holC j hCf hVf hWf hKf) (Knew_holC j hCf hVf hWf hKf hV0)
    (Jh_holC j hCf hVf) U

include hCf hVf hWf in
theorem Wnext2_holC (c : Fin d → ℕ) : HolE (fun e => Wnext2 j (Cf e) (Vf e) (Wf e) c) :=
  (HolE.prod _ fun b _ => (HolE.const 1).add (Wp_holC j hCf hVf hWf b)).sub (HolE.const 1)

include hCf hVf hWf hKf in
theorem Vnext2_holC (c : Fin d → ℕ) : HolE (fun e => Vnext2 j (Cf e) (Vf e) (Wf e) (Kf e) c) :=
  HolE.sum _ fun b _ => Vp_holC j hCf hVf hWf hKf b

end Map

end

end Step2
