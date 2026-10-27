import Step2.FlowCont.FlowCont1

/-!
# Continuity of the RG flow data: the Grassmann part of one step

The outputs of one raw step that are Grassmann-valued (`κ = cvec4 (Vnext2 …)`, `WlinNext`,
`Dnext`, `Kconn (Kplus …)`) are polynomial in the covariance `C`, in the coupling vectors of
`V` and `Δ`, in the field rescaling `r` and in `(W^lin, x)`. We realise all of them as
coefficient-wise holomorphic functions on the finite-dimensional complex normed space
`E = (Λ → Λ → ℂ) × ℂ⁴ × ℂ⁴ × ℂ × BSp j × BSp j × ASp j` (`Step2.Map.HolC`), and compose with a
continuous map into `E` (`step_grass_cont`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holE_VfamL {v : E → Fin 4 → ℂ} (hv : Differentiable ℂ v) (k : ℕ) (b : Fin d → ℕ) :
    HolE (fun e => VfamL (L := L) (N := N) k (v e) b) :=
  HolE.comp (holE_of_linear ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin d → ℕ =>
    EvR (Lam d L N)) b).comp (VfamL (L := L) (N := N) k))) hv

theorem holE_sigE {r : E → ℂ} (hr : Differentiable ℂ r) {f : E → EvR (Lam d L N)}
    (hf : HolE f) : HolE (fun e => sigE (r e) (f e)) := fun n z => by
  simp only [coe_sigE, coeff_sig]
  exact (hr.pow n).mul (hf n z)

theorem holE_Kflat (j : ℕ) {Δf : E → Fam d L N} {Kf : E → Act d L N}
    (hΔ : ∀ b, HolE (fun e => Δf e b)) (hΔ0 : ∀ e b, ε (Δf e b : Alg d L N) = 0)
    (hK : ∀ X, HolE (fun e => Kf e X)) (Y : Finset (Lam d L N)) :
    HolE (fun e => Kflat j (Δf e) (Kf e) Y) := by
  unfold Kflat bpow
  exact (HolE.prod _ fun b _ => (hΔ b).gexp fun e => hΔ0 e b).mul (hK Y)

theorem holE_Kconn (k : ℕ) {Kf : E → Act d L N} (hK : ∀ X, HolE (fun e => Kf e X))
    (X : Finset (Lam d L N)) : HolE (fun e => Kconn k (Kf e) X) := by
  unfold Kconn
  split_ifs
  · exact hK X
  · exact HolE.const 0

variable {Cf : E → Matrix (Lam d L N) (Lam d L N) ℂ}
  (hCf : ∀ x y, Differentiable ℂ (fun e => Cf e x y))
include hCf

theorem holE_SrcF (i : ℕ) {Af Bf : E → Fam d L N} (hA : ∀ b, HolE (fun e => Af e b))
    (hB : ∀ b, HolE (fun e => Bf e b)) (b : Fin d → ℕ) :
    HolE (fun e => SrcF i (Cf e) (EthEL (Cf e)) (Af e) (Bf e) b) := by
  simp only [SrcF, EthEL_apply]
  exact HolE.smul (differentiable_const _) (HolE.FCE_var hCf ((hA b).EthE_var hCf)
    (HolE.sum _ fun b'' _ => (hB b'').EthE_var hCf))

theorem holE_WlinNext (j : ℕ) {Vf Wf : E → Fam d L N} (hV : ∀ b, HolE (fun e => Vf e b))
    (hW : ∀ b, HolE (fun e => Wf e b)) (c : Fin d → ℕ) :
    HolE (fun e => WlinNext j (Cf e) (Vf e) (Wf e) c) := by
  simp only [WlinNext, Pi.add_apply, SrcL_apply, SrcFam, TrL, LinearMap.coe_mk, AddHom.coe_mk]
  refine HolE.add (HolE.sum _ fun b _ => (holE_SrcF hCf j hV hV b).sub
      (HolE.Loc2E _ _ (HolE.sum _ fun b' _ => holE_SrcF hCf j hV hV b')))
    (HolE.sum _ fun b _ => ((holE_sigE (differentiable_const _) (hW b)).EthE_var hCf).sub
      (HolE.Loc2E _ _ (HolE.sum _ fun b' _ =>
        (holE_sigE (differentiable_const _) (hW b')).EthE_var hCf)))

theorem holE_Dnext (j : ℕ) {Vf Wf Df : E → Fam d L N} (hV : ∀ b, HolE (fun e => Vf e b))
    (hW : ∀ b, HolE (fun e => Wf e b)) (hD : ∀ b, HolE (fun e => Df e b)) (c : Fin d → ℕ) :
    HolE (fun e => Dnext j (Cf e) (Vf e) (Wf e) (Df e) c) :=
  (Wnext2_holC j hCf hV (fun b => (hW b).add (hD b)) c).sub (holE_WlinNext hCf j hV hW c)

end Gen

/-! ### The step on a finite-dimensional parameter space -/

section Step

variable {j : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)]

/-- An element of `BSp j ℓ` from an admissible family. -/
def BSp.mk' (F : Fam d L N) (h : F ∈ BSub (L := L) (N := N) j) : BSp d L N j ℓ := ⟨F, h⟩

omit [Fact (0 < ℓ)] [Fact (0 < A)] in
theorem BSp.toFam_mk' (F : Fam d L N) (h : F ∈ BSub (L := L) (N := N) j) :
    (BSp.mk' (ℓ := ℓ) F h).toFam = F := rfl

variable (d L N j ℓ A) in
/-- The parameter space of one step. -/
abbrev PE : Type _ := (Lam d L N → Lam d L N → ℂ) × (Fin 4 → ℂ) × (Fin 4 → ℂ) × ℂ ×
  BSp d L N j ℓ × BSp d L N j ℓ × ASp d L N j ℓ A

namespace PE

variable (e : PE d L N j ℓ A)

def C : Matrix (Lam d L N) (Lam d L N) ℂ := e.1
def V : Fam d L N := VfamL j e.2.1
def Wl : Fam d L N := e.2.2.2.2.1.toFam
def D : Fam d L N := sigF e.2.2.2.1 e.2.2.2.2.2.1.toFam
def K : Act d L N := Kflat j (VfamL j e.2.2.1) (sigK e.2.2.2.1 e.2.2.2.2.2.2.toAct)

variable (d L N j ℓ A) in
theorem hC : ∀ x y, Differentiable ℂ (fun e : PE d L N j ℓ A => C e x y) := fun x y => by
  unfold C; fun_prop

variable (d L N j ℓ A) in
theorem hV : ∀ b, HolE (fun e : PE d L N j ℓ A => V e b) := fun b =>
  holE_VfamL (by fun_prop) j b

omit [Fact (0 < ℓ)] [Fact (0 < A)] in
variable (d L N j ℓ A) in
theorem hV0 : ∀ (e : PE d L N j ℓ A) b, ε (V e b : Alg d L N) = 0 := fun _ b =>
  eps_VfamL j _ b

variable (d L N j ℓ A) in
theorem hWl : ∀ b, HolE (fun e : PE d L N j ℓ A => Wl e b) := fun b =>
  (BSp.holE_toFam b).comp (by fun_prop)

variable (d L N j ℓ A) in
theorem hD : ∀ b, HolE (fun e : PE d L N j ℓ A => D e b) := fun b =>
  holE_sigE (by fun_prop) ((BSp.holE_toFam b).comp (by fun_prop))

variable (d L N j ℓ A) in
theorem hW : ∀ b, HolE (fun e : PE d L N j ℓ A => (Wl e + D e) b) := fun b =>
  (hWl d L N j ℓ A b).add (hD d L N j ℓ A b)

variable (d L N j ℓ A) in
theorem hK : ∀ X, HolE (fun e : PE d L N j ℓ A => K e X) := fun X =>
  holE_Kflat j (fun b => holE_VfamL (by fun_prop) j b) (fun _ b => eps_VfamL j _ b)
    (fun Y => holE_sigE (by fun_prop) ((ASp.holE_toAct Y).comp (by fun_prop))) X

end PE

variable {T : Type*} [TopologicalSpace T]

variable {u : T → PE d L N j ℓ A} (hu : Continuous u)
include hu

theorem PE.cont_kappa (i₀ : Fin d) (a : Fin 4) : Continuous fun t =>
    cvec4 (blockSet (L := L) (N := N) (j + 1) 0) i₀
      (Vnext2 j (PE.C (u t)) (PE.V (u t)) (PE.Wl (u t) + PE.D (u t)) (PE.K (u t)) 0) a := by
  have h := (Hol.lin (Vnext2_holC j (PE.hC d L N j ℓ A) (PE.hV d L N j ℓ A) (PE.hW d L N j ℓ A)
    (PE.hK d L N j ℓ A) 0)
      ((LinearMap.proj a).comp (cvec4 (blockSet (L := L) (N := N) (j + 1) 0) i₀))).continuous.comp
      hu
  simp only [Function.comp_def, LinearMap.comp_apply, LinearMap.proj_apply] at h
  exact h

theorem PE.cont_Wl : CF fun t => WlinNext j (PE.C (u t)) (PE.V (u t)) (PE.Wl (u t)) :=
  fun b n z => ((holE_WlinNext (PE.hC d L N j ℓ A) j (PE.hV d L N j ℓ A) (PE.hWl d L N j ℓ A) b)
    n z).continuous.comp hu

theorem PE.cont_D : CF fun t => Dnext j (PE.C (u t)) (PE.V (u t)) (PE.Wl (u t)) (PE.D (u t)) :=
  fun b n z => ((holE_Dnext (PE.hC d L N j ℓ A) j (PE.hV d L N j ℓ A) (PE.hWl d L N j ℓ A)
    (PE.hD d L N j ℓ A) b) n z).continuous.comp hu

theorem PE.cont_K : CA fun t => Kconn (j + 1) (Kplus j (PE.C (u t)) (PE.V (u t))
    (PE.Wl (u t) + PE.D (u t)) (PE.K (u t))) :=
  fun X n z => ((holE_Kconn (j + 1) (Kplus_holC j (PE.hC d L N j ℓ A) (PE.hV d L N j ℓ A)
    (PE.hW d L N j ℓ A) (PE.hK d L N j ℓ A) (PE.hV0 d L N j ℓ A)) X) n z).continuous.comp hu

omit hu in
theorem PE.continuous_mk (C : T → Matrix (Lam d L N) (Lam d L N) ℂ)
    (hC : ∀ x y, Continuous fun t => C t x y) {v vΔ : T → Fin 4 → ℂ} (hv : Continuous v)
    (hvΔ : Continuous vΔ) {r : T → ℂ} (hr : Continuous r) {Wl : T → Fam d L N}
    (hWl : ∀ t, Wl t ∈ BSub (L := L) (N := N) j) (hWlc : CF Wl) {x1 : T → BSp d L N j ℓ}
    (hx1 : Continuous x1) {x2 : T → ASp d L N j ℓ A} (hx2 : Continuous x2) :
    Continuous (fun t => (((C t : Lam d L N → Lam d L N → ℂ), v t, vΔ t, r t,
      BSp.mk' (ℓ := ℓ) (Wl t) (hWl t), x1 t, x2 t) : PE d L N j ℓ A)) := by
  have hWc : Continuous fun t => BSp.mk' (ℓ := ℓ) (Wl t) (hWl t) :=
    (BSp.continuous_iff _).2 (by simpa only [BSp.toFam_mk'] using hWlc)
  exact (continuous_pi fun x => continuous_pi fun y => hC x y).prodMk
    (hv.prodMk (hvΔ.prodMk (hr.prodMk (hWc.prodMk (hx1.prodMk hx2)))))

end Step

end

end Step2
