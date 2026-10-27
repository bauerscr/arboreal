import Step.Structure
import Step.ExpNorm

/-!
# Coefficient-wise continuity of Grassmann-valued maps

A map `f : ℝ → 𝒩(I)` is *coefficient-wise continuous* on `S` (`CC S f`) if every coefficient
`m ↦ (f m)_z` is continuous on `S`.  Since every linear functional on `𝒩(I)` is a fixed linear
combination of the (finitely many) coefficients (`expand`), this class is closed under fixed
linear maps (`CC.map`), products (`CC.mul`), linear combinations with continuous scalars, the
operators `ℒ^ζ_{C(m)}` and `𝔼_{C(m)}` for continuous `C` (`CC.Lζ`, `CC.EC`), and the
exponential of even elements with vanishing constant term (`CCE.gexp`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

section CC

variable {I J : Type*} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J] {S : Set ℝ}

/-- Coefficient-wise continuity on `S`. -/
def CC (S : Set ℝ) (f : ℝ → Grassmann.N I) : Prop :=
  ∀ n (z : Fin n → Sf I), ContinuousOn (fun m => coeff (f m) z) S

/-- A linear map on `𝒩(I)` is determined by its values on the monomials. -/
theorem expand {M : Type*} [AddCommGroup M] [Module ℂ M] (ℓ : Grassmann.N I →ₗ[ℂ] M)
    (F : Grassmann.N I) :
    ℓ F = ∑ n ∈ range (Nf I + 1), ∑ z : Fin n → Sf I,
      ((n.factorial : ℂ)⁻¹ * coeff F z) • ℓ (psiPow z) := by
  conv_lhs => rw [sum_coeff F]
  simp only [map_sum, map_smul]

theorem CC.lin {f : ℝ → Grassmann.N I} (hf : CC S f) (ℓ : Grassmann.N I →ₗ[ℂ] ℂ) :
    ContinuousOn (fun m => ℓ (f m)) S := by
  refine ContinuousOn.congr ?_ (fun m _ => expand ℓ (f m))
  refine continuousOn_finsetSum _ fun n _ => continuousOn_finsetSum _ fun z _ => ?_
  simp only [smul_eq_mul]
  exact (continuousOn_const.mul (hf n z)).mul continuousOn_const

theorem CC.bilin {f : ℝ → Grassmann.N I} {g : ℝ → Grassmann.N J} (hf : CC S f) (hg : CC S g)
    (B : Grassmann.N I →ₗ[ℂ] Grassmann.N J →ₗ[ℂ] ℂ) :
    ContinuousOn (fun m => B (f m) (g m)) S := by
  refine ContinuousOn.congr ?_ (fun m _ => by rw [expand B (f m)])
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine continuousOn_finsetSum _ fun n _ => continuousOn_finsetSum _ fun z _ => ?_
  exact (continuousOn_const.mul (hf n z)).mul (hg.lin _)

theorem CC.map {f : ℝ → Grassmann.N I} (hf : CC S f) (T : Grassmann.N I →ₗ[ℂ] Grassmann.N J) :
    CC S (fun m => T (f m)) := fun _ z => hf.lin ((coeffL z).comp T)

theorem CC.const (F : Grassmann.N I) : CC S (fun _ => F) := fun _ _ => continuousOn_const

theorem CC.mul {f g : ℝ → Grassmann.N I} (hf : CC S f) (hg : CC S g) :
    CC S (fun m => f m * g m) := fun _ z =>
  hf.bilin hg ((LinearMap.mul ℂ (Grassmann.N I)).compr₂ (coeffL z))

theorem CC.add {f g : ℝ → Grassmann.N I} (hf : CC S f) (hg : CC S g) :
    CC S (fun m => f m + g m) := fun n z => by
  simp only [coeff_add]; exact (hf n z).add (hg n z)

theorem CC.smul {c : ℝ → ℂ} {f : ℝ → Grassmann.N I} (hc : ContinuousOn c S) (hf : CC S f) :
    CC S (fun m => c m • f m) := fun n z => by
  simp only [coeff_smul]; exact hc.mul (hf n z)

theorem CC.neg {f : ℝ → Grassmann.N I} (hf : CC S f) : CC S (fun m => -f m) := by
  have := hf.smul (c := fun _ => -1) continuousOn_const
  simpa using this

theorem CC.sub {f g : ℝ → Grassmann.N I} (hf : CC S f) (hg : CC S g) :
    CC S (fun m => f m - g m) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem CC.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → Grassmann.N I}
    (hf : ∀ i ∈ s, CC S (f i)) : CC S (fun m => ∑ i ∈ s, f i m) := fun n z => by
  simp only [coeff_sum]; exact continuousOn_finsetSum _ fun i hi => hf i hi n z

theorem CC.pow {f : ℝ → Grassmann.N I} (hf : CC S f) (k : ℕ) : CC S (fun m => f m ^ k) := by
  induction k with
  | zero => simpa using CC.const (S := S) (1 : Grassmann.N I)
  | succ k ih => simpa [pow_succ] using ih.mul hf

theorem CC.congr {f g : ℝ → Grassmann.N I} (hf : CC S f) (h : ∀ m ∈ S, g m = f m) : CC S g :=
  fun n z => (hf n z).congr fun m hm => by simp only [h m hm]

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem CC.lzeta {C : ℝ → Matrix Λ Λ ℝ} (hC : ∀ x y, ContinuousOn (fun m => C m x y) S)
    {f : ℝ → Grassmann.N (Λ ⊕ Λ)} (hf : CC S f) : CC S (fun m => Grassmann.Lζ (C m) (f m)) := by
  simp only [Lζ_apply]
  exact CC.sum _ fun x _ => CC.sum _ fun y _ => CC.smul (Complex.continuous_ofReal.comp_continuousOn (hC x y))
    ((hf.map _).map _)

theorem CC.lzeta_pow {C : ℝ → Matrix Λ Λ ℝ} (hC : ∀ x y, ContinuousOn (fun m => C m x y) S)
    {f : ℝ → Grassmann.N (Λ ⊕ Λ)} (hf : CC S f) (k : ℕ) :
    CC S (fun m => (Grassmann.Lζ (C m) ^ k) (f m)) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => simpa [pow_succ', Module.End.mul_apply] using CC.lzeta hC ih

theorem Lζ_pow_eq_zero (C : Matrix Λ Λ ℝ) : Lζ C ^ (Nf (Λ ⊕ Λ) + 1) = 0 := by
  refine pow_eq_zero_of_degLe _ (fun n x hx => ?_) fun x hx => ?_
  · rw [Lζ_apply]
    exact DegLe.sum _ fun a _ => DegLe.sum _ fun b _ => (DD_degLe hx _ _).smul _
  · rw [Lζ_apply]
    exact sum_eq_zero fun a _ => sum_eq_zero fun b _ => by
      rw [D_eq_zero_of_degLe_zero hx, map_zero, smul_zero]

theorem EC_eq_sum (C : Matrix Λ Λ ℝ) (F : Grassmann.N (Λ ⊕ Λ)) :
    EC C F = ∑ i ∈ range (Nf (Λ ⊕ Λ) + 1),
      ((i.factorial : ℂ)⁻¹) • proj ((Lζ C ^ i) F) := by
  rw [EC, LinearMap.comp_apply, IsNilpotent.exp_eq_sum (Lζ_pow_eq_zero C)]
  simp only [LinearMap.coe_sum, Finset.sum_apply, map_sum, AlgHom.toLinearMap_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, map_rat_smul proj, ← Rat.cast_smul_eq_qsmul ℂ]
  push_cast
  rfl

theorem CC.EC {C : ℝ → Matrix Λ Λ ℝ} (hC : ∀ x y, ContinuousOn (fun m => C m x y) S)
    {f : ℝ → Grassmann.N (Λ ⊕ Λ)} (hf : CC S f) : CC S (fun m => EC (C m) (f m)) := by
  simp only [EC_eq_sum]
  exact CC.sum _ fun i _ => CC.smul continuousOn_const ((CC.lzeta_pow hC hf i).map proj.toLinearMap)

/-! ### Even elements -/

/-- Coefficient-wise continuity of maps into the even subalgebra. -/
def CCE (S : Set ℝ) (f : ℝ → EvR I) : Prop := CC S (fun m => (f m : Grassmann.N I))

theorem CCE.const (F : EvR I) : CCE S (fun _ => F) := CC.const _

theorem CCE.mul {f g : ℝ → EvR I} (hf : CCE S f) (hg : CCE S g) : CCE S (fun m => f m * g m) :=
  CC.mul hf hg

theorem CCE.sub {f g : ℝ → EvR I} (hf : CCE S f) (hg : CCE S g) : CCE S (fun m => f m - g m) :=
  CC.sub hf hg

theorem CCE.neg {f : ℝ → EvR I} (hf : CCE S f) : CCE S (fun m => -f m) := CC.neg hf

theorem CCE.smul {c : ℝ → ℂ} {f : ℝ → EvR I} (hc : ContinuousOn c S) (hf : CCE S f) :
    CCE S (fun m => c m • f m) := CC.smul hc hf

theorem CCE.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → EvR I} (hf : ∀ i ∈ s, CCE S (f i)) :
    CCE S (fun m => ∑ i ∈ s, f i m) := by
  unfold CCE
  simp only [AddSubmonoidClass.coe_finsetSum]
  exact CC.sum s hf

theorem CCE.prod {ι : Type*} (s : Finset ι) {f : ι → ℝ → EvR I} (hf : ∀ i ∈ s, CCE S (f i)) :
    CCE S (fun m => ∏ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CCE.const (S := S) (1 : EvR I)
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem CCE.inclE {f : ℝ → EvR Λ} (hf : CCE S f) : CCE S (fun m => inclE (f m)) :=
  CC.map hf incl.toLinearMap

theorem CCE.ECE {C : ℝ → Matrix Λ Λ ℝ} (hC : ∀ x y, ContinuousOn (fun m => C m x y) S)
    {f : ℝ → EvR (Λ ⊕ Λ)} (hf : CCE S f) : CCE S (fun m => ECE (C m) (f m)) :=
  CC.EC hC hf

theorem CCE.gexp {f : ℝ → EvR I} (hf : CCE S f) (h0 : ∀ m ∈ S, ε (f m : Grassmann.N I) = 0) :
    CCE S (fun m => gexp (f m)) := by
  refine CC.congr (f := fun m => ∑ i ∈ range (Nf I + 1),
    ((i.factorial : ℂ)⁻¹) • (f m : Grassmann.N I) ^ i) ?_ fun m hm => ?_
  · exact CC.sum _ fun i _ => CC.smul continuousOn_const (CC.pow hf i)
  · exact coe_gexp (pow_eq_zero_of_ε' (h0 m hm) (Nat.lt_succ_self _))

end CC

end

end Step
