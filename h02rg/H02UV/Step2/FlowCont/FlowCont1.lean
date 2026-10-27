import Step2.Map.RGMap
import Step2.Map.HolC

/-!
# Continuity of the RG flow data: generic tools

* `hol_of_linear`, `holE_of_linear`: a linear map from a finite-dimensional complex normed space
  into `𝒩(I)` (or its even part) is coefficient-wise holomorphic.
* `BSp.continuous_iff`, `ASp.continuous_iff`: a map into the finite-dimensional normed spaces
  `BSp j ℓ`, `ASp j ℓ A` is continuous iff all its Grassmann coefficients are.
* `continuous_clampDisk`: the radial clamp is continuous (for `r ≥ 0`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

/-! ### Linear maps are holomorphic -/

section Lin

variable {I : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem hol_of_linear (f : E →ₗ[ℂ] Grassmann.N I) : Hol (fun e => f e) := fun _ z => by
  have : (fun e => coeff (f e) z) = fun e => ((coeffL z).comp f) e := rfl
  rw [this]
  exact (LinearMap.toContinuousLinearMap ((coeffL z).comp f)).differentiable

theorem holE_of_linear (f : E →ₗ[ℂ] EvR I) : HolE (fun e => f e) :=
  hol_of_linear ((Ev I).val.toLinearMap.comp f)

end Lin

/-! ### The radial clamp -/

theorem clampDisk_eq_max {r : ℝ} (hr : 0 < r) (u : ℂ) :
    clampDisk r u = u * ((r / max r ‖u‖ : ℝ) : ℂ) := by
  rcases le_or_gt ‖u‖ r with h | h
  · rw [clampDisk_of_le h, max_eq_left h, div_self hr.ne', Complex.ofReal_one, mul_one]
  · unfold clampDisk
    rw [max_eq_right h.le, min_eq_right ((div_le_one (hr.trans h)).2 h.le)]

theorem continuous_clampDisk {r : ℝ} (hr : 0 ≤ r) : Continuous (clampDisk r) := by
  rcases hr.eq_or_lt with h0 | hpos
  · have : clampDisk r = fun _ => 0 := funext fun u => by
      unfold clampDisk; rw [← h0, zero_div, min_eq_right zero_le_one, Complex.ofReal_zero,
        mul_zero]
    rw [this]; exact continuous_const
  · have : clampDisk r = fun u => u * ((r / max r ‖u‖ : ℝ) : ℂ) :=
      funext (clampDisk_eq_max hpos)
    rw [this]
    refine continuous_id.mul (Complex.continuous_ofReal.comp
      (continuous_const.div (continuous_const.max continuous_norm) fun u => ?_))
    exact (hpos.trans_le (le_max_left _ _)).ne'

/-! ### Coefficient-wise continuity -/

variable {d L N : ℕ} [NeZero L]

/-- The Grassmann-coefficient map of block families. -/
def famCoefL : Fam d L N →ₗ[ℂ]
    ((Fin d → ℕ) × (Σ n : ℕ, Fin n → Sf (Lam d L N)) → ℂ) :=
  LinearMap.pi fun i => (coeffL i.2.2).comp ((Ev (Lam d L N)).val.toLinearMap.comp
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin d → ℕ => EvR (Lam d L N)) i.1))

theorem famCoefL_apply (F : Fam d L N) (i : (Fin d → ℕ) × (Σ n : ℕ, Fin n → Sf (Lam d L N))) :
    famCoefL F i = coeff ((F i.1 : EvR (Lam d L N)) : Alg d L N) i.2.2 := rfl

theorem famCoefL_injective : Function.Injective (famCoefL (d := d) (L := L) (N := N)) := by
  intro F G h
  funext b
  refine Subtype.ext ?_
  rw [sum_coeff (F b : Alg d L N), sum_coeff (G b : Alg d L N)]
  refine sum_congr rfl fun n _ => sum_congr rfl fun z _ => ?_
  have := congrFun h (b, ⟨n, z⟩)
  rw [famCoefL_apply, famCoefL_apply] at this
  rw [this]

/-- The Grassmann-coefficient map of activities. -/
def actCoefL : Act d L N →ₗ[ℂ]
    (Finset (Lam d L N) × (Σ n : ℕ, Fin n → Sf (Lam d L N)) → ℂ) :=
  LinearMap.pi fun i => (coeffL i.2.2).comp ((Ev (Lam d L N)).val.toLinearMap.comp
    (LinearMap.proj (R := ℂ) (φ := fun _ : Finset (Lam d L N) => EvR (Lam d L N)) i.1))

theorem actCoefL_apply (K : Act d L N) (i : Finset (Lam d L N) × (Σ n : ℕ, Fin n → Sf (Lam d L N))) :
    actCoefL K i = coeff ((K i.1 : EvR (Lam d L N)) : Alg d L N) i.2.2 := rfl

theorem actCoefL_injective : Function.Injective (actCoefL (d := d) (L := L) (N := N)) := by
  intro F G h
  funext b
  refine Subtype.ext ?_
  rw [sum_coeff (F b : Alg d L N), sum_coeff (G b : Alg d L N)]
  refine sum_congr rfl fun n _ => sum_congr rfl fun z _ => ?_
  have := congrFun h (b, ⟨n, z⟩)
  rw [actCoefL_apply, actCoefL_apply] at this
  rw [this]

variable {T : Type*} [TopologicalSpace T]

/-- Coefficient-wise continuity of a map into block families. -/
def CF (f : T → Fam d L N) : Prop :=
  ∀ b n (z : Fin n → Sf (Lam d L N)), Continuous fun t => coeff ((f t b : EvR _) : Alg d L N) z

/-- Coefficient-wise continuity of a map into activities. -/
def CA (f : T → Act d L N) : Prop :=
  ∀ X n (z : Fin n → Sf (Lam d L N)), Continuous fun t => coeff ((f t X : EvR _) : Alg d L N) z

variable {j : ℕ} {ℓ A : ℝ}

section B

variable [Fact (0 < ℓ)]

theorem BSp.continuous_iff (f : T → BSp d L N j ℓ) :
    Continuous f ↔ CF (fun t => (f t).toFam) := by
  let g : BSp d L N j ℓ →ₗ[ℂ] ((Fin d → ℕ) × (Σ n : ℕ, Fin n → Sf (Lam d L N)) → ℂ) :=
    famCoefL.comp BSp.toFam
  have hg : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.2
    (famCoefL_injective.comp BSp.toFam_injective)
  rw [(LinearMap.isClosedEmbedding_of_injective hg).isEmbedding.continuous_iff,
    continuous_pi_iff]
  exact ⟨fun h b n z => h (b, ⟨n, z⟩), fun h i => h i.1 i.2.1 i.2.2⟩

theorem BSp.holE_toFam (b : Fin d → ℕ) :
    HolE (fun F : BSp d L N j ℓ => F.toFam b) :=
  holE_of_linear ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin d → ℕ => EvR (Lam d L N)) b).comp
    (BSp.toFam : BSp d L N j ℓ →ₗ[ℂ] Fam d L N))

end B

section A

variable [Fact (0 < ℓ)] [Fact (0 < A)]

theorem ASp.continuous_iff (f : T → ASp d L N j ℓ A) :
    Continuous f ↔ CA (fun t => (f t).toAct) := by
  let g : ASp d L N j ℓ A →ₗ[ℂ] (Finset (Lam d L N) × (Σ n : ℕ, Fin n → Sf (Lam d L N)) → ℂ) :=
    actCoefL.comp ASp.toAct
  have hg : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.2
    (actCoefL_injective.comp ASp.toAct_injective)
  rw [(LinearMap.isClosedEmbedding_of_injective hg).isEmbedding.continuous_iff,
    continuous_pi_iff]
  exact ⟨fun h b n z => h (b, ⟨n, z⟩), fun h i => h i.1 i.2.1 i.2.2⟩

theorem ASp.holE_toAct (X : Finset (Lam d L N)) :
    HolE (fun K : ASp d L N j ℓ A => K.toAct X) :=
  holE_of_linear ((LinearMap.proj (R := ℂ) (φ := fun _ : Finset (Lam d L N) => EvR (Lam d L N))
    X).comp (ASp.toAct : ASp d L N j ℓ A →ₗ[ℂ] Act d L N))

end A

end

end Step2
