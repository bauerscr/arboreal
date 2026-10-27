module

public import ArborealDecay.H02.Spin

/-!
# The symmetry `J : ξ ↦ η, η ↦ -ξ`

`J` is the algebra automorphism of `Ω^{2Λ}` with `J ξ_i = η_i`, `J η_i = -ξ_i` (the rotation by
`π/2` in the `(ξ, η)` plane).  It satisfies `J(ξ_a η_b) = ξ_b η_a`, `J z_i = z_i`,
`J (u_i · u_j) = u_i · u_j`, hence fixes the action for all weights; it intertwines the fermionic
derivatives (`J ∂_{ξ_i} = ∂_{η_i} J`, `J ∂_{η_i} = -∂_{ξ_i} J`), hence commutes with the
factors `∂_{η_i}∂_{ξ_i} z_i⁻¹` and leaves `[·]_0` invariant.  Consequently (`avg_ξη_symm`)
`⟨ξ_a η_b⟩_{β,h} = ⟨ξ_b η_a⟩_{β,h}` for every symmetric `β` and every external field `h`.
-/

@[expose] public section

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open CliffordAlgebra Finset

section General

variable {M M' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup M'] [Module ℝ M']

theorem inv'_map' (f : M →ₗ[ℝ] M') (x : ExteriorAlgebra ℝ M) :
    inv' (ExteriorAlgebra.map f x) = ExteriorAlgebra.map f (inv' x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [ExteriorAlgebra.map_apply_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- The chain rule for the contraction over `ℝ`. -/
theorem contractLeft_map' (f : M →ₗ[ℝ] M') (φ : Module.Dual ℝ M') (x : ExteriorAlgebra ℝ M) :
    contractLeft φ (ExteriorAlgebra.map f x) = ExteriorAlgebra.map f (contractLeft (φ ∘ₗ f) x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [ExteriorAlgebra.map_apply_ι, contractLeft_ι]
  | mul a b ha hb =>
    rw [map_mul, contractLeft_mul, contractLeft_mul, ha, hb, map_add, map_mul, map_mul, inv'_map']
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end General

variable {Λ : Type*} [DecidableEq Λ]

local notation "A" => Grassmann Λ

/-- The linear map `ξ_i ↦ η_i`, `η_i ↦ -ξ_i` on the generators. -/
def Jlin : Gen Λ →ₗ[ℝ] Gen Λ where
  toFun v := fun a => match a with
    | Sum.inl i => -v (Sum.inr i)
    | Sum.inr i => v (Sum.inl i)
  map_add' v w := by funext a; rcases a with i | i <;> simp [add_comm]
  map_smul' r v := by funext a; rcases a with i | i <;> simp

/-- The automorphism `J : ξ_i ↦ η_i, η_i ↦ -ξ_i`. -/
def Jmap : Grassmann Λ →ₐ[ℝ] Grassmann Λ := ExteriorAlgebra.map Jlin

theorem Jmap_ξ (i : Λ) : Jmap (ξ i) = η i := by
  rw [Jmap, ξ, ExteriorAlgebra.map_apply_ι, η]; congr 1
  funext a; rcases a with j | j <;> simp [Jlin, Pi.single_apply]

theorem Jmap_η (i : Λ) : Jmap (η i) = -ξ i := by
  rw [Jmap, η, ExteriorAlgebra.map_apply_ι, ξ, ← map_neg]; congr 1
  funext a; rcases a with j | j <;> simp [Jlin, Pi.single_apply]

theorem Jmap_ξη (a b : Λ) : Jmap (ξ a * η b) = ξ b * η a := by
  rw [map_mul, Jmap_ξ, Jmap_η, mul_neg, η_anticomm_ξ, neg_neg]

theorem Jmap_z (i : Λ) : Jmap (z i) = z i := by
  rw [z, map_sub, map_one, Jmap_ξη]

theorem Jmap_dot (i j : Λ) : Jmap (dot i j) = dot i j := by
  rw [dot, map_sub, map_sub, map_neg, Jmap_ξη, Jmap_ξη, map_mul, Jmap_z, Jmap_z]; abel

theorem Jmap_action [Fintype Λ] (β : Λ → Λ → ℝ) (h : Λ → ℝ) : Jmap (action β h) = action β h := by
  simp [action, map_sum, map_smul, Jmap_dot, Jmap_z]

theorem Jlin_comp_inl (i : Λ) :
    (LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inl i)) ∘ₗ Jlin =
      -LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inr i) := by
  ext v; simp [Jlin]

theorem Jlin_comp_inr (i : Λ) :
    (LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inr i)) ∘ₗ Jlin =
      LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (Sum.inl i) := by
  ext v; simp [Jlin]

/-- `∂_{ξ_i} J = -J ∂_{η_i}`. -/
theorem dξ_Jmap (i : Λ) (x : A) : dξ i (Jmap x) = -Jmap (dη i x) := by
  rw [dξ, Jmap, contractLeft_map', Jlin_comp_inl, map_neg, LinearMap.neg_apply, map_neg]; rfl

/-- `∂_{η_i} J = J ∂_{ξ_i}`. -/
theorem dη_Jmap (i : Λ) (x : A) : dη i (Jmap x) = Jmap (dξ i x) := by
  rw [dη, Jmap, contractLeft_map', Jlin_comp_inr]; rfl

theorem Jmap_intStep (i : Λ) (F : A) : Jmap (intStep i F) = intStep i (Jmap F) := by
  rw [intStep_apply, intStep_apply]
  have : Jmap ((1 + ξ i * η i) * F) = (1 + ξ i * η i) * Jmap F := by
    rw [map_mul, map_add, map_one, Jmap_ξη]
  rw [← this, dξ_Jmap, map_neg, dη_Jmap, dξ_comm_dη, map_neg, neg_neg]

theorem Jmap_berezin (l : List Λ) (F : A) : Jmap (berezin l F) = berezin l (Jmap F) := by
  induction l generalizing F with
  | nil => rfl
  | cons i l ih => rw [berezin_cons, berezin_cons, ih, Jmap_intStep]

theorem algebraMapInv_Jmap (x : A) :
    ExteriorAlgebra.algebraMapInv (Jmap x) = ExteriorAlgebra.algebraMapInv x := by
  have : (ExteriorAlgebra.algebraMapInv : A →ₐ[ℝ] ℝ).comp Jmap = ExteriorAlgebra.algebraMapInv := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [Jmap, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.algebraMapInv]
  exact congrArg (fun f : A →ₐ[ℝ] ℝ => f x) this

variable [Fintype Λ]

theorem int0_Jmap (F : A) : int0 (Jmap F) = int0 F := by
  rw [int0, int0, ← Jmap_berezin, algebraMapInv_Jmap]

theorem isNilpotent_neg_action (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    IsNilpotent (-action β h) := by
  rw [action_eq β hβ h, neg_neg]
  exact (isNilpotent_W β hβ h).map cv

/-- `[J F]_{β,h} = [F]_{β,h}`. -/
theorem expect_Jmap (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (F : A) :
    expect β h (Jmap F) = expect β h F := by
  rw [expect, expect, ← int0_Jmap (F * _), map_mul,
    IsNilpotent.map_exp (isNilpotent_neg_action β hβ h), map_neg, Jmap_action]

/-- **The `ξ ↔ η` symmetry**: `[ξ_a η_b]_{β,h} = [ξ_b η_a]_{β,h}`. -/
theorem expect_ξη_symm (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (a b : Λ) :
    expect β h (ξ a * η b) = expect β h (ξ b * η a) := by
  rw [← expect_Jmap β hβ h, Jmap_ξη]

/-- **The `ξ ↔ η` symmetry**: `⟨ξ_a η_b⟩_{β,h} = ⟨ξ_b η_a⟩_{β,h}`, for any symmetric `β` and
any external field `h`. -/
theorem avg_ξη_symm (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) (a b : Λ) :
    avg β h (ξ a * η b) = avg β h (ξ b * η a) := by
  rw [avg, avg, expect_ξη_symm β hβ h]

end

end H02

end
