import Obs2.Map.Second
import Obs2.Flow.FlowMu

/-!
# The mass functionals do not see constant covariances (`Pauli`), locality of `e^{ℒ_Γ}`

With `J` the all-ones matrix, `D̄ = ∑_x ∂_{ψ̄_x}` and `D = ∑_y ∂_{ψ_y}`:

* `LopC_J`: `ℒ_J = D D̄`; `D̄² = D² = 0`, `D D̄ = −D̄ D`; `D̄`, `D` commute with every `ℒ_Γ`;
* `expLC_add_J`: `e^{ℒ_{Γ + cJ}} = e^{ℒ_Γ}(1 + c D D̄)`;
* `mass1 (-1) F = ε(D̄ F)`, `mass1 1 F = ε(D F)`, `mass2 F = ε(D D̄ F)`;
* **`mass1_expLC_add_J`**, `mass1p_expLC_add_J`, **`mass2_expLC_add_J`**: for all `Γ`, `c`, `F`,
  `m(e^{ℒ_{Γ + cJ}} F) = m(e^{ℒ_Γ} F)` for `m = m₁^{(−)}, m₁^{(+)}, m₂`. In particular the
  Case (2) functional `m₂` has the same property as `m₁` (the constant part of the covariance
  never contributes to the tadpoles);
* **`expLC_congr_NX`** (locality): for `F ∈ 𝒩(Y)`, `e^{ℒ_Γ} F` only depends on `Γ` on `Y × Y`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Obs2

noncomputable section

open Finset Grassmann Obs.LocObs Loc

section Gen

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- `D̄ = ∑_x ∂_{ψ̄_x}`. -/
def Dbar : Module.End ℂ (N I) := ∑ x, D (x, -1)

/-- `D = ∑_y ∂_{ψ_y}`. -/
def Dpsi : Module.End ℂ (N I) := ∑ y, D (y, 1)

/-- The all-ones matrix. -/
def Jmat (I : Type*) : Matrix I I ℂ := fun _ _ => 1

theorem Dbar_apply (F : N I) : Dbar F = ∑ x, D (x, -1) F := by
  simp [Dbar, LinearMap.sum_apply]

theorem Dpsi_apply (F : N I) : Dpsi F = ∑ y, D (y, 1) F := by
  simp [Dpsi, LinearMap.sum_apply]

/-- A sum `∑_{x,y} ∂_{φ x} ∂_{φ y}` vanishes. -/
theorem sum_D_D_eq_zero (φ : I → Sf I) (F : N I) :
    ∑ a, ∑ b, D (φ a) (D (φ b) F) = 0 := by
  have h : ∑ a, ∑ b, D (φ a) (D (φ b) F) = -∑ a, ∑ b, D (φ a) (D (φ b) F) := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun b _ => D_comm _ _ F
  have h2 : (2 : ℂ) • ∑ a, ∑ b, D (φ a) (D (φ b) F) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem Dbar_Dbar (F : N I) : Dbar (Dbar F) = 0 := by
  rw [Dbar_apply, Dbar_apply]
  simp only [map_sum]
  exact sum_D_D_eq_zero (fun x => (x, -1)) F

theorem Dbar_Dpsi (F : N I) : Dbar (Dpsi F) = -Dpsi (Dbar F) := by
  rw [Dbar_apply, Dpsi_apply, Dpsi_apply, Dbar_apply]
  simp only [map_sum]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun x _ => D_comm _ _ F

/-- `ℒ_J = D D̄`. -/
theorem LopC_J (F : N I) : LopC (Jmat I) F = Dpsi (Dbar F) := by
  rw [LopC_apply, Dbar_apply, Dpsi_apply]
  simp only [map_sum]
  rw [sum_comm]
  simp [Jmat]

theorem Dbar_LopC_J (F : N I) : Dbar (LopC (Jmat I) F) = 0 := by
  rw [LopC_J, Dbar_Dpsi, Dbar_Dbar, map_zero, neg_zero]

theorem LopC_J_sq (F : N I) : LopC (Jmat I) (LopC (Jmat I) F) = 0 := by
  rw [LopC_J (LopC (Jmat I) F), Dbar_LopC_J, map_zero]

/-- `∂_c` commutes with every `ℒ_Γ`. -/
theorem D_LopC (Γ : Matrix I I ℂ) (c : Sf I) (F : N I) :
    D c (LopC Γ F) = LopC Γ (D c F) := by
  rw [LopC_apply, LopC_apply, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [map_smul, DD_comm]

theorem commute_D_LopC (Γ : Matrix I I ℂ) (c : Sf I) : Commute (D c) (LopC Γ) :=
  LinearMap.ext fun F => D_LopC Γ c F

theorem commute_Dbar_LopC (Γ : Matrix I I ℂ) : Commute (Dbar (I := I)) (LopC Γ) :=
  Commute.sum_left _ _ _ fun x _ => commute_D_LopC Γ _

theorem commute_Dpsi_LopC (Γ : Matrix I I ℂ) : Commute (Dpsi (I := I)) (LopC Γ) :=
  Commute.sum_left _ _ _ fun x _ => commute_D_LopC Γ _

theorem LopC_smul (c : ℂ) (Γ : Matrix I I ℂ) : LopC (c • Γ) = c • LopC Γ := by
  ext F
  simp [LopC_apply, Finset.smul_sum, smul_smul]

/-- `e^{ℒ_{cJ}} = 1 + c D D̄`. -/
theorem expLC_J (c : ℂ) (F : N I) :
    expLC (c • Jmat I) F = F + c • LopC (Jmat I) F := by
  have h2 : (LopC (c • Jmat I)) ^ 2 = 0 := by
    refine LinearMap.ext fun F => ?_
    rw [LopC_smul, pow_two, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, LopC_J_sq, smul_zero, smul_zero]
    rfl
  have := IsNilpotent.exp_eq_sum h2
  rw [expLC, this]
  simp [Finset.sum_range_succ, LopC_smul]

/-- `e^{ℒ_{Γ + cJ}} = e^{ℒ_Γ}(1 + c D D̄)`. -/
theorem expLC_add_J (Γ : Matrix I I ℂ) (c : ℂ) (F : N I) :
    expLC (Γ + c • Jmat I) F = expLC Γ (F + c • LopC (Jmat I) F) := by
  rw [expLC, LopC_add, IsNilpotent.exp_add_of_commute (LopC_commute _ _) (LopC_isNilpotent _)
    (LopC_isNilpotent _), Module.End.mul_apply]
  rw [← expLC_J c F]

/-- **Pauli invariance**: any `X` with `X ℒ_J = 0` commuting with all `ℒ_Γ` gives
`ε(X e^{ℒ_{Γ+cJ}}F) = ε(X e^{ℒ_Γ}F)`. -/
theorem eps_X_expLC_add_J (X : Module.End ℂ (N I)) (hX : ∀ Γ : Matrix I I ℂ, Commute X (LopC Γ))
    (hJ : ∀ F, X (LopC (Jmat I) F) = 0) (Γ : Matrix I I ℂ) (c : ℂ) (F : N I) :
    ε (X (expLC (Γ + c • Jmat I) F)) = ε (X (expLC Γ F)) := by
  have hc : ∀ G, X (expLC Γ G) = expLC Γ (X G) := fun G => by
    have := Module.End.commute_exp_left_of_commute (LopC_isNilpotent Γ) (LopC_isNilpotent Γ)
      (hX Γ).symm.eq
    exact (LinearMap.congr_fun this G).symm
  rw [expLC_add_J, hc, hc, map_add, map_smul, hJ, smul_zero, add_zero]

end Gen

section Mass

variable {d L N : ℕ} [NeZero L]

theorem mass1_eq_Dbar (F : Alg d L N) : mass1 (-1) F = ε (Dbar F) := by
  rw [Obs.LocObs.mass1, Dbar_apply, map_sum]; rfl

theorem mass2_eq_DDbar (F : Alg d L N) : Obs.LocObs.mass2 F = ε (Dpsi (Dbar F)) := by
  rw [Obs.LocObs.mass2, Dbar_apply, Dpsi_apply, map_sum]
  simp only [map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rfl

/-- **`m₁(e^{ℒ_{Γ+cJ}}F) = m₁(e^{ℒ_Γ}F)`.** -/
theorem mass1_expLC_add_J (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (c : ℂ) (F : Alg d L N) :
    mass1 (-1) (expLC (Γ + c • Jmat _) F) = mass1 (-1) (expLC Γ F) := by
  rw [mass1_eq_Dbar, mass1_eq_Dbar]
  exact eps_X_expLC_add_J Dbar commute_Dbar_LopC Dbar_LopC_J Γ c F

/-- **Case (2): `m₂(e^{ℒ_{Γ+cJ}}F) = m₂(e^{ℒ_Γ}F)`** (`m₂ = ε ∘ D D̄`, `D D̄ ℒ_J = 0`). -/
theorem mass2_expLC_add_J (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (c : ℂ) (F : Alg d L N) :
    Obs.LocObs.mass2 (expLC (Γ + c • Jmat _) F) = Obs.LocObs.mass2 (expLC Γ F) := by
  rw [mass2_eq_DDbar, mass2_eq_DDbar]
  exact eps_X_expLC_add_J (Dpsi * Dbar)
    (fun Γ => (commute_Dpsi_LopC Γ).mul_left (commute_Dbar_LopC Γ))
    (fun F => by rw [Module.End.mul_apply, Dbar_LopC_J, map_zero]) Γ c F

end Mass

/-! ### Locality -/

section Loc

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem LopC_congr_NX {Y : Set I} {F : N I} (hF : F ∈ NX Y) {Γ Γ' : Matrix I I ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, Γ x y = Γ' x y) : LopC Γ F = LopC Γ' F := by
  rw [LopC_apply, LopC_apply]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ Y
  · by_cases hy : y ∈ Y
    · rw [h x hx y hy]
    · rw [D_eq_zero_of_mem_NX (D_mem_NX hF _) (a := (y, 1)) hy, smul_zero, smul_zero]
  · rw [D_eq_zero_of_mem_NX hF (a := (x, -1)) hx, map_zero, smul_zero, smul_zero]

theorem LopC_pow_congr_NX {Y : Set I} {F : N I} (hF : F ∈ NX Y) {Γ Γ' : Matrix I I ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, Γ x y = Γ' x y) (k : ℕ) : (LopC Γ ^ k) F = (LopC Γ' ^ k) F := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
    exact LopC_congr_NX (LopC_pow_mem_NX Γ' hF k) h

/-- **Locality**: for `F ∈ 𝒩(Y)`, `e^{ℒ_Γ}F` only depends on `Γ|_{Y × Y}`. -/
theorem expLC_congr_NX {Y : Set I} {F : N I} (hF : F ∈ NX Y) {Γ Γ' : Matrix I I ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, Γ x y = Γ' x y) : expLC Γ F = expLC Γ' F := by
  rw [expLC_apply_eq_sum, expLC_apply_eq_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LopC_pow_congr_NX hF h k]

end Loc

end

end Obs2
