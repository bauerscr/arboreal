import Obs2.Flow.Wick1

/-!
# `F_C` with a pair `ι u ι w`: one line plus one bubble

* `FC_pair`: for `PM u w` (`u` spin `+`, `w` spin `-`) and every `B`,
  `F_C(ι u ι w, B) = Xc_C(ι u ι w, B) + ½ X₂(ι u ι w, B)` (exactly; from `exp_mul_conj` with
  `[𝓛, A·] = 𝓛A + Xc(A, ·)`, `[𝓛, Xc(A, ·)] = X₂(A, ·)`, `[𝓛, X₂(A, ·)] = 0`);
* `FC_pbp`: the same for `ψ̄_aψ_a = -(ψ_aψ̄_a)`, and the explicit forms
  `Xc(ψ̄_aψ_a, B) = -∑_x C(x,a) ψ̄_a ∂_{ψ̄_x}B - ∑_y C(a,y) ψ_a ∂_{ψ_y}B` (`Xc_pbp`),
  `½X₂(ψ̄_aψ_a, B) = ∑_{x,y} C(x,a) C(a,y) ∂_{ψ̄_x}∂_{ψ_y} B` (`X2_pbp`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs

section Pair

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ)

theorem D_pair (u w : V Λ) (a : Sf Λ) : D a (ι u * ι w) = ι (u a • w - w a • u) := by
  rw [D_ι_mul, D_ι, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_sub, map_smul,
    map_smul]

theorem inv'_pair (u w : V Λ) : inv' (ι u * ι w) = ι u * ι w := by
  rw [map_mul, Step2.inv'_ι, Step2.inv'_ι, neg_mul_neg]

theorem Xc_one_left (r : ℂ) (Y : Grassmann.N Λ) : Xc C (r • (1 : Grassmann.N Λ)) Y = 0 := by
  unfold Xc
  have : ∀ a : Sf Λ, D a (r • (1 : Grassmann.N Λ)) = 0 := fun a => by
    rw [map_smul, show (1 : Grassmann.N Λ) = algebraMap ℂ _ 1 from (map_one _).symm,
      D_algebraMap, smul_zero]
  simp [this]

theorem LopC_Xc_D_pair (u w : V Λ) (a : Sf Λ) (Q : Grassmann.N Λ) :
    LopC C (Xc C (D a (ι u * ι w)) Q) = Xc C (D a (ι u * ι w)) (LopC C Q) := by
  rw [D_pair, LopC_Xc_lin]

theorem LopC_X2_pair (u w : V Λ) (Y : Grassmann.N Λ) :
    LopC C (X2 C (ι u * ι w) Y) = X2 C (ι u * ι w) (LopC C Y) := by
  unfold X2
  simp only [map_sum, map_smul, map_sub, LopC_Xc_D_pair, LopC_D]

/-- `e^{𝓛}(A Y) = A e^{𝓛}Y + 𝓛A e^{𝓛}Y + Xc(A, e^{𝓛}Y) + ½ X₂(A, e^{𝓛}Y)` for a pair `A`. -/
theorem expLC_mul_pair {u w : V Λ} (h : PM u w) (Y : Grassmann.N Λ) :
    expLC C (ι u * ι w * Y) = ι u * ι w * expLC C Y + (-pairC C u w) • expLC C Y +
      Xc C (ι u * ι w) (expLC C Y) + (1 / 2 : ℂ) • X2 C (ι u * ι w) (expLC C Y) := by
  set A := ι u * ι w with hAd
  have hA : inv' A = A := inv'_pair u w
  have hLA : LopC C A = (-pairC C u w) • (1 : Grassmann.N Λ) := LopC_two C h
  have h1 : LopC C * LinearMap.mulLeft ℂ A = LinearMap.mulLeft ℂ A * LopC C +
      ((-pairC C u w) • (1 : Module.End ℂ (Grassmann.N Λ)) + XcL C A) := by
    refine LinearMap.ext fun Q => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, XcL_apply, LopC_mul_even C hA, hLA,
      smul_mul_assoc, one_mul]
    abel
  have h2 : LopC C * ((-pairC C u w) • (1 : Module.End ℂ (Grassmann.N Λ)) + XcL C A) =
      ((-pairC C u w) • (1 : Module.End ℂ (Grassmann.N Λ)) + XcL C A) * LopC C + X2L C A := by
    refine LinearMap.ext fun Q => ?_
    have e := LopC_Xc C hA Q
    rw [hLA, Xc_one_left] at e
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, XcL_apply, X2L_apply, map_add, map_smul]
    rw [← e]; abel
  have h3 : LopC C * X2L C A = X2L C A * LopC C := by
    refine LinearMap.ext fun Q => ?_
    simp only [Module.End.mul_apply, X2L_apply, hAd, LopC_X2_pair]
  have hh := LinearMap.congr_fun (exp_mul_conj (LopC_isNilpotent C) h1 h2 h3) Y
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, XcL_apply, X2L_apply] at hh
  rw [hh, ← Rat.cast_smul_eq_qsmul ℂ]
  push_cast
  abel

/-- **`F_C` of a pair: one line plus one bubble.** -/
theorem FC_pair {u w : V Λ} (h : PM u w) (B : Grassmann.N Λ) :
    FC C (ι u * ι w) B = Xc C (ι u * ι w) B + (1 / 2 : ℂ) • X2 C (ι u * ι w) B := by
  rw [FC, expLC_two (-C) h, pairC_neg, neg_neg, add_mul, map_add, expLC_mul_pair C h,
    expLC_expLC_neg, smul_mul_assoc, one_mul, map_smul, expLC_expLC_neg]
  module

end Pair

/-! ### The vertex `ψ̄_aψ_a` -/

section Pbp

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)

local notation "ι" => (ExteriorAlgebra.ι ℂ : V Λ →ₗ[ℂ] Grassmann.N Λ)

theorem psibar_psi_eq (a : Λ) :
    psibar a * psi a = -(ι (ev ((a, 1) : Sf Λ)) * ι (ev ((a, -1) : Sf Λ))) := by
  unfold psibar psi; exact ψ_anticomm _ _

theorem pm_ev' (a : Λ) : PM (ev ((a, 1) : Sf Λ)) (ev (a, -1)) :=
  ⟨fun x => by simp [ev, Pi.single_apply, Prod.ext_iff], fun x => by
    simp [ev, Pi.single_apply, Prod.ext_iff]⟩

/-- `F_C(ψ̄_aψ_a, B) = Xc(ψ̄_aψ_a, B) + ½ X₂(ψ̄_aψ_a, B)`. -/
theorem FC_pbp' (a : Λ) (B : Grassmann.N Λ) :
    FC C (psibar a * psi a) B =
      Xc C (psibar a * psi a) B + (1 / 2 : ℂ) • X2 C (psibar a * psi a) B := by
  rw [psibar_psi_eq, show ∀ X : Grassmann.N Λ, -X = (-1 : ℂ) • X from fun X => by simp,
    FC_smul_left, Xc_smul_left, X2_smul_left, FC_pair C (pm_ev' a), smul_add, smul_comm]

theorem D_pb_minus (a x : Λ) :
    D (x, -1) (psibar a * psi a) = if x = a then psi a else 0 := by
  have e : psibar a * psi a = ι (ev ((a, -1) : Sf Λ)) * ι (ev ((a, 1) : Sf Λ)) := rfl
  rw [e, D_pair]
  by_cases h : x = a
  · subst h; simp [ev, Pi.single_apply, Prod.ext_iff]; rfl
  · simp [ev, Pi.single_apply, Prod.ext_iff, h]

theorem D_pb_plus (a y : Λ) :
    D (y, 1) (psibar a * psi a) = if y = a then -psibar a else 0 := by
  have e : psibar a * psi a = ι (ev ((a, -1) : Sf Λ)) * ι (ev ((a, 1) : Sf Λ)) := rfl
  rw [e, D_pair]
  by_cases h : y = a
  · subst h; simp [ev, Pi.single_apply, Prod.ext_iff]; rfl
  · simp [ev, Pi.single_apply, Prod.ext_iff, h]

/-- `Xc(ψ̄_aψ_a, B) = -∑_x C(x,a) ψ̄_a ∂_{ψ̄_x}B - ∑_y C(a,y) ψ_a ∂_{ψ_y}B`. -/
theorem Xc_pbp (a : Λ) (B : Grassmann.N Λ) :
    Xc C (psibar a * psi a) B = -(∑ x, C x a • (psibar a * D (x, -1) B)) -
      ∑ y, C a y • (psi a * D (y, 1) B) := by
  unfold Xc
  simp only [D_pb_minus, D_pb_plus, ite_mul, zero_mul, smul_sub, sum_sub_distrib, smul_ite,
    smul_zero, sum_ite_eq', mem_univ, if_true, neg_mul, smul_neg, sum_neg_distrib]
  rw [sum_comm (f := fun x y => if x = a then C x y • (psi a * D (y, 1) B) else 0)]
  simp only [sum_ite_eq', mem_univ, if_true]

theorem Xc_psi (a : Λ) (Q : Grassmann.N Λ) : Xc C (psi a) Q = ∑ x, C x a • D (x, -1) Q := by
  have e : (psi a : Grassmann.N Λ) = ι (ev ((a, 1) : Sf Λ)) := rfl
  rw [e, Xc_lin]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single a (fun y _ hy => by simp [ev, Pi.single_apply, Prod.ext_iff, hy]) (by simp)]
  simp [ev, Pi.single_apply, Prod.ext_iff]

theorem Xc_psibar (a : Λ) (Q : Grassmann.N Λ) :
    Xc C (psibar a) Q = -∑ y, C a y • D (y, 1) Q := by
  have e : (psibar a : Grassmann.N Λ) = ι (ev ((a, -1) : Sf Λ)) := rfl
  have h := FC_psibar C a Q
  rw [e, FC_lin] at h
  rw [e, ← h, neg_neg]

/-- `X₂(ψ̄_aψ_a, B) = ∑_y C(a,y) Xc(ψ_a, ∂_{ψ_y}B) + ∑_x C(x,a) Xc(ψ̄_a, ∂_{ψ̄_x}B)`. -/
theorem X2_pbp1 (a : Λ) (B : Grassmann.N Λ) :
    X2 C (psibar a * psi a) B = ∑ y, C a y • Xc C (psi a) (D (y, 1) B) +
      ∑ x, C x a • Xc C (psibar a) (D (x, -1) B) := by
  have h0 : ∀ Q : Grassmann.N Λ, Xc C 0 Q = 0 := fun Q => by
    simpa using Xc_smul_left C 0 0 Q
  have hn : ∀ Q : Grassmann.N Λ, Xc C (-psibar a) Q = -Xc C (psibar a) Q := fun Q => by
    simpa using Xc_smul_left C (-1) (psibar a) Q
  unfold X2
  simp only [D_pb_minus, D_pb_plus, smul_sub, sum_sub_distrib]
  have e1 : ∑ x, ∑ y, C x y • Xc C (if x = a then psi a else 0) (D (y, 1) B) =
      ∑ y, C a y • Xc C (psi a) (D (y, 1) B) := by
    rw [Fintype.sum_eq_single a (fun x hx => by simp [if_neg hx, h0])]
    simp
  have e2 : ∑ x, ∑ y, C x y • Xc C (if y = a then -psibar a else 0) (D (x, -1) B) =
      -∑ x, C x a • Xc C (psibar a) (D (x, -1) B) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_eq_single a (fun y hy => by simp [if_neg hy, h0])]
    simp [hn]
  rw [e1, e2, sub_neg_eq_add]

end Pbp

end

end Obs2
