import Obs2.Flow.WickV

/-!
# The one-loop coefficients of the observable vertices with the bulk polynomial `V_κ(Λ)`

For `κ = (z, y, ν, g)` and every complex covariance `C`:

* `mass1_FC_psibar_Vcoup` (Case (1), `lem:second`(iii)):
  `m₁ F_C(ψ̄_a, V_κ(Λ)) = ν ∑_x C(a, x)`;
* `mass2_FC_pbp_Vcoup` (Case (2), `lem:second`(ii)):
  `m₂ F_C(ψ̄_aψ_a, V_κ(Λ)) = ν (∑_x C(a, x) + ∑_x C(x, a)) - g 𝔩_C(a)`,
  `𝔩_C(a) = ∑_i ∑_z ½ ∑_{e = ±e_i} (C(a,z+e) - C(a,z)) (C(z+e,a) - C(z,a))` (`lfunC`).

The gradient monomials do not contribute: a quadratic local monomial `M` contributes its stencil
weight `∑ w = δ_{M, ψψ̄}` (`weight_sum`, from the moment identity `Loc.moment`) times a lattice sum
that is translation invariant over the torus (`stencil_sum`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs FRD

variable {d L N : ℕ} [NeZero L] (C : Matrix (Lam d L N) (Lam d L N) ℂ)

/-- `B ↦ F_C(A, B)` as a linear map. -/
def FCr (A : Alg d L N) : Alg d L N →ₗ[ℂ] Alg d L N where
  toFun := FC C A
  map_add' := FC_add_right C A
  map_smul' r B := FC_smul_right C r A B

theorem FC_one_right (A : Alg d L N) : FC C A 1 = 0 := by
  rw [FC, expLC_one (-C), mul_one, expLC_expLC_neg, mul_one, sub_self]

theorem sum_add_right' (f : Lam d L N → ℂ) (u : Lam d L N) : ∑ x, f (x + u) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight u) _ _ (fun _ => rfl)

theorem list_sum_fin {α : Type*} (m : List α) (f : α → Lam d L N → ℂ) :
    ∑ x, (m.map fun p => f p x).sum = (m.map fun p => ∑ x, f p x).sum := by
  induction m with
  | nil => simp
  | cons p m ih => simp [sum_add_distrib, ih]

theorem list_cast_sum {α : Type*} (m : List α) (f : α → ℝ) :
    (m.map fun p => ((f p : ℝ) : ℂ)).sum = (((m.map f).sum : ℝ) : ℂ) := by
  induction m with
  | nil => simp
  | cons p m ih => simp [ih]

/-- The total stencil weight of a quadratic monomial: `1` for `ψψ̄`, `0` otherwise. -/
theorem weight_sum (M : Mono d) :
    ((stencil M).map fun p => ((p.1 : ℝ) : ℂ)).sum = if M = Mono.c then 1 else 0 := by
  have h := moment M Mono.c (Nat.zero_le _) 0 0
  unfold applySt at h
  simp only [Qpoly, mul_one] at h
  rw [list_cast_sum, h]
  by_cases hM : M = Mono.c
  · subst hM; simp
  · rw [if_neg (Ne.symm hM), if_neg hM]; simp

/-- **A linear functional on the quadratic monomials over the torus.** -/
theorem stencil_sum (Φ : Alg d L N →ₗ[ℂ] ℂ) (F : Lam d L N → Lam d L N → ℂ) (K : ℂ)
    (hΦ : ∀ s t, Φ (psi s * psibar t) = F s t)
    (hK : ∀ u w : Lam d L N, ∑ x, F (x + u) (x + w) = K) (M : Mono d) :
    Φ (monoSet M univ) = (if M = Mono.c then 1 else 0) * K := by
  have e : ∀ x, Φ (monoAt M x) = ((stencil M).map fun p =>
      ((p.1 : ℝ) : ℂ) * F (x + prj p.2.1) (x + prj p.2.2)).sum := by
    intro x
    unfold monoAt
    rw [map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, map_smul, hΦ, smul_eq_mul]
  rw [monoSet, map_sum]
  simp only [e]
  rw [list_sum_fin]
  have e2 : ∀ p : ℝ × Zd d × Zd d,
      ∑ x, ((p.1 : ℝ) : ℂ) * F (x + prj p.2.1) (x + prj p.2.2) = ((p.1 : ℝ) : ℂ) * K := by
    intro p; rw [← mul_sum, hK]
  simp only [e2]
  rw [List.sum_map_mul_right, weight_sum]

/-! ### Case (1) -/

/-- **`m₁ F_C(ψ̄_a, V_κ(Λ)) = ν ∑_x C(a, x)`.** -/
theorem mass1_FC_psibar_Vcoup (a : Lam d L N) (κ : Step2.Coup) :
    mass1 (-1) (FC C (psibar a) (Step2.Vcoup κ univ)) = κ.nu * ∑ x, C a x := by
  set Φ := (mass1L (d := d) (L := L) (N := N) (-1)).comp (FCr C (psibar a)) with hΦd
  have hΦ : ∀ B, Φ B = mass1 (-1) (FC C (psibar a) B) := fun _ => rfl
  have hpair : ∀ M : Mono d, Φ (monoSet M univ) = (if M = Mono.c then 1 else 0) * ∑ x, C a x :=
    stencil_sum Φ (fun s _ => C a s) _ (fun s t => by rw [hΦ, mass1_FC_psibar_pair])
      (fun u w => sum_add_right' (fun x => C a x) u)
  have hq : ∀ i k : Fin d, Φ (mono4sSet i k univ) = 0 := fun i k => by
    rw [hΦ]
    exact mass1_FC_psibar_hom C a (IsHom.sum _ fun x _ => isHom_mono4s i k x) (by norm_num)
  have h1 : Φ 1 = 0 := by rw [hΦ, FC_one_right]; exact map_zero (mass1L (-1))
  rw [← hΦ, Step2.Vcoup, Step2.unif, map_add, map_add, map_smul, h1, smul_zero, zero_add, map_sum, map_sum]
  simp only [map_sum, map_smul, hq, hpair, smul_zero, sum_const_zero, add_zero, smul_eq_mul]
  rw [Fintype.sum_eq_single Mono.c (fun M hM => by rw [if_neg hM]; ring)]
  simp [Step2.coupC]

/-! ### Case (2) -/

/-- One gradient leg pair of the bubble. -/
def gpC (a : Lam d L N) (e : Dir d) (z : Lam d L N) : ℂ :=
  (C a (z + dirVec e) - C a z) * (C (z + dirVec e) a - C z a)

/-- `𝔩_C(a) = ∑_i ∑_z ½ ∑_{e = ±e_i} (C(a,z+e) - C(a,z)) (C(z+e,a) - C(z,a))`. -/
def lfunC (a : Lam d L N) : ℂ :=
  ∑ i : Fin d, ∑ z, (1 / 2 : ℂ) * (gpC C a (Sum.inl i) z + gpC C a (Sum.inr i) z)

theorem mass2_FC_pbp_mono4s (a : Lam d L N) (i : Fin d) :
    mass2 (FC C (pbp a) (mono4sSet i i univ)) = -∑ z, (1 / 2 : ℂ) *
      (gpC C a (Sum.inl i) z + gpC C a (Sum.inr i) z) := by
  rw [mono4sSet, FC_sum_right, mass2_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun z _ => ?_
  rw [mono4s_diag, FC_smul_right, mass2_smul, FC_sum_right, mass2_sum, Fin.sum_univ_two]
  simp only [pmdir, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    mass2_FC_pbp_gmono4, gpC]
  ring

/-- **`m₂ F_C(ψ̄_aψ_a, V_κ(Λ)) = ν (∑_x C(a,x) + ∑_x C(x,a)) - g 𝔩_C(a)`.** -/
theorem mass2_FC_pbp_Vcoup (a : Lam d L N) (κ : Step2.Coup) :
    mass2 (FC C (pbp a) (Step2.Vcoup κ univ)) =
      κ.nu * (∑ x, C a x + ∑ x, C x a) - κ.g * lfunC C a := by
  set Φ := (mass2L (d := d) (L := L) (N := N)).comp (FCr C (pbp a)) with hΦd
  have hΦ : ∀ B, Φ B = mass2 (FC C (pbp a) B) := fun _ => rfl
  have hpair : ∀ M : Mono d, Φ (monoSet M univ) =
      (if M = Mono.c then 1 else 0) * (∑ x, C a x + ∑ x, C x a) :=
    stencil_sum Φ (fun s t => C t a + C a s) _ (fun s t => by rw [hΦ, mass2_FC_pbp_pair])
      (fun u w => by
        rw [sum_add_distrib, sum_add_right' (fun x => C x a) w,
          sum_add_right' (fun x => C a x) u, add_comm])
  have hq : ∀ i : Fin d, Φ (mono4sSet i i univ) =
      -∑ z, (1 / 2 : ℂ) * (gpC C a (Sum.inl i) z + gpC C a (Sum.inr i) z) := fun i => by
    rw [hΦ, mass2_FC_pbp_mono4s]
  have h1 : Φ 1 = 0 := by rw [hΦ, FC_one_right]; exact map_zero mass2L
  rw [← hΦ, Step2.Vcoup, Step2.unif, map_add, map_add, map_smul, h1, smul_zero, zero_add, map_sum, map_sum]
  simp only [map_sum, map_smul, hpair, smul_eq_mul]
  rw [Fintype.sum_eq_single Mono.c (fun M hM => by rw [if_neg hM]; ring)]
  have hE : ∀ i : Fin d, ∑ k : Fin d, Step2.coupE κ i k * Φ (mono4sSet i k univ) =
      κ.g * Φ (mono4sSet i i univ) := fun i => by
    rw [Fintype.sum_eq_single i (fun k hk => by simp [Step2.coupE, Ne.symm hk])]
    simp [Step2.coupE]
  simp only [hE, hq]
  simp only [lfunC, if_true, Step2.coupC, one_mul, mul_neg, sum_neg_distrib, ← mul_sum]
  ring

end

end Obs2
