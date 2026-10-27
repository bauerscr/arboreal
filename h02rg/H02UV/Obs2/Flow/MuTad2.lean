import Obs2.Flow.WickVcoup

/-!
# The tadpole of the one-loop `𝒲^{obs}` cubic (Case (1))

The second-order term `F_C(β ψ̄_a, V_κ(Λ))` of the observable map (the `a` component of
`½ F_C(V'(Λ), V'(Λ))`) has a linear part (`ν C(a,x) ψ̄_x` and gradient terms, whose mass is
extracted by `Loc`) and a **cubic part** from the quartic `g M̂`. The cubic part stays in
`𝒲^{obs}`; at a later step a covariance `Γ` contracts it (`e^{ℒ_Γ}`) to a linear term, whose mass
is the tadpole part `(ν' - ν) w^{(1)}` of `𝔫_j` in the `μ^{(1)}` flow. This file evaluates it
exactly, for all complex `C, Γ` (lattice sums over the torus):

* `tad_mass1_DDD_four`: `m₁ ∂_{ψ_v} ∂_{ψ̄_u} ∂_{ψ_y} (ι a ι b ι c ι e)` for four linear forms of
  spins `+, -, +, -`;
* `tad_mass1_lop_gmono4`:
  `m₁ ℒ_Γ F_C(ψ̄_p, (∇_eψ)(∇_{e'}ψ̄)ψψ̄_z) = tadG C Γ p e e' z`,
  `tadG = (C(p,z+e) - C(p,z))(Γ(z+e',z) - Γ(z,z)) - C(p,z)(∇_{e'}∇_e Γ)(z,z)`;
* **`mass1_expLC_FC_psibar_Vcoup`**: `m₁(e^{ℒ_Γ} F_C(ψ̄_p, V_κ(Λ))) - m₁(F_C(ψ̄_p, V_κ(Λ))) =
  g · tauC C Γ p`, `tauC C Γ p = ∑_i ∑_z ½ ∑_{e = ±e_i} tadG C Γ p e e z` (the quadratic
  monomials and the constant give linear terms, on which `e^{ℒ_Γ}` is the identity);
* `tad_FC_one`: the same for `F_C(β ψ̄_a, V_κ(Λ) + r)` (the one-loop term of the observable map);
* `tauC_add_left`, `tauC_add_right`, `tauC_sum_left`, `tauC_zero_left`, `tauC_zero_right`:
  `tauC` is bilinear in `(C, Γ)`;
* **`tauC_TI`**: if `Γ(x,x) = c₀` and `Γ(x+e,x) = Γ(x,x+e) = c₀ + δ` for all `x` and unit `e`,
  then `tauC C Γ p = 2 d δ ∑_z C(p,z)` (`= ΔΓ(0) C^{(1)}(p)`, for every `C`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs FRD

variable {d L N : ℕ} [NeZero L]

local notation "ι" => (ExteriorAlgebra.ι ℂ : V (Lam d L N) →ₗ[ℂ] Alg d L N)

/-! ### Masses of linear forms -/

theorem tad_coeff_one (F : Alg d L N) (a : Sf (Lam d L N)) : coeff F ![a] = ε (D a F) := by
  simp only [coeff, Dseq, contr_succ, contr_zero]
  rfl

theorem tad_mass1_ι (v : V (Lam d L N)) : mass1 (-1) (ι v) = Sm v := by
  unfold mass1 Sm
  refine sum_congr rfl fun x _ => ?_
  rw [tad_coeff_one, D_ι, AlgHom.commutes]
  rfl

theorem tad_mass1_D_pair (p q : V (Lam d L N)) (s : Sf (Lam d L N)) :
    mass1 (-1) (D s (ι p * ι q)) = p s * Sm q - q s * Sm p := by
  rw [D_pair, tad_mass1_ι]
  simp only [Sm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sum_sub_distrib, mul_sum]

theorem tad_mass1_neg (F : Alg d L N) : mass1 (-1) (-F) = -mass1 (-1) F :=
  map_neg (mass1L (d := d) (L := L) (N := N) (-1)) F

/-- The triple derivative of four linear forms of spins `+, -, +, -`. -/
theorem tad_mass1_DDD_four {a b c e : V (Lam d L N)} (ha : ∀ y, a (y, -1) = 0)
    (hb : ∀ y, b (y, 1) = 0) (hc : ∀ y, c (y, -1) = 0) (he : ∀ y, e (y, 1) = 0)
    (u v y : Lam d L N) :
    mass1 (-1) (D (v, 1) (D (u, -1) (D (y, 1) (ι a * (ι b * (ι c * ι e)))))) =
      a (y, 1) * (b (u, -1) * c (v, 1) * Sm e - e (u, -1) * c (v, 1) * Sm b) +
        c (y, 1) * (-(b (u, -1) * a (v, 1) * Sm e) + e (u, -1) * a (v, 1) * Sm b) := by
  have e1 : D (y, 1) (ι a * (ι b * (ι c * ι e))) =
      a (y, 1) • (ι b * (ι c * ι e)) + c (y, 1) • (ι a * (ι b * ι e)) := by
    rw [D_ι_mul, D_ι_mul, D_pair, hb, he]
    simp only [zero_smul, zero_sub, sub_zero, map_smul, mul_smul_comm, mul_neg, neg_neg,
      sub_neg_eq_add]
  have e2 : D (u, -1) (ι b * (ι c * ι e)) = b (u, -1) • (ι c * ι e) + e (u, -1) • (ι b * ι c) := by
    rw [D_ι_mul, D_pair, hc]
    simp only [zero_smul, zero_sub, map_neg, map_smul, mul_neg, mul_smul_comm, sub_neg_eq_add]
  have e3 : D (u, -1) (ι a * (ι b * ι e)) =
      -(b (u, -1) • (ι a * ι e)) + e (u, -1) • (ι a * ι b) := by
    rw [D_ι_mul, D_pair, ha]
    simp only [zero_smul, zero_sub, map_sub, map_smul, mul_sub, mul_smul_comm]
    abel
  rw [e1, map_add, map_smul, map_smul, e2, e3]
  simp only [map_add, map_smul, map_neg, mass1_add, mass1_smul, tad_mass1_neg, tad_mass1_D_pair,
    hb, he]
  ring

/-- The triple derivative of `(∇_eψ)(∇_{e'}ψ̄)ψψ̄_z`. -/
theorem tad_mass1_DDD_gmono4 (e e' : Dir d) (z u v y : Lam d L N) :
    mass1 (-1) (D (v, 1) (D (u, -1) (D (y, 1) (gmono4 e e' z)))) =
      v4g e e' z 1 (u, -1) *
        (v4g e e' z 0 (y, 1) * v4g e e' z 2 (v, 1) - v4g e e' z 2 (y, 1) * v4g e e' z 0 (v, 1)) := by
  rw [gmono4_ι, tad_mass1_DDD_four (v4g_pos0 e e' z) (v4g_neg1 e e' z) (v4g_pos2 e e' z)
    (v4g_neg3 e e' z), Sm_v4g3, Sm_v4g1]
  ring

/-! ### `m₁ ℒ_Γ F_C(ψ̄_p, B)` -/

/-- `m₁ ℒ_Γ F_C(ψ̄_p, B) = ∑_{u,v} Γ(u,v) ∑_y C(p,y) m₁ ∂_{ψ_v} ∂_{ψ̄_u} ∂_{ψ_y} B`. -/
theorem tad_mass1_lop_FC (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N)
    (B : Alg d L N) :
    mass1 (-1) (LopC Γ (FC C (psibar p) B)) =
      ∑ u, ∑ v, Γ u v * ∑ y, C p y * mass1 (-1) (D (v, 1) (D (u, -1) (D (y, 1) B))) := by
  rw [LopC_apply, FC_psibar]
  show mass1L (-1) _ = _
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

/-- The tadpole of one gradient monomial. -/
def tadG (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) (e e' : Dir d)
    (z : Lam d L N) : ℂ :=
  (C p (z + dirVec e) - C p z) * (Γ (z + dirVec e') z - Γ z z) -
    C p z * (Γ (z + dirVec e') (z + dirVec e) - Γ (z + dirVec e') z - Γ z (z + dirVec e) + Γ z z)

theorem tad_sum_v4g0 (e e' : Dir d) (z : Lam d L N) (f : Lam d L N → ℂ) :
    ∑ y, f y * v4g e e' z 0 (y, 1) = f (z + dirVec e) - f z := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff, mul_sub, sum_sub_distrib]

theorem tad_sum_v4g2 (e e' : Dir d) (z : Lam d L N) (f : Lam d L N → ℂ) :
    ∑ y, f y * v4g e e' z 2 (y, 1) = f z := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff]

theorem tad_sum_v4g1 (e e' : Dir d) (z : Lam d L N) (f : Lam d L N → ℂ) :
    ∑ u, v4g e e' z 1 (u, -1) * f u = f (z + dirVec e') - f z := by
  simp [v4g, ev, Pi.single_apply, Prod.ext_iff, sub_mul, sum_sub_distrib]

/-- **`m₁ ℒ_Γ F_C(ψ̄_p, (∇_eψ)(∇_{e'}ψ̄)ψψ̄_z) = tadG C Γ p e e' z`.** -/
theorem tad_mass1_lop_gmono4 (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N)
    (e e' : Dir d) (z : Lam d L N) :
    mass1 (-1) (LopC Γ (FC C (psibar p) (gmono4 e e' z))) = tadG C Γ p e e' z := by
  rw [tad_mass1_lop_FC]
  simp only [tad_mass1_DDD_gmono4]
  have h1 : ∀ u v, ∑ y, C p y * (v4g e e' z 1 (u, -1) * (v4g e e' z 0 (y, 1) * v4g e e' z 2 (v, 1) -
      v4g e e' z 2 (y, 1) * v4g e e' z 0 (v, 1))) =
      v4g e e' z 1 (u, -1) * ((∑ y, C p y * v4g e e' z 0 (y, 1)) * v4g e e' z 2 (v, 1) -
        (∑ y, C p y * v4g e e' z 2 (y, 1)) * v4g e e' z 0 (v, 1)) := by
    intro u v
    rw [sum_mul, sum_mul, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun y _ => by ring
  simp only [h1, tad_sum_v4g0, tad_sum_v4g2]
  have h2 : ∀ u, ∑ v, Γ u v * (v4g e e' z 1 (u, -1) * ((C p (z + dirVec e) - C p z) *
      v4g e e' z 2 (v, 1) - C p z * v4g e e' z 0 (v, 1))) =
      v4g e e' z 1 (u, -1) * ((C p (z + dirVec e) - C p z) * (∑ v, Γ u v * v4g e e' z 2 (v, 1)) -
        C p z * (∑ v, Γ u v * v4g e e' z 0 (v, 1))) := by
    intro u
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun v _ => by ring
  simp only [h2, tad_sum_v4g0, tad_sum_v4g2]
  refine (tad_sum_v4g1 e e' z _).trans ?_
  unfold tadG
  ring

/-! ### Homogeneity and `e^{ℒ_Γ}` -/

theorem tad_lop_eq_zero {k : ℕ} (hk : k ≤ 1) {G : Alg d L N} (hG : IsHom k G)
    (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) : LopC Γ G = 0 := by
  rw [LopC_apply]
  refine sum_eq_zero fun u _ => sum_eq_zero fun v _ => ?_
  have h0 : IsHom 0 (D (u, -1) G) := by
    have := hG.D (u, -1)
    rwa [show k - 1 = 0 by omega] at this
  rw [h0.D_zero, smul_zero]

theorem tad_expLC_of_sq (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) {G : Alg d L N}
    (h : LopC Γ (LopC Γ G) = 0) : expLC Γ G = G + LopC Γ G := by
  rw [expLC_of_cube Γ (by rw [h, map_zero]), h, smul_zero, add_zero]

theorem tad_isHom_FC_psibar (C : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) {n : ℕ}
    {B : Alg d L N} (hB : IsHom n B) : IsHom (n - 1) (FC C (psibar p) B) := by
  rw [FC_psibar]
  exact IsHom.sum _ fun y _ => (hB.D (y, 1)).smul _

/-- The tadpole functional `B ↦ m₁(e^{ℒ_Γ} F_C(ψ̄_p, B)) - m₁(F_C(ψ̄_p, B))`. -/
def tadL (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) : Alg d L N →ₗ[ℂ] ℂ :=
  (mass1L (-1)).comp ((expLC Γ - LinearMap.id).comp (FCr C (psibar p)))

theorem tadL_apply (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) (B : Alg d L N) :
    tadL C Γ p B = mass1 (-1) (expLC Γ (FC C (psibar p) B)) - mass1 (-1) (FC C (psibar p) B) := by
  show mass1L (-1) (expLC Γ (FC C (psibar p) B) - FC C (psibar p) B) = _
  rw [map_sub]; rfl

theorem tadL_gmono4 (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) (e e' : Dir d)
    (z : Lam d L N) : tadL C Γ p (gmono4 e e' z) = tadG C Γ p e e' z := by
  have h3 : IsHom 3 (FC C (psibar p) (gmono4 e e' z)) := tad_isHom_FC_psibar C p (isHom_gmono4 e e' z)
  have h1 : IsHom 1 (LopC Γ (FC C (psibar p) (gmono4 e e' z))) := h3.lop Γ
  rw [tadL_apply, tad_expLC_of_sq Γ (tad_lop_eq_zero le_rfl h1 Γ), mass1_add, add_sub_cancel_left,
    tad_mass1_lop_gmono4]

theorem tadL_pair (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p s t : Lam d L N) :
    tadL C Γ p (psi s * psibar t) = 0 := by
  have h2 : IsHom 2 (psi s * psibar t : Alg d L N) :=
    (isHom_ι (ev ((s, 1) : Sf (Lam d L N)))).mul (isHom_ι (ev ((t, -1) : Sf (Lam d L N))))
  have h1 : IsHom 1 (FC C (psibar p) (psi s * psibar t)) := tad_isHom_FC_psibar C p h2
  rw [tadL_apply, expLC_eq_self Γ (tad_lop_eq_zero le_rfl h1 Γ), sub_self]

theorem tadL_one (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) :
    tadL C Γ p 1 = 0 := by
  rw [tadL_apply, FC_one_right, map_zero, sub_self]

/-- `∑_i ∑_z ½ ∑_{e = ±e_i} tadG C Γ p e e z`. -/
def tauC (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) : ℂ :=
  ∑ i : Fin d, ∑ z, (1 / 2 : ℂ) * (tadG C Γ p (Sum.inl i) (Sum.inl i) z +
    tadG C Γ p (Sum.inr i) (Sum.inr i) z)

theorem tadL_mono4s (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N) (i : Fin d) :
    tadL C Γ p (mono4sSet i i univ) = ∑ z, (1 / 2 : ℂ) * (tadG C Γ p (Sum.inl i) (Sum.inl i) z +
      tadG C Γ p (Sum.inr i) (Sum.inr i) z) := by
  rw [mono4sSet, map_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [mono4s_diag, map_smul, map_sum, Fin.sum_univ_two]
  simp only [pmdir, Matrix.cons_val_zero, Matrix.cons_val_one, tadL_gmono4,
    smul_eq_mul]

/-- **The tadpole of `F_C(ψ̄_p, V_κ(Λ))`**:
`m₁(e^{ℒ_Γ} F_C(ψ̄_p, V_κ(Λ))) - m₁(F_C(ψ̄_p, V_κ(Λ))) = g · tauC C Γ p`. -/
theorem mass1_expLC_FC_psibar_Vcoup (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N)
    (κ : Step2.Coup) :
    mass1 (-1) (expLC Γ (FC C (psibar p) (Step2.Vcoup κ univ))) -
        mass1 (-1) (FC C (psibar p) (Step2.Vcoup κ univ)) = κ.g * tauC C Γ p := by
  rw [← tadL_apply]
  have hpair : ∀ M : Mono d, tadL C Γ p (monoSet M univ) = (if M = Mono.c then 1 else 0) * 0 :=
    stencil_sum (tadL C Γ p) (fun _ _ => 0) 0 (fun s t => tadL_pair C Γ p s t)
      (fun _ _ => by simp)
  rw [Step2.Vcoup, Step2.unif, map_add, map_add, map_smul, tadL_one, smul_zero, zero_add,
    map_sum, map_sum]
  simp only [map_sum, map_smul, hpair, smul_eq_mul, mul_zero, sum_const_zero, zero_add]
  have hE : ∀ i : Fin d, ∑ k : Fin d, Step2.coupE κ i k * tadL C Γ p (mono4sSet i k univ) =
      κ.g * tadL C Γ p (mono4sSet i i univ) := fun i => by
    rw [Fintype.sum_eq_single i (fun k hk => by simp [Step2.coupE, Ne.symm hk])]
    simp [Step2.coupE]
  simp only [hE, tadL_mono4s, tauC, mul_sum]

/-- **The one-loop tadpole of the observable map** (Case (1)):
`m₁(e^{ℒ_Γ} F_C(β ψ̄_a, V_κ(Λ) + r)) - m₁(F_C(β ψ̄_a, V_κ(Λ) + r)) = β g tauC C Γ a`. -/
theorem tad_FC_one (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) (κ : Step2.Coup)
    (r β : ℂ) :
    mass1 (-1) (expLC Γ (FC C (β • psibar a) (Step2.Vcoup κ univ + r • (1 : Alg d L N)))) -
        mass1 (-1) (FC C (β • psibar a) (Step2.Vcoup κ univ + r • (1 : Alg d L N))) =
      β * (κ.g * tauC C Γ a) := by
  rw [FC_smul_left, FC_add_right, FC_smul_right, FC_one_right, smul_zero, add_zero, map_smul,
    mass1_smul, mass1_smul, ← mul_sub, mass1_expLC_FC_psibar_Vcoup]

/-! ### Bilinearity and the translation-invariant value -/

section Bilin

variable (C C' Γ Γ' : Matrix (Lam d L N) (Lam d L N) ℂ) (p : Lam d L N)

theorem tadG_add_left (e e' : Dir d) (z : Lam d L N) :
    tadG (C + C') Γ p e e' z = tadG C Γ p e e' z + tadG C' Γ p e e' z := by
  simp only [tadG, Matrix.add_apply]; ring

theorem tadG_add_right (e e' : Dir d) (z : Lam d L N) :
    tadG C (Γ + Γ') p e e' z = tadG C Γ p e e' z + tadG C Γ' p e e' z := by
  simp only [tadG, Matrix.add_apply]; ring

theorem tauC_add_left : tauC (C + C') Γ p = tauC C Γ p + tauC C' Γ p := by
  unfold tauC
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  rw [tadG_add_left, tadG_add_left]; ring

theorem tauC_add_right : tauC C (Γ + Γ') p = tauC C Γ p + tauC C Γ' p := by
  unfold tauC
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  rw [tadG_add_right, tadG_add_right]; ring

theorem tauC_zero_left : tauC (0 : Matrix (Lam d L N) (Lam d L N) ℂ) Γ p = 0 := by
  simp [tauC, tadG]

theorem tauC_zero_right : tauC C (0 : Matrix (Lam d L N) (Lam d L N) ℂ) p = 0 := by
  simp [tauC, tadG]

theorem tauC_sum_left {ι' : Type*} (s : Finset ι') (Cs : ι' → Matrix (Lam d L N) (Lam d L N) ℂ) :
    tauC (∑ k ∈ s, Cs k) Γ p = ∑ k ∈ s, tauC (Cs k) Γ p := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, tauC_zero_left]
  | insert k s hk ih => rw [sum_insert hk, sum_insert hk, tauC_add_left, ih]

/-- **The translation-invariant value**: `tauC C Γ p = 2 d δ ∑_z C(p, z)` if `Γ(x,x) = c₀` and
`Γ(x+e,x) = Γ(x,x+e) = c₀ + δ`. -/
theorem tauC_TI (c₀ δ : ℂ) (hc : ∀ x, Γ x x = c₀) (hδ : ∀ x e, Γ (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, Γ x (x + dirVec e) = c₀ + δ) :
    tauC C Γ p = 2 * d * δ * ∑ z, C p z := by
  have hG : ∀ (e : Dir d) z, tadG C Γ p e e z =
      δ * (C p (z + dirVec e) - C p z) + 2 * δ * C p z := by
    intro e z
    unfold tadG
    rw [hc, hc, hδ, hδ']
    ring
  have hS : ∀ e : Dir d, ∑ z, tadG C Γ p e e z = 2 * δ * ∑ z, C p z := by
    intro e
    simp only [hG, sum_add_distrib, ← mul_sum, sum_sub_distrib]
    rw [sum_add_right' (fun z => C p z) (dirVec e), sub_self, mul_zero, zero_add]
  unfold tauC
  have : ∀ i : Fin d, ∑ z, (1 / 2 : ℂ) * (tadG C Γ p (Sum.inl i) (Sum.inl i) z +
      tadG C Γ p (Sum.inr i) (Sum.inr i) z) = 2 * δ * ∑ z, C p z := by
    intro i
    rw [← mul_sum, sum_add_distrib, hS, hS]; ring
  rw [sum_congr rfl fun i _ => this i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Bilin

end

end Obs2
