import Step2.Coup.CoupStep
import Grassmann.Absorb

-- Merged from `Step2/Rescale.lean` (phase 3).
section

/-!
# Field rescaling (`h02uv-outline.tex`, Lemma `lem:C3`(iii))

`σ_λ ψ = λ ψ`, `σ_λ ψ̄ = λ ψ̄` (`sig`). Then `σ_λ 𝔼_{λ²Γ} θ = 𝔼_Γ θ σ_λ` (`expLC_sig`) and
`⟨σ_λ F⟩_Γ = ⟨F⟩_{λ²Γ}` (`omegaC_sig`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The field rescaling `ψ ↦ λψ`, `ψ̄ ↦ λψ̄`. -/
def sig (r : ℂ) : N Λ →ₐ[ℂ] N Λ := ExteriorAlgebra.map (r • LinearMap.id)

theorem sig_ψ (r : ℂ) (a : Sf Λ) : sig r (ψ a) = r • ψ a := by
  rw [sig, ψ, ExteriorAlgebra.map_apply_ι]; simp

theorem D_sig (r : ℂ) (a : Sf Λ) (F : N Λ) : D a (sig r F) = r • sig r (D a F) := by
  rw [sig, D_map]
  have : coord a ∘ₗ (r • LinearMap.id : V Λ →ₗ[ℂ] V Λ) = r • coord a := by
    ext v; simp
  rw [this, map_smul, LinearMap.smul_apply, map_smul]; rfl

theorem LopC_sig (C : Matrix Λ Λ ℂ) (r : ℂ) (F : N Λ) :
    LopC C (sig r F) = sig r (LopC ((r ^ 2) • C) F) := by
  simp only [LopC_apply, D_sig, map_smul, map_sum, smul_smul, Matrix.smul_apply, smul_eq_mul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1; ring

theorem expLC_sig (C : Matrix Λ Λ ℂ) (r : ℂ) (F : N Λ) :
    expLC C (sig r F) = sig r (expLC ((r ^ 2) • C) F) := by
  have hc : LopC C ∘ₗ (sig r).toLinearMap = (sig r).toLinearMap ∘ₗ LopC ((r ^ 2) • C) :=
    LinearMap.ext fun G => LopC_sig C r G
  have h := Module.End.commute_exp_left_of_commute (LopC_isNilpotent ((r ^ 2) • C))
    (LopC_isNilpotent C) hc
  exact LinearMap.congr_fun h F

theorem eps_sig (r : ℂ) (F : N Λ) : ε (sig r F) = ε F := algebraMapInv_map _ F

/-- **`⟨σ_λ F⟩_Γ = ⟨F⟩_{λ²Γ}`.** -/
theorem omegaC_sig (C : Matrix Λ Λ ℂ) (r : ℂ) (F : N Λ) :
    omegaC C (sig r F) = omegaC ((r ^ 2) • C) F := by
  rw [omegaC, expLC_sig, eps_sig, omegaC]

end General

end

end Step2

end

/-!
# The full step: absorption, normalisation, and the map (`h02uv-outline.tex`, `prop:C3`)

* `Vcoup_grad`: on the torus, `V_{(z,y,ζm²,0)}(Λ) = ζ (ψ, A ψ̄)`, `A = -Δ + m²`, `ζ = z + y`
  (summation by parts). Hence `V_κ(Λ) = V_{κ♭}(Λ) + ζ (ψ, Aψ̄)` with `κ♭ = (0, 0, ν - ζm², g)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- `A = -Δ + m²` as a complex matrix. -/
def Aop (msq : ℝ) : Matrix (Lam d L N) (Lam d L N) ℂ :=
  fun x y => (negLap x y : ℂ) + (msq : ℂ) * (if x = y then 1 else 0)

/-- `(ψ, A ψ̄) = ∑_{x,y} A_{xy} ψ_x ψ̄_y`. -/
def Qgrad (msq : ℝ) : Alg d L N := ∑ x, ∑ y, Aop msq x y • (psi x * psibar y)

/-! ### Summation by parts -/

/-- `∑_x ψ_x ψ̄_{x+e}`. -/
def Pb (e : Dir d) : Alg d L N := ∑ x, psi x * psibar (x + dirVec e)

/-- `∑_x ψ_x ψ̄_x`. -/
def S0 : Alg d L N := ∑ x : Lam d L N, psi x * psibar x

theorem dirVec_opp (i : Fin d) :
    (dirVec (Sum.inr i) : Lam d L N) = -dirVec (Sum.inl i) := rfl

theorem sum_shift_psi (v : Lam d L N) :
    ∑ x : Lam d L N, psi (x + v) * psibar x = ∑ x : Lam d L N, psi x * psibar (x + -v) := by
  refine Fintype.sum_equiv (Equiv.addRight v) _ _ fun x => ?_
  simp [add_neg_cancel_right]

theorem sum_shift_both (v : Lam d L N) :
    ∑ x : Lam d L N, psi (x + v) * psibar (x + v) = S0 :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ fun x => rfl

theorem monoSet_a2_univ (i : Fin d) :
    monoSet (Mono.a2 s(i, i)) (univ : Finset (Lam d L N)) =
      Pb (Sum.inl i) + Pb (Sum.inr i) - 2 • S0 := by
  simp only [monoSet, monoAt_a2, sub_mul, sum_add_distrib, sum_sub_distrib]
  rw [sum_shift_psi, sum_shift_psi, ← dirVec_opp, show -(dirVec (Sum.inr i) : Lam d L N) =
    dirVec (Sum.inl i) by rw [dirVec_opp, neg_neg]]
  simp only [Pb, S0]
  abel

theorem monoSet_b2_univ (i : Fin d) :
    monoSet (Mono.b2 s(i, i)) (univ : Finset (Lam d L N)) =
      Pb (Sum.inl i) + Pb (Sum.inr i) - 2 • S0 := by
  simp only [monoSet, monoAt_b2, mul_sub, sum_add_distrib, sum_sub_distrib, Pb, S0]
  abel

theorem monoSet_m2_univ (i : Fin d) :
    monoSet (Mono.m2 i i) (univ : Finset (Lam d L N)) =
      -(Pb (Sum.inl i) + Pb (Sum.inr i) - 2 • S0) := by
  simp only [monoSet, monoAt_m2, ← smul_sum, mul_sub, sub_mul, sum_add_distrib, sum_sub_distrib,
    sum_shift_both]
  rw [sum_shift_psi, sum_shift_psi, ← dirVec_opp, show -(dirVec (Sum.inr i) : Lam d L N) =
    dirVec (Sum.inl i) by rw [dirVec_opp, neg_neg]]
  simp only [Pb, S0]
  module

theorem monoSet_c_univ :
    monoSet (Mono.c : Mono d) (univ : Finset (Lam d L N)) = S0 := by
  simp only [monoSet, monoAt_c, S0]

theorem Qgrad_eq (msq : ℝ) :
    Qgrad (d := d) (L := L) (N := N) msq =
      ((2 * d : ℂ) + msq) • S0 - ∑ e : Dir d, Pb e := by
  have h1 : ∀ x : Lam d L N, ∑ y, Aop msq x y • (psi x * psibar y) =
      ((2 * d : ℂ) + msq) • (psi x * psibar x) - ∑ e : Dir d, psi x * psibar (x + dirVec e) := by
    intro x
    have hA : ∀ y, Aop msq x y = ((2 * d : ℂ) + msq) * (if x = y then 1 else 0) -
        ∑ e : Dir d, (if y = x + dirVec e then 1 else 0) := by
      intro y
      simp only [Aop, negLap]
      push_cast [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]
      ring
    simp only [hA, sub_smul, sum_sub_distrib, Finset.sum_smul, mul_ite, mul_one, mul_zero,
      ite_smul, zero_smul, one_smul, sum_ite_eq, mem_univ, if_true]
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, if_true]
  rw [Qgrad, sum_congr rfl fun x _ => h1 x, sum_sub_distrib, ← smul_sum, sum_comm]
  rfl

/-- **Summation by parts**: `V_{(z,y,ζm²,0)}(Λ) = ζ (ψ, Aψ̄)` with `ζ = z + y`. -/
theorem Vcoup_grad (msq : ℝ) (z y : ℂ) :
    Vcoup ⟨z, y, (z + y) * msq, 0⟩ (univ : Finset (Lam d L N)) = (z + y) • Qgrad msq := by
  rw [Vcoup, unif, zero_smul, zero_add, sum_mono]
  simp only [coupC, coupE, ite_smul, zero_smul, sum_sym2_diag, sum_const_zero, add_zero,
    ite_self]
  have hm : (∑ i : Fin d, ∑ k : Fin d, if i = k then z • monoSet (Mono.m2 i k)
      (univ : Finset (Lam d L N)) else 0) = ∑ i, z • monoSet (Mono.m2 i i) univ := by
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp
  rw [hm, Qgrad_eq, Fintype.sum_sum_type]
  simp only [monoSet_c_univ, monoSet_a2_univ, monoSet_b2_univ, monoSet_m2_univ]
  have e : ∀ i : Fin d, (Pb (Sum.inl i) + Pb (Sum.inr i) - 2 • S0 : Alg d L N) =
      Pb (Sum.inl i) + Pb (Sum.inr i) - (2 : ℂ) • S0 := fun i => by
    rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
  simp only [e, smul_sub, smul_add, smul_neg, sum_add_distrib, sum_sub_distrib, sum_neg_distrib,
    ← smul_sum, sum_const, card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  module

/-! ### The rescaling on even elements -/

section Sig

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `σ_λ` on even elements. -/
def sigE (r : ℂ) : EvR Λ →ₐ[ℂ] EvR Λ := mapE (r • LinearMap.id)

@[simp] theorem coe_sigE (r : ℂ) (F : EvR Λ) : (sigE r F : Grassmann.N Λ) = sig r (F : Grassmann.N Λ) := rfl

theorem sig_sig (r s : ℂ) (F : Grassmann.N Λ) : sig r (sig s F) = sig (r * s) F := by
  rw [sig, sig, sig, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  congr 2
  rw [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, smul_smul, mul_comm]

omit [DecidableEq Λ] [Fintype Λ] in
theorem sig_one (F : Grassmann.N Λ) : sig 1 F = F := by
  rw [sig, one_smul, ExteriorAlgebra.map_id, AlgHom.id_apply]

theorem coe_gexp_eq (F : EvR Λ) (hF : ε (F : Grassmann.N Λ) = 0) :
    (gexp F : Grassmann.N Λ) = IsNilpotent.exp (F : Grassmann.N Λ) :=
  IsNilpotent.map_exp (isNilpotent_of_ε' hF) (Ev Λ).val

theorem sigE_gexp (r : ℂ) (F : EvR Λ) (hF : ε (F : Grassmann.N Λ) = 0) :
    sigE r (gexp F) = gexp (sigE r F) :=
  IsNilpotent.map_exp (isNilpotent_of_ε' hF) (sigE r)

theorem eps_sigE (r : ℂ) (F : EvR Λ) : ε (sigE r F : Grassmann.N Λ) = ε (F : Grassmann.N Λ) := eps_sig r _

end Sig

/-! ### Splitting off the gradient part -/

section Factor

variable (j : ℕ)

theorem Kext_bpow_mul (E : (Fin d → ℕ) → EvR (Lam d L N)) (K : Act d L N)
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    Kext j (fun Y => bpow j E Y * K Y) X = bpow j E X * Kext j K X := by
  classical
  rw [Kext, prod_mul_distrib, Kext]
  congr 1
  conv_rhs => rw [bpow, show blocks j X = ((Comp j X).biUnion id).image (blk j) by
    rw [biUnion_comp hX]; rfl]
  rw [biUnion_image, prod_biUnion]
  · rfl
  · intro Y hY Y' hY' hne
    exact disjoint_blocks (isConn_of_mem_comp hX hY).1 (isConn_of_mem_comp hX hY').1
      (disjoint_of_not_touch (not_touch_of_mem_comp hX hY hY' hne))

theorem eps_neg_coe {Λ : Type*} [DecidableEq Λ] {F : EvR Λ} (hF : ε (F : Grassmann.N Λ) = 0) :
    ε ((-F : EvR Λ) : Grassmann.N Λ) = 0 := by
  rw [NegMemClass.coe_neg, map_neg, hF, neg_zero]

/-- **`Z(V♭ + Δ, 𝒲, K) = e^{-Δ(Λ)} Z(V♭, 𝒲, K♭)`** with `K♭(X) = e^{Δ(X)} K(X)`. -/
theorem gZ_factor (Vf Δ W : Fam d L N) (K : Act d L N) (hVf : ∀ b, ε (Vf b : Alg d L N) = 0)
    (hΔ : ∀ b, ε (Δ b : Alg d L N) = 0) :
    gZ j (Ib (fun b => Vf b + Δ b) W) K = bpow j (fun b => gexp (-Δ b)) univ *
      gZ j (Ib Vf W) (fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y) := by
  rw [gZ, gZ, mul_sum]
  refine sum_congr rfl fun X hX => ?_
  have hXp := (mem_Pj.1 hX).2
  have hc := IsPolymer.sdiff (isPolymer_univ j) hXp
  rw [Kext_bpow_mul j _ K hXp]
  have hI : Ib (fun b => Vf b + Δ b) W = fun b => gexp (-Δ b) * Ib Vf W b := funext fun b => by
    rw [Ib, Ib, neg_add, gexp_add (eps_neg_coe (hVf b)) (eps_neg_coe (hΔ b))]; ring
  have hU : bpow j (fun b => gexp (-Δ b)) univ =
      bpow j (fun b => gexp (-Δ b)) (univ \ X) * bpow j (fun b => gexp (-Δ b)) X := by
    rw [← bpow_union j _ hc hXp sdiff_disjoint, sdiff_union_of_subset (subset_univ _)]
  have hinv : bpow j (fun b => gexp (-Δ b)) X * bpow j (fun b => gexp (Δ b)) X = 1 := by
    rw [bpow, bpow, ← prod_mul_distrib]
    refine prod_eq_one fun b _ => ?_
    rw [← gexp_add (eps_neg_coe (hΔ b)) (hΔ b), neg_add_cancel, gexp_zero]
  rw [hI, bpow, prod_mul_distrib, ← bpow, ← bpow, hU]
  linear_combination (-(bpow j (fun b => gexp (-Δ b)) (univ \ X) * bpow j (Ib Vf W) (univ \ X) *
    Kext j K X)) * hinv

theorem sum_Vcoup_blocks (κ : Coup) :
    ∑ b ∈ blockIdx (d := d) (L := L) (N := N) j, Vcoup κ (blockSet (L := L) (N := N) j b) =
      Vcoup κ (univ : Finset (Lam d L N)) := by
  simp only [Vcoup]
  rw [unif_sum _ _ _ _ _ (pairwiseDisjoint_blockSet j _), mul_zero, blockIdx,
    biUnion_blocks (isPolymer_univ j)]

theorem sigE_gZ (r : ℂ) (V W : Fam d L N) (K : Act d L N) (hV : ∀ b, ε (V b : Alg d L N) = 0) :
    sigE r (gZ j (Ib V W) K) =
      gZ j (Ib (fun b => sigE r (V b)) (fun b => sigE r (W b))) (fun Y => sigE r (K Y)) := by
  rw [gZ, gZ, map_sum]
  refine sum_congr rfl fun X _ => ?_
  rw [map_mul, bpow, bpow, map_prod, Kext, Kext, map_prod]
  congr 1
  refine prod_congr rfl fun b _ => ?_
  rw [Ib, Ib, map_mul, sigE_gexp _ _ (eps_neg_coe (hV b)), map_neg, map_add, map_one]

/-- `∏_B e^{-Δ(B)} = e^{-ζ (ψ, Aψ̄)}` when `Δ(B) = V_{(z,y,ζm²,0)}(B)`, `ζ = z + y`. -/
theorem coe_bpow_gexp_grad (msq : ℝ) (z y : ℂ) (Δ : Fam d L N)
    (hΔ : ∀ b, (Δ b : Alg d L N) = Vcoup ⟨z, y, (z + y) * msq, 0⟩ (blockSet (L := L) (N := N) j b)) :
    (bpow j (fun b => gexp (-Δ b)) univ : Alg d L N) =
      IsNilpotent.exp (-((z + y) • ∑ x, ∑ x', Aop msq x x' • (psi x * psibar x'))) := by
  have hε : ∀ b, ε (Δ b : Alg d L N) = 0 := fun b => by rw [hΔ]; exact eps_Vcoup _ _
  have hs : ε (((∑ b ∈ blocks j (univ : Finset (Lam d L N)), -Δ b : EvR (Lam d L N))) : Alg d L N) = 0 := by
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    exact sum_eq_zero fun b _ => eps_neg_coe (hε b)
  rw [bpow, ← gexp_sum_of_ε _ _ fun b _ => eps_neg_coe (hε b), coe_gexp_eq _ hs, sum_neg_distrib,
    NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
  simp only [hΔ]
  rw [show blocks j univ = blockIdx (d := d) (L := L) (N := N) j from rfl, sum_Vcoup_blocks,
    Vcoup_grad, Qgrad]

/-- **The full step at the level of expectations** (`prop:C3`, algebraic part): with
`V = V♭ + Δ`, `Δ(B) = V_{(z,y,ζm²,0)}(B)`, `Γ(1 + ζAΓ)^{-1} = Γ₁ + Γ₂` and `λ s = 1`,
`⟨Z(V, 𝒲, K)⟩_Γ = det(1 + ζAΓ) ⟨𝔼_{λ²Γ₁} θ Z(σ_s V♭, σ_s 𝒲, σ_s K♭)⟩_{λ²Γ₂}`. -/
theorem omegaC_gZ_step (msq : ℝ) (z y r s : ℂ) (hrs : r * s = 1) (Vf Δ W : Fam d L N)
    (K : Act d L N) (hVf : ∀ b, ε (Vf b : Alg d L N) = 0)
    (hΔ : ∀ b, (Δ b : Alg d L N) = Vcoup ⟨z, y, (z + y) * msq, 0⟩ (blockSet (L := L) (N := N) j b))
    (Γ Γ₁ Γ₂ : Matrix (Lam d L N) (Lam d L N) ℂ)
    (hT : IsUnit (1 + (z + y) • (Aop msq * Γ)).det)
    (hΓ : Γ * (1 + (z + y) • (Aop msq * Γ))⁻¹ = Γ₁ + Γ₂) :
    omegaC Γ (gZ j (Ib (fun b => Vf b + Δ b) W) K : Alg d L N) =
      (1 + (z + y) • (Aop msq * Γ)).det * omegaC (r ^ 2 • Γ₂)
        (ECCE (r ^ 2 • Γ₁) (thetaE (gZ j (Ib (fun b => sigE s (Vf b)) (fun b => sigE s (W b)))
          (fun Y => sigE s (bpow j (fun b => gexp (Δ b)) Y * K Y)))) : Alg d L N) := by
  have hε : ∀ b, ε (Δ b : Alg d L N) = 0 := fun b => by rw [hΔ]; exact eps_Vcoup _ _
  rw [gZ_factor j Vf Δ W K hVf hε, MulMemClass.coe_mul, coe_bpow_gexp_grad j msq z y Δ hΔ,
    omegaC_onestep _ _ _ _ _ hT hΓ, ECC_theta, ← sigE_gZ j s _ _ _ hVf, coe_ECCE, coe_thetaE,
    ECC_theta, coe_sigE, ← omegaC_sig, ← expLC_sig, sig_sig, hrs, sig_one]

/-- **The full step** (`prop:C3`, algebraic part): absorption, rescaling and the `Step2` map with
`C' = λ²Γ₁`, applied to the rescaled data `(σ_s V♭, σ_s 𝒲, σ_s K♭)`. -/
theorem omegaC_full_step (msq : ℝ) (z y r s : ℂ) (hrs : r * s = 1) (Vf Δ W : Fam d L N)
    (K : Act d L N) (hVf : ∀ b, ε (Vf b : Alg d L N) = 0)
    (hΔ : ∀ b, (Δ b : Alg d L N) = Vcoup ⟨z, y, (z + y) * msq, 0⟩ (blockSet (L := L) (N := N) j b))
    (Γ Γ₁ Γ₂ : Matrix (Lam d L N) (Lam d L N) ℂ)
    (hT : IsUnit (1 + (z + y) • (Aop msq * Γ)).det)
    (hΓ : Γ * (1 + (z + y) • (Aop msq * Γ))⁻¹ = Γ₁ + Γ₂) {ℓ : ℝ}
    (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) (hjN : j + 1 < N) (hC : GoodCov2 j ℓ (r ^ 2 • Γ₁))
    (hV : InF j fun b => sigE s (Vf b)) (hW : InF j fun b => sigE s (W b))
    (hK : InK2 j fun Y => sigE s (bpow j (fun b => gexp (Δ b)) Y * K Y)) :
    let C' := r ^ 2 • Γ₁
    let Vs : Fam d L N := fun b => sigE s (Vf b)
    let Ws : Fam d L N := fun b => sigE s (W b)
    let Ks : Act d L N := fun Y => sigE s (bpow j (fun b => gexp (Δ b)) Y * K Y)
    omegaC Γ (gZ j (Ib (fun b => Vf b + Δ b) W) K : Alg d L N) =
      (1 + (z + y) • (Aop msq * Γ)).det * omegaC (r ^ 2 • Γ₂)
        ((∑ U ∈ Pj (j + 1) univ, bpow j (Ip j C' Vs Ws Ks) (univ \ U) *
          (Complex.exp (-uX j C' Vs Ws Ks U) • Kext (j + 1) (Kplus j C' Vs Ws Ks) U) :
            EvR (Lam d L N)) : Alg d L N) := by
  intro C' Vs Ws Ks
  rw [omegaC_gZ_step j msq z y r s hrs Vf Δ W K hVf hΔ Γ Γ₁ Γ₂ hT hΓ,
    stepK_ZVK (j := j) (C := C') (V := Vs) (W := Ws) (K := Ks) hd hL hjN hC hV hW (fun b => by rw [eps_sigE]; exact hVf b) hK]

end Factor

end

end Step2
