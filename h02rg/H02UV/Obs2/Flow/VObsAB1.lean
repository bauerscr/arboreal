import Obs2.Loc.LocABRepro
import Obs2.Pair.PairRed
import Obs2.Est.ErrAB

/-!
# The `ab` coupling `V'_{ab}`: coefficients, Pauli defects, norms

Along the reduced history the `ab` part of `V'(B)` is a `U(1)`-invariant element of `𝒩({a,b})`, hence
(`eq_proj0_of_ab`) of the form

  `F = ε + ∑_{u,v∈{a,b}} c_{uv}ψ̄_uψ_v + M₄ψ̄_aψ_aψ̄_bψ_b`.

With `δ = ψ_b − ψ_a` this is (**`proj0_grad`**, `a ≠ b`)

  `F = ε + m₂(F)ψ̄_aψ_a + (c_{ab}+c_{bb})ψ̄_aδ + (c_{ba}+c_{bb})δ̄ψ_a + c_{bb}δ̄δ + M₄ψ̄_aψ_aδ̄δ`,

the mass `m₂(F) = ∑c_{uv}` plus a gradient part (`gradAB`). In this file:

* `expLC_m2_eq`: `e^{ℒ_C}(ψ̄_uψ_v) = ψ̄_uψ_v + C(u,v)`;
* **`pauliDef2_of_ab`**: the `m₂` Pauli defect is carried by the quartic coefficient only,
  `𝔡₂_C(F) = M₄(F)(C(a,a) + C(b,b) − C(a,b) − C(b,a))`;
* **`pauliDef_of_ab`**: the `ε` Pauli defect is the determinant defect of `M₄` plus the gradient
  defects of the quadratic coefficients,
  `𝔡_C^a(F) = M₄(F)(C(a,a)C(b,b) − C(a,b)C(b,a)) + ∑_{u,v}c_{uv}(C(u,v) − C(a,a))`;
* **`tNorm_of_ab_le`**: `‖F‖_{T_h(ℓ)} ≤ |ε| + |m₂|ℓ² + (|c_{ab}+c_{bb}| + |c_{ba}+c_{bb}|)ℓ·g +
  |c_{bb}|g² + |M₄|ℓ²g²` with `g = |e|₁ℓ/h` the norm of `δ` (`tNorm_dlt_le`): the gradient and
  quartic parts carry the decaying factor `g`;
* `dAB_eq_grad`: the gradient part `D_j` of `MuChainAB` is `gradAB` of the total `V'(Λ)_{ab}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

/-- The quadratic coefficient `c_{uv}(F) = F_{(u,-)(v,+)}`. -/
def cfAB2 (u v : Lam d L N) (F : Alg d L N) : ℂ := coeff F ![(u, -1), (v, 1)]

/-- The quartic coefficient `M₄(F) = F_{(a,-)(a,+)(b,-)(b,+)}`. -/
def cfAB4 (a b : Lam d L N) (F : Alg d L N) : ℂ := coeff F ![(a, -1), (a, 1), (b, -1), (b, 1)]

theorem cfAB2_add (u v : Lam d L N) (F G : Alg d L N) :
    cfAB2 u v (F + G) = cfAB2 u v F + cfAB2 u v G := coeff_add _ _ _

theorem cfAB4_add (a b : Lam d L N) (F G : Alg d L N) :
    cfAB4 a b (F + G) = cfAB4 a b F + cfAB4 a b G := coeff_add _ _ _

theorem cfAB2_smul (u v : Lam d L N) (r : ℂ) (F : Alg d L N) :
    cfAB2 u v (r • F) = r * cfAB2 u v F := coeff_smul _ _ _

theorem cfAB4_smul (a b : Lam d L N) (r : ℂ) (F : Alg d L N) :
    cfAB4 a b (r • F) = r * cfAB4 a b F := coeff_smul _ _ _

theorem m4_eq_pbp_mul (a b : Lam d L N) : (m4 a b : Alg d L N) = pbp a * pbp b := rfl

/-- `e^{ℒ_C}(ψ̄_uψ_v) = ψ̄_uψ_v + C(u,v)`. -/
theorem expLC_m2_eq (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u v : Lam d L N) :
    expLC C (psibar u * psi v : Alg d L N) = psibar u * psi v + C u v • (1 : Alg d L N) := by
  have h : PM (ev ((v, 1) : Sf (Lam d L N))) (ev (u, -1)) :=
    ⟨fun y => by simp [ev, Prod.ext_iff], fun y => by simp [ev, Prod.ext_iff]⟩
  have e : (psibar u * psi v : Alg d L N) = -(ψ (v, 1) * ψ (u, -1) : Alg d L N) := by
    unfold psibar psi; exact ψ_anticomm _ _
  rw [e, map_neg]
  have := expLC_two C h
  simp only [ψ] at this ⊢
  rw [this, neg_add, neg_smul, neg_neg, pairC_ev]

/-- `e^{ℒ_C}` of the projection. -/
theorem expLC_proj0 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) (F : Alg d L N) :
    expLC C (proj0 a b F) = proj0 a b F +
      (∑ u ∈ ({a, b} : Finset (Lam d L N)), ∑ v ∈ ({a, b} : Finset (Lam d L N)),
        cfAB2 u v F * C u v) • (1 : Alg d L N) +
      cfAB4 a b F • (expLC C (m4 a b) - m4 a b) := by
  unfold proj0
  simp only [map_add, map_sum, map_smul, m2, expLC_m2_eq, smul_add, sum_add_distrib,
    smul_sub, sum_smul, smul_smul]
  rw [show (algebraMap ℂ (Alg d L N)) (ε F) = (algebraMap ℂ (Alg d L N)) (ε F) from rfl]
  have hA : expLC C (algebraMap ℂ (Alg d L N) (ε F)) = algebraMap ℂ (Alg d L N) (ε F) := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, expLC_one']
  rw [hA]
  unfold cfAB2 cfAB4
  abel

theorem mass2_proj0 (a b : Lam d L N) (F : Alg d L N) :
    mass2 (proj0 a b F) = ∑ u ∈ ({a, b} : Finset (Lam d L N)), ∑ v ∈ ({a, b} : Finset (Lam d L N)),
      cfAB2 u v F := by
  unfold proj0
  simp only [mass2_add, mass2_sum, mass2_smul, m2, mass2_m2, mass2_m4, mul_one, mul_zero, add_zero]
  rw [Algebra.algebraMap_eq_smul_one, mass2_smul, mass2_one, mul_zero, zero_add]
  rfl

/-- **The `m₂` Pauli defect on `𝒩({a,b})`**: only the quartic coefficient contributes. -/
theorem pauliDef2_proj0 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) (F : Alg d L N) :
    pauliDef2 C (proj0 a b F) = cfAB4 a b F * (C a a + C b b - C a b - C b a) := by
  rw [pauliDef2, expLC_proj0, mass2_add, mass2_add, mass2_smul, mass2_smul, mass2_one, mass2_sub,
    m4_eq_pbp_mul, mass2_expLC_pbp_mul, ← m4_eq_pbp_mul, mass2_m4]
  ring

theorem pauliDef2_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N} {F : Alg d L N}
    (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    pauliDef2 C F = cfAB4 a b F * (C a a + C b b - C a b - C b a) := by
  rw [eq_proj0_of_ab hN hS, pauliDef2_proj0]
  unfold cfAB4
  rw [coeff_proj0_four]

/-- `ε(e^{ℒ_C}F)` on the projection. -/
theorem eps_expLC_proj0 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) (F : Alg d L N) :
    ε (expLC C (proj0 a b F)) = ε F +
      ∑ u ∈ ({a, b} : Finset (Lam d L N)), ∑ v ∈ ({a, b} : Finset (Lam d L N)), cfAB2 u v F * C u v +
      cfAB4 a b F * (C a a * C b b - C a b * C b a) := by
  rw [expLC_proj0, map_add, map_add, map_smul, map_smul, map_sub, eps_proj0, m4_eq_pbp_mul,
    eps_expLC_pbp_mul, ← m4_eq_pbp_mul, eps_m4, map_one]
  simp only [smul_eq_mul, mul_one, sub_zero]

/-- **The `ε` Pauli defect on `𝒩({a,b})`**: the determinant defect of the quartic coefficient and
the gradient defects of the quadratic ones. -/
theorem pauliDef_proj0 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) (F : Alg d L N) :
    pauliDef C a (proj0 a b F) = cfAB4 a b F * (C a a * C b b - C a b * C b a) +
      ∑ u ∈ ({a, b} : Finset (Lam d L N)), ∑ v ∈ ({a, b} : Finset (Lam d L N)),
        cfAB2 u v F * (C u v - C a a) := by
  rw [pauliDef, eps_expLC_proj0, eps_expLC_proj0]
  simp only [Jmat, Matrix.smul_apply, smul_eq_mul, mul_one]
  simp only [mul_sub, sum_sub_distrib]
  ring

theorem pauliDef_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N} {F : Alg d L N}
    (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    pauliDef C a F = cfAB4 a b F * (C a a * C b b - C a b * C b a) +
      ∑ u ∈ ({a, b} : Finset (Lam d L N)), ∑ v ∈ ({a, b} : Finset (Lam d L N)),
        cfAB2 u v F * (C u v - C a a) := by
  have e := eq_proj0_of_ab hN hS
  have h4 : cfAB4 a b (proj0 a b F) = cfAB4 a b F := coeff_proj0_four a b F
  have h2 : ∀ u ∈ ({a, b} : Finset (Lam d L N)), ∀ v ∈ ({a, b} : Finset (Lam d L N)),
      cfAB2 u v (proj0 a b F) = cfAB2 u v F := by
    intro u hu v hv
    exact coeff_proj0_two a b F (by simpa using hu) (by simpa using hv)
  rw [e, pauliDef_proj0, h4]
  congr 1
  exact sum_congr rfl fun u hu => sum_congr rfl fun v hv => by rw [h2 u hu v hv]

/-! ### The gradient form -/

/-- The gradient part `(c_{ab}+c_{bb})ψ̄_aδ + (c_{ba}+c_{bb})δ̄ψ_a + c_{bb}δ̄δ + M₄ψ̄_aψ_aδ̄δ`. -/
def gradAB (a b : Lam d L N) (F : Alg d L N) : Alg d L N :=
  (cfAB2 a b F + cfAB2 b b F) • (psibar a * dlt a b) +
    (cfAB2 b a F + cfAB2 b b F) • (dbar a b * psi a) +
    cfAB2 b b F • (dbar a b * dlt a b) + cfAB4 a b F • m4 a b

/-- **The gradient form of the projection** (`a ≠ b`). -/
theorem proj0_grad {a b : Lam d L N} (hab : a ≠ b) (F : Alg d L N) :
    proj0 a b F = ε F • (1 : Alg d L N) + mass2 (proj0 a b F) • pbp a + gradAB a b F := by
  rw [mass2_proj0]
  unfold proj0 gradAB pbp
  simp only [sum_pair hab, Algebra.algebraMap_eq_smul_one]
  unfold m2 dbar dlt cfAB2 cfAB4
  simp only [mul_sub, sub_mul, add_smul, smul_sub]
  abel

theorem eq_grad_of_ab {a b : Lam d L N} (hab : a ≠ b) {F : Alg d L N}
    (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    F = ε F • (1 : Alg d L N) + mass2 F • pbp a + gradAB a b F := by
  conv_lhs => rw [eq_proj0_of_ab hN hS]
  rw [proj0_grad hab, ← eq_proj0_of_ab hN hS]

theorem gradAB_add (a b : Lam d L N) (F G : Alg d L N) :
    gradAB a b (F + G) = gradAB a b F + gradAB a b G := by
  unfold gradAB
  simp only [cfAB2_add, cfAB4_add, add_smul]
  abel

theorem gradAB_smul (a b : Lam d L N) (r : ℂ) (F : Alg d L N) :
    gradAB a b (r • F) = r • gradAB a b F := by
  unfold gradAB
  simp only [cfAB2_smul, cfAB4_smul, smul_add, smul_smul, mul_add]

/-- **Norm of the gradient part**: with `g = |e|₁ℓ/h` (the bound of `‖δ‖`),
`‖gradAB F‖ ≤ (|c_{ab}+c_{bb}| + |c_{ba}+c_{bb}|)ℓg + |c_{bb}|g² + |M₄|ℓ²g²`. -/
theorem tNorm_gradAB_le (hd : 1 ≤ d) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (X : Finset (Lam d L N))
    (a b : Lam d L N) (F : Alg d L N) :
    tNorm (Dir d) (pPhi d) h ℓ (gradAB a b F) ≤ ENNReal.ofReal
      ((‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖) * (ℓ * (eN1 X a b * ℓ * h⁻¹)) +
        ‖cfAB2 b b F‖ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹)) +
        ‖cfAB4 a b F‖ * (ℓ * ℓ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹)))) := by
  set g := eN1 X a b * ℓ * h⁻¹ with hg
  have hg0 : 0 ≤ g := by have := eN1_nonneg X a b; positivity
  have h1 : tNorm (Dir d) (pPhi d) h ℓ (psibar a * dlt a b : Alg d L N) ≤ ENNReal.ofReal (ℓ * g) :=
    tn_mul_bound hh hℓ hℓ.le (tNorm_psibar hh hℓ a).le (tNorm_dlt_le hd hh hℓ X a b)
  have h2 : tNorm (Dir d) (pPhi d) h ℓ (dbar a b * psi a : Alg d L N) ≤ ENNReal.ofReal (ℓ * g) := by
    have := tn_mul_bound hh hℓ hg0 (tNorm_dbar_le hd hh hℓ X a b) (tNorm_psi hh hℓ a).le
    rwa [mul_comm g ℓ] at this
  have h3 : tNorm (Dir d) (pPhi d) h ℓ (dbar a b * dlt a b : Alg d L N) ≤ ENNReal.ofReal (g * g) :=
    tn_mul_bound hh hℓ hg0 (tNorm_dbar_le hd hh hℓ X a b) (tNorm_dlt_le hd hh hℓ X a b)
  have h4 := tNorm_m4_le hd hh hℓ X a b
  rw [← hg] at h4
  unfold gradAB
  refine (tNorm_add_le _ _).trans ?_
  refine (add_le_add (tNorm_add_le _ _) (tn_smul_bound h4 le_rfl)).trans ?_
  refine (add_le_add (add_le_add (tNorm_add_le _ _) (tn_smul_bound h3 le_rfl)) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (tn_smul_bound h1 le_rfl) (tn_smul_bound h2 le_rfl))
    le_rfl) le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- **The norm of an element of `𝒩({a,b})`** in terms of its constant, its mass and the gradient
part (`a ≠ b`). -/
theorem tNorm_of_ab_le (hd : 1 ≤ d) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (X : Finset (Lam d L N))
    {a b : Lam d L N} (hab : a ≠ b) {F : Alg d L N}
    (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    tNorm (Dir d) (pPhi d) h ℓ F ≤ ENNReal.ofReal (‖ε F‖ + ‖mass2 F‖ * (ℓ * ℓ) +
      ((‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖) * (ℓ * (eN1 X a b * ℓ * h⁻¹)) +
        ‖cfAB2 b b F‖ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹)) +
        ‖cfAB4 a b F‖ * (ℓ * ℓ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹))))) := by
  have hg0 : 0 ≤ eN1 X a b * ℓ * h⁻¹ := by have := eN1_nonneg X a b; positivity
  have e := eq_grad_of_ab hab hN hS
  suffices key : tNorm (Dir d) (pPhi d) h ℓ (ε F • (1 : Alg d L N) + mass2 F • pbp a +
      gradAB a b F) ≤ _ by rwa [← e] at key
  have h1 : tNorm (Dir d) (pPhi d) h ℓ (ε F • (1 : Alg d L N)) ≤ ENNReal.ofReal ‖ε F‖ := by
    refine tn_smul_bound (r := 1) ?_ (by rw [mul_one])
    rw [ENNReal.ofReal_one]; exact tNorm_one_le hh hℓ
  have h2 : tNorm (Dir d) (pPhi d) h ℓ (mass2 F • pbp a) ≤ ENNReal.ofReal (‖mass2 F‖ * (ℓ * ℓ)) :=
    tn_smul_bound (tNorm_pbp_le hh hℓ a) le_rfl
  refine (tNorm_add_le _ _).trans ?_
  refine (add_le_add (tNorm_add_le _ _) (tNorm_gradAB_le hd hh hℓ X a b F)).trans ?_
  refine (add_le_add (add_le_add h1 h2) le_rfl).trans ?_
  rw [← ENNReal.ofReal_add (norm_nonneg _) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-! ### The gradient part `D_j` of the reduced flow -/

/-! ### The quartic coefficient under `e^{ℒ_C}` -/

theorem isHom_m4 (a b : Lam d L N) : IsHom 4 (m4 a b : Alg d L N) :=
  (isHom_pbp a).mul (isHom_pbp b)

/-- `e^{ℒ_C}` does not change the top coefficient of a homogeneous quartic. -/
theorem cfAB4_expLC_of_isHom4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N)
    {F : Alg d L N} (hF : IsHom 4 F) : cfAB4 a b (expLC C F) = cfAB4 a b F := by
  unfold cfAB4
  rw [expLC_eq_sum', coeff_sum, sum_range_succ', pow_zero, Module.End.one_apply, coeff_smul,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
  rw [sum_eq_zero fun i _ => by
    rw [coeff_smul, (hF.lopPow C (i + 1)) 4 _ (by omega), mul_zero], zero_add]

/-- **`M₄(e^{ℒ_C}F) = M₄(F)`** on `U(1)`-invariant elements of `𝒩({a,b})`. -/
theorem cfAB4_expLC_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N}
    {F : Alg d L N} (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    cfAB4 a b (expLC C F) = cfAB4 a b F := by
  have h4 : cfAB4 a b (proj0 a b F) = cfAB4 a b F := coeff_proj0_four a b F
  have h1 : cfAB4 a b (1 : Alg d L N) = 0 := coeff_one_of_ne' _ (by decide)
  rw [eq_proj0_of_ab hN hS, expLC_proj0, cfAB4_add, cfAB4_add, cfAB4_smul, cfAB4_smul, h1,
    show expLC C (m4 a b) - m4 a b = expLC C (m4 a b) + (-1 : ℂ) • m4 a b by
      rw [neg_one_smul, sub_eq_add_neg], cfAB4_add, cfAB4_smul,
    cfAB4_expLC_of_isHom4 C a b (isHom_m4 a b), h4]
  ring

/-! ### `V_{j+1}(B)_{ab} ∈ 𝒩({a,b})` -/

section StepMem

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

theorem Q2O_ab_mem_pair (b : Fin d → ℕ) :
    (Q2O P j K b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)) := by
  classical
  unfold Q2O
  split_ifs
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    exact Subalgebra.sum_mem _ fun X _ => by rw [LocO2_ab]; exact locABtXY_mem P _ _ _
  · exact zero_mem _

theorem uVpO_ab_mem_pair (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈
    NX ({P.a, P.b} : Set (Lam d L N))) (b : Fin d → ℕ) :
    (uVpO P j C V W K b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)) := by
  rw [uVpO_ab]
  exact sub_mem (sub_mem (expLC_mem_NX C (hV b)) (expLC_mem_NX C (Q2O_ab_mem_pair P j K b)))
    (locABtXY_mem P _ _ _)

theorem VpO_ab_mem_pair (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈
    NX ({P.a, P.b} : Set (Lam d L N))) (b : Fin d → ℕ) :
    (VpO P j C V W K b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)) := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).ab = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
  rw [h1, halg, upO_ab_eq, sub_zero]
  exact sub_mem (uVpO_ab_mem_pair P j C V W K hV b) (Subalgebra.algebraMap_mem _ _)

theorem Vnext2O_ab_mem_pair (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈
    NX ({P.a, P.b} : Set (Lam d L N))) (c' : Fin d → ℕ) :
    (Vnext2O P j C V W K c' : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)) := by
  rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
  exact Subalgebra.sum_mem _ fun b _ => VpO_ab_mem_pair P j C V W K hV b

/-- The total quartic coefficient `M₄ = ∑_BM₄(V(B)_{ab})`. -/
def m4Tot (P : ObsPts d L N) (j : ℕ) (V : OFam .two d L N) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, cfAB4 P.a P.b (V b : SA .two (Lam d L N)).ab

/-- **The `m₂` Pauli defect of `V_{ab}` is the gradient defect of the total quartic coefficient**:
`𝔡₂ = M₄(C(a,a) + C(b,b) − C(a,b) − C(b,a))`. -/
theorem pdefM2_eq_m4Tot (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈
    NX ({P.a, P.b} : Set (Lam d L N))) (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) :
    pdefM2 j C V = m4Tot P j V * (C P.a P.a + C P.b P.b - C P.a P.b - C P.b P.a) := by
  rw [pdefM2, m4Tot, sum_mul]
  exact sum_congr rfl fun b _ => pauliDef2_of_ab C (hV b) (hS b)

/-- **The `ε` Pauli defect of `V_{ab}`**: the determinant defect of `M₄` plus the gradient defects
of the quadratic coefficients. -/
theorem pdefAB2_sub_m4Tot (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈
    NX ({P.a, P.b} : Set (Lam d L N))) (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) :
    pdefAB2 P j C V - m4Tot P j V * (C P.a P.a * C P.b P.b - C P.a P.b * C P.b P.a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ∑ u ∈ ({P.a, P.b} : Finset (Lam d L N)),
        ∑ v ∈ ({P.a, P.b} : Finset (Lam d L N)),
          cfAB2 u v (V b : SA .two (Lam d L N)).ab * (C u v - C P.a P.a) := by
  rw [pdefAB2, m4Tot, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [pauliDef_of_ab C (hV b) (hS b)]
  ring

end StepMem

end

end Obs2
