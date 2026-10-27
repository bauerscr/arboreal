import Grassmann.Doubling
import Grassmann.GaussianC
import Grassmann.Conj

/-!
# The scaled doubling map (two field scales)

`θ_λ F = F(ψ + λ ζ)` (`thetaL`). Then:

* `ECC_theta_scale`: `𝔼_C θ F = 𝔼_{λ^{-2} C} θ_λ F` for `λ ≠ 0` (Gaussian rescaling of the
  fluctuation field);
* `tNorm_thetaL_le`: `‖θ_λ F‖_{T(ℓ ⊔ ℓ)} ≤ ‖F‖_{T((1 + λ) ℓ)}` for `λ ≥ 0`.

Together with a Gram bound at `ℓ_C = λ ℓ'` and `lem:pauli`, these give the expectation bound
with an output field scale `ℓ'` and an input field scale `ℓ` when `ℓ' + ℓ_C ≤ 2ℓ`.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset

variable {Λ : Type*} [DecidableEq Λ]

/-- The weight `1` on the first copy and `λ` on the second. -/
def wtS (c : ℂ) (b : Sf (Λ ⊕ Λ)) : ℂ := if b.1.isRight then c else 1

/-- Scaling of the second copy. -/
def scaleR (c : ℂ) : V (Λ ⊕ Λ) →ₗ[ℂ] V (Λ ⊕ Λ) where
  toFun w b := wtS c b * w b
  map_add' _ _ := by funext b; simp [mul_add]
  map_smul' _ _ := by funext b; simp; ring

/-- `θ_λ F = F(ψ + λ ζ)`. -/
def thetaL (c : ℂ) : N Λ →ₐ[ℂ] N (Λ ⊕ Λ) := ExteriorAlgebra.map (scaleR c ∘ₗ thetaV)

/-- Scaling of the fluctuation field. -/
def sigR (c : ℂ) : N (Λ ⊕ Λ) →ₐ[ℂ] N (Λ ⊕ Λ) := ExteriorAlgebra.map (scaleR c)

theorem thetaL_eq (c : ℂ) (F : N Λ) : thetaL c F = sigR c (theta F) := by
  rw [thetaL, sigR, theta, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

theorem coord_scaleR (c : ℂ) (b : Sf (Λ ⊕ Λ)) : coord b ∘ₗ scaleR c = wtS c b • coord b := by
  ext w; simp [scaleR]

/-- `∂_b (σ_c x) = w_c(b) σ_c(∂_b x)`. -/
theorem D_sigR (c : ℂ) (b : Sf (Λ ⊕ Λ)) (x : N (Λ ⊕ Λ)) :
    D b (sigR c x) = wtS c b • sigR c (D b x) := by
  rw [D, sigR, contractLeft_map, coord_scaleR, map_smul, LinearMap.smul_apply, map_smul]

theorem proj_sigR (c : ℂ) (x : N (Λ ⊕ Λ)) : proj (sigR c x) = proj x := by
  rw [proj, sigR, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  congr 2
  ext v ⟨a, σ⟩; simp [projV, scaleR, wtS]

variable [Fintype Λ]

theorem LζC_sigR {c : ℂ} (hc : c ≠ 0) (C : Matrix Λ Λ ℂ) (x : N (Λ ⊕ Λ)) :
    LζC ((c ^ 2)⁻¹ • C) (sigR c x) = sigR c (LζC C x) := by
  simp only [LζC_apply, map_sum, map_smul, D_sigR, Matrix.smul_apply, smul_smul]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  simp only [wtS, Sum.isRight_inr, if_true]
  congr 1
  simp only [smul_eq_mul]
  field_simp

/-- **Gaussian rescaling of the fluctuation field**: `𝔼_C x = 𝔼_{λ^{-2}C} σ_λ x`. -/
theorem ECC_sigR {c : ℂ} (hc : c ≠ 0) (C : Matrix Λ Λ ℂ) (x : N (Λ ⊕ Λ)) :
    ECC C x = ECC ((c ^ 2)⁻¹ • C) (sigR c x) := by
  have h := exp_apply_comm (LζC_isNilpotent C) (LζC_isNilpotent ((c ^ 2)⁻¹ • C))
    (sigR c).toRingHom.toAddMonoidHom (fun m => (LζC_sigR hc C m).symm) x
  have h' : sigR c (IsNilpotent.exp (LζC C) x) =
      IsNilpotent.exp (LζC ((c ^ 2)⁻¹ • C)) (sigR c x) := h
  rw [ECC, ECC, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, ← h', proj_sigR]

/-- `𝔼_C θ F = 𝔼_{λ^{-2}C} θ_λ F`. -/
theorem ECC_theta_scale {c : ℂ} (hc : c ≠ 0) (C : Matrix Λ Λ ℂ) (F : N Λ) :
    ECC C (theta F) = ECC ((c ^ 2)⁻¹ • C) (thetaL c F) := by
  rw [thetaL_eq, ECC_sigR hc]

/-- `σ_λ` fixes the first copy. -/
theorem sigR_incl (c : ℂ) (F : N Λ) : sigR c (incl F) = incl F := by
  rw [sigR, incl, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  congr 2
  ext v ⟨a, σ⟩; cases a <;> simp [inlV, scaleR, wtS]

/-! ### The norm of `θ_λ` -/

section Norm

theorem contr_smul_each {m : ℕ} (a : Fin m → ℂ) (φ : Fin m → Module.Dual ℂ (V Λ)) (x : N Λ) :
    contr (fun i => a i • φ i) x = (∏ i, a i) • contr φ x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [contr_succ, contr_succ, map_smul, LinearMap.smul_apply]
    have : Fin.tail (fun i => a i • φ i) = fun i => Fin.tail a i • Fin.tail φ i := rfl
    rw [this, ih, map_smul, Fin.prod_univ_succ, smul_smul, mul_comm]
    rfl

theorem coord_scaleR_thetaV (c : ℂ) (b : Sf (Λ ⊕ Λ)) :
    coord b ∘ₗ (scaleR c ∘ₗ thetaV) = wtS c b • coord (prf b) := by
  rw [← LinearMap.comp_assoc, coord_scaleR, LinearMap.smul_comp, coord_thetaV]

/-- `(θ_λ F)_w = (∏ w_λ(w_i)) F_{w'}`. -/
theorem coeff_thetaL (c : ℂ) (F : N Λ) {n : ℕ} (w : Fin n → Sf (Λ ⊕ Λ)) :
    coeff (thetaL c F) w = (∏ i, wtS c (w i)) * coeff F (fun i => prf (w i)) := by
  rw [coeff, Dseq, thetaL, contr_map, algebraMapInv_map]
  simp only [coord_scaleR_thetaV]
  rw [contr_smul_each, map_smul]
  rfl

variable {E : Type*} [Fintype E] [DecidableEq E] [AddAction (E → ℕ) Λ]

/-- The weighted lift of test functions. -/
def liftTL (c : ℂ) (g : TestFn (Λ ⊕ Λ)) : TestFn Λ := fun n z =>
  ∑ b : Fin n → Bool, (∏ i, wtS c (liftf (b i) (z i))) * g n fun i => liftf (b i) (z i)

theorem wtS_liftf (c : ℂ) (b : Bool) (a : Sf Λ) : wtS c (liftf b a) = if b then c else 1 := by
  cases b <;> simp [wtS, liftf]

theorem pair_thetaL (c : ℂ) (F : N Λ) (g : TestFn (Λ ⊕ Λ)) :
    pair (thetaL c F) g = pair F (liftTL c g) := by
  unfold pair
  have hsub : range (Nf Λ + 1) ⊆ range (Nf (Λ ⊕ Λ) + 1) := by
    intro n hn
    simp only [mem_range] at hn ⊢
    have : Nf Λ ≤ Nf (Λ ⊕ Λ) := by simp [Nf, Fintype.card_sum]
    omega
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun n _ => ?_
    congr 1
    simp_rw [coeff_thetaL]
    rw [← Fintype.sum_equiv (liftEquiv n) (fun p => ((∏ i, wtS c (liftEquiv n p i)) *
      coeff F (fun i => prf (liftEquiv n p i))) * g n (liftEquiv n p)) _ (fun _ => rfl),
      Fintype.sum_prod_type]
    simp only [liftEquiv, Equiv.coe_fn_mk, prf_liftf, liftTL, mul_sum]
    refine sum_congr rfl fun z _ => sum_congr rfl fun b _ => by ring
  · intro n _ hn
    simp only [mem_range, not_lt] at hn
    rw [sum_eq_zero fun w _ => by rw [coeff_thetaL, coeff_eq_zero_of_lt _ _ (by omega), mul_zero,
      zero_mul], mul_zero]

variable {p : ℕ} {h ℓ : ℝ}

theorem sum_prod_wt (c : ℝ) (n : ℕ) :
    ∑ b : Fin n → Bool, ∏ i, (if b i then c else 1) = (1 + c) ^ n := by
  rw [← Fintype.prod_sum (fun _ (b : Bool) => if b then c else 1)]
  simp [add_comm]

theorem phiNorm_liftTL_le (hh : 0 < h) (hℓ : 0 < ℓ) {c : ℝ} (hc : 0 ≤ c) (g : TestFn (Λ ⊕ Λ))
    {M : ℝ} (hM : 0 ≤ M) (hg : phiNorm E p h ℓ g ≤ ENNReal.ofReal M) :
    phiNorm E p h ((1 + c) * ℓ) (liftTL (c : ℂ) g) ≤ ENNReal.ofReal M := by
  refine phiNorm_le fun n z α hα => ?_
  have hnab : nab α (liftTL (c : ℂ) g n) z =
      ∑ b : Fin n → Bool, ((∏ i, (if b i then c else 1 : ℝ)) : ℂ) •
        nab α (g n) (fun i => liftf (b i) (z i)) := by
    unfold liftTL
    rw [nabla_sum]
    refine sum_congr rfl fun b _ => ?_
    have hw : ∀ z' : Fin n → Sf Λ, (∏ i, wtS (c : ℂ) (liftf (b i) (z' i))) =
        ((∏ i, (if b i then c else 1 : ℝ)) : ℂ) := fun z' => by
      push_cast
      exact prod_congr rfl fun i _ => by rw [wtS_liftf]; split_ifs <;> simp
    simp only [hw, ← smul_eq_mul]
    rw [nabla_smul]
    exact congrArg _ (nabla_comp_pi (sh (X := Λ) (E := E)) (sh (X := Λ ⊕ Λ) (E := E))
      (fun i => liftf (b i)) (fun i b' a => (sh_liftf (b i) b' a).symm) α (g n) z)
  unfold phiTerm
  rw [hnab]
  have hprod : ∀ b : Fin n → Bool, 0 ≤ ∏ i, (if b i then c else 1 : ℝ) := fun b =>
    prod_nonneg fun i _ => by split_ifs <;> linarith
  calc ((1 + c) * ℓ)⁻¹ ^ n * h ^ ord α *
        ‖∑ b : Fin n → Bool, ((∏ i, (if b i then c else 1 : ℝ)) : ℂ) •
          nab α (g n) (fun i => liftf (b i) (z i))‖
      ≤ ((1 + c) * ℓ)⁻¹ ^ n * h ^ ord α *
        ∑ b : Fin n → Bool, (∏ i, (if b i then c else 1 : ℝ)) * (M * ℓ ^ n * (h ^ ord α)⁻¹) := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
        rw [norm_smul, ← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hprod b)]
        exact mul_le_mul_of_nonneg_left (abs_nab_le hh hℓ hM hg _ α hα) (hprod b)
    _ = M := by
        rw [← sum_mul, sum_prod_wt]
        have hl : ℓ ^ n ≠ 0 := by positivity
        have hh' : h ^ ord α ≠ 0 := by positivity
        have h2 : (1 + c) ^ n ≠ 0 := by positivity
        rw [inv_pow, mul_pow]
        field_simp

/-- **`‖θ_λ F‖_{T(ℓ ⊔ ℓ)} ≤ ‖F‖_{T((1+λ)ℓ)}`** for `λ ≥ 0`. -/
theorem tNorm_thetaL_le (hh : 0 < h) (hℓ : 0 < ℓ) {c : ℝ} (hc : 0 ≤ c) (F : N Λ) :
    tNorm E p h ℓ (thetaL (c : ℂ) F) ≤ tNorm E p h ((1 + c) * ℓ) F := by
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh (by positivity) F)]
  refine tNorm_le fun g hg => ?_
  rw [pair_thetaL]
  have := abs_pair_le hh (by positivity) F zero_le_one
    (phiNorm_liftTL_le hh hℓ hc g zero_le_one (by rwa [ENNReal.ofReal_one]))
  rwa [mul_one] at this

end Norm

end

end Grassmann
