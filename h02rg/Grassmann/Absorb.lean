import Grassmann.IBPC
import Grassmann.Truncated
import Grassmann.Berezin

/-!
# The absorption identity (`h02uv-outline.tex`, `e:absorb`, Lemma `lem:onestep`)

For complex matrices `C` (covariance) and `B`, let `q_B = (ψ̄, Bψ) = ∑_{a,b} B_{ab} ψ̄_a ψ_b`
(`qf`). If `1 - Bᵀ C` is invertible and `C' = C (1 - Bᵀ C)^{-1}`, then for all `F`

  `⟨e^{-q_B} F⟩_C = ⟨e^{-q_B}⟩_C ⟨F⟩_{C'}`                                   (`omegaC_exp_mul`)

and, on the doubled algebra, `𝔼_C (e^{-q_B(ζ)} G) = ⟨e^{-q_B}⟩_C 𝔼_{C'} G` (`ECC_exp_mul`).

and the normalisation is `⟨e^{-q_B}⟩_C = det (1 - Bᵀ C)` (`omegaC_expQ`), so
`⟨e^{-q_B} F⟩_C = det (1 - Bᵀ C) ⟨F⟩_{C'}` (`omegaC_exp_mul_det`). `omegaC_onestep` is
`lem:onestep`: `⟨e^{-z(ψ,Aψ̄)} F⟩_Γ = det (1 + zAΓ) ⟨𝔼_{Γ₁} θ F⟩_{Γ₂}` when
`Γ (1 + zAΓ)^{-1} = Γ₁ + Γ₂`. No invertibility of `C` is assumed.

The proof uses only integration by parts: a linear functional `μ` with
`μ(ι v G) = μ(∂_{φ^C_v} G)` for all `v, G` is `μ(1) ⟨·⟩_C` (`eq_smul_omegaC_of_ibp`), and
`F ↦ ⟨e^{-q_B} F⟩_C` satisfies integration by parts for `C'`. The determinant is obtained by
adding the rows of `B` one at a time (rank-one updates, `det_add_row`), for all but finitely
many multiples `tB`, and then by the identity theorem for polynomials in `t`.

With `⟨ψ̄_x ψ_y⟩_C = C_{xy}`, the gradient term of `h02uv-outline.tex`,
`z (ψ, A ψ̄) = -z (ψ̄, Aᵀ ψ)`, is `q_B` with `B = -z Aᵀ`; then `1 - Bᵀ C = 1 + z A C` and
`C' = C (1 + z A C)^{-1}`.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset Matrix

variable {I : Type*} [DecidableEq I] [Fintype I]

/-! ### Uniqueness of the Gaussian functional -/

/-- `⟨·⟩_C` as a linear functional. -/
def omegaCL (C : Matrix I I ℂ) : N I →ₗ[ℂ] ℂ where
  toFun := omegaC C
  map_add' := omegaC_add C
  map_smul' c F := omegaC_smul C c F

theorem omegaCL_apply (C : Matrix I I ℂ) (F : N I) : omegaCL C F = omegaC C F := rfl

theorem omegaC_one (C : Matrix I I ℂ) : omegaC C 1 = 1 := by
  rw [omegaC_eq_of_Dbar C fun x => D_one _]; simp

/-- A linear functional satisfying Gaussian integration by parts for `C` is a multiple of
`⟨·⟩_C`. -/
theorem eq_smul_omegaC_of_ibp (C : Matrix I I ℂ) (μ : N I →ₗ[ℂ] ℂ)
    (h : ∀ (v : V I) (G : N I), μ (ι ℂ v * G) = μ (Dφ (phiCx C v) G)) (F : N I) :
    μ F = μ 1 * omegaC C F := by
  set ν : N I →ₗ[ℂ] ℂ := μ - μ 1 • omegaCL C
  have hν : ∀ (v : V I) (G : N I), ν (ι ℂ v * G) = ν (Dφ (phiCx C v) G) := by
    intro v G
    simp only [ν, LinearMap.sub_apply, LinearMap.smul_apply, omegaCL, LinearMap.coe_mk,
      AddHom.coe_mk, smul_eq_mul, h, omegaC_ι_mul]
  have hν1 : ν 1 = 0 := by
    simp [ν, omegaCL, omegaC_one]
  -- `ν` vanishes on all products of generators
  have hmono : ∀ k (u : Fin k → V I), ν (ιMulti ℂ k u) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u
      rcases k with _ | k
      · rw [ιMulti_zero_apply]; exact hν1
      · rw [ιMulti_succ_apply, hν]
        rcases k with _ | k
        · rw [ιMulti_zero_apply, Dφ, contractLeft_one, map_zero]
        · rw [Dφ, contractLeft_ιMulti, map_sum]
          exact sum_eq_zero fun j _ => by rw [map_smul, ih k (by omega), smul_zero]
  have hzero : ν = 0 := by
    refine LinearMap.ext_on_range (ExteriorAlgebra.ιMulti_span ℂ (V I)) fun x => ?_
    simpa using hmono x.1 x.2
  have := LinearMap.congr_fun hzero F
  simp only [ν, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, omegaCL,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, sub_eq_zero] at this
  exact this

/-! ### The quadratic form and its exponential -/

/-- `q_B = (ψ̄, Bψ) = ∑_{a,b} B_{ab} ψ̄_a ψ_b`. -/
def qf (B : Matrix I I ℂ) : N I := ∑ a, ∑ b, B a b • (psibar a * psi b)

theorem inv'_qf (B : Matrix I I ℂ) : inv' (qf B) = qf B := by
  simp [qf, map_sum, psibar, psi]

theorem qf_isNilpotent (B : Matrix I I ℂ) : IsNilpotent (qf B) := by
  have hev : ∀ (a b : Sf I) (c : ℂ), inv' (c • (ψ a * ψ b)) = c • (ψ a * ψ b) := by simp
  refine Commute.isNilpotent_sum (fun x _ => ?_) fun x x' _ _ => ?_
  · refine Commute.isNilpotent_sum (fun y _ => ?_) fun y y' _ _ => ?_
    · exact ⟨2, by rw [pow_two, psibar, psi, smul_mul_smul, ψ, ψ, ιι_sq, smul_zero]⟩
    · exact mul_comm_of_even (hev _ _ _) _
  · exact mul_comm_of_even (by simp [map_sum, psibar, psi]) _

/-- `e^{-q_B}`. -/
abbrev expQ (B : Matrix I I ℂ) : N I := IsNilpotent.exp (-qf B)

theorem inv'_expQ' (B : Matrix I I ℂ) : inv' (expQ B) = expQ B := by
  rw [IsNilpotent.map_exp (qf_isNilpotent B).neg, map_neg, inv'_qf]

theorem Dφ_mul (φ : Module.Dual ℂ (V I)) (x y : N I) :
    Dφ φ (x * y) = Dφ φ x * y + inv' x * Dφ φ y := contractLeft_mul φ x y

theorem Dφ_pow (φ : Module.Dual ℂ (V I)) {y : N I} (hy : inv' y = y) (n : ℕ) :
    Dφ φ (y ^ (n + 1)) = ((n + 1 : ℕ) : ℂ) • (y ^ n * Dφ φ y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Dφ, contractLeft_mul, ← Dφ, ih, hy, mul_smul_comm, ← mul_assoc, ← pow_succ',
      mul_comm_of_even (show inv' (y ^ (n + 1)) = y ^ (n + 1) by rw [map_pow, hy])]
    push_cast
    module

theorem Dφ_exp (φ : Module.Dual ℂ (V I)) {y : N I} (hy : inv' y = y) (hn : IsNilpotent y) :
    Dφ φ (IsNilpotent.exp y) = IsNilpotent.exp y * Dφ φ y := by
  obtain ⟨k, hk⟩ := hn
  have hk1 : y ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  conv_rhs => rw [IsNilpotent.exp_eq_sum hk]
  rw [IsNilpotent.exp_eq_sum hk1, map_sum, Finset.sum_mul, Finset.sum_range_succ', pow_zero,
    LinearMap.map_smul_of_tower, Dφ, contractLeft_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul_of_tower, ← Dφ, Dφ_pow φ hy, smul_mul_assoc, Nat.cast_smul_eq_nsmul ℂ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Nat.factorial_succ, Nat.cast_mul]
  congr 1
  field_simp

/-! ### Integration by parts for `⟨e^{-q_B} ·⟩_C` -/

/-- The vector `u` with `∂_φ q_B = ι u`. -/
def uvec (φ : Module.Dual ℂ (V I)) (B : Matrix I I ℂ) : V I :=
  ∑ a, ∑ b, B a b • (φ (ev (a, -1)) • ev (b, 1) - φ (ev (b, 1)) • ev (a, -1))

theorem Dφ_qf (φ : Module.Dual ℂ (V I)) (B : Matrix I I ℂ) :
    Dφ φ (qf B) = ι ℂ (uvec φ B) := by
  simp only [qf, uvec, map_sum, map_smul, map_sub, psibar, psi, ψ, Dφ, contractLeft_mul,
    contractLeft_ι, inv'_ι, Algebra.algebraMap_eq_smul_one]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [smul_mul_assoc, one_mul, neg_mul, mul_smul_comm, mul_one]
  abel

theorem omegaC_expQ_ibp (C B : Matrix I I ℂ) (v : V I) (G : N I) :
    omegaC C (expQ B * (ι ℂ (v + uvec (phiCx C v) B) * G)) =
      omegaC C (expQ B * Dφ (phiCx C v) G) := by
  have hE := inv'_expQ' B
  have hcomm : ∀ X : N I, expQ B * X = X * expQ B := mul_comm_of_even hE
  have h1 : omegaC C (expQ B * (ι ℂ v * G)) =
      omegaC C (Dφ (phiCx C v) (expQ B) * G) + omegaC C (expQ B * Dφ (phiCx C v) G) := by
    rw [← mul_assoc, hcomm, mul_assoc, omegaC_ι_mul, Dφ_mul, hE, omegaC_add]
  have h2 : Dφ (phiCx C v) (expQ B) = -(expQ B * ι ℂ (uvec (phiCx C v) B)) := by
    rw [Dφ_exp _ (by rw [map_neg, inv'_qf]) (qf_isNilpotent B).neg, map_neg, Dφ_qf, mul_neg]
  have h3 : omegaC C (-(expQ B * ι ℂ (uvec (phiCx C v) B)) * G) =
      -omegaC C (expQ B * (ι ℂ (uvec (phiCx C v) B) * G)) := by
    rw [neg_mul, mul_assoc, ← neg_one_smul ℂ, omegaC_smul]; ring
  rw [map_add, add_mul, mul_add, omegaC_add, h1, h2, h3]
  ring

/-! ### The linear algebra -/

/-- The `ψ` components `y ↦ v_{(y,+)}`. -/
def vp (v : V I) : I → ℂ := fun y => v (y, 1)

/-- The `ψ̄` components `x ↦ v_{(x,-)}`. -/
def vm (v : V I) : I → ℂ := fun x => v (x, -1)

theorem neg_one_ne_one' : (-1 : ℤˣ) ≠ 1 := by decide

theorem vp_ev_neg (a : I) : vp (ev (a, -1)) = 0 := by
  funext y; simp [vp, ev, Pi.single_apply, Prod.ext_iff, neg_one_ne_one'.symm]

theorem vm_ev_neg (a : I) : vm (ev (a, -1)) = Pi.single a 1 := by
  funext y; simp [vm, ev, Pi.single_apply, Prod.ext_iff]

theorem vp_ev_pos (b : I) : vp (ev (b, 1)) = Pi.single b 1 := by
  funext y; simp [vp, ev, Pi.single_apply, Prod.ext_iff]

theorem vm_ev_pos (b : I) : vm (ev (b, 1)) = 0 := by
  funext y; simp [vm, ev, Pi.single_apply, Prod.ext_iff, neg_one_ne_one']

theorem phiCx_apply (C : Matrix I I ℂ) (v u : V I) :
    phiCx C v u = vm v ⬝ᵥ (C *ᵥ vp u) - vm u ⬝ᵥ (C *ᵥ vp v) := by
  simp only [phiCx, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.proj_apply, smul_eq_mul, dotProduct, mulVec, vm, vp,
    mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem vp_add (v w : V I) : vp (v + w) = vp v + vp w := rfl
theorem vm_add (v w : V I) : vm (v + w) = vm v + vm w := rfl

theorem vp_smul (c : ℂ) (v : V I) : vp (c • v) = c • vp v := rfl
theorem vm_smul (c : ℂ) (v : V I) : vm (c • v) = c • vm v := rfl
theorem vp_sub (v w : V I) : vp (v - w) = vp v - vp w := rfl
theorem vm_sub (v w : V I) : vm (v - w) = vm v - vm w := rfl
theorem vp_sum {ι : Type*} (s : Finset ι) (f : ι → V I) : vp (∑ i ∈ s, f i) = ∑ i ∈ s, vp (f i) := by
  funext y; simp [vp, Finset.sum_apply]
theorem vm_sum {ι : Type*} (s : Finset ι) (f : ι → V I) : vm (∑ i ∈ s, f i) = ∑ i ∈ s, vm (f i) := by
  funext y; simp [vm, Finset.sum_apply]

theorem phiCx_ev_neg (C : Matrix I I ℂ) (v : V I) (a : I) :
    phiCx C v (ev (a, -1)) = -(C *ᵥ vp v) a := by
  rw [phiCx_apply, vp_ev_neg, vm_ev_neg, mulVec_zero, dotProduct_zero, single_one_dotProduct,
    zero_sub]

theorem phiCx_ev_pos (C : Matrix I I ℂ) (v : V I) (b : I) :
    phiCx C v (ev (b, 1)) = (Cᵀ *ᵥ vm v) b := by
  rw [phiCx_apply, vp_ev_pos, vm_ev_pos, zero_dotProduct, sub_zero, mulVec_single_one,
    dotProduct_comm]
  simp [mulVec, dotProduct, Matrix.col_apply, transpose_apply]

theorem vp_uvec (C B : Matrix I I ℂ) (v : V I) :
    vp (uvec (phiCx C v) B) = -(Bᵀ *ᵥ (C *ᵥ vp v)) := by
  simp only [uvec, vp_sum, vp_smul, vp_sub, vp_ev_pos, vp_ev_neg, smul_zero, sub_zero,
    phiCx_ev_neg]
  funext b₀
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.single_apply,
    mulVec, dotProduct, transpose_apply, mul_ite, mul_one, mul_zero, ← sum_neg_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [Finset.sum_ite_eq, mem_univ, if_true, sum_neg_distrib]
  ring

theorem vm_uvec (C B : Matrix I I ℂ) (v : V I) :
    vm (uvec (phiCx C v) B) = -(B *ᵥ (Cᵀ *ᵥ vm v)) := by
  simp only [uvec, vm_sum, vm_smul, vm_sub, vm_ev_pos, vm_ev_neg, smul_zero, zero_sub,
    phiCx_ev_pos, smul_neg]
  funext a₀
  simp only [Finset.sum_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, sum_neg_distrib, neg_inj]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, mem_univ, if_true]
  simp [mulVec, dotProduct]

/-- The map `v ↦ v + u_v` of the integration by parts formula. -/
def Tvec (C B : Matrix I I ℂ) (v : V I) : V I := v + uvec (phiCx C v) B

theorem vp_Tvec (C B : Matrix I I ℂ) (v : V I) : vp (Tvec C B v) = (1 - Bᵀ * C) *ᵥ vp v := by
  rw [Tvec, vp_add, vp_uvec, sub_mulVec, one_mulVec, mulVec_mulVec, sub_eq_add_neg]

theorem vm_Tvec (C B : Matrix I I ℂ) (v : V I) : vm (Tvec C B v) = (1 - B * Cᵀ) *ᵥ vm v := by
  rw [Tvec, vm_add, vm_uvec, sub_mulVec, one_mulVec, mulVec_mulVec, sub_eq_add_neg]

/-- The dressed covariance `C' = C (1 - Bᵀ C)^{-1}`. -/
def Cdress (C B : Matrix I I ℂ) : Matrix I I ℂ := C * (1 - Bᵀ * C)⁻¹

theorem det_dual (C B : Matrix I I ℂ) : (1 - B * Cᵀ).det = (1 - Bᵀ * C).det := by
  rw [det_one_sub_mul_comm, ← det_transpose, transpose_sub, transpose_one, transpose_mul,
    transpose_transpose]

theorem dot_mulVec_left (S : Matrix I I ℂ) (x y : I → ℂ) :
    (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Sᵀ *ᵥ y) := by
  simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem phiCx_Tvec (C B : Matrix I I ℂ) (hT : IsUnit (1 - Bᵀ * C).det) (v : V I) :
    phiCx (Cdress C B) (Tvec C B v) = phiCx C v := by
  have h1 : Cdress C B * (1 - Bᵀ * C) = C := by
    rw [Cdress, Matrix.mul_assoc, nonsing_inv_mul _ hT, Matrix.mul_one]
  have h2 : (1 - B * Cᵀ)ᵀ * Cdress C B = C := by
    rw [transpose_sub, transpose_one, transpose_mul, transpose_transpose, Cdress,
      ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      show C - C * (Bᵀ * C) = C * (1 - Bᵀ * C) by rw [Matrix.mul_sub, Matrix.mul_one],
      Matrix.mul_assoc, mul_nonsing_inv _ hT, Matrix.mul_one]
  refine LinearMap.ext fun u => ?_
  rw [phiCx_apply, phiCx_apply, vp_Tvec, vm_Tvec, mulVec_mulVec, h1]
  congr 1
  rw [dot_mulVec_left, mulVec_mulVec, h2]

theorem Tvec_surjective (C B : Matrix I I ℂ) (hT : IsUnit (1 - Bᵀ * C).det) (w : V I) :
    ∃ v, Tvec C B v = w := by
  have hS : IsUnit (1 - B * Cᵀ).det := by rw [det_dual]; exact hT
  set v : V I := fun c => if c.2 = 1 then ((1 - Bᵀ * C)⁻¹ *ᵥ vp w) c.1
    else ((1 - B * Cᵀ)⁻¹ *ᵥ vm w) c.1
  have hvp : vp v = (1 - Bᵀ * C)⁻¹ *ᵥ vp w := by funext y; simp [v, vp]
  have hvm : vm v = (1 - B * Cᵀ)⁻¹ *ᵥ vm w := by
    funext x; simp [v, vm, neg_one_ne_one']
  refine ⟨v, ?_⟩
  funext ⟨x, σ⟩
  rcases Int.units_eq_one_or σ with rfl | rfl
  · have := congrFun (vp_Tvec C B v) x
    rw [hvp, mulVec_mulVec, mul_nonsing_inv _ hT, one_mulVec] at this
    exact this
  · have := congrFun (vm_Tvec C B v) x
    rw [hvm, mulVec_mulVec, mul_nonsing_inv _ hS, one_mulVec] at this
    exact this

/-! ### The absorption identity -/

/-- `⟨e^{-q_B} F⟩_C = ⟨e^{-q_B}⟩_C ⟨F⟩_{C'}` with `C' = C (1 - Bᵀ C)^{-1}`. -/
theorem omegaC_exp_mul (C B : Matrix I I ℂ) (hT : IsUnit (1 - Bᵀ * C).det) (F : N I) :
    omegaC C (expQ B * F) = omegaC C (expQ B) * omegaC (Cdress C B) F := by
  set μ : N I →ₗ[ℂ] ℂ := omegaCL C ∘ₗ LinearMap.mulLeft ℂ (expQ B)
  have hμ : ∀ X, μ X = omegaC C (expQ B * X) := fun X => rfl
  have h := eq_smul_omegaC_of_ibp (Cdress C B) μ (fun w G => by
    obtain ⟨v, rfl⟩ := Tvec_surjective C B hT w
    rw [hμ, hμ, phiCx_Tvec C B hT]
    exact omegaC_expQ_ibp C B v G) F
  rwa [hμ, hμ, mul_one] at h

/-- The one-step form (`lem:onestep`): if `C (1 - Bᵀ C)^{-1} = C₁ + C₂`, then
`⟨e^{-q_B} F⟩_C = ⟨e^{-q_B}⟩_C ⟨𝔼_{C₁} θ F⟩_{C₂}`. -/
theorem omegaC_absorb_step (C B C₁ C₂ : Matrix I I ℂ) (hT : IsUnit (1 - Bᵀ * C).det)
    (hC : Cdress C B = C₁ + C₂) (F : N I) :
    omegaC C (expQ B * F) = omegaC C (expQ B) * omegaC C₂ (ECC C₁ (theta F)) := by
  rw [omegaC_exp_mul C B hT, hC, ECC_theta]
  congr 1
  rw [omegaC, omegaC, add_comm, expLC_add]

/-- The gradient term `z (ψ, A ψ̄) = z ∑_{x,y} A_{xy} ψ_x ψ̄_y` is `q_B` with `B = -z Aᵀ`. -/
theorem qf_grad (z : ℂ) (A : Matrix I I ℂ) :
    qf (-(z • Aᵀ)) = z • ∑ x, ∑ y, A x y • (psi x * psibar y) := by
  simp only [qf, Matrix.neg_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [psi, psibar, ψ, ψ, ι_anticomm, smul_neg, ← neg_smul, smul_smul]
  ring_nf

theorem one_sub_grad (z : ℂ) (A C : Matrix I I ℂ) :
    1 - (-(z • Aᵀ))ᵀ * C = 1 + z • (A * C) := by
  rw [transpose_neg, transpose_smul, transpose_transpose, neg_mul, sub_neg_eq_add,
    Matrix.smul_mul]

/-! ### The normalisation `⟨e^{-q_B}⟩_C = det (1 - Bᵀ C)` -/

theorem omegaC_psibar_psi (C : Matrix I I ℂ) (x y : I) : omegaC C (psibar x * psi y) = C x y := by
  have h := ECC_theta_psibar_psi C x y
  rw [ECC_theta] at h
  rw [omegaC, h, map_add, AlgHom.commutes]
  simp [psibar, psi, ψ, Algebra.algebraMap_eq_smul_one]

theorem qf_add (B₁ B₂ : Matrix I I ℂ) : qf (B₁ + B₂) = qf B₁ + qf B₂ := by
  simp only [qf, Matrix.add_apply, add_smul, sum_add_distrib]

theorem qf_smul (t : ℂ) (B : Matrix I I ℂ) : qf (t • B) = t • qf B := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, mul_smul, smul_sum]

theorem qf_zero : qf (0 : Matrix I I ℂ) = 0 := by simp [qf]

theorem expQ_add (B₁ B₂ : Matrix I I ℂ) : expQ (B₁ + B₂) = expQ B₁ * expQ B₂ := by
  rw [expQ, qf_add, neg_add, IsNilpotent.exp_add_of_commute
    (mul_comm_of_even (by rw [map_neg, inv'_qf]) _) (qf_isNilpotent _).neg
    (qf_isNilpotent _).neg]

theorem expQ_zero : expQ (0 : Matrix I I ℂ) = 1 := by
  rw [expQ, qf_zero, neg_zero, IsNilpotent.exp_zero]

/-- The `a`-th row of `B`. -/
def rowM (B : Matrix I I ℂ) (a : I) : Matrix I I ℂ := fun x y => if x = a then B a y else 0

theorem qf_rowM (B : Matrix I I ℂ) (a : I) :
    qf (rowM B a) = ∑ b, B a b • (psibar a * psi b) := by
  rw [qf, Finset.sum_eq_single a]
  · exact sum_congr rfl fun b _ => by simp [rowM]
  · intro x _ hx; exact sum_eq_zero fun b _ => by simp [rowM, hx]
  · simp

theorem omegaC_sum_psibar_psi (C : Matrix I I ℂ) (a : I) (r : I → ℂ) :
    omegaC C (∑ b, r b • (psibar a * psi b)) = ∑ b, r b * C a b := by
  rw [show omegaC C = omegaCL C from rfl, map_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul]
  rw [show omegaCL C (psibar a * psi b) = omegaC C (psibar a * psi b) from rfl, omegaC_psibar_psi]

theorem omegaC_expQ_row (C B : Matrix I I ℂ) (a : I) :
    omegaC C (expQ (rowM B a)) = 1 - ∑ b, B a b * C a b := by
  set w : V I := ∑ b, B a b • ev (b, 1)
  have hq : qf (rowM B a) = ι ℂ (ev (a, -1)) * ι ℂ w := by
    rw [qf_rowM]
    simp only [w, map_sum, map_smul, mul_sum, mul_smul_comm, psibar, psi, ψ]
  have hsq : qf (rowM B a) ^ 2 = 0 := by
    rw [hq, pow_two, mul_assoc, ← mul_assoc (ι ℂ w), ι_anticomm w, neg_mul, mul_neg, ← mul_assoc,
      ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul, neg_zero]
  have hsq' : (-qf (rowM B a)) ^ 2 = 0 := by rw [neg_sq, hsq]
  rw [expQ, IsNilpotent.exp_eq_sum hsq']
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  rw [omegaC_add, omegaC_one, ← neg_one_smul ℂ, omegaC_smul, qf_rowM, omegaC_sum_psibar_psi]
  ring

theorem rowM_transpose_mul (C B : Matrix I I ℂ) (a : I) :
    (rowM B a)ᵀ * C = replicateCol Unit (fun x => B a x) * replicateRow Unit (fun z => C a z) := by
  ext x z
  simp [rowM, Matrix.mul_apply, transpose_apply, replicateCol, replicateRow, ite_mul]

theorem det_add_row (C B₁ B : Matrix I I ℂ) (a : I) (hT : IsUnit (1 - B₁ᵀ * C).det) :
    (1 - (B₁ + rowM B a)ᵀ * C).det =
      (1 - B₁ᵀ * C).det * (1 - ∑ b, B a b * Cdress C B₁ a b) := by
  set T := 1 - B₁ᵀ * C
  set u : I → ℂ := fun x => B a x
  set v : I → ℂ := fun z => C a z
  have hTT : T * T⁻¹ = 1 := mul_nonsing_inv _ hT
  have hsplit : 1 - (B₁ + rowM B a)ᵀ * C =
      T * (1 + replicateCol Unit (-(T⁻¹ *ᵥ u)) * replicateRow Unit v) := by
    rw [transpose_add, Matrix.add_mul, rowM_transpose_mul, Matrix.mul_add, Matrix.mul_one,
      ← Matrix.mul_assoc]
    have : T * replicateCol Unit (-(T⁻¹ *ᵥ u)) = -replicateCol Unit u := by
      ext x i
      simp only [Matrix.mul_apply, replicateCol_apply, Matrix.neg_apply, Pi.neg_apply, mul_neg,
        sum_neg_distrib, neg_inj]
      have := congrFun (show T *ᵥ (T⁻¹ *ᵥ u) = u by rw [mulVec_mulVec, hTT, one_mulVec]) x
      simpa [mulVec, dotProduct] using this
    rw [this, Matrix.neg_mul]
    simp only [T]; abel
  rw [hsplit, det_mul, det_one_add_replicateCol_mul_replicateRow]
  congr 1
  rw [dotProduct_neg, ← sub_eq_add_neg]
  congr 1
  simp only [v, u, dotProduct, mulVec, Cdress, Matrix.mul_apply, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun z _ => by ring

/-- The rows of `B` in `S`. -/
def rowsM (B : Matrix I I ℂ) (S : Finset I) : Matrix I I ℂ := fun x y => if x ∈ S then B x y else 0

theorem rowsM_empty (B : Matrix I I ℂ) : rowsM B ∅ = 0 := by ext x y; simp [rowsM]

theorem rowsM_insert (B : Matrix I I ℂ) {a : I} {S : Finset I} (ha : a ∉ S) :
    rowsM B (insert a S) = rowsM B S + rowM B a := by
  ext x y
  by_cases hx : x = a
  · subst hx; simp [rowsM, rowM, ha]
  · simp [rowsM, rowM, hx]

theorem rowsM_univ (B : Matrix I I ℂ) : rowsM B univ = B := by ext x y; simp [rowsM]

theorem rowsM_smul (t : ℂ) (B : Matrix I I ℂ) (S : Finset I) :
    rowsM (t • B) S = t • rowsM B S := by
  ext x y; by_cases hx : x ∈ S <;> simp [rowsM, hx]

theorem omegaC_expQ_rows (C B : Matrix I I ℂ) (S : Finset I)
    (hS : ∀ S' ⊆ S, IsUnit (1 - (rowsM B S')ᵀ * C).det) :
    omegaC C (expQ (rowsM B S)) = (1 - (rowsM B S)ᵀ * C).det := by
  induction S using Finset.induction_on with
  | empty => simp [rowsM_empty, expQ_zero, omegaC_one]
  | insert a S ha ih =>
    have hS0 := hS S (Finset.subset_insert a S)
    rw [rowsM_insert B ha, expQ_add, omegaC_exp_mul C _ hS0,
      ih (fun S' h => hS S' (h.trans (Finset.subset_insert a S))), omegaC_expQ_row,
      det_add_row C _ B a hS0]

/-- The polynomial `t ↦ det (1 - t M)`. -/
def detPoly (M : Matrix I I ℂ) : Polynomial ℂ := (1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det

theorem eval_detPoly (M : Matrix I I ℂ) (t : ℂ) : (detPoly M).eval t = (1 - t • M).det := by
  rw [detPoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext x y
  simp [Matrix.one_apply, apply_ite]
  ring

theorem detPoly_ne_zero (M : Matrix I I ℂ) : detPoly M ≠ 0 := by
  intro h
  have := eval_detPoly M 0
  rw [h, Polynomial.eval_zero, zero_smul, sub_zero, det_one] at this
  exact zero_ne_one this

/-- **The normalisation**: `⟨e^{-q_B}⟩_C = det (1 - Bᵀ C)`. -/
theorem omegaC_expQ (C B : Matrix I I ℂ) : omegaC C (expQ B) = (1 - Bᵀ * C).det := by
  obtain ⟨k, hk⟩ := qf_isNilpotent B
  -- `t ↦ ⟨e^{-t q_B}⟩_C` as a polynomial
  set P : Polynomial ℂ := ∑ i ∈ range k,
    Polynomial.C (omegaC C (qf B ^ i) * ((-1) ^ i * ((i.factorial : ℂ))⁻¹)) * Polynomial.X ^ i
  have hP : ∀ t : ℂ, P.eval t = omegaC C (expQ (t • B)) := by
    intro t
    have hk' : (-qf (t • B)) ^ k = 0 := by rw [qf_smul, neg_pow, smul_pow, hk, smul_zero, mul_zero]
    rw [expQ, IsNilpotent.exp_eq_sum hk', show omegaC C = omegaCL C from rfl, map_sum]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    refine sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul_of_tower, qf_smul, ← neg_smul, smul_pow, map_smul, omegaCL_apply,
      ← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul, smul_eq_mul]
    push_cast; ring
  have hQ : ∀ t : ℂ, (detPoly (Bᵀ * C)).eval t = (1 - (t • B)ᵀ * C).det := by
    intro t; rw [eval_detPoly, transpose_smul, Matrix.smul_mul]
  -- the good parameters
  set bad : Set ℂ := ⋃ S' ∈ (univ : Finset I).powerset,
    {t | (detPoly ((rowsM B S')ᵀ * C)).IsRoot t}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun S' _ => ?_
    refine ((detPoly ((rowsM B S')ᵀ * C)).roots.toFinset.finite_toSet).subset fun t ht => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots (detPoly_ne_zero _)).2 ht
  have hgood : ∀ t ∉ bad, P.eval t = (detPoly (Bᵀ * C)).eval t := by
    intro t ht
    rw [hP, hQ, ← rowsM_univ (t • B)]
    refine omegaC_expQ_rows C (t • B) univ fun S' _ => ?_
    rw [isUnit_iff_ne_zero, rowsM_smul, transpose_smul, Matrix.smul_mul, ← eval_detPoly]
    intro h0
    exact ht (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.subset_univ S')))
      h0)
  have hPQ : P = detPoly (Bᵀ * C) :=
    Polynomial.eq_of_infinite_eval_eq _ _
      ((Set.infinite_univ.diff hbad).mono fun t ht => hgood t ht.2)
  have := congrArg (Polynomial.eval 1) hPQ
  rw [hP, hQ] at this
  simpa using this

/-- `e:absorb` with the determinant:
`⟨e^{-q_B} F⟩_C = det (1 - Bᵀ C) ⟨F⟩_{C (1 - Bᵀ C)^{-1}}`. -/
theorem omegaC_exp_mul_det (C B : Matrix I I ℂ) (hT : IsUnit (1 - Bᵀ * C).det) (F : N I) :
    omegaC C (expQ B * F) = (1 - Bᵀ * C).det * omegaC (Cdress C B) F := by
  rw [omegaC_exp_mul C B hT, omegaC_expQ]

/-- `lem:onestep`: `⟨e^{-z(ψ,Aψ̄)} F⟩_Γ = det (1 + zAΓ) ⟨𝔼_{Γ₁} θ F⟩_{Γ₂}` whenever
`Γ (1 + zAΓ)^{-1} = Γ₁ + Γ₂`. -/
theorem omegaC_onestep (z : ℂ) (A Γ Γ₁ Γ₂ : Matrix I I ℂ) (hT : IsUnit (1 + z • (A * Γ)).det)
    (hΓ : Γ * (1 + z • (A * Γ))⁻¹ = Γ₁ + Γ₂) (F : N I) :
    omegaC Γ (IsNilpotent.exp (-(z • ∑ x, ∑ y, A x y • (psi x * psibar y))) * F) =
      (1 + z • (A * Γ)).det * omegaC Γ₂ (ECC Γ₁ (theta F)) := by
  have hT' : IsUnit (1 - (-(z • Aᵀ))ᵀ * Γ).det := by rwa [one_sub_grad]
  have h := omegaC_absorb_step Γ (-(z • Aᵀ)) Γ₁ Γ₂ hT' (by rw [Cdress, one_sub_grad]; exact hΓ) F
  rw [omegaC_expQ, one_sub_grad, expQ, qf_grad] at h
  exact h

/-! ### The doubled algebra -/

section Doubled

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The `ζ` components of a vector of the doubled algebra. -/
def projRV : V (Λ ⊕ Λ) →ₗ[ℂ] V Λ where
  toFun w a := w (Sum.inr a.1, a.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vec_split (w : V (Λ ⊕ Λ)) : w = inlV (projV w) + inrV (projRV w) := by
  ext ⟨c, σ⟩; cases c <;> simp [inlV, inrV, projV, projRV]

theorem inclζ_ι_mul_incl (m : V Λ) (A : N Λ) :
    ι ℂ (inrV m) * incl A = incl (inv' A) * ι ℂ (inrV m) := by
  rw [ι_mul_eq, incl, inv'_map]

/-- `𝒩(Λ ⊔ Λ)` is spanned by the products `A(ψ) B(ζ)`. -/
theorem span_incl_inclζ :
    Submodule.span ℂ {G : N (Λ ⊕ Λ) | ∃ A B : N Λ, G = incl A * inclζ B} = ⊤ := by
  set S := Submodule.span ℂ {G : N (Λ ⊕ Λ) | ∃ A B : N Λ, G = incl A * inclζ B}
  have hgen : ∀ A B : N Λ, incl A * inclζ B ∈ S := fun A B => Submodule.subset_span ⟨A, B, rfl⟩
  have hι : ∀ w : V (Λ ⊕ Λ), ∀ H ∈ S, ι ℂ w * H ∈ S := by
    intro w H hH
    induction hH using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨A, B, rfl⟩ := hx
      rw [vec_split w, map_add, add_mul]
      refine add_mem ?_ ?_
      · have : ι ℂ (inlV (projV w)) = incl (ι ℂ (projV w)) := by
          rw [incl, ExteriorAlgebra.map_apply_ι]
        rw [this, ← mul_assoc, ← map_mul]; exact hgen _ _
      · rw [← mul_assoc, inclζ_ι_mul_incl, mul_assoc,
          show ι ℂ (inrV (projRV w)) = inclζ (ι ℂ (projRV w)) by
            rw [inclζ, ExteriorAlgebra.map_apply_ι], ← map_mul]
        exact hgen _ _
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  have hall : ∀ X : N (Λ ⊕ Λ), ∀ H ∈ S, X * H ∈ S := by
    intro X
    induction X using CliffordAlgebra.induction with
    | algebraMap r => intro H hH; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ r hH
    | ι w => exact hι w
    | mul a b ha hb => intro H hH; rw [mul_assoc]; exact ha _ (hb H hH)
    | add a b ha hb => intro H hH; rw [add_mul]; exact add_mem (ha H hH) (hb H hH)
  refine eq_top_iff.2 fun G _ => ?_
  have := hall G 1 (by simpa using hgen 1 1)
  rwa [mul_one] at this

/-- `e:absorb` on the doubled algebra: `𝔼_C (e^{-q_B(ζ)} G) = ⟨e^{-q_B}⟩_C 𝔼_{C'} G`. -/
theorem ECC_exp_mul (C B : Matrix Λ Λ ℂ) (hT : IsUnit (1 - Bᵀ * C).det) (G : N (Λ ⊕ Λ)) :
    ECC C (inclζ (expQ B) * G) = omegaC C (expQ B) • ECC (Cdress C B) G := by
  have hG : G ∈ Submodule.span ℂ {G : N (Λ ⊕ Λ) | ∃ A B : N Λ, G = incl A * inclζ B} := by
    rw [span_incl_inclζ]; trivial
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, B', rfl⟩ := hx
    have hev : inv' (inclζ (expQ B)) = inclζ (expQ B) := by
      rw [inclζ, inv'_map, inv'_expQ']
    rw [← mul_assoc, mul_comm_of_even hev, mul_assoc, ← map_mul, ECC_incl_mul_inclζ,
      ECC_incl_mul_inclζ, omegaC_exp_mul C B hT, smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [mul_smul_comm, map_smul, map_smul, hx, smul_comm]

/-- `e:absorb` on the doubled algebra, with the determinant. -/
theorem ECC_exp_mul_det (C B : Matrix Λ Λ ℂ) (hT : IsUnit (1 - Bᵀ * C).det) (G : N (Λ ⊕ Λ)) :
    ECC C (inclζ (expQ B) * G) = (1 - Bᵀ * C).det • ECC (Cdress C B) G := by
  rw [ECC_exp_mul C B hT, omegaC_expQ]

end Doubled

end

end Grassmann
