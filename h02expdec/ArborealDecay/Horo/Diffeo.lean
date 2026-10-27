module

public import Mathlib

/-!
# The bosonic horospherical diffeomorphism

BCHS v2 (`refs/BCHS/src/h02.tex` L1551–1563), bosonic part of (2.73): per vertex
`x = sinh t − ½ eᵗ s²`, `y = eᵗ s`, and then `z = √(1 + x² + y²) = cosh t + ½ eᵗ s²`.

On `N ⊕ N → ℝ` (`inl i` ↦ first coordinate `t_i` resp. `x_i`, `inr i` ↦ second coordinate
`s_i` resp. `y_i`, the convention of `ArborealDecay.Super.Pt`) we define

* `horo : (N ⊕ N → ℝ) → (N ⊕ N → ℝ)`, `(t, s) ↦ (x, y)` vertexwise;
* `horoInv`, `(x, y) ↦ (log (x + z), y / (x + z))` with `z = √(1 + x² + y²)`;
* `horoJac p`: the Jacobian matrix, `horoJac_det : det = ∏_i e^{t_i} z_i`;
* `integral_horo`: `∫ g(x, y) dx dy = ∫ (∏_i e^{t_i} z_i(t, s)) • g(horo (t, s)) dt ds`, for
  every `g` (both sides are Bochner integrals; non-integrability transfers too,
  `integrable_horo_iff`).
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open MeasureTheory Real Matrix

set_option linter.unusedSectionVars false

/-! ### One vertex -/

/-- `x(t, s) = sinh t − ½ eᵗ s²`. -/
def hx (t s : ℝ) : ℝ := sinh t - exp t * s ^ 2 / 2

/-- `y(t, s) = eᵗ s`. -/
def hy (t s : ℝ) : ℝ := exp t * s

/-- `z(t, s) = cosh t + ½ eᵗ s²`. -/
def hz (t s : ℝ) : ℝ := cosh t + exp t * s ^ 2 / 2

theorem hx_add_hz (t s : ℝ) : hx t s + hz t s = exp t := by
  simp only [hx, hz]; rw [← sinh_add_cosh]; ring

theorem hz_sub_hx (t s : ℝ) : hz t s - hx t s = exp (-t) + exp t * s ^ 2 := by
  simp only [hx, hz]; rw [cosh_eq, sinh_eq]; ring

theorem hz_pos (t s : ℝ) : 0 < hz t s := by
  have := cosh_pos t; have := exp_pos t; unfold hz; positivity

theorem hz_sq (t s : ℝ) : hz t s ^ 2 = 1 + hx t s ^ 2 + hy t s ^ 2 := by
  have h1 := cosh_sq_sub_sinh_sq t
  have h2 : sinh t + cosh t = exp t := sinh_add_cosh t
  simp only [hx, hy, hz]
  linear_combination h1 + exp t * s ^ 2 * h2

/-- `z = √(1 + x² + y²)` in horospherical coordinates. -/
theorem sqrt_horo (t s : ℝ) : √(1 + hx t s ^ 2 + hy t s ^ 2) = hz t s := by
  rw [← hz_sq, sqrt_sq (hz_pos t s).le]

/-- `√(1 + x² + y²)`. -/
def zOf (x y : ℝ) : ℝ := √(1 + x ^ 2 + y ^ 2)

theorem zOf_sq (x y : ℝ) : zOf x y ^ 2 = 1 + x ^ 2 + y ^ 2 := sq_sqrt (by positivity)

theorem zOf_nonneg (x y : ℝ) : 0 ≤ zOf x y := sqrt_nonneg _

theorem add_zOf_pos (x y : ℝ) : 0 < x + zOf x y := by
  have h := zOf_sq x y; have h0 := zOf_nonneg x y
  by_contra hc
  nlinarith [sq_nonneg y]

/-- The inverse at one vertex: `t = log (x + z)`. -/
def ht (x y : ℝ) : ℝ := log (x + zOf x y)

/-- The inverse at one vertex: `s = y / (x + z)`. -/
def hs (x y : ℝ) : ℝ := y / (x + zOf x y)

theorem exp_ht (x y : ℝ) : exp (ht x y) = x + zOf x y := exp_log (add_zOf_pos x y)

theorem hx_inv (x y : ℝ) : hx (ht x y) (hs x y) = x := by
  have hw := add_zOf_pos x y
  have hz := zOf_sq x y
  simp only [hx, hs, sinh_eq, exp_neg, exp_ht]
  field_simp
  linear_combination hz

theorem hy_inv (x y : ℝ) : hy (ht x y) (hs x y) = y := by
  have hw := add_zOf_pos x y
  simp only [hy, hs, exp_ht]; field_simp

theorem zOf_horo (t s : ℝ) : zOf (hx t s) (hy t s) = hz t s := sqrt_horo t s

theorem ht_horo (t s : ℝ) : ht (hx t s) (hy t s) = t := by
  rw [ht, zOf_horo, hx_add_hz, log_exp]

theorem hs_horo (t s : ℝ) : hs (hx t s) (hy t s) = s := by
  rw [hs, zOf_horo, hx_add_hz, hy]; field_simp [(exp_pos t).ne']

/-! ### All vertices -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The horospherical map `(t, s) ↦ (x, y)` on `N ⊕ N → ℝ`. -/
def horo (p : N ⊕ N → ℝ) : N ⊕ N → ℝ
  | .inl i => hx (p (.inl i)) (p (.inr i))
  | .inr i => hy (p (.inl i)) (p (.inr i))

/-- The inverse map `(x, y) ↦ (t, s)`. -/
def horoInv (q : N ⊕ N → ℝ) : N ⊕ N → ℝ
  | .inl i => ht (q (.inl i)) (q (.inr i))
  | .inr i => hs (q (.inl i)) (q (.inr i))

@[simp] theorem horo_inl (p : N ⊕ N → ℝ) (i : N) :
    horo p (.inl i) = hx (p (.inl i)) (p (.inr i)) := rfl

@[simp] theorem horo_inr (p : N ⊕ N → ℝ) (i : N) :
    horo p (.inr i) = hy (p (.inl i)) (p (.inr i)) := rfl

@[simp] theorem horoInv_inl (q : N ⊕ N → ℝ) (i : N) :
    horoInv q (.inl i) = ht (q (.inl i)) (q (.inr i)) := rfl

@[simp] theorem horoInv_inr (q : N ⊕ N → ℝ) (i : N) :
    horoInv q (.inr i) = hs (q (.inl i)) (q (.inr i)) := rfl

theorem horoInv_horo (p : N ⊕ N → ℝ) : horoInv (horo p) = p := by
  funext k; cases k with
  | inl i => simp [ht_horo]
  | inr i => simp [hs_horo]

theorem horo_horoInv (q : N ⊕ N → ℝ) : horo (horoInv q) = q := by
  funext k; cases k with
  | inl i => simp [hx_inv]
  | inr i => simp [hy_inv]

/-- The horospherical map as an equivalence. -/
def horoEquiv : (N ⊕ N → ℝ) ≃ (N ⊕ N → ℝ) where
  toFun := horo
  invFun := horoInv
  left_inv := horoInv_horo
  right_inv := horo_horoInv

theorem horo_injective : Function.Injective (horo : (N ⊕ N → ℝ) → _) :=
  horoEquiv.injective

theorem horo_surjective : Function.Surjective (horo : (N ⊕ N → ℝ) → _) :=
  horoEquiv.surjective

/-! ### Smoothness -/

theorem contDiff_horo : ContDiff ℝ ⊤ (horo : (N ⊕ N → ℝ) → _) := by
  rw [contDiff_pi]
  intro k
  cases k with
  | inl i =>
    have h1 : ContDiff ℝ ⊤ fun p : N ⊕ N → ℝ => p (.inl i) := contDiff_apply ℝ ℝ _
    have h2 : ContDiff ℝ ⊤ fun p : N ⊕ N → ℝ => p (.inr i) := contDiff_apply ℝ ℝ _
    simp only [horo_inl, hx]
    exact (h1.sinh).sub (((h1.exp).mul (h2.pow 2)).div_const 2)
  | inr i =>
    have h1 : ContDiff ℝ ⊤ fun p : N ⊕ N → ℝ => p (.inl i) := contDiff_apply ℝ ℝ _
    have h2 : ContDiff ℝ ⊤ fun p : N ⊕ N → ℝ => p (.inr i) := contDiff_apply ℝ ℝ _
    simp only [horo_inr, hy]
    exact (h1.exp).mul h2

theorem contDiff_horoInv : ContDiff ℝ ⊤ (horoInv : (N ⊕ N → ℝ) → _) := by
  rw [contDiff_pi]
  intro k
  cases k with
  | inl i =>
    have h1 : ContDiff ℝ ⊤ fun q : N ⊕ N → ℝ => q (.inl i) := contDiff_apply ℝ ℝ _
    have h2 : ContDiff ℝ ⊤ fun q : N ⊕ N → ℝ => q (.inr i) := contDiff_apply ℝ ℝ _
    have hz : ContDiff ℝ ⊤ fun q : N ⊕ N → ℝ => zOf (q (.inl i)) (q (.inr i)) :=
      ((contDiff_const.add (h1.pow 2)).add (h2.pow 2)).sqrt fun q => by positivity
    simp only [horoInv_inl, ht]
    exact (h1.add hz).log fun q => (add_zOf_pos _ _).ne'
  | inr i =>
    have h1 : ContDiff ℝ ⊤ fun q : N ⊕ N → ℝ => q (.inl i) := contDiff_apply ℝ ℝ _
    have h2 : ContDiff ℝ ⊤ fun q : N ⊕ N → ℝ => q (.inr i) := contDiff_apply ℝ ℝ _
    have hz : ContDiff ℝ ⊤ fun q : N ⊕ N → ℝ => zOf (q (.inl i)) (q (.inr i)) :=
      ((contDiff_const.add (h1.pow 2)).add (h2.pow 2)).sqrt fun q => by positivity
    simp only [horoInv_inr, hs]
    exact h2.div (h1.add hz) fun q => (add_zOf_pos _ _).ne'

/-! ### The Jacobian -/

/-- `∂x/∂t = cosh t − ½ eᵗ s²`. -/
def jA (t s : ℝ) : ℝ := cosh t - exp t * s ^ 2 / 2
/-- `∂x/∂s = −eᵗ s`. -/
def jB (t s : ℝ) : ℝ := -(exp t * s)
/-- `∂y/∂t = eᵗ s`. -/
def jC (t s : ℝ) : ℝ := exp t * s
/-- `∂y/∂s = eᵗ`. -/
def jD (t : ℝ) : ℝ := exp t

/-- The Jacobian matrix of `horo` at `p`, in `(inl, inr)` block form. -/
def horoJac (p : N ⊕ N → ℝ) : Matrix (N ⊕ N) (N ⊕ N) ℝ :=
  fromBlocks (diagonal fun i => jA (p (.inl i)) (p (.inr i)))
    (diagonal fun i => jB (p (.inl i)) (p (.inr i)))
    (diagonal fun i => jC (p (.inl i)) (p (.inr i)))
    (diagonal fun i => jD (p (.inl i)))

/-- The derivative of `horo` at `p`. -/
def horoD (p : N ⊕ N → ℝ) : (N ⊕ N → ℝ) →L[ℝ] (N ⊕ N → ℝ) :=
  LinearMap.toContinuousLinearMap (toLin' (horoJac p))

theorem horoD_apply_inl (p v : N ⊕ N → ℝ) (i : N) :
    horoD p v (.inl i) = jA (p (.inl i)) (p (.inr i)) * v (.inl i) +
      jB (p (.inl i)) (p (.inr i)) * v (.inr i) := by
  simp [horoD, horoJac, mulVec, dotProduct, Fintype.sum_sum_type, diagonal_apply]

theorem horoD_apply_inr (p v : N ⊕ N → ℝ) (i : N) :
    horoD p v (.inr i) = jC (p (.inl i)) (p (.inr i)) * v (.inl i) +
      jD (p (.inl i)) * v (.inr i) := by
  simp [horoD, horoJac, mulVec, dotProduct, Fintype.sum_sum_type, diagonal_apply]

theorem hasFDerivAt_horo (p : N ⊕ N → ℝ) : HasFDerivAt horo (horoD p) p := by
  rw [hasFDerivAt_pi']
  intro k
  have h1 (i : N) := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : N ⊕ N => ℝ) (.inl i) p
  have h2 (i : N) := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : N ⊕ N => ℝ) (.inr i) p
  cases k with
  | inl i =>
    have he := HasFDerivAt.exp (h1 i)
    have hp := HasFDerivAt.pow (h2 i) 2
    have hm := HasFDerivAt.mul he hp
    have hd := HasFDerivAt.mul_const hm (1 / 2 : ℝ)
    have h := HasFDerivAt.sub (HasFDerivAt.sinh (h1 i)) hd
    have hfun : (fun q : N ⊕ N → ℝ => horo q (.inl i)) = fun q =>
        sinh (q (.inl i)) - rexp (q (.inl i)) * q (.inr i) ^ 2 * (1 / 2) := by
      funext q; simp only [horo_inl, hx]; ring
    rw [hfun]
    refine h.congr_fderiv ?_
    ext v
    simp [horoD_apply_inl, jA, jB]
    ring
  | inr i =>
    have h := (h1 i).exp.mul (h2 i)
    refine h.congr_fderiv ?_
    ext v
    simp [horoD_apply_inr, jC, jD]
    ring

/-- The Jacobian determinant: `det D horo (t, s) = ∏_i e^{t_i} z(t_i, s_i)`. -/
theorem horoJac_det (p : N ⊕ N → ℝ) :
    (horoJac p).det = ∏ i, exp (p (.inl i)) * hz (p (.inl i)) (p (.inr i)) := by
  set D : Matrix N N ℝ := diagonal fun i => jD (p (.inl i))
  have hD : IsUnit D.det := by
    rw [det_diagonal]; exact (Finset.prod_pos fun i _ => exp_pos _).ne'.isUnit
  let _ : Invertible D := invertibleOfIsUnitDet D hD
  have hinv : ⅟D = diagonal fun i => (jD (p (.inl i)))⁻¹ := by
    refine invOf_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (exp_pos _).ne'
  rw [horoJac, det_fromBlocks₂₂, hinv, diagonal_mul_diagonal,
    diagonal_mul_diagonal, diagonal_sub, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have he := (exp_pos (p (.inl i))).ne'
  simp only [jA, jB, jC, jD, hz]
  field_simp
  ring

theorem horoD_det (p : N ⊕ N → ℝ) :
    (horoD p).det = ∏ i, exp (p (.inl i)) * hz (p (.inl i)) (p (.inr i)) := by
  rw [← horoJac_det, horoD, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin']

/-- The horospherical density `∏_i e^{t_i} z_i`. -/
def horoDens (p : N ⊕ N → ℝ) : ℝ := ∏ i, exp (p (.inl i)) * hz (p (.inl i)) (p (.inr i))

theorem horoDens_pos (p : N ⊕ N → ℝ) : 0 < horoDens p :=
  Finset.prod_pos fun _ _ => mul_pos (exp_pos _) (hz_pos _ _)

theorem abs_horoD_det (p : N ⊕ N → ℝ) : |(horoD p).det| = horoDens p := by
  rw [horoD_det]; exact abs_of_pos (horoDens_pos p)

/-! ### Change of variables -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Horospherical change of variables** (bosonic part):
`∫ g(x, y) dx dy = ∫ g(x(t, s), y(t, s)) ∏_i e^{t_i} z_i dt ds`. -/
theorem integral_horo (g : (N ⊕ N → ℝ) → E) :
    ∫ q, g q = ∫ p, horoDens p • g (horo p) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun p _ => (hasFDerivAt_horo p).hasFDerivWithinAt) horo_injective.injOn g
  rw [Set.image_univ_of_surjective horo_surjective, setIntegral_univ, setIntegral_univ] at h
  simpa only [abs_horoD_det] using h

theorem integrable_horo_iff (g : (N ⊕ N → ℝ) → E) :
    Integrable g ↔ Integrable fun p => horoDens p • g (horo p) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
    (fun p _ => (hasFDerivAt_horo p).hasFDerivWithinAt) horo_injective.injOn g
  rw [Set.image_univ_of_surjective horo_surjective, integrableOn_univ, integrableOn_univ] at h
  simpa only [abs_horoD_det] using h

end

end ArborealDecay.Horo

end
