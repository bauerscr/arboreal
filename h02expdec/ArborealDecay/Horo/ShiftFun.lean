module

public import ArborealDecay.Horo.Diffeo

/-!
# The horospherical shift function

After the bosonic change of variables `(t, s) ↦ (x, y)`, the remaining change of generators at
vertex `i` is `x_i ↦ x_i + g_i(x, y) n_i` with

  `g_i(x, y) = −1/(x_i + z_i) = −e^{−t_i}`,   `z_i = √(1 + x_i² + y_i²)`

(`gS`).  Its Berezinian factor is `1 + ∂_{x_i} g_i · n_i` with
`∂_{x_i} g_i = 1/(z_i (x_i + z_i))` (`gdS`, `fderiv_gS`), which in horospherical coordinates is
`e^{−t_i}/z_i` (`gdS_horo`).  Both `g_i` and `∂_{x_i} g_i` have temperate growth
(`hasTemperateGrowth_gS`, `hasTemperateGrowth_gdS`), via `g_i = (x_i − z_i)/(1 + y_i²)` and
`∂_{x_i} g_i = (1 − x_i/z_i)/(1 + y_i²)`.
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open Real Function

set_option linter.unusedSectionVars false

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `g_i(x, y) = −1/(x_i + z_i)`. -/
def gS (i : N) (q : N ⊕ N → ℝ) : ℝ := -(q (.inl i) + zOf (q (.inl i)) (q (.inr i)))⁻¹

/-- `∂_{x_i} g_i = 1/(z_i (x_i + z_i))`. -/
def gdS (i : N) (q : N ⊕ N → ℝ) : ℝ :=
  (zOf (q (.inl i)) (q (.inr i)) * (q (.inl i) + zOf (q (.inl i)) (q (.inr i))))⁻¹

/-- The unit vector `e_{x_i}`. -/
def exV (i : N) : N ⊕ N → ℝ := Pi.single (.inl i) 1

theorem zOf_pos (x y : ℝ) : 0 < zOf x y := sqrt_pos.2 (by positivity)

theorem zOf_sub_pos (x y : ℝ) : 0 < zOf x y - x := by
  have h := zOf_sq x y; have h0 := zOf_nonneg x y
  by_contra hc
  nlinarith [sq_nonneg y]

theorem add_zOf_mul_sub (x y : ℝ) : (x + zOf x y) * (zOf x y - x) = 1 + y ^ 2 := by
  have := zOf_sq x y; nlinarith

theorem gS_eq (i : N) (q : N ⊕ N → ℝ) :
    gS i q = (q (.inl i) - zOf (q (.inl i)) (q (.inr i))) * (1 + q (.inr i) ^ 2)⁻¹ := by
  have h1 := add_zOf_pos (q (.inl i)) (q (.inr i))
  have h2 := add_zOf_mul_sub (q (.inl i)) (q (.inr i))
  have h3 := zOf_sub_pos (q (.inl i)) (q (.inr i))
  rw [gS, ← h2]
  field_simp
  ring

theorem gdS_eq (i : N) (q : N ⊕ N → ℝ) :
    gdS i q = (1 - q (.inl i) * (zOf (q (.inl i)) (q (.inr i)))⁻¹) * (1 + q (.inr i) ^ 2)⁻¹ := by
  have h1 := add_zOf_pos (q (.inl i)) (q (.inr i))
  have h2 := add_zOf_mul_sub (q (.inl i)) (q (.inr i))
  have h0 := zOf_pos (q (.inl i)) (q (.inr i))
  have h3 := zOf_sub_pos (q (.inl i)) (q (.inr i))
  rw [gdS, ← h2]
  field_simp

/-! ### Temperate growth -/

/-- `q ↦ (x_i, y_i)` into the Euclidean plane. -/
def pairL (i : N) : (N ⊕ N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
      LinearMap.pi ![LinearMap.proj (.inl i), LinearMap.proj (.inr i)])

theorem norm_pairL_sq (i : N) (q : N ⊕ N → ℝ) :
    ‖pairL i q‖ ^ 2 = q (.inl i) ^ 2 + q (.inr i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [pairL, Real.norm_eq_abs, sq_abs]

theorem zOf_rpow (i : N) (r : ℝ) (q : N ⊕ N → ℝ) :
    zOf (q (.inl i)) (q (.inr i)) ^ (2 * r) = (1 + ‖pairL i q‖ ^ 2) ^ r := by
  rw [norm_pairL_sq, rpow_mul (zOf_nonneg _ _), ← add_assoc]
  norm_cast
  rw [zOf_sq]

theorem hasTemperateGrowth_zOf_rpow (i : N) (r : ℝ) :
    (fun q : N ⊕ N → ℝ => zOf (q (.inl i)) (q (.inr i)) ^ (2 * r)).HasTemperateGrowth := by
  have := (hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin 2)) r).comp
    (pairL i).hasTemperateGrowth
  convert this using 1
  funext q
  simp only [Function.comp_apply, zOf_rpow]

theorem hasTemperateGrowth_zOf (i : N) :
    (fun q : N ⊕ N → ℝ => zOf (q (.inl i)) (q (.inr i))).HasTemperateGrowth := by
  convert hasTemperateGrowth_zOf_rpow i (1 / 2) using 1
  funext q; norm_num

theorem hasTemperateGrowth_zOf_inv (i : N) :
    (fun q : N ⊕ N → ℝ => (zOf (q (.inl i)) (q (.inr i)))⁻¹).HasTemperateGrowth := by
  convert hasTemperateGrowth_zOf_rpow i (-1 / 2) using 1
  funext q
  rw [show 2 * (-1 / 2 : ℝ) = -1 by norm_num, rpow_neg_one]

theorem hasTemperateGrowth_coord (k : N ⊕ N) :
    (fun q : N ⊕ N → ℝ => q k).HasTemperateGrowth :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N ⊕ N => ℝ) k).hasTemperateGrowth

theorem hasTemperateGrowth_inv_one_add_sq (k : N ⊕ N) :
    (fun q : N ⊕ N → ℝ => (1 + q k ^ 2)⁻¹).HasTemperateGrowth := by
  have := (hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N ⊕ N => ℝ) k).hasTemperateGrowth
  convert this using 1
  funext q
  simp [Real.norm_eq_abs, sq_abs, rpow_neg_one]

theorem hasTemperateGrowth_gS (i : N) : (gS i).HasTemperateGrowth := by
  have := ((hasTemperateGrowth_coord (.inl i)).sub (hasTemperateGrowth_zOf i)).mul
    (hasTemperateGrowth_inv_one_add_sq (.inr i))
  convert this using 1
  funext q; rw [gS_eq]; rfl

theorem hasTemperateGrowth_gdS (i : N) : (gdS i).HasTemperateGrowth := by
  have := (((HasTemperateGrowth.const (1 : ℝ)).sub
    ((hasTemperateGrowth_coord (.inl i)).mul (hasTemperateGrowth_zOf_inv i))).mul
    (hasTemperateGrowth_inv_one_add_sq (.inr i)))
  convert this using 1
  funext q; rw [gdS_eq]; rfl

/-! ### The derivative -/

/-- A directional derivative can be computed along the line. -/
theorem fderiv_apply_eq_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    {q v : E} {d : ℝ} (hg : DifferentiableAt ℝ g q)
    (hd : HasDerivAt (fun c : ℝ => g (q + c • v)) d 0) : fderiv ℝ g q v = d := by
  have hline : HasDerivAt (fun c : ℝ => q + c • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hg' : HasFDerivAt g (fderiv ℝ g q) (q + (0 : ℝ) • v) := by simpa using hg.hasFDerivAt
  exact (hg'.comp_hasDerivAt (0 : ℝ) hline).unique hd

/-- The one-variable profile `u ↦ −1/(u + √(1 + u² + y²))`. -/
theorem hasDerivAt_gprofile (u y : ℝ) :
    HasDerivAt (fun u => -(u + zOf u y)⁻¹) (zOf u y * (u + zOf u y))⁻¹ u := by
  have hR : HasDerivAt (fun u : ℝ => 1 + u ^ 2 + y ^ 2) (2 * u) u := by
    simpa using (((hasDerivAt_id u).pow 2).const_add 1).add_const (y ^ 2)
  have hz : HasDerivAt (fun u => zOf u y) (2 * u / (2 * zOf u y)) u :=
    hR.sqrt (by positivity)
  have hw : HasDerivAt (fun u => (u + zOf u y)⁻¹)
      (-(1 + 2 * u / (2 * zOf u y)) / (u + zOf u y) ^ 2) u :=
    ((hasDerivAt_id' u).add hz).inv (add_zOf_pos u y).ne'
  convert hw.neg using 1
  have h0 := zOf_pos u y
  have h1 := add_zOf_pos u y
  field_simp
  ring

theorem fderiv_gS (i : N) (q : N ⊕ N → ℝ) : fderiv ℝ (gS i) q (exV i) = gdS i q := by
  refine fderiv_apply_eq_of_line
    ((hasTemperateGrowth_gS i).1.differentiable (by simp) q) ?_
  have e : (fun c : ℝ => gS i (q + c • exV i)) =
      (fun u => -(u + zOf u (q (.inr i)))⁻¹) ∘ fun c => q (.inl i) + c := by
    funext c
    simp [gS, exV]
  rw [e]
  have h := hasDerivAt_gprofile (q (.inl i) + 0) (q (.inr i))
  have := h.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (q (.inl i)))
  simpa [gdS] using this

/-- `∂_{x_i} g_i = e^{−t_i}/z_i` in horospherical coordinates. -/
theorem gdS_horo (i : N) (p : N ⊕ N → ℝ) :
    gdS i (horo p) = exp (-p (.inl i)) * (hz (p (.inl i)) (p (.inr i)))⁻¹ := by
  rw [gdS, horo_inl, horo_inr, zOf_horo, hx_add_hz, exp_neg, mul_inv, mul_comm]

/-- `g_i = −e^{−t_i}` in horospherical coordinates. -/
theorem gS_horo (i : N) (p : N ⊕ N → ℝ) : gS i (horo p) = -exp (-p (.inl i)) := by
  rw [gS, horo_inl, horo_inr, zOf_horo, hx_add_hz, exp_neg]

/-- `∂_{x_i} g_i` depends only on `(x_i, y_i)`. -/
theorem gdS_add_exV {i k : N} (h : i ≠ k) (q : N ⊕ N → ℝ) (c : ℝ) :
    gdS i (q + c • exV k) = gdS i q := by
  have h1 : (Sum.inl i : N ⊕ N) ≠ .inl k := fun e => h (Sum.inl_injective e)
  simp [gdS, exV, h1]

end

end ArborealDecay.Horo

end
