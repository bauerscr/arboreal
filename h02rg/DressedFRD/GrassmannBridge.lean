import DressedFRD.GramRep
import Grassmann.TorusC

/-!
# Dressed covariances in the Grassmann contraction estimate

For a symbol `w` let `kmat w` be the covariance matrix `(x, y) ↦ k(x - y)`, `k = kern w`.

* `kmat_isGram`: `kmat w` has the Gram representation of `lem:norm`(ii), with vectors in
  `EuclideanSpace ℂ Λ*` (`gramF`, `gramG`).
* `kmat_gramBound`: if `‖w‖_{(s)} ≤ κ` and `2 p ≤ q`, these vectors satisfy
  `GramBound (Dir d) p (L^s) ℓ` with `ℓ = κ^{1/2} L^{-s(d-2)/2}`.
* `Tj_ECC_theta_le_of_snorm`: hence `‖𝔼_{kmat w} θ F‖_{T_s(ℓ)} ≤ ‖F‖_{T_s(2ℓ)}` for every
  Gram-admissible `w`, positive or not. This is the replacement of `e:E-contract` used for
  `Γ^int_{j+1}` (`cor:rg`(a)), in every dimension.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- The covariance matrix of a symbol. -/
def kmat (w : Sym d n) : Matrix (Torus d n) (Torus d n) ℂ := fun x y => kern w (x - y)

/-- `|Λ|^{-1/2}`. -/
def sc (d n : ℕ) : ℝ := Real.sqrt ((n : ℝ) ^ d)⁻¹

theorem sc_sq : (sc d n) ^ 2 = ((n : ℝ) ^ d)⁻¹ := by
  rw [sc, Real.sq_sqrt (by positivity)]

/-- The left Gram vectors `x ↦ |Λ|^{-1/2} f_x`. -/
def gramF (w : Sym d n) (x : Torus d n) : EuclideanSpace ℂ (Torus d n) :=
  WithLp.toLp 2 fun m => (sc d n : ℂ) * gF w 0 x m

/-- The right Gram vectors `y ↦ |Λ|^{-1/2} g_y`. -/
def gramG (w : Sym d n) (y : Torus d n) : EuclideanSpace ℂ (Torus d n) :=
  WithLp.toLp 2 fun m => (sc d n : ℂ) * gG w 0 y m

theorem dop_zero (f : Torus d n → ℂ) (x : Torus d n) : dop 0 f x = f x := by
  have : Iic (0 : Dir d → ℕ) = {0} := by ext b; simp [nonpos_iff_eq_zero]
  simp [dop, cf, this]

theorem kmat_isGram (w : Sym d n) : IsGram (kmat w) (gramF w) (gramG w) := by
  intro x y
  have h := gram_rep w 0 0 x y
  simp only [dop_zero] at h
  rw [kmat, h, avgC]
  simp only [gramF, gramG, PiLp.inner_apply, RCLike.inner_apply, map_mul, conj_ofReal, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have hs : ((sc d n : ℂ)) * (sc d n : ℂ) = (((n : ℝ) ^ d)⁻¹ : ℝ) := by
    rw [← ofReal_mul, ← sq, sc_sq]
  push_cast at hs
  rw [← hs]; ring

/-- `∑_b c_{a,b} f(b + x) = ∇^a f(x)` for the profile `dprof`. -/
theorem sum_dprof_smul {H : Type*} [AddCommGroup H] [Module ℂ H] (a : Dir d → ℕ) (x : Torus d n)
    (v : Torus d n → H) :
    ∑ y, ((dprof a x y : ℝ) : ℂ) • v y = ∑ b ∈ Iic a, ((cf a b : ℝ) : ℂ) • v (b +ᵥ x) := by
  simp only [dprof, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul, sum_smul]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  simp [Pi.single_apply, mul_smul]

theorem gF_dop (w : Sym d n) (a : Dir d → ℕ) (x m : Torus d n) :
    ∑ b ∈ Iic a, ((cf a b : ℝ) : ℂ) * gF w 0 (b +ᵥ x) m = gF w a x m := by
  have h := dop_char a m x
  unfold dop at h
  simp only [gF, sigma_zero, one_mul, map_mul]
  have e : ∑ b ∈ Iic a, ((cf a b : ℝ) : ℂ) * ((starRingEnd ℂ) (Real.sqrt ‖w m‖ : ℂ) *
      (starRingEnd ℂ) (char m (b +ᵥ x))) =
      (starRingEnd ℂ) (Real.sqrt ‖w m‖ : ℂ) * (starRingEnd ℂ) (dop a (char m) x) := by
    rw [dop, map_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
  rw [e, dop_char, sigma]
  simp only [map_mul, map_prod, map_pow]
  ring

theorem gG_dop (w : Sym d n) (a : Dir d → ℕ) (y m : Torus d n) :
    ∑ b ∈ Iic a, ((cf a b : ℝ) : ℂ) * gG w 0 (b +ᵥ y) m = gG w a y m := by
  have h := dop_char a (-m) y
  simp only [gG, sigma_zero, one_mul]
  have e : ∑ b ∈ Iic a, ((cf a b : ℝ) : ℂ) * (sgn (w m) * (Real.sqrt ‖w m‖ : ℂ) *
      char (-m) (b +ᵥ y)) = sgn (w m) * (Real.sqrt ‖w m‖ : ℂ) * dop a (char (-m)) y := by
    rw [dop, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [Complex.real_smul]; ring
  rw [e, h, sigma]
  ring

theorem gvec_gramF (w : Sym d n) (a : Dir d → ℕ) (x : Torus d n) :
    gvec (gramF w) (dprof a x) = WithLp.toLp 2 fun m => (sc d n : ℂ) * gF w a x m := by
  rw [gvec, sum_dprof_smul]
  ext m
  simp only [gramF, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, PiLp.toLp_apply]
  rw [← gF_dop, mul_sum]
  refine sum_congr rfl fun b _ => by ring

theorem gvec_gramG (w : Sym d n) (a : Dir d → ℕ) (y : Torus d n) :
    gvec (gramG w) (dprof a y) = WithLp.toLp 2 fun m => (sc d n : ℂ) * gG w a y m := by
  rw [gvec, sum_dprof_smul]
  ext m
  simp only [gramG, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, PiLp.toLp_apply]
  rw [← gG_dop, mul_sum]
  refine sum_congr rfl fun b _ => by ring

theorem norm_toLp_sc_sq (f : Torus d n → ℂ) :
    ‖(WithLp.toLp 2 fun m => (sc d n : ℂ) * f m : EuclideanSpace ℂ (Torus d n))‖ ^ 2 =
      avg fun m => ‖f m‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun m _ => sq_nonneg _), avg, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  simp only [PiLp.toLp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    sc_sq]

variable {L : ℝ} {q s p : ℕ}

theorem norm_le_of_sq_le {v X : ℝ} (hv : 0 ≤ v) (hX : 0 ≤ X) (h : v ^ 2 ≤ X ^ 2) : v ≤ X := by
  nlinarith

/-- The Gram bound for a symbol with `‖w‖_{(s)} ≤ κ`. -/
theorem kmat_gramBound (hL : 0 < L) (hpq : 2 * p ≤ q) {w : Sym d n} {κ : ℝ}
    (hw : snorm L q s w ≤ κ) :
    GramBound (Dir d) p (L ^ s) (Real.sqrt κ * L ^ (-((s : ℝ) * ((d : ℝ) - 2)) / 2))
      (gramF w) (gramG w) := by
  have hκ : 0 ≤ κ := (snorm_nonneg hL w).trans hw
  intro a ha x
  have h2a : 2 * Grassmann.mabs a ≤ q := by omega
  set X := Real.sqrt κ * L ^ (-((s : ℝ) * ((d : ℝ) - 2)) / 2) * ((L ^ s) ^ Grassmann.mabs a)⁻¹
  have hX0 : 0 ≤ X := by positivity
  have e1 : ((L ^ s) ^ Grassmann.mabs a)⁻¹ = L ^ (-((s : ℝ) * Grassmann.mabs a)) := by
    rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_neg hL.le]; push_cast; rfl
  have e2 : X = Real.sqrt κ * L ^ (-((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs a)) / 2) := by
    simp only [X]; rw [e1, mul_assoc, ← Real.rpow_add hL]; congr 2; ring
  have hX2 : X ^ 2 = L ^ (-((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs a))) * κ := by
    rw [e2, mul_pow, Real.sq_sqrt hκ, ← Real.rpow_natCast, ← Real.rpow_mul hL.le, mul_comm]
    congr 2; push_cast; ring
  have hbd : ∀ f : Torus d n → ℂ, avg (fun m => ‖f m‖ ^ 2) ≤
      L ^ (-((s : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs a))) * snorm L q s w →
      ‖(WithLp.toLp 2 fun m => (sc d n : ℂ) * f m : EuclideanSpace ℂ (Torus d n))‖ ≤ X := by
    intro f hf
    refine norm_le_of_sq_le (norm_nonneg _) hX0 ?_
    rw [norm_toLp_sc_sq, hX2]
    exact hf.trans (mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hL.le _))
  exact ⟨by rw [gvec_gramF]; exact hbd _ (gF_norm_le hL h2a w x),
    by rw [gvec_gramG]; exact hbd _ (gG_norm_le hL h2a w x)⟩

/-- `e:E-contract` for a Gram-admissible symbol, in every dimension:
`‖𝔼_{kmat w} θ F‖_{T_s(ℓ)} ≤ ‖F‖_{T_s(2ℓ)}` with `ℓ = κ^{1/2} L^{-s(d-2)/2}`, for
`‖w‖_{(s)} ≤ κ` and `2 p_Φ ≤ q`. -/
theorem Tj_ECC_theta_le_of_snorm (hL : 0 < L) (hpq : 2 * pPhi d ≤ q) {w : Sym d n} {κ : ℝ}
    (hκ : 0 < κ) (hw : snorm L q s w ≤ κ) (F : N (Torus d n)) :
    Tj d L s (Real.sqrt κ * L ^ (-((s : ℝ) * ((d : ℝ) - 2)) / 2)) (ECC (kmat w) (theta F)) ≤
      Tj d L s (2 * (Real.sqrt κ * L ^ (-((s : ℝ) * ((d : ℝ) - 2)) / 2))) F :=
  Tj_ECC_theta_le hL (by positivity) s (kmat_isGram w) (kmat_gramBound hL hpq hw) F

end

end DressedFRD
