import Cont.LatGreen
import Cont.TorusHeat

/-!
# The lattice heat kernel on the discrete torus (B1, scaling limit, lattice side)

`latHeat t x = (e^{tΔ})(x, 0) = |Λ|⁻¹ ∑_k e^{-tλ(k)} cos(k·x)` on `Λ = Torus d n`.

* `latHeat_add` : semigroup property `p_{s+s'}(x) = ∑_y p_s(x - y) p_{s'}(y)`;
* `latHeat_nonneg` : positivity (power series of `e^{t∑_e τ_e}` in the shift operators);
* `latHeat_le_zero` : `p_t(x) ≤ p_t(0)`;
* `sum_lam_mul_latHeat_le` : the second-moment bound `∑_y λ(y) p_s(y) ≤ 8d²π² s / n²`
  (`λ(y) = ∑_i (2 - 2cos(2π y_i/n))` is a torus version of `|y|²`);
* `latHeat_zero_le` : on-diagonal bound `p_s(0) ≤ (C(1/n + 1/√s))^d`, `C = evenKernel 0 1`;
* `lam_mul_latHeat_le` (`d = 2`) : `λ(x) p_{2s}(x) ≤ 256 π² C² (s/n⁴ + 1/n²)`.

The last estimate replaces a pointwise off-diagonal (Carne–Varopoulos) bound: it is uniform in
`n` and gives smallness of the short-time part of the lattice Green function at macroscopic
distance.
-/

namespace Cont

noncomputable section

open FRD Grassmann Finset Real HurwitzZeta

variable {d n : ℕ} [NeZero n]

/-- The lattice heat kernel `p_t(x) = (e^{tΔ})(x, 0)`. -/
def latHeat (t : ℝ) (x : Torus d n) : ℝ := fmat (fun m ↦ Real.exp (-t * lam m)) x 0

lemma b1c_heatSym_even (t : ℝ) : Even' (fun m : Torus d n ↦ Real.exp (-t * lam m)) :=
  fun m ↦ by simp only [lam_neg]

lemma b1c_fmat_apply_sub (w : Torus d n → ℝ) (x y : Torus d n) :
    fmat w x y = fmat w (x - y) 0 := by
  simp [fmat]

/-- Semigroup property. -/
lemma latHeat_add (s s' : ℝ) (x : Torus d n) :
    latHeat (s + s') x = ∑ y, latHeat s (x - y) * latHeat s' y := by
  have h := congrFun (congrFun (fmat_mul (b1c_heatSym_even (d := d) (n := n) s)
    (b1c_heatSym_even s')) x) 0
  rw [Matrix.mul_apply] at h
  have : (fun m : Torus d n ↦ Real.exp (-(s + s') * lam m)) =
      fun m ↦ Real.exp (-s * lam m) * Real.exp (-s' * lam m) := by
    funext m; rw [← Real.exp_add]; ring_nf
  simp only [latHeat]
  rw [this, ← h]
  exact Fintype.sum_congr _ _ fun y ↦ by rw [b1c_fmat_apply_sub _ x y]

lemma b1c_norm_char (m x : Torus d n) : ‖char m x‖ = 1 := by
  simp [char, norm_prod, ZMod.stdAddChar_apply]

/-- `p_t(x) ≤ p_t(0)`. -/
lemma latHeat_le_zero (t : ℝ) (x : Torus d n) : latHeat t x ≤ latHeat t (0 : Torus d n) := by
  simp only [latHeat, fmat, sub_zero, char_zero_right, Complex.one_re, mul_one]
  gcongr with m
  exact mul_le_of_le_one_right (Real.exp_pos _).le
    ((Complex.re_le_norm _).trans (b1c_norm_char m x).le)

lemma latHeat_zero_eq (t : ℝ) :
    latHeat t (0 : Torus d n) = ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, Real.exp (-t * lam m) := by
  simp [latHeat, fmat, char_zero_right]

/-- Fourier coefficients of the heat kernel (complex form). -/
lemma b1c_sum_latHeat_char_c (t : ℝ) (m' : Torus d n) :
    ∑ y, (latHeat t y : ℂ) * char m' y = (Real.exp (-t * lam m') : ℂ) := by
  simp only [latHeat, fmat_complex (b1c_heatSym_even t), sub_zero, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  have hc : ((n : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))
  have key : ∀ m : Torus d n, ∑ y, ((n : ℂ) ^ d)⁻¹ * ((Real.exp (-t * lam m) : ℂ) * char m y) *
      char m' y = if m = -m' then (Real.exp (-t * lam m') : ℂ) else 0 := by
    intro m
    have : ∀ y, ((n : ℂ) ^ d)⁻¹ * ((Real.exp (-t * lam m) : ℂ) * char m y) * char m' y =
        ((n : ℂ) ^ d)⁻¹ * (Real.exp (-t * lam m) : ℂ) * char (m + m') y := fun y ↦ by
      rw [char_add_left]; ring
    rw [Fintype.sum_congr _ _ this, ← Finset.mul_sum, sum_char]
    by_cases h2 : m = -m'
    · rw [if_pos (by rw [h2, neg_add_cancel]), if_pos h2, h2, lam_neg]; field_simp
    · rw [if_neg h2, if_neg (fun h1 ↦ h2 (eq_neg_of_add_eq_zero_left h1)), mul_zero]
  rw [Fintype.sum_congr _ _ key]
  simp

/-- Fourier coefficients of the heat kernel. -/
lemma sum_latHeat_mul_char (t : ℝ) (m' : Torus d n) :
    ∑ y, latHeat t y * (char m' y).re = Real.exp (-t * lam m') := by
  have h := congrArg Complex.re (b1c_sum_latHeat_char_c t m')
  rw [Complex.re_sum, Complex.ofReal_re] at h
  simpa only [Complex.re_ofReal_mul] using h

lemma sum_latHeat (t : ℝ) : ∑ y : Torus d n, latHeat t y = 1 := by
  have h := sum_latHeat_mul_char (d := d) (n := n) t 0
  simpa [char_zero_left, lam_zero] using h

/-! ### Positivity -/

/-- `μ(k) = ∑_i 2cos k_i`, so that `λ = 2d - μ`. -/
def b1c_mu (m : Torus d n) : ℝ := ∑ i, 2 * cosk m i

omit [NeZero n] in
lemma b1c_lam_eq_mu (m : Torus d n) : lam m = 2 * d - b1c_mu m := by
  simp [lam, b1c_mu, Finset.sum_sub_distrib]; ring

/-- `C_j(y) = |Λ|⁻¹ ∑_k μ(k)^j e^{ik·y}`: the number of `j`-step nearest-neighbour paths
from `0` to `y` (divided by nothing); it is real and nonnegative. -/
def b1c_C (j : ℕ) (y : Torus d n) : ℂ := ((n : ℂ) ^ d)⁻¹ * ∑ m, (b1c_mu m : ℂ) ^ j * char m y

lemma b1c_C_zero (y : Torus d n) : b1c_C 0 y = if y = 0 then 1 else 0 := by
  have hc : ((n : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))
  simp only [b1c_C, pow_zero, one_mul, sum_char_left]
  split_ifs <;> simp [hc]

lemma b1c_C_succ (j : ℕ) (y : Torus d n) :
    b1c_C (j + 1) y = ∑ e : Dir d, b1c_C j (y + dirVec e) := by
  have hmu : ∀ m : Torus d n, (b1c_mu m : ℂ) = ∑ e : Dir d, char m (dirVec e) := fun m ↦ by
    rw [sum_char_dirVec, b1c_mu]; push_cast; rfl
  simp only [b1c_C, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [pow_succ, hmu, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [char_add_right]; ring

lemma b1c_C_nonneg (j : ℕ) (y : Torus d n) : (b1c_C j y).im = 0 ∧ 0 ≤ (b1c_C j y).re := by
  induction j generalizing y with
  | zero => rw [b1c_C_zero]; split_ifs <;> simp
  | succ j ih =>
    rw [b1c_C_succ, Complex.im_sum, Complex.re_sum]
    exact ⟨Finset.sum_eq_zero fun e _ ↦ (ih _).1, Finset.sum_nonneg fun e _ ↦ (ih _).2⟩

/-- Positivity of the lattice heat kernel. -/
theorem latHeat_nonneg {t : ℝ} (ht : 0 ≤ t) (y : Torus d n) : 0 ≤ latHeat t y := by
  -- power series of `e^{tμ}`
  have hser : ∀ m : Torus d n, HasSum (fun j : ℕ ↦ (((t * b1c_mu m) ^ j / j.factorial : ℝ) : ℂ)
      * char m y) ((Real.exp (t * b1c_mu m) : ℂ) * char m y) := fun m ↦ by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (t * b1c_mu m)
    rw [← Real.exp_eq_exp_ℝ] at h
    exact (Complex.hasSum_ofReal.mpr h).mul_right _
  have hsum := (hasSum_sum (s := Finset.univ) fun m _ ↦ hser m).mul_left ((n : ℂ) ^ d)⁻¹
  have hterm : ∀ j : ℕ, ((n : ℂ) ^ d)⁻¹ * ∑ m : Torus d n,
      (((t * b1c_mu m) ^ j / j.factorial : ℝ) : ℂ) * char m y =
      ((t ^ j / j.factorial : ℝ) : ℂ) * b1c_C j y := fun j ↦ by
    simp only [b1c_C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    push_cast; ring
  simp only [hterm] at hsum
  have hre := Complex.hasSum_re hsum
  have hnn : 0 ≤ (((n : ℂ) ^ d)⁻¹ * ∑ m : Torus d n,
      (Real.exp (t * b1c_mu m) : ℂ) * char m y).re := by
    refine hre.nonneg fun j ↦ ?_
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) (b1c_C_nonneg j y).2
  have heq : (latHeat t y : ℂ) = (Real.exp (-(2 * d) * t) : ℂ) * (((n : ℂ) ^ d)⁻¹ *
      ∑ m : Torus d n, (Real.exp (t * b1c_mu m) : ℂ) * char m y) := by
    rw [latHeat, fmat_complex (b1c_heatSym_even t), sub_zero, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [b1c_lam_eq_mu]
    have : Real.exp (-t * (2 * d - b1c_mu m)) = Real.exp (-(2 * d) * t) * Real.exp (t * b1c_mu m) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; push_cast; ring
  have := congrArg Complex.re heq
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at this
  rw [this]; exact mul_nonneg (Real.exp_pos _).le hnn

/-! ### The weight `λ(y)` and the second moment -/

lemma b1c_norm_one_sub_sq {z : ℂ} (hz : ‖z‖ = 1) : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  have h1 : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z; rw [hz, Complex.normSq_apply] at this; linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith

lemma b1c_norm_stdAddChar (a : ZMod n) : ‖(ZMod.stdAddChar a : ℂ)‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

lemma b1c_cosk_eq_re (m : Torus d n) (i : Fin d) : cosk m i = (char (unitT i) m).re := by
  rw [char_comm, char_unitT, re_stdAddChar, cosk]

lemma b1c_lam_eq_norm (m : Torus d n) :
    lam m = ∑ i, ‖1 - (ZMod.stdAddChar (co m i) : ℂ)‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [b1c_norm_one_sub_sq (b1c_norm_stdAddChar _), re_stdAddChar, cosk]

/-- Quasi-triangle inequality for the weight: `λ(x) ≤ 2(λ(x - y) + λ(y))`. -/
lemma b1c_lam_le (x y : Torus d n) : lam x ≤ 2 * (lam (x - y) + lam y) := by
  rw [b1c_lam_eq_norm, b1c_lam_eq_norm, b1c_lam_eq_norm, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  gcongr with i
  set z : ℂ := ZMod.stdAddChar (co (x - y) i)
  set u : ℂ := ZMod.stdAddChar (co y i)
  have hx : (ZMod.stdAddChar (co x i) : ℂ) = z * u := by
    simp only [z, u, ← AddChar.map_add_eq_mul, co_sub, Pi.sub_apply, sub_add_cancel]
  have hz : ‖z‖ = 1 := b1c_norm_stdAddChar _
  have htri : ‖1 - z * u‖ ≤ ‖1 - z‖ + ‖1 - u‖ := by
    have : 1 - z * u = (1 - z) + z * (1 - u) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hz, one_mul]
  rw [hx]
  have h0 : 0 ≤ ‖1 - z * u‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖1 - z‖ - ‖1 - u‖)]

lemma b1c_sum_lam_mul_latHeat (s : ℝ) :
    ∑ y : Torus d n, lam y * latHeat s y =
      ∑ i : Fin d, (2 - 2 * Real.exp (-s * lam (unitT i : Torus d n))) := by
  have hl : ∀ y : Torus d n, lam y = ∑ i, (2 - 2 * (char (unitT i) y).re) := fun y ↦
    Finset.sum_congr rfl fun i _ ↦ by rw [b1c_cosk_eq_re]
  calc ∑ y, lam y * latHeat s y = ∑ y, ∑ i, (2 - 2 * (char (unitT i) y).re) * latHeat s y :=
        Finset.sum_congr rfl fun y _ ↦ by rw [hl y, Finset.sum_mul]
    _ = ∑ i, ∑ y, (2 - 2 * (char (unitT i) y).re) * latHeat s y := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hi := sum_latHeat_mul_char (d := d) (n := n) s (unitT i)
        have h0 := sum_latHeat (d := d) (n := n) s
        calc ∑ y, (2 - 2 * (char (unitT i) y).re) * latHeat s y =
            2 * ∑ y, latHeat s y - 2 * ∑ y, latHeat s y * (char (unitT i) y).re := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun y _ ↦ by ring
          _ = _ := by rw [h0, hi]; ring

lemma b1c_two_sub_two_cos_le (θ : ℝ) : 2 - 2 * Real.cos θ ≤ θ ^ 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := θ); linarith

lemma b1c_lam_unitT_le (i : Fin d) : lam (unitT i : Torus d n) ≤ d * (2 * π / n) ^ 2 := by
  calc lam (unitT i : Torus d n) ≤ ∑ _j : Fin d, (2 * π / n) ^ 2 := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine (b1c_two_sub_two_cos_le _).trans ?_
        have hv : ((co (unitT i : Torus d n) j).val : ℝ) ≤ 1 := by
          have : (co (unitT i : Torus d n) j).val ≤ 1 := by
            simp only [co, unitT]
            by_cases h : j = i
            · subst h; simp only [Pi.single_eq_same]
              by_cases h1 : n = 1
              · have := ZMod.val_lt (1 : ZMod n); omega
              · rw [ZMod.val_one'' h1]
            · simp [Pi.single_eq_of_ne h]
          exact_mod_cast this
        have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
        have h0 : (0 : ℝ) ≤ (co (unitT i : Torus d n) j).val := Nat.cast_nonneg _
        have e : 2 * π * ((co (unitT i : Torus d n) j).val : ℝ) / n ≤ 2 * π / n := by
          have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 2 * π)
          rw [mul_one] at this; exact div_le_div_of_nonneg_right this hn.le
        exact pow_le_pow_left₀ (by positivity) e 2
    _ = d * (2 * π / n) ^ 2 := by simp

/-- Second-moment bound: `∑_y λ(y) p_s(y) ≤ 8d²π² s/n²`. -/
theorem sum_lam_mul_latHeat_le {s : ℝ} (hs : 0 ≤ s) :
    ∑ y : Torus d n, lam y * latHeat s y ≤ 8 * d ^ 2 * π ^ 2 * s / n ^ 2 := by
  rw [b1c_sum_lam_mul_latHeat]
  calc ∑ i : Fin d, (2 - 2 * Real.exp (-s * lam (unitT i : Torus d n))) ≤
      ∑ _i : Fin d, 2 * s * (d * (2 * π / n) ^ 2) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have := Real.add_one_le_exp (-s * lam (unitT i : Torus d n))
        have h2 := mul_le_mul_of_nonneg_left (b1c_lam_unitT_le (n := n) i) hs
        nlinarith
    _ = 8 * d ^ 2 * π ^ 2 * s / n ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
        field_simp; ring

/-- Weighted bound: `λ(x) p_{2s}(x) ≤ 4 p_s(0) ∑_y λ(y) p_s(y)`. -/
theorem lam_mul_latHeat_add_le {s : ℝ} (hs : 0 ≤ s) (x : Torus d n) :
    lam x * latHeat (s + s) x ≤ 4 * latHeat s (0 : Torus d n) * ∑ y : Torus d n, lam y * latHeat s y := by
  rw [latHeat_add, Finset.mul_sum]
  have hP := latHeat_nonneg (d := d) (n := n) hs
  have h1 : ∀ y, lam x * (latHeat s (x - y) * latHeat s y) ≤
      2 * (lam (x - y) * latHeat s (x - y)) * latHeat s 0 +
        2 * (lam y * latHeat s y) * latHeat s 0 := fun y ↦ by
    have hl := b1c_lam_le x y
    have hA := hP (x - y); have hB := hP y
    have hlA := lam_nonneg (x - y); have hlB := lam_nonneg y
    have hA0 := latHeat_le_zero s (x - y); have hB0 := latHeat_le_zero s y
    calc lam x * (latHeat s (x - y) * latHeat s y) ≤
        2 * (lam (x - y) + lam y) * (latHeat s (x - y) * latHeat s y) := by
          gcongr
      _ = 2 * (lam (x - y) * latHeat s (x - y)) * latHeat s y +
          2 * (lam y * latHeat s y) * latHeat s (x - y) := by ring
      _ ≤ _ := by gcongr
  refine (Finset.sum_le_sum fun y _ ↦ h1 y).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have : ∑ y : Torus d n, lam (x - y) * latHeat s (x - y) = ∑ y, lam y * latHeat s y :=
    Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ rfl
  rw [this]; ring

/-! ### On-diagonal bound -/

/-- `16 u² ≤ 2 - 2cos(2πu)` for `|u| ≤ 1/2`. -/
lemma b1c_two_sub_two_cos_ge {u : ℝ} (hu : |u| ≤ 1 / 2) :
    16 * u ^ 2 ≤ 2 - 2 * Real.cos (2 * π * u) := by
  have hc : Real.cos (2 * π * u) = 1 - 2 * Real.sin (π * u) ^ 2 := by
    rw [show 2 * π * u = 2 * (π * u) by ring, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (π * u); linarith
  rw [hc]
  have h1 : 2 / π * (π * |u|) ≤ Real.sin (π * |u|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [pi_pos])
  have h2 : 2 / π * (π * |u|) = 2 * |u| := by field_simp
  have h3 : Real.sin (π * u) ^ 2 = Real.sin (π * |u|) ^ 2 := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, neg_sq]
  have h4 : 0 ≤ 2 * |u| := by positivity
  have h5 : (2 * |u|) ^ 2 ≤ Real.sin (π * |u|) ^ 2 := by
    rw [h2] at h1; exact pow_le_pow_left₀ h4 h1 2
  have h6 : (2 * |u|) ^ 2 = 4 * u ^ 2 := by rw [mul_pow, sq_abs]; ring
  nlinarith

/-- `cos(2π (j mod n)/n) = cos(2πj/n)`. -/
lemma b1c_cos_val_intCast (j : ℤ) :
    Real.cos (2 * π * ((j : ZMod n).val : ℝ) / n) = Real.cos (2 * π * j / n) := by
  have hv : (((j : ZMod n).val : ℤ) : ℝ) = ((j % (n : ℤ) : ℤ) : ℝ) := by
    rw [ZMod.val_intCast]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hdiv : (j : ℝ) = (j % (n : ℤ) : ℤ) + ((j / (n : ℤ) : ℤ) : ℝ) * n := by
    have := Int.emod_add_mul_ediv j n
    have h2 : ((j % (n : ℤ) + (n : ℤ) * (j / (n : ℤ)) : ℤ) : ℝ) = (j : ℝ) := by exact_mod_cast this
    push_cast at h2; linarith
  have hval : (((j : ZMod n).val : ℕ) : ℝ) = (((j : ZMod n).val : ℤ) : ℝ) := by push_cast; rfl
  rw [hval, hv, hdiv]
  rw [show 2 * π * (((j % (n : ℤ) : ℤ) : ℝ) + ((j / (n : ℤ) : ℤ) : ℝ) * n) / n =
      2 * π * ((j % (n : ℤ) : ℤ) : ℝ) / n + ((j / (n : ℤ) : ℤ) : ℝ) * (2 * π) by field_simp]
  rw [Real.cos_add_int_mul_two_pi]

/-- `cos(2π val(a)/n) = cos(2π valMinAbs(a)/n)`. -/
lemma b1c_cosk_valMinAbs (a : ZMod n) :
    Real.cos (2 * π * (a.val : ℝ) / n) = Real.cos (2 * π * (a.valMinAbs : ℝ) / n) := by
  conv_lhs => rw [← ZMod.coe_valMinAbs a]
  exact b1c_cos_val_intCast _

lemma b1c_abs_valMinAbs_div_le (a : ZMod n) : |(a.valMinAbs : ℝ) / n| ≤ 1 / 2 := by
  have h := ZMod.valMinAbs_mem_Ioc a
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [abs_div, abs_of_pos hn, div_le_iff₀ hn, abs_le]
  have h1 : (-(n : ℤ) : ℝ) < (a.valMinAbs * 2 : ℤ) := by exact_mod_cast h.1
  have h2 : ((a.valMinAbs * 2 : ℤ) : ℝ) ≤ (n : ℤ) := by exact_mod_cast h.2
  push_cast at h1 h2
  constructor <;> linarith

/-- Lower bound of the symbol by the centred representative. -/
lemma b1c_lam_ge (m : Torus d n) :
    ∑ i, 16 * ((co m i).valMinAbs : ℝ) ^ 2 / n ^ 2 ≤ lam m := by
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h := b1c_two_sub_two_cos_ge (b1c_abs_valMinAbs_div_le (co m i))
  rw [cosk, b1c_cosk_valMinAbs]
  have e1 : 16 * ((co m i).valMinAbs : ℝ) ^ 2 / n ^ 2 =
      16 * (((co m i).valMinAbs : ℝ) / n) ^ 2 := by rw [div_pow]; ring
  have e2 : 2 * π * ((co m i).valMinAbs : ℝ) / n = 2 * π * (((co m i).valMinAbs : ℝ) / n) := by
    ring
  rw [e1, e2]; exact h

/-- The one-dimensional theta sum `∑_k e^{-πk²u} = evenKernel 0 u`. -/
lemma b1c_hasSum_theta {u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℤ ↦ Real.exp (-π * (k : ℝ) ^ 2 * u)) (evenKernel 0 u) := by
  simpa using HurwitzZeta.hasSum_int_evenKernel 0 hu

/-- `evenKernel 0 u ≤ C (1 + 1/√u)` with `C = evenKernel 0 1`. -/
lemma b1c_evenK0_le {u : ℝ} (hu : 0 < u) :
    evenKernel 0 u ≤ evenKernel 0 1 * (1 + 1 / Real.sqrt u) := by
  have hC : 0 ≤ evenKernel 0 1 := (b1c_hasSum_theta one_pos).nonneg fun _ ↦ (Real.exp_pos _).le
  have hsq : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  rcases le_or_gt 1 u with h1 | h1
  · have : evenKernel 0 u ≤ evenKernel 0 1 :=
      hasSum_le (fun k ↦ Real.exp_le_exp.2 (by
          nlinarith [mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg (k : ℝ))) (sub_nonneg.2 h1)]))
        (b1c_hasSum_theta hu) (b1c_hasSum_theta one_pos)
    have : 0 ≤ evenKernel 0 1 * (1 / Real.sqrt u) := by positivity
    nlinarith
  · -- Poisson: `evenKernel 0 u = cosKernel 0 (1/u) / √u`
    have hp := b1_cosK_eq_evenK 0 (s := 1 / u) (by positivity)
    rw [one_div_one_div] at hp
    have h1u : 1 ≤ 1 / u := by rw [le_div_iff₀ hu]; linarith
    have hdec := b1_cosK0_decay h1u
    have hE := b1_cosK0_sub_one_nonneg (s := 1) one_pos
    have hw : Real.exp (-π * (1 / u - 1)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
    have hk : cosKernel 0 (1 / u) ≤ cosKernel 0 1 := by
      have : (cosKernel 0 1 - 1) * Real.exp (-π * (1 / u - 1)) ≤ cosKernel 0 1 - 1 :=
        mul_le_of_le_one_right hE hw
      linarith
    have h11 := b1_cosK_eq_evenK 0 (s := 1) one_pos
    simp only [div_one, Real.sqrt_one, QuotientAddGroup.mk_zero] at h11 hp
    have hsqi : Real.sqrt (1 / u) = 1 / Real.sqrt u := by
      rw [Real.sqrt_div' _ hu.le, Real.sqrt_one]
    rw [hsqi] at hp
    have hev : evenKernel 0 u = cosKernel 0 (1 / u) * (1 / Real.sqrt u) := by
      rw [hp]; field_simp
    rw [hev, ← h11]
    have : 0 ≤ cosKernel 0 1 := by rw [h11]; exact hC
    have : 0 ≤ 1 / Real.sqrt u := by positivity
    nlinarith

/-- On-diagonal bound `p_s(0) ≤ (C (1/n + 1/√s))^d`, `C = evenKernel 0 1`. -/
theorem latHeat_zero_le {s : ℝ} (hs : 0 < s) :
    latHeat s (0 : Torus d n) ≤ (evenKernel 0 1 * (1 / n + 1 / Real.sqrt s)) ^ d := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  set c : ℝ := 16 * s / n ^ 2
  set g : ZMod n → ℝ := fun a ↦ Real.exp (-c * (a.valMinAbs : ℝ) ^ 2)
  have hexp : ∀ m : Torus d n, Real.exp (-s * lam m) ≤ ∏ i, g (co m i) := fun m ↦ by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left (b1c_lam_ge m) hs.le
    rw [Finset.mul_sum] at this
    have : ∑ i, -c * ((co m i).valMinAbs : ℝ) ^ 2 = -∑ i, s * (16 * ((co m i).valMinAbs : ℝ) ^ 2 / n ^ 2) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [c]; ring
    linarith
  set u : ℝ := c / π
  have hu : 0 < u := by positivity
  have hg : ∑ a : ZMod n, g a ≤ evenKernel 0 u := by
    have hsum := b1c_hasSum_theta hu
    have hinj : Function.Injective (fun a : ZMod n ↦ a.valMinAbs) := ZMod.injective_valMinAbs
    calc ∑ a : ZMod n, g a = ∑ k ∈ Finset.univ.image (fun a : ZMod n ↦ a.valMinAbs),
          Real.exp (-π * (k : ℝ) ^ 2 * u) := by
            rw [Finset.sum_image fun a _ b _ h ↦ hinj h]
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            simp only [g, u]; congr 1; field_simp
      _ ≤ evenKernel 0 u := by
            rw [← hsum.tsum_eq]
            exact hsum.summable.sum_le_tsum _ fun k _ ↦ (Real.exp_pos _).le
  have hev := b1c_evenK0_le hu
  have hsqu : 1 / Real.sqrt u ≤ n / Real.sqrt s := by
    have : u = s * (16 / (π * n ^ 2)) := by simp only [u, c]; field_simp
    rw [this, Real.sqrt_mul hs.le, Real.sqrt_div' _ (by positivity),
      show Real.sqrt 16 = 4 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      Real.sqrt_mul pi_pos.le, Real.sqrt_sq hn.le]
    have hs' : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have hpi : Real.sqrt π ≤ 4 := by
      rw [show (4 : ℝ) = Real.sqrt 16 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith [pi_lt_four])
    have hpi0 : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
    rw [div_le_div_iff₀ (by positivity) hs']
    field_simp
    nlinarith
  have hC : 0 ≤ evenKernel 0 1 := (b1c_hasSum_theta one_pos).nonneg fun _ ↦ (Real.exp_pos _).le
  rw [latHeat_zero_eq]
  calc ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, Real.exp (-s * lam m) ≤
      ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, ∏ i, g (co m i) := by
        gcongr with m; exact hexp m
    _ = ((n : ℝ) ^ d)⁻¹ * (∑ a : ZMod n, g a) ^ d := by
        congr 1
        rw [← Fin.prod_const, Fintype.prod_sum]
        rfl
    _ ≤ ((n : ℝ) ^ d)⁻¹ * (evenKernel 0 1 * (1 + n / Real.sqrt s)) ^ d := by
        have hg0 : 0 ≤ ∑ a : ZMod n, g a := Finset.sum_nonneg fun a _ ↦ (Real.exp_pos _).le
        gcongr
        exact hg.trans (hev.trans (by gcongr))
    _ = (evenKernel 0 1 * (1 / n + 1 / Real.sqrt s)) ^ d := by
        rw [← inv_pow, ← mul_pow]
        congr 1
        field_simp

/-- The constant `C₁ = evenKernel 0 1` of the on-diagonal bound. -/
def b1c_C1 : ℝ := evenKernel 0 1

/-- Two-dimensional weighted bound: `λ(x) p_{2s}(x) ≤ 256π²C₁² (s/n⁴ + 1/n²)`. -/
theorem lam_mul_latHeat_le {s : ℝ} (hs : 0 < s) (x : Torus 2 n) :
    lam x * latHeat (s + s) x ≤ 256 * π ^ 2 * b1c_C1 ^ 2 * (s / n ^ 4 + 1 / n ^ 2) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have h1 := lam_mul_latHeat_add_le hs.le x
  have h2 := sum_lam_mul_latHeat_le (d := 2) (n := n) hs.le
  have h3 := latHeat_zero_le (d := 2) (n := n) hs
  have hP0 : 0 ≤ latHeat s (0 : Torus 2 n) := latHeat_nonneg hs.le 0
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h4 : (evenKernel 0 1 * (1 / n + 1 / Real.sqrt s)) ^ 2 ≤
      2 * b1c_C1 ^ 2 * (1 / n ^ 2 + 1 / s) := by
    have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    rw [mul_pow, b1c_C1]
    have : (1 / (n : ℝ) + 1 / Real.sqrt s) ^ 2 ≤ 2 * (1 / n ^ 2 + 1 / s) := by
      have e1 : (1 / (n : ℝ)) ^ 2 = 1 / n ^ 2 := by ring
      have e2 : (1 / Real.sqrt s) ^ 2 = 1 / s := by rw [div_pow, hss, one_pow]
      have := sq_nonneg (1 / (n : ℝ) - 1 / Real.sqrt s)
      nlinarith
    calc evenKernel 0 1 ^ 2 * (1 / (n : ℝ) + 1 / Real.sqrt s) ^ 2 ≤
        evenKernel 0 1 ^ 2 * (2 * (1 / n ^ 2 + 1 / s)) := by gcongr
      _ = _ := by ring
  have hS0 : 0 ≤ ∑ y : Torus 2 n, lam y * latHeat s y :=
    Finset.sum_nonneg fun y _ ↦ mul_nonneg (lam_nonneg y) (latHeat_nonneg hs.le y)
  calc lam x * latHeat (s + s) x ≤ 4 * latHeat s 0 * ∑ y : Torus 2 n, lam y * latHeat s y := h1
    _ ≤ 4 * (2 * b1c_C1 ^ 2 * (1 / n ^ 2 + 1 / s)) * (8 * (2 : ℕ) ^ 2 * π ^ 2 * s / n ^ 2) := by
        gcongr; exact h3.trans h4
    _ = 256 * π ^ 2 * b1c_C1 ^ 2 * (s / n ^ 4 + 1 / n ^ 2) := by
        field_simp; ring

end

end Cont
