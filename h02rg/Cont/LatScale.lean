import Cont.LatScaleSeries
import Loc.Polymer

/-!
# Scaling limit of the lattice Green function on `𝕋²` (B1, item 2)

For `x ∈ 𝕋² = UnitAddTorus (Fin 2)`, `latPt n x ∈ Torus 2 n` is the nearest point of the lattice
of spacing `1/n` (rounding of `n · torusRep x`), and `latPtN L N = latPt (L^N)` on `Λ_N = Lam 2 L N`.

Main results:
* `latGreen_latPt_uniform` : for `δ, η > 0` there is `n₀` with
  `|G_lat^{(n)}(latPt n x) - G_𝕋(x)| ≤ η` for all `n ≥ n₀` and all `x` with `|x|_𝕋 ≥ δ`;
* `latGreen_latPtN_tendstoUniformlyOn` : `G_{Λ_N}(latPtN L N x) → G_𝕋(x)` uniformly on compact
  subsets of `𝕋² ∖ {0}` as `N → ∞` (`L ≥ 2`).

No rescaling is needed: in `d = 2` the lattice Green function `(-Δ_lat)⁻¹` (unit spacing,
zero mode removed) is dimensionless, and with `a(k) = n²λ(k)/(4π)` one has
`4π G_lat(x) = ∑_{k≠0} cos(k·x)/a(k)` while `4π G_𝕋(x) = ∑_{k≠0} cos(2πk·x)/(π|k|²)` (formally).

Proof. `4π G_lat = ∫_0^ε (P_n(s) - 1) ds + T_n(ε)` with `P_n(s) = n² p_{n²s/4π}` and
`T_n(ε) = ∑_{k ≠ 0} e^{-εa(k)} cos(k·x)/a(k)` (`b1c_lat_decomp`), and likewise
`4π G_𝕋 = ∫_0^ε (Θ_s - 1) ds + ∑_{k ≠ 0} e^{-επ|k|²} cos(2πk·x)/(π|k|²)`. The short-time parts are
`O(ε)` uniformly (`lam_mul_latHeat_le`, `b1c_abs_small_cont_le`), and the long-time series
converge uniformly in `x` by Tannery's theorem, with the majorant `3 e^{-4ε|k|²/π}` from
`a(k) ≥ 4|k|²/π` on the centred box.
-/

namespace Cont

noncomputable section

open Real Set Filter Topology MeasureTheory FRD Grassmann HurwitzZeta

/-! ### Lattice points -/

/-- Integer coordinates `round(n · torusRep x)`. -/
def b1c_j (n : ℕ) (x : UnitAddTorus (Fin 2)) (i : Fin 2) : ℤ := round ((n : ℝ) * torusRep x i)

/-- Nearest point of the lattice of spacing `1/n` (`Torus 2 n`) to `x ∈ 𝕋²`. -/
def latPt (n : ℕ) (x : UnitAddTorus (Fin 2)) : Torus 2 n := fun i ↦ ((b1c_j n x i : ℤ) : ZMod n)

/-- Nearest point of `Λ_N = Lam 2 L N` (spacing `L^{-N}`). -/
def latPtN (L N : ℕ) (x : UnitAddTorus (Fin 2)) : Loc.Lam 2 L N := latPt (L ^ N) x

lemma b1c_abs_j_sub {n : ℕ} (hn : 0 < n) (x : UnitAddTorus (Fin 2)) (i : Fin 2) :
    |(b1c_j n x i : ℝ) / n - torusRep x i| ≤ 1 / (2 * n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h := abs_sub_round ((n : ℝ) * torusRep x i)
  have e : (b1c_j n x i : ℝ) / n - torusRep x i =
      -(((n : ℝ) * torusRep x i - round ((n : ℝ) * torusRep x i)) / n) := by
    unfold b1c_j; field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hn', div_le_div_iff₀ hn' (by positivity)]
  nlinarith

/-! ### Symbols on `ℤ²` -/

/-- `α_n(k) = (n²/4π) ∑_i (2 - 2cos(2πk_i/n))`. -/
def b1c_alpha (n : ℕ) (k : ℤ × ℤ) : ℝ :=
  (n : ℝ) ^ 2 / (4 * π) *
    ((2 - 2 * Real.cos (2 * π * k.1 / n)) + (2 - 2 * Real.cos (2 * π * k.2 / n)))

/-- The centred box `-n < 2k_i ≤ n` (the range of `valMinAbs`). -/
def b1c_inBox (n : ℕ) (k : ℤ × ℤ) : Prop :=
  (-(n : ℤ) < k.1 * 2 ∧ k.1 * 2 ≤ n) ∧ (-(n : ℤ) < k.2 * 2 ∧ k.2 * 2 ≤ n)

instance (n : ℕ) (k : ℤ × ℤ) : Decidable (b1c_inBox n k) := by unfold b1c_inBox; infer_instance

lemma b1c_abs_div_le_of_box {n : ℕ} (hn : 0 < n) {a : ℤ} (h1 : -(n : ℤ) < a * 2)
    (h2 : a * 2 ≤ n) : |(a : ℝ) / n| ≤ 1 / 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1' : (-(n : ℤ) : ℝ) < ((a * 2 : ℤ) : ℝ) := by exact_mod_cast h1
  have h2' : ((a * 2 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2'
  rw [abs_div, abs_of_pos hn', div_le_iff₀ hn', abs_le]
  constructor <;> linarith

lemma b1c_alpha_ge {n : ℕ} (hn : 0 < n) {k : ℤ × ℤ} (hb : b1c_inBox n k) :
    4 / π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ≤ b1c_alpha n k := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 := b1c_two_sub_two_cos_ge (b1c_abs_div_le_of_box hn hb.1.1 hb.1.2)
  have h2 := b1c_two_sub_two_cos_ge (b1c_abs_div_le_of_box hn hb.2.1 hb.2.2)
  rw [show 2 * π * ((k.1 : ℝ) / n) = 2 * π * k.1 / n by ring] at h1
  rw [show 2 * π * ((k.2 : ℝ) / n) = 2 * π * k.2 / n by ring] at h2
  unfold b1c_alpha
  have e : 4 / π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) =
      (n : ℝ) ^ 2 / (4 * π) * (16 * ((k.1 : ℝ) / n) ^ 2 + 16 * ((k.2 : ℝ) / n) ^ 2) := by
    field_simp; ring
  rw [e]; gcongr

/-- `(n²/4π)(2 - 2cos(2πj/n)) = πj² sinc(πj/n)²`. -/
lemma b1c_one_eq_sinc {n : ℕ} (hn : 0 < n) (j : ℤ) :
    (n : ℝ) ^ 2 / (4 * π) * (2 - 2 * Real.cos (2 * π * j / n)) =
      π * (j : ℝ) ^ 2 * Real.sinc (π * j / n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hc : Real.cos (2 * π * j / n) = 1 - 2 * Real.sin (π * j / n) ^ 2 := by
    rw [show 2 * π * (j : ℝ) / n = 2 * (π * j / n) by ring, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (π * j / n); linarith
  rw [hc]
  by_cases hj : j = 0
  · simp [hj]
  · have hy : π * (j : ℝ) / n ≠ 0 := by
      have : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
      positivity
    rw [Real.sinc_of_ne_zero hy]
    have : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
    field_simp
    ring

lemma b1c_one_tendsto (j : ℤ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 / (4 * π) * (2 - 2 * Real.cos (2 * π * j / n))) atTop
      (𝓝 (π * (j : ℝ) ^ 2)) := by
  have h0 : Tendsto (fun n : ℕ ↦ π * (j : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h1 : Tendsto (fun n : ℕ ↦ Real.sinc (π * j / n)) atTop (𝓝 1) := by
    have := (Real.continuous_sinc.tendsto 0).comp h0
    rwa [Real.sinc_zero] at this
  have h2 : Tendsto (fun n : ℕ ↦ π * (j : ℝ) ^ 2 * Real.sinc (π * j / n) ^ 2) atTop
      (𝓝 (π * (j : ℝ) ^ 2)) := by
    have := (h1.pow 2).const_mul (π * (j : ℝ) ^ 2)
    simpa using this
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (b1c_one_eq_sinc hn j).symm

lemma b1c_alpha_tendsto (k : ℤ × ℤ) :
    Tendsto (fun n : ℕ ↦ b1c_alpha n k) atTop (𝓝 (b1c_bk k)) := by
  have := (b1c_one_tendsto k.1).add (b1c_one_tendsto k.2)
  have e : π * (k.1 : ℝ) ^ 2 + π * (k.2 : ℝ) ^ 2 = b1c_bk k := by unfold b1c_bk; ring
  rw [e] at this
  refine this.congr fun n ↦ ?_
  unfold b1c_alpha; ring

/-! ### The lattice decomposition -/

section lattice

variable {n : ℕ} [NeZero n]

/-- `a(k) = n²λ(k)/(4π)`. -/
def b1c_a (m : Torus 2 n) : ℝ := (n : ℝ) ^ 2 * lam m / (4 * π)

/-- `P_n(s, x) = n² p_{n²s/(4π)}(x) = ∑_k e^{-s a(k)} cos(k·x)`. -/
def b1c_P (s : ℝ) (x : Torus 2 n) : ℝ := ∑ m, Real.exp (-s * b1c_a m) * (char m x).re

/-- The long-time part `T_n(ε, x) = ∑_{k ≠ 0} e^{-εa(k)} cos(k·x)/a(k)`. -/
def b1c_Tn (ε : ℝ) (x : Torus 2 n) : ℝ :=
  ∑ m, if m = 0 then 0 else Real.exp (-ε * b1c_a m) * (char m x).re / b1c_a m

lemma b1c_P_eq (s : ℝ) (x : Torus 2 n) :
    b1c_P s x = (n : ℝ) ^ 2 * latHeat ((n : ℝ) ^ 2 * s / (4 * π)) x := by
  have hn : ((n : ℝ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))
  simp only [b1c_P, latHeat, fmat, sub_zero, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  congr 2; unfold b1c_a; ring

lemma b1c_a_zero : b1c_a (0 : Torus 2 n) = 0 := by simp [b1c_a, lam_zero]

lemma b1c_a_pos {m : Torus 2 n} (hm : m ≠ 0) : 0 < b1c_a m := by
  unfold b1c_a
  have := lam_pos hm
  have : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  positivity

lemma b1c_integral_exp {a : ℝ} (ha : a ≠ 0) (ε : ℝ) :
    ∫ s in (0 : ℝ)..ε, Real.exp (-s * a) = (1 - Real.exp (-ε * a)) / a := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) ε,
      HasDerivAt (fun s ↦ -Real.exp (-s * a) / a) (Real.exp (-s * a)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ ↦ -s * a) (-a) s := by
      simpa using (hasDerivAt_id s).neg.mul_const a
    have h2 := (h1.exp).neg.div_const a
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [neg_zero, zero_mul, Real.exp_zero]
  field_simp; ring

/-- `4π G_lat(x) = ∫_0^ε (P_n(s, x) - 1) ds + T_n(ε, x)`. -/
theorem b1c_lat_decomp (ε : ℝ) (x : Torus 2 n) :
    4 * π * latGreen x = (∫ s in (0 : ℝ)..ε, (b1c_P s x - 1)) + b1c_Tn ε x := by
  set g : Torus 2 n → ℝ → ℝ := fun m s ↦
    if m = 0 then 0 else Real.exp (-s * b1c_a m) * (char m x).re
  have hP : ∀ s, b1c_P s x - 1 = ∑ m, g m s := fun s ↦ by
    have : ∀ m, Real.exp (-s * b1c_a m) * (char m x).re = g m s + if m = 0 then 1 else 0 := by
      intro m
      by_cases hm : m = 0
      · subst hm; simp [g, b1c_a_zero, char_zero_left]
      · simp [g, hm]
    simp only [b1c_P, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp only [hP]
  rw [intervalIntegral.integral_finsetSum (fun m _ ↦ by
    by_cases hm : m = 0
    · simp only [g, hm, if_true]; exact intervalIntegrable_const
    · simp only [g, hm, if_false]
      apply Continuous.intervalIntegrable; fun_prop)]
  simp only [b1c_Tn, ← Finset.sum_add_distrib, latGreen, latGreenMat, fmat, sub_zero,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  by_cases hm : m = 0
  · simp [g, hm, latGreenSym]
  · have ha := b1c_a_pos hm
    simp only [g, hm, if_false, latGreenSym]
    rw [intervalIntegral.integral_mul_const, b1c_integral_exp ha.ne']
    have hl := lam_pos hm
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    unfold b1c_a at ha ⊢
    field_simp
    ring

/-- The constant `K₁ = 512π²C₁²` of the short-time lattice bound. -/
def b1c_K1 : ℝ := 512 * π ^ 2 * b1c_C1 ^ 2

lemma b1c_lam_mul_P_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (x : Torus 2 n) :
    lam x * b1c_P s x ≤ b1c_K1 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  set t : ℝ := (n : ℝ) ^ 2 * s / (8 * π)
  have ht : 0 < t := by positivity
  have h := lam_mul_latHeat_le ht x
  have e : t + t = (n : ℝ) ^ 2 * s / (4 * π) := by simp only [t]; field_simp; ring
  rw [e] at h
  rw [b1c_P_eq]
  have e2 : (n : ℝ) ^ 2 * (256 * π ^ 2 * b1c_C1 ^ 2 * (t / n ^ 4 + 1 / n ^ 2)) =
      256 * π ^ 2 * b1c_C1 ^ 2 * (s / (8 * π) + 1) := by
    simp only [t]; field_simp
  have hs8 : s / (8 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [pi_gt_three]
  calc lam x * ((n : ℝ) ^ 2 * latHeat ((n : ℝ) ^ 2 * s / (4 * π)) x) =
      (n : ℝ) ^ 2 * (lam x * latHeat ((n : ℝ) ^ 2 * s / (4 * π)) x) := by ring
    _ ≤ (n : ℝ) ^ 2 * (256 * π ^ 2 * b1c_C1 ^ 2 * (t / n ^ 4 + 1 / n ^ 2)) := by gcongr
    _ = 256 * π ^ 2 * b1c_C1 ^ 2 * (s / (8 * π) + 1) := e2
    _ ≤ 256 * π ^ 2 * b1c_C1 ^ 2 * (1 + 1) := by gcongr
    _ = b1c_K1 := by unfold b1c_K1; ring

lemma b1c_P_nonneg {s : ℝ} (hs : 0 ≤ s) (x : Torus 2 n) : 0 ≤ b1c_P s x := by
  rw [b1c_P_eq]
  have : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact mul_nonneg (by positivity) (latHeat_nonneg (by positivity) x)

/-- Short-time part of the lattice Green function at weight `λ(x) ≥ w₀`. -/
theorem b1c_abs_small_lat_le {x : Torus 2 n} {w₀ : ℝ} (hw : 0 < w₀) (hx : w₀ ≤ lam x)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ s in (0 : ℝ)..ε, (b1c_P s x - 1)| ≤ ε * (b1c_K1 / w₀ + 1) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := ε) (f := fun s ↦ b1c_P s x - 1) (C := b1c_K1 / w₀ + 1)
    (fun s hs ↦ by
      rw [uIoc_of_le hε.le] at hs
      have h1 := b1c_lam_mul_P_le hs.1 (hs.2.trans hε1) x
      have h0 := b1c_P_nonneg hs.1.le x
      have h2 : b1c_P s x ≤ b1c_K1 / w₀ := by
        rw [le_div_iff₀ hw]; nlinarith
      rw [Real.norm_eq_abs, abs_le]
      have : 0 ≤ b1c_K1 / w₀ := le_trans h0 h2
      constructor <;> linarith)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hε] at this
  linarith

/-- Weight of the lattice point: `λ(latPt x) ≥ 16|x|² - 4π/n`. -/
lemma b1c_lam_latPt_ge (x : UnitAddTorus (Fin 2)) :
    16 * (torusRep x 0 ^ 2 + torusRep x 1 ^ 2) - 4 * π / n ≤ lam (latPt n x) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hi : ∀ i : Fin 2, 16 * torusRep x i ^ 2 - 2 * π / n ≤ 2 - 2 * cosk (latPt n x) i := by
    intro i
    have hc : cosk (latPt n x) i = Real.cos (2 * π * (b1c_j n x i : ℝ) / n) := by
      rw [cosk]; exact b1c_cos_val_intCast _
    rw [hc]
    have h1 := b1c_two_sub_two_cos_ge ((abs_torusRep_le x i))
    have h2 := abs_cos_sub_cos_le (2 * π * (b1c_j n x i : ℝ) / n) (2 * π * torusRep x i)
    have h3 := b1c_abs_j_sub (Nat.pos_of_ne_zero (NeZero.ne n)) x i
    have e : 2 * π * (b1c_j n x i : ℝ) / n - 2 * π * torusRep x i =
        2 * π * ((b1c_j n x i : ℝ) / n - torusRep x i) := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h2
    have h4 : 2 * π * |(b1c_j n x i : ℝ) / n - torusRep x i| ≤ π / n := by
      calc 2 * π * |(b1c_j n x i : ℝ) / n - torusRep x i| ≤ 2 * π * (1 / (2 * n)) := by gcongr
        _ = π / n := by field_simp
    rw [abs_le] at h2
    have : 2 * π / n = 2 * (π / n) := by ring
    linarith [h2.1, h2.2]
  have := add_le_add (hi 0) (hi 1)
  rw [lam, Fin.sum_univ_two]
  linarith [this, show 4 * π / (n : ℝ) = 2 * π / n + 2 * π / n by ring]

/-! ### Transfer of the lattice sum to `ℤ²` -/

/-- The torus point with integer coordinates `j`. -/
def b1c_ofInt (j : Fin 2 → ℤ) : Torus 2 n := fun i ↦ (j i : ZMod n)

lemma b1c_re_char_cast (k j : Fin 2 → ℤ) :
    (char (b1c_ofInt k : Torus 2 n) (b1c_ofInt j)).re =
      Real.cos (2 * π * ((k 0 * j 0 + k 1 * j 1 : ℤ) : ℝ) / n) := by
  simp only [b1c_ofInt, char, co, Fin.prod_univ_two, ← Int.cast_mul, ZMod.stdAddChar_apply,
    ZMod.toCircle_intCast, ← Complex.exp_add]
  rw [show 2 * (π : ℂ) * Complex.I * ((k 0 * j 0 : ℤ) : ℂ) / n +
      2 * π * Complex.I * ((k 1 * j 1 : ℤ) : ℂ) / n =
      ((2 * π * ((k 0 * j 0 + k 1 * j 1 : ℤ) : ℝ) / n : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- Centred representative map `Torus 2 n → ℤ²`. -/
def b1c_emb (m : Torus 2 n) : ℤ × ℤ := ((co m 0).valMinAbs, (co m 1).valMinAbs)

omit [NeZero n] in
lemma b1c_emb_injective : Function.Injective (b1c_emb : Torus 2 n → ℤ × ℤ) := by
  intro m m' h
  simp only [b1c_emb, Prod.mk.injEq] at h
  funext i
  fin_cases i
  · exact ZMod.injective_valMinAbs h.1
  · exact ZMod.injective_valMinAbs h.2

lemma b1c_inBox_emb (m : Torus 2 n) : b1c_inBox n (b1c_emb m) := by
  have h0 := ZMod.valMinAbs_mem_Ioc (co m 0)
  have h1 := ZMod.valMinAbs_mem_Ioc (co m 1)
  exact ⟨h0, h1⟩

omit [NeZero n] in
lemma b1c_emb_eq_zero (m : Torus 2 n) : b1c_emb m = 0 ↔ m = 0 := by
  constructor
  · intro h
    simp only [b1c_emb, Prod.mk_eq_zero, ZMod.valMinAbs_eq_zero] at h
    funext i; fin_cases i
    · exact h.1
    · exact h.2
  · rintro rfl
    show ((0 : ZMod n).valMinAbs, (0 : ZMod n).valMinAbs) = 0
    simp

lemma b1c_alpha_emb (m : Torus 2 n) : b1c_alpha n (b1c_emb m) = b1c_a m := by
  simp only [b1c_alpha, b1c_a, b1c_emb, lam, Fin.sum_univ_two, cosk, b1c_cosk_valMinAbs]
  ring

lemma b1c_char_emb (m : Torus 2 n) (j : Fin 2 → ℤ) :
    (char m (b1c_ofInt j)).re =
      Real.cos (2 * π * (((b1c_emb m).1 * j 0 + (b1c_emb m).2 * j 1 : ℤ) : ℝ) / n) := by
  have hm : m = b1c_ofInt (fun i ↦ (co m i).valMinAbs) := by
    funext i; exact (ZMod.coe_valMinAbs _).symm
  conv_lhs => rw [hm]
  rw [b1c_re_char_cast]
  rfl

end lattice

/-- The `ℤ²` form of the lattice long-time terms. -/
def b1c_Fn (n : ℕ) (ε : ℝ) (j : Fin 2 → ℤ) (k : ℤ × ℤ) : ℝ :=
  if b1c_inBox n k ∧ k ≠ 0 then
    Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k *
      Real.cos (2 * π * ((k.1 * j 0 + k.2 * j 1 : ℤ) : ℝ) / n)
  else 0

theorem b1c_Tn_eq {n : ℕ} [NeZero n] (ε : ℝ) (j : Fin 2 → ℤ) :
    b1c_Tn ε (b1c_ofInt j : Torus 2 n) = ∑' k, b1c_Fn n ε j k := by
  have hsupp : Function.support (b1c_Fn n ε j) ⊆ Set.range (b1c_emb : Torus 2 n → ℤ × ℤ) := by
    intro k hk
    have hb : b1c_inBox n k := by
      by_contra h; apply hk; simp [b1c_Fn, h]
    refine ⟨fun i ↦ if i = 0 then (k.1 : ZMod n) else (k.2 : ZMod n), ?_⟩
    simp only [b1c_emb, co, Fin.isValue, ↓reduceIte, one_ne_zero]
    rw [(ZMod.valMinAbs_spec _ k.1).2 ⟨rfl, hb.1.1, hb.1.2⟩,
      (ZMod.valMinAbs_spec _ k.2).2 ⟨rfl, hb.2.1, hb.2.2⟩]
  rw [← b1c_emb_injective.tsum_eq hsupp, tsum_fintype]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [b1c_Fn, b1c_inBox_emb m, true_and, ne_eq, b1c_emb_eq_zero]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, if_false, not_false_eq_true, if_true]
    rw [b1c_alpha_emb, b1c_char_emb]
    ring

/-! ### Uniform comparison of the long-time series (Tannery) -/

/-- `x`-independent majorant of `|F_n(k) - F(k)|`. -/
def b1c_D (n : ℕ) (ε : ℝ) (k : ℤ × ℤ) : ℝ :=
  if b1c_inBox n k ∧ k ≠ 0 then
    |Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k - Real.exp (-(b1c_bk k) * ε) / b1c_bk k| +
      Real.exp (-(b1c_bk k) * ε) / b1c_bk k * (π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n)
  else if k = 0 then 0 else Real.exp (-(b1c_bk k) * ε) / b1c_bk k

/-- Summable majorant `3 e^{-4ε|k|²/π}`. -/
def b1c_B (ε : ℝ) (k : ℤ × ℤ) : ℝ :=
  3 * (Real.exp (-π * (k.1 : ℝ) ^ 2 * (4 * ε / π ^ 2)) *
    Real.exp (-π * (k.2 : ℝ) ^ 2 * (4 * ε / π ^ 2)))

lemma b1c_B_summable {ε : ℝ} (hε : 0 < ε) : Summable (b1c_B ε) :=
  (b1c_summable_gauss2 (by positivity)).mul_left 3

lemma b1c_gauss_eq (ε : ℝ) (k : ℤ × ℤ) :
    Real.exp (-π * (k.1 : ℝ) ^ 2 * (4 * ε / π ^ 2)) *
      Real.exp (-π * (k.2 : ℝ) ^ 2 * (4 * ε / π ^ 2)) =
      Real.exp (-ε * (4 / π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2))) := by
  rw [← Real.exp_add]; congr 1; field_simp; ring

lemma b1c_exp_b_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℤ × ℤ) :
    Real.exp (-(b1c_bk k) * ε) ≤ Real.exp (-ε * (4 / π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2))) := by
  apply Real.exp_le_exp.2
  have hq : 0 ≤ (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2 := by positivity
  have h4 : 4 / π ≤ π := by
    rw [div_le_iff₀ pi_pos]; nlinarith [pi_gt_three]
  have := mul_le_mul_of_nonneg_right h4 (mul_nonneg hq hε)
  unfold b1c_bk; nlinarith

lemma b1c_B_bounds {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (k : ℤ × ℤ) :
    (0 ≤ b1c_D n ε k ∧ b1c_D n ε k ≤ b1c_B ε k) ∧
      (∀ j, |b1c_Fn n ε j k| ≤ b1c_B ε k) ∧ (∀ y, |b1c_Fc ε y k| ≤ b1c_B ε k) := by
  set E := Real.exp (-ε * (4 / π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2)))
  have hBE : b1c_B ε k = 3 * E := by rw [b1c_B, b1c_gauss_eq]
  have hE : 0 < E := Real.exp_pos _
  by_cases hk : k = 0
  · have hB0' : 0 ≤ b1c_B ε k := by rw [hBE]; positivity
    subst hk
    simp [b1c_D, b1c_Fn, b1c_Fc, hB0']
  have hb := b1c_bk_pos hk
  have hbπ := b1c_bk_ge hk
  have hq := b1c_sq_sum_ge_one hk
  -- the continuum coefficient `e^{-εb}/b ≤ E/π ≤ E`
  have hB0 : 0 ≤ Real.exp (-(b1c_bk k) * ε) / b1c_bk k := by positivity
  have hB1 : Real.exp (-(b1c_bk k) * ε) / b1c_bk k ≤ E := by
    rw [div_le_iff₀ hb]
    have := b1c_exp_b_le hε.le k
    nlinarith [pi_gt_three]
  have hFc : ∀ y, |b1c_Fc ε y k| ≤ b1c_B ε k := fun y ↦ by
    simp only [b1c_Fc, hk, if_false, abs_mul, abs_of_nonneg hB0]
    rw [hBE]
    have := abs_cos_le_one (b1c_phase k y)
    nlinarith
  by_cases hbox : b1c_inBox n k
  · have hα := b1c_alpha_ge hn hbox
    have hα1 : 4 / π ≤ b1c_alpha n k := by
      have : 4 / π * 1 ≤ 4 / π * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) := by gcongr
      linarith
    have hαpos : 0 < b1c_alpha n k := lt_of_lt_of_le (by positivity) hα1
    have hA0 : 0 ≤ Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k := by positivity
    have hA1 : Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k ≤ E := by
      have h1 : Real.exp (-ε * b1c_alpha n k) ≤ E := Real.exp_le_exp.2 (by nlinarith)
      have h2 : 1 ≤ b1c_alpha n k := le_trans (by rw [le_div_iff₀ pi_pos]; linarith [pi_lt_four]) hα1
      rw [div_le_iff₀ hαpos]; nlinarith
    have hkn : π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n ≤ π := by
      have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
      have h1 := b1c_abs_div_le_of_box hn hbox.1.1 hbox.1.2
      have h2 := b1c_abs_div_le_of_box hn hbox.2.1 hbox.2.2
      rw [abs_div, abs_of_pos hn', div_le_iff₀ hn'] at h1 h2
      rw [div_le_iff₀ hn']; nlinarith [pi_pos]
    refine ⟨⟨?_, ?_⟩, fun j ↦ ?_, hFc⟩
    · simp only [b1c_D, hbox, ne_eq, hk, not_false_eq_true, and_self, if_true]; positivity
    · simp only [b1c_D, hbox, ne_eq, hk, not_false_eq_true, and_self, if_true]
      rw [hBE]
      have h3 := abs_sub (Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k)
        (Real.exp (-(b1c_bk k) * ε) / b1c_bk k)
      rw [abs_of_nonneg hA0, abs_of_nonneg hB0] at h3
      have h4 : Real.exp (-(b1c_bk k) * ε) / b1c_bk k * (π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n) ≤
          E / π * π := by
        have : Real.exp (-(b1c_bk k) * ε) / b1c_bk k ≤ E / π := by
          rw [div_le_div_iff₀ hb pi_pos]
          have := b1c_exp_b_le hε.le k
          nlinarith [Real.exp_pos (-(b1c_bk k) * ε)]
        gcongr
      rw [div_mul_cancel₀ _ pi_pos.ne'] at h4
      linarith
    · simp only [b1c_Fn, hbox, ne_eq, hk, not_false_eq_true, and_self, if_true, abs_mul,
        abs_of_nonneg hA0]
      rw [hBE]
      have := abs_cos_le_one (2 * π * ((k.1 * j 0 + k.2 * j 1 : ℤ) : ℝ) / n)
      nlinarith
  · refine ⟨⟨?_, ?_⟩, fun j ↦ ?_, hFc⟩
    · simp only [b1c_D, hbox, false_and, if_false, hk]; exact hB0
    · simp only [b1c_D, hbox, false_and, if_false, hk]; rw [hBE]; linarith
    · simp only [b1c_Fn, hbox, false_and, if_false, abs_zero]; rw [hBE]; positivity

lemma b1c_abs_Fn_sub_Fc_le {n : ℕ} (hn : 0 < n) {ε : ℝ} (x : UnitAddTorus (Fin 2))
    (k : ℤ × ℤ) :
    |b1c_Fn n ε (b1c_j n x) k - b1c_Fc ε (torusRep x) k| ≤ b1c_D n ε k := by
  by_cases hk : k = 0
  · simp [b1c_D, b1c_Fn, b1c_Fc, hk]
  by_cases hbox : b1c_inBox n k
  · simp only [b1c_D, b1c_Fn, b1c_Fc, hbox, ne_eq, hk, not_false_eq_true, and_self, if_true,
      if_false]
    set A := Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k
    set B := Real.exp (-(b1c_bk k) * ε) / b1c_bk k
    set cn := Real.cos (2 * π * ((k.1 * b1c_j n x 0 + k.2 * b1c_j n x 1 : ℤ) : ℝ) / n)
    set c := Real.cos (b1c_phase k (torusRep x))
    have hB0 : 0 ≤ B := by have := b1c_bk_pos hk; positivity
    have hcn : |cn| ≤ 1 := abs_cos_le_one _
    have hcc : |cn - c| ≤ π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n := by
      have e2 : 2 * π * ((k.1 * b1c_j n x 0 + k.2 * b1c_j n x 1 : ℤ) : ℝ) / n -
          b1c_phase k (torusRep x) = 2 * π * (k.1 * ((b1c_j n x 0 : ℝ) / n - torusRep x 0) +
          k.2 * ((b1c_j n x 1 : ℝ) / n - torusRep x 1)) := by
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
        simp only [b1c_phase]; push_cast; field_simp; ring
      refine (abs_cos_sub_cos_le _ _).trans ?_
      rw [e2]
      · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
        have h0 := b1c_abs_j_sub hn x 0
        have h1 := b1c_abs_j_sub hn x 1
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        calc 2 * π * |(k.1 : ℝ) * ((b1c_j n x 0 : ℝ) / n - torusRep x 0) +
              k.2 * ((b1c_j n x 1 : ℝ) / n - torusRep x 1)| ≤
            2 * π * (|(k.1 : ℝ)| * (1 / (2 * n)) + |(k.2 : ℝ)| * (1 / (2 * n))) := by
              gcongr
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul]
              gcongr
          _ = π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n := by field_simp
    have e : A * cn - B * c = (A - B) * cn + B * (cn - c) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hB0]
    have : |A - B| * |cn| ≤ |A - B| := mul_le_of_le_one_right (abs_nonneg _) hcn
    have : B * |cn - c| ≤ B * (π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n) := by gcongr
    linarith
  · simp only [b1c_D, b1c_Fn, b1c_Fc, hbox, false_and, if_false, hk, zero_sub, abs_neg,
      abs_mul]
    have hB0 : 0 ≤ Real.exp (-(b1c_bk k) * ε) / b1c_bk k := by have := b1c_bk_pos hk; positivity
    rw [abs_of_nonneg hB0]
    exact mul_le_of_le_one_right hB0 (abs_cos_le_one _)

lemma b1c_inBox_eventually (k : ℤ × ℤ) : ∀ᶠ n : ℕ in atTop, b1c_inBox n k := by
  filter_upwards [eventually_ge_atTop (2 * (k.1.natAbs + k.2.natAbs) + 1)] with n hn
  unfold b1c_inBox
  omega

lemma b1c_D_tendsto {ε : ℝ} (k : ℤ × ℤ) : Tendsto (fun n ↦ b1c_D n ε k) atTop (𝓝 0) := by
  by_cases hk : k = 0
  · simp [b1c_D, hk]
  have hb := b1c_bk_pos hk
  set B := Real.exp (-(b1c_bk k) * ε) / b1c_bk k
  have hA : Tendsto (fun n : ℕ ↦ Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k) atTop (𝓝 B) := by
    have hc : ContinuousAt (fun u : ℝ ↦ Real.exp (-ε * u) / u) (b1c_bk k) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).div
        continuousAt_id hb.ne'
    have := hc.tendsto.comp (b1c_alpha_tendsto k)
    have e : Real.exp (-ε * b1c_bk k) / b1c_bk k = B := by simp only [B]; congr 2; ring
    rw [e] at this
    exact this
  have hlim : Tendsto (fun n : ℕ ↦ |Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k - B| +
      B * (π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ |Real.exp (-ε * b1c_alpha n k) / b1c_alpha n k - B|) atTop
        (𝓝 0) := by
      have := (hA.sub_const B).abs
      simpa using this
    have h2 : Tendsto (fun n : ℕ ↦ B * (π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|) / n)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (π * (|(k.1 : ℝ)| + |(k.2 : ℝ)|))).const_mul B
      simpa using this
    simpa using h1.add h2
  refine hlim.congr' ?_
  filter_upwards [b1c_inBox_eventually k] with n hn
  simp only [b1c_D, hn, ne_eq, hk, not_false_eq_true, and_self, if_true, B]

/-- Tannery: `∑_k D_n(k) → 0`. -/
theorem b1c_tsum_D_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ ∑' k, b1c_D n ε k) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (f := fun n k ↦ b1c_D n ε k) (g := fun _ ↦ 0)
    (b1c_B_summable hε) (fun k ↦ b1c_D_tendsto k) (by
      filter_upwards [eventually_gt_atTop 0] with n hn k
      have := (b1c_B_bounds hn hε k).1
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  simpa using this

/-- Uniform comparison of the long-time parts. -/
theorem b1c_abs_Tn_sub_le {n : ℕ} [NeZero n] {ε : ℝ} (hε : 0 < ε) (x : UnitAddTorus (Fin 2)) :
    |b1c_Tn ε (latPt n x) - ∑' k, b1c_Fc ε (torusRep x) k| ≤ ∑' k, b1c_D n ε k := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hb := b1c_B_bounds hn hε
  have hsB := b1c_B_summable hε
  have hFn : Summable (b1c_Fn n ε (b1c_j n x)) :=
    Summable.of_norm_bounded hsB fun k ↦ by rw [Real.norm_eq_abs]; exact (hb k).2.1 _
  have hFc : Summable (b1c_Fc ε (torusRep x)) :=
    Summable.of_norm_bounded hsB fun k ↦ by rw [Real.norm_eq_abs]; exact (hb k).2.2 _
  have hD : Summable (b1c_D n ε) :=
    Summable.of_nonneg_of_le (fun k ↦ (hb k).1.1) (fun k ↦ (hb k).1.2) hsB
  have e : b1c_Tn ε (latPt n x) = ∑' k, b1c_Fn n ε (b1c_j n x) k := b1c_Tn_eq ε _
  rw [e, ← hFn.tsum_sub hFc]
  have habs : Summable fun k ↦ ‖b1c_Fn n ε (b1c_j n x) k - b1c_Fc ε (torusRep x) k‖ :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _)
      (fun k ↦ by rw [Real.norm_eq_abs]; exact b1c_abs_Fn_sub_Fc_le hn x k) hD
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans (Summable.tsum_le_tsum (fun k ↦ ?_) habs hD)
  rw [Real.norm_eq_abs]; exact b1c_abs_Fn_sub_Fc_le hn x k

/-! ### The scaling limit -/

lemma b1M_nonneg : 0 ≤ b1M := by
  have := b1K_nonneg; unfold b1M; positivity

lemma b1c_K1_nonneg : 0 ≤ b1c_K1 := by unfold b1c_K1; positivity

/-- Continuum decomposition at time `ε`. -/
lemma b1c_cont_decomp {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    4 * π * torusGreen x = (∫ s in (0 : ℝ)..ε, (torusHeat s x - 1)) +
      ∑' k, b1c_Fc ε (torusRep x) k := by
  rw [b1c_torusGreen_split hx hε, ← b1c_integral_large hε, torusProj_torusRep]

/-- **Scaling limit of the lattice Green function**, uniform version: for `δ, η > 0` there is
`n₀` such that `|G_lat^{(n)}(latPt n x) - G_𝕋(x)| ≤ η` for all `n ≥ n₀` and all `x ∈ 𝕋²` with
`|x|_𝕋 ≥ δ`. -/
theorem latGreen_latPt_uniform {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n : ℕ, ∀ _ : NeZero n, n₀ ≤ n → ∀ x : UnitAddTorus (Fin 2),
      δ ≤ torusNorm x → |latGreen (latPt n x) - torusGreen x| ≤ η := by
  set A1 : ℝ := b1c_K1 / (8 * δ ^ 2) + 1
  set A2 : ℝ := 1 / (π * δ ^ 2) + b1M + 1
  have hA1 : 0 < A1 := by have := b1c_K1_nonneg; positivity
  have hA2 : 0 < A2 := by have := b1M_nonneg; positivity
  set ε : ℝ := min 1 (2 * π * η / (A1 + A2))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεA : ε * (A1 + A2) ≤ 2 * π * η := by
    have := min_le_right 1 (2 * π * η / (A1 + A2))
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((tendsto_order.1 (b1c_tsum_D_tendsto hε)).2 (2 * π * η) (by positivity))
  refine ⟨max N1 (⌈π / (2 * δ ^ 2)⌉₊ + 1), fun n _ hn x hx ↦ ?_⟩
  have hn1 : N1 ≤ n := le_of_max_le_left hn
  have hn2 : π / (2 * δ ^ 2) ≤ n := by
    have := le_of_max_le_right hn
    have h' : (⌈π / (2 * δ ^ 2)⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith [Nat.le_ceil (π / (2 * δ ^ 2))]
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn2
  have hx0 := b1c_ne_zero_of_norm hδ hx
  have hr := b1c_r2_ge hδ hx
  -- the weight of the lattice point
  have hw : 8 * δ ^ 2 ≤ lam (latPt n x) := by
    have h := b1c_lam_latPt_ge (n := n) x
    have : 4 * π / n ≤ 8 * δ ^ 2 := by
      rw [div_le_iff₀ hnpos]
      rw [div_le_iff₀ (by positivity)] at hn2
      linarith
    linarith
  have hL := b1c_lat_decomp ε (latPt n x)
  have hC := b1c_cont_decomp hx0 hε
  have hSL := b1c_abs_small_lat_le (by positivity) hw hε hε1
  have hSC := b1c_abs_small_cont_le hδ hx hε hε1
  have hT := b1c_abs_Tn_sub_le (n := n) hε x
  have hD := (hN1 n hn1).le
  have key : |4 * π * latGreen (latPt n x) - 4 * π * torusGreen x| ≤ 4 * π * η := by
    rw [hL, hC]
    have e : (∫ s in (0 : ℝ)..ε, (b1c_P s (latPt n x) - 1)) + b1c_Tn ε (latPt n x) -
        ((∫ s in (0 : ℝ)..ε, (torusHeat s x - 1)) + ∑' k, b1c_Fc ε (torusRep x) k) =
        (∫ s in (0 : ℝ)..ε, (b1c_P s (latPt n x) - 1)) - (∫ s in (0 : ℝ)..ε, (torusHeat s x - 1)) +
          (b1c_Tn ε (latPt n x) - ∑' k, b1c_Fc ε (torusRep x) k) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_sub (∫ s in (0 : ℝ)..ε, (b1c_P s (latPt n x) - 1))
      (∫ s in (0 : ℝ)..ε, (torusHeat s x - 1))
    have hSL' : |∫ s in (0 : ℝ)..ε, (b1c_P s (latPt n x) - 1)| ≤ ε * A1 := hSL
    have hSC' : |∫ s in (0 : ℝ)..ε, (torusHeat s x - 1)| ≤ ε * A2 := hSC
    have : ε * A1 + ε * A2 ≤ 2 * π * η := by rw [← mul_add]; exact hεA
    linarith
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)] at key
  exact le_of_mul_le_mul_left key (by positivity)

lemma b1c_continuous_torusNorm : Continuous torusNorm := by
  unfold torusNorm
  exact Real.continuous_sqrt.comp (((continuous_norm.comp (continuous_apply 0)).pow 2).add
    ((continuous_norm.comp (continuous_apply 1)).pow 2))

lemma b1c_torusNorm_pos {x : UnitAddTorus (Fin 2)} (hx : x ≠ 0) : 0 < torusNorm x := by
  rcases (Real.sqrt_nonneg _).lt_or_eq with h | h
  · exact h
  · exfalso; apply hx
    have h0 : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 0 := by
      have := (Real.sqrt_eq_zero (by positivity)).1 h.symm; exact this
    have h00 : ‖x 0‖ = 0 := by nlinarith [norm_nonneg (x 0), norm_nonneg (x 1)]
    have h11 : ‖x 1‖ = 0 := by nlinarith [norm_nonneg (x 0), norm_nonneg (x 1)]
    funext i; fin_cases i
    · exact norm_eq_zero.1 h00
    · exact norm_eq_zero.1 h11

/-- **Scaling limit of the lattice Green function on `Λ_N`**: for `L ≥ 2`,
`G_{Λ_N}(latPtN L N x) → G_𝕋(x)` uniformly on compact subsets of `𝕋² ∖ {0}` as `N → ∞`. -/
theorem latGreen_latPtN_tendstoUniformlyOn {L : ℕ} [NeZero L] (hL : 2 ≤ L)
    {K : Set (UnitAddTorus (Fin 2))} (hK : IsCompact K) (h0 : (0 : UnitAddTorus (Fin 2)) ∉ K) :
    TendstoUniformlyOn (fun N x ↦ latGreen (latPtN L N x)) torusGreen atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hne b1c_continuous_torusNorm.continuousOn
  have hx₀ : x₀ ≠ 0 := fun h ↦ h0 (h ▸ hx₀K)
  have hδ := b1c_torusNorm_pos hx₀
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨n₀, hn₀⟩ := latGreen_latPt_uniform hδ (half_pos hη)
  filter_upwards [eventually_ge_atTop n₀] with N hN x hx
  rw [dist_comm, Real.dist_eq]
  have hle : n₀ ≤ L ^ N := hN.trans (Nat.lt_pow_self (by omega)).le
  exact lt_of_le_of_lt (hn₀ (L ^ N) inferInstance hle x (hmin hx)) (half_lt_self hη)

end

end Cont
