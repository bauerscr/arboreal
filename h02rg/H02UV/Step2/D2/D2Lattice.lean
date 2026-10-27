import Step2.D2.D2Continuum

/-!
# Lattice versus continuum for `prop:d2`

The lattice quantities of Proposition `prop:d2` are integrals over the Brillouin zone
`[-π, π]²` of functions of `λ(p) = ∑_i (2 - 2 cos p_i)`; their continuum approximations
(`D2Continuum`) are integrals over `ℝ²` of the same functions of `|p|²`. We take `ℝ² = ℂ`.

* `lamC`, `BZ`: `λ(p)` and the Brillouin zone;
* `normSq_sub_lamC_le`, `lamC_ge`: `0 ≤ |p|² - λ(p) ≤ |p|⁴/4`, and `λ(p) ≥ 4|p|²/π²` on `[-π,π]²`;
* `Ia α = ∫_{ℝ²} (1 + |p|)^{-α} d²p` (finite for `α > 2`), `integral_decay_scale`:
  `∫ (1 + a|p|)^{-α} = Ia α / a²`;
* `lattice_radial`: **lattice → continuum.** If `|h(y)| + |y h'(y)| ≤ K (1+y)^{-α}` with `α > 2`
  and `h(y)/y` is integrable on `(0, ∞)`, then for `c > 0`
  `|∫_{[-π,π]²} h(c√λ)/λ - ∫_{ℝ²} h(c|p|)/|p|²| ≤ (π⁶/256 + π⁻²) Ia α K / c²`;
* `lattice_cos`: `|∫_{[-π,π]²} (1 - cos p₁) h(c√λ)/λ| ≤ (π⁴/32) Ia α K / c²` if
  `|h(y)| ≤ K (1+y)^{-α}`;
* `lattice_mass`: `|∫_{[-π,π]²} (g(λ + m²) - g(λ))| ≤ (π²/4) Ia β M m² c²` if
  `|g'(t)| ≤ M c⁴ (1 + c√t)^{-β}`;
* `DecayProfile E K α`: `|1 - E(y)| + |y E'(y)| ≤ K (1+y)^{-α}`;
* `lattice_C`, `lattice_l`, `lattice_Ce1`: for a profile `E` (`0 → 1`) with
  `DecayProfile E K α`, `α > 2`, the lattice values of `C_{j+1}(0,0)`, `𝔩(w_{j+1}) - 𝔩(w_j)`,
  `C_{j+1}(0,e₁)` with symbols `ê_j(p) = E(L^j √λ(p))` are `(1/2π) log L + O(L^{-2j})`, with
  explicit constants.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real

/-! ### `λ(p)` and the Brillouin zone -/

/-- `λ(p) = (2 - 2 cos p₁) + (2 - 2 cos p₂)`, the symbol of `-Δ` on `ℤ²`, for `p ∈ ℝ² = ℂ`. -/
def lamC (z : ℂ) : ℝ := (2 - 2 * cos z.re) + (2 - 2 * cos z.im)

/-- The Brillouin zone `[-π, π]²`. -/
def BZ : Set ℂ := {z | |z.re| ≤ π ∧ |z.im| ≤ π}

theorem two_sub_two_cos_nonneg (x : ℝ) : 0 ≤ 2 - 2 * cos x := by
  linarith [cos_le_one x]

theorem two_sub_two_cos_le (x : ℝ) : 2 - 2 * cos x ≤ x ^ 2 := by
  linarith [one_sub_sq_div_two_le_cos (x := x)]

theorem le_two_sub_two_cos {x : ℝ} (hx : |x| ≤ π) : 4 / π ^ 2 * x ^ 2 ≤ 2 - 2 * cos x := by
  have := cos_le_one_sub_mul_cos_sq hx
  have e : 4 / π ^ 2 * x ^ 2 = 2 * (2 / π ^ 2 * x ^ 2) := by ring
  linarith

theorem sq_sub_sin_sq_le_of_nonneg {y : ℝ} (hy : 0 ≤ y) : y ^ 2 - sin y ^ 2 ≤ y ^ 4 := by
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp
  rcases le_or_gt y 1 with h1 | h1
  · have hs := sin_gt_sub_cube h h1
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    have hy3 : y ^ 3 ≤ y := by nlinarith
    have h0 : 0 ≤ y - y ^ 3 / 4 := by linarith
    have : (y - y ^ 3 / 4) ^ 2 ≤ sin y ^ 2 := pow_le_pow_left₀ h0 hs.le 2
    have e : (y - y ^ 3 / 4) ^ 2 = y ^ 2 - y ^ 4 / 2 + y ^ 6 / 16 := by ring
    have h4 : 0 ≤ y ^ 4 := by positivity
    have h6 : 0 ≤ y ^ 6 := by positivity
    linarith
  · have e : y ^ 4 - y ^ 2 = y ^ 2 * (y ^ 2 - 1) := by ring
    have : 0 ≤ y ^ 2 * (y ^ 2 - 1) := mul_nonneg (sq_nonneg y) (by nlinarith)
    nlinarith [sq_nonneg (sin y)]

theorem sq_sub_sin_sq_le (y : ℝ) : y ^ 2 - sin y ^ 2 ≤ y ^ 4 := by
  rcases le_total 0 y with hy | hy
  · exact sq_sub_sin_sq_le_of_nonneg hy
  · have := sq_sub_sin_sq_le_of_nonneg (neg_nonneg.2 hy)
    rwa [sin_neg, neg_sq, neg_sq, show (-y) ^ 4 = y ^ 4 by ring] at this

/-- `x² - (2 - 2 cos x) ≤ x⁴/4`. -/
theorem sq_sub_two_sub_two_cos_le (x : ℝ) : x ^ 2 - (2 - 2 * cos x) ≤ x ^ 4 / 4 := by
  have h := sq_sub_sin_sq_le (x / 2)
  have hs : sin (x / 2) ^ 2 = 1 / 2 - cos x / 2 := by
    rw [sin_sq_eq_half_sub]; ring_nf
  rw [hs] at h
  nlinarith

theorem normSq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem lamC_nonneg (z : ℂ) : 0 ≤ lamC z :=
  add_nonneg (two_sub_two_cos_nonneg _) (two_sub_two_cos_nonneg _)

theorem lamC_le (z : ℂ) : lamC z ≤ ‖z‖ ^ 2 := by
  rw [normSq_eq]; unfold lamC
  linarith [two_sub_two_cos_le z.re, two_sub_two_cos_le z.im]

/-- `|p|² - λ(p) ≤ |p|⁴/4`. -/
theorem normSq_sub_lamC_le (z : ℂ) : ‖z‖ ^ 2 - lamC z ≤ (‖z‖ ^ 2) ^ 2 / 4 := by
  rw [normSq_eq]; unfold lamC
  have h1 := sq_sub_two_sub_two_cos_le z.re
  have h2 := sq_sub_two_sub_two_cos_le z.im
  nlinarith [sq_nonneg z.re, sq_nonneg z.im, mul_nonneg (sq_nonneg z.re) (sq_nonneg z.im)]

/-- `λ(p) ≥ 4|p|²/π²` on `[-π, π]²`. -/
theorem lamC_ge {z : ℂ} (hz : z ∈ BZ) : 4 / π ^ 2 * ‖z‖ ^ 2 ≤ lamC z := by
  rw [normSq_eq]; unfold lamC
  have h1 := le_two_sub_two_cos hz.1
  have h2 := le_two_sub_two_cos hz.2
  linarith

theorem lamC_pos {z : ℂ} (hz : z ∈ BZ) (hz0 : z ≠ 0) : 0 < lamC z :=
  lt_of_lt_of_le (by have := norm_pos_iff.2 hz0; positivity) (lamC_ge hz)

/-- `√λ(p) ≥ 2|p|/π` on `[-π, π]²`. -/
theorem sqrt_lamC_ge {z : ℂ} (hz : z ∈ BZ) : 2 / π * ‖z‖ ≤ √(lamC z) := by
  rw [show 2 / π * ‖z‖ = √((2 / π * ‖z‖) ^ 2) from (sqrt_sq (by positivity)).symm]
  exact sqrt_le_sqrt (by have := lamC_ge hz; rw [show (2 / π * ‖z‖) ^ 2 = 4 / π ^ 2 * ‖z‖ ^ 2 by ring]; exact this)

theorem pi_lt_norm_of_not_mem_BZ {z : ℂ} (hz : z ∉ BZ) : π < ‖z‖ := by
  simp only [BZ, mem_setOf_eq, not_and_or, not_le] at hz
  rcases hz with h | h
  · exact h.trans_le (Complex.abs_re_le_norm z)
  · exact h.trans_le (Complex.abs_im_le_norm z)

theorem measurableSet_BZ : MeasurableSet BZ := by
  have h1 : MeasurableSet {z : ℂ | |z.re| ≤ π} :=
    measurableSet_le (continuous_abs.comp Complex.continuous_re).measurable measurable_const
  have h2 : MeasurableSet {z : ℂ | |z.im| ≤ π} :=
    measurableSet_le (continuous_abs.comp Complex.continuous_im).measurable measurable_const
  exact h1.inter h2

theorem continuous_lamC : Continuous lamC := by unfold lamC; fun_prop

/-! ### The decay integral -/

/-- `Ia α = ∫_{ℝ²} (1 + |p|)^{-α} d²p`. -/
def Ia (α : ℝ) : ℝ := ∫ z : ℂ, (1 + ‖z‖) ^ (-α)

theorem integrable_decay {α : ℝ} (hα : 2 < α) : Integrable fun z : ℂ => (1 + ‖z‖) ^ (-α) :=
  integrable_one_add_norm (by rw [Complex.finrank_real_complex]; exact_mod_cast hα)

theorem Ia_nonneg (α : ℝ) : 0 ≤ Ia α := integral_nonneg fun _ => by positivity

theorem integrable_decay_scale {α a : ℝ} (hα : 2 < α) (ha : 0 < a) :
    Integrable fun z : ℂ => (1 + a * ‖z‖) ^ (-α) := by
  have := (integrable_decay hα).comp_smul ha.ne'
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha]

/-- `∫ (1 + a|p|)^{-α} d²p = Ia α / a²`. -/
theorem integral_decay_scale (α : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ z : ℂ, (1 + a * ‖z‖) ^ (-α) = Ia α / a ^ 2 := by
  have := MeasureTheory.Measure.integral_comp_smul (volume : Measure ℂ)
    (fun z : ℂ => (1 + ‖z‖) ^ (-α)) a
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, Complex.finrank_real_complex,
    smul_eq_mul] at this
  rw [this, Ia, abs_of_pos (by positivity)]
  field_simp

theorem decay_antitone {α : ℝ} (hα : 0 ≤ α) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1 + y) ^ (-α) ≤ (1 + x) ^ (-α) :=
  rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

/-! ### Lattice versus continuum: the mean value estimate -/

section Radial

variable {h h' : ℝ → ℝ} {K α c : ℝ}

theorem K_nonneg_of_bound (hb : ∀ y, 0 < y → |h y| + |y * h' y| ≤ K * (1 + y) ^ (-α)) :
    0 ≤ K := by
  have h1 := hb 1 one_pos
  have h2 : 0 < (1 + (1 : ℝ)) ^ (-α) := by positivity
  have h3 : 0 ≤ |h 1| + |1 * h' 1| := by positivity
  by_contra hK
  rw [not_le] at hK
  nlinarith

theorem abs_Phi_le {y : ℝ} : |Phi h h' y| ≤ |h y| + |y * h' y| := by
  unfold Phi
  calc |h y - y * h' y / 2| ≤ |h y| + |y * h' y / 2| := abs_sub _ _
    _ ≤ |h y| + |y * h' y| := by
        rw [abs_div, abs_two]; linarith [abs_nonneg (y * h' y)]

/-- **Mean value step.** For `0 < a ≤ b`, `|f_c(b) - f_c(a)| ≤ K (1 + c√a)^{-α} a^{-2} (b - a)`,
where `f_c(s) = h(c√s)/s`. -/
theorem fc_sub_le (hd : ∀ y, 0 < y → HasDerivAt h (h' y) y)
    (hb : ∀ y, 0 < y → |h y| + |y * h' y| ≤ K * (1 + y) ^ (-α)) (hα : 0 ≤ α) (hc : 0 < c)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |fc h c b - fc h c a| ≤ K * (1 + c * √a) ^ (-α) / a ^ 2 * (b - a) := by
  have hK := K_nonneg_of_bound hb
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fc h c)
    (f' := fun t => -Phi h h' (c * √t) / t ^ 2) (s := Icc a b)
    (C := K * (1 + c * √a) ^ (-α) / a ^ 2)
    (fun t ht => (hasDerivAt_fc hd hc (ha.trans_le ht.1)).hasDerivWithinAt)
    (fun t ht => by
      have ht0 : 0 < t := ha.trans_le ht.1
      have hsq : √a ≤ √t := sqrt_le_sqrt ht.1
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
      have h1 : |Phi h h' (c * √t)| ≤ K * (1 + c * √a) ^ (-α) :=
        abs_Phi_le.trans ((hb _ (by positivity)).trans (mul_le_mul_of_nonneg_left
          (decay_antitone hα (by positivity) (by gcongr)) hK))
      exact div_le_div₀ (by positivity) h1 (by positivity) (by gcongr; exact ht.1))
    (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ b - a by linarith)]
    at this

theorem lamC_zero : lamC 0 = 0 := by simp [lamC]

/-- **Pointwise lattice error.** On `[-π, π]²`,
`|h(c√λ)/λ - h(c|p|)/|p|²| ≤ (π⁴/64) K (1 + (2c/π)|p|)^{-α}`. -/
theorem lattice_pointwise (hd : ∀ y, 0 < y → HasDerivAt h (h' y) y)
    (hb : ∀ y, 0 < y → |h y| + |y * h' y| ≤ K * (1 + y) ^ (-α)) (hα : 0 ≤ α) (hc : 0 < c)
    {z : ℂ} (hz : z ∈ BZ) :
    |h (c * √(lamC z)) / lamC z - h (c * ‖z‖) / ‖z‖ ^ 2| ≤
      π ^ 4 / 64 * K * (1 + 2 * c / π * ‖z‖) ^ (-α) := by
  have hK := K_nonneg_of_bound hb
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [lamC_zero]; positivity
  have ha := lamC_pos hz hz0
  have hab := lamC_le z
  have hge := lamC_ge hz
  have hmv := fc_sub_le hd hb hα hc ha hab
  simp only [fc, sqrt_sq (norm_nonneg z)] at hmv
  rw [abs_sub_comm]
  set a := lamC z
  set b := ‖z‖ ^ 2
  have hb0 : 0 ≤ b := by positivity
  have hdiff : b - a ≤ π ^ 4 / 64 * a ^ 2 := by
    have h1 := normSq_sub_lamC_le z
    have hpi : 0 < π := pi_pos
    have h2 : b ≤ π ^ 2 / 4 * a := by
      have : π ^ 2 / 4 * (4 / π ^ 2 * b) = b := by field_simp
      nlinarith
    have h3 : b ^ 2 ≤ (π ^ 2 / 4 * a) ^ 2 := pow_le_pow_left₀ hb0 h2 2
    nlinarith
  have hdec : (1 + c * √a) ^ (-α) ≤ (1 + 2 * c / π * ‖z‖) ^ (-α) :=
    decay_antitone hα (by positivity) (by
      have := sqrt_lamC_ge hz
      calc 2 * c / π * ‖z‖ = c * (2 / π * ‖z‖) := by ring
        _ ≤ c * √a := by gcongr)
  calc _ ≤ K * (1 + c * √a) ^ (-α) / a ^ 2 * (b - a) := hmv
    _ ≤ K * (1 + c * √a) ^ (-α) / a ^ 2 * (π ^ 4 / 64 * a ^ 2) := by gcongr
    _ = π ^ 4 / 64 * K * (1 + c * √a) ^ (-α) := by field_simp
    _ ≤ π ^ 4 / 64 * K * (1 + 2 * c / π * ‖z‖) ^ (-α) := by gcongr

/-- `h(c|p|)/|p|²` is integrable on `ℝ²` if `h(y)/y` is integrable on `(0, ∞)`. -/
theorem integrable_radial_div (hi : IntegrableOn (fun y => h y / y) (Ioi 0)) (hc : 0 < c) :
    Integrable fun z : ℂ => h (c * ‖z‖) / ‖z‖ ^ 2 := by
  have h1 := (integrableOn_Ioi_comp_mul_left_iff (fun y => h y / y) 0 hc).2
    (by rwa [mul_zero])
  have h2 := h1.const_mul c
  refine (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y => h (c * y) / y ^ 2)).2 ?_
  rw [Complex.finrank_real_complex]
  refine IntegrableOn.congr_fun h2 (fun y (hy : 0 < y) => ?_) measurableSet_Ioi
  simp only [smul_eq_mul, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp

/-- `h` extended by `0` off `(0, ∞)`; measurable if `h` is continuous on `(0, ∞)`. -/
def hpos (h : ℝ → ℝ) : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise h 0

theorem measurable_hpos (hcont : ContinuousOn h (Ioi 0)) : Measurable (hpos h) := by
  classical
  exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioi

theorem fc_hpos {s : ℝ} (hs : 0 ≤ s) (hc : 0 < c) : hpos h (c * √s) / s = h (c * √s) / s := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp
  · classical
    simp only [hpos, Set.piecewise_eq_of_mem _ _ _ (show c * √s ∈ Ioi 0 from
      mul_pos hc (sqrt_pos.2 hs))]

theorem measurable_lattice (hcont : ContinuousOn h (Ioi 0)) (hc : 0 < c) :
    Measurable fun z : ℂ => h (c * √(lamC z)) / lamC z := by
  have : (fun z : ℂ => h (c * √(lamC z)) / lamC z) =
      fun z => hpos h (c * √(lamC z)) / lamC z :=
    funext fun z => (fc_hpos (lamC_nonneg z) hc).symm
  rw [this]
  exact ((measurable_hpos hcont).comp (measurable_const.mul
    (continuous_sqrt.comp continuous_lamC).measurable)).div continuous_lamC.measurable

/-- **Lattice → continuum.** If `|h(y)| + |y h'(y)| ≤ K (1+y)^{-α}` with `α > 2` and `h(y)/y`
is integrable on `(0, ∞)`, then for `c > 0`
`|∫_{[-π,π]²} h(c√λ)/λ d²p - ∫_{ℝ²} h(c|p|)/|p|² d²p| ≤ (π⁶/256 + π⁻²) Ia(α) K / c²`. The
first part comes from `λ(p) = |p|²(1 + O(|p|²))` (`lattice_pointwise`), the second from the
region `|p|_∞ > π`. Both are localised at `|p| ≍ 1/c`. -/
theorem lattice_radial (hd : ∀ y, 0 < y → HasDerivAt h (h' y) y)
    (hb : ∀ y, 0 < y → |h y| + |y * h' y| ≤ K * (1 + y) ^ (-α))
    (hi : IntegrableOn (fun y => h y / y) (Ioi 0)) (hα : 2 < α) (hc : 0 < c) :
    |(∫ z in BZ, h (c * √(lamC z)) / lamC z) - ∫ z : ℂ, h (c * ‖z‖) / ‖z‖ ^ 2| ≤
      (π ^ 6 / 256 + 1 / π ^ 2) * Ia α * K / c ^ 2 := by
  have hK := K_nonneg_of_bound hb
  have hα0 : 0 ≤ α := by linarith
  have hcont : ContinuousOn h (Ioi 0) := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  set Fl := fun z : ℂ => h (c * √(lamC z)) / lamC z
  set Fc := fun z : ℂ => h (c * ‖z‖) / ‖z‖ ^ 2
  have hFc : Integrable Fc := integrable_radial_div hi hc
  have hpi : 0 < π := pi_pos
  have ha : 0 < 2 * c / π := by positivity
  set g := fun z : ℂ => π ^ 4 / 64 * K * (1 + 2 * c / π * ‖z‖) ^ (-α)
  have hg : Integrable g := (integrable_decay_scale hα ha).const_mul _
  have hbound : ∀ᵐ z ∂(volume.restrict BZ), ‖Fl z - Fc z‖ ≤ g z :=
    ae_restrict_of_forall_mem measurableSet_BZ fun z hz => by
      rw [Real.norm_eq_abs]; exact lattice_pointwise hd hb hα0 hc hz
  have hmeas : AEStronglyMeasurable (fun z => Fl z - Fc z) (volume.restrict BZ) :=
    ((measurable_lattice hcont hc).aestronglyMeasurable.sub hFc.aestronglyMeasurable).restrict
  have hdiff : IntegrableOn (fun z => Fl z - Fc z) BZ := hg.integrableOn.mono' hmeas hbound
  have hFl : IntegrableOn Fl BZ := by
    exact IntegrableOn.congr_fun (hdiff.add hFc.integrableOn) (fun z _ => by simp)
      measurableSet_BZ
  have hsplit : (∫ z in BZ, Fl z) - ∫ z, Fc z =
      (∫ z in BZ, (Fl z - Fc z)) - ∫ z in BZᶜ, Fc z := by
    rw [integral_sub hFl hFc.integrableOn, ← integral_add_compl measurableSet_BZ hFc]
    ring
  rw [hsplit]
  -- the Brillouin zone
  have e1 : |∫ z in BZ, (Fl z - Fc z)| ≤ π ^ 6 / 256 * Ia α * K / c ^ 2 := by
    have := norm_integral_le_of_norm_le hg.integrableOn hbound
    rw [Real.norm_eq_abs] at this
    refine this.trans ((setIntegral_le_integral hg (Eventually.of_forall fun z => by
      positivity)).trans (le_of_eq ?_))
    simp only [g]
    rw [integral_const_mul, integral_decay_scale α ha]
    field_simp
    ring
  -- the region outside
  set g2 := fun z : ℂ => K / π ^ 2 * (1 + c * ‖z‖) ^ (-α)
  have hg2 : Integrable g2 := (integrable_decay_scale hα hc).const_mul _
  have e2 : |∫ z in BZᶜ, Fc z| ≤ 1 / π ^ 2 * Ia α * K / c ^ 2 := by
    have hb2 : ∀ᵐ z ∂(volume.restrict BZᶜ), ‖Fc z‖ ≤ g2 z :=
      ae_restrict_of_forall_mem measurableSet_BZ.compl fun z hz => by
        have hz' := pi_lt_norm_of_not_mem_BZ hz
        have hn : 0 < ‖z‖ := hpi.trans hz'
        have h1 := hb (c * ‖z‖) (by positivity)
        have h2 : |h (c * ‖z‖)| ≤ K * (1 + c * ‖z‖) ^ (-α) := by
          linarith [abs_nonneg (c * ‖z‖ * h' (c * ‖z‖))]
        have h3 : π ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hpi.le hz'.le 2
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖z‖ ^ 2)]
        calc |h (c * ‖z‖)| / ‖z‖ ^ 2 ≤ K * (1 + c * ‖z‖) ^ (-α) / π ^ 2 :=
              div_le_div₀ (by positivity) h2 (by positivity) h3
          _ = g2 z := by simp only [g2]; ring
    have := norm_integral_le_of_norm_le hg2.integrableOn hb2
    rw [Real.norm_eq_abs] at this
    refine this.trans ((setIntegral_le_integral hg2 (Eventually.of_forall fun z => by
      positivity)).trans (le_of_eq ?_))
    simp only [g2]
    rw [integral_const_mul, integral_decay_scale α hc]
    field_simp
  calc _ ≤ |∫ z in BZ, (Fl z - Fc z)| + |∫ z in BZᶜ, Fc z| := abs_sub _ _
    _ ≤ _ := by
      have : (π ^ 6 / 256 + 1 / π ^ 2) * Ia α * K / c ^ 2 =
          π ^ 6 / 256 * Ia α * K / c ^ 2 + 1 / π ^ 2 * Ia α * K / c ^ 2 := by ring
      linarith

/-- The lattice integrand `h(c√λ)/λ` is integrable on `[-π, π]²` (under the hypotheses of
`lattice_radial`). -/
theorem lattice_integrableOn (hd : ∀ y, 0 < y → HasDerivAt h (h' y) y)
    (hb : ∀ y, 0 < y → |h y| + |y * h' y| ≤ K * (1 + y) ^ (-α))
    (hi : IntegrableOn (fun y => h y / y) (Ioi 0)) (hα : 2 < α) (hc : 0 < c) :
    IntegrableOn (fun z => h (c * √(lamC z)) / lamC z) BZ := by
  have hcont : ContinuousOn h (Ioi 0) := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hFc := integrable_radial_div hi hc
  have ha : 0 < 2 * c / π := by have := pi_pos; positivity
  have hg := (integrable_decay_scale hα ha).const_mul (π ^ 4 / 64 * K)
  have hdiff : IntegrableOn (fun z => h (c * √(lamC z)) / lamC z - h (c * ‖z‖) / ‖z‖ ^ 2) BZ :=
    hg.integrableOn.mono'
      ((measurable_lattice hcont hc).aestronglyMeasurable.sub hFc.aestronglyMeasurable).restrict
      (ae_restrict_of_forall_mem measurableSet_BZ fun z hz => by
        rw [Real.norm_eq_abs]; exact lattice_pointwise hd hb (by linarith) hc hz)
  exact IntegrableOn.congr_fun (hdiff.add hFc.integrableOn) (fun z _ => by simp)
    measurableSet_BZ

/-- **The gradient direction.** If `|h(y)| ≤ K (1+y)^{-α}` with `α > 2`, then
`|∫_{[-π,π]²} (1 - cos p₁) h(c√λ)/λ d²p| ≤ (π⁴/32) Ia(α) K / c²`. With `h(c√λ)/λ = Ĉ_{j+1}`
this is `C_{j+1}(0,0) - C_{j+1}(0,e₁) = O(L^{-2j})`. -/
theorem lattice_cos (hb : ∀ y, 0 < y → |h y| ≤ K * (1 + y) ^ (-α)) (hα : 2 < α) (hc : 0 < c) :
    |∫ z in BZ, (1 - cos z.re) * (h (c * √(lamC z)) / lamC z)| ≤
      π ^ 4 / 32 * Ia α * K / c ^ 2 := by
  have hpi : 0 < π := pi_pos
  have hK : 0 ≤ K := by
    have h1 := hb 1 one_pos
    have h2 : 0 < (1 + (1 : ℝ)) ^ (-α) := by positivity
    by_contra hK; rw [not_le] at hK; nlinarith [abs_nonneg (h 1)]
  have ha : 0 < 2 * c / π := by positivity
  set g := fun z : ℂ => π ^ 2 / 8 * K * (1 + 2 * c / π * ‖z‖) ^ (-α)
  have hg : Integrable g := (integrable_decay_scale hα ha).const_mul _
  have hbound : ∀ᵐ z ∂(volume.restrict BZ),
      ‖(1 - cos z.re) * (h (c * √(lamC z)) / lamC z)‖ ≤ g z :=
    ae_restrict_of_forall_mem measurableSet_BZ fun z hz => by
      rw [Real.norm_eq_abs]
      rcases eq_or_ne z 0 with rfl | hz0
      · simp only [lamC_zero, div_zero, mul_zero, abs_zero, g]; positivity
      have hl := lamC_pos hz hz0
      have hge := lamC_ge hz
      have h1 : 0 ≤ 1 - cos z.re := by linarith [cos_le_one z.re]
      have h2 : 1 - cos z.re ≤ π ^ 2 / 8 * lamC z := by
        have := one_sub_sq_div_two_le_cos (x := z.re)
        have h3 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by rw [normSq_eq]; nlinarith [sq_nonneg z.im]
        have h4 : π ^ 2 / 8 * (4 / π ^ 2 * ‖z‖ ^ 2) = ‖z‖ ^ 2 / 2 := by field_simp; ring
        nlinarith
      have hdec : |h (c * √(lamC z))| ≤ K * (1 + 2 * c / π * ‖z‖) ^ (-α) :=
        (hb _ (by have := sqrt_pos.2 hl; positivity)).trans (mul_le_mul_of_nonneg_left
          (decay_antitone (by linarith) (by positivity) (by
            have := sqrt_lamC_ge hz
            calc 2 * c / π * ‖z‖ = c * (2 / π * ‖z‖) := by ring
              _ ≤ c * √(lamC z) := by gcongr)) hK)
      rw [abs_mul, abs_div, abs_of_nonneg h1, abs_of_pos hl]
      calc (1 - cos z.re) * (|h (c * √(lamC z))| / lamC z)
          ≤ π ^ 2 / 8 * lamC z * (|h (c * √(lamC z))| / lamC z) := by gcongr
        _ = π ^ 2 / 8 * |h (c * √(lamC z))| := by field_simp
        _ ≤ g z := by simp only [g]; rw [mul_assoc]; gcongr
  have := norm_integral_le_of_norm_le hg.integrableOn hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans ((setIntegral_le_integral hg (Eventually.of_forall fun z => by
    positivity)).trans (le_of_eq ?_))
  simp only [g]
  rw [integral_const_mul, integral_decay_scale α ha]
  field_simp
  ring

/-- **The mass.** If `|g'(t)| ≤ M c⁴ (1 + c√t)^{-β}` for `t > 0`, with `β > 2`, then
`|∫_{[-π,π]²} (g(λ + m²) - g(λ)) d²p| ≤ (π²/4) Ia(β) M m² c²`. For `g = f_c`,
`f_c(s) = h(c√s)/s`, the hypothesis holds if `|Φ_h(y)| ≤ M y⁴ (1+y)^{-β}`
(`fc_deriv_bound_mass`). -/
theorem lattice_mass {g g' : ℝ → ℝ} {M β msq : ℝ} (hd : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hb : ∀ t, 0 < t → |g' t| ≤ M * c ^ 4 * (1 + c * √t) ^ (-β)) (hβ : 2 < β) (hc : 0 < c)
    (hm : 0 ≤ msq) :
    |∫ z in BZ, (g (lamC z + msq) - g (lamC z))| ≤ π ^ 2 / 4 * Ia β * M * msq * c ^ 2 := by
  have hpi : 0 < π := pi_pos
  have hM : 0 ≤ M := by
    have h1 := hb 1 one_pos
    have h2 : 0 < (1 + c * √1) ^ (-β) := by positivity
    have h3 : 0 < c ^ 4 := by positivity
    by_contra hM; rw [not_le] at hM
    have : M * c ^ 4 * (1 + c * √1) ^ (-β) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hM h3) h2
    linarith [abs_nonneg (g' 1)]
  have ha : 0 < 2 * c / π := by positivity
  set G := fun z : ℂ => M * c ^ 4 * msq * (1 + 2 * c / π * ‖z‖) ^ (-β)
  have hG : Integrable G := (integrable_decay_scale hβ ha).const_mul _
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := ae_iff.2 (by simp)
  have hbound : ∀ᵐ z ∂(volume.restrict BZ), ‖g (lamC z + msq) - g (lamC z)‖ ≤ G z := by
    filter_upwards [ae_restrict_mem measurableSet_BZ, ae_restrict_of_ae hne] with z hz hz0
    have hl := lamC_pos hz hz0
    have hdec : (1 + c * √(lamC z)) ^ (-β) ≤ (1 + 2 * c / π * ‖z‖) ^ (-β) :=
      decay_antitone (by linarith) (by positivity) (by
        have := sqrt_lamC_ge hz
        calc 2 * c / π * ‖z‖ = c * (2 / π * ‖z‖) := by ring
          _ ≤ c * √(lamC z) := by gcongr)
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
      (s := Icc (lamC z) (lamC z + msq)) (C := M * c ^ 4 * (1 + c * √(lamC z)) ^ (-β))
      (fun t ht => (hd t (hl.trans_le ht.1)).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        refine (hb t (hl.trans_le ht.1)).trans (mul_le_mul_of_nonneg_left
          (decay_antitone (by linarith) (by positivity) (by gcongr; exact ht.1)) (by positivity)))
      (convex_Icc _ _) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at this
    rw [abs_of_nonneg hm] at this
    rw [Real.norm_eq_abs]
    refine this.trans ?_
    simp only [G]
    calc M * c ^ 4 * (1 + c * √(lamC z)) ^ (-β) * msq
        = M * c ^ 4 * msq * (1 + c * √(lamC z)) ^ (-β) := by ring
      _ ≤ M * c ^ 4 * msq * (1 + 2 * c / π * ‖z‖) ^ (-β) := by gcongr
  have := norm_integral_le_of_norm_le hG.integrableOn hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans ((setIntegral_le_integral hG (Eventually.of_forall fun z => by
    positivity)).trans (le_of_eq ?_))
  simp only [G]
  rw [integral_const_mul, integral_decay_scale β ha]
  field_simp
  ring

/-- For `f_c(s) = h(c√s)/s`: `|f_c'(t)| ≤ M c⁴ (1 + c√t)^{-β}` if `|Φ_h(y)| ≤ M y⁴ (1+y)^{-β}`.
(`Φ_h = 0` for `h(y) = y²`, so this holds if `h(y) = a y² + O(y⁴)` at `0`.) -/
theorem fc_deriv_bound_mass {M β : ℝ}
    (hΦ : ∀ y, 0 < y → |Phi h h' y| ≤ M * y ^ 4 * (1 + y) ^ (-β)) (hc : 0 < c) {t : ℝ}
    (ht : 0 < t) : |-Phi h h' (c * √t) / t ^ 2| ≤ M * c ^ 4 * (1 + c * √t) ^ (-β) := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have hsq : √t ^ 2 = t := sq_sqrt ht.le
  rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  refine (hΦ _ (by positivity)).trans (le_of_eq ?_)
  have e : (c * √t) ^ 4 = c ^ 4 * t ^ 2 := by
    rw [mul_pow, show √t ^ 4 = (√t ^ 2) ^ 2 by ring, hsq]
  rw [e]
  ring

/-- **The gradient direction in the continuum.** If `|h(y)| ≤ K (1+y)^{-α}` with `α > 2`, then
`|∫_{ℝ²} (1 - cos p₁) h(c|p|)/|p|² d²p| ≤ Ia(α) K / (2c²)`. -/
theorem continuum_cos (hb : ∀ y, 0 < y → |h y| ≤ K * (1 + y) ^ (-α)) (hα : 2 < α) (hc : 0 < c) :
    |∫ z : ℂ, (1 - cos z.re) * (h (c * ‖z‖) / ‖z‖ ^ 2)| ≤ Ia α * K / (2 * c ^ 2) := by
  have hK : 0 ≤ K := by
    have h1 := hb 1 one_pos
    have h2 : 0 < (1 + (1 : ℝ)) ^ (-α) := by positivity
    by_contra hK; rw [not_le] at hK; nlinarith [abs_nonneg (h 1)]
  set g := fun z : ℂ => K / 2 * (1 + c * ‖z‖) ^ (-α)
  have hg : Integrable g := (integrable_decay_scale hα hc).const_mul _
  have hbound : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖(1 - cos z.re) * (h (c * ‖z‖) / ‖z‖ ^ 2)‖ ≤ g z :=
    Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      rcases eq_or_ne z 0 with rfl | hz0
      · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
          mul_zero, abs_zero, g]; positivity
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have h1 : 0 ≤ 1 - cos z.re := by linarith [cos_le_one z.re]
      have h2 : 1 - cos z.re ≤ ‖z‖ ^ 2 / 2 := by
        have := one_sub_sq_div_two_le_cos (x := z.re)
        have h3 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by rw [normSq_eq]; nlinarith [sq_nonneg z.im]
        linarith
      rw [abs_mul, abs_div, abs_of_nonneg h1, abs_of_pos (by positivity : (0 : ℝ) < ‖z‖ ^ 2)]
      calc (1 - cos z.re) * (|h (c * ‖z‖)| / ‖z‖ ^ 2)
          ≤ ‖z‖ ^ 2 / 2 * (|h (c * ‖z‖)| / ‖z‖ ^ 2) := by gcongr
        _ = |h (c * ‖z‖)| / 2 := by field_simp
        _ ≤ g z := by
            simp only [g]
            have := hb (c * ‖z‖) (by positivity)
            linarith
  have := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  simp only [g]
  rw [integral_const_mul, integral_decay_scale α hc]
  field_simp

end Radial

/-! ### Application to the scaling profile `E` -/

section Profile

variable {E E' : ℝ → ℝ} {K α L : ℝ}

/-- `|1 - E(y)| + |y E'(y)| ≤ K (1+y)^{-α}`: `E → 1` at `∞` at rate `y^{-α}`, and `yE'(y)`
decays at the same rate. -/
def DecayProfile (E E' : ℝ → ℝ) (K α : ℝ) : Prop :=
  ∀ y, 0 < y → |1 - E y| + |y * E' y| ≤ K * (1 + y) ^ (-α)

theorem DecayProfile.K_nonneg (hD : DecayProfile E E' K α) : 0 ≤ K := by
  have h1 := hD 1 one_pos
  have h2 : 0 < (1 + (1 : ℝ)) ^ (-α) := by positivity
  have h3 : 0 ≤ |1 - E 1| + |1 * E' 1| := by positivity
  by_contra hK; rw [not_le] at hK; nlinarith

/-- The single-scale difference `h(y) = E(Ly) - E(y)` satisfies the hypothesis of
`lattice_radial` with constant `2K`. -/
theorem DecayProfile.diff (hD : DecayProfile E E' K α) (hα : 0 ≤ α) (hL : 1 ≤ L) {y : ℝ}
    (hy : 0 < y) :
    |E (L * y) - E y| + |y * (L * E' (L * y) - E' y)| ≤ 2 * K * (1 + y) ^ (-α) := by
  have hK := hD.K_nonneg
  have h1 := hD (L * y) (by positivity)
  have h2 := hD y hy
  have h3 : (1 + L * y) ^ (-α) ≤ (1 + y) ^ (-α) :=
    decay_antitone hα hy.le (by nlinarith)
  have e1 : |E (L * y) - E y| ≤ |1 - E (L * y)| + |1 - E y| := by
    rw [show E (L * y) - E y = (1 - E y) - (1 - E (L * y)) by ring]
    linarith [abs_sub (1 - E y) (1 - E (L * y))]
  have e2 : |y * (L * E' (L * y) - E' y)| ≤ |L * y * E' (L * y)| + |y * E' y| := by
    rw [show y * (L * E' (L * y) - E' y) = L * y * E' (L * y) - y * E' y by ring]
    exact abs_sub _ _
  nlinarith

/-- `E²` is again a decay profile, with constant `2(1+K)K`. -/
theorem DecayProfile.sq (hD : DecayProfile E E' K α) (hα : 0 ≤ α) :
    DecayProfile (fun y => E y * E y) (fun y => 2 * E y * E' y) (2 * (1 + K) * K) α := by
  intro y hy
  have hK := hD.K_nonneg
  have h := hD y hy
  have hdec : (1 + y) ^ (-α) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hu : |1 - E y| ≤ K := by
    have : K * (1 + y) ^ (-α) ≤ K := mul_le_of_le_one_right hK hdec
    linarith [abs_nonneg (y * E' y)]
  have hE : |E y| ≤ 1 + K := by
    have := abs_sub (1 : ℝ) (1 - E y)
    rw [show (1 : ℝ) - (1 - E y) = E y by ring, abs_one] at this
    linarith
  have e1 : |1 - E y * E y| ≤ (2 + K) * |1 - E y| := by
    rw [show 1 - E y * E y = (1 - E y) * (2 - (1 - E y)) by ring, abs_mul, mul_comm]
    gcongr
    calc |2 - (1 - E y)| ≤ |(2 : ℝ)| + |1 - E y| := abs_sub _ _
      _ ≤ 2 + K := by rw [abs_two]; linarith
  have e2 : |y * (2 * E y * E' y)| ≤ 2 * (1 + K) * |y * E' y| := by
    rw [show y * (2 * E y * E' y) = 2 * E y * (y * E' y) by ring, abs_mul, abs_mul, abs_two]
    gcongr
  have hu0 := abs_nonneg (1 - E y)
  have hv0 := abs_nonneg (y * E' y)
  calc |1 - E y * E y| + |y * (2 * E y * E' y)|
      ≤ 2 * (1 + K) * (|1 - E y| + |y * E' y|) := by nlinarith
    _ ≤ 2 * (1 + K) * (K * (1 + y) ^ (-α)) := by gcongr
    _ = 2 * (1 + K) * K * (1 + y) ^ (-α) := by ring

theorem hasDerivAt_scale_diff (hd : ∀ y, 0 < y → HasDerivAt E (E' y) y) (hL : 0 < L) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun y => E (L * y) - E y) (L * E' (L * y) - E' y) y := by
  have h1 := (hd (L * y) (by positivity)).comp y ((hasDerivAt_id y).const_mul L)
  convert h1.sub (hd y hy) using 1
  simp only [mul_one]; ring

theorem pow_succ_mul_eq (L x : ℝ) (j : ℕ) : L * (L ^ j * x) = L ^ (j + 1) * x := by ring

/-- **`C_{j+1}(0,0)` on the lattice.** For a profile `E` (`0 → 1`) with
`|1 - E(y)| + |yE'(y)| ≤ K (1+y)^{-α}`, `α > 2`, and lattice symbol
`Ĉ_{j+1}(p) = (E(L^{j+1}√λ(p)) - E(L^j√λ(p)))/λ(p)`,
`|⨍_{[-π,π]²} Ĉ_{j+1} - (1/2π) log L| ≤ (2π)^{-2} (π⁶/256 + π⁻²) Ia(α) 2K L^{-2j}`. -/
theorem lattice_C (hE : Profile E 0 1) (hd : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hD : DecayProfile E E' K α) (hα : 2 < α) (hL : 1 ≤ L) (j : ℕ) :
    |(2 * π)⁻¹ ^ 2 * (∫ z in BZ,
        (E (L ^ (j + 1) * √(lamC z)) - E (L ^ j * √(lamC z))) / lamC z) - log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2) * Ia α * (2 * K) / (L ^ j) ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hc : 0 < L ^ j := by positivity
  have hi : IntegrableOn (fun y => (E (L * y) - E y) / y) (Ioi 0) := by
    have := hE.integrableOn one_pos hL
    simpa using this
  have key := lattice_radial (h := fun y => E (L * y) - E y)
    (h' := fun y => L * E' (L * y) - E' y) (fun y hy => hasDerivAt_scale_diff hd hL0 hy)
    (fun y hy => hD.diff (by linarith) hL hy) hi hα hc
  simp only [pow_succ_mul_eq] at key
  rw [← continuum_C hE hL j, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  gcongr

/-- **`𝔩(w_{j+1}) - 𝔩(w_j)` on the lattice.** With `ŵ_j(p) = E(L^j√λ(p))/λ(p)` and
`𝔩(w) = ⨍ λ ŵ²`, `|𝔩(w_{j+1}) - 𝔩(w_j) - (1/2π) log L| = O(L^{-2j})`, with the constant of
`lattice_C` for `E²` (decay constant `2(1+K)K`). -/
theorem lattice_l (hE : Profile E 0 1) (hd : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hD : DecayProfile E E' K α) (hα : 2 < α) (hL : 1 ≤ L) (j : ℕ) :
    |(2 * π)⁻¹ ^ 2 * (∫ z in BZ, lamC z * ((E (L ^ (j + 1) * √(lamC z)) / lamC z) ^ 2 -
        (E (L ^ j * √(lamC z)) / lamC z) ^ 2)) - log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2) * Ia α * (2 * (2 * (1 + K) * K)) /
        (L ^ j) ^ 2) := by
  have hE2 : Profile (fun y => E y * E y) 0 1 := by
    have := hE.mul hE; norm_num at this; exact this
  have hd2 : ∀ y, 0 < y → HasDerivAt (fun y => E y * E y) (2 * E y * E' y) y := fun y hy => by
    convert (hd y hy).mul (hd y hy) using 1; ring
  have := lattice_C hE2 hd2 (hD.sq (by linarith)) hα hL j
  have eq : (∫ z in BZ, lamC z * ((E (L ^ (j + 1) * √(lamC z)) / lamC z) ^ 2 -
      (E (L ^ j * √(lamC z)) / lamC z) ^ 2)) = ∫ z in BZ,
      (E (L ^ (j + 1) * √(lamC z)) * E (L ^ (j + 1) * √(lamC z)) -
        E (L ^ j * √(lamC z)) * E (L ^ j * √(lamC z))) / lamC z := by
    refine setIntegral_congr_fun measurableSet_BZ fun z _ => ?_
    rcases eq_or_ne (lamC z) 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [eq]
  exact this

/-- **`C_{j+1}(0,e₁)` on the lattice.** `⨍ cos(p₁) Ĉ_{j+1} = (1/2π) log L + O(L^{-2j})`. -/
theorem lattice_Ce1 (hE : Profile E 0 1) (hd : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hD : DecayProfile E E' K α) (hα : 2 < α) (hL : 1 ≤ L) (j : ℕ) :
    |(2 * π)⁻¹ ^ 2 * (∫ z in BZ, cos z.re *
        ((E (L ^ (j + 1) * √(lamC z)) - E (L ^ j * √(lamC z))) / lamC z)) - log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2 + π ^ 4 / 32) * Ia α * (2 * K) / (L ^ j) ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hc : 0 < L ^ j := by positivity
  have hα0 : 0 ≤ α := by linarith
  have hi : IntegrableOn (fun y => (E (L * y) - E y) / y) (Ioi 0) := by
    have := hE.integrableOn one_pos hL
    simpa using this
  set F := fun z : ℂ => (E (L ^ (j + 1) * √(lamC z)) - E (L ^ j * √(lamC z))) / lamC z
  have hF : IntegrableOn F BZ := by
    have := lattice_integrableOn (h := fun y => E (L * y) - E y)
      (h' := fun y => L * E' (L * y) - E' y) (fun y hy => hasDerivAt_scale_diff hd hL0 hy)
      (fun y hy => hD.diff hα0 hL hy) hi hα hc
    simpa only [pow_succ_mul_eq] using this
  have hF2 : IntegrableOn (fun z => (1 - cos z.re) * F z) BZ :=
    Integrable.bdd_mul (c := 2) hF (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [cos_le_one z.re, neg_one_le_cos z.re])
  have hsplit : (∫ z in BZ, cos z.re * F z) = (∫ z in BZ, F z) - ∫ z in BZ, (1 - cos z.re) * F z := by
    rw [← integral_sub hF hF2]
    congr 1; funext z; ring
  have h1 := lattice_C hE hd hD hα hL j
  have h2 := lattice_cos (h := fun y => E (L * y) - E y) (K := 2 * K) (α := α)
    (fun y hy => by
      have := hD.diff hα0 hL hy
      linarith [abs_nonneg (y * (L * E' (L * y) - E' y))]) hα hc
  simp only [pow_succ_mul_eq] at h2
  rw [hsplit, mul_sub]
  have hp : (0 : ℝ) < (2 * π)⁻¹ ^ 2 := by have := pi_pos; positivity
  have h2' : |(2 * π)⁻¹ ^ 2 * ∫ z in BZ, (1 - cos z.re) * F z| ≤
      (2 * π)⁻¹ ^ 2 * (π ^ 4 / 32 * Ia α * (2 * K) / (L ^ j) ^ 2) := by
    rw [abs_mul, abs_of_pos hp]; gcongr
  calc _ = |((2 * π)⁻¹ ^ 2 * (∫ z in BZ, F z) - log L / (2 * π)) -
        (2 * π)⁻¹ ^ 2 * ∫ z in BZ, (1 - cos z.re) * F z| := by ring_nf
    _ ≤ _ := abs_sub _ _ |>.trans (by
        have e : (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2 + π ^ 4 / 32) * Ia α * (2 * K) /
            (L ^ j) ^ 2) = (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2) * Ia α * (2 * K) /
            (L ^ j) ^ 2) + (2 * π)⁻¹ ^ 2 * (π ^ 4 / 32 * Ia α * (2 * K) / (L ^ j) ^ 2) := by
          ring
        linarith)

end Profile

end

end Step2.D2
