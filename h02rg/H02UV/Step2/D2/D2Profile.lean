import Step2.D2.D2Torus
import FRD.PtPre

/-!
# The scaling profile of the concrete finite range decomposition (`prop:d2`, (R1))

For the concrete family `P_t = ∑_i a_i P⁰_{t/2^i}` (`FRD.PtF.prePt.toPtFamily`) the scaling
profile is
`H(z) = 1 - ∑_i ω_i Ψ₁(z/2^i)/c₀`, `ω_i = w_i/W`, `Ψ₁(z) = ∫_z^∞ r ψ(r) dr`,
and `E(y) = H(y/(4√2 π))`.

* `Psi1`, `hasDerivAt_Psi1`, `Psi1_eq_integral`, `Psi1_le`: the tail `Ψ₁` and its decay;
* `Hp`, `hasDerivAt_Hp`: the profile in the angle variable;
* `Hp_decay`, `Hp_profile`, `Phi_Hp_le`: `|1 - H| + |zH'| ≤ K (1+z)^{-3}`, `H` is a profile
  `0 → 1`, and `|H - zH'/2| ≤ M z⁴ (1+z)^{-4}`;
* `Ep`, `Ep_decayProfile`, `Ep_profile`, `Phi_Ep_le`: the same for `E(y) = H(y/κ)`,
  `κ = 4√2 π`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF
open scoped Nat

/-! ### Smoothness of `ψ` at the origin -/

/-- A bound for the second derivative of `Ψ`. -/
def M2 : ℝ := SchwartzMap.seminorm ℝ 0 0
  (SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ ΨS))

theorem deriv_ΨS_eq : deriv (ΨS : ℝ → ℂ) = SchwartzMap.derivCLM ℝ ℂ ΨS := by
  funext x; rw [SchwartzMap.derivCLM_apply]

theorem norm_deriv2_le (x : ℝ) : ‖deriv (deriv (ΨS : ℝ → ℂ)) x‖ ≤ M2 := by
  rw [deriv_ΨS_eq, ← SchwartzMap.derivCLM_apply ℝ]
  exact SchwartzMap.norm_le_seminorm ℝ _ x

theorem ΨS_neg (x : ℝ) : ΨS (-x) = ΨS x := by rw [ΨS_eq, ΨS_eq, ψ_neg]

theorem deriv_ΨS_zero : deriv (ΨS : ℝ → ℂ) 0 = 0 := by
  have h := deriv_comp_neg (ΨS : ℝ → ℂ) 0
  have e : (fun x => ΨS (-x)) = (ΨS : ℝ → ℂ) := funext ΨS_neg
  rw [e, neg_zero] at h
  have : (2 : ℂ) * deriv (ΨS : ℝ → ℂ) 0 = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
  simpa using this

theorem M2_nonneg : 0 ≤ M2 := (norm_nonneg _).trans (norm_deriv2_le 0)

theorem norm_deriv_ΨS_le (s : ℝ) : ‖deriv (ΨS : ℝ → ℂ) s‖ ≤ M2 * |s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := deriv (ΨS : ℝ → ℂ))
    (s := univ) (x := 0) (y := s) (C := M2)
    (fun x _ => by rw [deriv_ΨS_eq]; exact SchwartzMap.differentiableAt _)
    (fun x _ => norm_deriv2_le x) convex_univ (mem_univ _) (mem_univ _)
  rwa [deriv_ΨS_zero, sub_zero, sub_zero, Real.norm_eq_abs] at h

/-- `|ψ(r) - ψ(w)| ≤ M₂ w²` for `0 ≤ r ≤ w` (`ψ` is even and `C²`). -/
theorem abs_ψ_sub_le {r w : ℝ} (hr : 0 ≤ r) (hrw : r ≤ w) : |ψ r - ψ w| ≤ M2 * w ^ 2 := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := (ΨS : ℝ → ℂ))
    (s := Icc 0 w) (x := r) (y := w) (C := M2 * w)
    (fun x _ => SchwartzMap.differentiableAt _)
    (fun x hx => (norm_deriv_ΨS_le x).trans (by
      rw [abs_of_nonneg hx.1]; exact mul_le_mul_of_nonneg_left hx.2 M2_nonneg))
    (convex_Icc _ _) ⟨hr, hrw⟩ ⟨hr.trans hrw, le_rfl⟩
  rw [ΨS_eq, ΨS_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at h
  rw [abs_of_nonneg (sub_nonneg.2 hrw)] at h
  rw [abs_sub_comm]
  calc |ψ w - ψ r| ≤ M2 * w * (w - r) := h
    _ ≤ M2 * w * w := by
        have := M2_nonneg; have : 0 ≤ w := hr.trans hrw
        gcongr; linarith
    _ = M2 * w ^ 2 := by ring

/-! ### Bounds on `ψ` -/

theorem exists_ψ_bound : ∃ B, 0 ≤ B ∧ ∀ r, ψ r ≤ B := by
  obtain ⟨C, hC0, hC⟩ := ψ_decay' 0
  exact ⟨C, hC0, fun r => by simpa using hC r⟩

/-- `ψ₀ = sup ψ`. -/
def ψmax : ℝ := (exists_ψ_bound).choose

theorem ψmax_nonneg : 0 ≤ ψmax := (exists_ψ_bound).choose_spec.1

theorem ψ_le_ψmax (r : ℝ) : ψ r ≤ ψmax := (exists_ψ_bound).choose_spec.2 r

/-- `|r|^k ψ(r) ≤ C (1 + |r|)^{-M}`. -/
theorem ψ_pow_decay (k M : ℕ) : ∃ C, 0 ≤ C ∧ ∀ r, |r| ^ k * ψ r ≤ C / (1 + |r|) ^ M := by
  obtain ⟨C, hC0, hC⟩ := ψ_decay' (k + M)
  refine ⟨C, hC0, fun r => ?_⟩
  have h1 : |r| ^ k ≤ (1 + |r|) ^ k := by gcongr; linarith
  have hp : 0 < 1 + |r| := by positivity
  calc |r| ^ k * ψ r ≤ (1 + |r|) ^ k * (C / (1 + |r|) ^ (k + M)) :=
        mul_le_mul h1 (hC r) (ψ_nonneg r) (by positivity)
    _ = C / (1 + |r|) ^ M := by rw [pow_add]; field_simp

/-! ### The tail `Ψ₁(z) = ∫_z^∞ r ψ(r) dr` -/

theorem continuous_rψ : Continuous fun r : ℝ => r * ψ r := continuous_id.mul ψ_continuous

/-- `Ψ₁(z) = c₀ - ∫_0^z r ψ(r) dr`, which is `∫_z^∞ r ψ(r) dr` for `z ≥ 0`. -/
def Psi1 (z : ℝ) : ℝ := c0 - ∫ r in (0 : ℝ)..z, r * ψ r

theorem hasDerivAt_Psi1 (z : ℝ) : HasDerivAt Psi1 (-(z * ψ z)) z := by
  have := (continuous_rψ.integral_hasStrictDerivAt 0 z).hasDerivAt
  exact this.const_sub c0

theorem Psi1_zero : Psi1 0 = c0 := by simp [Psi1]

theorem Psi1_eq_integral {z : ℝ} (hz : 0 ≤ z) : Psi1 z = ∫ r in Ioi z, r * ψ r := by
  have h := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (integrableOn_c0.mono_set Ioc_subset_Ioi_self) (integrableOn_c0.mono_set (Ioi_subset_Ioi hz))
  rw [Ioc_union_Ioi_eq_Ioi hz] at h
  rw [Psi1, c0, h, intervalIntegral.integral_of_le hz]
  ring

theorem Psi1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Psi1 z := by
  rw [Psi1_eq_integral hz]
  refine setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
  exact mul_nonneg (hz.trans (le_of_lt hr)) (ψ_nonneg r)

theorem c0_sub_Psi1 (z : ℝ) : c0 - Psi1 z = ∫ r in (0 : ℝ)..z, r * ψ r := by
  rw [Psi1]; ring

theorem c0_sub_Psi1_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ c0 - Psi1 z := by
  rw [c0_sub_Psi1]
  exact intervalIntegral.integral_nonneg hz fun r hr => mul_nonneg hr.1 (ψ_nonneg r)

theorem c0_sub_Psi1_le {z : ℝ} (hz : 0 ≤ z) : c0 - Psi1 z ≤ ψmax * z ^ 2 / 2 := by
  rw [c0_sub_Psi1]
  have h : (∫ r in (0 : ℝ)..z, r * ψ r) ≤ ∫ r in (0 : ℝ)..z, ψmax * r :=
    intervalIntegral.integral_mono_on hz (continuous_rψ.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      fun r hr => by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (ψ_le_ψmax r) hr.1
  refine h.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

theorem Psi1_le_c0 {z : ℝ} (hz : 0 ≤ z) : Psi1 z ≤ c0 := by
  linarith [c0_sub_Psi1_nonneg hz]

theorem hasDerivAt_inv_cube {r : ℝ} (hr : 0 < 1 + r) :
    HasDerivAt (fun r : ℝ => -((1 + r) ^ 3)⁻¹ / 3) (((1 + r) ^ 4)⁻¹) r := by
  have h0 : HasDerivAt (fun x : ℝ => (1 + x) ^ 3) (3 * (1 + r) ^ 2) r := by
    have := (hasDerivAt_pow 3 (1 + r)).comp r ((hasDerivAt_id r).const_add 1)
    convert this using 1
    simp
  have h := h0.inv (by positivity : (1 + r) ^ 3 ≠ 0)
  convert (h.neg).div_const 3 using 1
  have : (1 + r) ^ 4 ≠ 0 := by positivity
  field_simp

theorem tendsto_inv_cube :
    Tendsto (fun r : ℝ => -((1 + r) ^ 3)⁻¹ / 3) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => (1 + r) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have := ((tendsto_inv_atTop_zero.comp h1).neg).div_const 3
  simpa using this

/-- `∫_z^∞ (1 + r)^{-4} dr = (1+z)^{-3}/3`. -/
theorem integral_Ioi_one_add_pow {z : ℝ} (hz : 0 ≤ z) :
    ∫ r in Ioi z, ((1 + r) ^ 4)⁻¹ = ((1 + z) ^ 3)⁻¹ / 3 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun r hr => hasDerivAt_inv_cube
    (by have : z ≤ r := hr; linarith)) (fun r hr => by
      have : z < r := hr; positivity) tendsto_inv_cube]
  ring

theorem integrableOn_Ioi_one_add_pow (z : ℝ) (hz : 0 ≤ z) :
    IntegrableOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Ioi z) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun r hr => hasDerivAt_inv_cube
    (by have : z ≤ r := hr; linarith)) (fun r hr => by
      have : z < r := hr; positivity) tendsto_inv_cube

/-- **Decay of `Ψ₁`.** `Ψ₁(z) ≤ C (1+z)^{-3}` for `z ≥ 0`. -/
theorem exists_Psi1_decay : ∃ C, 0 ≤ C ∧ ∀ z, 0 ≤ z → Psi1 z ≤ C * ((1 + z) ^ 3)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := ψ_pow_decay 1 4
  refine ⟨C / 3, by positivity, fun z hz => ?_⟩
  rw [Psi1_eq_integral hz]
  have hb : ∀ r ∈ Ioi z, r * ψ r ≤ C * ((1 + r) ^ 4)⁻¹ := by
    intro r hr
    have hr0 : 0 ≤ r := hz.trans (le_of_lt hr)
    have := hC r
    rw [abs_of_nonneg hr0, pow_one] at this
    rwa [← div_eq_mul_inv]
  calc (∫ r in Ioi z, r * ψ r) ≤ ∫ r in Ioi z, C * ((1 + r) ^ 4)⁻¹ :=
        setIntegral_mono_on (integrableOn_c0.mono_set (Ioi_subset_Ioi hz))
          ((integrableOn_Ioi_one_add_pow z hz).const_mul C) measurableSet_Ioi hb
    _ = C / 3 * ((1 + z) ^ 3)⁻¹ := by
        rw [integral_const_mul, integral_Ioi_one_add_pow hz]; ring

/-- A fixed constant for the decay of `Ψ₁`. -/
def CΨ : ℝ := exists_Psi1_decay.choose

theorem CΨ_nonneg : 0 ≤ CΨ := exists_Psi1_decay.choose_spec.1

theorem Psi1_le {z : ℝ} (hz : 0 ≤ z) : Psi1 z ≤ CΨ * ((1 + z) ^ 3)⁻¹ :=
  exists_Psi1_decay.choose_spec.2 z hz

/-! ### The weights `ω_i = w_i / W` -/

/-- `ω_i = 1/(W i!)`, with `∑ ω_i = 1`. -/
def om (i : ℕ) : ℝ := PrePtFamily.w i / PrePtFamily.W

theorem om_pos (i : ℕ) : 0 < om i := div_pos (PrePtFamily.w_pos i) PrePtFamily.W_pos

theorem summable_om_pow (r : ℝ) : Summable fun i : ℕ => om i * r ^ i := by
  have : (fun i : ℕ => om i * r ^ i) = fun i => (r ^ i / i !) / PrePtFamily.W := by
    funext i; simp only [om, PrePtFamily.w]; ring
  rw [this]
  exact (Real.summable_pow_div_factorial r).div_const _

theorem summable_om : Summable om := by simpa using summable_om_pow 1

theorem tsum_om : ∑' i, om i = 1 := by
  simp only [om]
  rw [tsum_div_const]
  exact div_self PrePtFamily.W_pos.ne'

/-- `S_r = ∑ ω_i r^i`. -/
def Som (r : ℝ) : ℝ := ∑' i, om i * r ^ i

theorem Som_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Som r :=
  tsum_nonneg fun i => mul_nonneg (om_pos i).le (pow_nonneg hr i)

/-- A series `∑ ω_i f_i` with `|f_i| ≤ A r^i` converges and is bounded by `A S_r`. -/
theorem tsum_om_le {f : ℕ → ℝ} {A r : ℝ} (hr : 0 ≤ r) (hf : ∀ i, |f i| ≤ A * r ^ i) :
    Summable (fun i => om i * f i) ∧ |∑' i, om i * f i| ≤ A * Som r := by
  have hs : Summable fun i => |om i * f i| := by
    refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_)
      ((summable_om_pow r).mul_left A)
    rw [abs_mul, abs_of_pos (om_pos i)]
    calc om i * |f i| ≤ om i * (A * r ^ i) := mul_le_mul_of_nonneg_left (hf i) (om_pos i).le
      _ = A * (om i * r ^ i) := by ring
  have hs' : Summable fun i => om i * f i := hs.of_abs
  refine ⟨hs', ?_⟩
  refine (show |∑' i, om i * f i| ≤ ∑' i, |om i * f i| by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun i => om i * f i)
      (by simpa only [Real.norm_eq_abs] using hs)).trans ?_
  rw [Som, ← tsum_mul_left]
  refine hs.tsum_le_tsum (fun i => ?_) ((summable_om_pow r).mul_left A)
  rw [abs_mul, abs_of_pos (om_pos i)]
  calc om i * |f i| ≤ om i * (A * r ^ i) := mul_le_mul_of_nonneg_left (hf i) (om_pos i).le
    _ = A * (om i * r ^ i) := by ring

/-! ### The profile in the angle variable -/

/-- `H(z) = 1 - ∑_i ω_i Ψ₁(z/2^i)/c₀`. -/
def Hp (z : ℝ) : ℝ := 1 - ∑' i, om i * (Psi1 (z / 2 ^ i) / c0)

/-- `H'(z) = ∑_i ω_i (z/2^i) ψ(z/2^i) / (2^i c₀)`. -/
def Hp' (z : ℝ) : ℝ := ∑' i, om i * (z / 2 ^ i * ψ (z / 2 ^ i) / (2 ^ i * c0))

theorem exists_rψ_bound : ∃ B, 0 ≤ B ∧ ∀ r, |r * ψ r| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := ψ_pow_decay 1 0
  refine ⟨C, hC0, fun r => ?_⟩
  rw [abs_mul, abs_of_nonneg (ψ_nonneg r)]
  simpa using hC r

theorem hasDerivAt_Hp (z : ℝ) : HasDerivAt Hp (Hp' z) z := by
  obtain ⟨B, hB0, hB⟩ := exists_rψ_bound
  have hc0 := c0_pos
  set g : ℕ → ℝ → ℝ := fun i y => om i * (Psi1 (y / 2 ^ i) / c0)
  set g' : ℕ → ℝ → ℝ := fun i y => om i * (-(y / 2 ^ i * ψ (y / 2 ^ i)) / (2 ^ i * c0))
  have hg : ∀ i y, HasDerivAt (g i) (g' i y) y := by
    intro i y
    have h1 := (hasDerivAt_Psi1 (y / 2 ^ i)).comp y ((hasDerivAt_id y).div_const (2 ^ i))
    have h2 := (h1.div_const c0).const_mul (om i)
    convert h2 using 1
    simp only [g']
    field_simp
  have hg' : ∀ i y, ‖g' i y‖ ≤ om i * (B / c0) := by
    intro i y
    have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    simp only [g', Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (om_pos i), abs_div, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i * c0)]
    refine mul_le_mul_of_nonneg_left ?_ (om_pos i).le
    calc |y / 2 ^ i * ψ (y / 2 ^ i)| / (2 ^ i * c0) ≤ B / (2 ^ i * c0) := by
          gcongr; exact hB _
      _ ≤ B / (1 * c0) := by gcongr
      _ = B / c0 := by rw [one_mul]
  have hs0 : Summable fun i => g i 0 := by
    simp only [g, zero_div, Psi1_zero, div_self hc0.ne', mul_one]
    exact summable_om
  have hsum : Summable fun i => om i * (B / c0) := summable_om.mul_right _
  have h := hasDerivAt_tsum hsum hg hg' hs0 z
  have e : Hp' z = -∑' i, g' i z := by
    rw [Hp', ← tsum_neg]
    congr 1; funext i; simp only [g']; ring
  rw [e]
  exact h.const_sub 1

/-- `1 - H(z) = ∑ ω_i Ψ₁(z/2^i)/c₀`. -/
theorem one_sub_Hp (z : ℝ) : 1 - Hp z = ∑' i, om i * (Psi1 (z / 2 ^ i) / c0) := by
  rw [Hp]; ring

/-- `(1 + z/2^i)^{-k} ≤ (2^k)^i (1+z)^{-k}`. -/
theorem inv_one_add_div_pow_le {z : ℝ} (hz : 0 ≤ z) (i k : ℕ) :
    ((1 + z / 2 ^ i) ^ k)⁻¹ ≤ (2 ^ k) ^ i * ((1 + z) ^ k)⁻¹ := by
  have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have h1 : 1 + z ≤ 2 ^ i * (1 + z / 2 ^ i) := by
    rw [mul_add, mul_div_cancel₀ _ (by positivity), mul_one]; linarith
  have h3 : (1 + z) ^ k ≤ (2 ^ k) ^ i * (1 + z / 2 ^ i) ^ k := by
    rw [← pow_mul, mul_comm k i, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 k
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
    div_le_iff₀ (by positivity)]
  linarith [h3]

theorem one_sub_Hp_le {z : ℝ} (hz : 0 ≤ z) :
    |1 - Hp z| ≤ CΨ / c0 * Som 8 * ((1 + z) ^ 3)⁻¹ := by
  have hc0 := c0_pos
  rw [one_sub_Hp]
  have := (tsum_om_le (f := fun i => Psi1 (z / 2 ^ i) / c0) (A := CΨ / c0 * ((1 + z) ^ 3)⁻¹)
    (r := 8) (by norm_num) (fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      rw [abs_div, abs_of_nonneg (Psi1_nonneg hz'), abs_of_pos hc0]
      have h1 := Psi1_le hz'
      have h2 := inv_one_add_div_pow_le hz i 3
      norm_num at h2
      calc Psi1 (z / 2 ^ i) / c0 ≤ CΨ * ((1 + z / 2 ^ i) ^ 3)⁻¹ / c0 := by gcongr
        _ ≤ CΨ * (8 ^ i * ((1 + z) ^ 3)⁻¹) / c0 := by
            gcongr; exact CΨ_nonneg
        _ = CΨ / c0 * ((1 + z) ^ 3)⁻¹ * 8 ^ i := by ring)).2
  calc _ ≤ CΨ / c0 * ((1 + z) ^ 3)⁻¹ * Som 8 := this
    _ = _ := by ring

theorem z_Hp' (z : ℝ) : z * Hp' z = ∑' i, om i * ((z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0) := by
  rw [Hp', ← tsum_mul_left]
  congr 1; funext i
  have : (2 : ℝ) ^ i ≠ 0 := by positivity
  have := c0_pos.ne'
  field_simp

/-- A fixed constant with `r² ψ(r) ≤ C₂ (1 + |r|)^{-3}`. -/
def Cψ2 : ℝ := (ψ_pow_decay 2 3).choose

theorem Cψ2_nonneg : 0 ≤ Cψ2 := (ψ_pow_decay 2 3).choose_spec.1

theorem sq_ψ_le (r : ℝ) : r ^ 2 * ψ r ≤ Cψ2 * ((1 + |r|) ^ 3)⁻¹ := by
  have := (ψ_pow_decay 2 3).choose_spec.2 r
  rw [sq_abs] at this
  rwa [← div_eq_mul_inv]

theorem z_Hp'_le {z : ℝ} (hz : 0 ≤ z) :
    |z * Hp' z| ≤ Cψ2 / c0 * Som 8 * ((1 + z) ^ 3)⁻¹ := by
  have hc0 := c0_pos
  rw [z_Hp']
  have := (tsum_om_le (f := fun i => (z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0)
    (A := Cψ2 / c0 * ((1 + z) ^ 3)⁻¹) (r := 8) (by norm_num) (fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      rw [abs_div, abs_of_nonneg (by have := ψ_nonneg (z / 2 ^ i); positivity), abs_of_pos hc0]
      have h1 := sq_ψ_le (z / 2 ^ i)
      rw [abs_of_nonneg hz'] at h1
      have h2 := inv_one_add_div_pow_le hz i 3
      norm_num at h2
      calc (z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0 ≤ Cψ2 * ((1 + z / 2 ^ i) ^ 3)⁻¹ / c0 := by gcongr
        _ ≤ Cψ2 * (8 ^ i * ((1 + z) ^ 3)⁻¹) / c0 := by
            gcongr; exact Cψ2_nonneg
        _ = Cψ2 / c0 * ((1 + z) ^ 3)⁻¹ * 8 ^ i := by ring)).2
  calc _ ≤ Cψ2 / c0 * ((1 + z) ^ 3)⁻¹ * Som 8 := this
    _ = _ := by ring

theorem summable_om_Psi1 {z : ℝ} (hz : 0 ≤ z) : Summable fun i => om i * (Psi1 (z / 2 ^ i) / c0) := by
  have hc0 := c0_pos
  refine (tsum_om_le (A := 1) (r := 1) zero_le_one fun i => ?_).1
  have hz' : 0 ≤ z / 2 ^ i := by positivity
  rw [abs_div, abs_of_nonneg (Psi1_nonneg hz'), abs_of_pos hc0, one_pow, mul_one,
    div_le_one hc0]
  exact Psi1_le_c0 hz'

theorem Som_one : Som 1 = 1 := by simp [Som, tsum_om]

theorem Hp_eq {z : ℝ} (hz : 0 ≤ z) : Hp z = ∑' i, om i * ((c0 - Psi1 (z / 2 ^ i)) / c0) := by
  have hc0 := c0_pos
  have e : ∀ i, om i * ((c0 - Psi1 (z / 2 ^ i)) / c0) = om i - om i * (Psi1 (z / 2 ^ i) / c0) := by
    intro i; field_simp
  simp_rw [e]
  rw [Summable.tsum_sub summable_om (summable_om_Psi1 hz), tsum_om, Hp]

theorem abs_Hp_le_sq {z : ℝ} (hz : 0 ≤ z) : |Hp z| ≤ ψmax / (2 * c0) * z ^ 2 := by
  have hc0 := c0_pos
  rw [Hp_eq hz]
  have h := (tsum_om_le (f := fun i => (c0 - Psi1 (z / 2 ^ i)) / c0)
    (A := ψmax / (2 * c0) * z ^ 2) (r := 1) zero_le_one fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      have h2 : z / 2 ^ i ≤ z := div_le_self hz (one_le_pow₀ (by norm_num))
      rw [abs_div, abs_of_nonneg (c0_sub_Psi1_nonneg hz'), abs_of_pos hc0, one_pow, mul_one]
      have := c0_sub_Psi1_le hz'
      have := ψmax_nonneg
      calc (c0 - Psi1 (z / 2 ^ i)) / c0 ≤ ψmax * (z / 2 ^ i) ^ 2 / 2 / c0 := by gcongr
        _ ≤ ψmax * z ^ 2 / 2 / c0 := by gcongr
        _ = ψmax / (2 * c0) * z ^ 2 := by field_simp).2
  rwa [Som_one, mul_one] at h

/-- The decay constant of `H`. -/
def KH : ℝ := CΨ / c0 * Som 8 + Cψ2 / c0 * Som 8

theorem KH_nonneg : 0 ≤ KH := by
  have := c0_pos; have := CΨ_nonneg; have := Cψ2_nonneg; have := Som_nonneg (r := 8) (by norm_num)
  unfold KH; positivity

theorem one_add_rpow_neg_three {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ (-(3 : ℝ)) = ((1 + y) ^ 3)⁻¹ := by
  rw [Real.rpow_neg (by linarith)]; norm_cast

/-- **`H` is a decay profile**: `|1 - H(z)| + |z H'(z)| ≤ K_H (1+z)^{-3}`. -/
theorem Hp_decay : DecayProfile Hp Hp' KH 3 := by
  intro y hy
  have h1 := one_sub_Hp_le hy.le
  have h2 := z_Hp'_le hy.le
  rw [one_add_rpow_neg_three hy.le, KH]
  linarith

/-! ### The bound on `Φ_H = H - zH'/2` -/

/-- The single-scale term of `Φ_H`. -/
def bterm (w : ℝ) : ℝ := (c0 - Psi1 w) / c0 - w ^ 2 * ψ w / (2 * c0)

theorem abs_bterm_le_pow {w : ℝ} (hw : 0 ≤ w) : |bterm w| ≤ M2 / (2 * c0) * w ^ 4 := by
  have hc0 := c0_pos
  have e : bterm w = (∫ r in (0 : ℝ)..w, (r * ψ r - ψ w * r)) / c0 := by
    rw [intervalIntegral.integral_sub (f := fun r => r * ψ r) (g := fun r => ψ w * r)
      (continuous_rψ.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, ← c0_sub_Psi1, bterm]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hc0]
  have h1 := intervalIntegral.abs_integral_le_integral_abs (f := fun r => r * ψ r - ψ w * r)
    (μ := volume) hw
  have h2 : (∫ r in (0 : ℝ)..w, |r * ψ r - ψ w * r|) ≤ ∫ r in (0 : ℝ)..w, M2 * w ^ 2 * r :=
    intervalIntegral.integral_mono_on hw
      ((continuous_rψ.sub (continuous_const.mul continuous_id)).abs.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _) fun r hr => by
        rw [show r * ψ r - ψ w * r = r * (ψ r - ψ w) by ring, abs_mul, abs_of_nonneg hr.1,
          mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_ψ_sub_le hr.1 hr.2) hr.1
  rw [intervalIntegral.integral_const_mul, integral_id] at h2
  rw [div_le_iff₀ hc0]
  calc _ ≤ _ := h1.trans h2
    _ = M2 / (2 * c0) * w ^ 4 * c0 := by field_simp; ring

theorem abs_bterm_le_const {w : ℝ} (hw : 0 ≤ w) : |bterm w| ≤ 1 + Cψ2 / (2 * c0) := by
  have hc0 := c0_pos
  have h1 : 0 ≤ (c0 - Psi1 w) / c0 := div_nonneg (c0_sub_Psi1_nonneg hw) hc0.le
  have h2 : (c0 - Psi1 w) / c0 ≤ 1 := by
    rw [div_le_one hc0]; linarith [Psi1_nonneg hw]
  have h3 : 0 ≤ w ^ 2 * ψ w / (2 * c0) := by have := ψ_nonneg w; positivity
  have h4 : w ^ 2 * ψ w ≤ Cψ2 := by
    have := sq_ψ_le w
    have h5 : ((1 + |w|) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by
      linarith [abs_nonneg w]))
    have := Cψ2_nonneg
    nlinarith
  have h6 : w ^ 2 * ψ w / (2 * c0) ≤ Cψ2 / (2 * c0) := by gcongr
  rw [bterm, abs_le]; constructor <;> linarith

/-- The constant `M_Φ`. -/
def MPhi : ℝ := 16 * (M2 / (2 * c0) + (1 + Cψ2 / (2 * c0)))

theorem MPhi_nonneg : 0 ≤ MPhi := by
  have := c0_pos; have := M2_nonneg; have := Cψ2_nonneg; unfold MPhi; positivity

theorem abs_bterm_le {w : ℝ} (hw : 0 ≤ w) : |bterm w| ≤ MPhi * (w / (1 + w)) ^ 4 := by
  have hc0 := c0_pos
  have hA : 0 ≤ M2 / (2 * c0) := by have := M2_nonneg; positivity
  have hB : 0 ≤ 1 + Cψ2 / (2 * c0) := by have := Cψ2_nonneg; positivity
  have hp : 0 < 1 + w := by linarith
  rcases le_total w 1 with h | h
  · have e1 : w ^ 4 ≤ 16 * (w / (1 + w)) ^ 4 := by
      rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
      have : (1 + w) ^ 4 ≤ 16 := by
        calc (1 + w) ^ 4 ≤ 2 ^ 4 := by gcongr; linarith
          _ = 16 := by norm_num
      nlinarith [pow_nonneg hw 4]
    calc |bterm w| ≤ M2 / (2 * c0) * w ^ 4 := abs_bterm_le_pow hw
      _ ≤ M2 / (2 * c0) * (16 * (w / (1 + w)) ^ 4) := by gcongr
      _ ≤ MPhi * (w / (1 + w)) ^ 4 := by
          unfold MPhi
          have := pow_nonneg (div_nonneg hw hp.le) 4
          nlinarith
  · have e1 : 1 / 16 ≤ (w / (1 + w)) ^ 4 := by
      have : 1 / 2 ≤ w / (1 + w) := by rw [le_div_iff₀ hp]; linarith
      calc (1 : ℝ) / 16 = (1 / 2) ^ 4 := by norm_num
        _ ≤ _ := by gcongr
    calc |bterm w| ≤ 1 + Cψ2 / (2 * c0) := abs_bterm_le_const hw
      _ ≤ MPhi * (w / (1 + w)) ^ 4 := by
          unfold MPhi
          nlinarith

theorem div_one_add_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a / (1 + a) ≤ b / (1 + b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem Phi_Hp_eq {z : ℝ} (hz : 0 ≤ z) : Phi Hp Hp' z = ∑' i, om i * bterm (z / 2 ^ i) := by
  have hc0 := c0_pos
  have s1 : Summable fun i => om i * ((c0 - Psi1 (z / 2 ^ i)) / c0) := by
    refine (tsum_om_le (A := 1) (r := 1) zero_le_one fun i => ?_).1
    have hz' : 0 ≤ z / 2 ^ i := by positivity
    rw [abs_div, abs_of_nonneg (c0_sub_Psi1_nonneg hz'), abs_of_pos hc0, one_pow, mul_one,
      div_le_one hc0]
    linarith [Psi1_nonneg hz']
  have s2 : Summable fun i => om i * ((z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0) := by
    refine (tsum_om_le (A := Cψ2 / c0) (r := 1) zero_le_one fun i => ?_).1
    rw [abs_of_nonneg (by have := ψ_nonneg (z / 2 ^ i); positivity), one_pow, mul_one]
    have h := sq_ψ_le (z / 2 ^ i)
    have h5 : ((1 + |z / 2 ^ i|) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by
      linarith [abs_nonneg (z / 2 ^ i)]))
    have := Cψ2_nonneg
    have : (z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) ≤ Cψ2 := by nlinarith
    gcongr
  show Hp z - z * Hp' z / 2 = _
  rw [Hp_eq hz, z_Hp']
  have e : ∀ i, om i * bterm (z / 2 ^ i) = om i * ((c0 - Psi1 (z / 2 ^ i)) / c0) -
      (om i * ((z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0)) / 2 := by
    intro i; simp only [bterm]; field_simp
  simp_rw [e]
  rw [Summable.tsum_sub s1 (s2.div_const 2), tsum_div_const]

/-- **`Φ_H(z) = O(z⁴)` at `0`.** `|H(z) - zH'(z)/2| ≤ M_Φ z⁴ (1+z)^{-4}`. -/
theorem Phi_Hp_le {z : ℝ} (hz : 0 ≤ z) : |Phi Hp Hp' z| ≤ MPhi * z ^ 4 * (1 + z) ^ (-(4 : ℝ)) := by
  rw [Phi_Hp_eq hz]
  have h := (tsum_om_le (f := fun i => bterm (z / 2 ^ i)) (A := MPhi * (z / (1 + z)) ^ 4)
    (r := 1) zero_le_one fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      have h2 : z / 2 ^ i ≤ z := div_le_self hz (one_le_pow₀ (by norm_num))
      rw [one_pow, mul_one]
      refine (abs_bterm_le hz').trans ?_
      have := MPhi_nonneg
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hz' (by linarith))
        (div_one_add_mono hz' h2) 4) MPhi_nonneg).2
  rw [Som_one, mul_one] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.rpow_neg (by linarith), div_pow]
  norm_cast
  ring

/-! ### The profile `E(y) = H(y/κ)`, `κ = 4√2 π` -/

/-- `κ = 4√2 π`: `T x = L^j ρ/κ` for `T = L^j/2` and `ρ = 2√2 π x`. -/
def kap : ℝ := 4 * √2 * π

theorem kap_pos : 0 < kap := by unfold kap; positivity

theorem one_le_kap : 1 ≤ kap := by
  unfold kap
  have h1 : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  have h2 := pi_gt_three
  nlinarith

/-- The scaling profile `E(y) = H(y/κ)` of `prop:d2`. -/
def Ep (y : ℝ) : ℝ := Hp (y / kap)

/-- `E'(y) = H'(y/κ)/κ`. -/
def Ep' (y : ℝ) : ℝ := Hp' (y / kap) / kap

theorem hasDerivAt_Ep (y : ℝ) : HasDerivAt Ep (Ep' y) y := by
  have := (hasDerivAt_Hp (y / kap)).comp y ((hasDerivAt_id y).div_const kap)
  simp only [id, one_div] at this
  convert this using 1

theorem one_add_div_kap_rpow_le {y α : ℝ} (hy : 0 ≤ y) (hα : 0 ≤ α) :
    (1 + y / kap) ^ (-α) ≤ kap ^ α * (1 + y) ^ (-α) := by
  have hk := kap_pos
  have h1 : (1 + y) / kap ≤ 1 + y / kap := by
    rw [add_div]; gcongr; rw [div_le_one hk]; exact one_le_kap
  calc (1 + y / kap) ^ (-α) ≤ ((1 + y) / kap) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    _ = kap ^ α * (1 + y) ^ (-α) := by
        rw [Real.div_rpow (by linarith) hk.le, Real.rpow_neg hk.le, div_inv_eq_mul, mul_comm]

/-- **`E` is a decay profile** with constant `K_H κ³` and exponent `3`. -/
theorem Ep_decay : DecayProfile Ep Ep' (KH * kap ^ (3 : ℝ)) 3 := by
  intro y hy
  have hk := kap_pos
  have h := Hp_decay (y / kap) (by positivity)
  have e : y * Ep' y = y / kap * Hp' (y / kap) := by rw [Ep']; ring
  rw [Ep, e]
  refine h.trans ?_
  have := one_add_div_kap_rpow_le hy.le (α := 3) (by norm_num)
  have := KH_nonneg
  calc KH * (1 + y / kap) ^ (-(3 : ℝ)) ≤ KH * (kap ^ (3 : ℝ) * (1 + y) ^ (-(3 : ℝ))) := by
        gcongr
    _ = _ := by ring

theorem abs_Ep_le_sq {y : ℝ} (hy : 0 ≤ y) : |Ep y| ≤ ψmax / (2 * c0) * y ^ 2 := by
  have hk := kap_pos
  refine (abs_Hp_le_sq (by positivity)).trans ?_
  have : (y / kap) ^ 2 ≤ y ^ 2 := by
    rw [div_pow]; exact div_le_self (sq_nonneg y) (one_le_pow₀ one_le_kap)
  have := ψmax_nonneg; have := c0_pos
  gcongr

theorem one_sub_Ep_le {y : ℝ} (hy : 0 ≤ y) :
    |1 - Ep y| ≤ CΨ / c0 * Som 8 * kap ^ 3 * ((1 + y) ^ 3)⁻¹ := by
  have hk := kap_pos
  refine (one_sub_Hp_le (by positivity)).trans ?_
  have h := one_add_div_kap_rpow_le hy (α := 3) (by norm_num)
  rw [one_add_rpow_neg_three (by positivity), one_add_rpow_neg_three hy] at h
  have hA : 0 ≤ CΨ / c0 * Som 8 := by
    have := CΨ_nonneg; have := Som_nonneg (r := 8) (by norm_num); have := c0_pos; positivity
  norm_cast at h
  calc CΨ / c0 * Som 8 * ((1 + y / kap) ^ 3)⁻¹ ≤ CΨ / c0 * Som 8 * (kap ^ 3 * ((1 + y) ^ 3)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- **`E` is a profile `0 → 1`.** -/
theorem Ep_profile : Profile Ep 0 1 where
  cont := fun y _ => (hasDerivAt_Ep y).continuousAt.continuousWithinAt
  bound := by
    have hc0 := c0_pos
    set A := CΨ / c0 * Som 8 * kap ^ 3
    have hA : 0 ≤ A := by
      have := CΨ_nonneg; have := Som_nonneg (r := 8) (by norm_num); have := kap_pos; positivity
    have hB : 0 ≤ ψmax / (2 * c0) := by have := ψmax_nonneg; positivity
    refine ⟨1 + A + ψmax / (2 * c0), 2, two_pos, fun y hy => ⟨?_, fun hy1 => ?_,
      fun hy1 => ?_⟩⟩
    · have h1 := one_sub_Ep_le hy.le
      have h3 : ((1 + y) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
      have h4 : A * ((1 + y) ^ 3)⁻¹ ≤ A := mul_le_of_le_one_right hA h3
      have := abs_sub (1 : ℝ) (1 - Ep y)
      rw [show (1 : ℝ) - (1 - Ep y) = Ep y by ring, abs_one] at this
      linarith
    · rw [sub_zero]
      refine (abs_Ep_le_sq hy.le).trans ?_
      rw [show (y : ℝ) ^ (2 : ℝ) = y ^ 2 by norm_cast]
      have : 0 ≤ y ^ 2 := sq_nonneg y
      nlinarith
    · rw [abs_sub_comm]
      refine (one_sub_Ep_le hy.le).trans ?_
      have h5 : ((1 + y) ^ 3)⁻¹ ≤ y ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hy.le, show (y : ℝ) ^ (2 : ℝ) = y ^ 2 by norm_cast]
        gcongr
        nlinarith
      have h6 : 0 ≤ y ^ (-(2 : ℝ)) := by positivity
      calc A * ((1 + y) ^ 3)⁻¹ ≤ A * y ^ (-(2 : ℝ)) := by gcongr
        _ ≤ _ := by nlinarith

/-- **`Φ_E(y) = O(y⁴)`**: `|E(y) - yE'(y)/2| ≤ M_Φ y⁴ (1+y)^{-4}`. -/
theorem Phi_Ep_le {y : ℝ} (hy : 0 ≤ y) : |Phi Ep Ep' y| ≤ MPhi * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := by
  have hk := kap_pos
  have e : Phi Ep Ep' y = Phi Hp Hp' (y / kap) := by
    simp only [Phi, Ep, Ep']; ring
  rw [e]
  refine (Phi_Hp_le (by positivity)).trans ?_
  have h := one_add_div_kap_rpow_le hy (α := 4) (by norm_num)
  have e2 : (y / kap) ^ 4 = y ^ 4 / kap ^ (4 : ℝ) := by
    rw [div_pow]; norm_cast
  rw [e2]
  have := MPhi_nonneg
  have hk4 : 0 < kap ^ (4 : ℝ) := by positivity
  calc MPhi * (y ^ 4 / kap ^ (4 : ℝ)) * (1 + y / kap) ^ (-(4 : ℝ))
      ≤ MPhi * (y ^ 4 / kap ^ (4 : ℝ)) * (kap ^ (4 : ℝ) * (1 + y) ^ (-(4 : ℝ))) := by gcongr
    _ = MPhi * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := by field_simp

end

end Step2.D2
