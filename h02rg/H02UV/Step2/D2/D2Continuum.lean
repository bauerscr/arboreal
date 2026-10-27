import Step2.D2.D2Frullani

/-!
# The continuum values of `prop:d2`

In the continuum approximation of Proposition `prop:d2` (`⨍ dp → ∫ d²p/(2π)²`, `λ(p) → |p|²`,
`ê_j(p) → E(L^j|p|)`), the three quantities of the proposition are Frullani integrals. We take
`ℝ² = ℂ`.

* `integral_radial`: `∫_{ℝ²} f(|p|) d²p = 2π ∫_0^∞ y f(y) dy`;
* `Profile.continuum`, `Profile.continuum_scale`: for a profile `h` (`D2Frullani`),
  `(2π)^{-2} ∫_{ℝ²} (h(L^{j+1}|p|) - h(L^j|p|)) |p|^{-2} d²p = (h∞ - h₀) log L / (2π)`;
* `continuum_C`: the value of `C_{j+1}(0,0)`, symbol `(E_{j+1} - E_j)/|p|²`;
* `continuum_l`: the value of `𝔩(w_{j+1}) - 𝔩(w_j)`, `𝔩(w) = ∫ |p|² ŵ²`, `ŵ_j = E_j/|p|²`;
* `Profile.phi`: `Φ = E - yE'/2` is a profile `0 → 1` if `E` is and `yE'(y)` decays at a power
  rate at `0` and `∞`;
* `bubble_ibp`: for `f_c(s) = E(c√s)/s` and `Φ(y) = E(y) - y E'(y)/2`, the integration by parts
  `-∫_ε^R f_c (s³ f_c')' ds = [E Φ](c√R) - [E Φ](c√ε) + ∫_ε^R Φ(c√s)² ds/s`;
* `bubble_frullani`, `continuum_B`: the bubble difference
  `(4π)^{-1} ∫_0^∞ (-f_{L^{j+1}}(s³f'_{L^{j+1}})' + f_{L^j}(s³f'_{L^j})') ds = log L/(2π)`
  (as a limit of truncations `∫_{1/(n+1)}^{n+1}`: the individual terms are not integrable).
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real intervalIntegral

/-! ### Radial integrals in two dimensions -/

/-- `∫_{ℝ²} f(|p|) d²p = 2π ∫_0^∞ y f(y) dy`. -/
theorem integral_radial (f : ℝ → ℝ) : ∫ z : ℂ, f ‖z‖ = 2 * π * ∫ y in Ioi 0, y * f y := by
  rw [integral_fun_norm_addHaar volume f]
  simp [Complex.finrank_real_complex, Measure.real]
  ring

/-- **Continuum Frullani in `d = 2`.** -/
theorem Profile.continuum {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (2 * π)⁻¹ ^ 2 * ∫ z : ℂ, (h (b * ‖z‖) - h (a * ‖z‖)) / ‖z‖ ^ 2 =
      (hinf - h0) * log (b / a) / (2 * π) := by
  rw [integral_radial (fun y => (h (b * y) - h (a * y)) / y ^ 2)]
  have : ∫ y in Ioi 0, y * ((h (b * y) - h (a * y)) / y ^ 2) =
      ∫ y in Ioi 0, (h (b * y) - h (a * y)) / y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
    field_simp
  rw [this, hp.frullani ha hab]
  field_simp

theorem log_pow_succ_div {L : ℝ} (hL : 0 < L) (j : ℕ) : log (L ^ (j + 1) / L ^ j) = log L := by
  rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ hL.ne')]

/-- **Continuum Frullani at scales `L^j`, `L^{j+1}`.** -/
theorem Profile.continuum_scale {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) {L : ℝ}
    (hL : 1 ≤ L) (j : ℕ) :
    (2 * π)⁻¹ ^ 2 * ∫ z : ℂ, (h (L ^ (j + 1) * ‖z‖) - h (L ^ j * ‖z‖)) / ‖z‖ ^ 2 =
      (hinf - h0) * log L / (2 * π) := by
  rw [hp.continuum (by positivity) (pow_le_pow_right₀ hL (Nat.le_succ j)),
    log_pow_succ_div (by linarith)]

/-- **`C_{j+1}(0,0)` in the continuum.** With `Ĉ_{j+1}(p) = (E(L^{j+1}|p|) - E(L^j|p|))/|p|²`,
`∫ d²p/(2π)² Ĉ_{j+1}(p) = (1/2π) log L`. -/
theorem continuum_C {E : ℝ → ℝ} (hE : Profile E 0 1) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    (2 * π)⁻¹ ^ 2 * ∫ z : ℂ, (E (L ^ (j + 1) * ‖z‖) - E (L ^ j * ‖z‖)) / ‖z‖ ^ 2 =
      log L / (2 * π) := by
  rw [hE.continuum_scale hL j]; ring

/-- **`𝔩(w_{j+1}) - 𝔩(w_j)` in the continuum.** With `ŵ_j(p) = E(L^j|p|)/|p|²` and
`𝔩(w) = ∫ d²p/(2π)² |p|² ŵ(p)²`, the difference is `(1/2π) log L`. -/
theorem continuum_l {E : ℝ → ℝ} (hE : Profile E 0 1) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    (2 * π)⁻¹ ^ 2 * ∫ z : ℂ, ‖z‖ ^ 2 * ((E (L ^ (j + 1) * ‖z‖) / ‖z‖ ^ 2) ^ 2 -
      (E (L ^ j * ‖z‖) / ‖z‖ ^ 2) ^ 2) = log L / (2 * π) := by
  have h2 := (hE.mul hE).continuum_scale hL j
  rw [show (1 : ℝ) * 1 - 0 * 0 = 1 by norm_num, one_mul] at h2
  rw [← h2]
  congr 2
  funext z
  rcases eq_or_ne ‖z‖ 0 with hz | hz
  · simp [hz]
  · field_simp

/-! ### The bubble: integration by parts -/

variable {E E' Φ' : ℝ → ℝ}

/-- `f_c(s) = E(c√s)/s`, the continuum symbol `ŵ` at scale `c = L^j` in the variable `s = |p|²`. -/
def fc (E : ℝ → ℝ) (c s : ℝ) : ℝ := E (c * √s) / s

/-- `Φ(y) = E(y) - y E'(y)/2`. -/
def Phi (E E' : ℝ → ℝ) (y : ℝ) : ℝ := E y - y * E' y / 2

theorem hasDerivAt_mul_sqrt {c s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => c * √s) (c * (1 / (2 * √s))) s :=
  (Real.hasDerivAt_sqrt hs.ne').const_mul c

theorem one_div_two_sqrt_mul_self {s : ℝ} (hs : 0 < s) : 1 / (2 * √s) * s = √s / 2 := by
  have hsq : 0 < √s := Real.sqrt_pos.2 hs
  have hs' : s = √s * √s := (Real.mul_self_sqrt hs.le).symm
  rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) two_ne_zero]
  nth_rw 1 [hs']
  ring

/-- `f_c'(s) = -Φ(c√s)/s²`. -/
theorem hasDerivAt_fc (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y) {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) : HasDerivAt (fc E c) (-Phi E E' (c * √s) / s ^ 2) s := by
  have hsq : 0 < √s := Real.sqrt_pos.2 hs
  have h1 := ((hE (c * √s) (by positivity)).comp s (hasDerivAt_mul_sqrt (c := c) hs)).div
    (hasDerivAt_id s) hs.ne'
  convert h1 using 1
  simp only [Phi, id, Function.comp_apply]
  rw [show E' (c * √s) * (c * (1 / (2 * √s))) * s = E' (c * √s) * (c * (1 / (2 * √s) * s)) by
    ring, one_div_two_sqrt_mul_self hs]
  ring

/-- `s³ f_c'(s) = -s Φ(c√s)` near every `s > 0`. -/
theorem s3_deriv_fc (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y) {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) :
    (fun s => s ^ 3 * deriv (fc E c) s) =ᶠ[𝓝 s] fun s => -s * Phi E E' (c * √s) := by
  filter_upwards [Ioi_mem_nhds hs] with t (ht : 0 < t)
  rw [(hasDerivAt_fc hE hc ht).deriv]
  field_simp

theorem hasDerivAt_G (hΦ : ∀ y, 0 < y → HasDerivAt (Phi E E') (Φ' y) y) {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) :
    HasDerivAt (fun s => -s * Phi E E' (c * √s))
      (-Phi E E' (c * √s) - c * √s * Φ' (c * √s) / 2) s := by
  have hsq : 0 < √s := Real.sqrt_pos.2 hs
  have h1 := (hasDerivAt_id s).neg.mul
    ((hΦ (c * √s) (by positivity)).comp s (hasDerivAt_mul_sqrt (c := c) hs))
  convert h1 using 1
  have hs' : s = √s * √s := (Real.mul_self_sqrt hs.le).symm
  have h2 : s * (1 / (2 * √s)) = √s / 2 := by rw [mul_comm]; exact one_div_two_sqrt_mul_self hs
  simp only [Function.comp_apply, Pi.neg_apply, id_eq]
  linear_combination (Φ' (c * √s) * c) * h2

/-- `(s³ f_c')'(s) = -Φ(c√s) - (c√s/2) Φ'(c√s)`. -/
theorem deriv_s3_deriv_fc (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hΦ : ∀ y, 0 < y → HasDerivAt (Phi E E') (Φ' y) y) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    deriv (fun s => s ^ 3 * deriv (fc E c) s) s =
      -Phi E E' (c * √s) - c * √s * Φ' (c * √s) / 2 := by
  rw [(s3_deriv_fc hE hc hs).deriv_eq, (hasDerivAt_G hΦ hc hs).deriv]

theorem continuousOn_comp_mul_sqrt {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {c : ℝ}
    (hc : 0 < c) : ContinuousOn (fun s => g (c * √s)) (Ioi 0) :=
  hg.comp (continuousOn_const.mul Real.continuous_sqrt.continuousOn) fun s (hs : 0 < s) =>
    show 0 < c * √s from mul_pos hc (Real.sqrt_pos.2 hs)

/-- The continuum bubble integrand `f_c (s³ f_c')'`, written out. -/
def bub (E E' Φ' : ℝ → ℝ) (c s : ℝ) : ℝ :=
  fc E c s * (-Phi E E' (c * √s) - c * √s * Φ' (c * √s) / 2)

theorem continuousOn_bub (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hΦ : ∀ y, 0 < y → HasDerivAt (Phi E E') (Φ' y) y) (hΦ' : ContinuousOn Φ' (Ioi 0)) {c : ℝ}
    (hc : 0 < c) : ContinuousOn (bub E E' Φ' c) (Ioi 0) := by
  have hEc : ContinuousOn E (Ioi 0) := fun y hy => (hE y hy).continuousAt.continuousWithinAt
  have hΦc : ContinuousOn (Phi E E') (Ioi 0) := fun y hy =>
    (hΦ y hy).continuousAt.continuousWithinAt
  refine ((continuousOn_comp_mul_sqrt hEc hc).div continuousOn_id fun s (hs : 0 < s) =>
    hs.ne').mul ((continuousOn_comp_mul_sqrt hΦc hc).neg.sub
      (((continuousOn_const.mul Real.continuous_sqrt.continuousOn).mul
        (continuousOn_comp_mul_sqrt hΦ' hc)).div_const 2))

/-- **Integration by parts for the bubble.**
`-∫_ε^R f_c (s³ f_c')' ds = E Φ(c√R) - E Φ(c√ε) + ∫_ε^R Φ(c√s)² ds/s`. -/
theorem bubble_ibp (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hΦ : ∀ y, 0 < y → HasDerivAt (Phi E E') (Φ' y) y) (hΦ' : ContinuousOn Φ' (Ioi 0)) {c ε R : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hR : 0 < R) :
    -∫ s in ε..R, fc E c s * deriv (fun s => s ^ 3 * deriv (fc E c) s) s =
      E (c * √R) * Phi E E' (c * √R) - E (c * √ε) * Phi E E' (c * √ε) +
        ∫ s in ε..R, Phi E E' (c * √s) ^ 2 / s := by
  have hsub := uIcc_subset_Ioi hε hR
  have hΦc : ContinuousOn (Phi E E') (Ioi 0) := fun y hy =>
    (hΦ y hy).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_congr (g := fun s => fc E c s *
    (-Phi E E' (c * √s) - c * √s * Φ' (c * √s) / 2)) fun s hs => by
      rw [deriv_s3_deriv_fc hE hΦ hc (hsub hs)]]
  rw [integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt (u := fc E c)
    (u' := fun s => -Phi E E' (c * √s) / s ^ 2) (v := fun s => -s * Phi E E' (c * √s))
    (fun s hs => (hasDerivAt_fc hE hc (hsub hs)).hasDerivWithinAt)
    (fun s hs => (hasDerivAt_G hΦ hc (hsub hs)).hasDerivWithinAt)
    (((continuousOn_comp_mul_sqrt hΦc hc).neg.div (continuousOn_id.pow 2) fun s (hs : 0 < s) =>
      pow_ne_zero 2 hs.ne').mono hsub).intervalIntegrable
    (((continuousOn_comp_mul_sqrt hΦc hc).neg.sub
      (((continuousOn_const.mul Real.continuous_sqrt.continuousOn).mul
        (continuousOn_comp_mul_sqrt hΦ' hc)).div_const 2)).mono hsub).intervalIntegrable]
  have hint : ∫ s in ε..R, -Phi E E' (c * √s) / s ^ 2 * (-s * Phi E E' (c * √s)) =
      ∫ s in ε..R, Phi E E' (c * √s) ^ 2 / s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have : 0 < s := hsub hs
    field_simp
  rw [hint]
  simp only [fc]
  field_simp
  ring

/-- **The bubble difference in the continuum.** For profiles `E` and `Φ = E - yE'/2` (both with
limits `0` at `0` and `1` at `∞`) and `0 < a ≤ b`, the truncations of
`-∫_0^∞ (f_b (s³f_b')' - f_a (s³f_a')') ds` converge to `2 log(b/a)`. -/
theorem bubble_frullani (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hΦ : ∀ y, 0 < y → HasDerivAt (Phi E E') (Φ' y) y) (hΦ' : ContinuousOn Φ' (Ioi 0))
    (hEp : Profile E 0 1) (hΦp : Profile (Phi E E') 0 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => -∫ s in (n + 1 : ℝ)⁻¹..(n + 1),
      (fc E b s * deriv (fun s => s ^ 3 * deriv (fc E b) s) s -
        fc E a s * deriv (fun s => s ^ 3 * deriv (fc E a) s) s)) atTop
      (𝓝 (2 * log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hΦc : ContinuousOn (Phi E E') (Ioi 0) := fun y hy =>
    (hΦ y hy).continuousAt.continuousWithinAt
  set ε : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  set R : ℕ → ℝ := fun n => (n + 1 : ℝ)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hR : ∀ n, 0 < R n := fun n => by positivity
  -- the integrand, written out, is interval integrable
  have hii : ∀ {c : ℝ}, 0 < c → ∀ n, IntervalIntegrable
      (fun s => fc E c s * deriv (fun s => s ^ 3 * deriv (fc E c) s) s) volume (ε n) (R n) := by
    intro c hc n
    refine (((continuousOn_bub hE hΦ hΦ' hc).congr fun s (hs : 0 < s) => ?_).mono
      (uIcc_subset_Ioi (hε n) (hR n))).intervalIntegrable
    simp only [bub]; rw [deriv_s3_deriv_fc hE hΦ hc hs]
  have hiiΦ : ∀ {c : ℝ}, 0 < c → ∀ n, IntervalIntegrable
      (fun s => Phi E E' (c * √s) ^ 2 / s) volume (ε n) (R n) := by
    intro c hc n
    exact ((((continuousOn_comp_mul_sqrt hΦc hc).pow 2).div continuousOn_id
      fun s (hs : 0 < s) => hs.ne').mono (uIcc_subset_Ioi (hε n) (hR n))).intervalIntegrable
  have key : ∀ n, -∫ s in ε n..R n,
      (fc E b s * deriv (fun s => s ^ 3 * deriv (fc E b) s) s -
        fc E a s * deriv (fun s => s ^ 3 * deriv (fc E a) s) s) =
      ((E (b * √(R n)) * Phi E E' (b * √(R n)) - E (a * √(R n)) * Phi E E' (a * √(R n))) -
        (E (b * √(ε n)) * Phi E E' (b * √(ε n)) - E (a * √(ε n)) * Phi E E' (a * √(ε n)))) +
      ∫ s in ε n..R n, (Phi E E' (b * √s) ^ 2 - Phi E E' (a * √s) ^ 2) / s := by
    intro n
    rw [intervalIntegral.integral_sub (hii hb n) (hii ha n)]
    have e1 := bubble_ibp hE hΦ hΦ' hb (hε n) (hR n)
    have e2 := bubble_ibp hE hΦ hΦ' ha (hε n) (hR n)
    simp_rw [sub_div]
    rw [intervalIntegral.integral_sub (hiiΦ hb n) (hiiΦ ha n)]
    linarith
  simp_rw [show ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ = ε n from fun n => rfl,
    show ∀ n : ℕ, ((n : ℝ) + 1) = R n from fun n => rfl, key]
  -- the limits of the three pieces
  have hEΦ := hEp.mul hΦp
  simp only [mul_zero, mul_one] at hEΦ
  have hRt : Tendsto R atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsqR : ∀ {c : ℝ}, 0 < c → Tendsto (fun n => c * √(R n)) atTop atTop := fun hc =>
    (Real.tendsto_sqrt_atTop.comp hRt).const_mul_atTop hc
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hRt
  have hsqε : ∀ {c : ℝ}, 0 < c → Tendsto (fun n => c * √(ε n)) atTop (𝓝[>] 0) := by
    intro c hc
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := ((Real.continuous_sqrt.tendsto 0).comp hεt).const_mul c
      simpa using this
    · exact mul_pos hc (Real.sqrt_pos.2 (hε n))
  have hΦ2 := (hΦp.mul hΦp).integrableOn_sqrt ha hab
  have hI := tendsto_integral_trunc hΦ2
  rw [(hΦp.mul hΦp).frullani_sqrt ha hab] at hI
  have hlim := (((hEΦ.tendsto_atTop.comp (hsqR hb)).sub (hEΦ.tendsto_atTop.comp (hsqR ha))).sub
    ((hEΦ.tendsto_zero.comp (hsqε hb)).sub (hEΦ.tendsto_zero.comp (hsqε ha)))).add hI
  convert hlim using 2
  · simp only [sq]; rfl
  · simp

/-- **`𝔅(w_{j+1}) - 𝔅(w_j)` in the continuum.** With the bubble density `-f(s)(s³f'(s))'` in
`∫ d²p/(2π)² = (4π)^{-1} ∫ ds` and `f = f_{L^j}`, the difference is `(1/2π) log L`. -/
theorem continuum_B (hE : ∀ y, 0 < y → HasDerivAt E (E' y) y)
    (hΦ : ∀ y, 0 < y → HasDerivAt (Phi E E') (Φ' y) y) (hΦ' : ContinuousOn Φ' (Ioi 0))
    (hEp : Profile E 0 1) (hΦp : Profile (Phi E E') 0 1) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    Tendsto (fun n : ℕ => (4 * π)⁻¹ * -∫ s in (n + 1 : ℝ)⁻¹..(n + 1),
      (fc E (L ^ (j + 1)) s * deriv (fun s => s ^ 3 * deriv (fc E (L ^ (j + 1))) s) s -
        fc E (L ^ j) s * deriv (fun s => s ^ 3 * deriv (fc E (L ^ j)) s) s)) atTop
      (𝓝 (log L / (2 * π))) := by
  have := (bubble_frullani hE hΦ hΦ' hEp hΦp (by positivity)
    (pow_le_pow_right₀ hL (Nat.le_succ j))).const_mul (4 * π)⁻¹
  rw [log_pow_succ_div (by linarith)] at this
  convert this using 2
  field_simp
  ring

end

end Step2.D2
