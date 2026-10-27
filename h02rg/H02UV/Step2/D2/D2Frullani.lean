import Mathlib

/-!
# Frullani's integral (for `prop:d2`)

The universal value `(1/2π) log L` in Proposition `prop:d2` comes from Frullani's formula
`∫_0^∞ (h(bt) - h(at)) dt/t = (h(∞) - h(0)) log(b/a)`.

* `Profile h h₀ h∞`: `h` is continuous and bounded on `(0, ∞)`, with `|h(y) - h₀| ≤ K y^α` for
  `y ≤ 1` and `|h(y) - h∞| ≤ K y^{-α}` for `y ≥ 1` (some `K`, `α > 0`); closed under products
  (`Profile.mul`), so `E`, `E²`, `Φ²` are profiles once `E`, `Φ` are;
* `frullani_interval`: the exact identity
  `∫_ε^R (h(bt) - h(at)) dt/t = ∫_{aR}^{bR} h(u) du/u - ∫_{aε}^{bε} h(u) du/u`;
* `frullani_trunc`: the quantitative truncated form, error `(δ₀ + δ∞) log(b/a)` where `δ₀`, `δ∞`
  bound `|h - h₀|` on `[aε, bε]` and `|h - h∞|` on `[aR, bR]`;
* `Profile.integrableOn`, `Profile.frullani`: for a profile and `0 < a ≤ b`, the integrand is
  integrable on `(0, ∞)` and `∫_0^∞ (h(bt) - h(at)) dt/t = (h∞ - h₀) log(b/a)`;
* `Profile.frullani_sqrt`: the form `∫_0^∞ (h(b√s) - h(a√s)) ds/s = 2 (h∞ - h₀) log(b/a)` used
  in the outline (`s = |p|²`).
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real intervalIntegral

/-! ### Profiles -/

/-- `h` is continuous and bounded on `(0, ∞)` and tends to `h₀` at `0`, to `h∞` at `∞`, at a
power rate. -/
structure Profile (h : ℝ → ℝ) (h0 hinf : ℝ) : Prop where
  cont : ContinuousOn h (Ioi 0)
  bound : ∃ K α : ℝ, 0 < α ∧ ∀ y, 0 < y →
    |h y| ≤ K ∧ (y ≤ 1 → |h y - h0| ≤ K * y ^ α) ∧ (1 ≤ y → |h y - hinf| ≤ K * y ^ (-α))

theorem Profile.mul {h g : ℝ → ℝ} {h0 hinf g0 ginf : ℝ} (hp : Profile h h0 hinf)
    (gp : Profile g g0 ginf) : Profile (fun y => h y * g y) (h0 * g0) (hinf * ginf) where
  cont := hp.cont.mul gp.cont
  bound := by
    obtain ⟨Kh, αh, hαh, hh⟩ := hp.bound
    obtain ⟨Kg, αg, hαg, hg⟩ := gp.bound
    have hKh : 0 ≤ Kh := (abs_nonneg _).trans (hh 1 one_pos).1
    have hKg : 0 ≤ Kg := (abs_nonneg _).trans (hg 1 one_pos).1
    refine ⟨Kh * Kg + (|h0| + |hinf|) * Kg, min αh αg, lt_min hαh hαg, fun y hy => ?_⟩
    obtain ⟨hb, h0b, hib⟩ := hh y hy
    obtain ⟨gb, g0b, gib⟩ := hg y hy
    have hK2 : 0 ≤ (|h0| + |hinf|) * Kg := by positivity
    refine ⟨?_, fun hy1 => ?_, fun hy1 => ?_⟩
    · rw [abs_mul]
      nlinarith [abs_nonneg (h y), abs_nonneg (g y)]
    · have e1 : y ^ αh ≤ y ^ min αh αg := rpow_le_rpow_of_exponent_ge hy hy1 (min_le_left _ _)
      have e2 : y ^ αg ≤ y ^ min αh αg := rpow_le_rpow_of_exponent_ge hy hy1 (min_le_right _ _)
      have hyp : 0 ≤ y ^ min αh αg := by positivity
      have hyp' : 0 ≤ y ^ αg := by positivity
      calc |h y * g y - h0 * g0| = |(h y - h0) * g y + h0 * (g y - g0)| := by ring_nf
        _ ≤ |h y - h0| * |g y| + |h0| * |g y - g0| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (Kh * y ^ αh) * Kg + |h0| * (Kg * y ^ αg) := by
            gcongr; exacts [h0b hy1, g0b hy1]
        _ ≤ (Kh * y ^ min αh αg) * Kg + |h0| * (Kg * y ^ min αh αg) := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (abs_nonneg hinf) hKg) hyp,
              mul_nonneg (mul_nonneg (abs_nonneg h0) hKg) hyp]
    · have e1 : y ^ (-αh) ≤ y ^ (-min αh αg) :=
        rpow_le_rpow_of_exponent_le hy1 (neg_le_neg (min_le_left _ _))
      have e2 : y ^ (-αg) ≤ y ^ (-min αh αg) :=
        rpow_le_rpow_of_exponent_le hy1 (neg_le_neg (min_le_right _ _))
      have hyp : 0 ≤ y ^ (-min αh αg) := by positivity
      have hyp' : 0 ≤ y ^ (-αg) := by positivity
      calc |h y * g y - hinf * ginf| = |(h y - hinf) * g y + hinf * (g y - ginf)| := by ring_nf
        _ ≤ |h y - hinf| * |g y| + |hinf| * |g y - ginf| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (Kh * y ^ (-αh)) * Kg + |hinf| * (Kg * y ^ (-αg)) := by
            gcongr; exacts [hib hy1, gib hy1]
        _ ≤ (Kh * y ^ (-min αh αg)) * Kg + |hinf| * (Kg * y ^ (-min αh αg)) := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (abs_nonneg hinf) hKg) hyp,
              mul_nonneg (mul_nonneg (abs_nonneg h0) hKg) hyp]

/-! ### The truncated identity -/

theorem continuousOn_comp_mul_div {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {c : ℝ} (hc0 : 0 < c) :
    ContinuousOn (fun t => h (c * t) / t) (Ioi 0) :=
  (hc.comp (continuousOn_const.mul continuousOn_id) fun t (ht : 0 < t) =>
    show 0 < c * t from mul_pos hc0 ht).div continuousOn_id fun t (ht : 0 < t) => ht.ne'

theorem uIcc_subset_Ioi {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : uIcc x y ⊆ Ioi 0 :=
  fun _ hu => lt_of_lt_of_le (lt_min hx hy) hu.1

theorem intervalIntegrable_comp_mul_div {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {c : ℝ}
    (hc0 : 0 < c) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun t => h (c * t) / t) volume x y :=
  ((continuousOn_comp_mul_div hc hc0).mono (uIcc_subset_Ioi hx hy)).intervalIntegrable

theorem intervalIntegrable_div {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) : IntervalIntegrable (fun u => h u / u) volume x y := by
  simpa using intervalIntegrable_comp_mul_div hc one_pos hx hy

/-- `∫_x^y h(ct) dt/t = ∫_{cx}^{cy} h(u) du/u`. -/
theorem integral_comp_mul_div (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (x y : ℝ) :
    ∫ t in x..y, h (c * t) / t = ∫ u in c * x..c * y, h u / u := by
  have : ∀ t, h (c * t) / t = c * ((fun u => h u / u) (c * t)) := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · simp only; field_simp
  have hcm := intervalIntegral.integral_comp_mul_left (fun u => h u / u) (a := x) (b := y) hc.ne'
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, hcm, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Frullani, exact truncated form.** -/
theorem frullani_interval {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {a b ε R : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hε : 0 < ε) (hR : 0 < R) :
    ∫ t in ε..R, (h (b * t) - h (a * t)) / t =
      (∫ u in a * R..b * R, h u / u) - ∫ u in a * ε..b * ε, h u / u := by
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub (intervalIntegrable_comp_mul_div hc hb hε hR)
    (intervalIntegrable_comp_mul_div hc ha hε hR), integral_comp_mul_div h hb,
    integral_comp_mul_div h ha]
  exact integral_interval_sub_interval_comm' (intervalIntegrable_div hc (by positivity)
    (by positivity)) (intervalIntegrable_div hc (by positivity) (by positivity))
    (intervalIntegrable_div hc (by positivity) (by positivity))

/-- `|∫_x^y h(u) du/u - c log(y/x)| ≤ δ log(y/x)` if `|h - c| ≤ δ` on `[x, y]`. -/
theorem abs_integral_div_sub_le {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {x y c δ : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hδ : ∀ u ∈ Icc x y, |h u - c| ≤ δ) :
    |(∫ u in x..y, h u / u) - c * log (y / x)| ≤ δ * log (y / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hlog : ∀ c : ℝ, c * log (y / x) = ∫ u in x..y, (fun _ => c) u / u := by
    intro c
    simp_rw [div_eq_mul_inv c]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx hy]
  rw [hlog c, hlog δ, ← intervalIntegral.integral_sub (intervalIntegrable_div hc hx hy)
    (intervalIntegrable_div continuousOn_const hx hy), ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hxy (ae_of_all _ fun u hu => ?_)
    (intervalIntegrable_div continuousOn_const hx hy)
  have hu0 : 0 < u := hx.trans hu.1
  rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hu0]
  exact div_le_div_of_nonneg_right (hδ u ⟨hu.1.le, hu.2⟩) hu0.le

/-- **Frullani, quantitative truncated form.** -/
theorem frullani_trunc {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {a b ε R h0 hinf δ0 δinf : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) (hR : 0 < R)
    (h0b : ∀ u ∈ Icc (a * ε) (b * ε), |h u - h0| ≤ δ0)
    (hinfb : ∀ u ∈ Icc (a * R) (b * R), |h u - hinf| ≤ δinf) :
    |(∫ t in ε..R, (h (b * t) - h (a * t)) / t) - (hinf - h0) * log (b / a)| ≤
      (δ0 + δinf) * log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have e0 := abs_integral_div_sub_le hc (by positivity) (mul_le_mul_of_nonneg_right hab hε.le) h0b
  have e1 := abs_integral_div_sub_le hc (by positivity) (mul_le_mul_of_nonneg_right hab hR.le) hinfb
  rw [mul_div_mul_right _ _ hε.ne'] at e0
  rw [mul_div_mul_right _ _ hR.ne'] at e1
  rw [frullani_interval hc ha hb hε hR]
  calc _ = |((∫ u in a * R..b * R, h u / u) - hinf * log (b / a)) -
        ((∫ u in a * ε..b * ε, h u / u) - h0 * log (b / a))| := by ring_nf
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

/-! ### Integrability and the full formula -/

theorem Profile.integrableOn {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun t => (h (b * t) - h (a * t)) / t) (Ioi 0) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨K, α, hα, hK⟩ := hp.bound
  set f := fun t => (h (b * t) - h (a * t)) / t
  have hcont : ContinuousOn f (Ioi 0) :=
    ((hp.cont.comp (continuousOn_const.mul continuousOn_id) fun t (ht : 0 < t) =>
      show 0 < b * t from mul_pos hb ht).sub
      (hp.cont.comp (continuousOn_const.mul continuousOn_id) fun t (ht : 0 < t) =>
      show 0 < a * t from mul_pos ha ht)).div continuousOn_id fun t (ht : 0 < t) => ht.ne'
  have hab' : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  have hsplit : Ioi (0 : ℝ) = Ioc 0 (1 / b) ∪ (Ioc (1 / b) (1 / a) ∪ Ioi (1 / a)) := by
    rw [Ioc_union_Ioi_eq_Ioi hab', Ioc_union_Ioi_eq_Ioi (by positivity)]
  rw [hsplit]
  refine IntegrableOn.union ?_ (IntegrableOn.union ?_ ?_)
  · -- near `0`: `|f t| ≤ 2K b^α t^{α-1}`
    have hg : IntegrableOn (fun t : ℝ => 2 * K * b ^ α * t ^ (α - 1)) (Ioc 0 (1 / b)) := by
      refine Integrable.const_mul ?_ _
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1
        (intervalIntegrable_rpow' (by linarith))
    refine hg.mono' ((hcont.mono fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have hbt : b * t ≤ 1 := by
      have := mul_le_mul_of_nonneg_left ht.2 hb.le; rwa [mul_one_div_cancel hb.ne'] at this
    have hat : a * t ≤ b * t := mul_le_mul_of_nonneg_right hab ht0.le
    have h1 := (hK (b * t) (by positivity)).2.1 hbt
    have h2 := (hK (a * t) (by positivity)).2.1 (hat.trans hbt)
    have h3 : (a * t) ^ α ≤ (b * t) ^ α := rpow_le_rpow (by positivity) hat hα.le
    have h4 : (b * t) ^ α / t = b ^ α * t ^ (α - 1) := by
      rw [mul_rpow hb.le ht0.le, rpow_sub_one ht0.ne']; ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |h (b * t) - h (a * t)| / t ≤ (2 * K * (b * t) ^ α) / t := by
          gcongr
          calc |h (b * t) - h (a * t)| = |(h (b * t) - h0) - (h (a * t) - h0)| := by ring_nf
            _ ≤ |h (b * t) - h0| + |h (a * t) - h0| := abs_sub _ _
            _ ≤ _ := by nlinarith [(abs_nonneg _).trans (hK 1 one_pos).1]
      _ = 2 * K * b ^ α * t ^ (α - 1) := by rw [mul_div_assoc, h4]; ring
  · -- the middle: continuity on a compact set
    exact ((hcont.mono fun t ht => lt_of_lt_of_le (by positivity) ht.1).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  · -- near `∞`: `|f t| ≤ 2K a^{-α} t^{-α-1}`
    have hg : IntegrableOn (fun t : ℝ => 2 * K * a ^ (-α) * t ^ (-α - 1)) (Ioi (1 / a)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity)).const_mul _
    refine hg.mono' ((hcont.mono fun t (ht : 1 / a < t) =>
      lt_trans (by positivity) ht).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans (by positivity) ht
    have hat : 1 ≤ a * t := by
      have := mul_le_mul_of_nonneg_left (le_of_lt ht) ha.le; rwa [mul_one_div_cancel ha.ne'] at this
    have hbt : a * t ≤ b * t := mul_le_mul_of_nonneg_right hab ht0.le
    have h1 := (hK (b * t) (by positivity)).2.2 (hat.trans hbt)
    have h2 := (hK (a * t) (by positivity)).2.2 hat
    have h3 : (b * t) ^ (-α) ≤ (a * t) ^ (-α) :=
      rpow_le_rpow_of_nonpos (by positivity) hbt (by linarith)
    have h4 : (a * t) ^ (-α) / t = a ^ (-α) * t ^ (-α - 1) := by
      rw [mul_rpow ha.le ht0.le, rpow_sub_one ht0.ne']; ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |h (b * t) - h (a * t)| / t ≤ (2 * K * (a * t) ^ (-α)) / t := by
          gcongr
          calc |h (b * t) - h (a * t)| = |(h (b * t) - hinf) - (h (a * t) - hinf)| := by ring_nf
            _ ≤ |h (b * t) - hinf| + |h (a * t) - hinf| := abs_sub _ _
            _ ≤ _ := by nlinarith [(abs_nonneg _).trans (hK 1 one_pos).1]
      _ = 2 * K * a ^ (-α) * t ^ (-α - 1) := by rw [mul_div_assoc, h4]; ring

/-- Truncations `∫_{1/(n+1)}^{n+1}` of an integral over `(0, ∞)` converge. -/
theorem tendsto_integral_trunc {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    Tendsto (fun n : ℕ => ∫ t in (n + 1 : ℝ)⁻¹..(n + 1), g t) atTop (𝓝 (∫ t in Ioi 0, g t)) := by
  set s : ℕ → Set ℝ := fun n => Ioc ((n + 1 : ℝ)⁻¹) (n + 1)
  have hmono : Monotone s := by
    intro n m hnm
    have : (n + 1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ hnm
    exact Ioc_subset_Ioc (inv_anti₀ (by positivity) this) this
  have hU : (⋃ n, s n) = Ioi 0 := by
    ext t
    simp only [mem_iUnion, mem_Ioc, mem_Ioi, s]
    constructor
    · rintro ⟨n, h1, -⟩; exact lt_trans (by positivity) h1
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_gt (max t t⁻¹)
      refine ⟨n, ?_, ?_⟩
      · rw [inv_lt_comm₀ (by positivity) ht]; linarith [le_max_right t t⁻¹]
      · linarith [le_max_left t t⁻¹]
  have h1 := tendsto_setIntegral_of_monotone (μ := volume) (f := g) (fun n => measurableSet_Ioc)
    hmono (by rw [hU]; exact hg)
  rw [hU] at h1
  refine h1.congr fun n => ?_
  have h1n : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  rw [integral_of_le ((inv_le_one_of_one_le₀ h1n).trans h1n)]

/-- **Frullani's formula.** For a profile `h` and `0 < a ≤ b`,
`∫_0^∞ (h(bt) - h(at)) dt/t = (h∞ - h₀) log(b/a)`. -/
theorem Profile.frullani {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in Ioi 0, (h (b * t) - h (a * t)) / t = (hinf - h0) * log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨K, α, hα, hK⟩ := hp.bound
  refine tendsto_nhds_unique (tendsto_integral_trunc (hp.integrableOn ha hab)) ?_
  -- the truncated integrals converge to the Frullani value
  have hN : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hz0 : Tendsto (fun x : ℝ => (b * x⁻¹) ^ α) atTop (𝓝 0) := by
    have := ((continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).comp
      (by simpa using tendsto_inv_atTop_zero.const_mul b)
    simpa [Function.comp_def, zero_rpow hα.ne'] using this
  have hzi : Tendsto (fun x : ℝ => (a * x) ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp (tendsto_id.const_mul_atTop ha)
  have hbd : Tendsto (fun n : ℕ => (K * (b * (n + 1 : ℝ)⁻¹) ^ α + K * (a * (n + 1)) ^ (-α)) *
      log (b / a)) atTop (𝓝 0) := by
    have := (((hz0.comp hN).const_mul K).add ((hzi.comp hN).const_mul K)).mul_const (log (b / a))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbd
  have hev1 : ∀ᶠ n : ℕ in atTop, b ≤ (n + 1 : ℝ) := hN.eventually_ge_atTop b
  have hev2 : ∀ᶠ n : ℕ in atTop, a⁻¹ ≤ (n + 1 : ℝ) := hN.eventually_ge_atTop a⁻¹
  filter_upwards [hev1, hev2] with n hn1 hn2
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hε : 0 < (n + 1 : ℝ)⁻¹ := by positivity
  have h1n : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  rw [Real.norm_eq_abs]
  refine frullani_trunc hp.cont ha hab hε hn0 (fun u hu => ?_) (fun u hu => ?_)
  · have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
    have hu1 : u ≤ 1 := hu.2.trans (by
      rw [← div_eq_mul_inv, div_le_one hn0]; exact hn1)
    exact ((hK u hu0).2.1 hu1).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow hu0.le hu.2 hα.le) ((abs_nonneg _).trans (hK 1 one_pos).1))
  · have hu1 : 1 ≤ a * (n + 1) := by
      rw [← inv_mul_le_iff₀ ha, mul_one]; exact hn2
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (hu1.trans hu.1)
    exact ((hK u hu0).2.2 (hu1.trans hu.1)).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos (by positivity) hu.1 (by linarith))
      ((abs_nonneg _).trans (hK 1 one_pos).1))

/-- **Frullani in the variable `s = t²`.** `∫_0^∞ (h(b√s) - h(a√s)) ds/s = 2 (h∞ - h₀) log(b/a)`. -/
theorem Profile.frullani_sqrt {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ s in Ioi 0, (h (b * √s) - h (a * √s)) / s = 2 * ((hinf - h0) * log (b / a)) := by
  rw [← integral_comp_rpow_Ioi _ (two_ne_zero), ← hp.frullani ha hab, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
  simp only [smul_eq_mul]
  rw [Real.rpow_two, Real.sqrt_sq hx.le, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, abs_two]
  field_simp

theorem Profile.integrableOn_sqrt {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun s => (h (b * √s) - h (a * √s)) / s) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff _ (two_ne_zero)]
  refine IntegrableOn.congr_fun ((hp.integrableOn ha hab).const_mul 2) (fun x (hx : 0 < x) => ?_)
    measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [Real.rpow_two, Real.sqrt_sq hx.le, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, abs_two]
  field_simp

theorem Profile.tendsto_atTop {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) :
    Tendsto h atTop (𝓝 hinf) := by
  obtain ⟨K, α, hα, hK⟩ := hp.bound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (tendsto_rpow_neg_atTop hα).const_mul K)
  filter_upwards [eventually_ge_atTop 1] with y hy
  exact (hK y (by linarith)).2.2 hy

theorem Profile.tendsto_zero {h : ℝ → ℝ} {h0 hinf : ℝ} (hp : Profile h h0 hinf) :
    Tendsto h (𝓝[>] 0) (𝓝 h0) := by
  obtain ⟨K, α, hα, hK⟩ := hp.bound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hz : Tendsto (fun y : ℝ => K * y ^ α) (𝓝[>] 0) (𝓝 0) := by
    have := (((continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).const_mul K
    simpa [zero_rpow hα.ne'] using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hz
  filter_upwards [Ioc_mem_nhdsGT one_pos] with y hy
  exact (hK y hy.1).2.1 hy.2

end

end Step2.D2
