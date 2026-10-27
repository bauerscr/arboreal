import Mathlib

/-!
# A one-dimensional implicit function lemma (differentiability of `μ₀^c(b)`)

`hasDerivAt_implicit`: let `φ : ℝ × ℝ → ℝ` be differentiable at `(b₀, m(b₀))` and let `m` be
continuous at `b₀` with `φ(b, m(b)) = 0` for `b` near `b₀`. If `φ(b₀, ·)` is *expanding* near
`m(b₀)`, `|μ - m(b₀)| ≤ c |φ(b₀, μ)|`, then `m` is differentiable at `b₀`, with
`m'(b₀) = -∂_b φ / ∂_μ φ`. No `C¹` hypothesis is needed: the expansion replaces the invertibility
of `∂_μ φ` and the continuity of `m` replaces the contraction argument of the implicit function
theorem.
-/

open Filter Topology Asymptotics

noncomputable section

namespace Flow2

/-- The derivative of `φ` at `x₀` on `(h, r)`. -/
lemma fderiv_pair (D : ℝ × ℝ →L[ℝ] ℝ) (h r : ℝ) : D (h, r) = h * D (1, 0) + r * D (0, 1) := by
  have e : ((h, r) : ℝ × ℝ) = h • ((1 : ℝ), (0 : ℝ)) + r • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [e, D.map_add, D.map_smul, D.map_smul, smul_eq_mul, smul_eq_mul]

lemma norm_pair_le (h r : ℝ) : ‖((h, r) : ℝ × ℝ)‖ ≤ |h| + |r| := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (by linarith [abs_nonneg r]) (by linarith [abs_nonneg h])

/-- The remainder bound of a Fréchet derivative, pulled back along a curve. -/
lemma rem_bound {φ : ℝ × ℝ → ℝ} {x₀ : ℝ × ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} (hD : HasFDerivAt φ D x₀)
    {κ : ℝ} (hκ : 0 < κ) {α : Type*} {l : Filter α} {γ : α → ℝ × ℝ}
    (hγ : Tendsto γ l (𝓝 x₀)) :
    ∀ᶠ s in l, |φ (γ s) - φ x₀ - D (γ s - x₀)| ≤ κ * ‖γ s - x₀‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD).def hκ
  have h' : ∀ᶠ y in 𝓝 x₀, |φ y - φ x₀ - D (y - x₀)| ≤ κ * ‖y - x₀‖ := by
    have ht : Tendsto (fun y : ℝ × ℝ => y - x₀) (𝓝 x₀) (𝓝 0) := by
      have := ((continuous_id.sub continuous_const).tendsto x₀ :
        Tendsto (fun y : ℝ × ℝ => y - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)))
      simpa using this
    filter_upwards [ht.eventually h] with y hy
    simpa [Real.norm_eq_abs, add_sub_cancel] using hy
  exact hγ.eventually h'

/-- `|∂_μ φ| ≥ 1/(2c)` from the expansion. -/
lemma deriv_lower {φ : ℝ × ℝ → ℝ} {b₀ μs c : ℝ} (hc : 0 < c) {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt φ D (b₀, μs)) (hφ0 : φ (b₀, μs) = 0)
    (hlow : ∀ᶠ μ in 𝓝 μs, |μ - μs| ≤ c * |φ (b₀, μ)|) : 1 / (2 * c) ≤ |D (0, 1)| := by
  have hγ : Tendsto (fun μ : ℝ => ((b₀, μ) : ℝ × ℝ)) (𝓝 μs) (𝓝 (b₀, μs)) :=
    (continuous_const.prodMk continuous_id).tendsto μs
  have hr := rem_bound hD (by positivity : (0 : ℝ) < 1 / (2 * c)) hγ
  obtain ⟨μ, ⟨h1, h2⟩, hne⟩ := ((hr.and hlow).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {μ | μ ≠ μs} ∈ 𝓝[≠] μs) |>.exists
  have hpos : 0 < |μ - μs| := abs_pos.2 (sub_ne_zero.2 hne)
  have e1 : ((b₀, μ) : ℝ × ℝ) - (b₀, μs) = (0, μ - μs) := by ext <;> simp
  rw [e1, hφ0, fderiv_pair, zero_mul, zero_add] at h1
  have hn : ‖((0, μ - μs) : ℝ × ℝ)‖ = |μ - μs| := by
    rw [Prod.norm_def, norm_zero, Real.norm_eq_abs, max_eq_right (abs_nonneg _)]
  rw [hn] at h1
  have h3 : |φ (b₀, μ)| ≤ |μ - μs| * |D (0, 1)| + 1 / (2 * c) * |μ - μs| := by
    have := abs_sub_abs_le_abs_sub (φ (b₀, μ)) ((μ - μs) * D (0, 1))
    rw [sub_zero] at h1
    rw [abs_mul] at this
    linarith
  have h4 : |μ - μs| ≤ c * (|μ - μs| * |D (0, 1)|) + c * (1 / (2 * c)) * |μ - μs| := by
    have := mul_le_mul_of_nonneg_left h3 hc.le
    linarith
  have e2 : c * (1 / (2 * c)) = 1 / 2 := by field_simp
  rw [e2] at h4
  have h5 : |μ - μs| * (1 / 2) ≤ |μ - μs| * (c * |D (0, 1)|) := by nlinarith
  have h6 := le_of_mul_le_mul_left h5 hpos
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The implicit function lemma.** -/
theorem hasDerivAt_implicit {φ : ℝ × ℝ → ℝ} {m : ℝ → ℝ} {b₀ c : ℝ} (hc : 0 < c)
    {D : ℝ × ℝ →L[ℝ] ℝ} (hD : HasFDerivAt φ D (b₀, m b₀)) (hm : ContinuousAt m b₀)
    (h0 : ∀ᶠ b in 𝓝 b₀, φ (b, m b) = 0)
    (hlow : ∀ᶠ μ in 𝓝 (m b₀), |μ - m b₀| ≤ c * |φ (b₀, μ)|) :
    HasDerivAt m (-(D (1, 0) / D (0, 1))) b₀ := by
  have hφ0 : φ (b₀, m b₀) = 0 := h0.self_of_nhds
  set a := D (1, 0) with ha
  set d := D (0, 1) with hd
  have hdl := deriv_lower hc hD hφ0 hlow
  have hd0 : 0 < |d| := lt_of_lt_of_le (by positivity) hdl
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro η hη
  set K := 2 * c * |a| + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set κ := min (1 / (4 * c)) (η * |d| / (1 + K)) with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) (by positivity)
  have hκ1 : κ ≤ 1 / (4 * c) := min_le_left _ _
  have hκ2 : κ ≤ η * |d| / (1 + K) := min_le_right _ _
  have hγ1 : Tendsto (fun b : ℝ => ((b, m b) : ℝ × ℝ)) (𝓝 b₀) (𝓝 (b₀, m b₀)) :=
    (continuous_id.continuousAt.prodMk hm).tendsto
  have hγ3 : Tendsto (fun b : ℝ => ((b₀, m b) : ℝ × ℝ)) (𝓝 b₀) (𝓝 (b₀, m b₀)) :=
    (continuousAt_const.prodMk hm).tendsto
  filter_upwards [h0, rem_bound hD hκ0 hγ1, rem_bound hD hκ0 hγ3, hm.tendsto.eventually hlow]
    with b e0 e1 e3 e4
  obtain ⟨h, hh⟩ : ∃ h, h = b - b₀ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = m b - m b₀ := ⟨_, rfl⟩
  have p1 : ((b, m b) : ℝ × ℝ) - (b₀, m b₀) = (h, r) := by ext <;> simp [hh, hr]
  have p3 : ((b₀, m b) : ℝ × ℝ) - (b₀, m b₀) = (0, r) := by ext <;> simp [hr]
  rw [p1, e0, hφ0, fderiv_pair, ← ha, ← hd] at e1
  rw [p3, hφ0, fderiv_pair, ← ha, ← hd] at e3
  rw [← hr] at e4
  have n1 := norm_pair_le h r
  have n3 := norm_pair_le 0 r
  rw [abs_zero, zero_add] at n3
  have hκc : 0 ≤ κ := hκ0.le
  -- `|a h + d r| ≤ κ (|h| + |r|)`
  have f1 : |h * a + r * d| ≤ κ * (|h| + |r|) := by
    have : |h * a + r * d| = |0 - 0 - (h * a + r * d)| := by
      rw [sub_zero, zero_sub, abs_neg]
    rw [this]; exact e1.trans (mul_le_mul_of_nonneg_left n1 hκc)
  -- `|φ(b₀, m b) - d r| ≤ κ |r|`
  have f3 : |φ (b₀, m b) - r * d| ≤ κ * |r| := by
    have : φ (b₀, m b) - 0 - (0 * a + r * d) = φ (b₀, m b) - r * d := by ring
    rw [this] at e3; exact e3.trans (mul_le_mul_of_nonneg_left n3 hκc)
  -- `|r| ≤ K |h|`
  have f4 : |φ (b₀, m b)| ≤ κ * (|h| + |r|) + |a| * |h| + κ * |r| := by
    have e : φ (b₀, m b) = (h * a + r * d) - h * a + (φ (b₀, m b) - r * d) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have := abs_sub (h * a + r * d) (h * a)
    rw [abs_mul h a, mul_comm |h| |a|] at this
    linarith
  have hcκ : c * κ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hκ1 hc.le
    rwa [show c * (1 / (4 * c)) = 1 / 4 by field_simp] at this
  have f5 : |r| ≤ K * |h| := by
    have g1 := mul_le_mul_of_nonneg_left f4 hc.le
    have g2 : c * (κ * (|h| + |r|) + |a| * |h| + κ * |r|) =
        (c * κ) * (|h| + 2 * |r|) + c * |a| * |h| := by ring
    rw [g2] at g1
    have g3 := mul_le_mul_of_nonneg_right hcκ (by positivity : (0 : ℝ) ≤ |h| + 2 * |r|)
    rw [hK]
    nlinarith [abs_nonneg h, abs_nonneg r]
  -- conclusion
  have f6 : |r + h * (a / d)| ≤ κ * (1 + K) * |h| / |d| := by
    have hd' : d ≠ 0 := abs_pos.1 hd0
    have e : r + h * (a / d) = (h * a + r * d) / d := by field_simp; ring
    rw [e, abs_div, div_le_div_iff_of_pos_right hd0]
    refine f1.trans ?_
    have := mul_le_mul_of_nonneg_left f5 hκc
    nlinarith
  have f7 : κ * (1 + K) * |h| / |d| ≤ η * |h| := by
    rw [div_le_iff₀ hd0]
    have g := mul_le_mul_of_nonneg_right hκ2 (by positivity : (0 : ℝ) ≤ (1 + K) * |h|)
    have e : η * |d| / (1 + K) * ((1 + K) * |h|) = η * |h| * |d| := by field_simp
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hh, smul_eq_mul]
  have e : m b - m b₀ - h * -(a / d) = r + h * (a / d) := by rw [hr]; ring
  rw [e]
  exact f6.trans f7

/-- **The implicit function lemma** (differentiability). -/
theorem differentiableAt_implicit {φ : ℝ × ℝ → ℝ} {m : ℝ → ℝ} {b₀ c : ℝ} (hc : 0 < c)
    (hφ : DifferentiableAt ℝ φ (b₀, m b₀)) (hm : ContinuousAt m b₀)
    (h0 : ∀ᶠ b in 𝓝 b₀, φ (b, m b) = 0)
    (hlow : ∀ᶠ μ in 𝓝 (m b₀), |μ - m b₀| ≤ c * |φ (b₀, μ)|) :
    DifferentiableAt ℝ m b₀ :=
  (hasDerivAt_implicit hc hφ.hasFDerivAt hm h0 hlow).differentiableAt

end Flow2
