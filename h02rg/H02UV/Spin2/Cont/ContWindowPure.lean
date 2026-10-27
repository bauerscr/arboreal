import Step2.Flow.FlowThm

/-!
# `cor:window` (a): the pure limit arguments

* `a5w_log_div`: `log(αN + γ)/N → 0`.
* `a5w_limit`: if, with `B_N = A·N·log L`, `β = betaL L = (3/2π) log L`,
  `(J_N : ℤ) = ⌊N + log_L ℓ_N⌋` (`ℓ_N → ℓ > 0`), `|1/G_N − B_N + J_Nβ| ≤ C₁ + C₂ log B_N` and
  `|P_N − ϑ_N²| ≤ K ϑ_N² G_N` with `ϑ_N² = ((1/G_N)/B_N)^{2/3}` for large `N`, then
  `P_N → (1 − 3/(2πA))^{2/3}` (`A > 3/2π`).
-/

namespace Spin2

open Filter Topology

noncomputable section

/-- `log(αN + γ)/N → 0` for `α > 0`. -/
theorem a5w_log_div {α : ℝ} (hα : 0 < α) (γ : ℝ) :
    Tendsto (fun N : ℕ => Real.log (α * N + γ) / N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => α * N + γ) atTop atTop :=
    tendsto_atTop_add_const_right _ γ (tendsto_natCast_atTop_atTop.const_mul_atTop hα)
  have h2 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h4 : Tendsto (fun N : ℕ => α + γ / N) atTop (𝓝 α) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat γ)
  have h5 := (h2.comp h1).mul h4
  rw [zero_mul] at h5
  refine h5.congr' ?_
  filter_upwards [h1.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hy hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simp only [Function.comp]
  field_simp

/-- **The limit in `cor:window` (a)** (pure). -/
theorem a5w_limit (L : ℕ) (hL : 1 < (L : ℝ)) {A : ℝ} (hA : 3 / (2 * Real.pi) < A) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (ℓs : ℕ → ℝ) (hℓs : Tendsto ℓs atTop (𝓝 ℓ)) (P : ℕ → ℝ) (J : ℕ → ℕ)
    (G : ℕ → ℝ) (C₁ C₂ K : ℝ) (N₁ : ℕ)
    (h : ∀ N, N₁ ≤ N → (J N : ℤ) = ⌊(N : ℝ) + Real.logb L (ℓs N)⌋ ∧ 0 < G N ∧
      |1 / G N - A * (N * Real.log L) + J N * Step2.betaL L| ≤
        C₁ + C₂ * Real.log (A * (N * Real.log L)) ∧
      |P N - ((1 / G N) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ)| ≤
        K * ((1 / G N) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ) / (1 / G N)) :
    Tendsto P atTop (𝓝 ((1 - 3 / (2 * Real.pi * A)) ^ (2 / 3 : ℝ))) := by
  set lL := Real.log L with hlLd
  have hlL : 0 < lL := Real.log_pos hL
  have hπ : 0 < Real.pi := Real.pi_pos
  have hA0 : 0 < A := lt_trans (by positivity) hA
  have hAl : 0 < A * lL := mul_pos hA0 hlL
  -- `B_N → ∞`
  have hB : Tendsto (fun N : ℕ => A * (N * lL)) atTop atTop := by
    refine (tendsto_natCast_atTop_atTop.const_mul_atTop hAl).congr ?_
    intro N; ring
  -- `J_N / N → 1`
  have hlogb : Tendsto (fun N => Real.logb L (ℓs N)) atTop (𝓝 (Real.logb L ℓ)) := by
    simp only [Real.logb]; exact (hℓs.log hℓ.ne').div_const _
  have hJN0 : Tendsto (fun N : ℕ => ((J N : ℝ) - N) / N) atTop (𝓝 0) := by
    have hb := (tendsto_const_nhds (x := (1 : ℝ)).add hlogb.abs).div_atTop
      tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨hJ, -⟩ := h N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have f1 := Int.floor_le ((N : ℝ) + Real.logb L (ℓs N))
    have f2 := Int.lt_floor_add_one ((N : ℝ) + Real.logb L (ℓs N))
    rw [← hJ] at f1 f2
    push_cast at f1 f2
    have : |(J N : ℝ) - N| ≤ 1 + |Real.logb L (ℓs N)| := by
      rw [abs_le]
      have := abs_le.1 (le_refl |Real.logb L (ℓs N)|)
      constructor <;> linarith [neg_abs_le (Real.logb L (ℓs N)), le_abs_self (Real.logb L (ℓs N))]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN0]
    exact div_le_div_of_nonneg_right this hN0.le
  have hJN : Tendsto (fun N : ℕ => (J N : ℝ) / N) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add hJN0
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp; ring
  -- the error of `λ_N = (1/G_N)/B_N`
  have he1 : Tendsto (fun N : ℕ => (C₁ + C₂ * Real.log (A * (N * lL))) / (A * (N * lL)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have := (tendsto_const_nhds (x := C₁)).div_atTop hB |>.add
      ((h2.comp hB).const_mul C₂)
    rw [mul_zero, add_zero] at this
    refine this.congr ?_
    intro N; simp only [Function.comp]; ring
  set lam := fun N : ℕ => (1 / G N) / (A * (N * lL)) with hlamd
  set c := 3 / (2 * Real.pi) / A with hcd
  have hμ : Tendsto (fun N : ℕ => 1 - (J N : ℝ) / N * c) atTop (𝓝 (1 - 1 * c)) :=
    tendsto_const_nhds.sub (hJN.mul_const c)
  have hlm : Tendsto (fun N : ℕ => lam N - (1 - (J N : ℝ) / N * c)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ he1
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨-, hG, hX, -⟩ := h N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hBp : 0 < A * (N * lL) := by positivity
    have e : lam N - (1 - (J N : ℝ) / N * c) =
        (1 / G N - A * (N * lL) + J N * Step2.betaL L) / (A * (N * lL)) := by
      simp only [hlamd, hcd, Step2.betaL, ← hlLd]
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hBp]
    exact div_le_div_of_nonneg_right hX hBp.le
  have hlam : Tendsto lam atTop (𝓝 (1 - 3 / (2 * Real.pi * A))) := by
    have := hμ.add hlm
    rw [add_zero] at this
    have e : 1 - 1 * c = 1 - 3 / (2 * Real.pi * A) := by
      simp only [hcd]; field_simp
    rw [e] at this
    refine this.congr ?_
    intro N; ring
  have hpos : 0 < 1 - 3 / (2 * Real.pi * A) := by
    have : 3 / (2 * Real.pi * A) < 1 := by
      rw [div_lt_one (by positivity)]
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 hA
      linarith
    linarith
  have hθ := hlam.rpow_const (p := (2 / 3 : ℝ)) (Or.inl hpos.ne')
  -- `G_N → 0`
  have hG : Tendsto G atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hB).div hlam hpos.ne'
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨-, hG, -, -⟩ := h N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hBp : 0 < A * (N * lL) := by positivity
    simp only [hlamd, Pi.div_apply]
    field_simp
  have herr : Tendsto (fun N => K * lam N ^ (2 / 3 : ℝ) * G N) atTop (𝓝 0) := by
    have := (hθ.const_mul K).mul hG
    rwa [mul_zero] at this
  have hPθ : Tendsto (fun N => P N - lam N ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [eventually_ge_atTop N₁] with N hN
    obtain ⟨-, hG, -, hP⟩ := h N hN
    rw [Real.norm_eq_abs]
    refine hP.trans (le_of_eq ?_)
    simp only [hlamd]
    field_simp
  have := hθ.add hPθ
  rw [add_zero] at this
  refine this.congr ?_
  intro N; ring

end

end Spin2
