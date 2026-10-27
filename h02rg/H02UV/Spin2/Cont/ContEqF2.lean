import Spin2.Cont.ContEqF1

set_option autoImplicit false

/-!
# B3, `r`-dependent form, final assembly (II): the modulus and the asymptotics in `d = N_h − ms`

* **`MasterFacts.eqf_cddRel_le`**: `cddRel(K_p, ǧ, a, ι, A, r) ≤ eqfKc·(ǧ + a + L^{−r})` for
  `0 ≤ ǧ ≤ 1`, `a ≥ 0`.
* **`eqf_wait_ev`**: `(3/4)^d·K·(αd + γ)² ≤ 1` eventually.
* **`eqf_beta_ev`**: `dβ − (T + a log(2(dβ + T + c'))) > 0` and its inverse `≤ ε` eventually
  (`log x ≤ 2√x`).
-/

namespace Spin2

open Step Step2 PtCorr2 Filter Topology

noncomputable section

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- The constant of the modulus. -/
def eqfKc (ι A : ℝ) : ℝ :=
  4 * M.Kp + 24 * (M.core.cδ * (M.core.c ^ 2 * (4 / betaL L))) +
    1344 * (8 * (PtCorr2.csN 2 : ℝ) * (64 * M.core.cWo * M.core.Bk * M.core.c ^ 2 + 24 * (ι * A)) +
      8 * (M.core.rdtΓ * (M.core.cWo * M.core.c))) + 1

/-- **`cddRel ≤ eqfKc·(ǧ + a + L^{−r})`.** -/
theorem eqf_cddRel_le {g z ι A : ℝ} (r : ℕ) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hz : 0 ≤ z)
    (hι : 0 ≤ ι) (hA : 0 ≤ A) (hc : 0 ≤ M.core.c) (hΓ : 0 ≤ M.core.rdtΓ) :
    M.cddRel M.Kp g z ι A r ≤ M.eqfKc ι A * (g + z + 1 / (L : ℝ) ^ r) := by
  have hcst := M.core.consts_nonneg
  have hcW : 1 ≤ M.core.cWo := hcst.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := hcst.2.2.2.2.2.2.1
  have hcδ : 0 ≤ M.core.cδ := hcst.2.2.2.2.2.2.2.1
  have hKp := M.Kp_nonneg
  have hβL := ct_betaL_pos M.ct_L2
  have hLr : (0 : ℝ) < (L : ℝ) ^ r := by
    have : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L)); positivity
  set e := 1 / (L : ℝ) ^ r with hed
  have he : 0 ≤ e := by positivity
  have he' : ι * A / (L : ℝ) ^ r = ι * A * e := by rw [hed]; field_simp
  have hg2 : (M.core.c * g) ^ 2 ≤ M.core.c ^ 2 * g := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by rw [sq]; exact mul_le_of_le_one_right hg hg1)
      (by positivity)
  unfold cddRel eqfKc
  rw [he']
  have e1 : g / (betaL L / 4) = 4 / betaL L * g := by field_simp
  rw [e1]
  set S := g + z + e
  have hgS : g ≤ S := by simp only [S]; linarith
  have hzS : g + z ≤ S := by simp only [S]; linarith
  have heS : e ≤ S := by simp only [S]; linarith
  have t1 : 4 * (M.Kp * (g + z)) ≤ 4 * M.Kp * S := by
    have := mul_le_mul_of_nonneg_left hzS hKp; linarith
  have t2 : 24 * (M.core.cδ * (M.core.c ^ 2 * (4 / betaL L * g))) ≤
      24 * (M.core.cδ * (M.core.c ^ 2 * (4 / betaL L))) * S := by
    have h0 : 0 ≤ 24 * (M.core.cδ * (M.core.c ^ 2 * (4 / betaL L))) := by positivity
    have := mul_le_mul_of_nonneg_left hgS h0
    have e : 24 * (M.core.cδ * (M.core.c ^ 2 * (4 / betaL L * g))) =
        24 * (M.core.cδ * (M.core.c ^ 2 * (4 / betaL L))) * g := by ring
    linarith
  have t3 : 64 * M.core.cWo * M.core.Bk * (M.core.c * g) ^ 2 ≤
      64 * M.core.cWo * M.core.Bk * M.core.c ^ 2 * S := by
    have h0 : 0 ≤ 64 * M.core.cWo * M.core.Bk := by positivity
    have := mul_le_mul_of_nonneg_left hg2 h0
    have := mul_le_mul_of_nonneg_left hgS (show 0 ≤ 64 * M.core.cWo * M.core.Bk * M.core.c ^ 2 by
      positivity)
    linarith
  have t4 : 24 * (ι * A * e) ≤ 24 * (ι * A) * S := by
    have := mul_le_mul_of_nonneg_left heS (show 0 ≤ 24 * (ι * A) by positivity); linarith
  have t5 : 8 * (M.core.rdtΓ * (M.core.cWo * (M.core.c * g))) ≤
      8 * (M.core.rdtΓ * (M.core.cWo * M.core.c)) * S := by
    have := mul_le_mul_of_nonneg_left hgS (show 0 ≤ 8 * (M.core.rdtΓ * (M.core.cWo * M.core.c)) by
      positivity)
    linarith
  have hN : 0 ≤ 8 * (PtCorr2.csN 2 : ℝ) := by positivity
  have t34 := mul_le_mul_of_nonneg_left (add_le_add t3 t4) hN
  have t345 := mul_le_mul_of_nonneg_left (add_le_add t34 t5) (by norm_num : (0 : ℝ) ≤ 1344)
  linarith

end MasterFacts

/-- **The waiting condition holds for large `d`.** -/
theorem eqf_wait_ev (K α γ : ℝ) : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (3 / 4 : ℝ) ^ d * K * (α * d + γ) ^ 2 ≤ 1 := by
  have hr : |(3 / 4 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hr
  have hT : Tendsto (fun d : ℕ => (3 / 4 : ℝ) ^ d * K * (α * d + γ) ^ 2) atTop (𝓝 0) := by
    have := ((h2.const_mul (K * α ^ 2)).add (h1.const_mul (K * (2 * α * γ)))).add
      (h0.const_mul (K * γ ^ 2))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun d => ?_
    ring
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.1 (hT.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  exact ⟨d₀, hd₀⟩

/-- **The coupling at distance `d` below `N_h` is small for large `d`.** -/
theorem eqf_beta_ev {β T a c' ε : ℝ} (hβ : 0 < β) (hT : 0 ≤ T) (ha : 0 ≤ a) (hc' : 0 ≤ c')
    (hε : 0 < ε) : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    0 < d * β - (T + a * Real.log (2 * (d * β + T + c'))) ∧
      1 / (d * β - (T + a * Real.log (2 * (d * β + T + c')))) ≤ ε := by
  set U := max (max (T + c') (256 * a ^ 2)) (max (4 * T) (max (2 / ε) 1)) with hUd
  refine ⟨⌈U / β⌉₊, fun d hd => ?_⟩
  set u := (d : ℝ) * β with hud
  have hu : U ≤ u := by
    have h1 : U / β ≤ d := (Nat.le_ceil _).trans (by exact_mod_cast hd)
    rw [div_le_iff₀ hβ] at h1; exact h1
  have hu1 : T + c' ≤ u := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hu
  have hu2 : 256 * a ^ 2 ≤ u := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hu
  have hu3 : 4 * T ≤ u := (le_max_left _ _ |>.trans (le_max_right _ _)).trans hu
  have hu4 : 2 / ε ≤ u :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hu
  have hu5 : 1 ≤ u :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hu
  have hu0 : 0 < u := by linarith
  set x := 2 * (u + T + c') with hxd
  have hx0 : 0 ≤ x := by positivity
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have := Real.log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hsx : Real.sqrt x ≤ 2 * Real.sqrt u := by
    have : x ≤ 4 * u := by rw [hxd]; linarith
    calc Real.sqrt x ≤ Real.sqrt (4 * u) := Real.sqrt_le_sqrt this
      _ = 2 * Real.sqrt u := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsu : 16 * a ≤ Real.sqrt u := by
    rw [Real.le_sqrt (by positivity) hu0.le]; nlinarith
  have hsuu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have h4 : a * Real.log x ≤ u / 4 := by
    have h1 : a * Real.log x ≤ a * (2 * (2 * Real.sqrt u)) :=
      mul_le_mul_of_nonneg_left (hlog.trans (by linarith)) ha
    have h2 : 16 * a * Real.sqrt u ≤ Real.sqrt u * Real.sqrt u :=
      mul_le_mul_of_nonneg_right hsu (Real.sqrt_nonneg _)
    nlinarith
  have hf : u / 2 ≤ u - (T + a * Real.log x) := by linarith
  refine ⟨by linarith, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  have : 2 ≤ ε * u := by rw [div_le_iff₀ hε] at hu4; linarith
  nlinarith

end

end Spin2
