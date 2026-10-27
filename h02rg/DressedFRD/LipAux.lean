import DressedFRD.StepR
import DressedFRD.Holo

/-!
# Auxiliary results for the Lipschitz bound with decay (`DressedFRD/LipDecay.lean`)

* `exists_theta_lip`: a choice of `θ = ζ̄` satisfying `Good` and in addition
  `θ^{6/256} ≤ ρ/2`, `C_ρ K₁ θ ≤ ρ/16`, for a prescribed ratio `0 < ρ ≤ 1/2`.
* `sum_lip_of_hol`: the Schwarz lemma for weighted `ℓ¹` sums. If `t ↦ F t` is holomorphic for
  `|t| c < 1` and `∑_x w_x |F t x - F 0 x| ≤ M` for `|t| c ≤ 1` and for `t = 1`, then
  `∑_x w_x |F 1 x - F 0 x| ≤ M c`.

The proof of the decay applies `sum_lip_of_hol` to the one-step map `(ζ_i, W_i) ↦ w^{(i)}`
(`Data.Elt_le`), not to `C'_{j+1}` as a function of all past couplings: Cauchy estimates for the
latter only give `K max_k |ζ_k - ζ'_k|`, since the words of step `i` at scale `j + 1` are of size
`θ^{L^{j-i}/256}` but their `ζ_k`-derivative, `k < i`, is not smaller by a factor decaying in
`j - k` by itself. The decay comes from the contraction of the weighted tails along the flow.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD Filter Topology Metric

/-! ### The choice of `θ` -/

/-- `exists_theta` with the additional conditions `θ^{6/256} ≤ ρ/2` and
`C_ρ K₁ θ ≤ ρ/16`. -/
theorem exists_theta_lip (L c c₂ Cρ ρ : ℝ) (hL : 0 < L) (hc₂ : 0 ≤ c₂) (hCρ : 0 ≤ Cρ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ θ, Good L c c₂ Cρ θ ∧ θ ^ ((6 : ℝ) / 256) ≤ ρ / 2 ∧ Cρ * Data.K1 L c c₂ θ * θ ≤ ρ / 16 := by
  have hLc : 0 < L ^ (-c) := Real.rpow_pos_of_pos hL _
  have hsq : ∀ θ : ℝ, 0 < θ → Real.sqrt (2 * θ) = Real.sqrt 2 * θ ^ ((1 : ℝ) / 2) := by
    intro θ hθ
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow θ]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  set A := 2 * L ^ c * (2 * c₂) with hA
  set B := 2 * L ^ c * 12 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have e1 := eventually_rpow_le (a := (6 : ℝ) / 256) (ε := ρ / 2) (by norm_num) (by positivity)
  have e2 := eventually_rpow_le (a := (1 : ℝ) / 2) (ε := L ^ (-c) / Real.sqrt 2) (by norm_num)
    (by positivity)
  have e3 := eventually_rpow_le (a := (1 : ℝ) / 2 - 3 / 256) (ε := 1 / (4 * Real.sqrt 2))
    (by norm_num) (by positivity)
  have e4 := eventually_rpow_le (a := 1 - (6 : ℝ) / 256)
    (ε := ρ / (64 * (Cρ * A + Cρ * B) + 1)) (by norm_num) (by positivity)
  have e5 := eventually_rpow_le (a := 1 - (5 : ℝ) / 256)
    (ε := ρ / (64 * (Cρ * A + Cρ * B) + 1)) (by norm_num) (by positivity)
  have e6 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ≤ 1 / 8 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8)).filter_mono nhdsWithin_le_nhds
  obtain ⟨θ, hθ, h1, h2', h3, h4, h5, h6⟩ :=
    (eventually_pos.and (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))).exists
  have e6' : θ ^ (-(6 : ℝ) / 256) * θ = θ ^ (1 - (6 : ℝ) / 256) := by
    rw [show (1 : ℝ) - 6 / 256 = -(6 : ℝ) / 256 + 1 by ring, Real.rpow_add hθ, Real.rpow_one]
  have e5' : θ ^ (-(5 : ℝ) / 256) * θ = θ ^ (1 - (5 : ℝ) / 256) := by
    rw [show (1 : ℝ) - 5 / 256 = -(5 : ℝ) / 256 + 1 by ring, Real.rpow_add hθ, Real.rpow_one]
  have hD : 0 < 64 * (Cρ * A + Cρ * B) + 1 := by positivity
  have h4' : θ ^ (1 - (6 : ℝ) / 256) * (64 * (Cρ * A + Cρ * B) + 1) ≤ ρ := by
    rwa [le_div_iff₀ hD] at h4
  have h5' : θ ^ (1 - (5 : ℝ) / 256) * (64 * (Cρ * A + Cρ * B) + 1) ≤ ρ := by
    rwa [le_div_iff₀ hD] at h5
  have p6 : 0 ≤ θ ^ (1 - (6 : ℝ) / 256) := Real.rpow_nonneg hθ.le _
  have p5 : 0 ≤ θ ^ (1 - (5 : ℝ) / 256) := Real.rpow_nonneg hθ.le _
  have hCA : 0 ≤ Cρ * A := mul_nonneg hCρ hA0
  have hCB : 0 ≤ Cρ * B := mul_nonneg hCρ hB0
  have hK : Cρ * Data.K1 L c c₂ θ * θ =
      Cρ * A * θ ^ (1 - (6 : ℝ) / 256) + Cρ * B * θ ^ (1 - (5 : ℝ) / 256) := by
    rw [← e6', ← e5']; simp only [Data.K1, hA, hB]; ring
  have hKs : Cρ * Data.K1 L c c₂ θ * θ ≤ ρ / 64 := by
    rw [hK]; nlinarith
  refine ⟨θ, ⟨hθ, h6, h1.trans (by linarith), ?_, ?_, ?_⟩, h1, by linarith⟩
  · rw [hsq θ hθ]
    rw [le_div_iff₀ h2] at h2'
    linarith
  · rw [hsq θ hθ]
    have : θ ^ ((1 : ℝ) / 2) * θ ^ (-(3 : ℝ) / 256) = θ ^ ((1 : ℝ) / 2 - 3 / 256) := by
      rw [← Real.rpow_add hθ]; ring_nf
    have h3' : θ ^ ((1 : ℝ) / 2 - 3 / 256) * (4 * Real.sqrt 2) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at h3
    calc Real.sqrt 2 * θ ^ ((1 : ℝ) / 2) * (2 * θ ^ (-(3 : ℝ) / 256))
        = 2 * Real.sqrt 2 * (θ ^ ((1 : ℝ) / 2) * θ ^ (-(3 : ℝ) / 256)) := by ring
      _ = 2 * Real.sqrt 2 * θ ^ ((1 : ℝ) / 2 - 3 / 256) := by rw [this]
      _ ≤ 1 / 2 := by nlinarith
  · have : Cρ * (2 * (2 * L ^ c * (2 * c₂ * θ ^ (-(6 : ℝ) / 256) + 12 * θ ^ (-(5 : ℝ) / 256)))) * θ
        = 2 * (Cρ * Data.K1 L c c₂ θ * θ) := by simp only [Data.K1]; ring
    rw [this]; linarith

/-! ### A Schwarz-lemma bound for weighted `ℓ¹` sums -/

/-- The phase `z̄/|z|` (and `0` at `0`). -/
def phase (z : ℂ) : ℂ := if z = 0 then 0 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

theorem norm_phase_le (z : ℂ) : ‖phase z‖ ≤ 1 := by
  unfold phase
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (norm_ne_zero_iff.2 h)]

theorem phase_mul (z : ℂ) : phase z * z = (‖z‖ : ℂ) := by
  unfold phase
  split_ifs with h
  · simp [h]
  · have h' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
    rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff h']; ring

/-- If `t ↦ F t` is holomorphic for `|t| c < 1`, and `∑ c_x |F t x - F 0 x| ≤ M` for `|t| c ≤ 1`
and at `t = 1`, then `∑ c_x |F 1 x - F 0 x| ≤ M c`. -/
theorem sum_lip_of_hol {ι : Type*} (S : Finset ι) (w : ι → ℝ) (hw : ∀ x ∈ S, 0 ≤ w x)
    (F : ℂ → ι → ℂ) {c M : ℝ} (hc : 0 ≤ c)
    (hd : ∀ x ∈ S, ∀ t : ℂ, ‖t‖ * c < 1 → DifferentiableAt ℂ (fun t => F t x) t)
    (hM : ∀ t : ℂ, ‖t‖ * c ≤ 1 → ∑ x ∈ S, w x * ‖F t x - F 0 x‖ ≤ M)
    (hM1 : ∑ x ∈ S, w x * ‖F 1 x - F 0 x‖ ≤ M) :
    ∑ x ∈ S, w x * ‖F 1 x - F 0 x‖ ≤ M * c := by
  set X := ∑ x ∈ S, w x * ‖F 1 x - F 0 x‖
  have hX0 : 0 ≤ X := sum_nonneg fun x hx => mul_nonneg (hw x hx) (norm_nonneg _)
  have hM0 : 0 ≤ M := le_trans (by simp) (hM 0 (by simp))
  -- the scalar function
  set g : ℂ → ℂ := fun t => ∑ x ∈ S, ((w x : ℂ) * phase (F 1 x - F 0 x)) * (F t x - F 0 x)
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = (X : ℂ) := by
    simp only [g, X]; push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [mul_assoc, phase_mul]
  have hgle : ∀ t, ‖t‖ * c ≤ 1 → ‖g t‖ ≤ M := by
    intro t ht
    refine (norm_sum_le _ _).trans ((sum_le_sum fun x hx => ?_).trans (hM t ht))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw x hx)]
    have := norm_phase_le (F 1 x - F 0 x)
    have := hw x hx
    have := norm_nonneg (F t x - F 0 x)
    nlinarith [mul_nonneg (hw x hx) (norm_nonneg (F t x - F 0 x))]
  have hgd : ∀ t : ℂ, ‖t‖ * c < 1 → DifferentiableAt ℂ g t := by
    intro t ht
    exact DifferentiableAt.fun_sum fun x hx =>
      ((hd x hx t ht).sub_const _).const_mul _
  -- Schwarz on the disc of radius `T`
  have key : ∀ T : ℝ, 1 < T → T * c ≤ 1 → X ≤ M / T := by
    intro T hT hTc
    have hT0 : 0 < T := by linarith
    have hball : ∀ t ∈ ball (0 : ℂ) T, ‖t‖ * c < 1 ∨ c = 0 := by
      intro t ht
      rw [mem_ball, dist_zero_right] at ht
      rcases hc.lt_or_eq with h | h
      · left; nlinarith
      · right; exact h.symm
    have hdiff : DifferentiableOn ℂ g (ball 0 T) := fun t ht => by
      rcases hball t ht with h | h
      · exact (hgd t h).differentiableWithinAt
      · exact (hgd t (by rw [h]; simp)).differentiableWithinAt
    have hmaps : Set.MapsTo g (ball 0 T) (closedBall (g 0) M) := by
      intro t ht
      rw [mem_closedBall, hg0, dist_zero_right]
      rcases hball t ht with h | h
      · exact hgle t h.le
      · exact hgle t (by rw [h]; simp)
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) T := by rw [mem_ball, dist_zero_right]; simpa using hT
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps h1
    rw [hg1, hg0, dist_zero_right, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hX0,
      norm_one, mul_one] at this
    exact this
  rcases lt_or_ge c 1 with hc1 | hc1
  · rcases hc.lt_or_eq with hcp | hc0
    · have := key c⁻¹ (by rw [lt_inv_comm₀ one_pos hcp]; simpa using hc1)
        (by rw [inv_mul_cancel₀ hcp.ne'])
      rwa [div_inv_eq_mul] at this
    · -- `c = 0`: `X ≤ M/T` for all `T > 1`
      rw [← hc0, mul_zero]
      by_contra hXpos
      push Not at hXpos
      have hpos : 0 < (M + 1) / X := by positivity
      have := key ((M + 1) / X + 1) (by linarith) (by rw [← hc0, mul_zero]; norm_num)
      have hT : 0 < (M + 1) / X + 1 := by positivity
      rw [le_div_iff₀ hT] at this
      have : X * ((M + 1) / X + 1) = M + 1 + X := by field_simp
      nlinarith
  · calc X ≤ M := hM1
      _ ≤ M * c := le_mul_of_one_le_right hM0 hc1

end

end DressedFRD
