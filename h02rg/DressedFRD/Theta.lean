import Mathlib

/-!
# The choice of `ζ̄`

`exists_theta` produces `θ = ζ̄` satisfying the finitely many smallness conditions used in the
proof of `thm:main`. Each condition is of the form `θ^a ≤ ε` with `a > 0`, which holds for small
`θ > 0`.
-/

namespace DressedFRD

open Filter Topology

theorem eventually_rpow_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ^ a ≤ ε := by
  have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact (h.mono_left nhdsWithin_le_nhds).eventually (eventually_le_nhds hε)

theorem eventually_pos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin

/-- The smallness conditions on `θ = ζ̄`. -/
structure Good (L c c₂ Cρ θ : ℝ) : Prop where
  pos : 0 < θ
  le8 : θ ≤ 1 / 8
  quarter : θ ^ ((6 : ℝ) / 256) ≤ 1 / 4
  absorb : Real.sqrt (2 * θ) ≤ L ^ (-c)
  geom : Real.sqrt (2 * θ) * (2 * θ ^ (-(3 : ℝ) / 256)) ≤ 1 / 2
  small : Cρ * (2 * (2 * L ^ c * (2 * c₂ * θ ^ (-(6 : ℝ) / 256) + 12 * θ ^ (-(5 : ℝ) / 256)))) * θ ≤ 1

theorem exists_theta (L c c₂ Cρ : ℝ) (hL : 0 < L) (hc₂ : 0 ≤ c₂) (hCρ : 0 ≤ Cρ) :
    ∃ θ, Good L c c₂ Cρ θ := by
  have hLc : 0 < L ^ (-c) := Real.rpow_pos_of_pos hL _
  -- `√(2θ) = √2 θ^{1/2}`
  have hsq : ∀ θ : ℝ, 0 < θ → Real.sqrt (2 * θ) = Real.sqrt 2 * θ ^ ((1 : ℝ) / 2) := by
    intro θ hθ
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow θ]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  set A := 2 * L ^ c * (2 * c₂) with hA
  set B := 2 * L ^ c * 12 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have e1 := eventually_rpow_le (a := (6 : ℝ) / 256) (ε := 1 / 4) (by norm_num) (by norm_num)
  have e2 := eventually_rpow_le (a := (1 : ℝ) / 2) (ε := L ^ (-c) / Real.sqrt 2) (by norm_num)
    (by positivity)
  have e3 := eventually_rpow_le (a := (1 : ℝ) / 2 - 3 / 256) (ε := 1 / (4 * Real.sqrt 2))
    (by norm_num) (by positivity)
  have e4 := eventually_rpow_le (a := 1 - (6 : ℝ) / 256)
    (ε := 1 / (4 * (Cρ * A + Cρ * B) + 1)) (by norm_num) (by positivity)
  have e5 := eventually_rpow_le (a := 1 - (5 : ℝ) / 256)
    (ε := 1 / (4 * (Cρ * A + Cρ * B) + 1)) (by norm_num) (by positivity)
  have e6 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ≤ 1 / 8 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8)).filter_mono nhdsWithin_le_nhds
  obtain ⟨θ, hθ, h1, h2', h3, h4, h5, h6⟩ :=
    (eventually_pos.and (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))).exists
  refine ⟨θ, hθ, h6, h1, ?_, ?_, ?_⟩
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
  · have e6' : θ ^ (-(6 : ℝ) / 256) * θ = θ ^ (1 - (6 : ℝ) / 256) := by
      rw [show (1 : ℝ) - 6 / 256 = -(6 : ℝ) / 256 + 1 by ring, Real.rpow_add hθ, Real.rpow_one]
    have e5' : θ ^ (-(5 : ℝ) / 256) * θ = θ ^ (1 - (5 : ℝ) / 256) := by
      rw [show (1 : ℝ) - 5 / 256 = -(5 : ℝ) / 256 + 1 by ring, Real.rpow_add hθ, Real.rpow_one]
    have hD : 0 < 4 * (Cρ * A + Cρ * B) + 1 := by positivity
    have h4' : θ ^ (1 - (6 : ℝ) / 256) * (4 * (Cρ * A + Cρ * B) + 1) ≤ 1 := by
      rwa [le_div_iff₀ hD] at h4
    have h5' : θ ^ (1 - (5 : ℝ) / 256) * (4 * (Cρ * A + Cρ * B) + 1) ≤ 1 := by
      rwa [le_div_iff₀ hD] at h5
    have p6 : 0 ≤ θ ^ (1 - (6 : ℝ) / 256) := Real.rpow_nonneg hθ.le _
    have p5 : 0 ≤ θ ^ (1 - (5 : ℝ) / 256) := Real.rpow_nonneg hθ.le _
    calc Cρ * (2 * (2 * L ^ c * (2 * c₂ * θ ^ (-(6 : ℝ) / 256) + 12 * θ ^ (-(5 : ℝ) / 256)))) * θ
        = 2 * (Cρ * A) * (θ ^ (-(6 : ℝ) / 256) * θ) + 2 * (Cρ * B) * (θ ^ (-(5 : ℝ) / 256) * θ) := by
          simp only [hA, hB]; ring
      _ = 2 * (Cρ * A) * θ ^ (1 - (6 : ℝ) / 256) + 2 * (Cρ * B) * θ ^ (1 - (5 : ℝ) / 256) := by
          rw [e6', e5']
      _ ≤ 1 := by
          have hCA : 0 ≤ Cρ * A := mul_nonneg hCρ hA0
          have hCB : 0 ≤ Cρ * B := mul_nonneg hCρ hB0
          nlinarith

end DressedFRD
