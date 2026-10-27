module

public import Mathlib

/-!
# Elementary part of the finite-size criterion (§9)

* `qFun A a R = min 1 (A exp(-a (log (2+R))²))`, the superpolynomial profile;
* `R^N qFun R → 0` (`eq:q-times-R`) and the choice of `R` with `(8R+4) p q ≤ 1/2`
  (`eq:eta-choice`);
* the abstract iteration giving `eq:exp-final`.
-/

@[expose] public section

namespace ArborealDecay.ExpDecay

open Filter Topology

/-- The superpolynomial profile `q_β(R) = min 1 (A exp(-a (log (2+R))²))`. -/
noncomputable def qFun (A a : ℝ) (R : ℕ) : ℝ :=
  min 1 (A * Real.exp (-a * Real.log (2 + (R : ℝ)) ^ 2))

theorem qFun_nonneg {A a : ℝ} (hA : 0 ≤ A) (R : ℕ) : 0 ≤ qFun A a R :=
  le_min zero_le_one (mul_nonneg hA (Real.exp_pos _).le)

theorem qFun_le_one (A a : ℝ) (R : ℕ) : qFun A a R ≤ 1 := min_le_left _ _

theorem qFun_le (A a : ℝ) (R : ℕ) :
    qFun A a R ≤ A * Real.exp (-a * Real.log (2 + (R : ℝ)) ^ 2) := min_le_right _ _

/-- `R^N q_β(R) → 0` (`eq:q-times-R`). -/
theorem tendsto_pow_mul_qFun {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (N : ℕ) :
    Tendsto (fun R : ℕ => (R : ℝ) ^ N * qFun A a R) atTop (𝓝 0) := by
  have hlog : Tendsto (fun R : ℕ => Real.log (2 + (R : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun t : ℝ => (N : ℝ) - a * t) atTop atBot := by
    have := (tendsto_id.const_mul_atTop ha : Tendsto (fun t : ℝ => a * t) atTop atTop)
    exact (tendsto_atBot_add_const_left atTop (N : ℝ) (tendsto_neg_atTop_atBot.comp this)).congr
      (fun t => by simp [sub_eq_add_neg])
  have h1 : Tendsto (fun t : ℝ => t * ((N : ℝ) - a * t)) atTop atBot :=
    Filter.Tendsto.atTop_mul_atBot₀ tendsto_id h0
  have h2 : Tendsto (fun R : ℕ => A * Real.exp (Real.log (2 + (R : ℝ)) *
      ((N : ℝ) - a * Real.log (2 + (R : ℝ))))) atTop (𝓝 (A * 0)) :=
    ((Real.tendsto_exp_atBot.comp (h1.comp hlog))).const_mul A
  rw [mul_zero] at h2
  refine squeeze_zero (fun R => mul_nonneg (by positivity) (qFun_nonneg hA R)) (fun R => ?_) h2
  have hpos : (0 : ℝ) < 2 + (R : ℝ) := by positivity
  have e : Real.exp (Real.log (2 + (R : ℝ)) * ((N : ℝ) - a * Real.log (2 + (R : ℝ)))) =
      (2 + (R : ℝ)) ^ N * Real.exp (-a * Real.log (2 + (R : ℝ)) ^ 2) := by
    rw [← Real.exp_log hpos, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_log hpos]
    congr 1; ring
  rw [e, ← mul_assoc, mul_comm A, mul_assoc]
  calc (R : ℝ) ^ N * qFun A a R ≤ (2 + (R : ℝ)) ^ N * (A * Real.exp (-a * Real.log (2 + (R : ℝ)) ^ 2)) := by
        refine mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _) (qFun_le A a R)
          (qFun_nonneg hA R) (by positivity)
    _ = _ := by ring

/-- Choice of `R` (`eq:eta-choice`): `(8R+4) p q_β(R) ≤ 1/2` for `0 ≤ p ≤ 1`. -/
theorem exists_eta_le_half {A a p : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hp1 : p ≤ 1) :
    ∃ R : ℕ, (8 * (R : ℝ) + 4) * p * qFun A a R ≤ 1 / 2 := by
  have h1 := tendsto_pow_mul_qFun hA ha 1
  have h0 := tendsto_pow_mul_qFun hA ha 0
  have h : Tendsto (fun R : ℕ => 8 * ((R : ℝ) ^ 1 * qFun A a R) + 4 * ((R : ℝ) ^ 0 * qFun A a R))
      atTop (𝓝 (8 * 0 + 4 * 0)) := (h1.const_mul 8).add (h0.const_mul 4)
  simp only [mul_zero, add_zero] at h
  obtain ⟨R, hR⟩ := (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  refine ⟨R, ?_⟩
  have hq := qFun_nonneg hA (a := a) R
  have : (8 * (R : ℝ) + 4) * qFun A a R ≤ 1 / 2 := by
    simp only [pow_one, pow_zero, one_mul] at hR; nlinarith
  calc (8 * (R : ℝ) + 4) * p * qFun A a R = p * ((8 * (R : ℝ) + 4) * qFun A a R) := by ring
    _ ≤ 1 * (1 / 2) := mul_le_mul hp1 this (by positivity) zero_le_one
    _ = 1 / 2 := by ring

/-- Abstract iteration of the one-step contraction `eq:one-step-contraction`. -/
theorem iterate_contraction {V : Type*} (d : V → V → ℕ)
    (hd : ∀ x y z, d x z ≤ d x y + d y z) (τ : V → V → ℝ) (R : ℕ) (η : ℝ)
    (hτ : ∀ x z, τ x z ≤ 1)
    (step : ∀ y z, R < d y z → ∀ M : ℝ, (∀ v, d y v ≤ R + 1 → τ v z ≤ M) → τ y z ≤ η * M) :
    ∀ (n : ℕ) (y z : V), n * (R + 1) ≤ d y z → τ y z ≤ η ^ n := by
  intro n
  induction n with
  | zero => intro y z _; simpa using hτ y z
  | succ n ih =>
    intro y z h
    have hR : R < d y z := by nlinarith
    rw [pow_succ', ]
    refine step y z hR _ fun v hv => ih v z ?_
    have := hd y v z
    rw [Nat.succ_mul] at h
    omega

theorem half_pow_div_le (R d : ℕ) :
    (1 / 2 : ℝ) ^ (d / (R + 1)) ≤ 2 * Real.exp (-(Real.log 2 / (R + 1)) * d) := by
  have hR : (0 : ℝ) < R + 1 := by positivity
  have h1 : d < (d / (R + 1) + 1) * (R + 1) := by
    have := Nat.lt_div_mul_add (a := d) (b := R + 1) (Nat.succ_pos R)
    nlinarith
  have h2 : (d : ℝ) < ((d / (R + 1) : ℕ) + 1) * (R + 1) := by exact_mod_cast h1
  have h3 : (d : ℝ) / (R + 1) < (d / (R + 1) : ℕ) + 1 := by
    rw [div_lt_iff₀ hR]; exact h2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : (1 / 2 : ℝ) ^ (d / (R + 1)) = Real.exp (-((d / (R + 1) : ℕ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div, inv_pow]
  rw [e1]
  calc Real.exp (-((d / (R + 1) : ℕ) * Real.log 2))
      ≤ Real.exp (Real.log 2 + -(Real.log 2 / (R + 1)) * d) := by
        apply Real.exp_le_exp.mpr
        have : Real.log 2 / (R + 1) * d = Real.log 2 * ((d : ℝ) / (R + 1)) := by ring
        nlinarith
    _ = 2 * Real.exp (-(Real.log 2 / (R + 1)) * d) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]

/-- `eq:exp-final`: from the one-step contraction with `η ≤ 1/2`, `0 ≤ η`,
`τ(x,z) ≤ 2 exp(-(log 2/(R+1)) d(x,z))`. -/
theorem decay_of_contraction {V : Type*} (d : V → V → ℕ)
    (hd : ∀ x y z, d x z ≤ d x y + d y z) (τ : V → V → ℝ) (R : ℕ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ : ∀ x z, τ x z ≤ 1)
    (step : ∀ y z, R < d y z → ∀ M : ℝ, (∀ v, d y v ≤ R + 1 → τ v z ≤ M) → τ y z ≤ η * M)
    (x z : V) :
    τ x z ≤ 2 * Real.exp (-(Real.log 2 / (R + 1)) * (d x z : ℝ)) := by
  have h := iterate_contraction d hd τ R η hτ step (d x z / (R + 1)) x z
    (Nat.div_mul_le_self _ _)
  exact h.trans ((pow_le_pow_left₀ hη0 hη _).trans (half_pow_div_le R (d x z)))

end ArborealDecay.ExpDecay
