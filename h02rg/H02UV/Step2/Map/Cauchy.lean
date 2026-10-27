import Step2.Map.Exp
import Step.Deriv

/-!
# Cauchy estimates for the second-order step

One-variable estimates by the maximum modulus principle, for a linear functional `λ` of a
coefficient-wise holomorphic `f : ℂ → 𝒩` bounded by `B` on a circle of radius `R ≥ 1`:

* `rem3_le`: if `f(t) = t² F₂ + O(t³)` (`ExpE2 f 0 0 F₂`), then `|λ(f(1) - F₂)| ≤ 2B/R³`;
* `rem2_le`: if `f(s) = s F₁ + O(s²)` (`ExpE1 f 0 F₁`), then `|λ(f(1) - F₁)| ≤ 2B/R²`;
* `mixed_le`: for `F(t, s)` holomorphic in each variable and bounded by `B` on the closed
  polydisc of radii `R₁, R₂ ≥ 1`, `|λ(F(1,1) - F(1,0) - F(0,1) + F(0,0))| ≤ 4B/(R₁R₂)`;

and the choice of the radii (`rad1`, `rad2`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Metric

/-! ### Scalar estimates -/

theorem mm_le {h : ℂ → ℂ} (hh : Differentiable ℂ h) {R B : ℝ} (hR : 0 < R)
    (hB : ∀ ζ : ℂ, ‖ζ‖ = R → ‖h ζ‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ R) : ‖h z‖ ≤ B := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
    isBounded_ball hh.diffContOnCl (fun ζ hζ => hB ζ ?_) ?_
  · rw [frontier_ball (0 : ℂ) hR.ne'] at hζ; simpa using hζ
  · rw [closure_ball (0 : ℂ) hR.ne']; simpa using hz

/-- If `φ(t) = tⁿ k(t)` with `k` entire and `|φ| ≤ B` on `|t| = R`, then `|k| ≤ B/Rⁿ` on the
disc. -/
theorem coeff_le {φ k : ℂ → ℂ} {n : ℕ} (hk : Differentiable ℂ k) (he : ∀ t, φ t = t ^ n * k t)
    {R B : ℝ} (hR : 0 < R) (hB : ∀ ζ : ℂ, ‖ζ‖ = R → ‖φ ζ‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖k z‖ ≤ B / R ^ n := by
  refine mm_le hk hR (fun ζ hζ => ?_) hz
  have h := hB ζ hζ
  rw [he, norm_mul, norm_pow, hζ] at h
  rw [le_div_iff₀ (pow_pos hR n), mul_comm]; exact h

/-! ### Estimates for Grassmann-valued maps -/

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem OrdE.pair {n : ℕ} {f : ℂ → EvR I} (h : OrdE n f) (Λf : Grassmann.N I →ₗ[ℂ] ℂ) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ t, Λf (f t : Grassmann.N I) = t ^ n * k t := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨fun t => Λf (g t : Grassmann.N I), hg.lin Λf, fun t => ?_⟩
  rw [e, Subalgebra.coe_smul, map_smul, smul_eq_mul]

/-- The third-order remainder. -/
theorem rem3_le {f : ℂ → EvR I} {F₂ : EvR I} (h : ExpE2 f 0 0 F₂) (Λf : Grassmann.N I →ₗ[ℂ] ℂ)
    {R B : ℝ} (hR : 1 ≤ R) (hB : ∀ ζ : ℂ, ‖ζ‖ = R → ‖Λf (f ζ : Grassmann.N I)‖ ≤ B) :
    ‖Λf (f 1 : Grassmann.N I) - Λf (F₂ : Grassmann.N I)‖ ≤ 2 * B / R ^ 3 := by
  have hR0 : 0 < R := by linarith
  obtain ⟨k, hk, e⟩ := OrdE.pair h Λf
  have e' : ∀ t, Λf (f t : Grassmann.N I) - t ^ 2 * Λf (F₂ : Grassmann.N I) = t ^ 3 * k t := by
    intro t
    rw [← e]
    simp only [zero_add, zero_smul, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      Subalgebra.coe_smul, map_sub, map_add, map_smul, smul_eq_mul, ZeroMemClass.coe_zero,
      map_zero, mul_zero, add_zero, zero_add]
  -- `|λ F₂| ≤ B/R²`
  have hF₂ : ‖Λf (F₂ : Grassmann.N I)‖ ≤ B / R ^ 2 := by
    have := coeff_le (φ := fun t => Λf (f t : Grassmann.N I))
      (k := fun t => Λf (F₂ : Grassmann.N I) + t * k t) (n := 2)
      ((differentiable_const _).add (differentiable_id.mul hk))
      (fun t => by rw [mul_add, ← mul_assoc, ← pow_succ, ← e' t]; ring) hR0 hB
      (z := 0) (by simp; linarith)
    simpa using this
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hB R (by simp; linarith))
    exact this
  have h1 := coeff_le hk e' hR0 (B := 2 * B) (fun ζ hζ => by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_pow, hζ]
    have : R ^ 2 * ‖Λf (F₂ : Grassmann.N I)‖ ≤ B := by
      rw [le_div_iff₀ (by positivity)] at hF₂; linarith
    linarith [hB ζ hζ]) (z := 1) (by simp; linarith)
  have := e' 1
  rw [one_pow, one_mul, one_pow, one_mul] at this
  rw [this]; exact h1

/-- The second-order remainder. -/
theorem rem2_le {f : ℂ → EvR I} {F₁ : EvR I} (h : ExpE1 f 0 F₁) (Λf : Grassmann.N I →ₗ[ℂ] ℂ)
    {R B : ℝ} (hR : 1 ≤ R) (hB : ∀ ζ : ℂ, ‖ζ‖ = R → ‖Λf (f ζ : Grassmann.N I)‖ ≤ B) :
    ‖Λf (f 1 : Grassmann.N I) - Λf (F₁ : Grassmann.N I)‖ ≤ 2 * B / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  obtain ⟨k, hk, e⟩ := OrdE.pair h Λf
  have e' : ∀ t, Λf (f t : Grassmann.N I) - t * Λf (F₁ : Grassmann.N I) = t ^ 2 * k t := by
    intro t
    rw [← e]
    simp only [zero_add, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      Subalgebra.coe_smul, map_sub, map_add, map_smul, smul_eq_mul, ZeroMemClass.coe_zero,
      map_zero]
  have hF₁ : ‖Λf (F₁ : Grassmann.N I)‖ ≤ B / R ^ 1 := by
    have := coeff_le (φ := fun t => Λf (f t : Grassmann.N I))
      (k := fun t => Λf (F₁ : Grassmann.N I) + t * k t) (n := 1)
      ((differentiable_const _).add (differentiable_id.mul hk))
      (fun t => by
        have := e' t
        rw [pow_two] at this
        linear_combination this) hR0 hB
      (z := 0) (by simp; linarith)
    simpa using this
  have h1 := coeff_le hk e' hR0 (B := 2 * B) (fun ζ hζ => by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, hζ]
    have : R * ‖Λf (F₁ : Grassmann.N I)‖ ≤ B := by
      rw [pow_one, le_div_iff₀ hR0] at hF₁; linarith
    linarith [hB ζ hζ]) (z := 1) (by simp; linarith)
  have := e' 1
  rw [one_mul, one_pow, one_mul] at this
  rw [this]; exact h1

/-- The mixed term. -/
theorem mixed_le {F : ℂ → ℂ → EvR I} (hF1 : ∀ s, HolE (fun t => F t s))
    (hF2 : ∀ t, HolE (fun s => F t s)) (Λf : Grassmann.N I →ₗ[ℂ] ℂ) {R₁ R₂ B : ℝ}
    (hR₁ : 1 ≤ R₁) (hR₂ : 1 ≤ R₂)
    (hB : ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λf (F t s : Grassmann.N I)‖ ≤ B) :
    ‖Λf (F 1 1 : Grassmann.N I) - Λf (F 1 0 : Grassmann.N I) - Λf (F 0 1 : Grassmann.N I) +
      Λf (F 0 0 : Grassmann.N I)‖ ≤ 4 * B / (R₁ * R₂) := by
  have hR₁0 : 0 < R₁ := by linarith
  have hR₂0 : 0 < R₂ := by linarith
  set G : ℂ → ℂ → ℂ := fun t s => Λf (F t s : Grassmann.N I) - Λf (F t 0 : Grassmann.N I) -
    Λf (F 0 s : Grassmann.N I) + Λf (F 0 0 : Grassmann.N I) with hG
  have h4 : ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖G t s‖ ≤ 4 * B := by
    intro t s ht hs
    have h0 : ‖(0 : ℂ)‖ ≤ R₁ := by simp; linarith
    have h0' : ‖(0 : ℂ)‖ ≤ R₂ := by simp; linarith
    have := norm_add_le (Λf (F t s : Grassmann.N I) - Λf (F t 0 : Grassmann.N I) -
      Λf (F 0 s : Grassmann.N I)) (Λf (F 0 0 : Grassmann.N I))
    have := norm_sub_le (Λf (F t s : Grassmann.N I) - Λf (F t 0 : Grassmann.N I))
      (Λf (F 0 s : Grassmann.N I))
    have := norm_sub_le (Λf (F t s : Grassmann.N I)) (Λf (F t 0 : Grassmann.N I))
    linarith [hB t s ht hs, hB t 0 ht h0', hB 0 s h0 hs, hB 0 0 h0 h0']
  -- in `t`, for fixed `s`
  have hstep1 : ∀ s : ℂ, ‖s‖ ≤ R₂ → ‖G 1 s‖ ≤ 4 * B / R₁ := by
    intro s hs
    have hd : Differentiable ℂ (fun t => G t s) :=
      ((((hF1 s).lin Λf).sub ((hF1 0).lin Λf)).sub (differentiable_const _)).add
        (differentiable_const _)
    obtain ⟨k, hk, e⟩ := OrdS.one_of_zero hd (by simp [hG])
    have := coeff_le hk e hR₁0 (fun ζ hζ => h4 ζ s hζ.le hs) (z := 1) (by simp; linarith)
    have e1 : G 1 s = k 1 := by simpa using e 1
    rw [e1]; simpa using this
  have hd : Differentiable ℂ (fun s => G 1 s) :=
    ((((hF2 1).lin Λf).sub (differentiable_const _)).sub ((hF2 0).lin Λf)).add
      (differentiable_const _)
  obtain ⟨k, hk, e⟩ := OrdS.one_of_zero hd (by simp [hG])
  have := coeff_le hk e hR₂0 (fun ζ hζ => hstep1 ζ hζ.le) (z := 1) (by simp; linarith)
  have e1 : G 1 1 = k 1 := by simpa using e 1
  show ‖G 1 1‖ ≤ _
  rw [e1]
  refine this.trans (le_of_eq ?_)
  rw [pow_one, div_div]

/-! ### Choosing the radii -/

theorem rad1 {X c g ρ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hc : 0 ≤ c) (hρ : 0 < ρ) (hg : 0 ≤ g)
    (hgρ : g ≤ ρ) (h : ∀ R : ℝ, 1 ≤ R → R * g ≤ ρ → X ≤ c / R ^ n) : X ≤ c * (g / ρ) ^ n := by
  rcases hg.eq_or_lt with rfl | hg0
  · have : X ≤ 0 := le_zero_of_forall_le_div hc 1 fun R hR hR0 => by
      refine (h R hR (by simp; linarith)).trans ?_
      have : R ≤ R ^ n := by
        calc R = R ^ 1 := (pow_one R).symm
          _ ≤ R ^ n := pow_le_pow_right₀ hR hn
      exact div_le_div_of_nonneg_left hc hR0 this
    rw [zero_div, zero_pow (by omega), mul_zero]; exact this
  · have hR : 1 ≤ ρ / g := by rw [le_div_iff₀ hg0]; linarith
    have := h (ρ / g) hR (by field_simp; rfl)
    calc X ≤ c / (ρ / g) ^ n := this
      _ = c * (g / ρ) ^ n := by rw [div_pow, div_pow]; field_simp

theorem rad2 {X c g k ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ) (hg : 0 ≤ g) (hgρ : g ≤ ρ) (hk : 0 ≤ k)
    (hkρ : k ≤ ρ)
    (h : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ → X ≤ c / (R₁ * R₂)) :
    X ≤ c * (g / ρ) * (k / ρ) := by
  have h1 : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → X ≤ c * (k / ρ) / R₁ ^ 1 := by
    intro R₁ hR₁ hR₁g
    have hR₁0 : 0 < R₁ := by linarith
    have := rad1 (n := 1) le_rfl (div_nonneg hc hR₁0.le) hρ hk hkρ fun R₂ hR₂ hR₂k => by
      rw [pow_one, div_div]; exact h R₁ hR₁ hR₁g R₂ hR₂ hR₂k
    rw [pow_one] at this ⊢
    calc X ≤ c / R₁ * (k / ρ) := this
      _ = c * (k / ρ) / R₁ := by ring
  have := rad1 (n := 1) le_rfl (by positivity) hρ hg hgρ h1
  rw [pow_one] at this
  linarith [show c * (k / ρ) * (g / ρ) = c * (g / ρ) * (k / ρ) by ring]

end

end Step2
