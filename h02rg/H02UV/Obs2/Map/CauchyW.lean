import Obs2.Map.OrdW
import Step2.Map.Cauchy

/-!
# Cauchy estimates in a finite-dimensional algebra (`Step2.Map.Cauchy` for `HolW`)

For a linear functional `λ` of a weakly holomorphic `f : ℂ → R` bounded by `B` on a circle of
radius `R ≥ 1`: `rem3W_le` (`f = t² F₂ + O(t³)`), `rem2W_le` (`f = s F₁ + O(s²)`) and `mixedW_le`
(the mixed difference of a function of two variables), with the same constants as
`Step2.rem3_le`, `rem2_le`, `mixed_le`.
-/

namespace Obs2

noncomputable section

open Finset Step Step2

variable {R : Type*} [CommRing R] [Algebra ℂ R] [FiniteDimensional ℂ R]

theorem OrdW.pair {n : ℕ} {f : ℂ → R} (h : OrdW n f) (Λf : R →ₗ[ℂ] ℂ) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ t, Λf (f t) = t ^ n * k t := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨fun t => Λf (g t), hg Λf, fun t => by rw [e, map_smul, smul_eq_mul]⟩

/-- The third-order remainder. -/
theorem rem3W_le {f : ℂ → R} {F₂ : R} (h : ExpW2 f 0 0 F₂) (Λf : R →ₗ[ℂ] ℂ)
    {r B : ℝ} (hR : 1 ≤ r) (hB : ∀ ζ : ℂ, ‖ζ‖ = r → ‖Λf (f ζ)‖ ≤ B) :
    ‖Λf (f 1) - Λf F₂‖ ≤ 2 * B / r ^ 3 := by
  have hR0 : 0 < r := by linarith
  obtain ⟨k, hk, e⟩ := OrdW.pair h Λf
  have e' : ∀ t, Λf (f t) - t ^ 2 * Λf F₂ = t ^ 3 * k t := by
    intro t
    rw [← e]
    simp [map_sub, map_add, map_smul, smul_eq_mul]
  have hF₂ : ‖Λf F₂‖ ≤ B / r ^ 2 := by
    have := coeff_le (φ := fun t => Λf (f t)) (k := fun t => Λf F₂ + t * k t) (n := 2)
      ((differentiable_const _).add (differentiable_id.mul hk))
      (fun t => by rw [mul_add, ← mul_assoc, ← pow_succ, ← e' t]; ring) hR0 hB
      (z := 0) (by simp; linarith)
    simpa using this
  have h1 := coeff_le hk e' hR0 (B := 2 * B) (fun ζ hζ => by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_pow, hζ]
    have : r ^ 2 * ‖Λf F₂‖ ≤ B := by
      rw [le_div_iff₀ (by positivity)] at hF₂; linarith
    linarith [hB ζ hζ]) (z := 1) (by simp; linarith)
  have := e' 1
  rw [one_pow, one_mul, one_pow, one_mul] at this
  rw [this]; exact h1

/-- The second-order remainder. -/
theorem rem2W_le {f : ℂ → R} {F₁ : R} (h : ExpW1 f 0 F₁) (Λf : R →ₗ[ℂ] ℂ)
    {r B : ℝ} (hR : 1 ≤ r) (hB : ∀ ζ : ℂ, ‖ζ‖ = r → ‖Λf (f ζ)‖ ≤ B) :
    ‖Λf (f 1) - Λf F₁‖ ≤ 2 * B / r ^ 2 := by
  have hR0 : 0 < r := by linarith
  obtain ⟨k, hk, e⟩ := OrdW.pair h Λf
  have e' : ∀ t, Λf (f t) - t * Λf F₁ = t ^ 2 * k t := by
    intro t
    rw [← e]
    simp only [zero_add, map_sub, map_add, map_smul, smul_eq_mul]
  have hF₁ : ‖Λf F₁‖ ≤ B / r ^ 1 := by
    have := coeff_le (φ := fun t => Λf (f t)) (k := fun t => Λf F₁ + t * k t) (n := 1)
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
    have : r * ‖Λf F₁‖ ≤ B := by
      rw [pow_one, le_div_iff₀ hR0] at hF₁; linarith
    linarith [hB ζ hζ]) (z := 1) (by simp; linarith)
  have := e' 1
  rw [one_mul, one_pow, one_mul] at this
  rw [this]; exact h1

/-- The mixed term. -/
theorem mixedW_le {F : ℂ → ℂ → R} (hF1 : ∀ s, HolW (fun t => F t s))
    (hF2 : ∀ t, HolW (fun s => F t s)) (Λf : R →ₗ[ℂ] ℂ) {R₁ R₂ B : ℝ}
    (hR₁ : 1 ≤ R₁) (hR₂ : 1 ≤ R₂)
    (hB : ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λf (F t s)‖ ≤ B) :
    ‖Λf (F 1 1) - Λf (F 1 0) - Λf (F 0 1) + Λf (F 0 0)‖ ≤ 4 * B / (R₁ * R₂) := by
  have hR₁0 : 0 < R₁ := by linarith
  have hR₂0 : 0 < R₂ := by linarith
  set G : ℂ → ℂ → ℂ := fun t s => Λf (F t s) - Λf (F t 0) - Λf (F 0 s) + Λf (F 0 0) with hG
  have h4 : ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖G t s‖ ≤ 4 * B := by
    intro t s ht hs
    have h0 : ‖(0 : ℂ)‖ ≤ R₁ := by simp; linarith
    have h0' : ‖(0 : ℂ)‖ ≤ R₂ := by simp; linarith
    have := norm_add_le (Λf (F t s) - Λf (F t 0) - Λf (F 0 s)) (Λf (F 0 0))
    have := norm_sub_le (Λf (F t s) - Λf (F t 0)) (Λf (F 0 s))
    have := norm_sub_le (Λf (F t s)) (Λf (F t 0))
    linarith [hB t s ht hs, hB t 0 ht h0', hB 0 s h0 hs, hB 0 0 h0 h0']
  have hstep1 : ∀ s : ℂ, ‖s‖ ≤ R₂ → ‖G 1 s‖ ≤ 4 * B / R₁ := by
    intro s hs
    have hd : Differentiable ℂ (fun t => G t s) :=
      ((((hF1 s) Λf).sub ((hF1 0) Λf)).sub (differentiable_const _)).add
        (differentiable_const _)
    obtain ⟨k, hk, e⟩ := OrdS.one_of_zero hd (by simp [hG])
    have := coeff_le hk e hR₁0 (fun ζ hζ => h4 ζ s hζ.le hs) (z := 1) (by simp; linarith)
    have e1 : G 1 s = k 1 := by simpa using e 1
    rw [e1]; simpa using this
  have hd : Differentiable ℂ (fun s => G 1 s) :=
    ((((hF2 1) Λf).sub (differentiable_const _)).sub ((hF2 0) Λf)).add
      (differentiable_const _)
  obtain ⟨k, hk, e⟩ := OrdS.one_of_zero hd (by simp [hG])
  have := coeff_le hk e hR₂0 (fun ζ hζ => hstep1 ζ hζ.le) (z := 1) (by simp; linarith)
  have e1 : G 1 1 = k 1 := by simpa using e 1
  show ‖G 1 1‖ ≤ _
  rw [e1]
  refine this.trans (le_of_eq ?_)
  rw [pow_one, div_div]

/-- **The Cauchy assembly** (the core of `Step2.step2_ts`): for `F(t, s)` holomorphic in each
variable with `F(t, 0) = t² K₂ + O(t³)`, `F(0, s) = s 𝓛 + O(s²)`, `F(0,0) = 0`, and a functional
bounded by `1` on the polydiscs of radii `R₁ ≤ ρ/g`, `R₂ ≤ ρ/k`:
`|λ(F(1,1) - K₂ - 𝓛)| ≤ (4/ρ³)(g³ + g k + k²)`. -/
theorem cauchy_assemble {F : ℂ → ℂ → R} (hF1 : ∀ s, HolW (fun t => F t s))
    (hF2 : ∀ t, HolW (fun s => F t s)) {K₂ Ll : R} (hexp : ExpW2 (fun t => F t 0) 0 0 K₂)
    (hlin : ExpW1 (fun s => F 0 s) 0 Ll) (hF00 : F 0 0 = 0) (Λf : R →ₗ[ℂ] ℂ) {ρ g k : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hg0 : 0 ≤ g) (hgρ : g ≤ ρ) (hk0 : 0 ≤ k) (hkρ : k ≤ ρ)
    (hB : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
      ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λf (F t s)‖ ≤ 1) :
    ‖Λf (F 1 1) - Λf K₂ - Λf Ll‖ ≤ 4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2) := by
  have hR0g : (1 : ℝ) * g ≤ ρ := by linarith
  have hR0k : (1 : ℝ) * k ≤ ρ := by linarith
  have X1 : ‖Λf (F 1 1) - Λf (F 1 0) - Λf (F 0 1) + Λf (F 0 0)‖ ≤ 4 * (g / ρ) * (k / ρ) := by
    refine rad2 (by norm_num) hρ0 hg0 hgρ hk0 hkρ fun R₁ hR₁ hR₁g R₂ hR₂ hR₂k => ?_
    have := mixedW_le hF1 hF2 Λf hR₁ hR₂ (B := 1) (hB R₁ hR₁ hR₁g R₂ hR₂ hR₂k)
    simpa using this
  have X2 : ‖Λf (F 1 0) - Λf K₂‖ ≤ 2 * (g / ρ) ^ 3 := by
    refine rad1 (n := 3) (by norm_num) (by norm_num) hρ0 hg0 hgρ fun r hr hrg => ?_
    have := rem3W_le hexp Λf hr (B := 1) fun ζ hζ =>
      hB r hr hrg 1 le_rfl hR0k ζ 0 hζ.le (by simp)
    simpa using this
  have X3 : ‖Λf (F 0 1) - Λf Ll‖ ≤ 2 * (k / ρ) ^ 2 := by
    refine rad1 (n := 2) (by norm_num) (by norm_num) hρ0 hk0 hkρ fun r hr hrk => ?_
    have := rem2W_le hlin Λf hr (B := 1) fun ζ hζ =>
      hB 1 le_rfl hR0g r hr hrk 0 ζ (by simp) hζ.le
    simpa using this
  have hsplit : Λf (F 1 1) - Λf K₂ - Λf Ll =
      (Λf (F 1 1) - Λf (F 1 0) - Λf (F 0 1) + Λf (F 0 0)) + (Λf (F 1 0) - Λf K₂) +
        (Λf (F 0 1) - Λf Ll) := by
    rw [hF00, map_zero]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hρ3 : 0 < ρ ^ 3 := by positivity
  have hρ23 : ρ ^ 3 ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0.le hρ1 (by norm_num)
  have hgk : g / ρ * (k / ρ) ≤ g * k / ρ ^ 3 := by
    rw [div_mul_div_comm, ← sq]
    exact div_le_div_of_nonneg_left (by positivity) hρ3 hρ23
  have hkk : (k / ρ) ^ 2 ≤ k ^ 2 / ρ ^ 3 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) hρ3 hρ23
  have hg3 : (g / ρ) ^ 3 = g ^ 3 / ρ ^ 3 := div_pow _ _ _
  have e : 4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2) =
      4 * (g ^ 3 / ρ ^ 3) + 4 * (g * k / ρ ^ 3) + 4 * (k ^ 2 / ρ ^ 3) := by ring
  rw [e]
  have h1 : 4 * (g / ρ) * (k / ρ) ≤ 4 * (g * k / ρ ^ 3) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hgk (by norm_num)
  have h2 : 2 * (g / ρ) ^ 3 ≤ 4 * (g ^ 3 / ρ ^ 3) := by
    rw [hg3]; have : 0 ≤ g ^ 3 / ρ ^ 3 := by positivity
    linarith
  have h3 : 2 * (k / ρ) ^ 2 ≤ 4 * (k ^ 2 / ρ ^ 3) := by
    have : 0 ≤ k ^ 2 / ρ ^ 3 := by positivity
    linarith
  linarith only [X1, X2, X3, h1, h2, h3]

end

end Obs2
