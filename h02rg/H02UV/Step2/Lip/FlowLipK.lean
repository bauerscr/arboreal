import Step2.Lip.FlowLipCov

/-!
# Joint Lipschitz bound for `K_{j+1}` (Lipschitz bounds, part 4)

`Kplus_lip_joint`: Lipschitz continuity of `K_{j+1}` jointly in `(C, V, 𝒲, K)`, where the two
covariances `C, C'` are good at `ℓ_C` and their difference is good at `ℓ_Δ`. The bound is
`4 B s` with `B = 2κ e² + 16 C₁ e³` (the `stepK` bound on the doubled domain) and the relative
distance `s = ‖δV‖/e + ‖δ𝒲‖/e² + ‖δK‖/e² + ℓ_Δ²/(τ ℓ_C)²`, i.e.
`(8κ + 64 C₁ e)(e‖δV‖ + ‖δ𝒲‖ + ‖δK‖) + 4B ℓ_Δ²/(τℓ_C)²`. Input weight `A`, output weight `2A`
(`stepK_tsW`, the slack for `K♭`), two field scales `ℓ' + (1 + τ) ℓ_C ≤ 2ℓ`.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

/-- The relative distance of two inputs of the step. -/
def relDist (e a b c ℓΔ τ ℓC : ℝ) : ℝ := a / e + b / e ^ 2 + c / e ^ 2 + ℓΔ ^ 2 / (τ * ℓC) ^ 2

theorem relDist_nonneg {e a b c ℓΔ τ ℓC : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ relDist e a b c ℓΔ τ ℓC := by
  unfold relDist; positivity

/-- The consequences of `R s ≤ 1` for the radius `R`. -/
theorem relDist_radius {e a b c ℓΔ τ ℓC R : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hτ : 0 < τ) (hℓC : 0 < ℓC) (hℓΔ : 0 ≤ ℓΔ) (hR : 0 ≤ R)
    (hRs : R * relDist e a b c ℓΔ τ ℓC ≤ 1) :
    R * a ≤ e ∧ R * b ≤ e ^ 2 ∧ R * c ≤ e ^ 2 ∧ Real.sqrt R * ℓΔ ≤ τ * ℓC := by
  unfold relDist at hRs
  have h1 : 0 ≤ R * (a / e) := by positivity
  have h2 : 0 ≤ R * (b / e ^ 2) := by positivity
  have h3 : 0 ≤ R * (c / e ^ 2) := by positivity
  have h4 : 0 ≤ R * (ℓΔ ^ 2 / (τ * ℓC) ^ 2) := by positivity
  have hs : R * (a / e) + R * (b / e ^ 2) + R * (c / e ^ 2) + R * (ℓΔ ^ 2 / (τ * ℓC) ^ 2) ≤ 1 := by
    nlinarith
  have he2 : 0 < e ^ 2 := by positivity
  have hτℓ : 0 < τ * ℓC := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : R * (a / e) ≤ 1 := by linarith
    rw [← mul_div_assoc, div_le_one he] at this; exact this
  · have : R * (b / e ^ 2) ≤ 1 := by linarith
    rw [← mul_div_assoc, div_le_one he2] at this; exact this
  · have : R * (c / e ^ 2) ≤ 1 := by linarith
    rw [← mul_div_assoc, div_le_one he2] at this; exact this
  · have : R * (ℓΔ ^ 2 / (τ * ℓC) ^ 2) ≤ 1 := by linarith
    rw [← mul_div_assoc, div_le_one (by positivity)] at this
    have h5 : (Real.sqrt R * ℓΔ) ^ 2 ≤ (τ * ℓC) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hR]; exact this
    exact (pow_le_pow_iff_left₀ (by positivity) hτℓ.le two_ne_zero).1 h5

variable {d L N : ℕ} [NeZero L]

theorem eps_line {V V' : Fam d L N} (hV0 : ∀ b, ε (V b : Alg d L N) = 0)
    (hV0' : ∀ b, ε (V' b : Alg d L N) = 0) (z : ℂ) (b : Fin d → ℕ) :
    ε ((V + z • (V' - V)) b : Alg d L N) = 0 := by
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Subalgebra.coe_add,
    Subalgebra.coe_smul, AddSubgroupClass.coe_sub, map_add, map_smul, map_sub, hV0, hV0',
    sub_self, smul_zero, add_zero]

set_option maxHeartbeats 1000000 in
/-- **Joint Lipschitz bound for `K_{j+1}`** in `(C, V, 𝒲, K)`. -/
theorem Kplus_lip_joint (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC τ : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → 0 < τ →
    ℓ' + (1 + τ) * ℓC ≤ 2 * ℓ →
    ∀ C C' : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → GoodCov2 j ℓC C' →
    ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 j ℓΔ (C' - C) →
    ∀ (V V' W W' : Fam d L N) (K K' : Act d L N), InF j V → InF j V' → InF j W → InF j W' →
    InK2 j K → InK2 j K' → (∀ b, ε (V b : Alg d L N) = 0) → (∀ b, ε (V' b : Alg d L N) = 0) →
    ∀ e : ℝ, 0 < e → e ≤ ε₁ →
    Fnorm j ℓ V ≤ ENNReal.ofReal e → Fnorm j ℓ V' ≤ ENNReal.ofReal e →
    Fnorm j ℓ W ≤ ENNReal.ofReal (e ^ 2) → Fnorm j ℓ W' ≤ ENNReal.ofReal (e ^ 2) →
    Knorm j ℓ A K ≤ ENNReal.ofReal (e ^ 2) → Knorm j ℓ A K' ≤ ENNReal.ofReal (e ^ 2) →
    ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
    Fnorm j ℓ (V' - V) ≤ ENNReal.ofReal a → Fnorm j ℓ (W' - W) ≤ ENNReal.ofReal b →
    Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c →
    ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
      wnorm (j + 1) ℓ' (2 * A) U (Kplus j C' V' W' K' U - Kplus j C V W K U) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η))) * e ^ 2 +
          16 * C₁ * e ^ 3) * relDist e a b c ℓΔ τ ℓC) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, hS⟩ := stepK_tsW d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hS⟩ := hS L hL 2 one_le_two
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, hS⟩ := hS A hA
  refine ⟨min (ε₀ / 2) (1 / 2), C₁, lt_min (by positivity) (by norm_num), hC₁, ?_⟩
  intro N j hjN ℓ ℓ' ℓC τ hℓ hℓ' hℓC hτ hsum C C' hC hC' ℓΔ hℓΔ hΔ V V' W W' K K' hV hV' hW hW'
    hK hK' hV0 hV0' e he he1 hVe hVe' hWe hWe' hKe hKe' a b c ha hb hc hda hdb hdc U hU
  have hA0 : 0 < A := by linarith
  have hA2 : 0 < 2 * A := by linarith
  have he2 : e ≤ ε₀ / 2 := he1.trans (min_le_left _ _)
  have he12 : e ≤ 1 / 2 := he1.trans (min_le_right _ _)
  set κ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hκdef
  have hκ : 0 ≤ κ := by positivity
  set B := 2 * κ * e ^ 2 + 16 * C₁ * e ^ 3 with hB
  have hB0 : 0 ≤ B := by positivity
  have hs0 := relDist_nonneg (ℓΔ := ℓΔ) (τ := τ) (ℓC := ℓC) he ha hb hc
  -- the `stepK` bound in real form
  have bound : ∀ (Cz : Matrix (Lam d L N) (Lam d L N) ℂ) (ℓz : ℝ), 0 < ℓz → ℓ' + ℓz ≤ 2 * ℓ →
      GoodCov2 j ℓz Cz → ∀ (Vz Wz : Fam d L N) (Kz : Act d L N), InF j Vz → InF j Wz →
      (∀ b, ε (Vz b : Alg d L N) = 0) → InK2 j Kz → ∀ g k : ℝ, 0 ≤ g → g ≤ ε₀ → 0 ≤ k →
      k ≤ ε₀ → Fnorm j ℓ Vz ≤ ENNReal.ofReal g → Fnorm j ℓ Wz ≤ ENNReal.ofReal (g ^ 2) →
      Knorm j ℓ A Kz ≤ ENNReal.ofReal k →
      wnorm (j + 1) ℓ' (2 * A) U (Kplus j Cz Vz Wz Kz U) ≤
        ENNReal.ofReal (κ * k + C₁ * (g ^ 3 + g * k + k ^ 2)) :=
    fun Cz ℓz hℓz hsz hCz Vz Wz Kz hVz hWz hVz0 hKz g k hg hgε hk hkε hVg hWg hKk =>
      ennreal_stepK hκ hC₁ hg hk hKk (hS N j hjN ℓ ℓ' ℓz hℓ hℓ' hℓz hsz Cz hCz Vz Wz Kz hVz hWz
        hVz0 hKz g hg hgε hVg hWg (hKk.trans (ENNReal.ofReal_le_ofReal hkε)) U hU)
  have he3 : e ^ 2 ≤ e := by nlinarith
  have hsumC : ℓ' + ℓC ≤ 2 * ℓ := by nlinarith
  refine cauchy_lip hB0 hs0 ?_ ?_
  · -- far apart: both endpoints
    have h1 := bound C' ℓC hℓC hsumC hC' V' W' K' hV' hW' hV0' hK' e (e ^ 2) he.le (by linarith)
      (sq_nonneg e) (by nlinarith) hVe' hWe' hKe'
    have h2 := bound C ℓC hℓC hsumC hC V W K hV hW hV0 hK e (e ^ 2) he.le (by linarith)
      (sq_nonneg e) (by nlinarith) hVe hWe hKe
    refine (wnorm_sub_le' _ _ _ _ _ _).trans ((add_le_add h1 h2).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he.le (by linarith) (by norm_num)
    have h4' : C₁ * e ^ 4 ≤ C₁ * e ^ 3 := mul_le_mul_of_nonneg_left h4 hC₁
    rw [hB]
    nlinarith
  · intro R hR2 hRs
    have hR0 : 0 < R := by linarith
    obtain ⟨hRa, hRb, hRc, hRℓ⟩ := relDist_radius he ha hb hc hτ hℓC hℓΔ hR0.le hRs
    have hVf : ∀ b, HolE (fun z : ℂ => (V + z • (V' - V)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hWf : ∀ b, HolE (fun z : ℂ => (W + z • (W' - W)) b) := fun b =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hKf : ∀ X, HolE (fun z : ℂ => (K + z • (K' - K)) X) := fun X =>
      (HolE.const _).add (HolE.smul differentiable_id (HolE.const _))
    have hF := Kplus_holC (Cf := fun z : ℂ => C + z • (C' - C)) j (fun x y => cov_line_diff x y)
      hVf hWf hKf (fun z b => eps_line hV0 hV0' z b) U
    have hstep := wnorm_sub_le_of_hol (j := j + 1) hℓ' hA2 U hF (by linarith : (1 : ℝ) < R) hB0
      fun z hz => by
        obtain ⟨hVz, hWz, hKz⟩ := line_norms V V' W W' K K' he.le hR0.le ha hb hc z hz hVe hWe
          hKe hda hdb hdc hRa hRb hRc
        have hCz : GoodCov2 j ((1 + τ) * ℓC) (C + z • (C' - C)) :=
          (hC.line hΔ hℓΔ hz.le).mono (by nlinarith)
        refine (bound _ _ (by positivity) hsum hCz _ _ _
          (inF_add hV (inF_smul (inF_sub hV' hV) z)) (inF_add hW (inF_smul (inF_sub hW' hW) z))
          (eps_line hV0 hV0' z) (hK.add ((hK'.sub hK).smul z)) (2 * e) (2 * e ^ 2)
          (by positivity) (by linarith) (by positivity) (by nlinarith) hVz hWz hKz).trans
          (ENNReal.ofReal_le_ofReal ?_)
        have h4 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he.le (by linarith) (by norm_num)
        have h4' : C₁ * e ^ 4 ≤ C₁ * e ^ 3 := mul_le_mul_of_nonneg_left h4 hC₁
        rw [hB]
        nlinarith
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hstep
    exact hstep

end

end Step2
