import PtCorr2.Pair.SeedSplit2
import PtCorr2.Pair.VObsStepAB1

/-!
# The `V'` block sizes in the weights `wM` from the coefficients (the `hVo` input)

The `hVo` input of `obs_histFromABL_wM` is `‖V'_j(B)‖_{wM(M_{a,j},M_{b,j})} ≤ m_j` for every
`j`-block `B`. On `abSub` this is `(M_aM_b)^{-1}‖V'_j(B)_{ab}‖_{T_j(ℓ_j)}`, and by
`Obs2.tNorm_of_ab_le` the norm of an `ab` element of `𝒩({a,b})` is bounded by its coefficient
sizes: the mass `m₂` (per block: `Spin2.pairBlockMass_of_err2`), the gradient coefficients and the
quartic coefficient `M₄`.

* **`oTo_wM_le_coeffs`**: `‖F‖_{wM} ≤ (M_aM_b)^{-1}(|ε| + |m₂|ℓ² + gradient + M₄ terms)`.
* **`oTo_wM_le_mass`**: with `ε = 0`, `|m₂(F_{ab})| ≤ ρ` and the gradient/`M₄` part `≤ γ`:
  `‖F‖_{wM} ≤ (M_aM_b)^{-1}(ρℓ² + γ)`.
* **`hVo_of_coeffs`**: the `hVo` input along `obsHistFrom` from per-block mass bounds `ρ_j` and
  gradient/`M₄` bounds `γ_j` with `(M_{a,j}M_{b,j})^{-1}(ρ_jℓ_j² + γ_j) ≤ m_j`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LocObs

variable {L N : ℕ} [NeZero L]

theorem wM_ab_eq {Ma Mb : ℝ} (hMa : 0 < Ma) : (wM Ma Mb).ab = ENNReal.ofReal (Ma * Mb)⁻¹ := by
  show ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹ = _
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), mul_inv]

/-- The gradient and quartic part of the coefficient bound of `Obs2.tNorm_of_ab_le`. -/
def gradM4Sz (X : Finset (Lam 2 L N)) (a b : Lam 2 L N) (h ℓ : ℝ) (F : Alg 2 L N) : ℝ :=
  (‖cfAB2 a b F + cfAB2 b b F‖ + ‖cfAB2 b a F + cfAB2 b b F‖) * (ℓ * (eN1 X a b * ℓ * h⁻¹)) +
    ‖cfAB2 b b F‖ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹)) +
    ‖cfAB4 a b F‖ * (ℓ * ℓ * ((eN1 X a b * ℓ * h⁻¹) * (eN1 X a b * ℓ * h⁻¹)))

/-- **`‖F‖_{wM} ≤ (M_aM_b)^{-1}·(coefficient sizes)`** for `F ∈ abSub` with `F_{ab} ∈ 𝒩({a,b})`
symmetric. -/
theorem oTo_wM_le_coeffs {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (X : Finset (Lam 2 L N)) {a b : Lam 2 L N} (hab : a ≠ b)
    {F : OE c (Lam 2 L N)} (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))))
    (hN : (F : SA c (Lam 2 L N)).ab ∈ NX ({a, b} : Set (Lam 2 L N)))
    (hS : IsSym (F : SA c (Lam 2 L N)).ab) :
    oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal ((Ma * Mb)⁻¹ *
      (‖ε (F : SA c (Lam 2 L N)).ab‖ + ‖mass2 (F : SA c (Lam 2 L N)).ab‖ * (ℓ * ℓ) +
        gradM4Sz X a b ((L : ℝ) ^ j) ℓ (F : SA c (Lam 2 L N)).ab)) := by
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  rw [oTo_of_ab _ _ _ hF, wM_ab_eq hMa, ENNReal.ofReal_mul (inv_nonneg.2 (mul_pos hMa hMb).le)]
  refine mul_le_mul_left' ((tNorm_of_ab_le one_le_two hLj hℓ X hab hN hS).trans ?_) _
  unfold gradM4Sz
  exact le_of_eq (by ring_nf)

/-- **The `wM` size from the mass and the gradient/`M₄` sizes** (`ε = 0`). -/
theorem oTo_wM_le_mass {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (X : Finset (Lam 2 L N)) {a b : Lam 2 L N} (hab : a ≠ b)
    {F : OE c (Lam 2 L N)} (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))))
    (hN : (F : SA c (Lam 2 L N)).ab ∈ NX ({a, b} : Set (Lam 2 L N)))
    (hS : IsSym (F : SA c (Lam 2 L N)).ab) (hε : ε (F : SA c (Lam 2 L N)).ab = 0) {ρ γ : ℝ}
    (hρ : ‖mass2 (F : SA c (Lam 2 L N)).ab‖ ≤ ρ)
    (hγ : gradM4Sz X a b ((L : ℝ) ^ j) ℓ (F : SA c (Lam 2 L N)).ab ≤ γ) :
    oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal ((Ma * Mb)⁻¹ * (ρ * (ℓ * ℓ) + γ)) := by
  refine (oTo_wM_le_coeffs hMa hMb j hℓ X hab hF hN hS).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hε, norm_zero, zero_add]
  have : ‖mass2 (F : SA c (Lam 2 L N)).ab‖ * (ℓ * ℓ) ≤ ρ * (ℓ * ℓ) :=
    mul_le_mul_of_nonneg_right hρ (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 (mul_pos hMa hMb).le)

/-- **The `hVo` input of `obs_histFromABL_wM` from per-block coefficient sizes.** Along
`obsHistFrom` from `j₀` (anchored, `V_{ab} ∈ 𝒩({a,b})`, symmetric, no constants), per-block mass
bounds `ρ_j` and gradient/`M₄` bounds `γ_j` give `‖V'_j(B)‖_{wM(j)} ≤ m_j` as soon as
`(M_{a,j}M_{b,j})^{-1}(ρ_jℓ_j² + γ_j) ≤ m_j`. -/
theorem hVo_of_coeffs (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (hab : P.a ≠ P.b) (j₀ : ℕ) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R)) (n : ℕ)
    (Ma Mb : ℕ → ℝ) (hMa : ∀ j, 0 < Ma j) (hMb : ∀ j, 0 < Mb j) (m ρ γ : ℕ → ℝ)
    (X : Finset (Lam 2 L N)) (hℓ : ∀ j, 0 < histS R j t)
    (hAB : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      (obsHistFrom R P j₀ o₀ j t).V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (hN : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab ∈
        NX ({P.a, P.b} : Set (Lam 2 L N)))
    (hS : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      IsSym ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab)
    (hε : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab = 0)
    (hρ : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      ‖mass2 ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab‖ ≤ ρ j)
    (hγ : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      gradM4Sz X P.a P.b ((L : ℝ) ^ j) (histS R j t)
        ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab ≤ γ j)
    (hm : ∀ j, j₀ ≤ j → j < n →
      (Ma j * Mb j)⁻¹ * (ρ j * (histS R j t * histS R j t) + γ j) ≤ m j) :
    ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤
        ENNReal.ofReal (m j) := fun j hj hjn b hb =>
  (oTo_wM_le_mass (hMa j) (hMb j) j (hℓ j) X hab (hAB j hj hjn b hb) (hN j hj hjn b hb)
    (hS j hj hjn b hb) (hε j hj hjn b hb) (hρ j hj hjn b hb) (hγ j hj hjn b hb)).trans
    (ENNReal.ofReal_le_ofReal (hm j hj hjn))

end

end PtCorr2
