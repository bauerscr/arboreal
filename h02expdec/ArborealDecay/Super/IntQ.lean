module

public import ArborealDecay.Super.Q

/-!
# The superintegral and the vanishing of integrals of `Q`-exact forms

* `berezin = ∏_i ∂_{η_i} ∂_{ξ_i}` (all pairs).
* `superIntegral F = (2π)^{-N} ∫_{ℝ^{2N}} dx dy ∏_i ∂_{η_i} ∂_{ξ_i} F`, the normalisation of
  BCHS Theorem 2.8 (`∫ dx dy ∂_η ∂_ξ / (2π)` per pair).  For parameter generators `P` the result
  is a form in the parameter generators.
* `integral_berezin_Q`: `∫ ℓ (berezin (Q Θ p)) dp = 0` for every `Θ` in `SDecay` and every linear
  functional `ℓ`; hence `superIntegral (Q Θ) = 0` (`superIntegral_Q`).
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

variable {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]

/-- The Berezin integral `∏_i ∂_{η_i} ∂_{ξ_i}` over all pairs. -/
def berezin : SG N P →ₗ[ℝ] SG N P := berezinL (Finset.univ : Finset N).toList

/-- The superintegral `∫_{ℝ^{2N|2N}} F = (2π)^{-N} ∫ dx dy ∏_i ∂_{η_i} ∂_{ξ_i} F`
(BCHS Theorem 2.8 normalisation).  With parameter generators `P` its value is a form in the
parameters. -/
def superIntegral (F : Pt N → SG N P) : SG N P :=
  ((2 * Real.pi) ^ Fintype.card N)⁻¹ • sint (fun p => berezin (F p)) volume

theorem berezin_dξ (i : N) (x : SG N P) : berezin (dξ i x) = 0 :=
  berezinL_dξ (Finset.mem_toList.2 (Finset.mem_univ i)) x

theorem berezin_dη (i : N) (x : SG N P) : berezin (dη i x) = 0 :=
  berezinL_dη (Finset.mem_toList.2 (Finset.mem_univ i)) x

theorem berezin_mul_W (γ : ℝ) (H : SG N P) :
    berezin (H * W γ) = TL 1 γ (Finset.univ : Finset N).toList H :=
  berezinL_mul_WL γ (Finset.nodup_toList _) H

/-- Pointwise form of `ℓ ∘ berezin ∘ Q`: only the bosonic derivatives survive. -/
theorem dual_berezin_Q {Θ : Pt N → SG N P} (hΘ : SDiff Θ) (ℓ : Module.Dual ℝ (SG N P))
    (p : Pt N) :
    ℓ (berezin (Q Θ p)) = ∑ i,
      (fderiv ℝ (fun q => (ℓ ∘ₗ berezin ∘ₗ LinearMap.mulLeft ℝ (ξ i)) (Θ q)) p (ex i) +
        fderiv ℝ (fun q => (ℓ ∘ₗ berezin ∘ₗ LinearMap.mulLeft ℝ (η i)) (Θ q)) p (ey i)) := by
  simp only [Q, map_sum, map_add, map_sub, map_smul, berezin_dξ, berezin_dη, smul_zero,
    sub_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← dual_pd hΘ, ← dual_pd hΘ]
  rfl

/-- **Integrals of `Q`-exact forms vanish** (BHS App. B, Step 2: boundary terms vanish by decay,
and the Berezin integral of a fermionic derivative is zero). -/
theorem integral_berezin_Q {Θ : Pt N → SG N P} (hΘ : SDecay Θ) (ℓ : Module.Dual ℝ (SG N P)) :
    ∫ p, ℓ (berezin (Q Θ p)) = 0 := by
  simp_rw [dual_berezin_Q hΘ.sdiff ℓ]
  rw [integral_finsetSum _ fun i _ => ((hΘ _).integrable_fderiv _).fun_add
    ((hΘ _).integrable_fderiv _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_add ((hΘ _).integrable_fderiv _) ((hΘ _).integrable_fderiv _),
    (hΘ _).integral_fderiv_eq_zero, (hΘ _).integral_fderiv_eq_zero, add_zero]

theorem SDecay.sint_berezin_Q {Θ : Pt N → SG N P} (hΘ : SDecay Θ) :
    SInt (fun p => berezin (Q Θ p)) volume := fun ℓ => by
  simp_rw [dual_berezin_Q hΘ.sdiff ℓ]
  exact integrable_finsetSum _ fun i _ => ((hΘ _).integrable_fderiv _).fun_add
    ((hΘ _).integrable_fderiv _)

/-- `∫_{ℝ^{2N|2N}} Q Θ = 0`. -/
theorem superIntegral_Q {Θ : Pt N → SG N P} (hΘ : SDecay Θ) : superIntegral (Q Θ) = 0 := by
  have : sint (fun p => berezin (Q Θ p)) volume = 0 := ext_dual fun ℓ => by
    rw [dual_sint hΘ.sint_berezin_Q, integral_berezin_Q hΘ, map_zero]
  rw [superIntegral, this, smul_zero]

end

end ArborealDecay.Super

end
