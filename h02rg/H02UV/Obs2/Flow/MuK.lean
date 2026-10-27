import Obs2.Flow.MuTau
import Obs2.Est.LinComp
import Obs.FlowObsCoeff

/-!
# The activity term `E_K` of `MuErr` from the norm of `K^{obs}`

**`sum_mass1_le`**: if the `σ_a` component of `K(X)` vanishes unless `a ∈ X^□` (the support
property `OLocS`) and `w_a ‖K(X)_a‖_{T_j(ℓ)} ≤ k` for small `X`, then

  `|∑_{X ∈ 𝒮_j} m₁(K(X)_a)| ≤ c (k / w_a) ℓ^{-1}`,

with `c` the number of small sets near a point (`card_small_near`, uniform in `L`, `j`) and
`|m₁(F)| ≤ ℓ^{-1} ‖F‖_{T_j(ℓ)}` (`Obs.norm_mass1_le`). This is the field `hK` of `MuErr` with
`E_K = c (k/w_a) ℓ^{-1}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

/-- **`E_K` from the norm of `K^{obs}`.** -/
theorem sum_mass1_le (d : ℕ) : ∃ cs : ℕ, ∀ (L : ℕ) [NeZero L] (N j : ℕ) (c : Obs.Case)
    (a : Lam d L N) (K : Finset (Lam d L N) → OE c (Lam d L N)) (ℓ k wa : ℝ), 0 < ℓ → 0 < wa →
    0 ≤ k → (∀ X, IsSmall j X → a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0) →
    (∀ X, IsSmall j X →
      ENNReal.ofReal wa * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a ≤ ENNReal.ofReal k) →
    ‖∑ X ∈ smallSets (L := L) (N := N) j, mass1 (-1) (K X : SA c (Lam d L N)).a‖ ≤
      cs * (k / wa) * ℓ⁻¹ := by
  obtain ⟨cs, hcs⟩ := card_small_near d
  refine ⟨cs, fun L _ N j c a K ℓ k wa hℓ hwa hk hz hK => ?_⟩
  classical
  set S := smallSets (L := L) (N := N) j
  set S' := S.filter (fun X => a ∈ nbhd j X)
  have hsplit : ∑ X ∈ S, mass1 (-1) (K X : SA c (Lam d L N)).a =
      ∑ X ∈ S', mass1 (-1) (K X : SA c (Lam d L N)).a := by
    refine (sum_subset (filter_subset _ _) fun X hX hX' => ?_).symm
    rw [hz X (mem_smallSets.1 hX) (fun h => hX' (mem_filter.2 ⟨hX, h⟩))]
    exact map_zero (mass1L (d := d) (L := L) (N := N) (-1))
  rw [hsplit]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ X ∈ S', ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖ ≤ k / wa * ℓ⁻¹ := by
    intro X hX
    refine (norm_mass1_le hℓ j (-1) _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h := hK X (mem_smallSets.1 (mem_filter.1 hX).1)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hwa.le, ENNReal.toReal_ofReal hk] at h2
    rw [le_div_iff₀ hwa]
    linarith [mul_comm wa (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).a).toReal]
  have hc : (S'.card : ℝ) ≤ cs := by exact_mod_cast hcs L N j a
  calc ∑ X ∈ S', ‖mass1 (-1) (K X : SA c (Lam d L N)).a‖
      ≤ ∑ _X ∈ S', k / wa * ℓ⁻¹ := sum_le_sum hterm
    _ = S'.card * (k / wa * ℓ⁻¹) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ cs * (k / wa * ℓ⁻¹) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = cs * (k / wa) * ℓ⁻¹ := by ring

end

end Obs2
