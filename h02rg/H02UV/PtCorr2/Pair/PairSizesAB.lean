import PtCorr2.Pair.PairRecAB
import PtCorr2.Pair.PairInitAB

/-!
# From the `ab` recursion to the `ab` sizes of `Q'_k` and `𝒲'_k`

* **`exists_Q2O_ab_bound`**: `‖Q'(B)‖_{w} ≤ C κ` for `Q'(B) = ∑_{X ⊇ B small} Loc_{X,B} K(X)`, if
  `A^{(|𝓑(X)|-4)_+}‖K(X)‖_w ≤ κ` on connected `X` (`K(X)` without one-point parts, `K(X)_{ab}`
  local in `X^□`); `C = C_{loc} c_N` (`exists_LocO2_ab_bound`, `card_small_containing`);
* **`Tj_ab_le_of_oTo_wM`**: with the weights `wM M_a M_b`, `‖F_{ab}‖_{T_j(ℓ)} ≤ M_aM_b x` from
  `‖F‖_{wM} ≤ x` on `abSub`.

With `obs_histFromAB` (weights `wM M_a M_b`, `j₀ = j_x`, `o₀ = redSt …`) this gives the sizes
`ŝ^q_k = C M_aM_b kseqF_k / ‖β_{a,k+1}‖` and `ŝ^w_k = M_aM_b c_W r_k m_k / ‖β_{a,k+1}‖` of
`Spin2.PairErrSizesR`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 ENNReal

local notation "AB2" => (abSub : Subalgebra ℂ (OE _ (Lam 2 _ _)))

variable {c : Obs.Case} {L N : ℕ} [NeZero L]

/-- **The `ab` norm from the `wM` norm.** -/
theorem Tj_ab_le_of_oTo_wM {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ) (ℓ : ℝ)
    {F : OE c (Lam 2 L N)} (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N)))) {x : ℝ}
    (hx : oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal x) :
    Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).ab ≤ ENNReal.ofReal (Ma * Mb * x) := by
  rw [oTo_of_ab _ _ _ hF] at hx
  have hw : (wM Ma Mb).ab = ENNReal.ofReal (Ma * Mb)⁻¹ := by
    show ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹ = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), mul_inv]
  rw [hw] at hx
  have hM : 0 < Ma * Mb := mul_pos hMa hMb
  have e : ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal (Ma * Mb)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hM.le, mul_inv_cancel₀ hM.ne', ENNReal.ofReal_one]
  calc Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).ab
      = ENNReal.ofReal (Ma * Mb) * (ENNReal.ofReal (Ma * Mb)⁻¹ * Tj 2 (L : ℝ) j ℓ
          (F : SA c (Lam 2 L N)).ab) := by rw [← mul_assoc, e, one_mul]
    _ ≤ ENNReal.ofReal (Ma * Mb) * ENNReal.ofReal x := mul_le_mul_left' hx _
    _ ≤ ENNReal.ofReal (Ma * Mb * x) := by rw [ENNReal.ofReal_mul hM.le]

end

end PtCorr2
