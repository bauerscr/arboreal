import PtCorr2.Cont.ContZab1

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`): exact homogeneity of pure-`ab` norms under the `σ_a` weight

For an element with no `σ_a`, `σ_b` parts (e.g. every activity of the reduced pair chain,
`obsAbInv_redSt`), the observable norm in `wM(K·M_a, M_b)` is exactly `K^{-1}` times the norm in
`wM(M_a, M_b)` (**`fx_oTo_wM_ab_scale`**). Inflating the `a`-weight therefore divides the seed and
all sizes of the reduced chain by `K` while the conclusion picks up the factor `K`; this is what
removes the per-step growth `max(1, 2Λ₁)^{C_δ}` of `rpc9Mb` from the window `hmAB`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist ENNReal

variable {L N : ℕ} [NeZero L]

/-- **Homogeneity of the pure-`ab` observable norm**: `‖F‖^{obs}_{wM(KM_a,M_b)} = K^{-1}‖F‖^{obs}_{wM(M_a,M_b)}`. -/
theorem fx_oTo_wM_ab_scale {K Ma Mb : ℝ} (hK : 0 < K) (j : ℕ) (ℓ : ℝ)
    (F : OE .two (Lam 2 L N)) (hF : (F : SA .two (Lam 2 L N)).a = 0 ∧ (F : SA .two (Lam 2 L N)).b = 0) :
    oTo (wM (K * Ma) Mb) j ℓ F = ENNReal.ofReal K⁻¹ * oTo (wM Ma Mb) j ℓ F := by
  unfold oTo
  simp only [oTj, oNorm, coe_πobs, piobs_apply, hF.1, hF.2, wM]
  have hz : Tj 2 (L : ℝ) j ℓ (0 : Alg 2 L N) = 0 := tNorm_zero'
  rw [hz, mul_zero, mul_zero, add_zero, add_zero, zero_add, zero_add, mul_inv,
    ENNReal.ofReal_mul (inv_nonneg.2 hK.le)]
  ring

/-- The same as an inequality for the regulated activity norm. -/
theorem fx_oTo_wM_ab_le {K Ma Mb : ℝ} (hK : 0 < K) (j : ℕ) (ℓ : ℝ)
    (F : OE .two (Lam 2 L N)) (hF : (F : SA .two (Lam 2 L N)).a = 0 ∧ (F : SA .two (Lam 2 L N)).b = 0)
    {a k : ℝ} (hk : ENNReal.ofReal a * oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal k) :
    ENNReal.ofReal a * oTo (wM (K * Ma) Mb) j ℓ F ≤ ENNReal.ofReal (k / K) := by
  rw [fx_oTo_wM_ab_scale hK j ℓ F hF, div_eq_mul_inv, mul_comm k,
    ENNReal.ofReal_mul (inv_nonneg.2 hK.le), mul_left_comm]
  gcongr

end

end PtCorr2
