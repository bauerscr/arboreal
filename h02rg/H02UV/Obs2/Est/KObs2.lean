import Obs2.Est.EstBlock
import Obs2.Est.EstLoc
import Obs2.Est.KObs1

/-!
# The `K^{obs}` step in the rescaled norm: reduction to the full bound with sources

* `bho_hlocl`: the locality hypothesis `BHO.hlocl` of the block bounds (supports `Y^□ ∪ {a, b}`,
  as required by the pointed `loc^a`) holds for every `LocO2` (from `LocO2_cmpIn_pts`). Together
  with `exists_LocO2_obs_bound` (`BHO.hloc`) the localisation hypotheses of `BHO` are discharged.
* `oTj_scale`: with single-source weights (`w_ab = 0`) and sources rescaled by `λ`,
  `‖F‖_{w_λ} = ‖F_∅‖ + λ ‖π_obs F‖_w`; `oTj_scale_le` for the inputs.
* **`kobs_step`** (conditional): if the full output activity obeys the Step2-type bound in the
  `λ`-norm with `λ = ḡ/m` (`hK'`, the Step2 Cauchy chain on the algebra with sources, **not
  proved**), with a priori sizes `‖K^∅‖ ≤ c_b ḡ³`, `‖K^{obs}‖ ≤ c_k ḡ² m`, then
  `‖K'^{obs}‖ ≤ (θ₀ + C₁(2 + 2c_b + c_k)ḡ) k + (θ₀c_b + C₁(8 + 2c_b + c_b²)) ḡ² m`
  (`lam_trick`), the `k` half of `lin_iter`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- **`BHO.hlocl` holds for the pointed `Loc`.** -/
theorem bho_hlocl (hd : 1 ≤ d) (P : ObsPts d L N) (j : ℕ) :
    ∀ X Y : Finset (Lam d L N), IsPolymer j Y → ∀ F : OE c (Lam d L N),
      CmpIn (↑(nbhd j Y ∪ {P.a, P.b}) : Set (Lam d L N)) (LocO2 P X Y F : SA c (Lam d L N)) := by
  intro X Y hY F
  rw [Finset.coe_union, Finset.coe_insert, Finset.coe_singleton]
  exact LocO2_cmpIn_pts hd P X hY F

/-- **The rescaled norm**: `‖F‖_{w_λ} = ‖F_∅‖ + λ ‖π_obs F‖_w` for `w_ab = 0`. -/
theorem oTj_scale {w : Wt} (hw0 : w.ab = 0) (lam : ℝ≥0∞) (j : ℕ) (ℓ : ℝ)
    (F : OE c (Lam d L N)) :
    oTj d L (Wt.scale lam w) j ℓ (F : SA c (Lam d L N)) =
      Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e + lam * oTo w j ℓ F := by
  rw [oTj_eq_bulk_add]
  congr 1
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply, Wt.scale, hw0]
  rw [show Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 from tNorm_zero']
  ring

/-- **The `K^{obs}` step from the bound in the rescaled norm** (conditional on `hK'`). -/
theorem kobs_step {w : Wt} (hw0 : w.ab = 0) {j : ℕ} {ℓ' : ℝ} {F : OE c (Lam d L N)}
    {k b m g θ₀ C₁ cb ck : ℝ} (hm : 0 < m) (hg : 0 < g) (hg1 : g ≤ 1) (hk : 0 ≤ k)
    (hθ : 0 ≤ θ₀) (hC : 0 ≤ C₁) (hb0 : 0 ≤ b) (hb : b ≤ cb * g ^ 3) (hcb : 0 ≤ cb)
    (hkk : k ≤ ck * g ^ 2 * m) (hck : 0 ≤ ck)
    (hK' : oTj d L (Wt.scale (ENNReal.ofReal (g / m)) w) j ℓ' (F : SA c (Lam d L N)) ≤
      ENNReal.ofReal (θ₀ * (b + g / m * k) +
        C₁ * ((2 * g) ^ 3 + 2 * g * (b + g / m * k) + (b + g / m * k) ^ 2))) :
    oTo w j ℓ' F ≤ ENNReal.ofReal ((θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k +
      (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m) := by
  have hl : 0 < g / m := div_pos hg hm
  set R := θ₀ * (b + g / m * k) + C₁ * ((2 * g) ^ 3 + 2 * g * (b + g / m * k) + (b + g / m * k) ^ 2)
  rw [oTj_scale hw0] at hK'
  have h1 : ENNReal.ofReal (g / m) * oTo w j ℓ' F ≤ ENNReal.ofReal R := le_add_self.trans hK'
  have hfin : oTo w j ℓ' F ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hl)] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)
  have hR : 0 ≤ R := by positivity
  have h2 : g / m * (oTo w j ℓ' F).toReal ≤ R := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hl.le, ENNReal.toReal_ofReal hR] at this
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal
    (lam_trick hm hg hg1 hk hθ hC hb0 hb hcb hkk hck h2)

end

end Obs2
