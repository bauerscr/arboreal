import Obs2.Est.EstAB
import Obs2.Est.EstNormAB

/-!
# The localisation bound for all four components (any weights)

**`exists_LocO2_full_bound`**: `‖Loc_{X,Y}F‖^{obs}_w ≤ C‖F‖^{obs}_w` for every `F` with all four
components in `𝒩(X^□)` and any weights `w` (the pointed `loc^a`, `loc^b` on the single-source
components, `exists_LocO2_obs_bound`, and the barycentric `loc^{ab}` on the `ab` component, as in
`exists_LocO2_ab_bound`). `oTo_split_ab`: `‖F‖^{obs}_w = ‖F‖^{obs}_{(w_a,w_b,0)} + w_{ab}‖F_{ab}‖`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The single-source weights of `w`. -/
def wOne (w : Wt) : Wt := ⟨w.a, w.b, 0⟩

theorem oTo_split_ab (w : Wt) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo w j ℓ F = oTo (wOne w) j ℓ F + w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab := by
  simp only [oTo, oTj, oNorm, wOne, coe_πobs, piobs_apply, zero_mul, add_zero]

theorem oTo_one_le (w : Wt) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo (wOne w) j ℓ F ≤ oTo w j ℓ F := by
  rw [oTo_split_ab w j ℓ F]; exact le_self_add

theorem ab_le_oTo (w : Wt) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab ≤ oTo w j ℓ F := by
  rw [oTo_split_ab w j ℓ F]; exact le_add_self

/-- **The localisation bound, all four components.** -/
theorem exists_LocO2_full_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N : ℕ, ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt),
    ∀ k : ℕ, k < N → ∀ ℓ : ℝ, 0 < ℓ → ∀ X Y : Finset (Lam d L N), IsSmall k X → Y ⊆ X →
    ∀ F : OE c (Lam d L N), CmpInA (nbhd k X : Set (Lam d L N)) (F : SA c (Lam d L N)) →
      oTo w k ℓ (LocO2 P X Y F) ≤ ENNReal.ofReal C * oTo w k ℓ F := by
  obtain ⟨C1, hC1, h1⟩ := exists_LocO2_obs_bound d
  obtain ⟨C2, hC2, h2⟩ := exists_locABt_bound d hd
  refine ⟨max C1 C2, le_max_of_le_left hC1, fun L _ hL N c P w k hk ℓ hℓ X Y hX hYX F hF => ?_⟩
  have e1 : oTo (wOne w) k ℓ (LocO2 P X Y F) ≤ ENNReal.ofReal (max C1 C2) * oTo (wOne w) k ℓ F :=
    (h1 L hL N c P (wOne w) rfl k hk ℓ hℓ X Y hX hYX F hF.toCmpIn).trans
      (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
  have key : Tj d (L : ℝ) k ℓ (locABtXY P X Y (F : SA c (Lam d L N)).ab) ≤
      ENNReal.ofReal C2 * Tj d (L : ℝ) k ℓ (F : SA c (Lam d L N)).ab := by
    rw [locABtXY]
    by_cases hne : (X ∩ P.pts).Nonempty
    · refine (tNorm_smul_le _ _).trans ?_
      have hr := ENNReal.ofReal_le_ofReal (norm_ratio_le (P := P) hYX)
      rw [ENNReal.ofReal_one] at hr
      refine (mul_le_mul' hr le_rfl).trans ?_
      rw [one_mul, locABtX]
      split_ifs with ha
      · exact h2 L hL N k hk ℓ hℓ X hX P.a P.b ha _ hF.ab
      · exact h2 L hL N k hk ℓ hℓ X hX P.b P.a (mem_b_of_inter hne ha) _ hF.ab
    · have h0 : (((Y ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ)) = 0 := by
        simp [Finset.not_nonempty_iff_eq_empty.1 hne]
      rw [h0, zero_smul, Step.Tj_zero]
      exact zero_le
  have e2 : w.ab * Tj d (L : ℝ) k ℓ (LocO2 P X Y F : SA c (Lam d L N)).ab ≤
      ENNReal.ofReal (max C1 C2) * (w.ab * Tj d (L : ℝ) k ℓ (F : SA c (Lam d L N)).ab) := by
    rw [LocO2_ab, mul_left_comm]
    refine mul_le_mul_left' (key.trans ?_) _
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  rw [oTo_split_ab w k ℓ (LocO2 P X Y F), oTo_split_ab w k ℓ F, mul_add]
  exact add_le_add e1 e2

end

end Obs2
