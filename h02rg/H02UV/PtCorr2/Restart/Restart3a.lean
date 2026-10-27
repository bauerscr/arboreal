import PtCorr2.Restart.RerepK
import PtCorr2.Pair.PairInitU

/-!
# B3, T6: the two bulk inputs of `rr_delta_KbHF` (pure layer)

* **`r3_IbO_e_le`**: the bulk part of the block factor `I(B) = e^{-V(B)}(1 + 𝒲(B))` only sees the bulk
  parts: if `bulk V(B) = x` (with `ε(x) = 0`) and `bulk 𝒲(B) = y`, then
  `‖I(B)_∅‖ ≤ e^{‖x‖}(1 + ‖y‖)` (`bulk` is an algebra hom, `bulk(e^F) = e^{bulk F}`).
* **`r3_reg_of_Knorm`**: the regulator `A^{|𝓑(W)|}‖K(W)‖ ≤ 1` for connected `W` from the
  `K`-norm `sup_X A^{(|𝓑(X)|-4)_+}‖K(X)‖ ≤ κ` and `A⁴κ ≤ 1` (`A ≥ 1`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- **The bulk part of the block factor `I(B) = e^{-V(B)}(1 + 𝒲(B))`.** -/
theorem r3_IbO_e_le {c : Obs.Case} (j : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (V W : (Fin 2 → ℕ) → OE c (Lam 2 L N)) (q : Fin 2 → ℕ) (x y : EvR (Lam 2 L N))
    (hVx : bulk (V q) = x) (hWy : bulk (W q) = y) (hx : ε (x : Alg 2 L N) = 0)
    {v f : ℝ} (hv0 : 0 ≤ v) (hf0 : 0 ≤ f)
    (hv : Tj 2 (L : ℝ) j ℓ (x : Alg 2 L N) ≤ ENNReal.ofReal v)
    (hf : Tj 2 (L : ℝ) j ℓ (y : Alg 2 L N) ≤ ENNReal.ofReal f) :
    Tj 2 (L : ℝ) j ℓ ((IbO V W q : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e ≤
      ENNReal.ofReal (Real.exp v * (1 + f)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos hL0 _
  have e : ((IbO V W q : OE c (Lam 2 L N)) : SA c (Lam 2 L N)).e =
      ((gexp (-x) * (1 + y) : EvR (Lam 2 L N)) : Alg 2 L N) := by
    rw [← coe_bulk]
    unfold IbO
    rw [map_mul, bulk_oexp', map_neg, map_add, map_one, hVx, hWy]
  rw [e]
  refine (tNorm_mul_le' hh hℓ _ _).trans ?_
  have hε : ε ((-x : EvR (Lam 2 L N)) : Alg 2 L N) = 0 := by
    rw [NegMemClass.coe_neg, map_neg, hx, neg_zero]
  have h1 : Tj 2 (L : ℝ) j ℓ ((gexp (-x) : EvR (Lam 2 L N)) : Alg 2 L N) ≤
      ENNReal.ofReal (Real.exp v) :=
    tNorm_gexp_le hh hℓ hε hv0 (by rw [NegMemClass.coe_neg, tNorm_neg]; exact hv)
  have h2 : Tj 2 (L : ℝ) j ℓ (((1 + y : EvR (Lam 2 L N))) : Alg 2 L N) ≤ ENNReal.ofReal (1 + f) := by
    rw [AddMemClass.coe_add, OneMemClass.coe_one]
    refine (tNorm_add_le _ _).trans ?_
    rw [ENNReal.ofReal_add zero_le_one hf0, ENNReal.ofReal_one]
    exact add_le_add (tNorm_one_le hh hℓ) hf
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' h1 h2

/-- **The large-set regulator from the `K`-norm**: `A^{|𝓑(W)|}‖K(W)‖ ≤ 1` from
`Knorm ≤ κ` and `A⁴κ ≤ 1`. -/
theorem r3_reg_of_Knorm {j : ℕ} {ℓ A κ : ℝ} (hA : 1 ≤ A) (K : Act 2 L N)
    (hK : Knorm j ℓ A K ≤ ENNReal.ofReal κ) (hκ : A ^ 4 * κ ≤ 1) :
    ∀ W, IsConn j W → ENNReal.ofReal (A ^ nb j W) *
      Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1 := by
  intro W hW
  have hA0 : 0 ≤ A := by linarith
  have h1 : ENNReal.ofReal (A ^ (nb j W - 2 ^ 2)) *
      Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ Knorm j ℓ A K :=
    le_iSup₂ (f := fun X (_ : X ∈ connSets (L := L) (N := N) j) =>
      ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ ((K X : Step.EvR (Lam 2 L N)) : Alg 2 L N)) W
      (by simp [connSets]; exact hW)
  calc ENNReal.ofReal (A ^ nb j W) * Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N)
      ≤ ENNReal.ofReal (A ^ 4) * (ENNReal.ofReal (A ^ (nb j W - 2 ^ 2)) *
          Tj 2 (L : ℝ) j ℓ ((K W : Step.EvR (Lam 2 L N)) : Alg 2 L N)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hA0 _)]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (regA_le A hA _)) le_rfl
    _ ≤ ENNReal.ofReal (A ^ 4) * ENNReal.ofReal κ := mul_le_mul' le_rfl (h1.trans hK)
    _ ≤ 1 := by
        by_cases hκ0 : 0 ≤ κ
        · rw [← ENNReal.ofReal_mul (pow_nonneg hA0 _), ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hκ
        · rw [ENNReal.ofReal_of_nonpos (show κ ≤ 0 by linarith), mul_zero]; exact zero_le_one

/-- `rr_delta_KbHF` with the block bound `hI` only for `b ∈ 𝓑_m` (all that is used). -/
theorem r3_delta_KbHF (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P' : ObsPts 2 L N)
    (m : ℕ) (t : Flow2.Hist.Seq (Xs R)) (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)
    {o o' : ObsSt .two L N} (ho : o.IsObs) {k₁ k₂ ι βs : ℝ}
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hι : 0 ≤ ι) (hA : 1 ≤ R.A)
    (hK₁ : ∀ Y, IsConn m Y → ENNReal.ofReal (R.A ^ (nb m Y - 2 ^ 2)) *
      oTo Obs2.wA m (histS R m t) (o.K Y) ≤ ENNReal.ofReal k₁)
    (hK₂ : ∀ Y, IsConn m Y → ENNReal.ofReal (R.A ^ (nb m Y - 2 ^ 2)) *
      oTo Obs2.wA m (histS R m t) (o'.K Y) ≤ ENNReal.ofReal k₂)
    (hI : ∀ b ∈ blockIdx (L := L) (N := N) m, Tj 2 (L : ℝ) m (histS R m t)
      ((IbO (fun b' => emb (stVf R m (rawHist R m t)
      (t m).1 (t m).2.1 b' + stDelta R m (rawHist R m t) b') + (o.V b' - rrD a a' β b'))
      (fullW (rawHist R m t) (rawD R (rawHist R m t).u (t m).2.2) o) b :
        OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal ι)
    (hKb : ∀ W, IsConn m W → ENNReal.ofReal (R.A ^ nb m W) *
      Tj 2 (L : ℝ) m (histS R m t) ((rawK R (rawHist R m t).u (t m).2.2 W :
        Step.EvR (Lam 2 L N)) : Alg 2 L N) ≤ 1)
    (hβ : ∑ b ∈ blockIdx (L := L) (N := N) m, ‖β b‖ ≤ βs) (hs : 0 < histS R m t) :
    KbHF R P' m (subSt (rrStH R m t a a' β o) o') t m
      (k₁ + k₂ + βs * (2 * ((2 : ℕ) : ℝ) * supNorm (a - a') * histS R m t ^ 2 / (L : ℝ) ^ m) *
        ι * R.A) := by
  intro Y hY
  rw [obsHistFrom_self]
  exact rr_delta_K_wt R m _ _ _ _ _ a a' β hs hA ho hY hk₁ hk₂ hι (hK₁ Y hY) (hK₂ Y hY)
    (fun b hb => hI b (blocks_subset_blockIdx Y hb)) hKb
    ((sum_le_sum_of_subset_of_nonneg (blocks_subset_blockIdx Y)
      (fun _ _ _ => norm_nonneg _)).trans hβ)

end

end PtCorr2
