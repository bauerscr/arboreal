import Obs2.Est.EstNorm

/-!
# The observable part of `K♭`

**`oTo_KflatO_le`**: for `K♭(X) = ∏_{B ⊆ X} e^{Δ(B)} K(X)` (`KflatO`) with `‖Δ(B)‖_j ≤ δ`,

  `(A e^{-δ})^{(|𝓑_j(X)| - 2^d)_+} ‖K♭(X)^{obs}‖ ≤ e^{2^d δ} A^{(|𝓑_j(X)| - 2^d)_+} ‖K(X)^{obs}‖`,

the observable analogue of `Step2.Knorm_Kflat_le` (the factor `∏ e^{Δ(B)}` is bulk).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- `‖(emb x · F)^{obs}‖ ≤ ‖x‖ ‖F^{obs}‖`. -/
theorem oTo_emb_mul_le (w : Wt) (hw : w.Sub) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (x : EvR (Lam d L N))
    (F : OE c (Lam d L N)) :
    oTo w j ℓ (emb x * F) ≤ Tj d (L : ℝ) j ℓ (x : Alg d L N) * oTo w j ℓ F := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  refine (oTo_mul_le w hh hℓ hw _ _).trans (le_of_eq ?_)
  rw [oTo_emb, zero_mul, add_zero, coe_emb, ofN_e]

/-- **The observable part of `K♭`.** -/
theorem oTo_KflatO_le (w : Wt) (hw : w.Sub) (j : ℕ) {ℓ A δ : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (Δ : Step2.Fam d L N) (hΔ0 : ∀ b, ε (Δ b : Alg d L N) = 0)
    (hΔ : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ (Δ b : Alg d L N) ≤ ENNReal.ofReal δ)
    (K : OAct c d L N) (X : Finset (Lam d L N)) :
    ENNReal.ofReal ((A * Real.exp (-δ)) ^ (nb j X - 2 ^ d)) * oTo w j ℓ (KflatO j Δ K X) ≤
      ENNReal.ofReal (Real.exp (2 ^ d * δ)) *
        (ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X)) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) j
  have hP : Tj d (L : ℝ) j ℓ ((bpow j (fun b => gexp (Δ b)) X : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal (Real.exp δ ^ nb j X) := by
    refine (tNorm_prod_le hh hℓ _ _).trans ?_
    calc ∏ b ∈ blocks j X, Tj d (L : ℝ) j ℓ ((gexp (Δ b) : EvR (Lam d L N)) : Alg d L N)
        ≤ ∏ b ∈ blocks j X, ENNReal.ofReal (Real.exp δ) :=
          prod_le_prod' fun b hb => tNorm_gexp_le hh hℓ (hΔ0 b) hδ
            (hΔ b (mem_blockIdx_of_mem_blocks hb))
      _ = ENNReal.ofReal (Real.exp δ ^ nb j X) := by
          rw [prod_const, ENNReal.ofReal_pow (Real.exp_pos _).le, nb]
  set n := nb j X
  set m := n - 2 ^ d
  have hnm : (n : ℝ) ≤ m + 2 ^ d := by
    have : n ≤ m + 2 ^ d := by omega
    exact_mod_cast this
  calc ENNReal.ofReal ((A * Real.exp (-δ)) ^ m) * oTo w j ℓ (KflatO j Δ K X)
      ≤ ENNReal.ofReal ((A * Real.exp (-δ)) ^ m) *
        (ENNReal.ofReal (Real.exp δ ^ n) * oTo w j ℓ (K X)) := by
        refine mul_le_mul_left' ?_ _
        exact (oTo_emb_mul_le w hw hℓ _ _).trans (mul_le_mul_right' hP _)
    _ = ENNReal.ofReal (Real.exp (-δ) ^ m * Real.exp δ ^ n) *
        (ENNReal.ofReal (A ^ m) * oTo w j ℓ (K X)) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ ENNReal.ofReal (Real.exp (2 ^ d * δ)) * (ENNReal.ofReal (A ^ m) * oTo w j ℓ (K X)) := by
        gcongr
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith

end

end Obs2
