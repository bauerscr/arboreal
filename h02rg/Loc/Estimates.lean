import Loc.EstContract

/-!
# Proposition `prop:Loc` (i) and (ii)

For `L ≥ L₀(d)`, `j < N`, small sets `Y ⊆ X` and `F ∈ 𝒩(X^□)`:

* (i) `Loc_bound`: `‖Loc_{X,Y} F‖_{T_j(ℓ_j)} ≤ C̄ ‖F‖_{T_j(ℓ_j)}`;
* (ii) `Loc_contract`: for `U(1)`-invariant `F`,
  `‖(1 - Loc_X) F‖_{T_{j+1}(2ℓ_{j+1})} ≤ C̄ L^{-d} L^{-((d-2)/2 ∧ 1)} ‖F‖_{T_j(ℓ_j)}`.

The constants `C̄` and `L₀` depend only on `d` (we take `L₀ = 2^{d+3} + 8d + 1`).  In (ii) we
in fact prove the stronger rate `L^{-(d+1)}` (`exists_contract_bound`).

The proof is organised as follows.
* `Loc.EstBasic`: seminorm properties of `‖·‖_T`, pairings with test functions of one length;
* `Loc.EstCutoff`, `Loc.EstTransfer`, `Loc.EstLeibniz`, `Loc.EstLocal`: smooth cut-offs at scale
  `L^j`, the transfer of test functions from `ℤ^d` to the torus, the Leibniz rule, and the
  resulting bound for localised test functions;
* `Loc.EstMono`, `Loc.EstMu`, `Loc.EstCoef`, `Loc.EstPartI`: `‖M_x‖_T ≤ ℓ^2 L^{-j deg M}`,
  `‖μ_β(F)‖ ≤ C ℓ^{-2} L^{j deg β} ‖F‖_T`, the triangular solution of `c A_X = μ(F)`, and (i);
* `Loc.EstPath`, `Loc.EstVanish`, `Loc.EstTaylor`, `Loc.EstQuad`, `Loc.EstLocCoeffs`,
  `Loc.EstContract1`, `Loc.EstContract2`, `Loc.EstContract`: the contraction estimate, split by
  the length of the sequences: length `0` and odd lengths do not contribute, length `2` gains
  `L^{-3}` from the Taylor remainder of degree `2` (the Taylor polynomial is annihilated since
  `Loc_X` preserves the pairings `μ_β`), lengths `4` and `6` gain `L^{-2}` since antisymmetric test
  functions vanish when two entries of equal spin coincide, and lengths `≥ 8` gain enough from
  `(2ℓ_{j+1}/ℓ_j)^8`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d : ℕ}

/-- Proposition `prop:Loc` (i). -/
theorem Loc_bound (hd : 3 ≤ d) : ∃ Cbar : ℝ, ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    IsSmall j Y → Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)),
      Tj d (L : ℝ) j (ellj d L ℓ₀ j) (LocXY X Y F) ≤
        ENNReal.ofReal Cbar * Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨C, _, hC⟩ := exists_LocXY_bound d (by omega)
  refine ⟨C, 2 ^ (d + 3) + 8 * d + 1, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X Y hX _ hYX F hF
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact hC L (by omega) N j hj X Y hX hYX F hF _ (ellj_pos hL0 hℓ₀ j)

/-- Proposition `prop:Loc` (ii), for `U(1)`-symmetric `F`. -/
theorem Loc_contract (hd : 3 ≤ d) : ∃ Cbar : ℝ, ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), IsSym F →
      Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (F - LocX X F) ≤
        ENNReal.ofReal (Cbar * (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-min (((d : ℝ) - 2) / 2) 1)) *
          Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨C, hC0, hC⟩ := exists_contract_bound d hd
  refine ⟨C, 2 ^ (d + 3) + 8 * d + 1, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X hX F hF hsym
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  refine (hC L (by omega) N j hj ℓ₀ hℓ₀ X hX F hF hsym).trans ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  rw [mul_assoc, ← Real.rpow_add hL0]
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 ?_) hC0
  have := min_le_right (((d : ℝ) - 2) / 2) 1
  linarith

end

end Loc
