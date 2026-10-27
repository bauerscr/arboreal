import Obs2.Est.EstBlock
import Obs2.Est.EstLoc
import Obs2.Flow.FlowMu

/-!
# One-step bound for the single-point coupling `μ` (the `m` recursion of `lin_iter`)

With the exact recursion of `Obs2.Flow.FlowMu` (`VpO_a_one`, `mass2_VpO_a`):
`β_{j+1} = β_j - ∑_{X ⊇ B} m(K(X)_a) - m(S(B_+)_a)` at the block `B ∋ a`, and the block bounds of
`Obs2.Est.EstBlock` with the `a`-only weights `wA = (1, 0, 0)` (so that the observable norm is
`‖F_a‖_{T_j(ℓ)}`, `oTo_wA`), we get (`mu_step_one`, Case (1), `m = mass1(-1)`):

`|β_{j+1} - β_j| ≤ c C₀ ℓ^{-1} k + C_m ℓ'^{-1} L^d (2 c_near Q₁² r m_V + Q₁ m_W)`,

where `k = sup_X ‖K(X)_a‖_{T_j(ℓ)}` (small `X ⊇ B`), `m_V = sup_B ‖V(B)_a‖_{T_j(ℓ)}`
(`= |β_j| ℓ` for `V(B_a)_a = β_j ψ̄_a`), `m_W = sup_B ‖𝒲(B)_a‖_{T_j(ℓ)}` and `r` the bulk radius
of `V♭`. Case (2) (`mu_step_two`) is the same with `m = mass2`, `ℓ^{-2}` and `2C_m²`.

This is the `m` half of the hypotheses of `Obs2.lin_iter`:
`|β_{j+1}| ≤ (1 + a_j)|β_j| + A k_j + A' m_{W,j}` with `a_j = 2 c_near Q₁² C_m L^d r_j ℓ/ℓ' = O(ḡ_j)`.
The sharp `a_j` (the one-loop coefficients `-𝔫_j`, `g^♭𝔩_j` of `lem:second`) is the explicit Wick
evaluation of `m(S(B_+)_a)`, not done here.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann FRD Loc Obs Obs.SA Obs.LocObs Step ENNReal

variable {d L N : ℕ} [NeZero L]

/-- The `a`-only weights `(1, 0, 0)`. -/
def wA : Wt := ⟨1, 0, 0⟩

theorem wA_sub : wA.Sub := by unfold Wt.Sub wA; simp

theorem wA_ab : wA.ab = 0 := rfl

theorem oTo_wA {c : Obs.Case} (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo wA j ℓ F = Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a := by
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply, wA]
  rw [show Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 from tNorm_zero']; simp

/-- **One step of `μ^{(1)}`** (Case (1)). -/
theorem mu_step_one (d : ℕ) : ∃ (c : ℕ) (C₀ Cm : ℝ), 0 ≤ C₀ ∧ 0 ≤ Cm ∧ ∀ (L : ℕ) [NeZero L] (N : ℕ)
    (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .one d L N) (K : OAct .one d L N) (r mV mW k Cl cS : ℝ),
    BHO P j ℓ ℓ' ℓC C V W K wA r mV mW k Cl cS →
    ∀ b : Fin d → ℕ, b ∈ blockIdx (L := L) (N := N) j → P.a ∈ blockSet (L := L) (N := N) j b →
    ∀ β : ℂ, (V b : SA .one (Lam d L N)).a = β • psibar P.a →
      (VpO P j C V W K b : SA .one (Lam d L N)).a = (β - (∑ X ∈ (smallSets (L := L) (N := N) j).filter
          (fun X => blockSet j b ⊆ X), mass1 (-1) (K X : SA .one (Lam d L N)).a) -
          mass1 (-1) (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .one (Lam d L N)).a) •
          psibar P.a ∧
      ‖(∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
          mass1 (-1) (K X : SA .one (Lam d L N)).a) +
        mass1 (-1) (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .one (Lam d L N)).a‖ ≤
        c * (C₀ * ℓ⁻¹ * k) + Cm * ℓ'⁻¹ * ((L : ℝ) ^ d * sO d L r mV mW) := by
  obtain ⟨c, C₀, hC₀, hK⟩ := K_term_bound d
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  refine ⟨c, C₀, Cm, hC₀, hCm0, ?_⟩
  intro L _ N P j ℓ ℓ' ℓC C V W K r mV mW k Cl cS H b hb ha β hV
  refine ⟨VpO_a_one P j C V W K H.hjN ha hV, ?_⟩
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hK L H.hL8 N j H.hj b hb (fun X => (K X : SA .one (Lam d L N)).a) ℓ k H.hℓ H.hk
      fun X hX => ?_).2
    obtain ⟨hs, -⟩ := mem_smallSets_filter.1 hX
    exact ⟨(H.hKl X hs).a, by rw [← oTo_wA]; exact H.hKk X hs⟩
  · have hs1 : IsSmall (j + 1) (Step2.Bp (L := L) (N := N) j b) :=
      isSmall_clo (isSmall_blockSet_of_mem hb)
    have hm := mass1_le hCm H.hL8 H.hjN hs1 (H.SX_mem (b := b)).a (-1) H.hℓ'
    have hT : (Tj d (L : ℝ) (j + 1) ℓ'
        (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .one (Lam d L N)).a).toReal ≤
        (L : ℝ) ^ d * sO d L r mV mW := by
      have := H.SX_o b
      rw [oTo_wA] at this
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO) this
    refine hm.trans ?_
    have : 0 ≤ Cm * ℓ'⁻¹ := mul_nonneg hCm0 (inv_nonneg.2 H.hℓ'.le)
    exact mul_le_mul_of_nonneg_left hT this

/-- **One step of `μ^{(2)}`** (Case (2)). -/
theorem mu_step_two (d : ℕ) : ∃ (c : ℕ) (C₀ Cm : ℝ), 0 ≤ C₀ ∧ 0 ≤ Cm ∧ ∀ (L : ℕ) [NeZero L] (N : ℕ)
    (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N) (r mV mW k Cl cS : ℝ),
    BHO P j ℓ ℓ' ℓC C V W K wA r mV mW k Cl cS →
    ∀ b : Fin d → ℕ, b ∈ blockIdx (L := L) (N := N) j → P.a ∈ blockSet (L := L) (N := N) j b →
    ∀ α β : ℂ, (V b : SA .two (Lam d L N)).a = α • (1 : Alg d L N) + β • pbp P.a →
      mass2 (VpO P j C V W K b : SA .two (Lam d L N)).a = β - (∑ X ∈ (smallSets (L := L) (N := N) j).filter
          (fun X => blockSet j b ⊆ X), mass2 (K X : SA .two (Lam d L N)).a) -
          mass2 (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a ∧
      ‖(∑ X ∈ (smallSets (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X),
          mass2 (K X : SA .two (Lam d L N)).a) +
        mass2 (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a‖ ≤
        c * (2 * C₀ ^ 2 * ℓ⁻¹ ^ 2 * k) + 2 * Cm ^ 2 * ℓ'⁻¹ ^ 2 * ((L : ℝ) ^ d * sO d L r mV mW) := by
  obtain ⟨c, C₀, hC₀, hK⟩ := K_term_bound d
  obtain ⟨Cm, hCm0, hCm⟩ := exists_mass_bound d
  refine ⟨c, C₀, Cm, hC₀, hCm0, ?_⟩
  intro L _ N P j ℓ ℓ' ℓC C V W K r mV mW k Cl cS H b hb ha α β hV
  refine ⟨mass2_VpO_a P j C V W K H.hjN ha hV, ?_⟩
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hK L H.hL8 N j H.hj b hb (fun X => (K X : SA .two (Lam d L N)).a) ℓ k H.hℓ H.hk
      fun X hX => ?_).1
    obtain ⟨hs, -⟩ := mem_smallSets_filter.1 hX
    exact ⟨(H.hKl X hs).a, by rw [← oTo_wA]; exact H.hKk X hs⟩
  · have hs1 : IsSmall (j + 1) (Step2.Bp (L := L) (N := N) j b) :=
      isSmall_clo (isSmall_blockSet_of_mem hb)
    have hm := mass2_le hCm H.hL8 H.hjN hs1 (H.SX_mem (b := b)).a H.hℓ'
    have hT : (Tj d (L : ℝ) (j + 1) ℓ'
        (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a).toReal ≤
        (L : ℝ) ^ d * sO d L r mV mW := by
      have := H.SX_o b
      rw [oTo_wA] at this
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO) this
    refine hm.trans ?_
    have : 0 ≤ 2 * Cm ^ 2 * ℓ'⁻¹ ^ 2 := by have := H.hℓ'; positivity
    exact mul_le_mul_of_nonneg_left hT this

end

end Obs2
