import PtCorr2.Last.LastAB2
import Obs2.Flow.Tau2Bd

/-!
# The last-step defect of the `σ_aσ_b` constant for inputs without one-point parts (model level)

**`lastDef_ab_le`**: at `j + 1 = N`, for inputs in `abSub` with `‖V(B)_{ab}‖ ≤ M`,
`‖𝒲(B)_{ab}‖ ≤ m_W` and bulk inputs of size `≤ τ ≤ 1`,

  `|−𝔡_{ab} + X_{ab} + ρ_aρ_b| ≤ L²((Q₁ + 5 + 2L²Q₁²)M + Q₁m_W)`

(`ρ_a = 0` without one-point parts; `X_{ab} = ∑_Bε S(B)_{ab}` since there is no `Q` and no far
part at the last scale; the Pauli defect `𝔡_C^a(F) = ε(e^{ℒ_C}F) − εF − C(a,a)m₂F` is bounded
termwise; the block bounds come from the swapped inputs, `Vpr_oA`, `Sb_oA`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen

variable {L N : ℕ} [NeZero L]

section Model

variable (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
  (V W : OFam .two 2 L N) (K : OAct .two 2 L N)

/-- Without one-point parts `ρ_a = 0` at the last scale. -/
theorem rhoA2_last (hj : j + 1 = N) (hV : ∀ b, (V b : SA .two (Lam 2 L N)).a = 0)
    (hW : ∀ b, (W b : SA .two (Lam 2 L N)).a = 0) : rhoA2 P j C V W K = 0 := by
  have hVa : (VprLO j C V : SA .two (Lam 2 L N)).a = 0 := by
    rw [VprLO, AddSubmonoidClass.coe_finsetSum, SA.sum_a]
    exact sum_eq_zero fun b _ => by
      rw [VprO, EthO_eq_expO, coe_expO, expS_a, hV b, map_zero]
  unfold rhoA2 wkA2
  rw [hVa, FC_zero_left, map_zero, add_zero]
  rw [sum_eq_zero fun b _ => by rw [Q2O_last P hj]; show ε (expLC C 0) = 0; rw [map_zero, map_zero],
    sum_eq_zero fun b _ => by rw [EthO_eq_expO, coe_expO, expS_a, hW b, map_zero, map_zero],
    add_zero]

set_option maxHeartbeats 4000000 in
/-- **The last-step defect of the `σ_aσ_b` constant** (model level). -/
theorem lastDef_ab_le (hj : j + 1 = N) (hLp : pauliL0 2 ≤ L) {A : ℝ} (hA1 : 1 ≤ A)
    {ℓ ℓ' ℓC : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    (hC : Step2.GoodCov2 j ℓC C)
    (hV : Step2.InF j (bulkF V)) (hW : Step2.InF j (bulkF W))
    (hV0 : ∀ b, ε ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) = 0) (hK : Step2.InK2 j (bulkF K))
    (hVl : ∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (V b : SA .two (Lam 2 L N)))
    (hWl : ∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (W b : SA .two (Lam 2 L N)))
    (hVab : ∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (hWab : ∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    {τ M mW : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hM : 0 ≤ M) (hmW0 : 0 ≤ mW)
    (hVb : Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal τ)
    (hWb : Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal τ)
    (hKb : Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal τ)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ (V b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal M)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ (W b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal mW) :
    ‖-pdefAB2 P j C V + (xAB2 P j C V W K + rhoA2 P j C V W K * rhoB2 P j C V W K)‖ ≤
      (L : ℝ) ^ 2 * ((Step2.Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW) := by
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal τ :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N)) b hb).trans hVb
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ ((bulkF W b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal τ :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ ((bulkF W b : EvR (Lam 2 L N)) : Alg 2 L N)) b hb).trans hWb
  have H0 : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A τ :=
    { hd := le_refl _ |>.trans (by norm_num), hLp := hLp, hjN := hj, hℓ := hℓ, hℓ' := hℓ',
      hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1,
      hr := hτ.le, hr1 := hτ1, hVr := hVr', hWr := hWr', hKr := hKb }
  have H : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF (swF V)) (bulkF (swF W)) (bulkF (swF K)) A τ := by
    rw [bulkF_swF, bulkF_swF, bulkF_swFK]; exact H0
  have hQ := H.hQ1
  have hQ0 : 0 ≤ Step2.Q1 2 := by linarith
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hn : ((blockIdx (d := 2) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ 2 := by
    exact_mod_cast Step2.LastN.card_blockIdx_last (d := 2) (L := L) hj
  have hVo' : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (swF V b) ≤ ENNReal.ofReal M :=
    fun b hb => by rw [swF_apply, oTo_wA_swO]; exact hVo b hb
  have hWo' : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (swF W b) ≤ ENNReal.ofReal mW :=
    fun b hb => by rw [swF_apply, oTo_wA_swO]; exact hWo b hb
  -- `ρ_a = 0`
  rw [rhoA2_last P j C V W K hj (fun b => (hVab b).1) (fun b => (hWab b).1), zero_mul, add_zero]
  -- the Pauli defect, termwise
  have hP1 : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ‖pauliDef C P.a (V b : SA .two (Lam 2 L N)).ab‖ ≤ (Step2.Q1 2 + 5) * M := by
    intro b hb
    have e := eps_expLC_pauli C P.a (V b : SA .two (Lam 2 L N)).ab
    have hpd : pauliDef C P.a (V b : SA .two (Lam 2 L N)).ab =
        ε (expLC C (V b : SA .two (Lam 2 L N)).ab) - ε (V b : SA .two (Lam 2 L N)).ab -
          C P.a P.a * mass2 (V b : SA .two (Lam 2 L N)).ab := by rw [e]; ring
    rw [hpd]
    have k1 : ‖ε (expLC C (V b : SA .two (Lam 2 L N)).ab)‖ ≤ Step2.Q1 2 * M := by
      have h := Vpr_oA H (fun b' => cmpIn_swO (hVl b')) hVo' hb
      rw [Obs2.oTo_wA] at h
      have e2 : ((VprO C (swF V) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
          expLC C (V b : SA .two (Lam 2 L N)).ab := by
        rw [← sw_VprO]; show (VprO C V b : SA .two (Lam 2 L N)).ab = _
        rw [VprO, EthO_eq_expO, coe_expO, expS_ab]
      rw [e2] at h
      exact eps_le_of_Tj hℓ' (mul_nonneg hQ0 hM) h
    have k2 : ‖ε (V b : SA .two (Lam 2 L N)).ab‖ ≤ M := eps_le_of_Tj hℓ hM (hVo b hb)
    have k3 : ‖C P.a P.a * mass2 (V b : SA .two (Lam 2 L N)).ab‖ ≤ 4 * M := by
      rw [norm_mul]
      have hCe := good_entry hC P.a P.a
      have hm := norm_mass2_le hℓ j (V b : SA .two (Lam 2 L N)).ab
      have hT : (Tj 2 (L : ℝ) j ℓ (V b : SA .two (Lam 2 L N)).ab).toReal ≤ M :=
        ENNReal.toReal_le_of_le_ofReal hM (hVo b hb)
      have hℓC2 : ℓC ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
      have hm' : ‖mass2 (V b : SA .two (Lam 2 L N)).ab‖ ≤ M * ℓ⁻¹ ^ 2 :=
        hm.trans (mul_le_mul_of_nonneg_right hT (by positivity))
      calc ‖C P.a P.a‖ * ‖mass2 (V b : SA .two (Lam 2 L N)).ab‖ ≤ (4 * ℓ ^ 2) * (M * ℓ⁻¹ ^ 2) :=
            mul_le_mul (hCe.trans hℓC2) hm' (norm_nonneg _) (by positivity)
        _ = 4 * M := by field_simp
    calc ‖ε (expLC C (V b : SA .two (Lam 2 L N)).ab) - ε (V b : SA .two (Lam 2 L N)).ab -
          C P.a P.a * mass2 (V b : SA .two (Lam 2 L N)).ab‖
        ≤ ‖ε (expLC C (V b : SA .two (Lam 2 L N)).ab)‖ + ‖ε (V b : SA .two (Lam 2 L N)).ab‖ +
          ‖C P.a P.a * mass2 (V b : SA .two (Lam 2 L N)).ab‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ Step2.Q1 2 * M + M + 4 * M := add_le_add (add_le_add k1 k2) k3
      _ = (Step2.Q1 2 + 5) * M := by ring
  have hP : ‖pdefAB2 P j C V‖ ≤ (L : ℝ) ^ 2 * ((Step2.Q1 2 + 5) * M) := by
    unfold pdefAB2
    refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ hP1).trans ?_)
    rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn (by positivity)
  -- `X_{ab} = ∑_Bε S(B)_{ab}`
  have hVa : (VprLO j C V : SA .two (Lam 2 L N)).a = 0 := by
    rw [VprLO, AddSubmonoidClass.coe_finsetSum, SA.sum_a]
    exact sum_eq_zero fun b _ => by
      rw [VprO, EthO_eq_expO, coe_expO, expS_a, (hVab b).1, map_zero]
  have hX : xAB2 P j C V W K = ∑ b ∈ blockIdx (L := L) (N := N) j,
      ε ((SbO j C (swF V) (swF W) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a := by
    have h1 := eps_SbO_sum_ab j C V W
    rw [hVa, FC_zero_left, map_zero, add_zero] at h1
    have h2 : ∑ b ∈ blockIdx (L := L) (N := N) j,
        ε ((SbO j C (swF V) (swF W) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
        ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam 2 L N)).ab :=
      sum_congr rfl fun b _ => by rw [← sw_SbO j C hVab]; rfl
    rw [h2, h1]
    unfold xAB2 wkAB2
    rw [farAB_last P j C V W hj, sub_zero,
      sum_eq_zero fun b _ => by rw [Q2O_last P hj]; show ε (expLC C 0) = 0; rw [map_zero, map_zero],
      zero_add, add_comm]
  have hS1 : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ‖ε ((SbO j C (swF V) (swF W) b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a‖ ≤
        (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW := fun b hb =>
    eps_le_of_Tj hℓ' (add_nonneg (by positivity) (mul_nonneg hQ0 hmW0)) (by
      rw [← Obs2.oTo_wA]
      exact Sb_oA H (fun b' => cmpIn_swO (hVl b')) (fun b' => cmpIn_swO (hWl b')) hM hmW0
        hVo' hWo' hb)
  have hXb : ‖xAB2 P j C V W K‖ ≤
      (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW) := by
    have hX0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW :=
      add_nonneg (mul_nonneg (mul_nonneg hL2 (mul_nonneg zero_le_two (sq_nonneg _)))
        (mul_nonneg hτ.le hM)) (mul_nonneg hQ0 hmW0)
    rw [hX]
    refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ hS1).trans ?_)
    rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn hX0
  have hτM : τ * M ≤ M := mul_le_of_le_one_left hM hτ1
  have k1 : (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW) ≤
      (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW) := by
    have := mul_le_mul_of_nonneg_left hτM (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2))
    exact mul_le_mul_of_nonneg_left (by linarith) hL2
  calc ‖-pdefAB2 P j C V + xAB2 P j C V W K‖ ≤ ‖pdefAB2 P j C V‖ + ‖xAB2 P j C V W K‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg]
    _ ≤ (L : ℝ) ^ 2 * ((Step2.Q1 2 + 5) * M) +
        (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW) :=
        add_le_add hP (hXb.trans k1)
    _ = _ := by ring

end Model

end

end PtCorr2
