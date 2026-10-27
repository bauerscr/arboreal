import PtCorr2.Last.LastAB1
import PtCorr2.Last.LastObsK5
import Obs2.Est.EstNormAB

/-!
# The `σ_aσ_b` jets of `F_N` for inputs without one-point parts (model level)

**`finG_jets_ab`**: at `j + 1 = N`, for inputs in `abSub` (all four components local), the jet
bound `LastJetBd L A r₀` of the `σ_a` sector applied to the swapped inputs `swO V, swO 𝒲, swO K`
(`PtCorr2.sw_finG`: `swO F_N = F_N[swO ·]`, so `(F_N)_{ab} = (F_N[swO ·])_a`) gives, for `ab` sizes
`‖V(B)_{ab}‖ ≤ M`, `‖𝒲(B)_{ab}‖ ≤ m_W ≤ τM`, `A^{(|𝓑_j(X)|-4)_+}‖K(X)_{ab}‖ ≤ τM/r₀`:

  `ℓ'²|c2(F_N)_{ab}| ≤ (c_J(c_ρ + 4/r₀²)τ + L²(2Q₁ + 2L²Q₁²))M`,
  `|ε(F_N)_{ab}| ≤ c_J(c_ρ + 4/r₀²)τM`.

The total `∑_Bc2(V_N(B))_a` of the swapped inputs is bounded crudely: `c2(V_N(B))_a = c2V'_{B,a} −
c2(Loc S)_a`, `∑_Bc2(Loc_{Λ,B}S(Λ))_a = ∑_Bc2S(B)_a` (`total_W_mass`), and the block bounds
`Vpr_oA`, `Sb_oA` of the bulk last step.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen

variable {L N : ℕ} [NeZero L]

theorem cmpIn_swO {Λ : Type*} [DecidableEq Λ] {S : Set Λ} {F : OE .two Λ}
    (hF : CmpInA S (F : SA .two Λ)) : CmpIn S ((swO F : OE .two Λ) : SA .two Λ) :=
  ⟨hF.e, hF.ab, zero_mem _⟩

theorem bulkF_swF (V : (Fin 2 → ℕ) → OE .two (Lam 2 L N)) :
    bulkF (swF V) = bulkF V := funext fun b => bulk_swO (V b)

theorem bulkF_swFK (K : Finset (Lam 2 L N) → OE .two (Lam 2 L N)) :
    bulkF (swF K) = bulkF K := funext fun X => bulk_swO (K X)

theorem oTo_wA_swO (j : ℕ) (ℓ : ℝ) (F : OE .two (Lam 2 L N)) :
    oTo Obs2.wA j ℓ (swO F) = Tj 2 (L : ℝ) j ℓ (F : SA .two (Lam 2 L N)).ab := by
  rw [Obs2.oTo_wA]; rfl

set_option maxHeartbeats 4000000 in
/-- **The `σ_aσ_b` jets of `F_N` at the last scale** (inputs without one-point parts). -/
theorem finG_jets_ab {A r₀ : ℝ} (hJ : LastJetBd L A r₀) (hA1 : 1 ≤ A) (hr₀ : 0 < r₀)
    (hr₀1 : r₀ ≤ 1) :
    ∀ (N j : ℕ), j + 1 = N → pauliL0 2 ≤ L → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC →
      ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, Step2.GoodCov2 j ℓC C →
    ∀ (P : ObsPts 2 L N) (V W : OFam .two 2 L N) (K : OAct .two 2 L N),
      Step2.InF j (bulkF V) → Step2.InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) = 0) → Step2.InK2 j (bulkF K) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
        (V b : SA .two (Lam 2 L N))) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
        (W b : SA .two (Lam 2 L N))) →
      (∀ X, IsConn j X → CmpInA (nbhd j X : Set (Lam 2 L N)) (K X : SA .two (Lam 2 L N))) →
      (∀ b, V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) →
      (∀ b, W b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) →
      (∀ X, IsConn j X → K X ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N)))) →
      ∀ τ M MV mW : ℝ, 0 < τ → τ ≤ r₀ → 0 < M → 0 ≤ MV → MV ≤ M → 0 ≤ mW → mW ≤ τ * M →
      Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal τ →
      Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal τ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal τ →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        Tj 2 (L : ℝ) j ℓ (V b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal MV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        Tj 2 (L : ℝ) j ℓ (W b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal mW) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ (K X : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (τ * M / r₀)) →
      cRho L * τ ≤ 1 → 4 * τ ≤ r₀ ^ 2 →
        ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).ab)‖ ≤
          cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M +
            (L : ℝ) ^ 2 * ((Step2.Q1 2 + 2 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2) * MV +
              Step2.Q1 2 * mW) ∧
        ‖ε ((finG P j C V W K : SA .two (Lam 2 L N)).ab)‖ ≤
          cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M := by
  intro N j hj hLp ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P V W K hV hW hV0 hK hVl hWl hKl hVab hWab hKab
    τ M MV mW hτ hτr hM hMV0 hMVM hmW0 hmW hVb hWb hKb hVoV hWo hKo hsm hsm2
  have hτ1 : τ ≤ 1 := hτr.trans hr₀1
  have hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ (V b : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal M :=
    fun b hb => (hVoV b hb).trans (ENNReal.ofReal_le_ofReal hMVM)
  have hfin := sw_finG P j C hj hVab hWab hKab
  have hJ' := hJ N j hj hLp ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P (swF V) (swF W) (swF K)
    (by rw [bulkF_swF]; exact hV) (by rw [bulkF_swF]; exact hW)
    (by rw [bulkF_swF]; exact hV0) (by rw [bulkF_swFK]; exact hK)
    (fun b => cmpIn_swO (hVl b)) (fun b => cmpIn_swO (hWl b))
    (fun X hX => cmpIn_swO (hKl X hX)) τ M mW hτ hτr hM hmW0 hmW
    (by rw [bulkF_swF]; exact hVb) (by rw [bulkF_swF]; exact hWb)
    (by rw [bulkF_swFK]; exact hKb)
    (fun b hb => by rw [swF_apply, oTo_wA_swO]; exact hVo b hb)
    (fun b hb => by rw [swF_apply, oTo_wA_swO]; exact hWo b hb)
    (fun X hX => by rw [swF_apply, oTo_wA_swO]; exact hKo X hX) hsm hsm2
  rw [← hfin] at hJ'
  obtain ⟨h1, h2⟩ := hJ'
  have ec : ∀ F : OE .two (Lam 2 L N), ((swO F : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      (F : SA .two (Lam 2 L N)).ab := fun F => rfl
  rw [ec] at h1 h2
  refine ⟨?_, h2⟩
  -- the bulk last step for the block bounds
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
  have hVo' : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (swF V b) ≤ ENNReal.ofReal MV :=
    fun b hb => by rw [swF_apply, oTo_wA_swO]; exact hVoV b hb
  have hWo' : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (swF W b) ≤ ENNReal.ofReal mW :=
    fun b hb => by rw [swF_apply, oTo_wA_swO]; exact hWo b hb
  -- the per-block `c2` of `V'` and `S` (swapped)
  have hVp : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ℓ' ^ 2 * ‖Suscept.c2 ((VprO C (swF V) b : SA .two (Lam 2 L N)).a)‖ ≤ Step2.Q1 2 * MV :=
    fun b hb => c2_le_of_Tj hℓ' (mul_nonneg hQ0 hMV0) (by
      rw [← Obs2.oTo_wA]
      exact Vpr_oA H (fun b' => cmpIn_swO (hVl b')) hVo' hb)
  have hSb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ℓ' ^ 2 * ‖Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a)‖ ≤
        (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * MV) + Step2.Q1 2 * mW :=
    fun b hb => c2_le_of_Tj hℓ' (add_nonneg (by positivity) (mul_nonneg hQ0 hmW0)) (by
      rw [← Obs2.oTo_wA]
      exact Sb_oA H (fun b' => cmpIn_swO (hVl b')) (fun b' => cmpIn_swO (hWl b')) hMV0 hmW0
        hVo' hWo' hb)
  -- the total of `c2(V_N(B))_a` (swapped)
  have hLS : ∑ b ∈ blockIdx (L := L) (N := N) j,
      Suscept.c2 ((LSO P j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j,
        Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a) := by
    have h := total_W_mass P j C (swF V) (swF W) mass2L (locMass_two P.a)
    have e : ∀ b, mass2L ((WpO P j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a) =
        -(Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a) -
          Suscept.c2 ((LSO P j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a)) := fun b => by
      show mass2 _ = _
      rw [mass2_eq_neg_c2]
      congr 1
      exact PtCorr.c2_sub _ _
    rw [sum_congr rfl fun b _ => e b, sum_neg_distrib, neg_eq_zero, sum_sub_distrib,
      sub_eq_zero] at h
    exact h.symm
  have hsum' : ∑ b ∈ blockIdx (L := L) (N := N) j,
      Suscept.c2 ((VpO P j C (swF V) (swF W) (swF K) b : SA .two (Lam 2 L N)).a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j,
          Suscept.c2 ((VprO C (swF V) b : SA .two (Lam 2 L N)).a) -
        ∑ b ∈ blockIdx (L := L) (N := N) j,
          Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a) := by
    rw [sum_congr rfl fun b _ => c2_VpO_a_last P j C (swF V) (swF W) (swF K) hj b, sum_sub_distrib,
      hLS]
  set X := ∑ b ∈ blockIdx (L := L) (N := N) j,
    Suscept.c2 ((VpO P j C (swF V) (swF W) (swF K) b : SA .two (Lam 2 L N)).a) with hXd
  have hX : ℓ' ^ 2 * ‖X‖ ≤
      (L : ℝ) ^ 2 * ((Step2.Q1 2 + 2 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW) := by
    rw [hsum']
    have hA' := norm_sum_le (blockIdx (L := L) (N := N) j)
      fun b => Suscept.c2 ((VprO C (swF V) b : SA .two (Lam 2 L N)).a)
    have hB' := norm_sum_le (blockIdx (L := L) (N := N) j)
      fun b => Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a)
    have hℓ2 : 0 ≤ ℓ' ^ 2 := sq_nonneg _
    have k1 : ℓ' ^ 2 * ∑ b ∈ blockIdx (L := L) (N := N) j,
        ‖Suscept.c2 ((VprO C (swF V) b : SA .two (Lam 2 L N)).a)‖ ≤ (L : ℝ) ^ 2 * (Step2.Q1 2 * MV) := by
      rw [mul_sum]
      refine (sum_le_card_nsmul _ _ _ hVp).trans ?_
      rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn (mul_nonneg hQ0 hMV0)
    have hSbt : (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * MV) + Step2.Q1 2 * mW ≤
        (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW := by
      have e1 : τ * MV ≤ MV := mul_le_of_le_one_left hMV0 hτ1
      have := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2))
      linarith
    have hS0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW :=
      add_nonneg (mul_nonneg (mul_nonneg hL2 (mul_nonneg zero_le_two (sq_nonneg _))) hMV0)
        (mul_nonneg hQ0 hmW0)
    have k2 : ℓ' ^ 2 * ∑ b ∈ blockIdx (L := L) (N := N) j,
        ‖Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a)‖ ≤
        (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW) := by
      rw [mul_sum]
      refine (sum_le_card_nsmul _ _ _ fun b hb => (hSb b hb).trans hSbt).trans ?_
      rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn hS0
    calc ℓ' ^ 2 * ‖∑ b ∈ blockIdx (L := L) (N := N) j,
            Suscept.c2 ((VprO C (swF V) b : SA .two (Lam 2 L N)).a) -
          ∑ b ∈ blockIdx (L := L) (N := N) j,
            Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a)‖
        ≤ ℓ' ^ 2 * (∑ b ∈ blockIdx (L := L) (N := N) j,
            ‖Suscept.c2 ((VprO C (swF V) b : SA .two (Lam 2 L N)).a)‖ +
          ∑ b ∈ blockIdx (L := L) (N := N) j,
            ‖Suscept.c2 ((SbO j C (swF V) (swF W) b : SA .two (Lam 2 L N)).a)‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hA' hB')) hℓ2
      _ ≤ (L : ℝ) ^ 2 * (Step2.Q1 2 * MV) +
          (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW) := by
          rw [mul_add]; exact add_le_add k1 k2
      _ = _ := by ring
  have hℓ2 : 0 ≤ ℓ' ^ 2 := sq_nonneg _
  have := norm_sub_le (Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).ab) + X) X
  rw [add_sub_cancel_right] at this
  calc ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).ab)‖
      ≤ ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).ab) + X‖ + ℓ' ^ 2 * ‖X‖ := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left this hℓ2
    _ ≤ _ := add_le_add h1 hX

end

end PtCorr2
